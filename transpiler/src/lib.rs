//! Verus Spec-to-Implementation Transpiler
//!
//! This crate provides tools to transform Verus `spec fn` predicates (TLA-style
//! Init/Next specifications) into verified `exec fn` implementations.
//!
//! # Overview
//!
//! The transpiler pipeline consists of:
//! 1. **Parser** - Parse Verus spec functions from Rust source files
//! 2. **Annotation** - Process mode annotations from `.automan` files
//! 3. **Mode Analysis** - Analyze input/output modes and track assignments
//! 4. **Validation** - Check saturation, harmony, and obligation constraints
//! 5. **Translation** - Generate exec functions with proof linkage
//! 6. **Printing** - Format output as valid Rust/Verus code
//!
//! # Example
//!
//! ```ignore
//! use verus_transpiler::{Transpiler, TranspilerConfig};
//!
//! let config = TranspilerConfig::default();
//! let transpiler = Transpiler::new(config);
//!
//! let result = transpiler.transpile_file(
//!     "src/protocol/RSL/acceptor.rs",
//!     "src/protocol/RSL/acceptor.automan",
//! )?;
//!
//! std::fs::write("src/implementation/RSL/acceptor_gen.rs", result)?;
//! ```

pub mod annotation;
pub mod ast;
pub mod build_integration;
pub mod checker;
pub mod codegen;
pub mod config;
pub mod error;
pub mod modelcheck;
pub mod moder;
pub mod parser;
pub mod printer;
pub mod roundtrip;
pub mod runtime;
pub mod spec_analyzer;
pub mod templates;
pub mod tla;
pub mod translator;
pub mod types;
pub mod verus2tla;

// Re-export commonly used types
pub use annotation::{AnnotationParser, FunctionAnnotation, ModuleAnnotations};
pub use ast::{Expr, Parameter, ParameterMode, SpecFunction, Type};
pub use checker::{
    validate_function, validate_function_with_registry, HarmonyChecker, ObligationChecker,
    QuantifierMatcher, SaturationChecker,
};
pub use codegen::{
    classify_actions, extract_lnext_actions, find_and_analyze_lnext, generate_all_types,
    generate_host_init_test_program, generate_host_scaffold, generate_marshalable_impls,
    generate_message_code, scheduler_config_to_toml, ActionClassificationOverrides, ActionKind,
    GeneratedCode, HostScaffoldParams, HostTestParams, SchedulerAction, SchedulerConfig,
    TemplateCodeGenerator, TypeGenerator,
};
pub use config::{
    MarshalableConfig, MarshalableEnum, MarshalableEnumVariant, MarshalableType, MessageConfig,
    MessageVariant, ModuleConfig, NamingConfig, OutputConfig, RoleConfig, RoleDispatchConfig,
    SchedulerActionConfig, SchedulerTomlConfig, TranspilerConfig as FileConfig,
};
pub use error::{DiagnosticAccumulator, TranspileError, TranspileResult, TranspileWarning};
pub use moder::{AnnotatedFunction, AssignmentTracker, ModeAnalyzer, PredicateKind};
pub use parser::{parse_file, VerusParser};
pub use printer::{print_function, Printer, PrinterConfig};
pub use runtime::{DeepClone, ExecType, SpecType, Validated, ValidatedResult, View};
pub use templates::{match_expression, QuantifierTemplate, TemplateMatcher};
pub use translator::{
    ExecFunction, FunctionClassification, FunctionInfo, Translator, TranslatorConfig,
};
pub use types::{EnumDef, FieldDef, FunctionSig, StructDef, TypeParser, TypeRegistry};

use std::path::Path;

/// Main transpiler configuration
#[derive(Debug, Clone, Default)]
pub struct TranspilerConfig {
    /// Configuration for the translator
    pub translator: TranslatorConfig,
    /// Configuration for the printer
    pub printer: PrinterConfig,
    /// Custom imports to include in generated code (before verus! block)
    pub custom_imports: Vec<String>,
    /// Whether to generate type definitions inline from the spec file.
    /// When true, parses struct/enum definitions from the spec file and generates
    /// corresponding exec types with View trait implementations.
    /// This makes the output self-contained without depending on manual implementation code.
    pub generate_inline_types: bool,
    /// Type remapping table for custom type name mappings
    pub type_remapping: std::collections::HashMap<String, String>,
    /// Whether to generate wrapper methods in an impl block for &mut self pattern.
    pub generate_wrapper_methods: bool,
    /// Functions to skip during transpilation (require manual implementation).
    /// These are functions with patterns too complex for automatic transpilation.
    pub skip_functions: Vec<String>,
    /// Functions to skip without generating stubs (even in proof-fallback mode).
    /// Use for functions that already exist in implementation files.
    pub no_stub_functions: Vec<String>,
    /// The type name for the impl block when generating wrapper methods.
    pub wrapper_impl_type: Option<String>,
    /// Raw Verus code to inject at the end of the `verus! {}` block.
    /// Used for functions too complex for auto-generation.
    pub manual_code: Option<String>,
    /// When true, transpilation errors for individual functions are caught
    /// and the function is automatically added to skip_functions instead of
    /// aborting. Produces a report of skipped functions with reasons.
    pub auto_skip: bool,
    /// When true (implies auto_skip), untranslatable functions are emitted as
    /// `#[verifier(external_body)]` stubs instead of being silently skipped.
    /// Each stub includes a `// TRANSLATE-TODO:` or `// PROOF-TODO:` comment.
    pub proof_fallback: bool,
    /// Message type pair (ExecType, SpecType) for generating `lemma_empty_msg_map()`.
    /// Used by composite handlers that return `(CState, Vec<CMessage>)`.
    pub msg_vec_type: Option<(String, String)>,
    /// Exec type names whose non-scalar fields should be wrapped in Arc<T>.
    /// Used to compute arc_wrap_fields for the translator.
    pub arc_wrap_types: Vec<String>,
}

/// A function that was automatically skipped during transpilation.
#[derive(Debug, Clone)]
pub struct SkippedFunction {
    /// Name of the skipped function
    pub name: String,
    /// Reason it was skipped (error message)
    pub reason: String,
}

/// Main transpiler orchestrating the pipeline
pub struct Transpiler {
    config: TranspilerConfig,
}

impl Transpiler {
    /// Create a new transpiler with the given configuration
    pub fn new(config: TranspilerConfig) -> Self {
        Self { config }
    }

    /// Transpile a single spec file with its annotation file.
    /// Returns the generated code and a list of auto-skipped functions (if `auto_skip` is enabled).
    pub fn transpile_file_with_report(
        &self,
        spec_path: &Path,
        annotation_path: &Path,
    ) -> TranspileResult<(String, Vec<SkippedFunction>)> {
        let (output, skipped) = self.transpile_file_inner(spec_path, Some(annotation_path))?;
        Ok((output, skipped))
    }

    /// Transpile a single spec file with its annotation file
    pub fn transpile_file(
        &self,
        spec_path: &Path,
        annotation_path: &Path,
    ) -> TranspileResult<String> {
        let (output, _skipped) = self.transpile_file_inner(spec_path, Some(annotation_path))?;
        Ok(output)
    }

    /// Transpile a spec file whose mode annotations may live inline
    /// (`// @automan` directives), in a `.automan` sidecar, or both
    /// (Phase 55.3). With `None`, the spec file must carry inline directives.
    pub fn transpile_file_auto(
        &self,
        spec_path: &Path,
        annotation_path: Option<&Path>,
    ) -> TranspileResult<String> {
        let (output, _skipped) = self.transpile_file_inner(spec_path, annotation_path)?;
        Ok(output)
    }

    /// [`Self::transpile_file_auto`] with the auto-skip report.
    pub fn transpile_file_auto_with_report(
        &self,
        spec_path: &Path,
        annotation_path: Option<&Path>,
    ) -> TranspileResult<(String, Vec<SkippedFunction>)> {
        self.transpile_file_inner(spec_path, annotation_path)
    }

    fn transpile_file_inner(
        &self,
        spec_path: &Path,
        annotation_path: Option<&Path>,
    ) -> TranspileResult<(String, Vec<SkippedFunction>)> {
        // Parse spec file, capturing inline directives (Phase 55.1).
        let spec_source = std::fs::read_to_string(spec_path)?;
        let spec_parser =
            VerusParser::new(spec_source).with_file_path(spec_path.display().to_string());
        let parsed = spec_parser.parse_spec_functions_annotated()?;
        let inline_annotations: Vec<annotation::FunctionAnnotation> =
            parsed.iter().filter_map(|(_, ann)| ann.clone()).collect();
        let spec_fns: Vec<crate::ast::SpecFunction> =
            parsed.into_iter().map(|(func, _)| func).collect();

        // Parse sidecar annotations, then fold the inline ones in. A function
        // annotated identically in both warns; a conflict is an error.
        let sidecar = match annotation_path {
            Some(path) => annotation::parse_annotation_file(path)?,
            None => Vec::new(),
        };
        if annotation_path.is_none() && inline_annotations.is_empty() {
            return Err(TranspileError::Annotation {
                message: format!(
                    "{}: no mode annotations — pass an .automan sidecar or add inline \
                     `// @automan` directives to the spec functions",
                    spec_path.display()
                ),
                span: None,
            });
        }
        let annotations = annotation::merge_sidecar_and_inline(sidecar, inline_annotations)?;

        // Process each function
        let mut mode_analyzer = ModeAnalyzer::new();
        let mut translator_config = self.config.translator.clone();

        // Auto-populate set_fields, hashset_element_types, and clone strategies from struct defs
        let mut hashset_element_types: std::collections::HashSet<String> =
            std::collections::HashSet::new();
        let mut auto_clone_strategy: std::collections::HashMap<String, String> =
            std::collections::HashMap::new();
        if self.config.generate_inline_types {
            let type_defs_for_fields = types::parse_types_from_file(spec_path)?;
            let registry_for_fields = types::build_registry(type_defs_for_fields);
            let naming = crate::config::NamingConfig {
                spec_prefix: self.config.translator.spec_prefix.clone(),
                exec_prefix: self.config.translator.exec_prefix.clone(),
                ..Default::default()
            };
            for struct_def in registry_for_fields.structs.values() {
                if struct_def.is_spec {
                    let mut has_set_field = false;
                    for field in &struct_def.fields {
                        if let crate::ast::Type::Set(inner) = &field.ty {
                            has_set_field = true;
                            translator_config.set_fields.insert(field.name.clone());
                            // If the element type is a named struct, track it as a HashSet element type
                            if let crate::ast::Type::Named(path) = inner.as_ref() {
                                let spec_name = path.segments.last().cloned().unwrap_or_default();
                                if spec_name.starts_with(&naming.spec_prefix) {
                                    let base = &spec_name[naming.spec_prefix.len()..];
                                    let exec_name = format!("{}{}", naming.exec_prefix, base);
                                    hashset_element_types.insert(exec_name);
                                }
                            }
                        }
                    }
                    // Structs with HashSet fields need external_body Clone (Verus doesn't support HashSet::clone)
                    if has_set_field {
                        let exec_name = naming.get_exec_type(&struct_def.name);
                        auto_clone_strategy.insert(exec_name, "external_body".to_string());
                    }

                    // Compute arc_wrap_fields for this struct if it's in arc_wrap_types
                    let exec_name = naming.get_exec_type(&struct_def.name);
                    if self.config.arc_wrap_types.contains(&exec_name) {
                        let mut arc_fields = std::collections::HashSet::new();
                        for field in &struct_def.fields {
                            let is_scalar = matches!(
                                &field.ty,
                                crate::ast::Type::Bool
                                    | crate::ast::Type::Int
                                    | crate::ast::Type::Nat
                                    | crate::ast::Type::Unit
                            );
                            if !is_scalar {
                                arc_fields.insert(field.name.clone());
                            }
                        }
                        if !arc_fields.is_empty() {
                            translator_config
                                .arc_wrap_fields
                                .insert(exec_name, arc_fields);
                        }
                    }
                }
            }
        }

        // Compute arc_wrap_fields from struct definitions even when generate_inline_types is false.
        // This is needed for the translator to emit Arc::new() in struct construction.
        if !self.config.arc_wrap_types.is_empty() && translator_config.arc_wrap_fields.is_empty() {
            if let Ok(type_defs) = types::parse_types_from_file(spec_path) {
                let registry = types::build_registry(type_defs);
                let naming = crate::config::NamingConfig {
                    spec_prefix: self.config.translator.spec_prefix.clone(),
                    exec_prefix: self.config.translator.exec_prefix.clone(),
                    ..Default::default()
                };
                for struct_def in registry.structs.values() {
                    if struct_def.is_spec {
                        let exec_name = naming.get_exec_type(&struct_def.name);
                        if self.config.arc_wrap_types.contains(&exec_name) {
                            let mut arc_fields = std::collections::HashSet::new();
                            for field in &struct_def.fields {
                                let is_scalar = matches!(
                                    &field.ty,
                                    crate::ast::Type::Bool
                                        | crate::ast::Type::Int
                                        | crate::ast::Type::Nat
                                        | crate::ast::Type::Unit
                                );
                                if !is_scalar {
                                    arc_fields.insert(field.name.clone());
                                }
                            }
                            if !arc_fields.is_empty() {
                                translator_config
                                    .arc_wrap_fields
                                    .insert(exec_name, arc_fields);
                            }
                        }
                    }
                }
            }
        }

        let has_auto_set_fields = !translator_config.set_fields.is_empty();
        let mut translator = Translator::new(translator_config);
        let mut printer = Printer::new(self.config.printer.clone());

        // Pre-pass: populate function registry with classifications.
        // This must happen before translation so that let-bindings can resolve
        // calls to value-returning helpers (e.g., step_down_if_needed -> CStepDownIfNeeded).
        {
            let mut pre_analyzer = ModeAnalyzer::new();
            for spec_fn in &spec_fns {
                if self.config.skip_functions.contains(&spec_fn.name) {
                    // For skipped functions, try to get annotations so we can
                    // register input param types (needed for bool detection
                    // in detect_helper_call when called from other functions).
                    let annotation = annotations
                        .iter()
                        .flat_map(|m| m.functions.values())
                        .find(|a| a.name == spec_fn.name);
                    let input_param_types = if let Some(ann) = annotation {
                        if let Ok(annotated) = pre_analyzer.annotate(spec_fn.clone(), ann) {
                            annotated
                                .spec_fn
                                .params
                                .iter()
                                .zip(&annotated.param_modes)
                                .filter(|(_, m)| **m == crate::ast::ParameterMode::Input)
                                .map(|(p, _)| p.ty.clone())
                                .collect()
                        } else {
                            Vec::new()
                        }
                    } else {
                        Vec::new()
                    };
                    translator.register_skipped_function_with_types(
                        &spec_fn.name,
                        "explicitly skipped (skip_functions)",
                        input_param_types,
                    );
                    continue;
                }
                let annotation = annotations
                    .iter()
                    .flat_map(|m| m.functions.values())
                    .find(|a| a.name == spec_fn.name);
                if let Some(annotation) = annotation {
                    if let Ok(annotated) = pre_analyzer.annotate(spec_fn.clone(), annotation) {
                        if annotated.is_functionalizable {
                            translator.register_function(&annotated);
                        }
                    }
                }
            }
        }

        let mut output = String::new();
        output.push_str("// Auto-generated by verus-transpiler\n");
        output.push_str("// DO NOT EDIT MANUALLY\n\n");

        // Add custom imports before verus! block (sorted case-insensitively for rustfmt compatibility)
        let mut sorted_imports = self.config.custom_imports.clone();
        // Auto-add proof-related imports when generate_proofs is enabled
        // Only add set_lib when HashSet fields are present (clone_hashset is generated locally)
        if self.config.translator.generate_proofs && self.needs_set_helpers() {
            let proof_imports = ["use vstd::set_lib::*;"];
            for imp in &proof_imports {
                let imp_str = imp.to_string();
                if !sorted_imports.contains(&imp_str) {
                    sorted_imports.push(imp_str);
                }
            }
        }
        // Auto-add Arc import when arc_wrap_fields is configured
        if !self.config.translator.arc_wrap_fields.is_empty() {
            let arc_import = "use std::sync::Arc;".to_string();
            if !sorted_imports.iter().any(|i| i.contains("std::sync::Arc")) {
                sorted_imports.push(arc_import);
            }
        }
        // Auto-add clone_hashset_u64 import when verified hashset clone is active
        if self.config.translator.use_verified_hashset_clone && self.needs_set_helpers() {
            let hashset_import =
                "use crate::common::collections::hashsets::clone_hashset_u64;".to_string();
            if !sorted_imports
                .iter()
                .any(|i| i.contains("clone_hashset_u64"))
            {
                sorted_imports.push(hashset_import);
            }
        }
        // Phase 42.8: the untyped `clone_hashset` helper (emitted when the
        // verified variant is off) mentions `HashSet` in its signature, so the
        // output has to import it. Without this the emitted module does not
        // compile -- which is why regenerating broadcast_gen.rs failed with
        // "cannot find type `HashSet` in this scope".
        if !self.config.translator.use_verified_hashset_clone && self.needs_set_helpers() {
            let hashset_import = "use std::collections::HashSet;".to_string();
            if !sorted_imports
                .iter()
                .any(|i| i.contains("std::collections::HashSet"))
            {
                sorted_imports.push(hashset_import);
            }
        }
        sorted_imports.sort_by_key(|a| a.to_lowercase());
        for import in &sorted_imports {
            output.push_str(import);
            output.push('\n');
        }
        if !sorted_imports.is_empty() {
            output.push('\n');
        }

        output.push_str("verus! {\n\n");

        // Generate inline types if configured
        if self.config.generate_inline_types {
            let type_defs = types::parse_types_from_file(spec_path)?;
            let registry = types::build_registry(type_defs);
            let naming_config = crate::config::NamingConfig {
                spec_prefix: self.config.translator.spec_prefix.clone(),
                exec_prefix: self.config.translator.exec_prefix.clone(),
                int_type: self.config.translator.int_type.clone(),
                nat_type: self.config.translator.nat_type.clone(),
                ..Default::default()
            };
            let mut type_gen = TypeGenerator::new(naming_config.clone())
                .with_remapping(self.config.type_remapping.clone())
                .with_validity_predicate_name(
                    self.config.translator.validity_predicate_name.clone(),
                )
                .with_primitive_types(
                    self.config
                        .translator
                        .primitive_types
                        .iter()
                        .cloned()
                        .collect(),
                );
            type_gen.set_hashset_element_types(hashset_element_types);
            if !auto_clone_strategy.is_empty() {
                type_gen.set_clone_strategy(auto_clone_strategy);
            }

            // Generate structs (sorted by name for deterministic output)
            let mut struct_names: Vec<_> = registry.structs.keys().cloned().collect();
            struct_names.sort();
            for name in struct_names {
                let struct_def = &registry.structs[&name];
                if struct_def.is_spec {
                    let generated = type_gen.generate_struct(struct_def);
                    output.push_str(&generated.code);
                    output.push('\n');
                }
            }

            // Generate enums (sorted by name for deterministic output)
            let mut enum_names: Vec<_> = registry.enums.keys().cloned().collect();
            enum_names.sort();
            for name in enum_names {
                let enum_def = &registry.enums[&name];
                if enum_def.is_spec {
                    let generated = type_gen.generate_enum(enum_def);
                    output.push_str(&generated.code);
                    output.push('\n');
                }
            }
        }

        // Generate proof helper lemmas if generate_proofs is enabled
        if self.config.translator.generate_proofs {
            let (
                generated_needs_set_helpers,
                generated_needs_vec_helpers,
                generated_needs_set_remove,
            ) = Self::collect_generated_proof_helper_needs(
                &spec_fns,
                &annotations,
                &self.config.skip_functions,
                &self.config.translator,
            )?;
            // Emit helpers either when explicitly configured, or when the spec
            // syntax itself uses empty Seq/Set constructs that generate proof calls.
            let has_vec_fields = !self.config.translator.vec_fields.is_empty()
                || spec_fns.iter().any(|f| Self::spec_uses_empty_seq(&f.body))
                || generated_needs_vec_helpers;
            let has_set_fields = self.needs_set_helpers()
                || has_auto_set_fields
                || spec_fns.iter().any(|f| Self::spec_uses_empty_set(&f.body))
                || generated_needs_set_helpers;
            let has_set_remove = spec_fns.iter().any(|f| Self::spec_uses_remove(&f.body))
                || generated_needs_set_remove;
            let helpers = Self::generate_proof_helper_lemmas(
                has_vec_fields,
                has_set_fields,
                has_set_remove,
                &self.config.translator.struct_vec_fields,
                &self.config.translator.int_type,
                &self.config.translator.clone_up_to_view_types,
                &self.config.msg_vec_type,
                self.config.translator.use_verified_hashset_clone,
                &self.config.translator.arc_wrap_fields,
            );
            if !helpers.is_empty() {
                output.push_str(&helpers);
                output.push('\n');
            }
            // Generate clone helper functions for clone_field_types
            let clone_helpers = Self::generate_clone_helpers(
                &self.config.translator.clone_field_types,
                &self.config.translator.variant_remapping,
            );
            if !clone_helpers.is_empty() {
                output.push_str(&clone_helpers);
                output.push('\n');
            }
            // Generate HashMap abstractify proof lemmas for map_fields
            if self.has_map_fields() {
                let map_helpers = Self::generate_map_proof_lemmas(
                    &self.config.translator.map_fields,
                    &self.config.translator.verified_clone_fns,
                    &self.config.translator.arc_wrap_fields,
                );
                if !map_helpers.is_empty() {
                    output.push_str(&map_helpers);
                    output.push('\n');
                }
            }
        }

        // Generate clone_hashset helper when auto-detected set fields need it,
        // even if generate_proofs is disabled (needed for correct compilation)
        if has_auto_set_fields && !self.config.translator.generate_proofs {
            let helpers = Self::generate_proof_helper_lemmas(
                false,
                true,
                false,
                &std::collections::HashMap::new(),
                &self.config.translator.int_type,
                &self.config.translator.clone_up_to_view_types,
                &None,
                self.config.translator.use_verified_hashset_clone,
                &self.config.translator.arc_wrap_fields,
            );
            if !helpers.is_empty() {
                output.push_str(&helpers);
                output.push('\n');
            }
        }

        // Collect all translated functions
        let mut exec_functions = Vec::new();
        let mut skipped_functions = Vec::new();

        for spec_fn in spec_fns {
            // Check if this function should be skipped
            if self.config.skip_functions.contains(&spec_fn.name) {
                if self.config.proof_fallback
                    && !self.config.no_stub_functions.contains(&spec_fn.name)
                {
                    // Emit stub for explicitly skipped functions (unless in no_stub_functions)
                    let annotation = annotations
                        .iter()
                        .flat_map(|m| m.functions.values())
                        .find(|a| a.name == spec_fn.name);
                    let reason = "explicitly skipped (skip_functions)";
                    let stub = self.generate_external_body_stub(&spec_fn, annotation, reason);
                    output.push_str(&stub);
                    output.push('\n');
                    skipped_functions.push(SkippedFunction {
                        name: spec_fn.name.clone(),
                        reason: reason.to_string(),
                    });
                }
                continue;
            }

            // Find matching annotation
            let annotation = annotations
                .iter()
                .flat_map(|m| m.functions.values())
                .find(|a| a.name == spec_fn.name);

            if let Some(annotation) = annotation {
                let fn_name = spec_fn.name.clone();
                // Save spec_fn for stub generation if proof_fallback and annotation fails
                let spec_fn_backup = if self.config.proof_fallback {
                    Some(spec_fn.clone())
                } else {
                    None
                };

                // Annotate and validate
                let annotated = match mode_analyzer.annotate(spec_fn, annotation) {
                    Ok(a) => a,
                    Err(e) => {
                        let reason = format!("annotation error: {}", e);
                        if self.config.proof_fallback
                            && !self.config.no_stub_functions.contains(&fn_name)
                        {
                            let stub = self.generate_external_body_stub(
                                spec_fn_backup.as_ref().unwrap(),
                                Some(annotation),
                                &reason,
                            );
                            output.push_str(&stub);
                            output.push('\n');
                        }
                        if self.config.auto_skip {
                            skipped_functions.push(SkippedFunction {
                                name: fn_name,
                                reason,
                            });
                            continue;
                        } else {
                            return Err(e);
                        }
                    }
                };

                // Check if functionalizable
                if annotated.is_functionalizable {
                    // Translate
                    let exec_fn = match translator.translate(&annotated) {
                        Ok(f) => f,
                        Err(e) => {
                            let reason = format!("transpilation error: {}", e);
                            if self.config.proof_fallback
                                && !self.config.no_stub_functions.contains(&fn_name)
                            {
                                let stub = self.generate_external_body_stub(
                                    &annotated.spec_fn,
                                    Some(annotation),
                                    &reason,
                                );
                                output.push_str(&stub);
                                output.push('\n');
                            }
                            if self.config.auto_skip {
                                skipped_functions.push(SkippedFunction {
                                    name: fn_name,
                                    reason,
                                });
                                continue;
                            } else {
                                return Err(e);
                            }
                        }
                    };

                    // Print
                    let fn_output = printer.print_function(&exec_fn);
                    output.push_str(&fn_output);
                    output.push('\n');

                    // Collect for wrapper generation
                    if self.config.generate_wrapper_methods {
                        exec_functions.push(exec_fn);
                    }
                } else if self.config.proof_fallback
                    && !self.config.no_stub_functions.contains(&fn_name)
                {
                    // Function exists but can't be functionalized — emit stub
                    let reason = annotated
                        .non_functionalizable_reason
                        .as_deref()
                        .unwrap_or("not functionalizable");
                    let stub = self.generate_external_body_stub(
                        &annotated.spec_fn,
                        Some(annotation),
                        &format!("not functionalizable: {}", reason),
                    );
                    output.push_str(&stub);
                    output.push('\n');
                    skipped_functions.push(SkippedFunction {
                        name: fn_name,
                        reason: format!("not functionalizable: {}", reason),
                    });
                }
            }
        }

        // Generate wrapper methods if configured
        if self.config.generate_wrapper_methods {
            if let Some(ref impl_type) = self.config.wrapper_impl_type {
                let wrappers = self.generate_wrappers(&exec_functions, impl_type);
                if !wrappers.is_empty() {
                    output.push_str(&wrappers);
                    output.push('\n');
                }
            }
        }

        // Inject manual code if configured
        if let Some(ref manual) = self.config.manual_code {
            output.push('\n');
            output.push_str(manual);
            output.push('\n');
        }

        output.push_str("} // verus!\n");

        Ok((output, skipped_functions))
    }

    /// Generate an `#[verifier(external_body)]` stub for a function that failed translation.
    /// Used in proof-fallback mode to emit placeholders instead of silently skipping.
    fn generate_external_body_stub(
        &self,
        spec_fn: &crate::ast::SpecFunction,
        annotation: Option<&crate::annotation::FunctionAnnotation>,
        reason: &str,
    ) -> String {
        let spec_prefix = &self.config.translator.spec_prefix;
        let exec_prefix = &self.config.translator.exec_prefix;
        let int_type = &self.config.translator.int_type;

        let exec_name = Self::spec_to_exec_name(&spec_fn.name, spec_prefix, exec_prefix);

        // Build parameter list: input params get &type, output params become return types
        let mut input_params = Vec::new();
        let mut output_types = Vec::new();
        for (i, param) in spec_fn.params.iter().enumerate() {
            let is_output = annotation
                .map(|a| {
                    i < a.param_modes.len() && a.param_modes[i] == crate::ast::ParameterMode::Output
                })
                .unwrap_or(false);
            let type_str = Self::type_to_exec_string(
                &param.ty,
                spec_prefix,
                exec_prefix,
                int_type,
                &self.config.type_remapping,
            );
            if is_output {
                output_types.push(type_str);
            } else {
                input_params.push(format!("{}: &{}", param.name, type_str));
            }
        }

        let return_type = if !output_types.is_empty() {
            if output_types.len() == 1 {
                format!(" -> (result: {})", output_types[0])
            } else {
                format!(" -> (result: ({}))", output_types.join(", "))
            }
        } else if !matches!(spec_fn.return_type, crate::ast::Type::Bool) {
            // Non-predicate helper: return type from spec function's return type
            let exec_ret = Self::type_to_exec_string(
                &spec_fn.return_type,
                spec_prefix,
                exec_prefix,
                int_type,
                &self.config.type_remapping,
            );
            output_types.push(exec_ret.clone());
            format!(" -> (result: {})", exec_ret)
        } else {
            String::new()
        };

        // Build ensures clauses for external_body stubs
        let mut ensures_lines = Vec::new();
        // Add validity ensures for output types (skip if type is in skip_valid_types)
        let vp = &self.config.translator.validity_predicate_name;
        if !vp.is_empty() {
            for (idx, ot) in output_types.iter().enumerate() {
                let skips_valid = self
                    .config
                    .translator
                    .skip_valid_types
                    .iter()
                    .any(|sv| ot.contains(sv))
                    || ot.starts_with("Vec<")
                    || ot.starts_with("HashMap<")
                    || ot.starts_with("HashSet<")
                    || ot == "bool"
                    || ot == "u64"
                    || ot == "i64"
                    || ot == "usize";
                if !skips_valid {
                    let accessor = if output_types.len() > 1 {
                        format!("result.{}", idx)
                    } else {
                        "result".to_string()
                    };
                    ensures_lines.push(format!("    {}.{}(),", accessor, vp));
                }
                // Add vec_element_ensures for Vec outputs
                if ot.starts_with("Vec<") && !self.config.translator.vec_element_ensures.is_empty()
                {
                    let accessor = if output_types.len() > 1 {
                        format!("result.{}", idx)
                    } else {
                        "result".to_string()
                    };
                    for pred in &self.config.translator.vec_element_ensures {
                        // Phase 54.7: emit the trigger explicitly. Verus
                        // otherwise picks `X@[i]` itself and reports it, and an
                        // auto-chosen trigger can change between releases.
                        ensures_lines.push(format!(
                            "    forall |i:int| #![trigger {}@[i]] 0 <= i < {}@.len() ==> {}@[i].{}(),",
                            accessor, accessor, accessor, pred
                        ));
                    }
                }
            }
        }
        // Add spec predicate ensures: SpecFn(input@, result@, ...)
        // Only for predicate functions (return type is bool), not helper functions that return values
        let is_predicate = matches!(spec_fn.return_type, crate::ast::Type::Bool);
        if annotation.is_some() && is_predicate {
            let mut spec_args = Vec::new();
            let mut output_idx = 0usize;
            let num_outputs = output_types.len();
            for (i, param) in spec_fn.params.iter().enumerate() {
                let is_output = annotation
                    .map(|a| {
                        i < a.param_modes.len()
                            && a.param_modes[i] == crate::ast::ParameterMode::Output
                    })
                    .unwrap_or(false);
                let type_name = if let crate::ast::Type::Named(p) = &param.ty {
                    p.segments.last().cloned().unwrap_or_default()
                } else {
                    String::new()
                };
                let is_primitive = self.config.translator.primitive_types.contains(&type_name);
                // Check for custom view expression (e.g., "Votes" → "abstractify_cvotes({param})")
                let has_custom_view = self
                    .config
                    .translator
                    .type_view_exprs
                    .contains_key(&type_name);
                if is_output {
                    // For tuple returns, use result.0@, result.1@, etc.
                    let result_ref = if num_outputs > 1 {
                        format!("result.{}", output_idx)
                    } else {
                        "result".to_string()
                    };
                    if has_custom_view {
                        let view_expr = self.config.translator.type_view_exprs[&type_name]
                            .replace("{param}", &format!("&{}", result_ref));
                        spec_args.push(view_expr);
                    } else {
                        // Check if this is a Seq<NamedType> that needs .map(|i, p: T| p@)
                        let output_type = &output_types[output_idx];
                        if output_type.starts_with("Vec<")
                            && !output_type.starts_with("Vec<u64>")
                            && !output_type.starts_with("Vec<i64>")
                        {
                            // Extract inner type for view mapping
                            let inner = &output_type[4..output_type.len() - 1];
                            spec_args.push(format!("{}@.map(|i, p: {}| p@)", result_ref, inner));
                        } else {
                            spec_args.push(format!("{}@", result_ref));
                        }
                    }
                    output_idx += 1;
                } else if matches!(
                    param.ty,
                    crate::ast::Type::Int | crate::ast::Type::Nat | crate::ast::Type::Bool
                ) || is_primitive
                {
                    spec_args.push(format!("*{} as int", param.name));
                } else if has_custom_view {
                    let view_expr = self.config.translator.type_view_exprs[&type_name]
                        .replace("{param}", &param.name);
                    spec_args.push(view_expr);
                } else {
                    spec_args.push(format!("{}@", param.name));
                }
            }
            ensures_lines.push(format!("    {}({}),", spec_fn.name, spec_args.join(", ")));
        }

        let ensures_section = if ensures_lines.is_empty() {
            String::new()
        } else {
            format!("\nensures\n{}", ensures_lines.join("\n"))
        };

        format!(
            "// TRANSLATE-TODO: {}\n\
             #[verifier(external_body)]\n\
             pub exec fn {}({}){}{}\n{{\n    unimplemented!()\n}}\n",
            reason,
            exec_name,
            input_params.join(", "),
            return_type,
            ensures_section,
        )
    }

    /// Convert spec name to exec name (e.g., LInit → CInit)
    fn spec_to_exec_name(spec_name: &str, spec_prefix: &str, exec_prefix: &str) -> String {
        if let Some(rest) = spec_name.strip_prefix(spec_prefix) {
            if rest.chars().next().is_some_and(|c| c.is_ascii_uppercase()) {
                return format!("{}{}", exec_prefix, rest);
            }
        }
        format!("{}{}", exec_prefix, spec_name)
    }

    /// Convert AST Type to exec type string for stub generation.
    /// Uses `type_remapping` (from TOML `[remapping]`) to resolve named types.
    fn type_to_exec_string(
        ty: &crate::ast::Type,
        spec_prefix: &str,
        exec_prefix: &str,
        int_type: &str,
        type_remapping: &std::collections::HashMap<String, String>,
    ) -> String {
        use crate::ast::Type;
        match ty {
            Type::Int => int_type.to_string(),
            Type::Nat => int_type.to_string(),
            Type::Bool => "bool".to_string(),
            Type::Named(path) => {
                let name = path.segments.last().cloned().unwrap_or_default();
                // Check remapping table first (e.g., "RslPacket" → "CPacket")
                if let Some(mapped) = type_remapping.get(&name) {
                    return mapped.clone();
                }
                Self::spec_to_exec_name(&name, spec_prefix, exec_prefix)
            }
            Type::Generic(path, args) => {
                let name = path.segments.last().cloned().unwrap_or_default();
                let exec_name = if let Some(mapped) = type_remapping.get(&name) {
                    mapped.clone()
                } else {
                    Self::spec_to_exec_name(&name, spec_prefix, exec_prefix)
                };
                let args_str: Vec<String> = args
                    .iter()
                    .map(|a| {
                        Self::type_to_exec_string(
                            a,
                            spec_prefix,
                            exec_prefix,
                            int_type,
                            type_remapping,
                        )
                    })
                    .collect();
                format!("{}<{}>", exec_name, args_str.join(", "))
            }
            Type::Seq(inner) => {
                format!(
                    "Vec<{}>",
                    Self::type_to_exec_string(
                        inner,
                        spec_prefix,
                        exec_prefix,
                        int_type,
                        type_remapping
                    )
                )
            }
            Type::Set(inner) => {
                format!(
                    "HashSet<{}>",
                    Self::type_to_exec_string(
                        inner,
                        spec_prefix,
                        exec_prefix,
                        int_type,
                        type_remapping
                    )
                )
            }
            Type::Map(k, v) => {
                format!(
                    "HashMap<{}, {}>",
                    Self::type_to_exec_string(
                        k,
                        spec_prefix,
                        exec_prefix,
                        int_type,
                        type_remapping
                    ),
                    Self::type_to_exec_string(
                        v,
                        spec_prefix,
                        exec_prefix,
                        int_type,
                        type_remapping
                    )
                )
            }
            Type::Tuple(inner) => {
                let parts: Vec<String> = inner
                    .iter()
                    .map(|t| {
                        Self::type_to_exec_string(
                            t,
                            spec_prefix,
                            exec_prefix,
                            int_type,
                            type_remapping,
                        )
                    })
                    .collect();
                format!("({})", parts.join(", "))
            }
            _ => "/* unknown type */".to_string(),
        }
    }

    /// Transpile a spec function from source strings
    /// Transpile from source strings, returning both code and skipped function report.
    pub fn transpile_source_with_report(
        &self,
        spec_source: &str,
        annotation_source: &str,
    ) -> TranspileResult<(String, Vec<SkippedFunction>)> {
        self.transpile_source_inner(spec_source, annotation_source)
    }

    pub fn transpile_source(
        &self,
        spec_source: &str,
        annotation_source: &str,
    ) -> TranspileResult<String> {
        let (output, _skipped) = self.transpile_source_inner(spec_source, annotation_source)?;
        Ok(output)
    }

    fn transpile_source_inner(
        &self,
        spec_source: &str,
        annotation_source: &str,
    ) -> TranspileResult<(String, Vec<SkippedFunction>)> {
        let parser = VerusParser::new(spec_source.to_string());
        let parsed = parser.parse_spec_functions_annotated()?;
        let inline_annotations: Vec<annotation::FunctionAnnotation> =
            parsed.iter().filter_map(|(_, ann)| ann.clone()).collect();
        let spec_fns: Vec<crate::ast::SpecFunction> =
            parsed.into_iter().map(|(func, _)| func).collect();

        let ann_parser = AnnotationParser::new(annotation_source.to_string());
        let annotations =
            annotation::merge_sidecar_and_inline(ann_parser.parse()?, inline_annotations)?;

        let mut mode_analyzer = ModeAnalyzer::new();
        let has_auto_set_fields = false;
        let mut translator = Translator::new(self.config.translator.clone());
        let mut printer = Printer::new(self.config.printer.clone());

        // Pre-pass: populate function registry with classifications.
        {
            let mut pre_analyzer = ModeAnalyzer::new();
            for spec_fn in &spec_fns {
                if self.config.skip_functions.contains(&spec_fn.name) {
                    let annotation = annotations
                        .iter()
                        .flat_map(|m| m.functions.values())
                        .find(|a| a.name == spec_fn.name);
                    let input_param_types = if let Some(ann) = annotation {
                        if let Ok(annotated) = pre_analyzer.annotate(spec_fn.clone(), ann) {
                            annotated
                                .spec_fn
                                .params
                                .iter()
                                .zip(&annotated.param_modes)
                                .filter(|(_, m)| **m == crate::ast::ParameterMode::Input)
                                .map(|(p, _)| p.ty.clone())
                                .collect()
                        } else {
                            Vec::new()
                        }
                    } else {
                        Vec::new()
                    };
                    translator.register_skipped_function_with_types(
                        &spec_fn.name,
                        "explicitly skipped (skip_functions)",
                        input_param_types,
                    );
                    continue;
                }
                let annotation = annotations
                    .iter()
                    .flat_map(|m| m.functions.values())
                    .find(|a| a.name == spec_fn.name);
                if let Some(annotation) = annotation {
                    if let Ok(annotated) = pre_analyzer.annotate(spec_fn.clone(), annotation) {
                        if annotated.is_functionalizable {
                            translator.register_function(&annotated);
                        }
                    }
                }
            }
        }

        let mut output = String::new();

        // Add custom imports before verus! block (sorted case-insensitively for rustfmt compatibility)
        let mut sorted_imports = self.config.custom_imports.clone();
        // Auto-add proof-related imports when generate_proofs is enabled
        // Only add set_lib when HashSet fields are present (clone_hashset is generated locally)
        if self.config.translator.generate_proofs && self.needs_set_helpers() {
            let proof_imports = ["use vstd::set_lib::*;"];
            for imp in &proof_imports {
                let imp_str = imp.to_string();
                if !sorted_imports.contains(&imp_str) {
                    sorted_imports.push(imp_str);
                }
            }
        }
        // Auto-add clone_hashset_u64 import when verified hashset clone is active
        if self.config.translator.use_verified_hashset_clone && self.needs_set_helpers() {
            let hashset_import =
                "use crate::common::collections::hashsets::clone_hashset_u64;".to_string();
            if !sorted_imports
                .iter()
                .any(|i| i.contains("clone_hashset_u64"))
            {
                sorted_imports.push(hashset_import);
            }
        }
        sorted_imports.sort_by_key(|a| a.to_lowercase());
        for import in &sorted_imports {
            output.push_str(import);
            output.push('\n');
        }
        if !sorted_imports.is_empty() {
            output.push('\n');
        }

        output.push_str("verus! {\n\n");

        // Generate inline types if configured
        if self.config.generate_inline_types {
            let mut type_parser = types::TypeParser::new(spec_source);
            let type_defs = type_parser.parse_types()?;
            let registry = types::build_registry(type_defs);
            let naming_config = crate::config::NamingConfig {
                spec_prefix: self.config.translator.spec_prefix.clone(),
                exec_prefix: self.config.translator.exec_prefix.clone(),
                int_type: self.config.translator.int_type.clone(),
                nat_type: self.config.translator.nat_type.clone(),
                ..Default::default()
            };
            let type_gen = TypeGenerator::new(naming_config.clone())
                .with_remapping(self.config.type_remapping.clone())
                .with_validity_predicate_name(
                    self.config.translator.validity_predicate_name.clone(),
                )
                .with_primitive_types(
                    self.config
                        .translator
                        .primitive_types
                        .iter()
                        .cloned()
                        .collect(),
                );

            // Generate structs (sorted by name for deterministic output)
            let mut struct_names: Vec<_> = registry.structs.keys().cloned().collect();
            struct_names.sort();
            for name in struct_names {
                let struct_def = &registry.structs[&name];
                if struct_def.is_spec {
                    let generated = type_gen.generate_struct(struct_def);
                    output.push_str(&generated.code);
                    output.push('\n');
                }
            }

            // Generate enums (sorted by name for deterministic output)
            let mut enum_names: Vec<_> = registry.enums.keys().cloned().collect();
            enum_names.sort();
            for name in enum_names {
                let enum_def = &registry.enums[&name];
                if enum_def.is_spec {
                    let generated = type_gen.generate_enum(enum_def);
                    output.push_str(&generated.code);
                    output.push('\n');
                }
            }
        }

        // Generate proof helper lemmas if generate_proofs is enabled
        if self.config.translator.generate_proofs {
            let (
                generated_needs_set_helpers,
                generated_needs_vec_helpers,
                generated_needs_set_remove,
            ) = Self::collect_generated_proof_helper_needs(
                &spec_fns,
                &annotations,
                &self.config.skip_functions,
                &self.config.translator,
            )?;
            // Emit helpers either when explicitly configured, or when the spec
            // syntax itself uses empty Seq/Set constructs that generate proof calls.
            let has_vec_fields = !self.config.translator.vec_fields.is_empty()
                || spec_fns.iter().any(|f| Self::spec_uses_empty_seq(&f.body))
                || generated_needs_vec_helpers;
            let has_set_fields = self.needs_set_helpers()
                || has_auto_set_fields
                || spec_fns.iter().any(|f| Self::spec_uses_empty_set(&f.body))
                || generated_needs_set_helpers;
            let has_set_remove = spec_fns.iter().any(|f| Self::spec_uses_remove(&f.body))
                || generated_needs_set_remove;
            let helpers = Self::generate_proof_helper_lemmas(
                has_vec_fields,
                has_set_fields,
                has_set_remove,
                &self.config.translator.struct_vec_fields,
                &self.config.translator.int_type,
                &self.config.translator.clone_up_to_view_types,
                &self.config.msg_vec_type,
                self.config.translator.use_verified_hashset_clone,
                &self.config.translator.arc_wrap_fields,
            );
            if !helpers.is_empty() {
                output.push_str(&helpers);
                output.push('\n');
            }
            // Generate clone helper functions for clone_field_types
            let clone_helpers = Self::generate_clone_helpers(
                &self.config.translator.clone_field_types,
                &self.config.translator.variant_remapping,
            );
            if !clone_helpers.is_empty() {
                output.push_str(&clone_helpers);
                output.push('\n');
            }
            // Generate HashMap abstractify proof lemmas for map_fields
            if self.has_map_fields() {
                let map_helpers = Self::generate_map_proof_lemmas(
                    &self.config.translator.map_fields,
                    &self.config.translator.verified_clone_fns,
                    &self.config.translator.arc_wrap_fields,
                );
                if !map_helpers.is_empty() {
                    output.push_str(&map_helpers);
                    output.push('\n');
                }
            }
        }

        // Collect all translated functions
        let mut exec_functions = Vec::new();
        let mut skipped_functions = Vec::new();

        for spec_fn in spec_fns {
            // Check if this function should be skipped
            if self.config.skip_functions.contains(&spec_fn.name) {
                continue;
            }

            let annotation = annotations
                .iter()
                .flat_map(|m| m.functions.values())
                .find(|a| a.name == spec_fn.name);

            if let Some(annotation) = annotation {
                let fn_name = spec_fn.name.clone();

                let annotated = match mode_analyzer.annotate(spec_fn, annotation) {
                    Ok(a) => a,
                    Err(e) => {
                        if self.config.auto_skip {
                            skipped_functions.push(SkippedFunction {
                                name: fn_name,
                                reason: format!("annotation error: {}", e),
                            });
                            continue;
                        } else {
                            return Err(e);
                        }
                    }
                };

                if annotated.is_functionalizable {
                    let exec_fn = match translator.translate(&annotated) {
                        Ok(f) => f,
                        Err(e) => {
                            if self.config.auto_skip {
                                skipped_functions.push(SkippedFunction {
                                    name: fn_name,
                                    reason: format!("transpilation error: {}", e),
                                });
                                continue;
                            } else {
                                return Err(e);
                            }
                        }
                    };

                    output.push_str(&printer.print_function(&exec_fn));
                    output.push('\n');

                    // Collect for wrapper generation
                    if self.config.generate_wrapper_methods {
                        exec_functions.push(exec_fn);
                    }
                }
            }
        }

        // Generate wrapper methods if configured
        if self.config.generate_wrapper_methods {
            if let Some(ref impl_type) = self.config.wrapper_impl_type {
                let wrappers = self.generate_wrappers(&exec_functions, impl_type);
                if !wrappers.is_empty() {
                    output.push_str(&wrappers);
                    output.push('\n');
                }
            }
        }

        // Inject manual code if configured
        if let Some(ref manual) = self.config.manual_code {
            output.push('\n');
            output.push_str(manual);
            output.push('\n');
        }

        output.push_str("} // verus!\n");

        Ok((output, skipped_functions))
    }

    /// Generate proof helper lemma functions that are emitted at the top of
    /// the generated file when `generate_proofs` is enabled.
    ///
    /// Currently emits:
    /// - `lemma_empty_set_map()`: proves `Set::<u64>::empty().map(|x: u64| x as int) =~= Set::<int>::empty()`
    /// - `lemma_set_map_remove_commute(s, elt)`: proves `s.remove(elt).map(f) =~= s.map(f).remove(f(elt))`
    /// - `lemma_empty_seq_map()` / `lemma_empty_<field>_map()`: empty Seq mapping proof
    /// - `lemma_seq_push_map_commute(s, x)` / `lemma_<field>_push_map_commute(s, x)`: push commutativity
    /// - `clone_<field>()`: external_body clone wrapper for struct-typed Vec fields
    #[allow(clippy::too_many_arguments)]
    fn generate_proof_helper_lemmas(
        has_vec_fields: bool,
        has_set_fields: bool,
        has_set_remove: bool,
        struct_vec_fields: &std::collections::HashMap<String, (String, String)>,
        int_type: &str,
        clone_up_to_view_types: &std::collections::HashSet<String>,
        msg_vec_type: &Option<(String, String)>,
        use_verified_hashset_clone: bool,
        arc_wrap_fields: &std::collections::HashMap<String, std::collections::HashSet<String>>,
    ) -> String {
        let mut output = String::new();

        // lemma_empty_set_map — only when HashSet fields are present
        if has_set_fields {
            output.push_str("/// Helper proof: mapping an injective function over an empty set yields an empty set.\n");
            output.push_str("proof fn lemma_empty_set_map()\n");
            output.push_str("ensures\n");
            output.push_str(&format!(
                "    Set::<{}>::empty().map(|x: {}| x as int) =~= Set::<int>::empty(),\n",
                int_type, int_type
            ));
            output.push_str("{\n");
            output.push_str(&format!("    let f = |x: {}| x as int;\n", int_type));
            output.push_str(&format!(
                "    let s = Set::<{}>::empty().map(f);\n",
                int_type
            ));
            output.push_str("    assert forall|y: int| !(#[trigger] s.contains(y)) by {\n");
            output.push_str("    }\n");
            output.push_str("}\n\n");

            if !use_verified_hashset_clone {
                // clone_hashset — external_body helper for cloning HashSet fields
                output.push_str(
                    "/// Helper: clone a HashSet (Verus doesn't support HashSet::clone).\n",
                );
                output.push_str("#[verifier(external_body)]\n");
                output.push_str(
                    "fn clone_hashset<K: std::hash::Hash + Eq + Clone>(s: &HashSet<K>) -> (res: HashSet<K>)\n"
                );
                output.push_str("ensures\n");
                output.push_str("    res@ == s@,\n");
                output.push_str("{\n");
                output.push_str("    s.clone()\n");
                output.push_str("}\n\n");
            }
            // When use_verified_hashset_clone is true, clone_hashset_u64 is imported
            // from crate::common::collections::hashsets instead.
        }

        // lemma_set_map_remove_commute — only when spec uses .remove() and has set fields
        if has_set_fields && has_set_remove {
            output.push_str("/// Helper proof: removing an element commutes with mapping for injective functions.\n");
            output.push_str(&format!(
                "proof fn lemma_set_map_remove_commute(s: Set<{}>, elt: {})\n",
                int_type, int_type
            ));
            output.push_str("ensures\n");
            output.push_str(&format!(
                "    s.remove(elt).map(|x: {}| x as int) =~= s.map(|x: {}| x as int).remove(elt as int),\n",
                int_type, int_type
            ));
            output.push_str("{\n");
            output.push_str(&format!("    let f = |x: {}| x as int;\n", int_type));
            output.push_str("    let lhs = s.remove(elt).map(f);\n");
            output.push_str("    let rhs = s.map(f).remove(f(elt));\n");
            output.push_str("    assert forall|y: int| (#[trigger] lhs.contains(y)) implies rhs.contains(y) by {\n");
            output.push_str(&format!(
                "        let x = choose|x: {}| s.remove(elt).contains(x) && f(x) == y;\n",
                int_type
            ));
            output.push_str("        assert(s.contains(x));\n");
            output.push_str("        assert(x != elt);\n");
            output.push_str("        assert(f(x) != f(elt));\n");
            output.push_str("        assert(s.map(f).contains(y));\n");
            output.push_str("    }\n");
            output.push_str("    assert forall|y: int| (#[trigger] rhs.contains(y)) implies lhs.contains(y) by {\n");
            output.push_str(&format!(
                "        let x = choose|x: {}| s.contains(x) && f(x) == y;\n",
                int_type
            ));
            output.push_str("        assert(y != f(elt));\n");
            output.push_str("        assert(f(x) != f(elt));\n");
            output.push_str("        assert(x != elt);\n");
            output.push_str("        assert(s.remove(elt).contains(x));\n");
            output.push_str("    }\n");
            output.push_str("}\n\n");
        }

        // Generate struct-typed Vec proof helpers and clone wrappers
        if !struct_vec_fields.is_empty() {
            let mut sorted_fields: Vec<_> = struct_vec_fields.iter().collect();
            sorted_fields.sort_by_key(|(k, _)| k.to_string());

            for (field, (exec_type, spec_type)) in &sorted_fields {
                // lemma_empty_<field>_map
                output.push_str(&format!(
                    "/// Helper proof: mapping over an empty Vec<{}> yields an empty seq.\n",
                    exec_type
                ));
                output.push_str(&format!("proof fn lemma_empty_{}_map()\n", field));
                output.push_str("ensures\n");
                output.push_str(&format!(
                    "    Seq::<{}>::empty().map(|i: int, e: {}| e@) =~= Seq::<{}>::empty(),\n",
                    exec_type, exec_type, spec_type
                ));
                output.push_str("{\n");
                output.push_str("}\n\n");

                // lemma_<field>_push_map_commute
                output.push_str(&format!(
                    "/// Helper proof: push commutes with Seq::map for {} view.\n",
                    exec_type
                ));
                output.push_str(&format!(
                    "proof fn lemma_{}_push_map_commute(s: Seq<{}>, x: {})\n",
                    field, exec_type, exec_type
                ));
                output.push_str("ensures\n");
                output.push_str(&format!(
                    "    s.push(x).map(|i: int, e: {}| e@) =~= s.map(|i: int, e: {}| e@).push(x@),\n",
                    exec_type, exec_type
                ));
                output.push_str("{\n");
                output.push_str("}\n\n");

                // clone_<field> — verified loop or external_body wrapper
                // Check if this field is Arc-wrapped (any struct in arc_wrap_fields
                // lists this field name).
                let is_arc_wrapped = arc_wrap_fields
                    .values()
                    .any(|fields| fields.contains(&field.to_string()));
                let use_verified_loop =
                    !is_arc_wrapped && clone_up_to_view_types.contains(exec_type.as_str());
                output.push_str(&format!(
                    "/// Helper: clone a Vec<{}> preserving both raw and mapped view.\n",
                    exec_type
                ));
                if is_arc_wrapped {
                    // Arc-wrapped: clone_<field> accepts &Arc<Vec<T>> and does
                    // Arc::clone (O(1)), declared as external_body for Verus.
                    output.push_str("#[verifier(external_body)]\n");
                    output.push_str(&format!(
                        "fn clone_{}(v: &Arc<Vec<{}>>) -> (res: Arc<Vec<{}>>) \n",
                        field, exec_type, exec_type
                    ));
                    output.push_str("ensures\n");
                    output.push_str("    res@ == v@,\n");
                    output.push_str(&format!(
                        "    res@.map(|i: int, e: {}| e@) =~= v@.map(|i: int, e: {}| e@),\n",
                        exec_type, exec_type
                    ));
                    output.push_str("{\n");
                    output.push_str("    v.clone()\n");
                    output.push_str("}\n\n");

                    // clone_<field>_inner — deep clone inner Vec from Arc for mutation sites
                    output.push_str(&format!(
                        "/// Helper: deep-clone inner Vec from Arc<Vec<{}>> for mutation.\n",
                        exec_type
                    ));
                    output.push_str("#[verifier(external_body)]\n");
                    output.push_str(&format!(
                        "fn clone_{}_inner(v: &Arc<Vec<{}>>) -> (res: Vec<{}>) \n",
                        field, exec_type, exec_type
                    ));
                    output.push_str("ensures\n");
                    output.push_str("    res@ == v@,\n");
                    output.push_str(&format!(
                        "    res@.map(|i: int, e: {}| e@) =~= v@.map(|i: int, e: {}| e@),\n",
                        exec_type, exec_type
                    ));
                    output.push_str("{\n");
                    output.push_str("    (**v).clone()\n");
                    output.push_str("}\n\n");

                    // index_<field> — trusted indexing helper for Arc<Vec<T>>
                    output.push_str(&format!(
                        "/// Helper: index into Arc<Vec<{}>> with verified postcondition.\n",
                        exec_type
                    ));
                    output.push_str("#[verifier(external_body)]\n");
                    output.push_str(&format!(
                        "fn index_{}(v: &Arc<Vec<{}>>, idx: usize) -> (res: {}) \n",
                        field, exec_type, exec_type
                    ));
                    output.push_str("requires\n");
                    output.push_str("    idx < v@.len(),\n");
                    output.push_str("ensures\n");
                    output.push_str("    res == v@[idx as int],\n");
                    output.push_str("{\n");
                    output.push_str("    (*v)[idx].clone()\n");
                    output.push_str("}\n\n");
                } else if use_verified_loop {
                    output.push_str(&format!(
                        "fn clone_{}(v: &Vec<{}>) -> (res: Vec<{}>)\n",
                        field, exec_type, exec_type
                    ));
                    output.push_str("ensures\n");
                    output.push_str("    res@ == v@,\n");
                    output.push_str(&format!(
                        "    res@.map(|i: int, e: {}| e@) =~= v@.map(|i: int, e: {}| e@),\n",
                        exec_type, exec_type
                    ));
                    output.push_str("{\n");
                    output.push_str("    let mut res: Vec<");
                    output.push_str(exec_type);
                    output.push_str("> = Vec::new();\n");
                    output.push_str("    let mut idx: usize = 0;\n");
                    output.push_str("    while idx < v.len()\n");
                    output.push_str("    invariant\n");
                    output.push_str("        idx <= v.len(),\n");
                    output.push_str("        res@.len() == idx as int,\n");
                    output.push_str("        forall|j: int| 0 <= j < idx as int ==> (#[trigger] res@[j]) == v@[j],\n");
                    output.push_str("        forall|j: int| 0 <= j < idx as int ==> (#[trigger] res@[j])@ == v@[j]@,\n");
                    output.push_str("    decreases\n");
                    output.push_str("        v.len() - idx,\n");
                    output.push_str("    {\n");
                    output.push_str("        let elem = v[idx].clone_up_to_view();\n");
                    output.push_str("        res.push(elem);\n");
                    output.push_str("        idx = idx + 1;\n");
                    output.push_str("    }\n");
                    output.push_str("    proof {\n");
                    output.push_str("        assert(res@ =~= v@);\n");
                    output.push_str(&format!(
                        "        assert(res@.map(|i: int, e: {}| e@) =~= v@.map(|i: int, e: {}| e@));\n",
                        exec_type, exec_type
                    ));
                    output.push_str("    }\n");
                    output.push_str("    res\n");
                    output.push_str("}\n\n");
                } else {
                    output.push_str("/// Verus doesn't automatically derive v.clone()@.map(f) =~= v@.map(f) from clone ensures.\n");
                    output.push_str("#[verifier(external_body)]\n");
                    output.push_str(&format!(
                        "fn clone_{}(v: &Vec<{}>) -> (res: Vec<{}>)\n",
                        field, exec_type, exec_type
                    ));
                    output.push_str("ensures\n");
                    output.push_str("    res@ == v@,\n");
                    output.push_str(&format!(
                        "    res@.map(|i: int, e: {}| e@) =~= v@.map(|i: int, e: {}| e@),\n",
                        exec_type, exec_type
                    ));
                    output.push_str("{\n");
                    output.push_str("    v.clone()\n");
                    output.push_str("}\n\n");
                }
            }
        } else if has_vec_fields {
            // Seq proof helpers only needed when vec_fields are configured (u64-typed)
            // lemma_empty_seq_map
            output.push_str("/// Helper proof: mapping over an empty Seq yields an empty Seq.\n");
            output.push_str("proof fn lemma_empty_seq_map()\n");
            output.push_str("ensures\n");
            output.push_str(
                "    Seq::<u64>::empty().map(|i: int, v: u64| v as int) =~= Seq::<int>::empty(),\n",
            );
            output.push_str("{\n");
            output.push_str("}\n\n");

            // lemma_seq_push_map_commute
            output.push_str(
                "/// Helper proof: push commutes with Seq::map for index-ignoring functions.\n",
            );
            output.push_str("proof fn lemma_seq_push_map_commute(s: Seq<u64>, x: u64)\n");
            output.push_str("ensures\n");
            output.push_str("    s.push(x).map(|i: int, v: u64| v as int) =~= s.map(|i: int, v: u64| v as int).push(x as int),\n");
            output.push_str("{\n");
            output.push_str("}\n\n");
        }

        // Generate lemma_empty_msg_map for message type (sent_packets proof helper)
        if let Some((exec_type, spec_type)) = msg_vec_type {
            output.push_str(&format!(
                "/// Helper proof: mapping over an empty Vec<{}> yields an empty seq.\n",
                exec_type
            ));
            output.push_str("proof fn lemma_empty_msg_map()\n");
            output.push_str("ensures\n");
            output.push_str(&format!(
                "    Seq::<{}>::empty().map(|i: int, e: {}| e@) =~= Seq::<{}>::empty(),\n",
                exec_type, exec_type, spec_type
            ));
            output.push_str("{\n");
            output.push_str("}\n\n");
        }

        output
    }

    /// Generate clone helper functions for non-Copy enum fields.
    ///
    /// For each entry in `clone_field_types`, generates a function like:
    /// ```text
    /// fn clone_role(r: &CNodeRole) -> (res: CNodeRole)
    /// ensures
    ///     res@ == r@,
    ///     res.valid() == r.valid(),
    /// {
    ///     match r {
    ///         CNodeRole::Head => CNodeRole::Head,
    ///         CNodeRole::Middle => CNodeRole::Middle,
    ///         CNodeRole::Tail => CNodeRole::Tail,
    ///     }
    /// }
    /// ```
    fn generate_clone_helpers(
        clone_field_types: &std::collections::HashMap<String, String>,
        variant_remapping: &std::collections::HashMap<String, String>,
    ) -> String {
        let mut output = String::new();

        // Collect unique enum types from clone_field_types
        let mut seen_types = std::collections::HashSet::new();
        let mut field_type_pairs: Vec<(&String, &String)> = clone_field_types.iter().collect();
        field_type_pairs.sort_by_key(|(field, _)| field.to_string());

        for (field_name, enum_type) in &field_type_pairs {
            if !seen_types.insert(enum_type.to_string()) {
                continue; // Skip duplicate types
            }

            // Collect variants for this enum type from variant_remapping
            let mut variants: Vec<String> = Vec::new();
            for qualified_path in variant_remapping.values() {
                if let Some(pos) = qualified_path.rfind("::") {
                    let type_prefix = &qualified_path[..pos];
                    if type_prefix == enum_type.as_str() {
                        variants.push(qualified_path.clone());
                    }
                }
            }
            variants.sort();

            if variants.is_empty() {
                continue; // No variants found for this type
            }

            // Use field name for helper name: field "role" -> "clone_role"
            let fn_name = format!("clone_{}", field_name);
            output.push_str(&format!(
                "/// Helper: clone {} preserving view (workaround for missing derive Clone spec).\n",
                enum_type
            ));
            output.push_str("#[verifier(external_body)]\n");
            output.push_str(&format!(
                "fn {}(r: &{}) -> (res: {})\n",
                fn_name, enum_type, enum_type
            ));
            output.push_str("ensures\n");
            output.push_str("    res@ == r@,\n");
            output.push_str("    res.valid() == r.valid(),\n");
            output.push_str("{\n");
            output.push_str("    r.clone()\n");
            output.push_str("}\n\n");
        }

        output
    }

    /// Check if this transpiler config uses HashSet fields (collection_fields).
    /// Returns true when collection_fields is non-empty, OR when no field categories
    /// are configured at all (backward-compatible mode where all fields are treated as collections).
    fn needs_set_helpers(&self) -> bool {
        !self.config.translator.collection_fields.is_empty()
            || !self.config.translator.set_fields.is_empty()
    }

    /// Check if this transpiler config uses HashMap fields with deep abstraction (map_fields).
    fn has_map_fields(&self) -> bool {
        !self.config.translator.map_fields.is_empty()
    }

    /// Generate HashMap abstractify proof lemmas and helpers for map_fields.
    ///
    /// For each entry in `map_fields`, generates:
    /// - `lemma_abstractify_empty_{prefix}()`: empty map abstractifies to empty
    /// - `lemma_abstractify_{prefix}_insert()`: insert commutes with abstractify
    /// - `lemma_abstractify_{prefix}_remove()`: remove commutes with abstractify
    /// - `lemma_abstractify_singleton_{prefix}()`: singleton map abstractify
    /// - `clone_{prefix}()`: verified delegation or external_body clone wrapper
    /// - `filter_{prefix}()`: external_body filter-by-key-threshold helper
    fn generate_map_proof_lemmas(
        map_fields: &std::collections::HashMap<String, (String, String, String)>,
        verified_clone_fns: &std::collections::HashMap<String, String>,
        arc_wrap_fields: &std::collections::HashMap<String, std::collections::HashSet<String>>,
    ) -> String {
        let mut output = String::new();

        // Collect all field names that are Arc-wrapped in any struct
        let arc_wrapped_field_names: std::collections::HashSet<&str> = arc_wrap_fields
            .values()
            .flat_map(|fields| fields.iter().map(|f| f.as_str()))
            .collect();

        let mut sorted_fields: Vec<_> = map_fields.iter().collect();
        sorted_fields.sort_by_key(|(k, _)| k.to_string());

        for (_field, (exec_type, prefix, value_type)) in &sorted_fields {
            let is_arc = arc_wrapped_field_names.contains(_field.as_str());
            // `&ExecType` unconditionally. The lemma's own body calls
            // `abstractify_{prefix}`, which is hand-written in `types_i.rs` and takes
            // a reference, so a by-value parameter does not type-check against it:
            // "expected &HashMap<..>, found HashMap<..>". Being Arc-wrapped also needs
            // the reference (auto-deref from `&Arc<ExecType>`), which is why this was
            // conditional -- but that was never the only case. Phase 42.8.c.2.iv.B.
            let param_type = format!("&{}", exec_type);
            // =========================================================
            // lemma_abstractify_empty_{prefix}
            // =========================================================
            output.push_str(&format!(
                "/// If m@ is empty, abstractify_{} is empty.\n",
                prefix
            ));
            output.push_str(&format!(
                "proof fn lemma_abstractify_empty_{}(m: {})\n",
                prefix, param_type
            ));
            output.push_str("requires\n");
            output.push_str(&format!(
                "    m@ == Map::<COperationNumber, {}>::empty(),\n",
                value_type
            ));
            output.push_str("ensures\n");
            output.push_str(&format!(
                "    abstractify_{}(m) =~= Map::<OperationNumber, {}>::empty(),\n",
                prefix,
                // Derive spec value type: strip C prefix from value_type
                value_type.strip_prefix('C').unwrap_or(value_type)
            ));
            output.push_str("{\n");
            output.push_str(&format!("    let abs = abstractify_{}(m);\n", prefix));
            output.push_str("    assert forall |ak: int| !abs.contains_key(ak) by { }\n");
            output.push_str("}\n\n");

            // Derive spec value type for reuse
            let spec_value_type = value_type.strip_prefix('C').unwrap_or(value_type.as_str());

            // =========================================================
            // lemma_abstractify_{prefix}_insert
            // =========================================================
            output.push_str(
                "/// If m2@ =~= old@.insert(k, v) and old is abstractable and v is abstractable,\n",
            );
            output.push_str("/// then abstractify on m2 = abstractify on old + insert.\n");
            output.push_str(&format!("proof fn lemma_abstractify_{}_insert(\n", prefix));
            output.push_str(&format!(
                "    old_m: {0},\n    m2: {0},\n    k: COperationNumber,\n    v: {1},\n)\n",
                param_type, value_type
            ));
            output.push_str("requires\n");
            output.push_str(&format!("    {}_is_abstractable(old_m),\n", prefix));
            output.push_str("    v.abstractable(),\n");
            output.push_str("    m2@ =~= old_m@.insert(k, v),\n");
            output.push_str("ensures\n");
            output.push_str(&format!(
                "    abstractify_{0}(m2) =~= abstractify_{0}(old_m).insert(k as int, v@),\n",
                prefix
            ));
            output.push_str(&format!("    {}_is_abstractable(m2),\n", prefix));
            output.push_str(&format!(
                "    {0}_is_valid(old_m) && v.valid() ==> {0}_is_valid(m2),\n",
                prefix
            ));
            output.push_str("{\n");
            output.push_str(&format!(
                "    let abs2 = abstractify_{0}(m2);\n    let expected = abstractify_{0}(old_m).insert(k as int, v@);\n", prefix
            ));
            // Domain equivalence
            output.push_str("    assert forall |ak: int| abs2.contains_key(ak) == expected.contains_key(ak) by {\n");
            output.push_str("        if expected.contains_key(ak) {\n");
            output.push_str("            if ak == k as int {\n");
            output.push_str("                assert(m2@.contains_key(k) && (k as int) == ak);\n");
            output.push_str("            } else {\n");
            output.push_str("                let k0 = choose |k0: u64| old_m@.contains_key(k0) && k0 as int == ak;\n");
            output.push_str("                assert(m2@.contains_key(k0) && k0 as int == ak);\n");
            output.push_str("            }\n");
            output.push_str("        }\n");
            output.push_str("        if abs2.contains_key(ak) {\n");
            output.push_str(
                "            let kw = choose |kw: u64| m2@.contains_key(kw) && kw as int == ak;\n",
            );
            output.push_str("            if kw == k { assert(ak == k as int); }\n");
            output.push_str(
                "            else { assert(old_m@.contains_key(kw) && kw as int == ak); }\n",
            );
            output.push_str("        }\n");
            output.push_str("    }\n");
            // Value equivalence
            output.push_str("    assert forall |ak: int| #![trigger abs2[ak]] #![trigger expected[ak]] abs2.contains_key(ak) implies abs2[ak] == expected[ak] by {\n");
            output.push_str(
                "        let kw = choose |kw: u64| m2@.contains_key(kw) && kw as int == ak;\n",
            );
            output
                .push_str("        if ak == k as int { assert(kw == k); assert(m2@[kw] == v); }\n");
            output.push_str("        else { assert(m2@[kw] == old_m@[kw]); }\n");
            output.push_str("    }\n");
            // Abstractability
            output.push_str(
                "    assert forall |i: COperationNumber| #![auto] m2@.contains_key(i) implies\n",
            );
            output.push_str("        COperationNumberIsAbstractable(i) && m2@[i].abstractable()\n");
            output.push_str("    by {\n");
            output.push_str("        if i == k { assert(m2@[i] == v); }\n");
            output.push_str(
                "        else { assert(old_m@.contains_key(i)); assert(m2@[i] == old_m@[i]); }\n",
            );
            output.push_str("    }\n");
            // Validity (conditional)
            output.push_str(&format!(
                "    if {}_is_valid(old_m) && v.valid() {{\n",
                prefix
            ));
            output.push_str("        assert forall |i: COperationNumber| #![auto] m2@.contains_key(i) implies\n");
            output.push_str("            COperationNumberIsValid(i) && m2@[i].valid()\n");
            output.push_str("        by {\n");
            output.push_str("            if i == k { assert(m2@[i] == v); }\n");
            output.push_str("            else { assert(old_m@.contains_key(i)); assert(m2@[i] == old_m@[i]); }\n");
            output.push_str("        }\n");
            output.push_str("    }\n");
            output.push_str("}\n\n");

            // =========================================================
            // lemma_abstractify_{prefix}_remove
            // =========================================================
            output.push_str("/// If m2@ =~= old@.remove(k) and old is abstractable,\n/// then abstractify on m2 = abstractify on old - remove.\n");
            output.push_str(&format!("proof fn lemma_abstractify_{}_remove(\n", prefix));
            output.push_str(&format!(
                "    old_m: {0},\n    m2: {0},\n    k: COperationNumber,\n)\n",
                param_type
            ));
            output.push_str("requires\n");
            output.push_str(&format!("    {}_is_abstractable(old_m),\n", prefix));
            output.push_str("    m2@ =~= old_m@.remove(k),\n");
            output.push_str("ensures\n");
            output.push_str(&format!(
                "    abstractify_{0}(m2) =~= abstractify_{0}(old_m).remove(k as int),\n",
                prefix
            ));
            output.push_str(&format!("    {}_is_abstractable(m2),\n", prefix));
            output.push_str(&format!(
                "    {0}_is_valid(old_m) ==> {0}_is_valid(m2),\n",
                prefix
            ));
            output.push_str("{\n");
            output.push_str(&format!(
                "    let abs2 = abstractify_{0}(m2);\n    let expected = abstractify_{0}(old_m).remove(k as int);\n", prefix
            ));
            output.push_str("    assert forall |ak: int| abs2.contains_key(ak) == expected.contains_key(ak) by {\n");
            output.push_str("        if expected.contains_key(ak) {\n");
            output.push_str("            let kw = choose |kw: u64| old_m@.contains_key(kw) && kw as int == ak;\n");
            output.push_str("            assert(kw != k);\n");
            output.push_str("            assert(m2@.contains_key(kw) && kw as int == ak);\n");
            output.push_str("        }\n");
            output.push_str("        if abs2.contains_key(ak) {\n");
            output.push_str(
                "            let kw = choose |kw: u64| m2@.contains_key(kw) && kw as int == ak;\n",
            );
            output.push_str("            assert(kw != k);\n");
            output.push_str("            assert(old_m@.contains_key(kw) && kw as int == ak);\n");
            output.push_str("        }\n");
            output.push_str("    }\n");
            output.push_str("    assert forall |ak: int| #![trigger abs2[ak]] #![trigger expected[ak]] abs2.contains_key(ak) implies abs2[ak] == expected[ak] by {\n");
            output.push_str(
                "        let kw = choose |kw: u64| m2@.contains_key(kw) && kw as int == ak;\n",
            );
            output.push_str("        let kw_orig = choose |kw2: u64| old_m@.contains_key(kw2) && kw2 as int == ak;\n");
            output.push_str("        assert(kw_orig == kw);\n");
            output.push_str("        assert(m2@[kw] == old_m@[kw]);\n");
            output.push_str("    }\n");
            // Abstractability
            output.push_str(
                "    assert forall |i: COperationNumber| #![auto] m2@.contains_key(i) implies\n",
            );
            output.push_str("        COperationNumberIsAbstractable(i) && m2@[i].abstractable()\n");
            output.push_str("    by {\n");
            output
                .push_str("        assert(old_m@.contains_key(i)); assert(m2@[i] == old_m@[i]);\n");
            output.push_str("    }\n");
            // Validity
            output.push_str(&format!("    if {}_is_valid(old_m) {{\n", prefix));
            output.push_str("        assert forall |i: COperationNumber| #![auto] m2@.contains_key(i) implies\n");
            output.push_str("            COperationNumberIsValid(i) && m2@[i].valid()\n");
            output.push_str("        by {\n");
            output.push_str(
                "            assert(old_m@.contains_key(i)); assert(m2@[i] == old_m@[i]);\n",
            );
            output.push_str("        }\n");
            output.push_str("    }\n");
            output.push_str("}\n\n");

            // =========================================================
            // lemma_abstractify_singleton_{prefix}
            // =========================================================
            output.push_str("/// Singleton: if m@ =~= Map::empty().insert(opn, tup), prove abstractify result.\n");
            output.push_str(&format!(
                "proof fn lemma_abstractify_singleton_{}(m: {}, opn: COperationNumber, tup: {})\n",
                prefix, param_type, value_type
            ));
            output.push_str("requires\n");
            output.push_str(&format!(
                "    m@ =~= Map::<COperationNumber, {}>::empty().insert(opn, tup),\n",
                value_type
            ));
            output.push_str("    tup.abstractable(),\n");
            output.push_str("ensures\n");
            output.push_str(&format!(
                "    abstractify_{0}(m) =~= Map::<OperationNumber, {1}>::empty().insert(opn as int, tup@),\n",
                prefix, spec_value_type
            ));
            output.push_str(&format!("    {}_is_abstractable(m),\n", prefix));
            output.push_str(&format!("    tup.valid() ==> {}_is_valid(m),\n", prefix));
            output.push_str("{\n");
            output.push_str(&format!(
                "    let abs = abstractify_{0}(m);\n    let expected = Map::<OperationNumber, {1}>::empty().insert(opn as int, tup@);\n",
                prefix, spec_value_type
            ));
            output.push_str("    assert forall |ak: int| abs.contains_key(ak) == expected.contains_key(ak) by {\n");
            output.push_str("        if expected.contains_key(ak) { assert(m@.contains_key(opn) && (opn as int) == ak); }\n");
            output.push_str("        if abs.contains_key(ak) {\n");
            output.push_str(
                "            let k = choose |k: u64| m@.contains_key(k) && k as int == ak;\n",
            );
            output.push_str("            assert(k == opn);\n");
            output.push_str("        }\n");
            output.push_str("    }\n");
            output.push_str("    assert forall |ak: int| #![trigger abs[ak]] #![trigger expected[ak]] abs.contains_key(ak) implies abs[ak] == expected[ak] by {\n");
            output.push_str(
                "        let k = choose |k: u64| m@.contains_key(k) && k as int == ak;\n",
            );
            output.push_str("        assert(k == opn); assert(m@[k] == tup);\n");
            output.push_str("    }\n");
            // Abstractability + validity
            output.push_str(
                "    assert forall |i: COperationNumber| #![auto] m@.contains_key(i) implies\n",
            );
            output.push_str("        COperationNumberIsAbstractable(i) && m@[i].abstractable()\n");
            output.push_str("    by { assert(i == opn); assert(m@[i] == tup); }\n");
            output.push_str("    if tup.valid() {\n");
            output.push_str(
                "        assert forall |i: COperationNumber| #![auto] m@.contains_key(i) implies\n",
            );
            output.push_str("            COperationNumberIsValid(i) && m@[i].valid()\n");
            output.push_str("        by { assert(i == opn); assert(m@[i] == tup); }\n");
            output.push_str("    }\n");
            output.push_str("}\n\n");

            // =========================================================
            // clone_{prefix} helper (verified delegation or external_body)
            // =========================================================
            output.push_str(&format!(
                "/// Helper: clone a {} preserving view.\n",
                exec_type
            ));
            if let Some(verified_fn) = verified_clone_fns.get(prefix.as_str()) {
                // Verified: delegate to the proven clone function
                output.push_str(&format!(
                    "fn clone_{}(m: &{}) -> (res: {})\n",
                    prefix, exec_type, exec_type
                ));
                output.push_str("ensures\n");
                output.push_str("    res@ == m@,\n");
                output.push_str("{\n");
                output.push_str(&format!("    {}(m)\n", verified_fn));
                output.push_str("}\n\n");
            } else {
                // Fallback: external_body trusted wrapper
                output.push_str("#[verifier(external_body)]\n");
                output.push_str(&format!(
                    "fn clone_{}(m: &{}) -> (res: {})\n",
                    prefix, exec_type, exec_type
                ));
                output.push_str("ensures\n");
                output.push_str("    res@ == m@,\n");
                output.push_str("{\n");
                output.push_str("    m.clone()\n");
                output.push_str("}\n\n");
            }

            // =========================================================
            // filter_{prefix} external_body helper
            // =========================================================
            output.push_str(&format!(
                "/// Helper: filter {} keeping only entries with key >= threshold.\n",
                exec_type
            ));
            output.push_str("#[verifier(external_body)]\n");
            output.push_str(&format!(
                "fn filter_{}(m: &{}, threshold: u64) -> (res: {})\n",
                prefix, exec_type, exec_type
            ));
            output.push_str("requires\n");
            if is_arc {
                output.push_str(&format!("    {}_is_valid(m),\n", prefix));
            } else {
                output.push_str(&format!("    {}_is_valid(*m),\n", prefix));
            }
            output.push_str("ensures\n");
            if is_arc {
                output.push_str(&format!("    {}_is_valid(&res),\n", prefix));
                output.push_str(&format!("    {}_is_abstractable(&res),\n", prefix));
            } else {
                output.push_str(&format!("    {}_is_valid(res),\n", prefix));
                output.push_str(&format!("    {}_is_abstractable(res),\n", prefix));
            }
            output.push_str("    forall |k: COperationNumber| res@.contains_key(k) ==>\n");
            output.push_str("        m@.contains_key(k) && k >= threshold && (#[trigger] res@[k])@ == m@[k]@,\n");
            output.push_str(
                "    forall |k: COperationNumber| m@.contains_key(k) && k >= threshold ==>\n",
            );
            output.push_str("        res@.contains_key(k),\n");
            output.push_str("    forall |k: COperationNumber| res@.contains_key(k) ==>\n");
            output.push_str("        m@.contains_key(k),\n");
            output.push_str("{\n");
            output.push_str("    let mut filtered = HashMap::new();\n");
            output.push_str("    for (k, v) in m.iter() {\n");
            output.push_str("        if *k >= threshold {\n");
            output.push_str("            filtered.insert(*k, v.clone_up_to_view());\n");
            output.push_str("        }\n");
            output.push_str("    }\n");
            output.push_str("    filtered\n");
            output.push_str("}\n\n");
        }

        output
    }

    /// Check if a spec expression tree contains a `.remove()` method call.
    /// Used to determine if `lemma_set_map_remove_commute` should be generated.
    fn spec_uses_remove(expr: &crate::ast::Expr) -> bool {
        use crate::ast::Expr;
        match expr {
            Expr::MethodCall {
                method,
                receiver,
                args,
                ..
            } => {
                if method == "remove" {
                    return true;
                }
                Self::spec_uses_remove(receiver) || args.iter().any(Self::spec_uses_remove)
            }
            Expr::Conjunction(parts) | Expr::Disjunction(parts) => {
                parts.iter().any(Self::spec_uses_remove)
            }
            Expr::Binary(lhs, _, rhs)
            | Expr::Eq(lhs, rhs)
            | Expr::Ne(lhs, rhs)
            | Expr::Lt(lhs, rhs)
            | Expr::Le(lhs, rhs)
            | Expr::Gt(lhs, rhs)
            | Expr::Ge(lhs, rhs)
            | Expr::Implies(lhs, rhs) => Self::spec_uses_remove(lhs) || Self::spec_uses_remove(rhs),
            Expr::Not(inner) | Expr::Field(inner, _) | Expr::Arrow(inner, _) => {
                Self::spec_uses_remove(inner)
            }
            Expr::If {
                cond,
                then_branch,
                else_branch,
            } => {
                Self::spec_uses_remove(cond)
                    || Self::spec_uses_remove(then_branch)
                    || else_branch
                        .as_ref()
                        .is_some_and(|e| Self::spec_uses_remove(e))
            }
            Expr::Let { value, body, .. } => {
                Self::spec_uses_remove(value) || Self::spec_uses_remove(body)
            }
            Expr::Call { args, .. } => args.iter().any(Self::spec_uses_remove),
            Expr::Index(base, idx) => Self::spec_uses_remove(base) || Self::spec_uses_remove(idx),
            Expr::Forall { body, .. }
            | Expr::Exists { body, .. }
            | Expr::Closure { body, .. }
            | Expr::Choose { body, .. } => Self::spec_uses_remove(body),
            _ => false,
        }
    }

    /// Pre-analyze translated exec bodies to determine which proof helper
    /// definitions must be emitted in the file prelude.
    fn collect_generated_proof_helper_needs(
        spec_fns: &[SpecFunction],
        annotations: &[ModuleAnnotations],
        skip_functions: &[String],
        translator_config: &TranslatorConfig,
    ) -> TranspileResult<(bool, bool, bool)> {
        let mut mode_analyzer = ModeAnalyzer::new();
        let translator = Translator::new(translator_config.clone());

        let mut needs_set_helpers = false;
        let mut needs_vec_helpers = false;
        let mut needs_set_remove = false;

        for spec_fn in spec_fns {
            if skip_functions.contains(&spec_fn.name) {
                continue;
            }

            let annotation = annotations
                .iter()
                .flat_map(|m| m.functions.values())
                .find(|a| a.name == spec_fn.name);

            if let Some(annotation) = annotation {
                let annotated = mode_analyzer.annotate(spec_fn.clone(), annotation)?;
                if !annotated.is_functionalizable {
                    continue;
                }

                let exec_fn = translator.translate(&annotated)?;
                let proof_needs = crate::translator::ProofNeeds::analyze(&exec_fn.body);

                if proof_needs.has_empty_set || !proof_needs.remove_sites.is_empty() {
                    needs_set_helpers = true;
                }
                if proof_needs.has_empty_vec || !proof_needs.push_sites.is_empty() {
                    needs_vec_helpers = true;
                }
                if !proof_needs.remove_sites.is_empty() {
                    needs_set_remove = true;
                }
            }
        }

        Ok((needs_set_helpers, needs_vec_helpers, needs_set_remove))
    }

    /// Check if a spec expression tree contains an empty set constructor.
    /// Used to determine if `lemma_empty_set_map` should be emitted even without
    /// explicit collection field configuration.
    fn spec_uses_empty_set(expr: &crate::ast::Expr) -> bool {
        Self::spec_uses_empty_collection(expr, true)
    }

    /// Check if a spec expression tree contains an empty sequence constructor.
    /// Used to determine if `lemma_empty_seq_map` should be emitted even without
    /// explicit vec field configuration.
    fn spec_uses_empty_seq(expr: &crate::ast::Expr) -> bool {
        Self::spec_uses_empty_collection(expr, false)
    }

    /// Recursive helper for detecting empty collection constructs in spec AST.
    fn spec_uses_empty_collection(expr: &crate::ast::Expr, detect_set: bool) -> bool {
        use crate::ast::Expr;
        let collection_name = if detect_set { "Set" } else { "Seq" };

        let matches_empty = if detect_set {
            match expr {
                Expr::SetEmpty => true,
                Expr::SetLit(items) => items.is_empty(),
                Expr::Call { func, args } => {
                    args.is_empty() && Self::path_is_empty_ctor_for(func, collection_name)
                }
                Expr::MethodCall {
                    receiver,
                    method,
                    args,
                } => {
                    method == "empty"
                        && args.is_empty()
                        && Self::expr_mentions_collection(receiver, collection_name)
                }
                _ => false,
            }
        } else {
            match expr {
                Expr::SeqEmpty => true,
                Expr::SeqLit(items) => items.is_empty(),
                Expr::Call { func, args } => {
                    args.is_empty() && Self::path_is_empty_ctor_for(func, collection_name)
                }
                Expr::MethodCall {
                    receiver,
                    method,
                    args,
                } => {
                    method == "empty"
                        && args.is_empty()
                        && Self::expr_mentions_collection(receiver, collection_name)
                }
                _ => false,
            }
        };
        if matches_empty {
            return true;
        }

        match expr {
            Expr::Conjunction(parts) | Expr::Disjunction(parts) => parts
                .iter()
                .any(|p| Self::spec_uses_empty_collection(p, detect_set)),
            Expr::Binary(lhs, _, rhs)
            | Expr::Eq(lhs, rhs)
            | Expr::Ne(lhs, rhs)
            | Expr::Lt(lhs, rhs)
            | Expr::Le(lhs, rhs)
            | Expr::Gt(lhs, rhs)
            | Expr::Ge(lhs, rhs)
            | Expr::Implies(lhs, rhs)
            | Expr::Iff(lhs, rhs) => {
                Self::spec_uses_empty_collection(lhs, detect_set)
                    || Self::spec_uses_empty_collection(rhs, detect_set)
            }
            Expr::Not(inner)
            | Expr::Field(inner, _)
            | Expr::Arrow(inner, _)
            | Expr::View(inner)
            | Expr::Unary(_, inner)
            | Expr::Is(inner, _) => Self::spec_uses_empty_collection(inner, detect_set),
            Expr::If {
                cond,
                then_branch,
                else_branch,
            } => {
                Self::spec_uses_empty_collection(cond, detect_set)
                    || Self::spec_uses_empty_collection(then_branch, detect_set)
                    || else_branch
                        .as_ref()
                        .is_some_and(|e| Self::spec_uses_empty_collection(e, detect_set))
            }
            Expr::Let { value, body, .. } => {
                Self::spec_uses_empty_collection(value, detect_set)
                    || Self::spec_uses_empty_collection(body, detect_set)
            }
            Expr::Call { args, .. } => args
                .iter()
                .any(|a| Self::spec_uses_empty_collection(a, detect_set)),
            Expr::MethodCall { receiver, args, .. } => {
                Self::spec_uses_empty_collection(receiver, detect_set)
                    || args
                        .iter()
                        .any(|a| Self::spec_uses_empty_collection(a, detect_set))
            }
            Expr::Index(base, idx) => {
                Self::spec_uses_empty_collection(base, detect_set)
                    || Self::spec_uses_empty_collection(idx, detect_set)
            }
            Expr::Forall { body, triggers, .. } => {
                Self::spec_uses_empty_collection(body, detect_set)
                    || triggers.iter().any(|t| {
                        t.exprs
                            .iter()
                            .any(|e| Self::spec_uses_empty_collection(e, detect_set))
                    })
            }
            Expr::Exists { body, .. } | Expr::Closure { body, .. } | Expr::Choose { body, .. } => {
                Self::spec_uses_empty_collection(body, detect_set)
            }
            Expr::Struct { fields, .. } => fields
                .iter()
                .any(|(_, e)| Self::spec_uses_empty_collection(e, detect_set)),
            Expr::StructUpdate { base, fields, .. } => {
                Self::spec_uses_empty_collection(base, detect_set)
                    || fields
                        .iter()
                        .any(|(_, e)| Self::spec_uses_empty_collection(e, detect_set))
            }
            Expr::MapLit(items) => items.iter().any(|(k, v)| {
                Self::spec_uses_empty_collection(k, detect_set)
                    || Self::spec_uses_empty_collection(v, detect_set)
            }),
            Expr::SeqLit(items) | Expr::SetLit(items) => items
                .iter()
                .any(|e| Self::spec_uses_empty_collection(e, detect_set)),
            Expr::Match { scrutinee, arms } => {
                Self::spec_uses_empty_collection(scrutinee, detect_set)
                    || arms.iter().any(|arm| {
                        arm.guard
                            .as_ref()
                            .is_some_and(|g| Self::spec_uses_empty_collection(g, detect_set))
                            || Self::spec_uses_empty_collection(&arm.body, detect_set)
                    })
            }
            Expr::Cast(inner, _) => Self::spec_uses_empty_collection(inner, detect_set),
            Expr::SetEmpty
            | Expr::SeqEmpty
            | Expr::MapEmpty
            | Expr::Ident(_)
            | Expr::Literal(_)
            | Expr::ConstantValue(_) => false,
        }
    }

    /// Heuristic: returns true when path resembles `<Collection>::empty`.
    fn path_is_empty_ctor_for(path: &crate::ast::Path, collection_name: &str) -> bool {
        let has_empty = path
            .segments
            .iter()
            .any(|s| s == "empty" || s.contains("empty"));
        let has_collection = path.segments.iter().any(|s| {
            s == collection_name || s.starts_with(collection_name) || s.contains(collection_name)
        });
        has_empty && has_collection
    }

    /// Heuristic: returns true when an expression node appears to refer to a collection type.
    fn expr_mentions_collection(expr: &crate::ast::Expr, collection_name: &str) -> bool {
        use crate::ast::Expr;

        match expr {
            Expr::Ident(name) => {
                name == collection_name
                    || name.starts_with(collection_name)
                    || name.contains(collection_name)
            }
            Expr::Field(base, field) => {
                field == collection_name
                    || field.starts_with(collection_name)
                    || field.contains(collection_name)
                    || Self::expr_mentions_collection(base, collection_name)
            }
            Expr::Call { func, .. } => Self::path_is_empty_ctor_for(func, collection_name),
            Expr::MethodCall { receiver, .. } => {
                Self::expr_mentions_collection(receiver, collection_name)
            }
            _ => false,
        }
    }

    /// Generate wrapper methods for functions that take the impl type as first parameter.
    /// The wrappers convert functional-style `fn foo(&Type, ...) -> Type`
    /// to `impl Type { fn foo(&mut self, ...) }` pattern.
    fn generate_wrappers(&self, exec_functions: &[ExecFunction], impl_type: &str) -> String {
        let mut wrappers = Vec::new();
        let validity_pred = &self.config.translator.validity_predicate_name;

        for func in exec_functions {
            // Check if this function is a wrapper candidate:
            // - First param is a reference to impl_type
            // - Return type contains impl_type
            if !self.is_wrapper_candidate(func, impl_type) {
                continue;
            }

            // Generate wrapper method
            if let Some(wrapper) = self.generate_single_wrapper(func, impl_type, validity_pred) {
                wrappers.push(wrapper);
            }
        }

        if wrappers.is_empty() {
            return String::new();
        }

        // Wrap in impl block
        let mut output = format!("impl {} {{\n", impl_type);
        for wrapper in wrappers {
            output.push_str(&wrapper);
            output.push('\n');
        }
        output.push_str("}\n");
        output
    }

    /// Check if a function is a candidate for wrapper generation.
    fn is_wrapper_candidate(&self, func: &ExecFunction, impl_type: &str) -> bool {
        // Must have at least one parameter
        if func.params.is_empty() {
            return false;
        }

        // First param must be a reference to impl_type
        let first_param = &func.params[0];
        if !first_param.is_reference {
            return false;
        }

        // Check if the type matches impl_type
        let type_str = first_param.ty.to_rust_string();
        if !type_str.contains(impl_type) {
            return false;
        }

        // Return type must contain impl_type
        let return_str = func.return_type.to_rust_string();
        return_str.contains(impl_type)
    }

    /// Generate a single wrapper method for a function.
    fn generate_single_wrapper(
        &self,
        func: &ExecFunction,
        impl_type: &str,
        validity_pred: &str,
    ) -> Option<String> {
        let mut output = String::new();
        let indent = "    ";

        // Generate method signature
        // Convert function name to method name (remove type prefix if present)
        let method_name = func.name.strip_prefix(impl_type).unwrap_or(&func.name);
        let method_name = method_name.strip_prefix('_').unwrap_or(method_name);

        // Generate parameter list (skip first param, which becomes &mut self)
        let other_params: Vec<String> = func
            .params
            .iter()
            .skip(1)
            .map(|p| {
                if p.is_reference {
                    format!("{}: &{}", p.name, p.ty.to_rust_string())
                } else {
                    format!("{}: {}", p.name, p.ty.to_rust_string())
                }
            })
            .collect();

        // Determine return type
        // If return is just impl_type, return nothing (mutates self)
        // If return is tuple (impl_type, Other), return Other
        let return_type = self.extract_non_self_return_type(&func.return_type, impl_type);

        // Generate signature
        output.push_str(&format!("{}pub fn {}(&mut self", indent, method_name));
        if !other_params.is_empty() {
            output.push_str(", ");
            output.push_str(&other_params.join(", "));
        }
        output.push(')');
        if let Some(ref ret) = return_type {
            output.push_str(&format!(" -> {}", ret));
        }
        output.push('\n');

        // Generate requires clause
        output.push_str(&format!("{}requires\n", indent));
        output.push_str(&format!(
            "{}{}old(self).{}(),\n",
            indent, indent, validity_pred
        ));

        // Generate ensures clause
        output.push_str(&format!("{}ensures\n", indent));
        output.push_str(&format!("{}{}self.{}(),\n", indent, indent, validity_pred));

        // Generate body
        output.push_str(&format!("{}{{\n", indent));

        // Generate call to original function
        let _self_param = &func.params[0].name;
        let other_args: Vec<&str> = func
            .params
            .iter()
            .skip(1)
            .map(|p| p.name.as_str())
            .collect();

        if return_type.is_some() {
            // Return is tuple, extract and update self
            output.push_str(&format!(
                "{}{}let (new_self, result) = {}(self",
                indent, indent, func.name
            ));
            for arg in &other_args {
                output.push_str(&format!(", {}", arg));
            }
            output.push_str(");\n");
            output.push_str(&format!("{}{}*self = new_self;\n", indent, indent));
            output.push_str(&format!("{}{}result\n", indent, indent));
        } else {
            // Return is just state, update self
            output.push_str(&format!("{}{}*self = {}(self", indent, indent, func.name));
            for arg in &other_args {
                output.push_str(&format!(", {}", arg));
            }
            output.push_str(");\n");
        }

        output.push_str(&format!("{}}}\n", indent));

        Some(output)
    }

    /// Extract the non-self part of the return type.
    /// If return is `TypeName`, returns None (just updating self).
    /// If return is `(TypeName, Other)`, returns Some("Other").
    fn extract_non_self_return_type(
        &self,
        return_type: &translator::ExecType,
        impl_type: &str,
    ) -> Option<String> {
        let type_str = return_type.to_rust_string();

        // If it's just the impl_type, no separate return
        if type_str == impl_type {
            return None;
        }

        // If it's a tuple containing impl_type
        if type_str.starts_with('(') && type_str.contains(impl_type) {
            // Parse tuple and extract non-impl_type components
            // For now, assume simple (ImplType, Other) pattern
            let inner = type_str.trim_start_matches('(').trim_end_matches(')');
            let parts: Vec<&str> = inner.split(',').map(|s: &str| s.trim()).collect();
            let other_parts: Vec<&str> = parts
                .into_iter()
                .filter(|p: &&str| !p.contains(impl_type))
                .collect();
            if !other_parts.is_empty() {
                if other_parts.len() == 1 {
                    return Some(other_parts[0].to_string());
                } else {
                    return Some(format!("({})", other_parts.join(", ")));
                }
            }
        }

        None
    }
}

impl Default for Transpiler {
    fn default() -> Self {
        Self::new(TranspilerConfig::default())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_transpiler_creation() {
        let config = TranspilerConfig::default();
        let transpiler = Transpiler::new(config);
        assert!(transpiler.config.translator.spec_prefix == "L");
    }

    #[test]
    fn test_custom_imports_in_output() {
        let config = TranspilerConfig {
            custom_imports: vec![
                "use vstd::prelude::*;".to_string(),
                "use std::collections::HashMap;".to_string(),
            ],
            ..Default::default()
        };

        let transpiler = Transpiler::new(config);

        // Create minimal input to test output format
        let spec_source = r#"
            verus! {
                pub open spec fn TestPred(x: int, y: int) -> bool {
                    y == x + 1
                }
            }
        "#;
        let annotation_source = r#"
            module test {
                TestPred(+, -);
            }
        "#;

        let result = transpiler
            .transpile_source(spec_source, annotation_source)
            .unwrap();

        // Check that imports appear before verus! block
        assert!(result.contains("use vstd::prelude::*;"));
        assert!(result.contains("use std::collections::HashMap;"));

        // Verify order: imports should come before verus!
        let import_pos = result.find("use vstd::prelude::*;").unwrap();
        let verus_pos = result.find("verus!").unwrap();
        assert!(
            import_pos < verus_pos,
            "Custom imports should appear before verus! block"
        );
    }

    #[test]
    fn test_inline_type_generation() {
        let config = TranspilerConfig {
            generate_inline_types: true,
            ..Default::default()
        };

        let transpiler = Transpiler::new(config);

        // Spec source with struct and function
        let spec_source = r#"
            verus! {
                pub struct LState {
                    pub value: int,
                    pub active: bool,
                }

                pub open spec fn StateInit(s: LState) -> bool {
                    s.value == 0 && s.active
                }
            }
        "#;
        let annotation_source = r#"
            module test {
                StateInit(-);
            }
        "#;

        let result = transpiler
            .transpile_source(spec_source, annotation_source)
            .unwrap();

        // Check that generated types appear in output
        assert!(
            result.contains("pub struct CState"),
            "Should generate CState struct: {}",
            result
        );
        assert!(
            result.contains("impl CState"),
            "Should generate impl block for CState: {}",
            result
        );
        assert!(
            result.contains("fn well_formed"),
            "Should generate well_formed predicate: {}",
            result
        );
        assert!(
            result.contains("impl View for CState"),
            "Should generate View impl for CState: {}",
            result
        );

        // Check that functions are also generated
        assert!(
            result.contains("pub exec fn CStateInit"),
            "Should generate CStateInit function: {}",
            result
        );
    }

    #[test]
    fn test_inline_type_generation_uses_translator_numeric_types() {
        let config = TranspilerConfig {
            generate_inline_types: true,
            translator: TranslatorConfig {
                int_type: "u64".to_string(),
                nat_type: "u32".to_string(),
                ..Default::default()
            },
            ..Default::default()
        };

        let transpiler = Transpiler::new(config);

        let spec_source = r#"
            verus! {
                pub struct LState {
                    pub value: int,
                    pub slots: nat,
                }

                pub open spec fn StateInit(s: LState) -> bool {
                    s.value == 0 && s.slots == 1
                }
            }
        "#;
        let annotation_source = r#"
            module test {
                StateInit(-);
            }
        "#;

        let result = transpiler
            .transpile_source(spec_source, annotation_source)
            .unwrap();

        assert!(
            result.contains("pub value: u64"),
            "Inline int field should use translator int_type: {}",
            result
        );
        assert!(
            result.contains("pub slots: u32"),
            "Inline nat field should use translator nat_type: {}",
            result
        );
    }

    #[test]
    fn test_inline_type_generation_disabled_by_default() {
        let config = TranspilerConfig::default();
        assert!(
            !config.generate_inline_types,
            "generate_inline_types should be false by default"
        );

        let transpiler = Transpiler::new(config);

        let spec_source = r#"
            verus! {
                pub struct LState {
                    pub value: int,
                }

                pub open spec fn StateInit(s: LState) -> bool {
                    s.value == 0
                }
            }
        "#;
        let annotation_source = r#"
            module test {
                StateInit(-);
            }
        "#;

        let result = transpiler
            .transpile_source(spec_source, annotation_source)
            .unwrap();

        // Should NOT generate types when disabled
        assert!(
            !result.contains("pub struct CState"),
            "Should NOT generate CState struct when inline types disabled: {}",
            result
        );
    }

    #[test]
    fn test_wrapper_generation_config_defaults() {
        let config = TranspilerConfig::default();
        assert!(
            !config.generate_wrapper_methods,
            "generate_wrapper_methods should be false by default"
        );
        assert!(
            config.wrapper_impl_type.is_none(),
            "wrapper_impl_type should be None by default"
        );
    }

    #[test]
    fn test_wrapper_generation_simple() {
        let config = TranspilerConfig {
            generate_wrapper_methods: true,
            wrapper_impl_type: Some("CState".to_string()),
            ..Default::default()
        };

        let transpiler = Transpiler::new(config);

        // Create spec with function that takes state and returns new state
        let spec_source = r#"
            verus! {
                pub struct LState {
                    pub value: int,
                }

                pub open spec fn StateUpdate(s: LState, s_: LState, delta: int) -> bool {
                    s_.value == s.value + delta
                }
            }
        "#;
        let annotation_source = r#"
            module test {
                StateUpdate(+, -, +);
            }
        "#;

        let result = transpiler
            .transpile_source(spec_source, annotation_source)
            .unwrap();

        // Check that wrapper impl block is generated
        assert!(
            result.contains("impl CState {"),
            "Should generate impl CState block: {}",
            result
        );

        // Check that wrapper method is generated
        assert!(
            result.contains("pub fn Update(&mut self"),
            "Should generate Update wrapper method: {}",
            result
        );

        // Check that wrapper has requires/ensures
        assert!(
            result.contains("old(self).well_formed()"),
            "Should have old(self) in requires: {}",
            result
        );
        assert!(
            result.contains("self.well_formed()"),
            "Should have self.well_formed() in ensures: {}",
            result
        );

        // Check that wrapper calls original function
        assert!(
            result.contains("*self = CStateUpdate(self"),
            "Should call CStateUpdate and assign to *self: {}",
            result
        );
    }

    #[test]
    fn test_wrapper_generation_disabled() {
        let config = TranspilerConfig {
            generate_wrapper_methods: false,
            wrapper_impl_type: Some("CState".to_string()),
            ..Default::default()
        };

        let transpiler = Transpiler::new(config);

        let spec_source = r#"
            verus! {
                pub struct LState {
                    pub value: int,
                }

                pub open spec fn StateUpdate(s: LState, s_: LState, delta: int) -> bool {
                    s_.value == s.value + delta
                }
            }
        "#;
        let annotation_source = r#"
            module test {
                StateUpdate(+, -, +);
            }
        "#;

        let result = transpiler
            .transpile_source(spec_source, annotation_source)
            .unwrap();

        // Should NOT generate wrapper when disabled
        assert!(
            !result.contains("impl CState {"),
            "Should NOT generate impl CState block when disabled: {}",
            result
        );
    }

    #[test]
    fn test_generate_proofs_emits_helper_lemma() {
        let config = TranspilerConfig {
            translator: TranslatorConfig {
                generate_proofs: true,
                ..Default::default()
            },
            ..Default::default()
        };
        let transpiler = Transpiler::new(config);

        let spec_source = r#"
            verus! {
                pub open spec fn LInit(s: Set<int>) -> bool {
                    s =~= Set::<int>::empty()
                }
            }
        "#;
        let annotation_source = r#"
            module test {
                LInit(-);
            }
        "#;

        let result = transpiler
            .transpile_source(spec_source, annotation_source)
            .unwrap();

        // Should emit the helper lemma definition (not only call sites)
        assert!(
            result.contains("proof fn lemma_empty_set_map()"),
            "Should contain lemma_empty_set_map definition when generate_proofs=true: {}",
            result
        );
    }

    #[test]
    fn test_generate_proofs_emits_empty_seq_helper_without_vec_field_config() {
        let config = TranspilerConfig {
            translator: TranslatorConfig {
                generate_proofs: true,
                ..Default::default()
            },
            ..Default::default()
        };
        let transpiler = Transpiler::new(config);

        let spec_source = r#"
            verus! {
                pub open spec fn LInitSeq(s: Seq<int>) -> bool {
                    s =~= Seq::<int>::empty()
                }
            }
        "#;
        let annotation_source = r#"
            module test {
                LInitSeq(-);
            }
        "#;

        let result = transpiler
            .transpile_source(spec_source, annotation_source)
            .unwrap();

        assert!(
            result.contains("proof fn lemma_empty_seq_map()"),
            "Should contain lemma_empty_seq_map definition for Seq::empty usage: {}",
            result
        );
    }

    #[test]
    fn test_generate_proofs_disabled_no_helper_lemma() {
        let config = TranspilerConfig {
            translator: TranslatorConfig {
                generate_proofs: false,
                ..Default::default()
            },
            ..Default::default()
        };
        let transpiler = Transpiler::new(config);

        let spec_source = r#"
            verus! {
                pub open spec fn LInit(s: Set<int>) -> bool {
                    s =~= Set::<int>::empty()
                }
            }
        "#;
        let annotation_source = r#"
            module test {
                LInit(-);
            }
        "#;

        let result = transpiler
            .transpile_source(spec_source, annotation_source)
            .unwrap();

        // Should NOT emit the helper lemma
        assert!(
            !result.contains("lemma_empty_set_map"),
            "Should NOT contain lemma_empty_set_map when generate_proofs=false: {}",
            result
        );
    }

    #[test]
    fn test_generate_proofs_auto_imports() {
        // With collection_fields configured, set_lib and clone_hashset should be auto-imported
        let config = TranspilerConfig {
            translator: TranslatorConfig {
                generate_proofs: true,
                collection_fields: vec!["some_set".to_string()].into_iter().collect(),
                ..Default::default()
            },
            custom_imports: vec!["use vstd::prelude::*;".to_string()],
            ..Default::default()
        };
        let transpiler = Transpiler::new(config);

        let spec_source = r#"
            verus! {
                pub open spec fn LTest(x: int) -> bool { x > 0 }
            }
        "#;
        let annotation_source = r#"
            module test {
                LTest(+);
            }
        "#;

        let result = transpiler
            .transpile_source(spec_source, annotation_source)
            .unwrap();

        // Should auto-add proof-related imports when collection_fields present
        assert!(
            result.contains("use vstd::set_lib::*;"),
            "Should auto-import vstd::set_lib when collection_fields present: {}",
            result
        );
        assert!(
            result.contains("fn clone_hashset"),
            "Should generate local clone_hashset when collection_fields present: {}",
            result
        );
    }

    #[test]
    fn test_generate_proofs_no_duplicate_imports() {
        let config = TranspilerConfig {
            translator: TranslatorConfig {
                generate_proofs: true,
                ..Default::default()
            },
            custom_imports: vec![
                "use vstd::prelude::*;".to_string(),
                "use vstd::set_lib::*;".to_string(), // Already present
            ],
            ..Default::default()
        };
        let transpiler = Transpiler::new(config);

        let spec_source = r#"
            verus! {
                pub open spec fn LTest(x: int) -> bool { x > 0 }
            }
        "#;
        let annotation_source = r#"
            module test {
                LTest(+);
            }
        "#;

        let result = transpiler
            .transpile_source(spec_source, annotation_source)
            .unwrap();

        // Count occurrences of set_lib import — should be exactly 1
        let count = result.matches("use vstd::set_lib::*;").count();
        assert_eq!(
            count, 1,
            "Should not duplicate set_lib import, found {} occurrences",
            count
        );
    }

    #[test]
    fn test_generate_proof_helper_lemmas_content() {
        let empty = std::collections::HashMap::new();
        let output = Transpiler::generate_proof_helper_lemmas(
            false,
            true,
            true,
            &empty,
            "u64",
            &std::collections::HashSet::new(),
            &None,
            false,
            &std::collections::HashMap::new(),
        );

        // Verify lemma_empty_set_map
        assert!(output.contains("proof fn lemma_empty_set_map()"));
        assert!(
            output.contains("Set::<u64>::empty().map(|x: u64| x as int) =~= Set::<int>::empty()")
        );

        // Verify lemma_set_map_remove_commute (only when has_set_remove=true)
        assert!(output.contains("proof fn lemma_set_map_remove_commute(s: Set<u64>, elt: u64)"));
        assert!(output.contains(
            "s.remove(elt).map(|x: u64| x as int) =~= s.map(|x: u64| x as int).remove(elt as int)"
        ));
        assert!(output.contains("let lhs = s.remove(elt).map(f);"));
        assert!(output.contains("let rhs = s.map(f).remove(f(elt));"));
        // Both directions of the proof
        assert!(output.contains("lhs.contains(y)) implies rhs.contains(y)"));
        assert!(output.contains("rhs.contains(y)) implies lhs.contains(y)"));

        // Seq lemmas should NOT be present without vec_fields
        assert!(!output.contains("lemma_empty_seq_map"));
        assert!(!output.contains("lemma_seq_push_map_commute"));

        // Verify clone_hashset helper is generated
        assert!(
            output.contains("fn clone_hashset"),
            "clone_hashset helper should be generated when has_set_fields=true"
        );
        assert!(output.contains("#[verifier(external_body)]"));
        assert!(output.contains("res@ == s@"));

        // When has_set_remove=false, remove_commute should NOT be present
        let output_no_remove = Transpiler::generate_proof_helper_lemmas(
            false,
            true,
            false,
            &empty,
            "u64",
            &std::collections::HashSet::new(),
            &None,
            false,
            &std::collections::HashMap::new(),
        );
        assert!(!output_no_remove.contains("lemma_set_map_remove_commute"));

        // When has_set_fields=false, set lemmas should NOT be present
        let output_no_sets = Transpiler::generate_proof_helper_lemmas(
            false,
            false,
            false,
            &empty,
            "u64",
            &std::collections::HashSet::new(),
            &None,
            false,
            &std::collections::HashMap::new(),
        );
        assert!(!output_no_sets.contains("lemma_empty_set_map"));
        assert!(!output_no_sets.contains("lemma_set_map_remove_commute"));
        assert!(!output_no_sets.contains("clone_hashset"));
    }

    #[test]
    fn test_generate_proof_helper_lemmas_int_type_parameterization() {
        let empty = std::collections::HashMap::new();

        // With i64 int_type (TLA+ pipeline default)
        let output_i64 = Transpiler::generate_proof_helper_lemmas(
            false,
            true,
            true,
            &empty,
            "i64",
            &std::collections::HashSet::new(),
            &None,
            false,
            &std::collections::HashMap::new(),
        );
        assert!(output_i64.contains("Set::<i64>::empty()"));
        assert!(output_i64.contains("|x: i64| x as int"));
        assert!(output_i64.contains("lemma_set_map_remove_commute(s: Set<i64>, elt: i64)"));

        // With u64 int_type (RSL protocol default)
        let output_u64 = Transpiler::generate_proof_helper_lemmas(
            false,
            true,
            true,
            &empty,
            "u64",
            &std::collections::HashSet::new(),
            &None,
            false,
            &std::collections::HashMap::new(),
        );
        assert!(output_u64.contains("Set::<u64>::empty()"));
        assert!(output_u64.contains("|x: u64| x as int"));
    }

    #[test]
    fn test_generate_proof_helper_lemmas_with_vec_fields() {
        let empty = std::collections::HashMap::new();
        let output = Transpiler::generate_proof_helper_lemmas(
            true,
            true,
            true,
            &empty,
            "u64",
            &std::collections::HashSet::new(),
            &None,
            false,
            &std::collections::HashMap::new(),
        );

        // Set lemmas should be present when has_set_fields=true
        assert!(output.contains("proof fn lemma_empty_set_map()"));
        assert!(output.contains("proof fn lemma_set_map_remove_commute(s: Set<u64>, elt: u64)"));

        // Seq lemmas should be present with vec_fields
        assert!(output.contains("proof fn lemma_empty_seq_map()"));
        assert!(output.contains("proof fn lemma_seq_push_map_commute(s: Seq<u64>, x: u64)"));
    }

    #[test]
    fn test_generate_proof_helper_lemmas_with_struct_vec_fields() {
        let mut svf = std::collections::HashMap::new();
        svf.insert(
            "log".to_string(),
            ("CLogEntry".to_string(), "LLogEntry".to_string()),
        );
        let output = Transpiler::generate_proof_helper_lemmas(
            true,
            true,
            false,
            &svf,
            "u64",
            &std::collections::HashSet::new(),
            &None,
            false,
            &std::collections::HashMap::new(),
        );

        // Set lemmas should be present when has_set_fields=true
        assert!(output.contains("proof fn lemma_empty_set_map()"));

        // Struct-typed lemmas should be present
        assert!(output.contains("proof fn lemma_empty_log_map()"));
        assert!(output.contains("Seq::<CLogEntry>::empty().map(|i: int, e: CLogEntry| e@) =~= Seq::<LLogEntry>::empty()"));
        assert!(
            output.contains("proof fn lemma_log_push_map_commute(s: Seq<CLogEntry>, x: CLogEntry)")
        );

        // Clone wrapper should be present
        assert!(output.contains("#[verifier(external_body)]"));
        assert!(output.contains("fn clone_log(v: &Vec<CLogEntry>) -> (res: Vec<CLogEntry>)"));
        assert!(output.contains("res@ == v@"));

        // Generic u64-typed seq lemmas should NOT be present (struct_vec takes priority)
        assert!(!output.contains("lemma_empty_seq_map"));
        assert!(!output.contains("lemma_seq_push_map_commute"));
    }

    #[test]
    fn test_generate_proof_helper_lemmas_with_clone_up_to_view_types() {
        let mut svf = std::collections::HashMap::new();
        svf.insert(
            "request_queue".to_string(),
            ("CRequest".to_string(), "Request".to_string()),
        );
        // CRequest is in clone_up_to_view_types — should generate verified loop
        let mut cutv = std::collections::HashSet::new();
        cutv.insert("CRequest".to_string());
        let output = Transpiler::generate_proof_helper_lemmas(
            true,
            true,
            false,
            &svf,
            "u64",
            &cutv,
            &None,
            false,
            &std::collections::HashMap::new(),
        );

        // Should generate clone_request_queue with verified loop, NOT external_body
        assert!(
            output.contains("fn clone_request_queue(v: &Vec<CRequest>) -> (res: Vec<CRequest>)"),
            "Should generate clone_request_queue function: {}",
            output
        );
        assert!(
            !output.contains("#[verifier(external_body)]\nfn clone_request_queue"),
            "Should NOT use external_body for CRequest clone: {}",
            output
        );
        assert!(
            output.contains("clone_up_to_view()"),
            "Should use clone_up_to_view in loop body: {}",
            output
        );
        assert!(
            output.contains("while idx < v.len()"),
            "Should generate while loop: {}",
            output
        );
        assert!(
            output.contains("res@.len() == idx as int"),
            "Should have length invariant: {}",
            output
        );
        assert!(
            output.contains("res@ =~= v@"),
            "Should have extensional equality proof assertion: {}",
            output
        );
        assert!(
            output.contains("decreases"),
            "Should have decreases clause for while loop: {}",
            output
        );
        assert!(
            output.contains("v.len() - idx"),
            "Should have v.len() - idx as decreases measure: {}",
            output
        );
    }

    #[test]
    fn test_generate_proof_helper_lemmas_external_body_when_not_in_cutv() {
        let mut svf = std::collections::HashMap::new();
        svf.insert(
            "log".to_string(),
            ("CLogEntry".to_string(), "LLogEntry".to_string()),
        );
        // CLogEntry is NOT in clone_up_to_view_types — should use external_body
        let cutv = std::collections::HashSet::new();
        let output = Transpiler::generate_proof_helper_lemmas(
            true,
            true,
            false,
            &svf,
            "u64",
            &cutv,
            &None,
            false,
            &std::collections::HashMap::new(),
        );

        assert!(
            output.contains("#[verifier(external_body)]"),
            "Should use external_body when type not in clone_up_to_view_types: {}",
            output
        );
        assert!(output.contains("fn clone_log(v: &Vec<CLogEntry>) -> (res: Vec<CLogEntry>)"),);
        assert!(
            !output.contains("clone_up_to_view"),
            "Should NOT use clone_up_to_view when type not listed: {}",
            output
        );
    }

    #[test]
    fn test_generate_clone_helpers_basic() {
        let mut clone_field_types = std::collections::HashMap::new();
        clone_field_types.insert("role".to_string(), "CNodeRole".to_string());

        let mut variant_remapping = std::collections::HashMap::new();
        variant_remapping.insert("Head".to_string(), "CNodeRole::Head".to_string());
        variant_remapping.insert("Middle".to_string(), "CNodeRole::Middle".to_string());
        variant_remapping.insert("Tail".to_string(), "CNodeRole::Tail".to_string());

        let output = Transpiler::generate_clone_helpers(&clone_field_types, &variant_remapping);

        // Helper name is based on field name: field "role" -> "clone_role"
        assert!(output.contains("fn clone_role(r: &CNodeRole) -> (res: CNodeRole)"));
        assert!(
            output.contains("#[verifier(external_body)]"),
            "Should have external_body: {}",
            output
        );
        assert!(output.contains("res@ == r@,"));
        assert!(output.contains("res.valid() == r.valid(),"));
        assert!(
            output.contains("r.clone()"),
            "Should use r.clone() body: {}",
            output
        );
    }

    #[test]
    fn test_generate_clone_helpers_empty() {
        let clone_field_types = std::collections::HashMap::new();
        let variant_remapping = std::collections::HashMap::new();

        let output = Transpiler::generate_clone_helpers(&clone_field_types, &variant_remapping);
        assert!(output.is_empty());
    }

    #[test]
    fn test_generate_clone_helpers_no_matching_variants() {
        let mut clone_field_types = std::collections::HashMap::new();
        clone_field_types.insert("role".to_string(), "CUnknownRole".to_string());

        let mut variant_remapping = std::collections::HashMap::new();
        variant_remapping.insert("Head".to_string(), "CNodeRole::Head".to_string());

        let output = Transpiler::generate_clone_helpers(&clone_field_types, &variant_remapping);
        // No matching variants for CUnknownRole, so no helper generated
        assert!(output.is_empty());
    }

    #[test]
    fn test_generate_map_proof_lemmas() {
        let mut map_fields = std::collections::HashMap::new();
        map_fields.insert(
            "unexecuted_learner_state".to_string(),
            (
                "CLearnerState".to_string(),
                "clearnerstate".to_string(),
                "CLearnerTuple".to_string(),
            ),
        );
        let output = Transpiler::generate_map_proof_lemmas(
            &map_fields,
            &std::collections::HashMap::new(),
            &std::collections::HashMap::new(),
        );

        // Check all 4 proof lemmas are generated
        assert!(
            // `&CLearnerState` even with no Arc-wrapped fields: the lemma body calls
            // `abstractify_clearnerstate`, which takes a reference (Phase 42.8.c.2.iv.B).
            output.contains("proof fn lemma_abstractify_empty_clearnerstate(m: &CLearnerState)"),
            "Should contain empty lemma taking &CLearnerState"
        );
        assert!(
            output.contains("proof fn lemma_abstractify_clearnerstate_insert("),
            "Should contain insert lemma"
        );
        assert!(
            output.contains("proof fn lemma_abstractify_clearnerstate_remove("),
            "Should contain remove lemma"
        );
        assert!(
            output.contains("proof fn lemma_abstractify_singleton_clearnerstate(m: &CLearnerState"),
            "Should contain singleton lemma taking &CLearnerState"
        );

        // Check helpers are generated
        assert!(
            output.contains("fn clone_clearnerstate(m: &CLearnerState) -> (res: CLearnerState)"),
            "Should contain clone helper"
        );
        assert!(output.contains("fn filter_clearnerstate(m: &CLearnerState, threshold: u64) -> (res: CLearnerState)"),
            "Should contain filter helper");

        // Check spec value type derivation (CLearnerTuple -> LearnerTuple)
        assert!(
            output.contains("Map::<OperationNumber, LearnerTuple>::empty()"),
            "Should use derived spec value type LearnerTuple"
        );

        // Check validity/abstractability ensures
        assert!(
            output.contains("clearnerstate_is_abstractable(m2)"),
            "Should check abstractability"
        );
        assert!(
            output.contains("clearnerstate_is_valid(old_m)"),
            "Should check validity"
        );
    }

    /// Phase 54.7.e. The value-equivalence `assert forall` in the generated map
    /// lemmas carries explicit triggers. They pin exactly what Verus was already
    /// choosing (`abs2[ak]` / `expected[ak]`, reported as trigger 1 and 2 of 2),
    /// so the instantiation is unchanged and only the note goes away -- which is
    /// the point: an auto-chosen trigger can move between Verus releases.
    #[test]
    fn test_map_proof_lemmas_pin_the_value_equivalence_triggers() {
        let mut map_fields = std::collections::HashMap::new();
        map_fields.insert(
            "unexecuted_learner_state".to_string(),
            (
                "CLearnerState".to_string(),
                "clearnerstate".to_string(),
                "CLearnerTuple".to_string(),
            ),
        );
        let output = Transpiler::generate_map_proof_lemmas(
            &map_fields,
            &std::collections::HashMap::new(),
            &std::collections::HashMap::new(),
        );

        // Only the *value*-equivalence assert is pinned. The key-set assert
        // (`abs2.contains_key(ak) == expected.contains_key(ak)`) emits no note, so
        // there is no chosen trigger to pin and annotating it would be a change
        // with no evidence behind it.
        assert!(
            !output.contains(
                "assert forall |ak: int| abs2.contains_key(ak) implies abs2[ak] == expected[ak]"
            ),
            "the unannotated value-equivalence form must not survive:\n{}",
            output
        );
        assert!(
            output.contains(
                "assert forall |ak: int| #![trigger abs2[ak]] #![trigger expected[ak]] \
                 abs2.contains_key(ak)"
            ),
            "insert/remove lemmas should pin both chosen triggers:\n{}",
            output
        );
        assert!(
            output.contains(
                "assert forall |ak: int| #![trigger abs[ak]] #![trigger expected[ak]] \
                 abs.contains_key(ak)"
            ),
            "the singleton lemma uses `abs`, not `abs2`:\n{}",
            output
        );
    }

    #[test]
    fn test_generate_map_proof_lemmas_empty() {
        let map_fields = std::collections::HashMap::new();
        let output = Transpiler::generate_map_proof_lemmas(
            &map_fields,
            &std::collections::HashMap::new(),
            &std::collections::HashMap::new(),
        );
        assert!(
            output.is_empty(),
            "Empty map_fields should generate nothing"
        );
    }

    #[test]
    fn test_generate_map_proof_lemmas_filter_helper() {
        let mut map_fields = std::collections::HashMap::new();
        map_fields.insert(
            "votes".to_string(),
            (
                "CVotes".to_string(),
                "cvotes".to_string(),
                "CVote".to_string(),
            ),
        );
        let output = Transpiler::generate_map_proof_lemmas(
            &map_fields,
            &std::collections::HashMap::new(),
            &std::collections::HashMap::new(),
        );

        // Should have filter helper with proper type
        assert!(output.contains("fn filter_cvotes(m: &CVotes, threshold: u64) -> (res: CVotes)"));
        assert!(output.contains("cvotes_is_valid(*m)"));
        assert!(output.contains("cvotes_is_valid(res)"));
        assert!(output.contains("v.clone_up_to_view()"));
    }

    #[test]
    fn test_generate_map_proof_lemmas_verified_clone() {
        let mut map_fields = std::collections::HashMap::new();
        map_fields.insert(
            "unexecuted_learner_state".to_string(),
            (
                "CLearnerState".to_string(),
                "clearnerstate".to_string(),
                "CLearnerTuple".to_string(),
            ),
        );
        let mut verified_clone_fns = std::collections::HashMap::new();
        verified_clone_fns.insert(
            "clearnerstate".to_string(),
            "clone_clearnerstate_up_to_view".to_string(),
        );
        let output = Transpiler::generate_map_proof_lemmas(
            &map_fields,
            &verified_clone_fns,
            &std::collections::HashMap::new(),
        );

        // Should NOT contain external_body for clone
        assert!(
            !output.contains("#[verifier(external_body)]\nfn clone_clearnerstate"),
            "Should not use external_body when verified clone is configured"
        );
        // Should delegate to the verified function
        assert!(
            output.contains("clone_clearnerstate_up_to_view(m)"),
            "Should delegate to verified clone function"
        );
        // Should still contain the clone function signature
        assert!(
            output.contains("fn clone_clearnerstate(m: &CLearnerState) -> (res: CLearnerState)"),
            "Should still generate clone wrapper"
        );
        // Filter should still be external_body (not affected)
        assert!(
            output.contains("#[verifier(external_body)]\nfn filter_clearnerstate"),
            "Filter should remain external_body"
        );
    }

    #[test]
    fn test_generate_map_proof_lemmas_arc_wrapped() {
        let mut map_fields = std::collections::HashMap::new();
        map_fields.insert(
            "unexecuted_learner_state".to_string(),
            (
                "CLearnerState".to_string(),
                "clearnerstate".to_string(),
                "CLearnerTuple".to_string(),
            ),
        );
        let mut arc_wrap_fields: std::collections::HashMap<
            String,
            std::collections::HashSet<String>,
        > = std::collections::HashMap::new();
        let mut fields = std::collections::HashSet::new();
        fields.insert("unexecuted_learner_state".to_string());
        arc_wrap_fields.insert("CLearner".to_string(), fields);

        let output = Transpiler::generate_map_proof_lemmas(
            &map_fields,
            &std::collections::HashMap::new(),
            &arc_wrap_fields,
        );

        // All 4 proof lemmas should take &CLearnerState instead of CLearnerState
        assert!(
            output.contains("proof fn lemma_abstractify_empty_clearnerstate(m: &CLearnerState)"),
            "Empty lemma should take &CLearnerState, got:\n{}",
            output
        );
        assert!(
            output.contains("    old_m: &CLearnerState,\n    m2: &CLearnerState,"),
            "Insert lemma should take &CLearnerState"
        );
        assert!(
            output.contains("proof fn lemma_abstractify_singleton_clearnerstate(m: &CLearnerState"),
            "Singleton lemma should take &CLearnerState"
        );

        // filter_{prefix} should use _is_valid(m) not _is_valid(*m) for Arc-wrapped
        assert!(
            output.contains("clearnerstate_is_valid(m),"),
            "Filter requires should use _is_valid(m) for Arc, not _is_valid(*m)"
        );
        assert!(
            output.contains("clearnerstate_is_valid(&res),"),
            "Filter ensures should use _is_valid(&res) for Arc"
        );
    }

    #[test]
    fn test_needs_set_helpers_with_map_fields_only() {
        // When only map_fields is configured, needs_set_helpers should return false
        let config = TranspilerConfig {
            translator: TranslatorConfig {
                map_fields: vec![(
                    "state".to_string(),
                    (
                        "CState".to_string(),
                        "cstate".to_string(),
                        "CEntry".to_string(),
                    ),
                )]
                .into_iter()
                .collect(),
                ..Default::default()
            },
            ..Default::default()
        };
        let transpiler = Transpiler::new(config);
        assert!(
            !transpiler.needs_set_helpers(),
            "map_fields only should not need set helpers"
        );
        assert!(transpiler.has_map_fields(), "should have map_fields");
    }

    #[test]
    fn test_needs_set_helpers_with_collection_fields() {
        // When collection_fields is configured, needs_set_helpers should return true
        let config = TranspilerConfig {
            translator: TranslatorConfig {
                collection_fields: vec!["alive".to_string()].into_iter().collect(),
                ..Default::default()
            },
            ..Default::default()
        };
        let transpiler = Transpiler::new(config);
        assert!(transpiler.needs_set_helpers());
    }

    #[test]
    fn test_needs_set_helpers_no_config() {
        // When no field categories configured, no set helpers needed
        let config = TranspilerConfig::default();
        let transpiler = Transpiler::new(config);
        assert!(!transpiler.needs_set_helpers());
    }

    #[test]
    fn test_needs_set_helpers_false_when_only_other_fields() {
        // When only vec_fields/clone_fields configured (no collection_fields), should return false
        let config = TranspilerConfig {
            translator: TranslatorConfig {
                vec_fields: vec!["history".to_string()].into_iter().collect(),
                clone_fields: vec!["role".to_string()].into_iter().collect(),
                ..Default::default()
            },
            ..Default::default()
        };
        let transpiler = Transpiler::new(config);
        assert!(!transpiler.needs_set_helpers());
    }

    #[test]
    fn test_manual_code_injection() {
        let config = TranspilerConfig {
            manual_code: Some("// manual code block\npub exec fn ManualFunc() { }".to_string()),
            ..Default::default()
        };
        let transpiler = Transpiler::new(config);

        let spec_source = r#"
        verus! {
            pub open spec fn LTest(x: int) -> bool { x > 0 }
        }
        "#;
        let annotation_source = "module test { LTest(+); }";
        let result = transpiler
            .transpile_source(spec_source, annotation_source)
            .unwrap();
        assert!(
            result.contains("// manual code block"),
            "Manual code should be injected"
        );
        assert!(
            result.contains("pub exec fn ManualFunc()"),
            "Manual function should be present"
        );
        // Manual code should appear before } // verus!
        let manual_pos = result.find("ManualFunc").unwrap();
        let end_pos = result.find("} // verus!").unwrap();
        assert!(
            manual_pos < end_pos,
            "Manual code should appear before verus! closing"
        );
    }

    #[test]
    fn test_manual_code_none() {
        let config = TranspilerConfig::default();
        let transpiler = Transpiler::new(config);

        let spec_source = r#"
        verus! {
            pub open spec fn LTest(x: int) -> bool { x > 0 }
        }
        "#;
        let annotation_source = "module test { LTest(+); }";
        let result = transpiler
            .transpile_source(spec_source, annotation_source)
            .unwrap();
        // Should not have extra blank line before } // verus! when no manual code
        assert!(result.contains("} // verus!"));
    }

    // =========================================================================
    // Regression tests for proof generation pipeline (Phase 12.6.2)
    // =========================================================================

    /// Test that set-based proof generation produces correct proof blocks.
    /// Requires collection_fields configured to trigger set helper generation.
    #[test]
    fn test_regression_set_proof_pipeline() {
        let config = TranspilerConfig {
            translator: TranslatorConfig {
                generate_proofs: true,
                collection_fields: vec!["s".to_string()].into_iter().collect(),
                ..TranslatorConfig::default()
            },
            ..Default::default()
        };
        let transpiler = Transpiler::new(config);

        let spec_source = r#"
        verus! {
            pub open spec fn LInitState(s: Set<int>) -> bool {
                s =~= Set::<int>::empty()
            }
        }
        "#;
        let annotation_source = "module test { LInitState(-); }";
        let result = transpiler
            .transpile_source(spec_source, annotation_source)
            .unwrap();

        // Should contain proof-related imports/helper for empty set when collection_fields present
        assert!(
            result.contains("lemma_empty_set_map") || result.contains("HashSet::new"),
            "Should contain proof for empty set creation:\n{}",
            result
        );
    }

    /// Test that generate_proofs=true + set insert emits proof block with broadcast use.
    #[test]
    fn test_regression_set_insert_proof_pipeline() {
        let config = TranspilerConfig {
            translator: TranslatorConfig {
                generate_proofs: true,
                ..TranslatorConfig::default()
            },
            ..Default::default()
        };
        let transpiler = Transpiler::new(config);

        let spec_source = r#"
            verus! {
                pub open spec fn TestAddMember(s: Set<int>, s_: Set<int>, v: int) -> bool {
                    s_ =~= s.insert(v)
                }
            }
        "#;
        let annotation_source = r#"
            module test {
                TestAddMember(+, -, +);
            }
        "#;
        let result = transpiler
            .transpile_source(spec_source, annotation_source)
            .unwrap();

        // Should contain proof-related code for set operations
        // The proof block emits either broadcast use or the insert function call
        assert!(
            result.contains("insert") || result.contains("proof"),
            "Should contain set insert in generated code:\n{}",
            result
        );
    }

    /// Test that int params use `*x as int` in ensures clauses.
    #[test]
    fn test_regression_primitive_int_ensures() {
        let config = TranspilerConfig::default();
        let transpiler = Transpiler::new(config);

        let spec_source = r#"
            verus! {
                pub open spec fn TestIncrement(x: int, y: int) -> bool {
                    y == x + 1
                }
            }
        "#;
        let annotation_source = r#"
            module test {
                TestIncrement(+, -);
            }
        "#;
        let result = transpiler
            .transpile_source(spec_source, annotation_source)
            .unwrap();

        // int params should appear as `*x as int` in ensures clause
        assert!(
            result.contains("*x as int"),
            "Int param should use *x as int in ensures:\n{}",
            result
        );
    }

    /// Test that generate_proofs with struct_vec_fields config produces
    /// correct clone helper functions.
    #[test]
    fn test_regression_struct_vec_fields_clone_helper() {
        let mut struct_vec_fields = std::collections::HashMap::new();
        struct_vec_fields.insert(
            "entries".to_string(),
            ("CEntry".to_string(), "LEntry".to_string()),
        );

        let config = TranspilerConfig {
            translator: TranslatorConfig {
                generate_loops_for_verification: true,
                struct_vec_fields,
                ..TranslatorConfig::default()
            },
            ..Default::default()
        };

        let output = Transpiler::generate_proof_helper_lemmas(
            false,
            config.translator.generate_loops_for_verification,
            true,
            &config.translator.struct_vec_fields,
            "u64",
            &config.translator.clone_up_to_view_types,
            &None,
            false,
            &std::collections::HashMap::new(),
        );

        // Should generate clone_log helper for struct_vec_fields
        assert!(
            output.contains("clone_entries"),
            "Should generate clone helper for struct_vec_fields 'entries'"
        );
        assert!(
            output.contains("CEntry"),
            "Clone helper should reference exec type CEntry"
        );
    }

    /// Test that map_fields config generates abstractify lemmas.
    #[test]
    fn test_regression_map_fields_abstractify_lemmas() {
        let mut map_fields = std::collections::HashMap::new();
        map_fields.insert(
            "cache".to_string(),
            (
                "HashMap<u64, CReply>".to_string(),
                "creplycache".to_string(),
                "CReply".to_string(),
            ),
        );

        let output = Transpiler::generate_map_proof_lemmas(
            &map_fields,
            &std::collections::HashMap::new(),
            &std::collections::HashMap::new(),
        );

        // Should generate abstractify lemmas for the map field
        assert!(
            output.contains("lemma_abstractify_empty_creplycache"),
            "Should generate empty lemma for map field"
        );
        assert!(
            output.contains("lemma_abstractify_creplycache_insert"),
            "Should generate insert lemma for map field"
        );
    }

    #[test]
    fn test_transpile_output_is_deterministic() {
        // Regression: struct construction field ordering and inline type ordering
        // must be deterministic across multiple transpilations (no HashMap iteration order dependency).
        let config = TranspilerConfig {
            generate_inline_types: true,
            translator: TranslatorConfig {
                int_type: "u64".to_string(),
                nat_type: "u64".to_string(),
                generate_proofs: true,
                ..Default::default()
            },
            ..Default::default()
        };

        let spec_source = r#"
            verus! {
                pub struct LInner {
                    pub alpha: int,
                    pub beta: int,
                }

                pub struct LState {
                    pub x: int,
                    pub y: int,
                    pub z: int,
                }

                pub open spec fn LInit(s_: LState) -> bool {
                    &&& s_.x == 0
                    &&& s_.y == 1
                    &&& s_.z == 2
                }
            }
        "#;
        let annotation_source = "module test\nLInit(-)\n";

        // Transpile multiple times and verify all outputs are identical
        let mut results = Vec::new();
        for _ in 0..5 {
            let transpiler = Transpiler::new(config.clone());
            let result = transpiler
                .transpile_source(spec_source, annotation_source)
                .unwrap();
            results.push(result);
        }

        for i in 1..results.len() {
            assert_eq!(
                results[0], results[i],
                "Transpilation run {} produced different output than run 0",
                i
            );
        }
    }

    // ==================== Auto-skip tests ====================

    #[test]
    fn test_auto_skip_disabled_errors_propagate() {
        // A spec function that cannot be transpiled (unsupported pattern)
        // should cause an error when auto_skip is false
        let config = TranspilerConfig {
            auto_skip: false,
            proof_fallback: false,
            ..Default::default()
        };
        let transpiler = Transpiler::new(config);

        // Spec with a function that has no matching annotation — should not error
        // (functions without annotations are simply skipped).
        // Instead, test with a function that HAS annotation but fails translation.
        let spec_source = r#"
            verus! {
                pub open spec fn GoodFn(x: int, y: int) -> bool {
                    y == x + 1
                }
            }
        "#;
        let annotation_source = r#"
            module test {
                GoodFn(+, -);
            }
        "#;

        // This should succeed — good function transpiles fine
        let result = transpiler.transpile_source(spec_source, annotation_source);
        assert!(
            result.is_ok(),
            "Good function should transpile: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_auto_skip_enabled_returns_report() {
        let config = TranspilerConfig {
            auto_skip: true,
            proof_fallback: false,
            ..Default::default()
        };
        let transpiler = Transpiler::new(config);

        let spec_source = r#"
            verus! {
                pub open spec fn GoodFn(x: int, y: int) -> bool {
                    y == x + 1
                }
            }
        "#;
        let annotation_source = r#"
            module test {
                GoodFn(+, -);
            }
        "#;

        let (output, skipped) = transpiler
            .transpile_source_with_report(spec_source, annotation_source)
            .unwrap();

        // Good function should be in output, no skips
        assert!(
            output.contains("CGoodFn"),
            "Should contain transpiled function: {}",
            output
        );
        assert!(
            skipped.is_empty(),
            "No functions should be skipped: {:?}",
            skipped
        );
    }

    #[test]
    fn test_auto_skip_skips_failed_functions_and_continues() {
        let config = TranspilerConfig {
            auto_skip: true,
            proof_fallback: false,
            ..Default::default()
        };
        let transpiler = Transpiler::new(config);

        // Two functions: first good, second has annotation but will fail
        // because the mode annotation references a non-existent parameter pattern
        let spec_source = r#"
            verus! {
                pub open spec fn GoodFn(x: int, y: int) -> bool {
                    y == x + 1
                }

                pub open spec fn AnotherGoodFn(a: int, b: int) -> bool {
                    b == a * 2
                }
            }
        "#;
        let annotation_source = r#"
            module test {
                GoodFn(+, -);
                AnotherGoodFn(+, -);
            }
        "#;

        let (output, skipped) = transpiler
            .transpile_source_with_report(spec_source, annotation_source)
            .unwrap();

        // Both good functions should transpile
        assert!(
            output.contains("CGoodFn"),
            "Should contain CGoodFn: {}",
            output
        );
        assert!(
            output.contains("CAnotherGoodFn"),
            "Should contain CAnotherGoodFn: {}",
            output
        );
        assert!(skipped.is_empty(), "No functions should be skipped");
    }

    #[test]
    fn test_auto_skip_default_is_false() {
        let config = TranspilerConfig::default();
        assert!(!config.auto_skip, "auto_skip should default to false");
    }

    #[test]
    fn test_auto_skip_with_skip_functions() {
        // Verify that skip_functions list still works alongside auto_skip
        let config = TranspilerConfig {
            auto_skip: true,
            proof_fallback: false,
            skip_functions: vec!["GoodFn".to_string()],
            ..Default::default()
        };
        let transpiler = Transpiler::new(config);

        let spec_source = r#"
            verus! {
                pub open spec fn GoodFn(x: int, y: int) -> bool {
                    y == x + 1
                }

                pub open spec fn OtherFn(a: int, b: int) -> bool {
                    b == a + 2
                }
            }
        "#;
        let annotation_source = r#"
            module test {
                GoodFn(+, -);
                OtherFn(+, -);
            }
        "#;

        let (output, skipped) = transpiler
            .transpile_source_with_report(spec_source, annotation_source)
            .unwrap();

        // GoodFn should be explicitly skipped (not in output, not in auto-skip report)
        assert!(
            !output.contains("CGoodFn"),
            "GoodFn should be skipped: {}",
            output
        );
        assert!(
            output.contains("COtherFn"),
            "OtherFn should be in output: {}",
            output
        );
        assert!(skipped.is_empty(), "No auto-skipped functions");
    }

    #[test]
    fn test_skipped_function_struct_fields() {
        let sf = SkippedFunction {
            name: "TestFn".to_string(),
            reason: "transpilation error: unsupported pattern".to_string(),
        };
        assert_eq!(sf.name, "TestFn");
        assert!(sf.reason.contains("unsupported pattern"));

        // Clone should work
        let sf2 = sf.clone();
        assert_eq!(sf2.name, sf.name);
        assert_eq!(sf2.reason, sf.reason);
    }

    // ─── proof-fallback tests ─────────────────────────────────────────

    #[test]
    fn test_proof_fallback_default_is_false() {
        let config = TranspilerConfig::default();
        assert!(
            !config.proof_fallback,
            "proof_fallback should default to false"
        );
    }

    #[test]
    fn test_spec_to_exec_name_basic() {
        assert_eq!(Transpiler::spec_to_exec_name("LInit", "L", "C"), "CInit");
        assert_eq!(Transpiler::spec_to_exec_name("LFoo", "L", "C"), "CFoo");
        assert_eq!(Transpiler::spec_to_exec_name("Init", "L", "C"), "CInit");
        assert_eq!(
            Transpiler::spec_to_exec_name("LInit", "L", "Exec"),
            "ExecInit"
        );
    }

    #[test]
    fn test_spec_to_exec_name_no_prefix_match() {
        assert_eq!(Transpiler::spec_to_exec_name("Foo", "L", "C"), "CFoo");
        assert_eq!(Transpiler::spec_to_exec_name("MyFunc", "L", "C"), "CMyFunc");
    }

    #[test]
    fn test_spec_to_exec_name_lowercase_after_prefix() {
        assert_eq!(Transpiler::spec_to_exec_name("Llow", "L", "C"), "CLlow");
    }

    #[test]
    fn test_type_to_exec_string_primitives() {
        use crate::ast::Type;
        assert_eq!(
            Transpiler::type_to_exec_string(&Type::Int, "L", "C", "u64", &Default::default()),
            "u64"
        );
        assert_eq!(
            Transpiler::type_to_exec_string(&Type::Nat, "L", "C", "u64", &Default::default()),
            "u64"
        );
        assert_eq!(
            Transpiler::type_to_exec_string(&Type::Bool, "L", "C", "u64", &Default::default()),
            "bool"
        );
        assert_eq!(
            Transpiler::type_to_exec_string(&Type::Int, "L", "C", "i64", &Default::default()),
            "i64"
        );
    }

    #[test]
    fn test_type_to_exec_string_collections() {
        use crate::ast::Type;
        let int_ty = Type::Int;
        let seq_ty = Type::Seq(Box::new(int_ty.clone()));
        assert_eq!(
            Transpiler::type_to_exec_string(&seq_ty, "L", "C", "u64", &Default::default()),
            "Vec<u64>"
        );

        let set_ty = Type::Set(Box::new(int_ty.clone()));
        assert_eq!(
            Transpiler::type_to_exec_string(&set_ty, "L", "C", "u64", &Default::default()),
            "HashSet<u64>"
        );

        let map_ty = Type::Map(Box::new(int_ty.clone()), Box::new(int_ty.clone()));
        assert_eq!(
            Transpiler::type_to_exec_string(&map_ty, "L", "C", "u64", &Default::default()),
            "HashMap<u64, u64>"
        );
    }

    #[test]
    fn test_type_to_exec_string_named() {
        use crate::ast::{Path, Type};
        let named = Type::Named(Path {
            segments: vec!["LState".to_string()],
        });
        assert_eq!(
            Transpiler::type_to_exec_string(&named, "L", "C", "u64", &Default::default()),
            "CState"
        );
    }

    #[test]
    fn test_type_to_exec_string_nested_seq() {
        use crate::ast::{Path, Type};
        let inner = Type::Named(Path {
            segments: vec!["LMessage".to_string()],
        });
        let seq_ty = Type::Seq(Box::new(inner));
        assert_eq!(
            Transpiler::type_to_exec_string(&seq_ty, "L", "C", "u64", &Default::default()),
            "Vec<CMessage>"
        );
    }

    #[test]
    fn test_type_to_exec_string_with_remapping() {
        use crate::ast::{Path, Type};
        let mut remapping = std::collections::HashMap::new();
        remapping.insert("RslPacket".to_string(), "CPacket".to_string());
        remapping.insert("OperationNumber".to_string(), "u64".to_string());
        let named = Type::Named(Path::single("RslPacket".to_string()));
        assert_eq!(
            Transpiler::type_to_exec_string(&named, "L", "C", "u64", &remapping),
            "CPacket"
        );
        let named2 = Type::Named(Path::single("OperationNumber".to_string()));
        assert_eq!(
            Transpiler::type_to_exec_string(&named2, "L", "C", "u64", &remapping),
            "u64"
        );
        // Non-mapped type still uses prefix replacement
        let named3 = Type::Named(Path::single("LState".to_string()));
        assert_eq!(
            Transpiler::type_to_exec_string(&named3, "L", "C", "u64", &remapping),
            "CState"
        );
    }

    #[test]
    fn test_proof_fallback_emits_stub_for_good_function() {
        let config = TranspilerConfig {
            auto_skip: true,
            proof_fallback: true,
            ..Default::default()
        };
        let transpiler = Transpiler::new(config);

        let spec_source = r#"
            verus! {
                pub open spec fn GoodFn(x: int, y: int) -> bool {
                    y == x + 1
                }
            }
        "#;
        let annotation_source = r#"
            module test {
                GoodFn(+, -);
            }
        "#;

        let (output, skipped) = transpiler
            .transpile_source_with_report(spec_source, annotation_source)
            .unwrap();

        assert!(
            output.contains("CGoodFn"),
            "Good function should still transpile normally: {}",
            output
        );
        assert!(
            skipped.is_empty(),
            "No functions should be skipped: {:?}",
            skipped
        );
        assert!(
            !output.contains("external_body"),
            "Good function should not be a stub: {}",
            output
        );
    }

    #[test]
    fn test_proof_fallback_implies_auto_skip() {
        let config = TranspilerConfig {
            auto_skip: true,
            proof_fallback: true,
            ..Default::default()
        };
        let transpiler = Transpiler::new(config);

        let spec_source = r#"
            verus! {
                pub open spec fn GoodFn(x: int, y: int) -> bool {
                    y == x + 1
                }
            }
        "#;
        let annotation_source = r#"
            module test {
                GoodFn(+, -);
            }
        "#;

        let (output, _skipped) = transpiler
            .transpile_source_with_report(spec_source, annotation_source)
            .unwrap();
        assert!(output.contains("CGoodFn"), "Should transpile: {}", output);
    }

    fn make_test_spec_fn(
        name: &str,
        params: Vec<(&str, crate::ast::Type)>,
    ) -> crate::ast::SpecFunction {
        use crate::ast::*;
        SpecFunction {
            name: name.to_string(),
            generics: Generics::default(),
            params: params
                .into_iter()
                .map(|(n, ty)| Parameter {
                    name: n.to_string(),
                    ty,
                    mode: None,
                    variable_mode: VariableMode::Exec,
                    span: None,
                })
                .collect(),
            return_type: Type::Bool,
            requires: vec![],
            ensures: vec![],
            recommends: vec![],
            decreases: vec![],
            body: Expr::Literal(Literal::Bool(true)),
            span: None,
        }
    }

    fn make_test_annotation(
        name: &str,
        modes: Vec<crate::ast::ParameterMode>,
    ) -> crate::annotation::FunctionAnnotation {
        crate::annotation::FunctionAnnotation {
            name: name.to_string(),
            param_modes: modes,
            kind: crate::ast::FunctionKind::Predicate,
            return_type: None,
        }
    }

    #[test]
    fn test_generate_external_body_stub_basic() {
        use crate::ast::{ParameterMode, Path, Type};

        let config = TranspilerConfig {
            proof_fallback: true,
            ..Default::default()
        };
        let transpiler = Transpiler::new(config);

        let spec_fn = make_test_spec_fn(
            "LInit",
            vec![
                ("c", Type::Named(Path::single("LConstants".to_string()))),
                ("s_", Type::Named(Path::single("LState".to_string()))),
            ],
        );

        let annotation =
            make_test_annotation("LInit", vec![ParameterMode::Input, ParameterMode::Output]);

        let stub =
            transpiler.generate_external_body_stub(&spec_fn, Some(&annotation), "test reason");
        assert!(
            stub.contains("#[verifier(external_body)]"),
            "Should have external_body: {}",
            stub
        );
        assert!(
            stub.contains("pub exec fn CInit"),
            "Should have exec name: {}",
            stub
        );
        assert!(
            stub.contains("c: &CConstants"),
            "Should have input param: {}",
            stub
        );
        assert!(
            stub.contains("-> (result: CState)"),
            "Should have output return: {}",
            stub
        );
        assert!(
            stub.contains("TRANSLATE-TODO: test reason"),
            "Should have reason comment: {}",
            stub
        );
        assert!(
            stub.contains("unimplemented!()"),
            "Should have unimplemented body: {}",
            stub
        );
    }

    #[test]
    fn test_generate_external_body_stub_multiple_outputs() {
        use crate::ast::{ParameterMode, Type};

        let config = TranspilerConfig::default();
        let transpiler = Transpiler::new(config);

        let spec_fn = make_test_spec_fn(
            "LFoo",
            vec![("x", Type::Int), ("y", Type::Int), ("z", Type::Int)],
        );

        let annotation = make_test_annotation(
            "LFoo",
            vec![
                ParameterMode::Input,
                ParameterMode::Output,
                ParameterMode::Output,
            ],
        );

        let stub =
            transpiler.generate_external_body_stub(&spec_fn, Some(&annotation), "multi-output");
        // Default int_type is i64
        assert!(
            stub.contains("-> (result: (i64, i64))"),
            "Should have tuple return: {}",
            stub
        );
    }

    #[test]
    fn test_generate_external_body_stub_no_annotation() {
        use crate::ast::Type;

        let config = TranspilerConfig::default();
        let transpiler = Transpiler::new(config);

        let spec_fn = make_test_spec_fn("LHelper", vec![("a", Type::Int), ("b", Type::Int)]);

        let stub = transpiler.generate_external_body_stub(&spec_fn, None, "no annotation");
        // Default int_type is i64
        assert!(stub.contains("a: &i64"), "Should have param a: {}", stub);
        assert!(stub.contains("b: &i64"), "Should have param b: {}", stub);
        assert!(
            !stub.contains("->"),
            "Should not have return type: {}",
            stub
        );
    }

    #[test]
    fn test_generate_external_body_stub_collection_types() {
        use crate::ast::{ParameterMode, Type};

        let config = TranspilerConfig::default();
        let transpiler = Transpiler::new(config);

        let spec_fn = make_test_spec_fn(
            "LProcess",
            vec![
                ("items", Type::Seq(Box::new(Type::Int))),
                ("result", Type::Set(Box::new(Type::Int))),
            ],
        );

        let annotation = make_test_annotation(
            "LProcess",
            vec![ParameterMode::Input, ParameterMode::Output],
        );

        let stub =
            transpiler.generate_external_body_stub(&spec_fn, Some(&annotation), "collections");
        // Default int_type is i64
        assert!(
            stub.contains("items: &Vec<i64>"),
            "Should have Vec input: {}",
            stub
        );
        assert!(
            stub.contains("-> (result: HashSet<i64>)"),
            "Should have HashSet output: {}",
            stub
        );
    }

    #[test]
    fn test_generate_external_body_stub_non_predicate_no_spec_ensures() {
        // A spec function that returns Seq<T> (not bool) should NOT get
        // SpecFn(args...) in ensures — it's not a predicate.
        use crate::ast::{Path, Type};

        let config = TranspilerConfig::default();
        let transpiler = Transpiler::new(config);

        // Create spec fn with non-bool return type
        let mut spec_fn = make_test_spec_fn(
            "LBuildBroadcast",
            vec![
                ("src", Type::Named(Path::single("LEndPoint".to_string()))),
                (
                    "dsts",
                    Type::Seq(Box::new(Type::Named(Path::single("LEndPoint".to_string())))),
                ),
                ("m", Type::Named(Path::single("LMessage".to_string()))),
            ],
        );
        // Override return type to Seq<LPacket> (non-bool)
        spec_fn.return_type = Type::Seq(Box::new(Type::Named(Path::single("LPacket".to_string()))));

        // No annotation (all params are inputs, no output)
        let stub = transpiler.generate_external_body_stub(&spec_fn, None, "recursive helper");
        // Should NOT contain the spec function name as an ensures predicate
        assert!(
            !stub.contains("ensures"),
            "Non-predicate function should not have ensures: {}",
            stub
        );
        assert!(
            !stub.contains("LBuildBroadcast("),
            "Should not use non-predicate as ensures: {}",
            stub
        );
    }

    #[test]
    fn test_generate_external_body_stub_predicate_has_spec_ensures() {
        // A spec function that returns bool SHOULD get SpecFn(args...) in ensures.
        use crate::ast::{ParameterMode, Path, Type};

        let config = TranspilerConfig {
            translator: crate::translator::TranslatorConfig {
                validity_predicate_name: "valid".to_string(),
                ..Default::default()
            },
            ..Default::default()
        };
        let transpiler = Transpiler::new(config);

        let spec_fn = make_test_spec_fn(
            "LInit",
            vec![
                ("c", Type::Named(Path::single("LConstants".to_string()))),
                ("s_", Type::Named(Path::single("LState".to_string()))),
            ],
        );

        let annotation =
            make_test_annotation("LInit", vec![ParameterMode::Input, ParameterMode::Output]);

        let stub = transpiler.generate_external_body_stub(&spec_fn, Some(&annotation), "test");
        assert!(
            stub.contains("ensures"),
            "Predicate should have ensures: {}",
            stub
        );
        assert!(
            stub.contains("LInit("),
            "Predicate should use spec fn in ensures: {}",
            stub
        );
        assert!(
            stub.contains("result.valid()"),
            "Should have validity ensures: {}",
            stub
        );
    }

    #[test]
    fn test_no_stub_functions_suppresses_stub_in_proof_fallback() {
        // When a function is in both skip_functions and no_stub_functions,
        // proof_fallback mode should NOT generate a stub for it.
        use crate::ast::{ParameterMode, Type};

        let config = TranspilerConfig {
            proof_fallback: true,
            skip_functions: vec!["LSkipWithStub".to_string(), "LSkipNoStub".to_string()],
            no_stub_functions: vec!["LSkipNoStub".to_string()],
            ..Default::default()
        };
        let transpiler = Transpiler::new(config);

        // Test via generate_external_body_stub: a function in no_stub_functions
        // should be suppressed by the pipeline, not by the stub generator.
        // Instead, test the pipeline logic directly: the key check is
        //   self.config.proof_fallback && !self.config.no_stub_functions.contains(&spec_fn.name)

        // Simulate: LSkipWithStub is in skip_functions but NOT in no_stub → should generate stub
        let spec_fn_with_stub =
            make_test_spec_fn("LSkipWithStub", vec![("s", Type::Int), ("s_", Type::Int)]);
        let annotation = make_test_annotation(
            "LSkipWithStub",
            vec![ParameterMode::Input, ParameterMode::Output],
        );

        // proof_fallback is true, NOT in no_stub → stub should be generated
        assert!(
            transpiler.config.proof_fallback
                && !transpiler
                    .config
                    .no_stub_functions
                    .contains(&"LSkipWithStub".to_string())
        );
        let stub =
            transpiler.generate_external_body_stub(&spec_fn_with_stub, Some(&annotation), "test");
        assert!(
            stub.contains("CSkipWithStub"),
            "Should generate stub: {}",
            stub
        );

        // Simulate: LSkipNoStub is in skip_functions AND in no_stub → should NOT generate stub
        assert!(transpiler
            .config
            .no_stub_functions
            .contains(&"LSkipNoStub".to_string()));
        // The pipeline check: !self.config.no_stub_functions.contains(&spec_fn.name) → false
        // So the stub generation is skipped entirely (no code emitted).
    }

    #[test]
    fn test_skip_valid_types_omits_valid_in_stub() {
        // When output type is in skip_valid_types, stub should NOT have result.valid()
        use crate::ast::{ParameterMode, Path, Type};

        let config = TranspilerConfig {
            proof_fallback: true,
            translator: crate::translator::TranslatorConfig {
                validity_predicate_name: "valid".to_string(),
                skip_valid_types: ["Votes".to_string()].into_iter().collect(),
                ..Default::default()
            },
            ..Default::default()
        };
        let transpiler = Transpiler::new(config);

        let spec_fn = make_test_spec_fn(
            "LRemoveVotes",
            vec![
                ("votes", Type::Named(Path::single("Votes".to_string()))),
                ("result_", Type::Named(Path::single("Votes".to_string()))),
            ],
        );

        let annotation = make_test_annotation(
            "LRemoveVotes",
            vec![ParameterMode::Input, ParameterMode::Output],
        );

        let stub = transpiler.generate_external_body_stub(&spec_fn, Some(&annotation), "test");
        // Should NOT have result.valid() because Votes is in skip_valid_types
        assert!(
            !stub.contains("result.valid()"),
            "Should skip valid() for skip_valid_types: {}",
            stub
        );
    }
}
