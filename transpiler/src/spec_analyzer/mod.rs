//! Spec Analyzer: extracts structured schema from protocol spec files.
//!
//! This module parses spec `.rs` files (types + protocol logic) and builds a
//! `SpecSchema` containing all struct/enum definitions, type aliases, and
//! function signatures. This is the foundation for Phase 20 auto-inference
//! of TOML configuration.
//!
//! # Usage
//!
//! ```ignore
//! use verus_transpiler::spec_analyzer::{analyze_spec_file, analyze_spec_files, SpecSchema};
//!
//! // Analyze a single file
//! let schema = analyze_spec_file("src/protocol/Paxos/paxos.rs")?;
//!
//! // Analyze types + protocol files together
//! let schema = analyze_spec_files(&[
//!     "src/protocol/Paxos/types.rs",
//!     "src/protocol/Paxos/paxos.rs",
//! ])?;
//!
//! assert!(schema.structs.contains_key("LState"));
//! assert!(schema.functions.contains_key("LInit"));
//! ```

use crate::annotation::ModuleAnnotations;
use crate::ast::{ParameterMode, SpecFunction, Type};
use crate::config::{MethodCallConfig, NamingConfig, TranspilerConfig};
use crate::error::TranspileResult;
use crate::parser::parse_file;
use crate::types::{
    build_registry, parse_types_from_file_without_functions, EnumDef, FieldDef, FunctionSig,
    StructDef, TypeAlias, TypeRegistry, VariantDef, VariantFields,
};
use std::collections::HashMap;
use std::path::{Path, PathBuf};

/// A structured schema extracted from protocol spec files.
///
/// Contains all type definitions (structs, enums, aliases) and function
/// signatures found in the spec. This is the input for auto-deriving
/// TOML configuration in later phases.
#[derive(Debug, Default)]
pub struct SpecSchema {
    /// All struct definitions, keyed by name (e.g., "LState", "LConstants")
    pub structs: HashMap<String, StructDef>,
    /// All enum definitions, keyed by name (e.g., "LMessage")
    pub enums: HashMap<String, EnumDef>,
    /// All type aliases, keyed by name (e.g., "Votes", "RequestBatch")
    pub aliases: HashMap<String, TypeAlias>,
    /// All spec function signatures, keyed by name (e.g., "LInit", "LSend1a")
    pub functions: HashMap<String, FunctionSig>,
    /// Insertion order for structs (deterministic iteration)
    pub struct_order: Vec<String>,
    /// Insertion order for enums (deterministic iteration)
    pub enum_order: Vec<String>,
    /// Insertion order for aliases (deterministic iteration)
    pub alias_order: Vec<String>,
    /// Source files that were analyzed
    pub source_files: Vec<String>,
}

impl SpecSchema {
    /// Create a new empty schema
    pub fn new() -> Self {
        Self::default()
    }

    /// Build from a TypeRegistry
    pub fn from_registry(registry: TypeRegistry) -> Self {
        Self {
            structs: registry.structs,
            enums: registry.enums,
            aliases: registry.aliases,
            functions: registry.functions,
            struct_order: registry.struct_order,
            enum_order: registry.enum_order,
            alias_order: registry.alias_order,
            source_files: Vec::new(),
        }
    }

    /// Merge another schema into this one (for combining types.rs + protocol.rs)
    pub fn merge(&mut self, other: SpecSchema) {
        for name in &other.struct_order {
            if let Some(s) = other.structs.get(name) {
                if !self.structs.contains_key(name) {
                    self.struct_order.push(name.clone());
                }
                self.structs.insert(name.clone(), s.clone());
            }
        }
        for name in &other.enum_order {
            if let Some(e) = other.enums.get(name) {
                if !self.enums.contains_key(name) {
                    self.enum_order.push(name.clone());
                }
                self.enums.insert(name.clone(), e.clone());
            }
        }
        for name in &other.alias_order {
            if let Some(a) = other.aliases.get(name) {
                if !self.aliases.contains_key(name) {
                    self.alias_order.push(name.clone());
                }
                self.aliases.insert(name.clone(), a.clone());
            }
        }
        for (name, f) in other.functions {
            self.functions.insert(name, f);
        }
        self.source_files.extend(other.source_files);
    }

    /// Get all struct field names for a given struct
    pub fn get_struct_fields(&self, name: &str) -> Option<&[FieldDef]> {
        self.structs.get(name).map(|s| s.fields.as_slice())
    }

    /// Get all enum variant names for a given enum
    pub fn get_enum_variants(&self, name: &str) -> Option<&[VariantDef]> {
        self.enums.get(name).map(|e| e.variants.as_slice())
    }

    /// Find which enum variant contains a given field name.
    /// Returns (enum_name, variant_name) if found.
    pub fn find_variant_with_field(&self, field_name: &str) -> Option<(String, String)> {
        for (enum_name, enum_def) in &self.enums {
            for variant in &enum_def.variants {
                match &variant.fields {
                    VariantFields::Struct(fields) => {
                        if fields.iter().any(|f| f.name == field_name) {
                            return Some((enum_name.clone(), variant.name.clone()));
                        }
                    }
                    _ => {}
                }
            }
        }
        None
    }

    /// Get all function names
    pub fn function_names(&self) -> Vec<&str> {
        self.functions.keys().map(|s| s.as_str()).collect()
    }

    /// Get the number of each type of definition
    pub fn summary(&self) -> SchemaSummary {
        SchemaSummary {
            num_structs: self.structs.len(),
            num_enums: self.enums.len(),
            num_aliases: self.aliases.len(),
            num_functions: self.functions.len(),
        }
    }
}

/// Summary statistics for a SpecSchema
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SchemaSummary {
    pub num_structs: usize,
    pub num_enums: usize,
    pub num_aliases: usize,
    pub num_functions: usize,
}

/// Parsed protocol sources for source-first workflows.
///
/// This pairs a protocol logic file (`<proto>.rs`) with its sibling `types.rs`
/// and exposes both:
/// - merged schema (types + signatures), and
/// - full parsed spec functions (`SpecFunction` / `Expr` AST) from both files.
#[derive(Debug)]
pub struct ProtocolSourceBundle {
    /// `src/protocol/<Proto>/types.rs`
    pub types_file: PathBuf,
    /// `src/protocol/<Proto>/<proto>.rs`
    pub protocol_file: PathBuf,
    /// Merged schema from `types.rs` + `<proto>.rs`
    pub schema: SpecSchema,
    /// Parsed spec functions from both files (`types.rs` first, then protocol file)
    pub spec_functions: Vec<SpecFunction>,
    /// Validated required model-check entrypoints.
    pub entrypoints: RequiredEntrypoints,
}

/// Required source-first entrypoints for model checking.
#[derive(Debug, Clone)]
pub struct RequiredEntrypoints {
    /// Configured init entrypoint (`s: LState, c: LConstants) -> bool`.
    pub linit: SpecFunction,
    /// Configured next entrypoint (`s: LState, s_: LState, c: LConstants) -> bool`.
    pub lnext: SpecFunction,
}

/// Analyze a single spec file and return both schema + parsed spec AST.
///
/// Function signatures in the returned schema are populated from the canonical
/// parser/AST path (`parse_file` -> `SpecFunction`), not from the type parser.
fn analyze_spec_file_with_ast(path: &Path) -> TranspileResult<(SpecSchema, Vec<SpecFunction>)> {
    let type_defs = parse_types_from_file_without_functions(path)?;
    let mut registry = build_registry(type_defs);

    let spec_functions = parse_file(path)?;
    for spec_fn in &spec_functions {
        registry.register_spec_function(spec_fn);
    }

    let mut schema = SpecSchema::from_registry(registry);
    schema.source_files.push(path.display().to_string());
    Ok((schema, spec_functions))
}

/// Analyze a single spec file and return a SpecSchema.
pub fn analyze_spec_file<P: AsRef<Path>>(path: P) -> TranspileResult<SpecSchema> {
    let (schema, _) = analyze_spec_file_with_ast(path.as_ref())?;
    Ok(schema)
}

/// Analyze multiple spec files and return a merged SpecSchema.
/// Typically used to combine types.rs + protocol.rs for a single protocol.
pub fn analyze_spec_files<P: AsRef<Path>>(paths: &[P]) -> TranspileResult<SpecSchema> {
    let (schema, _) = analyze_spec_files_with_ast(paths)?;
    Ok(schema)
}

/// Analyze multiple spec files and return merged schema + parsed spec AST.
///
/// `spec_functions` are returned in file order (all functions from `paths[0]`,
/// then `paths[1]`, etc.).
pub fn analyze_spec_files_with_ast<P: AsRef<Path>>(
    paths: &[P],
) -> TranspileResult<(SpecSchema, Vec<SpecFunction>)> {
    let mut schema = SpecSchema::new();
    let mut spec_functions = Vec::new();
    for path in paths {
        let (file_schema, file_spec_functions) = analyze_spec_file_with_ast(path.as_ref())?;
        schema.merge(file_schema);
        spec_functions.extend(file_spec_functions);
    }
    Ok((schema, spec_functions))
}

/// Resolve and validate required model-check entrypoints from parsed spec functions.
///
/// Required signatures:
/// - `LInit(s: LState, c: LConstants) -> bool`
/// - `LNext(s: LState, s_: LState, c: LConstants) -> bool`
pub fn resolve_required_entrypoints(
    spec_functions: &[SpecFunction],
) -> TranspileResult<RequiredEntrypoints> {
    resolve_required_entrypoints_named(spec_functions, "LInit", "LNext")
}

/// Resolve and validate configured model-check entrypoints from parsed spec functions.
pub fn resolve_required_entrypoints_named(
    spec_functions: &[SpecFunction],
    init_name: &str,
    next_name: &str,
) -> TranspileResult<RequiredEntrypoints> {
    let available_names: Vec<String> = spec_functions.iter().map(|f| f.name.clone()).collect();
    let available_names_text = if available_names.is_empty() {
        "<none>".to_string()
    } else {
        available_names.join(", ")
    };

    let linit = spec_functions
        .iter()
        .find(|f| f.name == init_name)
        .cloned()
        .ok_or_else(|| crate::error::TranspileError::Config {
            message: format!(
                "Missing required entrypoint `{}(s: LState, c: LConstants) -> bool`.\nFound spec functions: {}.\nFix: add/rename a function to `{}` with the required signature.",
                init_name, available_names_text, init_name
            ),
        })?;
    let lnext = spec_functions
        .iter()
        .find(|f| f.name == next_name)
        .cloned()
        .ok_or_else(|| crate::error::TranspileError::Config {
            message: format!(
                "Missing required entrypoint `{}(s: LState, s_: LState, c: LConstants) -> bool`.\nFound spec functions: {}.\nFix: add/rename a function to `{}` with the required signature.",
                next_name, available_names_text, next_name
            ),
        })?;

    validate_linit_signature(&linit, init_name)?;
    validate_lnext_signature(&lnext, next_name)?;

    Ok(RequiredEntrypoints { linit, lnext })
}

fn validate_linit_signature(linit: &SpecFunction, expected_name: &str) -> TranspileResult<()> {
    let mut issues = Vec::new();
    if linit.params.len() != 2 {
        issues.push(format!(
            "expected 2 parameters, found {}",
            linit.params.len()
        ));
    }
    if !matches!(linit.return_type, Type::Bool) {
        issues.push(format!(
            "expected return type `bool`, found `{}`",
            format_type_for_diagnostic(&linit.return_type)
        ));
    }
    if let Some(first) = linit.params.first() {
        if first.name != "s" {
            issues.push(format!(
                "expected first parameter name `s`, found `{}`",
                first.name
            ));
        }
        if !is_named_type(&first.ty, "LState") {
            issues.push(format!(
                "expected first parameter type `LState`, found `{}`",
                format_type_for_diagnostic(&first.ty)
            ));
        }
    }
    if let Some(second) = linit.params.get(1) {
        if second.name != "c" {
            issues.push(format!(
                "expected second parameter name `c`, found `{}`",
                second.name
            ));
        }
        if !is_named_type(&second.ty, "LConstants") {
            issues.push(format!(
                "expected second parameter type `LConstants`, found `{}`",
                format_type_for_diagnostic(&second.ty)
            ));
        }
    }

    if !issues.is_empty() {
        return Err(crate::error::TranspileError::Config {
            message: format!(
                "Incompatible `{}` signature.\nExpected: {}(s: LState, c: LConstants) -> bool\nFound: {}\nIssues: {}\nFix: rename/retype parameters to match the expected entrypoint.",
                expected_name,
                expected_name,
                format_signature_for_diagnostic(linit),
                issues.join("; ")
            ),
        });
    }

    Ok(())
}

fn validate_lnext_signature(lnext: &SpecFunction, expected_name: &str) -> TranspileResult<()> {
    let mut issues = Vec::new();
    if lnext.params.len() != 3 {
        issues.push(format!(
            "expected 3 parameters, found {}",
            lnext.params.len()
        ));
    }
    if !matches!(lnext.return_type, Type::Bool) {
        issues.push(format!(
            "expected return type `bool`, found `{}`",
            format_type_for_diagnostic(&lnext.return_type)
        ));
    }
    if let Some(first) = lnext.params.first() {
        if first.name != "s" {
            issues.push(format!(
                "expected first parameter name `s`, found `{}`",
                first.name
            ));
        }
        if !is_named_type(&first.ty, "LState") {
            issues.push(format!(
                "expected first parameter type `LState`, found `{}`",
                format_type_for_diagnostic(&first.ty)
            ));
        }
    }
    if let Some(second) = lnext.params.get(1) {
        if second.name != "s_" {
            issues.push(format!(
                "expected second parameter name `s_`, found `{}`",
                second.name
            ));
        }
        if !is_named_type(&second.ty, "LState") {
            issues.push(format!(
                "expected second parameter type `LState`, found `{}`",
                format_type_for_diagnostic(&second.ty)
            ));
        }
    }
    if let Some(third) = lnext.params.get(2) {
        if third.name != "c" {
            issues.push(format!(
                "expected third parameter name `c`, found `{}`",
                third.name
            ));
        }
        if !is_named_type(&third.ty, "LConstants") {
            issues.push(format!(
                "expected third parameter type `LConstants`, found `{}`",
                format_type_for_diagnostic(&third.ty)
            ));
        }
    }

    if !issues.is_empty() {
        return Err(crate::error::TranspileError::Config {
            message: format!(
                "Incompatible `{}` signature.\nExpected: {}(s: LState, s_: LState, c: LConstants) -> bool\nFound: {}\nIssues: {}\nFix: rename/retype parameters to match the expected entrypoint.",
                expected_name,
                expected_name,
                format_signature_for_diagnostic(lnext),
                issues.join("; ")
            ),
        });
    }

    Ok(())
}

fn is_named_type(ty: &Type, expected_name: &str) -> bool {
    match ty {
        Type::Named(path) => path.last() == Some(expected_name),
        _ => false,
    }
}

fn format_signature_for_diagnostic(spec_fn: &SpecFunction) -> String {
    let params = spec_fn
        .params
        .iter()
        .map(|p| format!("{}: {}", p.name, format_type_for_diagnostic(&p.ty)))
        .collect::<Vec<_>>()
        .join(", ");
    format!(
        "{}({}) -> {}",
        spec_fn.name,
        params,
        format_type_for_diagnostic(&spec_fn.return_type)
    )
}

fn format_type_for_diagnostic(ty: &Type) -> String {
    match ty {
        Type::Named(path) => path.segments.join("::"),
        Type::Generic(path, args) => format!(
            "{}<{}>",
            path.segments.join("::"),
            args.iter()
                .map(format_type_for_diagnostic)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Type::Tuple(types) => format!(
            "({})",
            types
                .iter()
                .map(format_type_for_diagnostic)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Type::Seq(inner) => format!("Seq<{}>", format_type_for_diagnostic(inner)),
        Type::Set(inner) => format!("Set<{}>", format_type_for_diagnostic(inner)),
        Type::Map(key, value) => format!(
            "Map<{}, {}>",
            format_type_for_diagnostic(key),
            format_type_for_diagnostic(value)
        ),
        Type::Reference { ty, mutable } => {
            if *mutable {
                format!("&mut {}", format_type_for_diagnostic(ty))
            } else {
                format!("&{}", format_type_for_diagnostic(ty))
            }
        }
        Type::Bool => "bool".to_string(),
        Type::Int => "int".to_string(),
        Type::Nat => "nat".to_string(),
        Type::Unit => "()".to_string(),
    }
}

/// Ingest protocol sources directly from `<proto>.rs` + sibling `types.rs`.
///
/// This is the source-first ingestion path used by Phase 22 model checking work.
/// Given `src/protocol/<Proto>/<proto>.rs`, this function resolves and reads:
/// - `src/protocol/<Proto>/types.rs`
/// - `src/protocol/<Proto>/<proto>.rs`
///
/// and returns both merged schema and parsed spec AST functions.
pub fn ingest_protocol_sources<P: AsRef<Path>>(
    protocol_file: P,
) -> TranspileResult<ProtocolSourceBundle> {
    ingest_protocol_sources_with_types_and_entrypoints(
        protocol_file.as_ref(),
        None,
        "LInit",
        "LNext",
    )
}

/// Ingest protocol sources from `<proto>.rs` and either:
/// - an explicit `types.rs` path, or
/// - inferred sibling `types.rs` next to `<proto>.rs` when no override is provided.
pub fn ingest_protocol_sources_with_types(
    protocol_file: &Path,
    types_file_override: Option<&Path>,
) -> TranspileResult<ProtocolSourceBundle> {
    ingest_protocol_sources_with_types_and_entrypoints(
        protocol_file,
        types_file_override,
        "LInit",
        "LNext",
    )
}

/// Ingest protocol sources with configurable required init/next entrypoint names.
pub fn ingest_protocol_sources_with_types_and_entrypoints(
    protocol_file: &Path,
    types_file_override: Option<&Path>,
    init_name: &str,
    next_name: &str,
) -> TranspileResult<ProtocolSourceBundle> {
    if !protocol_file.exists() {
        return Err(crate::error::TranspileError::Config {
            message: format!(
                "Protocol source file not found: {}",
                protocol_file.display()
            ),
        });
    }
    let protocol_name = protocol_file
        .file_name()
        .and_then(|s| s.to_str())
        .unwrap_or_default();
    if protocol_name == "types.rs" {
        return Err(crate::error::TranspileError::Config {
            message: format!(
                "Protocol source must be <proto>.rs, not types.rs: {}",
                protocol_file.display()
            ),
        });
    }

    let Some(protocol_dir) = protocol_file.parent() else {
        return Err(crate::error::TranspileError::Config {
            message: format!(
                "Cannot resolve protocol directory for {}",
                protocol_file.display()
            ),
        });
    };

    let types_file = if let Some(explicit_types_file) = types_file_override {
        if !explicit_types_file.exists() {
            return Err(crate::error::TranspileError::Config {
                message: format!(
                    "Explicit types source file not found for protocol source {}: {}",
                    protocol_file.display(),
                    explicit_types_file.display()
                ),
            });
        }
        explicit_types_file.to_path_buf()
    } else {
        let inferred_types_file = protocol_dir.join("types.rs");
        if !inferred_types_file.exists() {
            return Err(crate::error::TranspileError::Config {
                message: format!(
                    "Expected sibling types.rs for protocol source {}: missing {}",
                    protocol_file.display(),
                    inferred_types_file.display()
                ),
            });
        }
        inferred_types_file
    };

    let (schema, spec_functions) =
        analyze_spec_files_with_ast(&[types_file.as_path(), protocol_file])?;
    let entrypoints = resolve_required_entrypoints_named(&spec_functions, init_name, next_name)?;

    Ok(ProtocolSourceBundle {
        types_file,
        protocol_file: protocol_file.to_path_buf(),
        schema,
        spec_functions,
        entrypoints,
    })
}

/// Infers `TranspilerConfig` fields from a `SpecSchema`.
///
/// Given a spec schema (types + functions) and naming conventions, derives
/// Tier 1 config sections that are mechanically determinable:
/// - `[remapping]`: L→C type name mappings
/// - `[variant_remapping]`: enum variant → qualified exec path
/// - Field classification: `collection_fields`, `vec_fields`, `clone_fields`, etc.
/// - `clone_field_types`: maps clone_fields to their exec enum type
/// - `clone_strategy`: `external_body` for structs with HashSet fields
/// - `spec_only_functions`: functions with no output-mode params (when `.automan`
///   annotations are available)
///
/// The returned config is partial — callers should merge it with explicit TOML
/// overrides (explicit entries take precedence over auto-derived ones).
pub struct ConfigInferer<'a> {
    schema: &'a SpecSchema,
    naming: &'a NamingConfig,
    annotation_param_modes: HashMap<String, Vec<ParameterMode>>,
    function_path_hints: HashMap<String, String>,
    method_call_hints: HashMap<String, MethodCallConfig>,
    eq_function_field_hints: HashMap<String, String>,
    type_view_expr_hints: HashMap<String, String>,
}

impl<'a> ConfigInferer<'a> {
    pub fn new(schema: &'a SpecSchema, naming: &'a NamingConfig) -> Self {
        Self {
            schema,
            naming,
            annotation_param_modes: HashMap::new(),
            function_path_hints: HashMap::new(),
            method_call_hints: HashMap::new(),
            eq_function_field_hints: HashMap::new(),
            type_view_expr_hints: HashMap::new(),
        }
    }

    /// Create an inferer with parsed `.automan` modules.
    ///
    /// When annotation modes are present, this enables deriving
    /// `spec_only_functions` from functions that have no output (`-`) params.
    pub fn with_annotations(
        schema: &'a SpecSchema,
        naming: &'a NamingConfig,
        modules: &[ModuleAnnotations],
    ) -> Self {
        let mut annotation_param_modes = HashMap::new();
        for module in modules {
            for (name, annotation) in &module.functions {
                annotation_param_modes.insert(name.clone(), annotation.param_modes.clone());
            }
        }
        Self {
            schema,
            naming,
            annotation_param_modes,
            function_path_hints: HashMap::new(),
            method_call_hints: HashMap::new(),
            eq_function_field_hints: HashMap::new(),
            type_view_expr_hints: HashMap::new(),
        }
    }

    /// Attach externally-derived `function_paths` hints.
    ///
    /// This is used for data not present in `SpecSchema` itself (e.g. symbol
    /// discovery from generated/implementation modules).
    pub fn with_function_path_hints(mut self, hints: HashMap<String, String>) -> Self {
        self.function_path_hints = hints;
        self
    }

    /// Attach externally-derived `method_calls` hints.
    ///
    /// This is used for data that depends on implementation symbols rather than
    /// `SpecSchema` alone.
    pub fn with_method_call_hints(mut self, hints: HashMap<String, MethodCallConfig>) -> Self {
        self.method_call_hints = hints;
        self
    }

    /// Attach externally-derived `eq_function_fields` hints.
    ///
    /// This is used for data that depends on implementation helper symbols rather
    /// than `SpecSchema` alone.
    pub fn with_eq_function_field_hints(mut self, hints: HashMap<String, String>) -> Self {
        self.eq_function_field_hints = hints;
        self
    }

    /// Attach externally-derived `type_view_exprs` hints.
    ///
    /// This is used for data that depends on implementation helper symbols rather
    /// than `SpecSchema` alone.
    pub fn with_type_view_expr_hints(mut self, hints: HashMap<String, String>) -> Self {
        self.type_view_expr_hints = hints;
        self
    }

    /// Derive a `TranspilerConfig` with all Tier 1 fields populated.
    pub fn infer(&self) -> TranspilerConfig {
        let mut config = TranspilerConfig::default();
        config.naming = self.naming.clone();

        self.infer_remapping(&mut config);
        self.infer_variant_remapping(&mut config);
        self.infer_function_paths(&mut config);
        self.infer_method_calls(&mut config);
        self.infer_eq_function_fields(&mut config);
        self.infer_type_view_exprs(&mut config);
        self.infer_field_classification(&mut config);
        self.infer_clone_strategy(&mut config);
        self.infer_spec_only_functions(&mut config);
        self.infer_arrow_variants(&mut config);
        self.infer_struct_vec_fields(&mut config);
        self.infer_default_output(&mut config);

        config
    }

    /// Derive `[remapping]` section: L→C type name mappings.
    ///
    /// Rules:
    /// 1. Every struct/enum with `spec_prefix` gets mapped to `exec_prefix` equivalent
    /// 2. Message enum variants get identity mappings (prevent double-prefixing)
    fn infer_remapping(&self, config: &mut TranspilerConfig) {
        let spec_prefix = &self.naming.spec_prefix;
        let exec_prefix = &self.naming.exec_prefix;

        // Map all struct names
        for name in &self.schema.struct_order {
            if name.starts_with(spec_prefix) {
                let base = &name[spec_prefix.len()..];
                let exec_name = format!("{}{}", exec_prefix, base);
                config.remapping.insert(name.clone(), exec_name);
            }
        }

        // Map all enum names + add identity mappings for variants
        for name in &self.schema.enum_order {
            if name.starts_with(spec_prefix) {
                let base = &name[spec_prefix.len()..];
                let exec_name = format!("{}{}", exec_prefix, base);
                config.remapping.insert(name.clone(), exec_name);
            }

            // Add identity mappings for all enum variants to prevent double-prefixing
            if let Some(enum_def) = self.schema.enums.get(name) {
                for variant in &enum_def.variants {
                    // Only add if not already mapped and variant name doesn't start with prefix
                    if !config.remapping.contains_key(&variant.name) {
                        config
                            .remapping
                            .insert(variant.name.clone(), variant.name.clone());
                    }
                }
            }
        }

        // Map type aliases
        for name in &self.schema.alias_order {
            if name.starts_with(spec_prefix) {
                let base = &name[spec_prefix.len()..];
                let exec_name = format!("{}{}", exec_prefix, base);
                config.remapping.insert(name.clone(), exec_name);
            }
        }
    }

    /// Derive `[variant_remapping]` section: bare variant → `CEnum::Variant`.
    ///
    /// For each enum that has a field in a state struct (LState/LConstants),
    /// map each variant to its fully-qualified C-prefixed enum path.
    fn infer_variant_remapping(&self, config: &mut TranspilerConfig) {
        let spec_prefix = &self.naming.spec_prefix;
        let exec_prefix = &self.naming.exec_prefix;

        // Find which enums are used as fields in state structs
        let field_enum_types = self.collect_field_enum_types();

        for enum_name in &field_enum_types {
            let exec_enum_name = if enum_name.starts_with(spec_prefix) {
                let base = &enum_name[spec_prefix.len()..];
                format!("{}{}", exec_prefix, base)
            } else {
                format!("{}{}", exec_prefix, enum_name)
            };

            if let Some(enum_def) = self.schema.enums.get(enum_name) {
                for variant in &enum_def.variants {
                    config.variant_remapping.insert(
                        variant.name.clone(),
                        format!("{}::{}", exec_enum_name, variant.name),
                    );
                }
            }
        }
    }

    /// Derive field classification from struct field types.
    ///
    /// Examines all fields across all structs (primarily LState and LConstants):
    /// - `Set<T>` → `collection_fields`
    /// - `Seq<T>` where T is primitive (int/nat/u64) → `vec_fields`
    /// - `Map<K,V>` where both K,V are primitive → `hashmap_index_fields`
    /// - Enum-typed fields → `clone_fields` + `clone_field_types`
    fn infer_field_classification(&self, config: &mut TranspilerConfig) {
        let spec_prefix = &self.naming.spec_prefix;
        let exec_prefix = &self.naming.exec_prefix;

        // Collect all enum names for detecting enum-typed fields
        let enum_names: Vec<String> = self.schema.enums.keys().cloned().collect();

        for struct_def in self.schema.structs.values() {
            for field in &struct_def.fields {
                match &field.ty {
                    Type::Set(_) => {
                        if !config.collection_fields.contains(&field.name) {
                            config.collection_fields.push(field.name.clone());
                        }
                    }
                    Type::Seq(inner) => {
                        if self.is_primitive_inner_type(inner) {
                            if !config.vec_fields.contains(&field.name) {
                                config.vec_fields.push(field.name.clone());
                            }
                        }
                        // Seq<StructType> → struct_vec_fields handled in Tier 2
                    }
                    Type::Map(key_ty, val_ty) => {
                        if self.is_primitive_inner_type(key_ty)
                            && self.is_primitive_inner_type(val_ty)
                        {
                            if !config.hashmap_index_fields.contains(&field.name) {
                                config.hashmap_index_fields.push(field.name.clone());
                            }
                        }
                        // Map with complex value types → map_fields handled in Tier 2
                    }
                    Type::Named(path) => {
                        let type_name = path.segments.last().unwrap_or(&String::new()).clone();
                        // Check if this is an enum type → clone_fields
                        // Skip unit enums (all-unit variants) since they get #[derive(Copy)]
                        if enum_names.contains(&type_name) {
                            let is_unit_enum = self.schema.enums.get(&type_name)
                                .map_or(false, |e| e.variants.iter().all(|v| {
                                    matches!(v.fields, crate::types::VariantFields::Unit)
                                }));
                            if !is_unit_enum {
                                if !config.clone_fields.contains(&field.name) {
                                    config.clone_fields.push(field.name.clone());
                                }
                                // Derive clone_field_types: field → CEnumName
                                let exec_enum_name = if type_name.starts_with(spec_prefix) {
                                    let base = &type_name[spec_prefix.len()..];
                                    format!("{}{}", exec_prefix, base)
                                } else {
                                    format!("{}{}", exec_prefix, &type_name)
                                };
                                config
                                    .clone_field_types
                                    .insert(field.name.clone(), exec_enum_name);
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
    }

    /// Derive `[clone_strategy]` section.
    ///
    /// Any exec struct that contains a `Set<T>` field (becomes `HashSet` in exec)
    /// needs special clone handling. When ALL Set fields have u64-compatible inner
    /// types (Int, Nat, or named u64), uses "verified" strategy with `clone_hashset_u64`.
    /// Otherwise falls back to "external_body".
    fn infer_clone_strategy(&self, config: &mut TranspilerConfig) {
        let spec_prefix = &self.naming.spec_prefix;
        let exec_prefix = &self.naming.exec_prefix;

        for (struct_name, struct_def) in &self.schema.structs {
            let set_fields: Vec<_> = struct_def
                .fields
                .iter()
                .filter(|f| matches!(&f.ty, Type::Set(_)))
                .collect();

            if !set_fields.is_empty() {
                let exec_name = if struct_name.starts_with(spec_prefix) {
                    let base = &struct_name[spec_prefix.len()..];
                    format!("{}{}", exec_prefix, base)
                } else {
                    struct_name.clone()
                };

                // Check if all Set fields have u64-compatible inner types
                let all_u64_sets = set_fields.iter().all(|f| {
                    if let Type::Set(inner) = &f.ty {
                        match inner.as_ref() {
                            Type::Int | Type::Nat => true,
                            Type::Named(p) => p.last().map_or(false, |n| {
                                n == "u64" || n == "i64" || n == "usize"
                            }),
                            _ => false,
                        }
                    } else {
                        false
                    }
                });

                let strategy = if all_u64_sets {
                    "verified"
                } else {
                    "external_body"
                };
                config
                    .clone_strategy
                    .insert(exec_name, strategy.to_string());
            }
        }
    }

    /// Derive `function_paths` from caller-provided hints.
    fn infer_function_paths(&self, config: &mut TranspilerConfig) {
        if self.function_path_hints.is_empty() {
            return;
        }

        let mut keys: Vec<&String> = self.function_path_hints.keys().collect();
        keys.sort();
        for key in keys {
            if let Some(path) = self.function_path_hints.get(key) {
                config.function_paths.insert(key.clone(), path.clone());
            }
        }
    }

    /// Derive `method_calls` from caller-provided hints.
    fn infer_method_calls(&self, config: &mut TranspilerConfig) {
        if self.method_call_hints.is_empty() {
            return;
        }

        let mut keys: Vec<&String> = self.method_call_hints.keys().collect();
        keys.sort();
        for key in keys {
            if let Some(method_cfg) = self.method_call_hints.get(key) {
                config.method_calls.insert(key.clone(), method_cfg.clone());
            }
        }
    }

    /// Derive `eq_function_fields` from caller-provided hints.
    fn infer_eq_function_fields(&self, config: &mut TranspilerConfig) {
        if self.eq_function_field_hints.is_empty() {
            return;
        }

        let mut keys: Vec<&String> = self.eq_function_field_hints.keys().collect();
        keys.sort();
        for key in keys {
            if let Some(function_name) = self.eq_function_field_hints.get(key) {
                config
                    .eq_function_fields
                    .insert(key.clone(), function_name.clone());
            }
        }
    }

    /// Derive `type_view_exprs` from caller-provided hints.
    fn infer_type_view_exprs(&self, config: &mut TranspilerConfig) {
        if self.type_view_expr_hints.is_empty() {
            return;
        }

        let mut keys: Vec<&String> = self.type_view_expr_hints.keys().collect();
        keys.sort();
        for key in keys {
            if let Some(view_expr) = self.type_view_expr_hints.get(key) {
                config
                    .type_view_exprs
                    .insert(key.clone(), view_expr.clone());
            }
        }
    }

    /// Derive `spec_only_functions` from `.automan` modes.
    ///
    /// A function is spec-only if all annotated parameter modes are input (`+`).
    /// If annotations are unavailable, this inference is skipped.
    fn infer_spec_only_functions(&self, config: &mut TranspilerConfig) {
        if self.annotation_param_modes.is_empty() {
            return;
        }

        let mut function_names: Vec<String> = self.schema.functions.keys().cloned().collect();
        function_names.sort();

        for function_name in function_names {
            let Some(sig) = self.schema.functions.get(&function_name) else {
                continue;
            };
            let Some(param_modes) = self.annotation_param_modes.get(&function_name) else {
                continue;
            };

            // Only trust annotations that match signature arity.
            if param_modes.len() != sig.params.len() {
                continue;
            }

            let has_output_param = param_modes
                .iter()
                .any(|mode| matches!(mode, ParameterMode::Output));
            if !has_output_param && !config.spec_only_functions.contains(&function_name) {
                config.spec_only_functions.push(function_name);
            }
        }
    }

    /// Derive `[arrow_variants]` section: field name → exec variant path.
    ///
    /// For each enum with struct variants (named fields), maps every field name
    /// to its containing variant's fully-qualified exec path. This enables
    /// transforming spec-mode `msg->field` arrow access into exec-level
    /// `match` destructuring.
    ///
    /// Only processes enums whose variants have struct-style named fields.
    /// Unit/tuple variants are skipped.
    fn infer_arrow_variants(&self, config: &mut TranspilerConfig) {
        let spec_prefix = &self.naming.spec_prefix;
        let exec_prefix = &self.naming.exec_prefix;

        for (enum_name, enum_def) in &self.schema.enums {
            // Get the exec enum name from remapping or apply prefix rule
            let exec_enum_name = config.remapping.get(enum_name).cloned().unwrap_or_else(|| {
                if enum_name.starts_with(spec_prefix) {
                    let base = &enum_name[spec_prefix.len()..];
                    format!("{}{}", exec_prefix, base)
                } else {
                    enum_name.clone()
                }
            });

            for variant in &enum_def.variants {
                if let VariantFields::Struct(fields) = &variant.fields {
                    if fields.is_empty() {
                        continue;
                    }
                    // Get the exec variant name from remapping or apply prefix rule
                    let exec_variant_name = config
                        .remapping
                        .get(&variant.name)
                        .cloned()
                        .unwrap_or_else(|| format!("{}{}", exec_prefix, &variant.name));

                    let exec_variant_path = format!("{}::{}", exec_enum_name, exec_variant_name);

                    for field in fields {
                        // Only add if not already mapped (first occurrence wins
                        // if field name appears in multiple variants)
                        if !config.arrow_variants.contains_key(&field.name) {
                            config
                                .arrow_variants
                                .insert(field.name.clone(), exec_variant_path.clone());
                        }
                    }
                }
            }
        }
    }

    /// Derive `[struct_vec_fields]` section.
    ///
    /// Detects `Seq<StructType>` fields where the element type is a struct
    /// (not primitive, not enum). Maps field name → `[CElementType, LElementType]`.
    /// These generate `clone_<field>()` and View-mapped proof helpers.
    fn infer_struct_vec_fields(&self, config: &mut TranspilerConfig) {
        let spec_prefix = &self.naming.spec_prefix;
        let exec_prefix = &self.naming.exec_prefix;

        for struct_def in self.schema.structs.values() {
            for field in &struct_def.fields {
                if let Type::Seq(inner) = &field.ty {
                    // Only for non-primitive struct element types
                    if let Type::Named(path) = inner.as_ref() {
                        let type_name = path.segments.last().unwrap_or(&String::new()).clone();

                        // Skip if primitive
                        if self.is_primitive_inner_type(inner) {
                            continue;
                        }

                        // Skip if enum
                        if self.schema.enums.contains_key(&type_name) {
                            continue;
                        }

                        // It's a struct element type — add to struct_vec_fields
                        if !config.struct_vec_fields.contains_key(&field.name) {
                            let exec_type_name = config
                                .remapping
                                .get(&type_name)
                                .cloned()
                                .unwrap_or_else(|| {
                                    if type_name.starts_with(spec_prefix) {
                                        let base = &type_name[spec_prefix.len()..];
                                        format!("{}{}", exec_prefix, base)
                                    } else {
                                        format!("{}{}", exec_prefix, &type_name)
                                    }
                                });
                            config
                                .struct_vec_fields
                                .insert(field.name.clone(), vec![exec_type_name, type_name]);
                        }
                    }
                }
            }
        }
    }

    /// Set default output flags (generate_* all true, standard validity predicate).
    fn infer_default_output(&self, config: &mut TranspilerConfig) {
        config.output.generate_abstraction_fns = true;
        config.output.generate_validity_predicates = true;
        config.output.validity_predicate_name = "valid".to_string();
        config.output.generate_clone = true;
        config.output.generate_loops_for_verification = true;
        config.output.generate_proofs = true;
        config.output.generate_inline_types = false;
    }

    /// Collect enum type names that appear as struct fields.
    fn collect_field_enum_types(&self) -> Vec<String> {
        let mut result = Vec::new();
        let enum_names: Vec<String> = self.schema.enums.keys().cloned().collect();

        for struct_def in self.schema.structs.values() {
            for field in &struct_def.fields {
                if let Type::Named(path) = &field.ty {
                    if let Some(last) = path.segments.last() {
                        if enum_names.contains(last) && !result.contains(last) {
                            result.push(last.clone());
                        }
                    }
                }
            }
        }
        result
    }

    /// Check if a type is "primitive" for field classification purposes.
    /// Primitive means: int, nat, bool, or a named type that resolves to a
    /// primitive via type alias (e.g., `OperationNumber = u64`).
    fn is_primitive_inner_type(&self, ty: &Type) -> bool {
        match ty {
            Type::Int | Type::Nat | Type::Bool => true,
            Type::Named(path) => {
                let name = path.segments.last().unwrap_or(&String::new()).clone();
                // Check well-known primitives
                if matches!(
                    name.as_str(),
                    "int" | "nat" | "u64" | "i64" | "u32" | "i32" | "usize" | "bool"
                ) {
                    return true;
                }
                // Check if it's a type alias to a primitive
                if let Some(alias) = self.schema.aliases.get(&name) {
                    return self.is_primitive_inner_type(&alias.ty);
                }
                false
            }
            _ => false,
        }
    }
}

/// Merge an auto-inferred config with a manually-written one.
///
/// Explicit TOML entries take precedence over auto-derived values.
/// Only empty/default fields in `base` get filled from `inferred`.
pub fn merge_configs(base: &mut TranspilerConfig, inferred: &TranspilerConfig) {
    // Remapping: add inferred entries that aren't already in base
    for (k, v) in &inferred.remapping {
        if !base.remapping.contains_key(k) {
            base.remapping.insert(k.clone(), v.clone());
        }
    }

    // Variant remapping: add inferred entries not in base
    for (k, v) in &inferred.variant_remapping {
        if !base.variant_remapping.contains_key(k) {
            base.variant_remapping.insert(k.clone(), v.clone());
        }
    }

    // Function paths: add inferred entries not in base
    for (k, v) in &inferred.function_paths {
        if !base.function_paths.contains_key(k) {
            base.function_paths.insert(k.clone(), v.clone());
        }
    }

    // Method calls: add inferred entries not in base
    for (k, v) in &inferred.method_calls {
        if !base.method_calls.contains_key(k) {
            base.method_calls.insert(k.clone(), v.clone());
        }
    }

    // Eq function fields: add inferred entries not in base
    for (k, v) in &inferred.eq_function_fields {
        if !base.eq_function_fields.contains_key(k) {
            base.eq_function_fields.insert(k.clone(), v.clone());
        }
    }

    // Type view expressions: add inferred entries not in base
    for (k, v) in &inferred.type_view_exprs {
        if !base.type_view_exprs.contains_key(k) {
            base.type_view_exprs.insert(k.clone(), v.clone());
        }
    }

    // Spec-only functions: add inferred entries not in base
    for f in &inferred.spec_only_functions {
        if !base.spec_only_functions.contains(f) {
            base.spec_only_functions.push(f.clone());
        }
    }

    // Collection fields: add inferred entries not in base
    for f in &inferred.collection_fields {
        if !base.collection_fields.contains(f) {
            base.collection_fields.push(f.clone());
        }
    }

    // Vec fields: add inferred entries not in base
    for f in &inferred.vec_fields {
        if !base.vec_fields.contains(f) {
            base.vec_fields.push(f.clone());
        }
    }

    // Hashmap index fields: add inferred entries not in base
    for f in &inferred.hashmap_index_fields {
        if !base.hashmap_index_fields.contains(f) {
            base.hashmap_index_fields.push(f.clone());
        }
    }

    // Clone fields: add inferred entries not in base
    for f in &inferred.clone_fields {
        if !base.clone_fields.contains(f) {
            base.clone_fields.push(f.clone());
        }
    }

    // Clone field types: add inferred entries not in base
    for (k, v) in &inferred.clone_field_types {
        if !base.clone_field_types.contains_key(k) {
            base.clone_field_types.insert(k.clone(), v.clone());
        }
    }

    // Clone strategy: add inferred entries not in base
    for (k, v) in &inferred.clone_strategy {
        if !base.clone_strategy.contains_key(k) {
            base.clone_strategy.insert(k.clone(), v.clone());
        }
    }

    // Arrow variants: add inferred entries not in base
    for (k, v) in &inferred.arrow_variants {
        if !base.arrow_variants.contains_key(k) {
            base.arrow_variants.insert(k.clone(), v.clone());
        }
    }

    // Struct vec fields: add inferred entries not in base
    for (k, v) in &inferred.struct_vec_fields {
        if !base.struct_vec_fields.contains_key(k) {
            base.struct_vec_fields.insert(k.clone(), v.clone());
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::annotation::AnnotationParser;
    use crate::ast::{Generics, Path as AstPath, Type};
    use crate::types::{ParamSig, TypeParser};
    use std::fs;
    use tempfile::tempdir;

    #[test]
    fn test_empty_schema() {
        let schema = SpecSchema::new();
        assert_eq!(schema.structs.len(), 0);
        assert_eq!(schema.enums.len(), 0);
        assert_eq!(schema.aliases.len(), 0);
        assert_eq!(schema.functions.len(), 0);
    }

    #[test]
    fn test_schema_from_registry() {
        let mut registry = TypeRegistry::new();
        registry.register_struct(StructDef {
            name: "LState".to_string(),
            generics: Generics::default(),
            fields: vec![],
            is_spec: true,
        });
        registry.register_function(FunctionSig {
            name: "LInit".to_string(),
            generics: Generics::default(),
            params: vec![],
            return_type: Type::Bool,
            is_spec: true,
        });

        let schema = SpecSchema::from_registry(registry);
        assert_eq!(schema.structs.len(), 1);
        assert!(schema.structs.contains_key("LState"));
        assert_eq!(schema.functions.len(), 1);
        assert!(schema.functions.contains_key("LInit"));
    }

    #[test]
    fn test_schema_merge() {
        let mut schema1 = SpecSchema::new();
        schema1.structs.insert(
            "LState".to_string(),
            StructDef {
                name: "LState".to_string(),
                generics: Generics::default(),
                fields: vec![],
                is_spec: true,
            },
        );
        schema1.struct_order.push("LState".to_string());

        let mut schema2 = SpecSchema::new();
        schema2.functions.insert(
            "LInit".to_string(),
            FunctionSig {
                name: "LInit".to_string(),
                generics: Generics::default(),
                params: vec![],
                return_type: Type::Bool,
                is_spec: true,
            },
        );
        schema2.structs.insert(
            "LConstants".to_string(),
            StructDef {
                name: "LConstants".to_string(),
                generics: Generics::default(),
                fields: vec![],
                is_spec: true,
            },
        );
        schema2.struct_order.push("LConstants".to_string());

        schema1.merge(schema2);
        assert_eq!(schema1.structs.len(), 2);
        assert_eq!(schema1.functions.len(), 1);
        assert_eq!(schema1.struct_order, vec!["LState", "LConstants"]);
    }

    #[test]
    fn test_find_variant_with_field() {
        let mut schema = SpecSchema::new();
        schema.enums.insert(
            "LMessage".to_string(),
            EnumDef {
                name: "LMessage".to_string(),
                generics: Generics::default(),
                variants: vec![
                    VariantDef {
                        name: "Msg1a".to_string(),
                        fields: VariantFields::Struct(vec![FieldDef {
                            name: "bal_1a".to_string(),
                            ty: Type::Named(AstPath::single("Ballot".to_string())),
                            is_public: true,
                        }]),
                    },
                    VariantDef {
                        name: "Msg2a".to_string(),
                        fields: VariantFields::Struct(vec![
                            FieldDef {
                                name: "bal_2a".to_string(),
                                ty: Type::Named(AstPath::single("Ballot".to_string())),
                                is_public: true,
                            },
                            FieldDef {
                                name: "val_2a".to_string(),
                                ty: Type::Named(AstPath::single("RequestBatch".to_string())),
                                is_public: true,
                            },
                        ]),
                    },
                ],
                is_spec: true,
            },
        );

        assert_eq!(
            schema.find_variant_with_field("bal_1a"),
            Some(("LMessage".to_string(), "Msg1a".to_string()))
        );
        assert_eq!(
            schema.find_variant_with_field("val_2a"),
            Some(("LMessage".to_string(), "Msg2a".to_string()))
        );
        assert_eq!(schema.find_variant_with_field("nonexistent"), None);
    }

    #[test]
    fn test_parse_spec_fn_from_source() {
        let source = r#"
verus! {
    pub struct LState {
        pub value: int,
    }

    pub open spec fn LInit(s: LState, c: LConstants) -> bool
    {
        s.value == 0
    }

    pub open spec fn LStep(s: LState, s_: LState, c: LConstants, sent_packets: Seq<LMessage>) -> bool
    {
        &&& s_.value == s.value + 1
        &&& sent_packets == Seq::empty()
    }
}
        "#;

        let mut parser = TypeParser::new(source);
        let types = parser.parse_types().unwrap();

        // Should parse: 1 struct + 2 functions
        let structs: Vec<_> = types
            .iter()
            .filter(|t| matches!(t, crate::types::TypeDef::Struct(_)))
            .collect();
        let functions: Vec<_> = types
            .iter()
            .filter(|t| matches!(t, crate::types::TypeDef::Function(_)))
            .collect();

        assert_eq!(structs.len(), 1);
        assert_eq!(functions.len(), 2);

        // Check first function
        match &functions[0] {
            crate::types::TypeDef::Function(f) => {
                assert_eq!(f.name, "LInit");
                assert_eq!(f.params.len(), 2);
                assert_eq!(f.params[0].name, "s");
                assert_eq!(f.params[1].name, "c");
                assert!(matches!(f.return_type, Type::Bool));
                assert!(f.is_spec);
            }
            _ => unreachable!(),
        }

        // Check second function
        match &functions[1] {
            crate::types::TypeDef::Function(f) => {
                assert_eq!(f.name, "LStep");
                assert_eq!(f.params.len(), 4);
                assert_eq!(f.params[0].name, "s");
                assert_eq!(f.params[1].name, "s_");
                assert_eq!(f.params[2].name, "c");
                assert_eq!(f.params[3].name, "sent_packets");
            }
            _ => unreachable!(),
        }
    }

    #[test]
    fn test_parse_spec_fn_with_recommends() {
        let source = r#"
verus! {
    pub open spec fn helper(x: int, y: int) -> bool
        recommends x > 0
    {
        x + y > 0
    }
}
        "#;

        let mut parser = TypeParser::new(source);
        let types = parser.parse_types().unwrap();

        let functions: Vec<_> = types
            .iter()
            .filter(|t| matches!(t, crate::types::TypeDef::Function(_)))
            .collect();

        assert_eq!(functions.len(), 1);
        match &functions[0] {
            crate::types::TypeDef::Function(f) => {
                assert_eq!(f.name, "helper");
                assert_eq!(f.params.len(), 2);
                assert!(matches!(f.return_type, Type::Bool));
            }
            _ => unreachable!(),
        }
    }

    #[test]
    fn test_parse_spec_fn_no_return_type() {
        // Some spec functions don't have explicit -> bool
        let source = r#"
verus! {
    pub open spec fn u64_inc(x: u64) -> u64
    {
        if x < u64::MAX { (x + 1) as u64 } else { x }
    }
}
        "#;

        let mut parser = TypeParser::new(source);
        let types = parser.parse_types().unwrap();

        let functions: Vec<_> = types
            .iter()
            .filter(|t| matches!(t, crate::types::TypeDef::Function(_)))
            .collect();

        assert_eq!(functions.len(), 1);
        match &functions[0] {
            crate::types::TypeDef::Function(f) => {
                assert_eq!(f.name, "u64_inc");
                assert_eq!(f.params.len(), 1);
                // Return type should be u64 (Named type)
                match &f.return_type {
                    Type::Named(path) => assert_eq!(path.segments[0], "u64"),
                    _ => panic!("Expected Named type u64, got {:?}", f.return_type),
                }
            }
            _ => unreachable!(),
        }
    }

    #[test]
    fn test_parse_mixed_types_and_functions() {
        let source = r#"
verus! {
    pub struct LState {
        pub tm_state: LTMState,
        pub rm_states: Map<int, LRMState>,
    }

    pub enum LTMState {
        Init,
        Committed,
        Aborted,
    }

    pub type RequestBatch = Seq<Request>;

    pub open spec fn LInit(s: LState, c: LConstants) -> bool
    {
        &&& s.tm_state is Init
        &&& forall |rm: int| 0 <= rm < c.num_rms ==> s.rm_states[rm] is Working
    }

    pub open spec fn LTMSendPrepare(s: LState, s_: LState, c: LConstants, sent_packets: Seq<LTPCMessage>) -> bool
    {
        &&& s.tm_state is Init
        &&& s_ == s
        &&& sent_packets.len() == c.num_rms
    }
}
        "#;

        let mut parser = TypeParser::new(source);
        let types = parser.parse_types().unwrap();

        let registry = build_registry(types);
        let schema = SpecSchema::from_registry(registry);

        assert_eq!(schema.structs.len(), 1);
        assert!(schema.structs.contains_key("LState"));
        assert_eq!(schema.enums.len(), 1);
        assert!(schema.enums.contains_key("LTMState"));
        assert_eq!(schema.aliases.len(), 1);
        assert!(schema.aliases.contains_key("RequestBatch"));
        assert_eq!(schema.functions.len(), 2);
        assert!(schema.functions.contains_key("LInit"));
        assert!(schema.functions.contains_key("LTMSendPrepare"));

        let summary = schema.summary();
        assert_eq!(
            summary,
            SchemaSummary {
                num_structs: 1,
                num_enums: 1,
                num_aliases: 1,
                num_functions: 2,
            }
        );
    }

    // --- Real protocol spec file tests ---

    #[test]
    fn test_analyze_twophase_types() {
        let path = std::path::Path::new("../src/protocol/TwoPhase/types.rs");
        if !path.exists() {
            return; // Skip if not in workspace
        }
        let schema = analyze_spec_file(path).unwrap();
        // TwoPhase types.rs should have structs and enums
        assert!(
            schema.structs.len() + schema.enums.len() > 0,
            "TwoPhase types.rs should have type definitions"
        );
    }

    #[test]
    fn test_analyze_twophase_protocol() {
        let types_path = std::path::Path::new("../src/protocol/TwoPhase/types.rs");
        let proto_path = std::path::Path::new("../src/protocol/TwoPhase/twophase.rs");
        if !types_path.exists() || !proto_path.exists() {
            return;
        }
        let schema = analyze_spec_files(&[types_path, proto_path]).unwrap();

        // Must have LState, LConstants
        assert!(
            schema.structs.contains_key("LState"),
            "TwoPhase should have LState struct"
        );
        assert!(
            schema.structs.contains_key("LConstants"),
            "TwoPhase should have LConstants struct"
        );

        // Must have LInit function
        assert!(
            schema.functions.contains_key("LInit"),
            "TwoPhase should have LInit function"
        );

        // Should have multiple transition functions
        assert!(
            schema.functions.len() >= 3,
            "TwoPhase should have at least 3 functions, got {}",
            schema.functions.len()
        );

        let summary = schema.summary();
        assert!(summary.num_structs >= 2);
        assert!(summary.num_functions >= 3);
    }

    #[test]
    fn test_ingest_protocol_sources_twophase() {
        let proto_path = std::path::Path::new("../src/protocol/TwoPhase/twophase.rs");
        if !proto_path.exists() {
            return;
        }

        let bundle = ingest_protocol_sources(proto_path).unwrap();
        assert_eq!(
            bundle
                .types_file
                .file_name()
                .and_then(|s| s.to_str())
                .unwrap_or_default(),
            "types.rs"
        );
        assert_eq!(bundle.protocol_file, proto_path);
        assert!(bundle.schema.structs.contains_key("LState"));
        assert!(bundle.schema.functions.contains_key("LInit"));
        assert_eq!(bundle.entrypoints.linit.name, "LInit");
        assert_eq!(bundle.entrypoints.lnext.name, "LNext");
        assert!(
            bundle.spec_functions.iter().any(|f| f.name == "LInit"),
            "ingestion should parse LInit from sources"
        );
        assert!(
            bundle.spec_functions.iter().any(|f| f.name == "LNext"),
            "ingestion should parse LNext from protocol source"
        );
    }

    #[test]
    fn test_resolve_required_entrypoints_named_custom_names() {
        let dir = tempdir().unwrap();
        let types_path = dir.path().join("types.rs");
        let proto_path = dir.path().join("demo.rs");

        fs::write(
            &types_path,
            r#"
verus! {
    pub struct LState { pub value: int }
    pub struct LConstants { pub limit: int }
    pub open spec fn InitCustom(s: LState, c: LConstants) -> bool { s.value <= c.limit }
}
"#,
        )
        .unwrap();
        fs::write(
            &proto_path,
            r#"
verus! {
    pub open spec fn NextCustom(s: LState, s_: LState, c: LConstants) -> bool {
        s_.value <= c.limit && s.value <= c.limit
    }
}
"#,
        )
        .unwrap();

        let (_, spec_functions) =
            analyze_spec_files_with_ast(&[types_path.as_path(), proto_path.as_path()]).unwrap();

        let entrypoints =
            resolve_required_entrypoints_named(&spec_functions, "InitCustom", "NextCustom")
                .unwrap();
        assert_eq!(entrypoints.linit.name, "InitCustom");
        assert_eq!(entrypoints.lnext.name, "NextCustom");
    }

    #[test]
    fn test_resolve_required_entrypoints_named_missing_custom_next() {
        let dir = tempdir().unwrap();
        let types_path = dir.path().join("types.rs");
        let proto_path = dir.path().join("demo.rs");

        fs::write(
            &types_path,
            r#"
verus! {
    pub struct LState { pub value: int }
    pub struct LConstants { pub limit: int }
    pub open spec fn InitCustom(s: LState, c: LConstants) -> bool { s.value <= c.limit }
}
"#,
        )
        .unwrap();
        fs::write(
            &proto_path,
            r#"
verus! {
    pub open spec fn NextOther(s: LState, s_: LState, c: LConstants) -> bool {
        s_.value <= c.limit && s.value <= c.limit
    }
}
"#,
        )
        .unwrap();

        let (_, spec_functions) =
            analyze_spec_files_with_ast(&[types_path.as_path(), proto_path.as_path()]).unwrap();

        let err = resolve_required_entrypoints_named(&spec_functions, "InitCustom", "NextCustom")
            .unwrap_err();
        let msg = err.to_string();
        assert!(msg.contains("Missing required entrypoint `NextCustom"));
        assert!(msg.contains("Fix: add/rename a function to `NextCustom`"));
    }

    #[test]
    fn test_ingest_protocol_sources_with_explicit_types_path() {
        let dir = tempdir().unwrap();
        let explicit_types_path = dir.path().join("custom_types.rs");
        let proto_path = dir.path().join("demo.rs");

        fs::write(
            &explicit_types_path,
            r#"
verus! {
    pub struct LState { pub value: int }
    pub struct LConstants { pub limit: int }
    pub open spec fn LInit(s: LState, c: LConstants) -> bool { s.value <= c.limit }
}
"#,
        )
        .unwrap();
        fs::write(
            &proto_path,
            r#"
verus! {
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        s_.value <= c.limit && s.value <= c.limit
    }
}
"#,
        )
        .unwrap();

        let bundle =
            ingest_protocol_sources_with_types(&proto_path, Some(&explicit_types_path)).unwrap();
        assert_eq!(bundle.types_file, explicit_types_path);
        assert_eq!(bundle.protocol_file, proto_path);
        assert!(bundle.schema.structs.contains_key("LState"));
        assert_eq!(bundle.entrypoints.linit.name, "LInit");
        assert_eq!(bundle.entrypoints.lnext.name, "LNext");
    }

    #[test]
    fn test_ingest_protocol_sources_with_explicit_missing_types_path() {
        let dir = tempdir().unwrap();
        let proto_path = dir.path().join("demo.rs");
        let missing_types_path = dir.path().join("missing_types.rs");

        fs::write(
            &proto_path,
            r#"
verus! {
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        s_.value <= c.limit && s.value <= c.limit
    }
}
"#,
        )
        .unwrap();

        let err =
            ingest_protocol_sources_with_types(&proto_path, Some(&missing_types_path)).unwrap_err();
        assert!(matches!(err, crate::error::TranspileError::Config { .. }));
        assert!(err
            .to_string()
            .contains("Explicit types source file not found"));
    }

    #[test]
    fn test_ingest_protocol_sources_missing_required_lnext() {
        let dir = tempdir().unwrap();
        let types_path = dir.path().join("types.rs");
        let proto_path = dir.path().join("demo.rs");

        fs::write(
            &types_path,
            r#"
verus! {
    pub struct LState { pub value: int }
    pub struct LConstants { pub limit: int }
    pub open spec fn LInit(s: LState, c: LConstants) -> bool { s.value <= c.limit }
}
"#,
        )
        .unwrap();
        fs::write(
            &proto_path,
            r#"
verus! {
    pub open spec fn LStep(s: LState, s_: LState, c: LConstants) -> bool { s_.value <= c.limit && s.value <= c.limit }
}
"#,
        )
        .unwrap();

        let err = ingest_protocol_sources(&proto_path).unwrap_err();
        assert!(matches!(err, crate::error::TranspileError::Config { .. }));
        let msg = err.to_string();
        assert!(msg.contains("Missing required entrypoint `LNext"));
        assert!(msg.contains("Fix: add/rename a function to `LNext`"));
    }

    #[test]
    fn test_ingest_protocol_sources_rejects_incompatible_linit_signature() {
        let dir = tempdir().unwrap();
        let types_path = dir.path().join("types.rs");
        let proto_path = dir.path().join("demo.rs");

        fs::write(
            &types_path,
            r#"
verus! {
    pub struct LState { pub value: int }
    pub struct LConstants { pub limit: int }
    pub open spec fn LInit(state: LState, c: LConstants) -> bool { state.value <= c.limit }
}
"#,
        )
        .unwrap();
        fs::write(
            &proto_path,
            r#"
verus! {
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool { s_.value <= c.limit && s.value <= c.limit }
}
"#,
        )
        .unwrap();

        let err = ingest_protocol_sources(&proto_path).unwrap_err();
        assert!(matches!(err, crate::error::TranspileError::Config { .. }));
        let msg = err.to_string();
        assert!(msg.contains("Incompatible `LInit` signature"));
        assert!(msg.contains("Expected: LInit(s: LState, c: LConstants) -> bool"));
        assert!(msg.contains("expected first parameter name `s`, found `state`"));
    }

    #[test]
    fn test_analyze_spec_files_with_ast_derives_function_signatures_from_parser() {
        let dir = tempdir().unwrap();
        let types_path = dir.path().join("types.rs");
        let proto_path = dir.path().join("demo.rs");

        fs::write(
            &types_path,
            r#"
verus! {
    pub struct LState {
        pub value: int,
    }

    pub struct LConstants {
        pub limit: int,
    }

    pub open spec fn LInit(s: LState, Ghost g: int) -> bool {
        g >= s.value
    }
}
"#,
        )
        .unwrap();
        fs::write(
            &proto_path,
            r#"
verus! {
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        s_.value <= c.limit && s.value <= c.limit
    }
}
"#,
        )
        .unwrap();

        let (schema, spec_functions) =
            analyze_spec_files_with_ast(&[types_path.as_path(), proto_path.as_path()]).unwrap();
        let function_names: Vec<&str> = spec_functions.iter().map(|f| f.name.as_str()).collect();

        assert_eq!(
            function_names,
            vec!["LInit", "LNext"],
            "spec functions should be returned in file order"
        );
        assert!(schema.functions.contains_key("LInit"));
        assert!(schema.functions.contains_key("LNext"));

        let init_sig = schema.functions.get("LInit").unwrap();
        assert_eq!(init_sig.params.len(), 2);
        assert_eq!(init_sig.params[1].name, "g");
        assert!(matches!(init_sig.params[1].ty, Type::Int));
    }

    #[test]
    fn test_ingest_protocol_sources_missing_types_file() {
        let dir = tempdir().unwrap();
        let proto_path = dir.path().join("demo.rs");
        fs::write(
            &proto_path,
            "verus! { pub open spec fn LInit() -> bool { true } }",
        )
        .unwrap();

        let err = ingest_protocol_sources(&proto_path).unwrap_err();
        assert!(matches!(err, crate::error::TranspileError::Config { .. }));
        assert!(err.to_string().contains("missing"));
    }

    #[test]
    fn test_ingest_protocol_sources_rejects_types_rs_input() {
        let dir = tempdir().unwrap();
        let types_path = dir.path().join("types.rs");
        fs::write(&types_path, "verus! {}").unwrap();

        let err = ingest_protocol_sources(&types_path).unwrap_err();
        assert!(matches!(err, crate::error::TranspileError::Config { .. }));
        assert!(err.to_string().contains("not types.rs"));
    }

    #[test]
    fn test_analyze_paxos_protocol() {
        let types_path = std::path::Path::new("../src/protocol/Paxos/types.rs");
        let proto_path = std::path::Path::new("../src/protocol/Paxos/paxos.rs");
        if !types_path.exists() || !proto_path.exists() {
            return;
        }
        let schema = analyze_spec_files(&[types_path, proto_path]).unwrap();
        assert!(schema.structs.contains_key("LState"));
        assert!(schema.structs.contains_key("LConstants"));
        assert!(schema.functions.contains_key("LInit"));
        assert!(schema.functions.len() >= 3);
    }

    #[test]
    fn test_analyze_leaderelection_protocol() {
        let types_path = std::path::Path::new("../src/protocol/LeaderElection/types.rs");
        let proto_path = std::path::Path::new("../src/protocol/LeaderElection/election.rs");
        if !types_path.exists() || !proto_path.exists() {
            return;
        }
        let schema = analyze_spec_files(&[types_path, proto_path]).unwrap();
        assert!(schema.structs.contains_key("LState"));
        assert!(schema.structs.contains_key("LConstants"));
        assert!(schema.functions.contains_key("LInit"));
        assert!(schema.functions.len() >= 3);
    }

    #[test]
    fn test_analyze_raft_protocol() {
        let types_path = std::path::Path::new("../src/protocol/Raft/types.rs");
        let proto_path = std::path::Path::new("../src/protocol/Raft/raft.rs");
        if !types_path.exists() || !proto_path.exists() {
            return;
        }
        let schema = analyze_spec_files(&[types_path, proto_path]).unwrap();
        assert!(schema.structs.contains_key("LState"));
        assert!(schema.structs.contains_key("LConstants"));
        assert!(schema.functions.contains_key("LInit"));
        assert!(schema.functions.len() >= 5);
    }

    #[test]
    fn test_analyze_chainreplication_protocol() {
        let types_path = std::path::Path::new("../src/protocol/ChainReplication/types.rs");
        let proto_path = std::path::Path::new("../src/protocol/ChainReplication/chain.rs");
        if !types_path.exists() || !proto_path.exists() {
            return;
        }
        let schema = analyze_spec_files(&[types_path, proto_path]).unwrap();
        assert!(schema.structs.contains_key("LState"));
        assert!(schema.structs.contains_key("LConstants"));
        assert!(schema.functions.contains_key("LInit"));
        assert!(schema.functions.len() >= 3);
    }

    #[test]
    fn test_analyze_primarybackup_protocol() {
        let types_path = std::path::Path::new("../src/protocol/PrimaryBackup/types.rs");
        let proto_path = std::path::Path::new("../src/protocol/PrimaryBackup/primarybackup.rs");
        if !types_path.exists() || !proto_path.exists() {
            return;
        }
        let schema = analyze_spec_files(&[types_path, proto_path]).unwrap();
        assert!(schema.structs.contains_key("LState"));
        assert!(schema.structs.contains_key("LConstants"));
        assert!(schema.functions.contains_key("LInit"));
        assert!(schema.functions.len() >= 3);
    }

    #[test]
    fn test_analyze_pbft_protocol() {
        let types_path = std::path::Path::new("../src/protocol/PBFT/types.rs");
        let proto_path = std::path::Path::new("../src/protocol/PBFT/pbft.rs");
        if !types_path.exists() || !proto_path.exists() {
            return;
        }
        let schema = analyze_spec_files(&[types_path, proto_path]).unwrap();
        assert!(schema.structs.contains_key("LState"));
        assert!(schema.structs.contains_key("LConstants"));
        assert!(schema.functions.contains_key("LInit"));
        assert!(schema.functions.len() >= 3);
    }

    #[test]
    fn test_analyze_verticalpaxos_protocol() {
        let types_path = std::path::Path::new("../src/protocol/VerticalPaxos/types.rs");
        let proto_path = std::path::Path::new("../src/protocol/VerticalPaxos/vpaxos.rs");
        if !types_path.exists() || !proto_path.exists() {
            return;
        }
        let schema = analyze_spec_files(&[types_path, proto_path]).unwrap();
        assert!(schema.structs.contains_key("LState"));
        assert!(schema.structs.contains_key("LConstants"));
        assert!(schema.functions.contains_key("LInit"));
        assert!(schema.functions.len() >= 3);
    }

    #[test]
    fn test_analyze_epaxos_protocol() {
        let types_path = std::path::Path::new("../src/protocol/EPaxos/types.rs");
        let proto_path = std::path::Path::new("../src/protocol/EPaxos/epaxos.rs");
        if !types_path.exists() || !proto_path.exists() {
            return;
        }
        let schema = analyze_spec_files(&[types_path, proto_path]).unwrap();
        assert!(schema.structs.contains_key("LState"));
        assert!(schema.structs.contains_key("LConstants"));
        assert!(schema.functions.contains_key("LInit"));
        assert!(schema.functions.len() >= 3);
    }

    #[test]
    fn test_analyze_all_protocols_summary() {
        // Test that all 10 protocols can be analyzed and print summary
        let protocols = vec![
            ("TwoPhase", "types.rs", "twophase.rs"),
            ("Paxos", "types.rs", "paxos.rs"),
            ("LeaderElection", "types.rs", "election.rs"),
            ("Raft", "types.rs", "raft.rs"),
            ("ChainReplication", "types.rs", "chain.rs"),
            ("PrimaryBackup", "types.rs", "primarybackup.rs"),
            ("PBFT", "types.rs", "pbft.rs"),
            ("VerticalPaxos", "types.rs", "vpaxos.rs"),
            ("EPaxos", "types.rs", "epaxos.rs"),
        ];

        let mut all_ok = true;
        for (name, types_file, proto_file) in &protocols {
            let types_path =
                std::path::PathBuf::from(format!("../src/protocol/{}/{}", name, types_file));
            let proto_path =
                std::path::PathBuf::from(format!("../src/protocol/{}/{}", name, proto_file));

            if !types_path.exists() || !proto_path.exists() {
                continue;
            }

            match analyze_spec_files(&[types_path.as_path(), proto_path.as_path()]) {
                Ok(schema) => {
                    let summary = schema.summary();
                    // Every protocol should have at least: LState, LConstants, LInit
                    assert!(
                        summary.num_structs >= 2,
                        "{}: expected >= 2 structs, got {}",
                        name,
                        summary.num_structs
                    );
                    assert!(
                        summary.num_functions >= 2,
                        "{}: expected >= 2 functions, got {}",
                        name,
                        summary.num_functions
                    );
                }
                Err(e) => {
                    panic!("{}: failed to analyze: {}", name, e);
                }
            }
        }
    }

    // --- ConfigInferer tests ---

    fn default_naming() -> NamingConfig {
        NamingConfig {
            spec_prefix: "L".to_string(),
            exec_prefix: "C".to_string(),
            int_type: "u64".to_string(),
            nat_type: "u64".to_string(),
            ..NamingConfig::default()
        }
    }

    #[test]
    fn test_infer_remapping_basic() {
        let source = r#"
verus! {
    pub struct LState {
        pub value: int,
    }

    pub struct LConstants {
        pub num_rms: int,
    }

    pub enum LTMState {
        Init,
        Committed,
        Aborted,
    }
}
        "#;
        let mut parser = TypeParser::new(source);
        let types = parser.parse_types().unwrap();
        let registry = build_registry(types);
        let schema = SpecSchema::from_registry(registry);
        let naming = default_naming();
        let inferer = ConfigInferer::new(&schema, &naming);
        let config = inferer.infer();

        // Struct remappings
        assert_eq!(config.remapping.get("LState").unwrap(), "CState");
        assert_eq!(config.remapping.get("LConstants").unwrap(), "CConstants");

        // Enum remapping
        assert_eq!(config.remapping.get("LTMState").unwrap(), "CTMState");

        // Variant identity mappings (prevent double-prefixing)
        assert_eq!(config.remapping.get("Init").unwrap(), "Init");
        assert_eq!(config.remapping.get("Committed").unwrap(), "Committed");
        assert_eq!(config.remapping.get("Aborted").unwrap(), "Aborted");
    }

    #[test]
    fn test_infer_variant_remapping() {
        let source = r#"
verus! {
    pub struct LState {
        pub tm_state: LTMState,
    }

    pub enum LTMState {
        Init,
        Committed,
        Aborted,
    }
}
        "#;
        let mut parser = TypeParser::new(source);
        let types = parser.parse_types().unwrap();
        let registry = build_registry(types);
        let schema = SpecSchema::from_registry(registry);
        let naming = default_naming();
        let inferer = ConfigInferer::new(&schema, &naming);
        let config = inferer.infer();

        // Variant remapping: bare name → CEnumName::Variant
        assert_eq!(
            config.variant_remapping.get("Init").unwrap(),
            "CTMState::Init"
        );
        assert_eq!(
            config.variant_remapping.get("Committed").unwrap(),
            "CTMState::Committed"
        );
        assert_eq!(
            config.variant_remapping.get("Aborted").unwrap(),
            "CTMState::Aborted"
        );
    }

    #[test]
    fn test_infer_variant_remapping_only_field_enums() {
        // Enums NOT used as struct fields should NOT get variant remapping
        let source = r#"
verus! {
    pub struct LState {
        pub value: int,
    }

    pub enum LUnusedEnum {
        A,
        B,
    }
}
        "#;
        let mut parser = TypeParser::new(source);
        let types = parser.parse_types().unwrap();
        let registry = build_registry(types);
        let schema = SpecSchema::from_registry(registry);
        let naming = default_naming();
        let inferer = ConfigInferer::new(&schema, &naming);
        let config = inferer.infer();

        // No variant remapping since the enum is not used as a field
        assert!(config.variant_remapping.is_empty());
    }

    #[test]
    fn test_infer_collection_fields() {
        let source = r#"
verus! {
    pub struct LState {
        pub prepared: Set<int>,
        pub committed: Set<int>,
        pub value: int,
    }

    pub struct LConstants {
        pub nodes: Set<int>,
    }
}
        "#;
        let mut parser = TypeParser::new(source);
        let types = parser.parse_types().unwrap();
        let registry = build_registry(types);
        let schema = SpecSchema::from_registry(registry);
        let naming = default_naming();
        let inferer = ConfigInferer::new(&schema, &naming);
        let config = inferer.infer();

        // Set<T> fields → collection_fields
        assert!(config.collection_fields.contains(&"prepared".to_string()));
        assert!(config.collection_fields.contains(&"committed".to_string()));
        assert!(config.collection_fields.contains(&"nodes".to_string()));
        assert_eq!(config.collection_fields.len(), 3);
    }

    #[test]
    fn test_infer_vec_fields() {
        let source = r#"
verus! {
    pub struct LState {
        pub history: Seq<int>,
    }
}
        "#;
        let mut parser = TypeParser::new(source);
        let types = parser.parse_types().unwrap();
        let registry = build_registry(types);
        let schema = SpecSchema::from_registry(registry);
        let naming = default_naming();
        let inferer = ConfigInferer::new(&schema, &naming);
        let config = inferer.infer();

        assert!(config.vec_fields.contains(&"history".to_string()));
    }

    #[test]
    fn test_infer_hashmap_index_fields() {
        let source = r#"
verus! {
    pub struct LState {
        pub match_index: Map<u64, u64>,
        pub next_index: Map<u64, u64>,
    }
}
        "#;
        let mut parser = TypeParser::new(source);
        let types = parser.parse_types().unwrap();
        let registry = build_registry(types);
        let schema = SpecSchema::from_registry(registry);
        let naming = default_naming();
        let inferer = ConfigInferer::new(&schema, &naming);
        let config = inferer.infer();

        assert!(config
            .hashmap_index_fields
            .contains(&"match_index".to_string()));
        assert!(config
            .hashmap_index_fields
            .contains(&"next_index".to_string()));
    }

    #[test]
    fn test_infer_clone_fields_and_types() {
        let source = r#"
verus! {
    pub struct LState {
        pub role: LServerRole,
        pub term: int,
    }

    pub enum LServerRole {
        Follower,
        Candidate,
        Leader,
    }
}
        "#;
        let mut parser = TypeParser::new(source);
        let types = parser.parse_types().unwrap();
        let registry = build_registry(types);
        let schema = SpecSchema::from_registry(registry);
        let naming = default_naming();
        let inferer = ConfigInferer::new(&schema, &naming);
        let config = inferer.infer();

        // Unit enums (all-unit variants) are Copy → NOT in clone_fields
        assert!(!config.clone_fields.contains(&"role".to_string()));
        assert_eq!(config.clone_fields.len(), 0);
        assert!(config.clone_field_types.get("role").is_none());
    }

    #[test]
    fn test_infer_clone_strategy() {
        let source = r#"
verus! {
    pub struct LState {
        pub prepared: Set<int>,
        pub value: int,
    }

    pub struct LConstants {
        pub nodes: Set<int>,
    }

    pub struct LConfig {
        pub count: int,
    }
}
        "#;
        let mut parser = TypeParser::new(source);
        let types = parser.parse_types().unwrap();
        let registry = build_registry(types);
        let schema = SpecSchema::from_registry(registry);
        let naming = default_naming();
        let inferer = ConfigInferer::new(&schema, &naming);
        let config = inferer.infer();

        // Structs with Set<int> fields get verified clone (u64-compatible inner type)
        assert_eq!(
            config.clone_strategy.get("CState").unwrap(),
            "verified"
        );
        assert_eq!(
            config.clone_strategy.get("CConstants").unwrap(),
            "verified"
        );
        // Structs without Set fields should NOT need special clone strategy
        assert!(!config.clone_strategy.contains_key("CConfig"));
    }

    #[test]
    fn test_infer_spec_only_functions_from_annotations() {
        let source = r#"
verus! {
    pub open spec fn LInit(s: LState, c: LConstants) -> bool { true }
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants, sent_packets: Seq<LMessage>) -> bool { true }
    pub open spec fn WellFormedLConfiguration(c: LConstants) -> bool { true }
}
        "#;
        let mut parser = TypeParser::new(source);
        let types = parser.parse_types().unwrap();
        let registry = build_registry(types);
        let schema = SpecSchema::from_registry(registry);
        let naming = default_naming();

        let annotation_source = r#"
module Test {
    LInit(-, +);
    LNext(+, -, +, -);
    WellFormedLConfiguration(+);
}
        "#;
        let modules = AnnotationParser::new(annotation_source.to_string())
            .parse()
            .unwrap();

        let inferer = ConfigInferer::with_annotations(&schema, &naming, &modules);
        let config = inferer.infer();

        assert!(config
            .spec_only_functions
            .contains(&"WellFormedLConfiguration".to_string()));
        assert!(!config.spec_only_functions.contains(&"LInit".to_string()));
        assert!(!config.spec_only_functions.contains(&"LNext".to_string()));
    }

    #[test]
    fn test_infer_spec_only_functions_without_annotations() {
        let source = r#"
verus! {
    pub open spec fn WellFormedLConfiguration(c: LConstants) -> bool { true }
}
        "#;
        let mut parser = TypeParser::new(source);
        let types = parser.parse_types().unwrap();
        let registry = build_registry(types);
        let schema = SpecSchema::from_registry(registry);
        let naming = default_naming();

        let inferer = ConfigInferer::new(&schema, &naming);
        let config = inferer.infer();

        assert!(config.spec_only_functions.is_empty());
    }

    #[test]
    fn test_infer_default_output_flags() {
        let schema = SpecSchema::new();
        let naming = default_naming();
        let inferer = ConfigInferer::new(&schema, &naming);
        let config = inferer.infer();

        assert!(config.output.generate_abstraction_fns);
        assert!(config.output.generate_validity_predicates);
        assert_eq!(config.output.validity_predicate_name, "valid");
        assert!(config.output.generate_clone);
        assert!(config.output.generate_loops_for_verification);
        assert!(config.output.generate_proofs);
        assert!(!config.output.generate_inline_types);
    }

    #[test]
    fn test_infer_function_paths_from_hints() {
        let schema = SpecSchema::new();
        let naming = default_naming();
        let mut hints = HashMap::new();
        hints.insert(
            "BroadcastToEveryone".to_string(),
            "crate::generated::RSL::broadcast_gen::CBroadcastToEveryone".to_string(),
        );

        let inferer = ConfigInferer::new(&schema, &naming).with_function_path_hints(hints);
        let config = inferer.infer();

        assert_eq!(
            config.function_paths.get("BroadcastToEveryone"),
            Some(&"crate::generated::RSL::broadcast_gen::CBroadcastToEveryone".to_string())
        );
    }

    #[test]
    fn test_infer_method_calls_from_hints() {
        let schema = SpecSchema::new();
        let naming = default_naming();
        let mut hints = HashMap::new();
        hints.insert(
            "GetReplicaIndex".to_string(),
            MethodCallConfig {
                method_name: "CGetReplicaIndex".to_string(),
                receiver_arg_index: 1,
                destructure_index: Some(1),
            },
        );

        let inferer = ConfigInferer::new(&schema, &naming).with_method_call_hints(hints);
        let config = inferer.infer();

        let inferred = config
            .method_calls
            .get("GetReplicaIndex")
            .expect("method call should be inferred");
        assert_eq!(inferred.method_name, "CGetReplicaIndex");
        assert_eq!(inferred.receiver_arg_index, 1);
        assert_eq!(inferred.destructure_index, Some(1));
    }

    #[test]
    fn test_infer_eq_function_fields_from_hints() {
        let schema = SpecSchema::new();
        let naming = default_naming();
        let mut hints = HashMap::new();
        hints.insert("current_view".to_string(), "CBalEq".to_string());
        hints.insert("bal_1b".to_string(), "CBalEq".to_string());

        let inferer = ConfigInferer::new(&schema, &naming).with_eq_function_field_hints(hints);
        let config = inferer.infer();

        assert_eq!(
            config.eq_function_fields.get("current_view"),
            Some(&"CBalEq".to_string())
        );
        assert_eq!(
            config.eq_function_fields.get("bal_1b"),
            Some(&"CBalEq".to_string())
        );
    }

    #[test]
    fn test_infer_type_view_exprs_from_hints() {
        let schema = SpecSchema::new();
        let naming = default_naming();
        let mut hints = HashMap::new();
        hints.insert(
            "Votes".to_string(),
            "abstractify_cvotes({param})".to_string(),
        );

        let inferer = ConfigInferer::new(&schema, &naming).with_type_view_expr_hints(hints);
        let config = inferer.infer();

        assert_eq!(
            config.type_view_exprs.get("Votes"),
            Some(&"abstractify_cvotes({param})".to_string())
        );
    }

    #[test]
    fn test_merge_configs_explicit_overrides_inferred() {
        let mut base = TranspilerConfig::default();
        base.remapping
            .insert("LState".to_string(), "MyCustomState".to_string());
        base.spec_only_functions.push("AlreadyExplicit".to_string());
        base.eq_function_fields
            .insert("current_view".to_string(), "CustomEq".to_string());
        base.type_view_exprs
            .insert("Votes".to_string(), "custom_votes({param})".to_string());

        let mut inferred = TranspilerConfig::default();
        inferred
            .remapping
            .insert("LState".to_string(), "CState".to_string());
        inferred
            .remapping
            .insert("LConstants".to_string(), "CConstants".to_string());
        inferred.collection_fields.push("prepared".to_string());
        inferred.function_paths.insert(
            "BroadcastToEveryone".to_string(),
            "crate::generated::RSL::broadcast_gen::CBroadcastToEveryone".to_string(),
        );
        inferred.method_calls.insert(
            "GetReplicaIndex".to_string(),
            MethodCallConfig {
                method_name: "CGetReplicaIndex".to_string(),
                receiver_arg_index: 1,
                destructure_index: Some(1),
            },
        );
        inferred
            .eq_function_fields
            .insert("current_view".to_string(), "CBalEq".to_string());
        inferred
            .eq_function_fields
            .insert("bal_1b".to_string(), "CBalEq".to_string());
        inferred.type_view_exprs.insert(
            "Votes".to_string(),
            "abstractify_cvotes({param})".to_string(),
        );
        inferred.type_view_exprs.insert(
            "RequestBatch".to_string(),
            "abstractify_crequestbatch({param})".to_string(),
        );
        inferred
            .spec_only_functions
            .push("WellFormedLConfiguration".to_string());
        inferred
            .spec_only_functions
            .push("AlreadyExplicit".to_string());

        merge_configs(&mut base, &inferred);

        // Explicit override wins
        assert_eq!(base.remapping.get("LState").unwrap(), "MyCustomState");
        // Inferred entry added where base was empty
        assert_eq!(base.remapping.get("LConstants").unwrap(), "CConstants");
        assert!(base.collection_fields.contains(&"prepared".to_string()));
        assert_eq!(
            base.function_paths.get("BroadcastToEveryone"),
            Some(&"crate::generated::RSL::broadcast_gen::CBroadcastToEveryone".to_string())
        );
        assert_eq!(
            base.method_calls.get("GetReplicaIndex").map(|mc| (
                &mc.method_name,
                mc.receiver_arg_index,
                mc.destructure_index
            )),
            Some((&"CGetReplicaIndex".to_string(), 1, Some(1)))
        );
        assert_eq!(
            base.eq_function_fields.get("current_view"),
            Some(&"CustomEq".to_string())
        );
        assert_eq!(
            base.eq_function_fields.get("bal_1b"),
            Some(&"CBalEq".to_string())
        );
        assert_eq!(
            base.type_view_exprs.get("Votes"),
            Some(&"custom_votes({param})".to_string())
        );
        assert_eq!(
            base.type_view_exprs.get("RequestBatch"),
            Some(&"abstractify_crequestbatch({param})".to_string())
        );
        assert!(base
            .spec_only_functions
            .contains(&"AlreadyExplicit".to_string()));
        assert!(base
            .spec_only_functions
            .contains(&"WellFormedLConfiguration".to_string()));
        assert_eq!(base.spec_only_functions.len(), 2);
    }

    #[test]
    fn test_infer_twophase_matches_toml() {
        let types_path = std::path::Path::new("../src/protocol/TwoPhase/types.rs");
        let proto_path = std::path::Path::new("../src/protocol/TwoPhase/twophase.rs");
        if !types_path.exists() || !proto_path.exists() {
            return;
        }
        let schema = analyze_spec_files(&[types_path, proto_path]).unwrap();
        let naming = default_naming();
        let inferer = ConfigInferer::new(&schema, &naming);
        let config = inferer.infer();

        // Check remappings match what the existing TOML has
        assert_eq!(config.remapping.get("LState").unwrap(), "CState");
        assert_eq!(config.remapping.get("LConstants").unwrap(), "CConstants");
        assert_eq!(config.remapping.get("LTMState").unwrap(), "CTMState");
        assert_eq!(config.remapping.get("LRMState").unwrap(), "CRMState");
        assert_eq!(config.remapping.get("LTPCMessage").unwrap(), "CTPCMessage");

        // Variant identity mappings
        assert_eq!(config.remapping.get("Prepare").unwrap(), "Prepare");
        assert_eq!(config.remapping.get("Commit").unwrap(), "Commit");

        // Variant remapping (LTMState is used as field in LState)
        assert_eq!(
            config.variant_remapping.get("Init").unwrap(),
            "CTMState::Init"
        );
        assert_eq!(
            config.variant_remapping.get("Committed").unwrap(),
            "CTMState::Committed"
        );
        assert_eq!(
            config.variant_remapping.get("Aborted").unwrap(),
            "CTMState::Aborted"
        );

        // Collection fields (Set<int> fields)
        assert!(config
            .collection_fields
            .contains(&"tm_prepared".to_string()));
        assert!(config
            .collection_fields
            .contains(&"rm_prepared".to_string()));
        assert!(config
            .collection_fields
            .contains(&"rm_committed".to_string()));
        assert!(config.collection_fields.contains(&"rm_aborted".to_string()));
        assert!(config.collection_fields.contains(&"rm".to_string()));

        // Unit enums (CTMState) → Copy, NOT in clone_fields
        assert!(!config.clone_fields.contains(&"tm_state".to_string()));
        assert!(config.clone_field_types.get("tm_state").is_none());

        // Clone strategy (LState has Set<int> fields → verified)
        assert_eq!(
            config.clone_strategy.get("CState").unwrap(),
            "verified"
        );
    }

    #[test]
    fn test_infer_paxos_matches_toml() {
        let types_path = std::path::Path::new("../src/protocol/Paxos/types.rs");
        let proto_path = std::path::Path::new("../src/protocol/Paxos/paxos.rs");
        if !types_path.exists() || !proto_path.exists() {
            return;
        }
        let schema = analyze_spec_files(&[types_path, proto_path]).unwrap();
        let naming = default_naming();
        let inferer = ConfigInferer::new(&schema, &naming);
        let config = inferer.infer();

        // Remappings
        assert_eq!(config.remapping.get("LState").unwrap(), "CState");
        assert_eq!(config.remapping.get("LPhase").unwrap(), "CPhase");

        // Variant remapping (LPhase used as field in LState)
        assert_eq!(
            config.variant_remapping.get("Idle").unwrap(),
            "CPhase::Idle"
        );
        assert_eq!(
            config.variant_remapping.get("Phase1").unwrap(),
            "CPhase::Phase1"
        );
        assert_eq!(
            config.variant_remapping.get("Phase2").unwrap(),
            "CPhase::Phase2"
        );
        assert_eq!(
            config.variant_remapping.get("Decided").unwrap(),
            "CPhase::Decided"
        );

        // Collection fields
        assert!(config
            .collection_fields
            .contains(&"promises_rcvd".to_string()));
        assert!(config
            .collection_fields
            .contains(&"accepts_rcvd".to_string()));

        // Unit enums (CPhase) → Copy, NOT in clone_fields
        assert!(!config.clone_fields.contains(&"phase".to_string()));
        assert!(config.clone_field_types.get("phase").is_none());
    }

    #[test]
    fn test_infer_raft_matches_toml() {
        let types_path = std::path::Path::new("../src/protocol/Raft/types.rs");
        let proto_path = std::path::Path::new("../src/protocol/Raft/raft.rs");
        if !types_path.exists() || !proto_path.exists() {
            return;
        }
        let schema = analyze_spec_files(&[types_path, proto_path]).unwrap();
        let naming = default_naming();
        let inferer = ConfigInferer::new(&schema, &naming);
        let config = inferer.infer();

        // Remappings
        assert_eq!(config.remapping.get("LState").unwrap(), "CState");
        assert_eq!(config.remapping.get("LServerRole").unwrap(), "CServerRole");
        assert_eq!(config.remapping.get("LLogEntry").unwrap(), "CLogEntry");

        // Variant remapping
        assert_eq!(
            config.variant_remapping.get("Follower").unwrap(),
            "CServerRole::Follower"
        );
        assert_eq!(
            config.variant_remapping.get("Candidate").unwrap(),
            "CServerRole::Candidate"
        );
        assert_eq!(
            config.variant_remapping.get("Leader").unwrap(),
            "CServerRole::Leader"
        );

        // Collection fields
        assert!(config
            .collection_fields
            .contains(&"votes_granted".to_string()));

        // Unit enums (CServerRole) → Copy, NOT in clone_fields
        assert!(!config.clone_fields.contains(&"role".to_string()));
        assert!(config.clone_field_types.get("role").is_none());

        // Clone strategy (Raft CState has Set<int> fields → verified)
        assert_eq!(
            config.clone_strategy.get("CState").unwrap(),
            "verified"
        );
    }

    #[test]
    fn test_infer_leaderelection_matches_toml() {
        let types_path = std::path::Path::new("../src/protocol/LeaderElection/types.rs");
        let proto_path = std::path::Path::new("../src/protocol/LeaderElection/election.rs");
        if !types_path.exists() || !proto_path.exists() {
            return;
        }
        let schema = analyze_spec_files(&[types_path, proto_path]).unwrap();
        let naming = default_naming();
        let inferer = ConfigInferer::new(&schema, &naming);
        let config = inferer.infer();

        // Collection fields
        assert!(config.collection_fields.contains(&"electing".to_string()));
        assert!(config.collection_fields.contains(&"alive".to_string()));
        assert!(config.collection_fields.contains(&"nodes".to_string()));
    }

    #[test]
    fn test_infer_all_protocols() {
        // Verify ConfigInferer doesn't panic for any protocol
        let protocols = vec![
            ("TwoPhase", "types.rs", "twophase.rs"),
            ("Paxos", "types.rs", "paxos.rs"),
            ("LeaderElection", "types.rs", "election.rs"),
            ("Raft", "types.rs", "raft.rs"),
            ("ChainReplication", "types.rs", "chain.rs"),
            ("PrimaryBackup", "types.rs", "primarybackup.rs"),
            ("PBFT", "types.rs", "pbft.rs"),
            ("VerticalPaxos", "types.rs", "vpaxos.rs"),
            ("EPaxos", "types.rs", "epaxos.rs"),
        ];

        let naming = default_naming();
        for (name, types_file, proto_file) in &protocols {
            let types_path =
                std::path::PathBuf::from(format!("../src/protocol/{}/{}", name, types_file));
            let proto_path =
                std::path::PathBuf::from(format!("../src/protocol/{}/{}", name, proto_file));

            if !types_path.exists() || !proto_path.exists() {
                continue;
            }

            let schema = analyze_spec_files(&[types_path.as_path(), proto_path.as_path()]).unwrap();
            let inferer = ConfigInferer::new(&schema, &naming);
            let config = inferer.infer();

            // Every protocol should have LState→CState mapping
            assert!(
                config.remapping.contains_key("LState"),
                "{}: missing LState remapping",
                name
            );
            assert_eq!(
                config.remapping.get("LState").unwrap(),
                "CState",
                "{}: wrong LState remapping",
                name
            );

            // Every protocol should have LConstants→CConstants mapping
            assert!(
                config.remapping.contains_key("LConstants"),
                "{}: missing LConstants remapping",
                name
            );
        }
    }

    #[test]
    fn test_is_primitive_inner_type() {
        let mut schema = SpecSchema::new();
        // Add a type alias that resolves to a primitive
        schema.aliases.insert(
            "OperationNumber".to_string(),
            TypeAlias {
                name: "OperationNumber".to_string(),
                generics: Generics::default(),
                ty: Type::Int,
            },
        );

        let naming = default_naming();
        let inferer = ConfigInferer::new(&schema, &naming);

        assert!(inferer.is_primitive_inner_type(&Type::Int));
        assert!(inferer.is_primitive_inner_type(&Type::Nat));
        assert!(inferer.is_primitive_inner_type(&Type::Bool));
        assert!(inferer.is_primitive_inner_type(&Type::Named(AstPath::single("u64".to_string()))));
        assert!(inferer
            .is_primitive_inner_type(&Type::Named(AstPath::single("OperationNumber".to_string()))));
        assert!(
            !inferer.is_primitive_inner_type(&Type::Named(AstPath::single("LBallot".to_string())))
        );
    }

    // --- Arrow variants tests ---

    #[test]
    fn test_infer_arrow_variants_basic() {
        let source = r#"
verus! {
    pub enum LMessage {
        Msg1a { bal_1a: int },
        Msg2a { bal_2a: int, val_2a: int },
    }
}
        "#;
        let mut parser = TypeParser::new(source);
        let types = parser.parse_types().unwrap();
        let registry = build_registry(types);
        let schema = SpecSchema::from_registry(registry);
        let naming = default_naming();
        let inferer = ConfigInferer::new(&schema, &naming);
        let config = inferer.infer();

        // bal_1a → CMessage::Msg1a (enum gets L→C prefix; variant has no L prefix → identity)
        assert_eq!(
            config.arrow_variants.get("bal_1a").unwrap(),
            "CMessage::Msg1a"
        );
        // bal_2a and val_2a both → CMessage::Msg2a
        assert_eq!(
            config.arrow_variants.get("bal_2a").unwrap(),
            "CMessage::Msg2a"
        );
        assert_eq!(
            config.arrow_variants.get("val_2a").unwrap(),
            "CMessage::Msg2a"
        );
    }

    #[test]
    fn test_infer_arrow_variants_with_remapping() {
        // When remapping provides custom variant names, arrow_variants should use them
        let source = r#"
verus! {
    pub enum LMessage {
        Prepare { ballot: int },
        Promise { ballot: int, accepted_val: int },
    }
}
        "#;
        let mut parser = TypeParser::new(source);
        let types = parser.parse_types().unwrap();
        let registry = build_registry(types);
        let schema = SpecSchema::from_registry(registry);
        let naming = default_naming();
        let inferer = ConfigInferer::new(&schema, &naming);
        let config = inferer.infer();

        // Variant "Prepare" has identity remapping (from infer_remapping)
        // so exec variant name = "Prepare", not "CPrepare"
        assert_eq!(
            config.arrow_variants.get("ballot").unwrap(),
            "CMessage::Prepare"
        );
        assert_eq!(
            config.arrow_variants.get("accepted_val").unwrap(),
            "CMessage::Promise"
        );
    }

    #[test]
    fn test_infer_arrow_variants_skips_unit_variants() {
        let source = r#"
verus! {
    pub enum LTMState {
        Init,
        Committed,
        Aborted,
    }
}
        "#;
        let mut parser = TypeParser::new(source);
        let types = parser.parse_types().unwrap();
        let registry = build_registry(types);
        let schema = SpecSchema::from_registry(registry);
        let naming = default_naming();
        let inferer = ConfigInferer::new(&schema, &naming);
        let config = inferer.infer();

        // Unit variants have no fields → no arrow_variants entries
        assert!(config.arrow_variants.is_empty());
    }

    #[test]
    fn test_infer_arrow_variants_first_occurrence_wins() {
        // If same field name in multiple variants, first wins
        let source = r#"
verus! {
    pub enum LMessage {
        MsgA { value: int, extra: int },
        MsgB { value: int },
    }
}
        "#;
        let mut parser = TypeParser::new(source);
        let types = parser.parse_types().unwrap();
        let registry = build_registry(types);
        let schema = SpecSchema::from_registry(registry);
        let naming = default_naming();
        let inferer = ConfigInferer::new(&schema, &naming);
        let config = inferer.infer();

        // "value" appears in both MsgA and MsgB — first occurrence wins
        // (HashMap iteration order is non-deterministic, but we just check it's mapped)
        assert!(config.arrow_variants.contains_key("value"));
        assert!(config.arrow_variants.contains_key("extra"));
    }

    #[test]
    fn test_infer_arrow_variants_merge() {
        let mut base = TranspilerConfig::default();
        base.arrow_variants.insert(
            "bal_1a".to_string(),
            "CustomEnum::CustomVariant".to_string(),
        );

        let mut inferred = TranspilerConfig::default();
        inferred
            .arrow_variants
            .insert("bal_1a".to_string(), "CMessage::CMsg1a".to_string());
        inferred
            .arrow_variants
            .insert("bal_2a".to_string(), "CMessage::CMsg2a".to_string());

        merge_configs(&mut base, &inferred);

        // Explicit override wins for bal_1a
        assert_eq!(
            base.arrow_variants.get("bal_1a").unwrap(),
            "CustomEnum::CustomVariant"
        );
        // Inferred entry added for bal_2a
        assert_eq!(
            base.arrow_variants.get("bal_2a").unwrap(),
            "CMessage::CMsg2a"
        );
    }

    // --- Struct vec fields tests ---

    #[test]
    fn test_infer_struct_vec_fields_basic() {
        let source = r#"
verus! {
    pub struct LLogEntry {
        pub term: int,
        pub value: int,
    }

    pub struct LState {
        pub log: Seq<LLogEntry>,
        pub history: Seq<int>,
    }
}
        "#;
        let mut parser = TypeParser::new(source);
        let types = parser.parse_types().unwrap();
        let registry = build_registry(types);
        let schema = SpecSchema::from_registry(registry);
        let naming = default_naming();
        let inferer = ConfigInferer::new(&schema, &naming);
        let config = inferer.infer();

        // Seq<LLogEntry> → struct_vec_fields: "log" = ["CLogEntry", "LLogEntry"]
        assert!(config.struct_vec_fields.contains_key("log"));
        let log_entry = config.struct_vec_fields.get("log").unwrap();
        assert_eq!(log_entry[0], "CLogEntry"); // exec type
        assert_eq!(log_entry[1], "LLogEntry"); // spec type

        // Seq<int> → vec_fields, NOT struct_vec_fields
        assert!(!config.struct_vec_fields.contains_key("history"));
        assert!(config.vec_fields.contains(&"history".to_string()));
    }

    #[test]
    fn test_infer_struct_vec_fields_skips_enum() {
        let source = r#"
verus! {
    pub enum LPhase {
        Idle,
        Active,
    }

    pub struct LState {
        pub phases: Seq<LPhase>,
    }
}
        "#;
        let mut parser = TypeParser::new(source);
        let types = parser.parse_types().unwrap();
        let registry = build_registry(types);
        let schema = SpecSchema::from_registry(registry);
        let naming = default_naming();
        let inferer = ConfigInferer::new(&schema, &naming);
        let config = inferer.infer();

        // Seq<LPhase> where LPhase is an enum → NOT struct_vec_fields
        assert!(!config.struct_vec_fields.contains_key("phases"));
    }

    #[test]
    fn test_infer_struct_vec_fields_raft() {
        let types_path = std::path::Path::new("../src/protocol/Raft/types.rs");
        let proto_path = std::path::Path::new("../src/protocol/Raft/raft.rs");
        if !types_path.exists() || !proto_path.exists() {
            return;
        }
        let schema = analyze_spec_files(&[types_path, proto_path]).unwrap();
        let naming = default_naming();
        let inferer = ConfigInferer::new(&schema, &naming);
        let config = inferer.infer();

        // Raft has log: Seq<LLogEntry> → struct_vec_fields
        assert!(
            config.struct_vec_fields.contains_key("log"),
            "Raft should have 'log' in struct_vec_fields"
        );
        let log_entry = config.struct_vec_fields.get("log").unwrap();
        assert_eq!(log_entry[0], "CLogEntry");
        assert_eq!(log_entry[1], "LLogEntry");
    }

    #[test]
    fn test_infer_struct_vec_fields_merge() {
        let mut base = TranspilerConfig::default();
        base.struct_vec_fields.insert(
            "log".to_string(),
            vec!["CustomEntry".to_string(), "LEntry".to_string()],
        );

        let mut inferred = TranspilerConfig::default();
        inferred.struct_vec_fields.insert(
            "log".to_string(),
            vec!["CLogEntry".to_string(), "LLogEntry".to_string()],
        );
        inferred.struct_vec_fields.insert(
            "items".to_string(),
            vec!["CItem".to_string(), "LItem".to_string()],
        );

        merge_configs(&mut base, &inferred);

        // Explicit override wins for log
        assert_eq!(base.struct_vec_fields.get("log").unwrap()[0], "CustomEntry");
        // Inferred entry added for items
        assert_eq!(base.struct_vec_fields.get("items").unwrap()[0], "CItem");
    }

    // ==================== Phase 20.2.6: Migration validation tests ====================

    /// Helper: load a TOML config from a path
    fn load_file_config(path: &std::path::Path) -> TranspilerConfig {
        TranspilerConfig::from_file(path).unwrap_or_else(|e| {
            panic!("Failed to load {}: {}", path.display(), e);
        })
    }

    /// Validate that auto-inferred remapping covers the existing TOML's remapping.
    /// Returns (covered, missing) where missing are TOML entries not auto-derived.
    fn check_remapping_coverage(
        inferred: &TranspilerConfig,
        toml: &TranspilerConfig,
    ) -> (usize, Vec<String>) {
        let mut covered = 0;
        let mut missing = Vec::new();
        for (k, v) in &toml.remapping {
            if let Some(iv) = inferred.remapping.get(k) {
                if iv == v {
                    covered += 1;
                } else {
                    missing.push(format!("{}: inferred={}, toml={}", k, iv, v));
                }
            } else {
                missing.push(format!("{}: not inferred", k));
            }
        }
        (covered, missing)
    }

    /// Validate that auto-inferred collection_fields covers the TOML's.
    fn check_vec_coverage(inferred: &[String], toml: &[String]) -> (usize, Vec<String>) {
        let mut covered = 0;
        let mut missing = Vec::new();
        for f in toml {
            if inferred.contains(f) {
                covered += 1;
            } else {
                missing.push(f.clone());
            }
        }
        (covered, missing)
    }

    #[test]
    fn test_auto_inference_produces_valid_config_for_all_protocols() {
        // Validate that auto-inference produces non-empty, correct results
        // for all non-RSL protocols (Phase 21: TOMLs no longer contain Tier 1 fields)
        let protocols: Vec<(&str, &str, &str, &str)> = vec![
            (
                "TwoPhase",
                "types.rs",
                "twophase.rs",
                "twophase_transpile.toml",
            ),
            ("Paxos", "types.rs", "paxos.rs", "paxos_transpile.toml"),
            (
                "LeaderElection",
                "types.rs",
                "election.rs",
                "election_transpile.toml",
            ),
            ("Raft", "types.rs", "raft.rs", "raft_transpile.toml"),
            (
                "ChainReplication",
                "types.rs",
                "chain.rs",
                "chain_transpile.toml",
            ),
            (
                "PrimaryBackup",
                "types.rs",
                "primarybackup.rs",
                "primarybackup_transpile.toml",
            ),
            ("PBFT", "types.rs", "pbft.rs", "pbft_transpile.toml"),
            (
                "VerticalPaxos",
                "types.rs",
                "vpaxos.rs",
                "vpaxos_transpile.toml",
            ),
            ("EPaxos", "types.rs", "epaxos.rs", "epaxos_transpile.toml"),
        ];

        // Protocols known to have HashSet fields (need clone_strategy = "external_body")
        let needs_clone_strategy: Vec<&str> = vec![
            "TwoPhase",
            "Paxos",
            "LeaderElection",
            "Raft",
            "ChainReplication",
            "PBFT",
            "VerticalPaxos",
            "EPaxos",
        ];

        let mut checked = 0;
        for (name, types_file, proto_file, toml_file) in &protocols {
            let base = format!("../src/protocol/{}", name);
            let types_path = std::path::PathBuf::from(format!("{}/{}", base, types_file));
            let proto_path = std::path::PathBuf::from(format!("{}/{}", base, proto_file));
            let toml_path = std::path::PathBuf::from(format!("{}/{}", base, toml_file));

            if !types_path.exists() || !proto_path.exists() || !toml_path.exists() {
                continue;
            }

            let toml_config = load_file_config(&toml_path);
            let naming = &toml_config.naming;

            let schema = analyze_spec_files(&[types_path.as_path(), proto_path.as_path()]).unwrap();
            let inferer = ConfigInferer::new(&schema, naming);
            let inferred = inferer.infer();

            // Every protocol should have remappings inferred
            assert!(
                !inferred.remapping.is_empty(),
                "[{}] Auto-inference produced no remappings",
                name
            );

            // Protocols with HashSet fields should get clone_strategy
            if needs_clone_strategy.contains(name) {
                assert!(
                    !inferred.clone_strategy.is_empty(),
                    "[{}] Should have clone_strategy but auto-inference produced none",
                    name
                );
                // All inferred clone strategies should be "verified" or "external_body"
                for (k, v) in &inferred.clone_strategy {
                    assert!(
                        v == "verified" || v == "external_body",
                        "[{}] clone_strategy for {} should be verified or external_body, got {}",
                        name, k, v
                    );
                }
            }

            checked += 1;
        }

        assert!(
            checked >= 9,
            "Should have checked all 9 protocols, only checked {}",
            checked
        );
    }

    #[test]
    fn test_merge_produces_same_output_as_explicit_toml() {
        // Test that merge_configs(toml_overrides, inferred) preserves all TOML entries
        let protocols: Vec<(&str, &str, &str, &str)> = vec![
            (
                "TwoPhase",
                "types.rs",
                "twophase.rs",
                "twophase_transpile.toml",
            ),
            ("Paxos", "types.rs", "paxos.rs", "paxos_transpile.toml"),
            ("Raft", "types.rs", "raft.rs", "raft_transpile.toml"),
        ];

        for (name, types_file, proto_file, toml_file) in &protocols {
            let base = format!("../src/protocol/{}", name);
            let types_path = std::path::PathBuf::from(format!("{}/{}", base, types_file));
            let proto_path = std::path::PathBuf::from(format!("{}/{}", base, proto_file));
            let toml_path = std::path::PathBuf::from(format!("{}/{}", base, toml_file));

            if !types_path.exists() || !proto_path.exists() || !toml_path.exists() {
                continue;
            }

            // Load existing TOML
            let toml_config = load_file_config(&toml_path);

            // Analyze spec files
            let schema = analyze_spec_files(&[types_path.as_path(), proto_path.as_path()]).unwrap();
            let inferer = ConfigInferer::new(&schema, &toml_config.naming);
            let inferred = inferer.infer();

            // Merge: TOML overrides should be preserved
            let mut merged = toml_config.clone();
            merge_configs(&mut merged, &inferred);

            // All original TOML entries should still be present in merged config
            for (k, v) in &toml_config.remapping {
                assert_eq!(
                    merged.remapping.get(k).unwrap(),
                    v,
                    "[{}] TOML remapping for {} was overwritten by merge",
                    name,
                    k
                );
            }

            for f in &toml_config.collection_fields {
                assert!(
                    merged.collection_fields.contains(f),
                    "[{}] TOML collection_field {} was lost in merge",
                    name,
                    f
                );
            }

            for f in &toml_config.vec_fields {
                assert!(
                    merged.vec_fields.contains(f),
                    "[{}] TOML vec_field {} was lost in merge",
                    name,
                    f
                );
            }

            for (k, v) in &toml_config.clone_strategy {
                assert_eq!(
                    merged.clone_strategy.get(k).unwrap(),
                    v,
                    "[{}] TOML clone_strategy for {} was overwritten",
                    name,
                    k
                );
            }

            // Merged should have MORE or EQUAL entries than original TOML
            assert!(
                merged.remapping.len() >= toml_config.remapping.len(),
                "[{}] Merged remapping shrunk: {} < {}",
                name,
                merged.remapping.len(),
                toml_config.remapping.len()
            );
        }
    }
}
