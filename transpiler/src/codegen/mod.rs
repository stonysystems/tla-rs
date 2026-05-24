//! Code generation for exec types and implementations.
//!
//! This module generates:
//! - Concrete (exec) type definitions from spec types
//! - `well_formed()` validity predicates
//! - `View` trait implementations
//! - Clone implementations
//! - Executable code from quantifier templates

pub mod host_test;
pub mod marshalable;
pub mod messages;
pub mod scheduler;
pub mod template_codegen;

pub use host_test::{generate_host_init_test_program, HostTestParams};
pub use marshalable::generate_marshalable_impls;
pub use messages::generate_message_code;
pub use scheduler::{
    classify_actions, extract_lnext_actions, find_and_analyze_lnext, generate_host_scaffold,
    scheduler_config_to_toml, ActionClassificationOverrides, ActionKind, HostScaffoldParams,
    SchedulerAction, SchedulerConfig,
};
pub use template_codegen::TemplateCodeGenerator;

use std::collections::{HashMap, HashSet};

use crate::ast::Type;
use crate::config::NamingConfig;
use crate::types::{EnumDef, FieldDef, StructDef, TypeRegistry, VariantDef, VariantFields};

/// Generated code output
#[derive(Debug, Clone)]
pub struct GeneratedCode {
    /// The generated Rust code as a string
    pub code: String,
    /// Any warnings generated during code generation
    pub warnings: Vec<String>,
}

/// Type generator for producing exec types from spec types
pub struct TypeGenerator {
    /// Naming configuration
    config: NamingConfig,
    /// Type remapping table (spec name -> exec name)
    remapping: HashMap<String, String>,
    /// Indentation string
    indent: String,
    /// Name of the validity predicate (e.g., "well_formed" or "valid")
    validity_predicate_name: String,
    /// Types to treat as primitive (no valid() predicate needed)
    primitive_types: Vec<String>,
    /// Per-field custom View expressions (key: "SpecType.field_name")
    view_overrides: HashMap<String, String>,
    /// Extra fields for exec types (key: "ExecType.field_name", value: "type = default")
    extra_fields: HashMap<String, String>,
    /// Clone strategy per exec type ("derive", "external_body", or "verified")
    clone_strategy: HashMap<String, String>,
    /// Custom derives per exec type (additional derives beyond Clone)
    custom_derives: HashMap<String, Vec<String>>,
    /// Fields to skip per exec type during generation
    skip_fields: HashMap<String, Vec<String>>,
    /// Exec type names that should NOT get auto-generated validity predicates.
    skip_validity_types: HashSet<String>,
    /// Exec type names that should NOT get auto-generated View trait impls.
    skip_view_types: HashSet<String>,
    /// Generate clone_up_to_view for primitive-only generated structs.
    generate_clone_up_to_view_simple: bool,
    /// Exec type names that are stored inside HashSet<T> and need Hash+Eq impls.
    /// These get `#[verifier(external_body)]` Hash/PartialEq/Eq impls since
    /// Verus doesn't verify these trait implementations.
    hashset_element_types: HashSet<String>,
    /// Exec enum names that are unit enums (all variants have no fields).
    /// These get `Copy` in addition to `Clone` and are treated as copy-scalar
    /// in verified clone generation.
    unit_enums: HashSet<String>,
    /// Exec type names whose non-scalar fields should be wrapped in `Arc<T>`.
    arc_wrap_types: HashSet<String>,
    /// Fine-grained: specific fields per exec type to Arc-wrap (overrides arc_wrap_types).
    arc_wrap_fields: HashMap<String, Vec<String>>,
}

impl TypeGenerator {
    /// Create a new type generator with default settings.
    ///
    /// Use the builder methods (`with_remapping`, `with_validity_predicate_name`,
    /// `with_primitive_types`) to customize before generating code.
    pub fn new(config: NamingConfig) -> Self {
        Self {
            config,
            remapping: HashMap::new(),
            indent: "    ".to_string(),
            validity_predicate_name: "well_formed".to_string(),
            primitive_types: Vec::new(),
            view_overrides: HashMap::new(),
            extra_fields: HashMap::new(),
            clone_strategy: HashMap::new(),
            custom_derives: HashMap::new(),
            skip_fields: HashMap::new(),
            skip_validity_types: HashSet::new(),
            skip_view_types: HashSet::new(),
            generate_clone_up_to_view_simple: false,
            hashset_element_types: HashSet::new(),
            unit_enums: HashSet::new(),
            arc_wrap_types: HashSet::new(),
            arc_wrap_fields: HashMap::new(),
        }
    }

    /// Set the type remapping table (spec name -> exec name).
    pub fn with_remapping(mut self, remapping: HashMap<String, String>) -> Self {
        self.remapping = remapping;
        self
    }

    /// Set the validity predicate name (default: "well_formed").
    pub fn with_validity_predicate_name(mut self, name: String) -> Self {
        self.validity_predicate_name = name;
        self
    }

    /// Set the list of primitive types (no valid() predicate needed).
    pub fn with_primitive_types(mut self, types: Vec<String>) -> Self {
        self.primitive_types = types;
        self
    }

    /// Set view overrides for custom per-field View expressions
    pub fn set_view_overrides(&mut self, overrides: HashMap<String, String>) {
        self.view_overrides = overrides;
    }

    /// Set extra fields for exec types not present in spec
    pub fn set_extra_fields(&mut self, fields: HashMap<String, String>) {
        self.extra_fields = fields;
    }

    /// Set clone strategy per exec type
    pub fn set_clone_strategy(&mut self, strategy: HashMap<String, String>) {
        self.clone_strategy = strategy;
    }

    /// Set custom derives per exec type
    pub fn set_custom_derives(&mut self, derives: HashMap<String, Vec<String>>) {
        self.custom_derives = derives;
    }

    /// Set fields to skip per exec type
    pub fn set_skip_fields(&mut self, fields: HashMap<String, Vec<String>>) {
        self.skip_fields = fields;
    }

    /// Set exec types whose validity predicates should be supplied manually.
    pub fn set_skip_validity_types(&mut self, types: HashSet<String>) {
        self.skip_validity_types = types;
    }

    /// Set exec types whose View impls should be supplied manually.
    pub fn set_skip_view_types(&mut self, types: HashSet<String>) {
        self.skip_view_types = types;
    }

    /// Enable generation of clone_up_to_view methods for primitive-only structs.
    pub fn set_generate_clone_up_to_view_simple(&mut self, enabled: bool) {
        self.generate_clone_up_to_view_simple = enabled;
    }

    /// Set types that are stored inside HashSet<T> and need Hash+Eq impls
    pub fn set_hashset_element_types(&mut self, types: HashSet<String>) {
        self.hashset_element_types = types;
    }

    pub fn set_unit_enums(&mut self, enums: HashSet<String>) {
        self.unit_enums = enums;
    }

    /// Set exec type names whose non-scalar fields should be wrapped in Arc<T>.
    pub fn set_arc_wrap_types(&mut self, types: HashSet<String>) {
        self.arc_wrap_types = types;
    }

    pub fn set_arc_wrap_fields(&mut self, fields: HashMap<String, Vec<String>>) {
        self.arc_wrap_fields = fields;
    }

    /// Check if a field should be Arc-wrapped in the given struct.
    /// When arc_wrap_fields is specified for a struct, only those listed fields are wrapped.
    /// Otherwise falls back to arc_wrap_types which wraps all non-scalar fields.
    fn should_arc_wrap_field(&self, exec_name: &str, field_ty: &Type) -> bool {
        if !self.arc_wrap_types.contains(exec_name) {
            return false;
        }
        !self.is_copy_scalar_type_for_clone_up_to_view(field_ty)
    }

    /// Check if a specific named field should be Arc-wrapped.
    fn should_arc_wrap_named_field(&self, exec_name: &str, field_name: &str, field_ty: &Type) -> bool {
        if !self.arc_wrap_types.contains(exec_name) {
            return false;
        }
        // If fine-grained field list exists, use it
        if let Some(fields) = self.arc_wrap_fields.get(exec_name) {
            return fields.iter().any(|f| f == field_name);
        }
        // Fallback: wrap all non-scalar fields
        !self.is_copy_scalar_type_for_clone_up_to_view(field_ty)
    }

    /// Generate `#[derive(...)]` attribute and determine clone strategy for a type.
    ///
    /// Returns the clone strategy string ("derive" or "external_body") and appends
    /// any `#[derive(...)]` attribute to `code`.
    fn generate_derives(&self, exec_name: &str, code: &mut String) -> String {
        let clone_strat = self
            .clone_strategy
            .get(exec_name)
            .map(|s| s.as_str())
            .unwrap_or("derive");

        let mut derives = Vec::new();
        if clone_strat == "derive" {
            derives.push("Clone".to_string());
        }
        // Unit enums (all unit variants) get Copy for verified clone support
        if self.unit_enums.contains(exec_name) && !derives.contains(&"Copy".to_string()) {
            derives.push("Copy".to_string());
        }
        if let Some(custom) = self.custom_derives.get(exec_name) {
            for d in custom {
                if !derives.contains(d) {
                    derives.push(d.clone());
                }
            }
        }
        if !derives.is_empty() {
            code.push_str(&format!("#[derive({})]\n", derives.join(", ")));
        }

        clone_strat.to_string()
    }

    /// Like `generate_derives` but never emits `Clone` in the derive list.
    /// Used for Arc-wrapped types that need a manual external_body Clone impl.
    fn generate_derives_without_clone(&self, exec_name: &str, code: &mut String) {
        let mut derives = Vec::new();
        if self.unit_enums.contains(exec_name) {
            derives.push("Copy".to_string());
        }
        if let Some(custom) = self.custom_derives.get(exec_name) {
            for d in custom {
                if d != "Clone" && !derives.contains(d) {
                    derives.push(d.clone());
                }
            }
        }
        if !derives.is_empty() {
            code.push_str(&format!("#[derive({})]\n", derives.join(", ")));
        }
    }

    /// Generate `#[verifier(external_body)]` Clone impl for types that can't use `#[derive(Clone)]`.
    /// When field information is available, generates a real field-by-field clone body
    /// (copy scalars directly, `.clone()` for non-copy fields).
    fn generate_external_body_clone(
        &self,
        exec_name: &str,
        fields: &[&FieldDef],
        code: &mut String,
    ) {
        code.push_str(&format!("impl Clone for {} {{\n", exec_name));
        code.push_str(&format!(
            "{}#[verifier(external_body)]\n{}fn clone(&self) -> (res: Self)\n{}ensures\n{}    res@ == self@,\n{}    res.{}() == self.{}(),\n",
            self.indent, self.indent, self.indent,
            self.indent, self.indent,
            self.validity_predicate_name, self.validity_predicate_name,
        ));
        // Add concrete field-level ensures for fields whose types support spec equality.
        // This lets Verus track field values through `..base.clone()` in struct updates,
        // since external_body clone is opaque and view equality alone doesn't imply
        // concrete field equality (e.g., enum discriminants, u64 values, bools).
        // We include all fields except container types (Vec, HashSet, HashMap, Set, Seq, Map)
        // since Verus can compare those only through views.
        for field in fields {
            if Self::is_spec_equality_comparable(&field.ty) {
                code.push_str(&format!(
                    "{}    res.{} == self.{},\n",
                    self.indent, field.name, field.name,
                ));
            }
        }
        if fields.is_empty() {
            code.push_str(&format!("{}{{ unimplemented!() }}\n", self.indent));
        } else {
            code.push_str(&format!("{}{{\n", self.indent));
            code.push_str(&format!("{}    {} {{\n", self.indent, exec_name));
            for field in fields {
                if self.is_copy_scalar_type_for_clone_up_to_view(&field.ty) {
                    code.push_str(&format!(
                        "{}        {}: self.{},\n",
                        self.indent, field.name, field.name
                    ));
                } else {
                    code.push_str(&format!(
                        "{}        {}: self.{}.clone(),\n",
                        self.indent, field.name, field.name
                    ));
                }
            }
            code.push_str(&format!("{}    }}\n", self.indent));
            code.push_str(&format!("{}}}\n", self.indent));
        }
        code.push_str("}\n\n");
    }

    /// Check if a type is HashSet<u64> (Set<Int> or Set<Nat> in spec, becomes HashSet<u64>).
    fn is_hashset_u64(ty: &Type) -> bool {
        match ty {
            Type::Set(inner) => match inner.as_ref() {
                Type::Int | Type::Nat => true,
                Type::Named(p) => p
                    .last()
                    .is_some_and(|n| n == "u64" || n == "i64" || n == "usize"),
                _ => false,
            },
            _ => false,
        }
    }

    /// Generate verified Clone impl using `clone_hashset_u64` for HashSet<u64> fields.
    /// No `#[verifier(external_body)]` — all field clones are verified.
    fn generate_verified_clone(&self, exec_name: &str, fields: &[&FieldDef], code: &mut String) {
        code.push_str(&format!("impl Clone for {} {{\n", exec_name));
        code.push_str(&format!(
            "{}fn clone(&self) -> (res: Self)\n{}ensures\n{}    res@ == self@,\n{}    res.{}() == self.{}(),\n",
            self.indent, self.indent, self.indent,
            self.indent,
            self.validity_predicate_name, self.validity_predicate_name,
        ));
        for field in fields {
            if Self::is_spec_equality_comparable(&field.ty) {
                code.push_str(&format!(
                    "{}    res.{} == self.{},\n",
                    self.indent, field.name, field.name,
                ));
            }
        }
        code.push_str(&format!("{}{{\n", self.indent));
        code.push_str(&format!("{}    {} {{\n", self.indent, exec_name));
        for field in fields {
            if self.is_copy_scalar_type_for_clone_up_to_view(&field.ty) {
                code.push_str(&format!(
                    "{}        {}: self.{},\n",
                    self.indent, field.name, field.name
                ));
            } else if self.should_arc_wrap_named_field(exec_name, &field.name, &field.ty) {
                // Arc-wrapped field: Arc::clone is O(1) refcount bump
                code.push_str(&format!(
                    "{}        {}: self.{}.clone(),\n",
                    self.indent, field.name, field.name
                ));
            } else if Self::is_hashset_u64(&field.ty) {
                code.push_str(&format!(
                    "{}        {}: clone_hashset_u64(&self.{}),\n",
                    self.indent, field.name, field.name
                ));
            } else {
                code.push_str(&format!(
                    "{}        {}: self.{}.clone(),\n",
                    self.indent, field.name, field.name
                ));
            }
        }
        code.push_str(&format!("{}    }}\n", self.indent));
        code.push_str(&format!("{}}}\n", self.indent));
        code.push_str("}\n\n");
    }

    fn is_copy_scalar_type_for_clone_up_to_view(&self, ty: &Type) -> bool {
        match ty {
            Type::Bool | Type::Int | Type::Nat | Type::Unit => true,
            Type::Named(path) => {
                let name = path.last().unwrap_or("Unknown");
                if self.primitive_types.contains(&name.to_string()) {
                    return true;
                }
                if is_copy_scalar_primitive_type(name) {
                    return true;
                }
                // Unit enums are Copy — can be directly copied without .clone()
                let exec_name = self.get_exec_type(name);
                if self.unit_enums.contains(&exec_name) {
                    return true;
                }
                if let Some(remapped) = self.remapping.get(name) {
                    if self.primitive_types.contains(remapped) {
                        return true;
                    }
                    if self.unit_enums.contains(remapped) {
                        return true;
                    }
                    return is_copy_scalar_primitive_type(remapped);
                }
                false
            }
            Type::Reference { .. }
            | Type::Generic(_, _)
            | Type::Seq(_)
            | Type::Set(_)
            | Type::Map(_, _)
            | Type::Tuple(_) => false,
        }
    }

    /// Check if a type supports equality comparison in Verus spec mode for clone ensures.
    /// Returns true for primitives (u64, bool, etc.) and Named types (including enums).
    /// Returns false for container types (Vec, HashSet, HashMap, Seq, Set, Map) where
    /// spec equality would require element-level reasoning.
    fn is_spec_equality_comparable(ty: &Type) -> bool {
        match ty {
            Type::Bool | Type::Int | Type::Nat | Type::Unit => true,
            Type::Named(_) => true,
            Type::Reference { .. }
            | Type::Generic(_, _)
            | Type::Seq(_)
            | Type::Set(_)
            | Type::Map(_, _)
            | Type::Tuple(_) => false,
        }
    }

    fn generate_clone_up_to_view_simple_method(
        &self,
        exec_name: &str,
        fields: &[&FieldDef],
    ) -> Option<String> {
        if !self.generate_clone_up_to_view_simple {
            return None;
        }
        if fields.is_empty() {
            return None;
        }
        if !fields
            .iter()
            .all(|field| self.is_copy_scalar_type_for_clone_up_to_view(&field.ty))
        {
            return None;
        }

        let mut code = format!("impl {} {{\n", exec_name);
        code.push_str(&format!(
            "{}pub fn clone_up_to_view(&self) -> (result: Self)\n",
            self.indent
        ));
        code.push_str(&format!(
            "{}ensures\n{}    result@ == self@,\n",
            self.indent, self.indent
        ));
        code.push_str(&format!("{}{{\n", self.indent));
        code.push_str(&format!("{}    {} {{\n", self.indent, exec_name));
        for field in fields {
            code.push_str(&format!(
                "{}        {}: self.{},\n",
                self.indent, field.name, field.name
            ));
        }
        code.push_str(&format!("{}    }}\n", self.indent));
        code.push_str(&format!("{}}}\n", self.indent));
        code.push_str("}\n\n");
        Some(code)
    }

    /// Generate an exec struct from a spec struct
    pub fn generate_struct(&self, spec: &StructDef) -> GeneratedCode {
        let mut code = String::new();
        let warnings = Vec::new();

        let exec_name = self.get_exec_type(&spec.name);
        let is_arc_wrapped = self.arc_wrap_types.contains(&exec_name);

        // Arc-wrapped types need external_body Clone (no Arc::clone spec in vstd),
        // so suppress #[derive(Clone)] by temporarily overriding the clone strategy.
        let clone_strat = if is_arc_wrapped {
            self.generate_derives_without_clone(&exec_name, &mut code);
            "external_body".to_string()
        } else {
            self.generate_derives(&exec_name, &mut code)
        };

        // Get skip fields for this type
        let skip_fields = self.skip_fields.get(&exec_name);
        let generated_fields: Vec<&FieldDef> = spec
            .fields
            .iter()
            .filter(|field| !skip_fields.is_some_and(|skips| skips.contains(&field.name)))
            .collect();

        // Generate struct definition
        code.push_str(&format!("pub struct {} {{\n", exec_name));
        for field in &generated_fields {
            let exec_type = self.translate_type(&field.ty);
            let vis = if field.is_public { "pub " } else { "" };
            if self.should_arc_wrap_named_field(&exec_name, &field.name, &field.ty) {
                code.push_str(&format!(
                    "{}{}{}: Arc<{}>,\n",
                    self.indent, vis, field.name, exec_type
                ));
            } else {
                code.push_str(&format!(
                    "{}{}{}: {},\n",
                    self.indent, vis, field.name, exec_type
                ));
            }
        }
        // Add extra fields not in spec
        for (key, value) in &self.extra_fields {
            if let Some(field_name) = key.strip_prefix(&format!("{}.", exec_name)) {
                // Parse "type = default" format — we only need the type for the struct definition
                let field_type = value.split('=').next().unwrap_or(value).trim();
                code.push_str(&format!(
                    "{}pub {}: {},\n",
                    self.indent, field_name, field_type
                ));
            }
        }
        code.push_str("}\n\n");

        if let Some(clone_up_to_view_impl) =
            self.generate_clone_up_to_view_simple_method(&exec_name, &generated_fields)
        {
            code.push_str(&clone_up_to_view_impl);
        }

        if clone_strat == "external_body" {
            self.generate_external_body_clone(&exec_name, &generated_fields, &mut code);
        } else if clone_strat == "verified" {
            self.generate_verified_clone(&exec_name, &generated_fields, &mut code);
        }

        // Generate Hash+PartialEq+Eq impls for types stored in HashSet
        if self.hashset_element_types.contains(&exec_name) {
            code.push_str(&format!("impl std::hash::Hash for {} {{\n", exec_name));
            code.push_str(&format!(
                "{}#[verifier(external_body)]\n{}fn hash<H: std::hash::Hasher>(&self, state: &mut H) {{ unimplemented!() }}\n",
                self.indent, self.indent
            ));
            code.push_str("}\n\n");

            code.push_str(&format!("impl PartialEq for {} {{\n", exec_name));
            code.push_str(&format!(
                "{}#[verifier(external_body)]\n{}fn eq(&self, other: &Self) -> bool {{ unimplemented!() }}\n",
                self.indent, self.indent
            ));
            code.push_str("}\n\n");

            code.push_str(&format!("impl Eq for {} {{}}\n\n", exec_name));
        }

        // Generate well_formed predicate unless this type is configured for manual validity impl.
        if !self.skip_validity_types.contains(&exec_name) {
            code.push_str(&self.generate_well_formed_struct(&exec_name, &spec.fields));
            code.push('\n');
        }

        // Generate View implementation unless this type is configured for manual View impl.
        if !self.skip_view_types.contains(&exec_name) {
            code.push_str(&self.generate_view_impl(&spec.name, &exec_name, &spec.fields));
        }

        GeneratedCode { code, warnings }
    }

    /// Generate an exec enum from a spec enum
    pub fn generate_enum(&self, spec: &EnumDef) -> GeneratedCode {
        let mut code = String::new();
        let warnings = Vec::new();

        let exec_name = self.get_exec_type(&spec.name);
        let clone_strat = self.generate_derives(&exec_name, &mut code);

        // Generate enum definition
        code.push_str(&format!("pub enum {} {{\n", exec_name));
        for variant in &spec.variants {
            code.push_str(&self.generate_variant(variant));
        }
        code.push_str("}\n\n");

        if clone_strat == "external_body" {
            self.generate_external_body_clone(&exec_name, &[], &mut code);
        } else if clone_strat == "verified" {
            self.generate_verified_clone(&exec_name, &[], &mut code);
        }

        // Generate well_formed predicate unless this type is configured for manual validity impl.
        if !self.skip_validity_types.contains(&exec_name) {
            code.push_str(&self.generate_well_formed_enum(&exec_name, &spec.variants));
            code.push('\n');
        }

        // Generate View implementation unless this type is configured for manual View impl.
        if !self.skip_view_types.contains(&exec_name) {
            code.push_str(&self.generate_view_impl_enum(&spec.name, &exec_name, &spec.variants));
        }

        GeneratedCode { code, warnings }
    }

    /// Generate a single enum variant (using exec variant name from remapping)
    fn generate_variant(&self, variant: &VariantDef) -> String {
        let exec_variant_name = self.get_exec_variant_name(&variant.name);
        match &variant.fields {
            VariantFields::Unit => format!("{}{},\n", self.indent, exec_variant_name),
            VariantFields::Tuple(types) => {
                let type_strs: Vec<_> = types.iter().map(|t| self.translate_type(t)).collect();
                format!(
                    "{}{}({}),\n",
                    self.indent,
                    exec_variant_name,
                    type_strs.join(", ")
                )
            }
            VariantFields::Struct(fields) => {
                let mut s = format!("{}{} {{\n", self.indent, exec_variant_name);
                for field in fields {
                    let exec_type = self.translate_type(&field.ty);
                    s.push_str(&format!(
                        "{}{}    {}: {},\n",
                        self.indent, "", field.name, exec_type
                    ));
                }
                s.push_str(&format!("{}}},\n", self.indent));
                s
            }
        }
    }

    /// Generate validity predicate for a struct
    fn generate_well_formed_struct(&self, exec_name: &str, fields: &[FieldDef]) -> String {
        let pred_name = &self.validity_predicate_name;
        let mut code = format!("impl {} {{\n", exec_name);
        code.push_str(&format!(
            "{}pub open spec fn {}(&self) -> bool {{\n",
            self.indent, pred_name
        ));

        // Get skip fields for this type
        let skip = self.skip_fields.get(exec_name);

        // Collect fields that need validity checks (excluding skipped fields)
        let fields_needing_check: Vec<_> = fields
            .iter()
            .filter(|f| {
                if let Some(skips) = skip {
                    if skips.contains(&f.name) {
                        return false;
                    }
                }
                self.needs_well_formed(&f.ty)
            })
            .collect();

        if fields_needing_check.is_empty() {
            // All fields are primitives, just return true
            code.push_str(&format!("{}{}true\n", self.indent, self.indent));
        } else {
            // Generate conjunction of validity calls
            for field in fields_needing_check.iter() {
                let prefix = "&&& ";
                code.push_str(&format!(
                    "{}{}{}self.{}.{}()\n",
                    self.indent, self.indent, prefix, field.name, pred_name
                ));
            }
        }

        code.push_str(&format!("{}}}\n", self.indent));
        code.push_str("}\n");
        code
    }

    /// Generate validity predicate for an enum
    fn generate_well_formed_enum(&self, exec_name: &str, variants: &[VariantDef]) -> String {
        let pred_name = &self.validity_predicate_name;
        let mut code = format!("impl {} {{\n", exec_name);
        code.push_str(&format!(
            "{}pub open spec fn {}(&self) -> bool {{\n",
            self.indent, pred_name
        ));
        code.push_str(&format!("{}{}match self {{\n", self.indent, self.indent));

        for variant in variants {
            code.push_str(&self.generate_well_formed_variant_arm(exec_name, variant));
        }

        code.push_str(&format!("{}{}}}\n", self.indent, self.indent));
        code.push_str(&format!("{}}}\n", self.indent));
        code.push_str("}\n");
        code
    }

    /// Generate a match arm for validity check
    fn generate_well_formed_variant_arm(&self, enum_name: &str, variant: &VariantDef) -> String {
        let arm_indent = format!("{}{}{}", self.indent, self.indent, self.indent);
        let pred_name = &self.validity_predicate_name;
        let exec_variant_name = self.get_exec_variant_name(&variant.name);

        match &variant.fields {
            VariantFields::Unit => {
                format!(
                    "{}{}::{} => true,\n",
                    arm_indent, enum_name, exec_variant_name
                )
            }
            VariantFields::Tuple(types) => {
                let patterns: Vec<_> = (0..types.len()).map(|i| format!("v{}", i)).collect();
                let pattern = patterns.join(", ");

                let mut checks = Vec::new();
                for (i, ty) in types.iter().enumerate() {
                    if self.needs_well_formed(ty) {
                        checks.push(format!("v{}.{}()", i, pred_name));
                    }
                }

                if checks.is_empty() {
                    format!(
                        "{}{}::{}({}) => true,\n",
                        arm_indent, enum_name, exec_variant_name, pattern
                    )
                } else {
                    format!(
                        "{}{}::{}({}) => {},\n",
                        arm_indent,
                        enum_name,
                        exec_variant_name,
                        pattern,
                        checks.join(" && ")
                    )
                }
            }
            VariantFields::Struct(fields) => {
                let patterns: Vec<_> = fields.iter().map(|f| f.name.clone()).collect();
                let pattern = patterns.join(", ");

                let mut checks = Vec::new();
                for field in fields {
                    if self.needs_well_formed(&field.ty) {
                        checks.push(format!("{}.{}()", field.name, pred_name));
                    }
                }

                if checks.is_empty() {
                    format!(
                        "{}{}::{} {{ {} }} => true,\n",
                        arm_indent, enum_name, exec_variant_name, pattern
                    )
                } else {
                    format!(
                        "{}{}::{} {{ {} }} => {},\n",
                        arm_indent,
                        enum_name,
                        exec_variant_name,
                        pattern,
                        checks.join(" && ")
                    )
                }
            }
        }
    }

    /// Generate View trait implementation for a struct
    fn generate_view_impl(&self, spec_name: &str, exec_name: &str, fields: &[FieldDef]) -> String {
        // Get skip fields for this type
        let skip = self.skip_fields.get(exec_name);

        let mut code = format!("impl View for {} {{\n", exec_name);
        code.push_str(&format!("{}type V = {};\n\n", self.indent, spec_name));
        code.push_str(&format!(
            "{}open spec fn view(&self) -> {} {{\n",
            self.indent, spec_name
        ));
        code.push_str(&format!("{}{}{} {{\n", self.indent, self.indent, spec_name));

        for field in fields {
            // Check view_overrides first (key: "SpecType.field_name")
            let override_key = format!("{}.{}", spec_name, field.name);
            let has_view_override = self.view_overrides.contains_key(&override_key);

            // Skip fields configured to be omitted, UNLESS they have a view_override.
            // A view_override on a skipped field means the spec type still has the field
            // and the View impl must provide a value (e.g., Set::empty() for a dropped field).
            if let Some(skips) = skip {
                if skips.contains(&field.name) && !has_view_override {
                    continue;
                }
            }

            let view_expr = if let Some(custom_expr) = self.view_overrides.get(&override_key) {
                custom_expr.clone()
            } else {
                self.generate_view_field_expr(&field.name, &field.ty, false)
            };
            code.push_str(&format!(
                "{}{}{}{}: {},\n",
                self.indent, self.indent, self.indent, field.name, view_expr
            ));
        }

        code.push_str(&format!("{}{}}}\n", self.indent, self.indent));
        code.push_str(&format!("{}}}\n", self.indent));
        code.push_str("}\n");
        code
    }

    /// Generate View trait implementation for an enum
    fn generate_view_impl_enum(
        &self,
        spec_name: &str,
        exec_name: &str,
        variants: &[VariantDef],
    ) -> String {
        let mut code = format!("impl View for {} {{\n", exec_name);
        code.push_str(&format!("{}type V = {};\n\n", self.indent, spec_name));
        code.push_str(&format!(
            "{}open spec fn view(&self) -> {} {{\n",
            self.indent, spec_name
        ));
        code.push_str(&format!("{}{}match self {{\n", self.indent, self.indent));

        for variant in variants {
            code.push_str(&self.generate_view_variant_arm(spec_name, exec_name, variant));
        }

        code.push_str(&format!("{}{}}}\n", self.indent, self.indent));
        code.push_str(&format!("{}}}\n", self.indent));
        code.push_str("}\n");
        code
    }

    /// Generate a match arm for View implementation.
    /// The exec side uses the remapped variant name, the spec side uses the original.
    fn generate_view_variant_arm(
        &self,
        spec_name: &str,
        exec_name: &str,
        variant: &VariantDef,
    ) -> String {
        let arm_indent = format!("{}{}{}", self.indent, self.indent, self.indent);
        let exec_variant_name = self.get_exec_variant_name(&variant.name);
        let spec_variant_name = &variant.name;

        match &variant.fields {
            VariantFields::Unit => {
                format!(
                    "{}{}::{} => {}::{},\n",
                    arm_indent, exec_name, exec_variant_name, spec_name, spec_variant_name
                )
            }
            VariantFields::Tuple(types) => {
                let patterns: Vec<_> = (0..types.len()).map(|i| format!("v{}", i)).collect();
                let pattern = patterns.join(", ");

                let mut views = Vec::new();
                for (i, ty) in types.iter().enumerate() {
                    let view_expr = self.generate_view_field_expr(&format!("v{}", i), ty, true);
                    views.push(view_expr);
                }

                format!(
                    "{}{}::{}({}) => {}::{}({}),\n",
                    arm_indent,
                    exec_name,
                    exec_variant_name,
                    pattern,
                    spec_name,
                    spec_variant_name,
                    views.join(", ")
                )
            }
            VariantFields::Struct(fields) => {
                let patterns: Vec<_> = fields.iter().map(|f| f.name.clone()).collect();
                let pattern = patterns.join(", ");

                let mut field_views = Vec::new();
                for field in fields {
                    let view_expr = self.generate_view_field_expr(&field.name, &field.ty, true);
                    field_views.push(format!("{}: {}", field.name, view_expr));
                }

                format!(
                    "{}{}::{} {{ {} }} => {}::{} {{ {} }},\n",
                    arm_indent,
                    exec_name,
                    exec_variant_name,
                    pattern,
                    spec_name,
                    spec_variant_name,
                    field_views.join(", ")
                )
            }
        }
    }

    /// Get exec type name, checking remapping table first
    fn get_exec_type(&self, name: &str) -> String {
        // First check explicit remapping
        if let Some(exec_type) = self.remapping.get(name) {
            return exec_type.clone();
        }
        // Fall back to naming convention
        self.config.get_exec_type(name)
    }

    /// Get the exec variant name, checking remapping table first.
    /// Unlike type names, variant names are NOT automatically prefixed with C.
    /// They only change if explicitly listed in the remapping table.
    fn get_exec_variant_name(&self, spec_variant_name: &str) -> String {
        if let Some(exec_name) = self.remapping.get(spec_variant_name) {
            return exec_name.clone();
        }
        spec_variant_name.to_string()
    }

    /// Get the exec name for a type alias (e.g., "RequestBatch" -> "CRequestBatch")
    pub fn get_exec_alias_name(&self, spec_name: &str) -> String {
        // Check remapping first (alias name itself might be remapped)
        if let Some(exec_name) = self.remapping.get(spec_name) {
            return exec_name.clone();
        }
        self.config.get_exec_type(spec_name)
    }

    /// Translate a type alias's target type to exec equivalent
    pub fn translate_alias_type(&self, ty: &Type) -> String {
        self.translate_type(ty)
    }

    /// Translate a spec type to its exec equivalent
    fn translate_type(&self, ty: &Type) -> String {
        match ty {
            Type::Named(path) => {
                let name = path.last().unwrap_or("Unknown");
                // Rust primitive types should pass through unchanged
                if is_rust_primitive_type(name) {
                    return name.to_string();
                }
                self.get_exec_type(name)
            }
            Type::Generic(path, args) => {
                let name = path.last().unwrap_or("Unknown");
                let exec_name = self.get_exec_type(name);
                let arg_strs: Vec<_> = args.iter().map(|a| self.translate_type(a)).collect();
                format!("{}<{}>", exec_name, arg_strs.join(", "))
            }
            Type::Seq(inner) => format!("Vec<{}>", self.translate_type(inner)),
            Type::Set(inner) => format!("HashSet<{}>", self.translate_type(inner)),
            Type::Map(k, v) => {
                format!(
                    "HashMap<{}, {}>",
                    self.translate_type(k),
                    self.translate_type(v)
                )
            }
            Type::Tuple(types) => {
                let type_strs: Vec<_> = types.iter().map(|t| self.translate_type(t)).collect();
                format!("({})", type_strs.join(", "))
            }
            Type::Reference { ty, mutable } => {
                if *mutable {
                    format!("&mut {}", self.translate_type(ty))
                } else {
                    format!("&{}", self.translate_type(ty))
                }
            }
            Type::Bool => "bool".to_string(),
            Type::Int => self.config.int_type.clone(),
            Type::Nat => self.config.nat_type.clone(),
            Type::Unit => "()".to_string(),
        }
    }

    /// Check if a type needs well_formed validation
    /// Takes remapping into account - if a type is remapped to a primitive (u64, bool, etc.)
    /// or stdlib type (Vec, HashMap, HashSet), it doesn't need valid() call.
    fn needs_well_formed(&self, ty: &Type) -> bool {
        self.needs_well_formed_with_remapping(ty)
    }

    /// Check if a type needs well_formed, considering type remapping and primitive_types list.
    /// Returns true if the type DOES need a valid() call, false if it should be skipped.
    fn needs_well_formed_with_remapping(&self, ty: &Type) -> bool {
        match ty {
            Type::Bool | Type::Int | Type::Nat | Type::Unit => false,
            Type::Named(path) => {
                let name = path.last().unwrap_or("Unknown");

                // First check if this type or its remapped name is in primitive_types list
                if self.primitive_types.contains(&name.to_string()) {
                    return false;
                }

                // Check if this type is remapped to a primitive or stdlib type
                if let Some(remapped) = self.remapping.get(name) {
                    // Check if remapped name is in primitive_types list
                    if self.primitive_types.contains(remapped) {
                        return false;
                    }
                    // If remapped to stdlib type, skip valid()
                    if is_primitive_or_stdlib_type(remapped) {
                        return false;
                    }
                    // Remapped to a custom type that needs valid()
                    return true;
                }

                // Not remapped - check if the type name itself is a primitive or stdlib type
                !is_primitive_or_stdlib_type(name)
            }
            Type::Generic(path, args) => {
                let name = path.last().unwrap_or("Unknown");

                // Check primitive_types list
                if self.primitive_types.contains(&name.to_string()) {
                    return false;
                }

                // Check if this type is remapped to a primitive or stdlib type
                if let Some(remapped) = self.remapping.get(name) {
                    if self.primitive_types.contains(remapped)
                        || is_primitive_or_stdlib_type(remapped)
                    {
                        return false;
                    }
                }

                // For generic types, also check the args
                args.iter()
                    .any(|arg| self.needs_well_formed_with_remapping(arg))
            }
            // Vec, HashMap, HashSet don't have valid() predicates by default
            // They contain elements that might need valid() but we can't call valid() on the container
            Type::Seq(_) | Type::Set(_) | Type::Map(_, _) => false,
            Type::Tuple(types) => types
                .iter()
                .any(|t| self.needs_well_formed_with_remapping(t)),
            Type::Reference { ty, .. } => self.needs_well_formed_with_remapping(ty),
        }
    }

    /// Check if a type needs the view operator (@)
    fn needs_view(&self, ty: &Type) -> bool {
        needs_view_check(ty)
    }

    /// Generate the View expression for a field or variant binding.
    ///
    /// For struct fields (`is_variant_binding = false`): uses `self.{name}` accessor.
    /// For enum variant bindings (`is_variant_binding = true`): uses bare `{name}` with
    /// `*` dereference for plain values.
    fn generate_view_field_expr(&self, name: &str, ty: &Type, is_variant_binding: bool) -> String {
        let accessor = if is_variant_binding {
            name.to_string()
        } else {
            format!("self.{}", name)
        };
        if let Some(map_expr) = self.collection_view_map_expr(ty, &accessor) {
            return map_expr;
        }
        if self.needs_view(ty) {
            format!("{}@", accessor)
        } else if needs_as_int_conversion(ty) {
            if is_variant_binding {
                format!("*{} as int", name)
            } else {
                format!("{} as int", accessor)
            }
        } else if is_variant_binding {
            format!("*{}", name)
        } else {
            accessor
        }
    }

    /// Generate a `.map()` expression for collection types whose inner elements need
    /// type conversion in the View impl. For example, `Set<int>` maps to `HashSet<u64>`
    /// in exec, so the View needs `self.field@.map(|x: u64| x as int)` to convert
    /// `Set<u64>` back to `Set<int>`.
    /// Returns None if no inner conversion is needed.
    fn collection_view_map_expr(&self, ty: &Type, accessor: &str) -> Option<String> {
        match ty {
            Type::Set(inner) if needs_as_int_conversion(inner) => {
                let exec_inner = self.translate_type(inner);
                Some(format!("{}@.map(|x: {}| x as int)", accessor, exec_inner))
            }
            Type::Seq(inner) if needs_as_int_conversion(inner) => {
                let exec_inner = self.translate_type(inner);
                Some(format!(
                    "{}@.map(|i: int, x: {}| x as int)",
                    accessor, exec_inner
                ))
            }
            // Seq<NamedType> where inner needs View: map each element with @
            Type::Seq(inner) if inner_needs_view_map(inner) => {
                let exec_inner = self.translate_type(inner);
                Some(format!("{}@.map(|i: int, x: {}| x@)", accessor, exec_inner))
            }
            // Set<NamedType> where inner needs View: map each element with @
            Type::Set(inner) if inner_needs_view_map(inner) => {
                let exec_inner = self.translate_type(inner);
                Some(format!("{}@.map(|x: {}| x@)", accessor, exec_inner))
            }
            _ => None,
        }
    }
}

/// Check if a type needs the view operator (@) (standalone function for recursion)
fn needs_view_check(ty: &Type) -> bool {
    match ty {
        Type::Bool | Type::Int | Type::Nat | Type::Unit => false,
        Type::Named(_) | Type::Generic(_, _) => true,
        Type::Seq(_) | Type::Set(_) | Type::Map(_, _) => true,
        Type::Tuple(types) => types.iter().any(needs_view_check),
        Type::Reference { ty, .. } => needs_view_check(ty),
    }
}

/// Check if a type needs `as int` conversion in View impl
/// This applies to Int and Nat types which are translated to i64/u64 in exec
fn needs_as_int_conversion(ty: &Type) -> bool {
    match ty {
        Type::Int | Type::Nat => true,
        Type::Reference { ty, .. } => needs_as_int_conversion(ty),
        _ => false,
    }
}

/// Check if a collection's inner type needs `.map(|x| x@)` in View impl.
/// Returns true for named spec types (e.g., LLogEntry) that have their own View trait.
/// Returns false for Rust primitives (u64, bool) and abstract types (int, nat).
fn inner_needs_view_map(ty: &Type) -> bool {
    match ty {
        Type::Named(path) => {
            let name = path.last().unwrap_or("Unknown");
            !is_rust_primitive_type(name)
        }
        Type::Generic(_, _) => true,
        _ => false,
    }
}

/// Check if a type name is a Rust primitive type that should not get spec→exec naming applied.
/// These types appear in spec files when the user already uses concrete types (e.g., `Map<u64, u64>`).
fn is_rust_primitive_type(name: &str) -> bool {
    matches!(
        name,
        "u8" | "u16"
            | "u32"
            | "u64"
            | "u128"
            | "usize"
            | "i8"
            | "i16"
            | "i32"
            | "i64"
            | "i128"
            | "isize"
            | "char"
            | "String"
    )
}

/// Check if a type name is a Copy scalar primitive in Rust.
/// Excludes non-Copy types such as `String`.
fn is_copy_scalar_primitive_type(name: &str) -> bool {
    matches!(
        name,
        "bool"
            | "u8"
            | "u16"
            | "u32"
            | "u64"
            | "u128"
            | "usize"
            | "i8"
            | "i16"
            | "i32"
            | "i64"
            | "i128"
            | "isize"
            | "char"
    )
}

/// Check if a type name represents a primitive or stdlib type that doesn't have valid()
fn is_primitive_or_stdlib_type(type_name: &str) -> bool {
    // Primitive types
    if matches!(
        type_name,
        "bool"
            | "u8"
            | "u16"
            | "u32"
            | "u64"
            | "u128"
            | "usize"
            | "i8"
            | "i16"
            | "i32"
            | "i64"
            | "i128"
            | "isize"
            | "int"
            | "nat"
            | "()"
            | "String"
            | "&str"
    ) {
        return true;
    }

    // Standard library collection types (don't have valid() method)
    if matches!(
        type_name,
        "Vec" | "HashMap" | "HashSet" | "BTreeMap" | "BTreeSet" | "VecDeque"
    ) {
        return true;
    }

    // Check for generic stdlib types like Vec<T>, HashMap<K, V>
    if type_name.starts_with("Vec<")
        || type_name.starts_with("HashMap<")
        || type_name.starts_with("HashSet<")
        || type_name.starts_with("BTreeMap<")
        || type_name.starts_with("BTreeSet<")
        || type_name.starts_with("VecDeque<")
    {
        return true;
    }

    false
}

impl NamingConfig {
    /// Get the exec type name for a spec type
    ///
    /// Only replaces prefix if followed by uppercase letter to avoid
    /// mangling names like "LearnerTuple" (should become "CLearnerTuple"
    /// not "CearnerTuple").
    pub fn get_exec_type(&self, spec_name: &str) -> String {
        if spec_name.starts_with(&self.spec_prefix) {
            let rest = &spec_name[self.spec_prefix.len()..];
            // Check if the character after the prefix is uppercase
            if rest.chars().next().is_some_and(|c| c.is_uppercase()) {
                return format!("{}{}", self.exec_prefix, rest);
            }
        }
        // Default: prepend exec prefix
        format!("{}{}", self.exec_prefix, spec_name)
    }
}

/// Generate all types from a type registry
pub fn generate_all_types(registry: &TypeRegistry, config: &NamingConfig) -> GeneratedCode {
    generate_all_types_with_remapping(registry, config, &HashMap::new())
}

/// Generate all types from a type registry with custom type remapping
pub fn generate_all_types_with_remapping(
    registry: &TypeRegistry,
    config: &NamingConfig,
    remapping: &HashMap<String, String>,
) -> GeneratedCode {
    generate_all_types_with_options(registry, config, remapping, &[], "well_formed")
}

/// Generate all types from a type registry with custom remapping and imports
pub fn generate_all_types_with_options(
    registry: &TypeRegistry,
    config: &NamingConfig,
    remapping: &HashMap<String, String>,
    custom_imports: &[String],
    validity_predicate_name: &str,
) -> GeneratedCode {
    generate_all_types_full(&TypeGenConfig {
        registry,
        naming: config,
        remapping,
        custom_imports,
        validity_predicate_name,
        view_overrides: &HashMap::new(),
        extra_fields: &HashMap::new(),
        clone_strategy: &HashMap::new(),
        skip_types: &[],
        re_exports: &[],
        extra_type_aliases: &HashMap::new(),
        custom_derives: &HashMap::new(),
        skip_fields: &HashMap::new(),
        skip_validity_types: &[],
        skip_view_types: &[],
        generate_clone_up_to_view_simple: false,
        generate_unreachable_value_helper: false,
        manual_code: None,
        arc_wrap_types: &[],
        arc_wrap_fields: &HashMap::new(),
    })
}

/// Full configuration for type generation
pub struct TypeGenConfig<'a> {
    pub registry: &'a TypeRegistry,
    pub naming: &'a NamingConfig,
    pub remapping: &'a HashMap<String, String>,
    pub custom_imports: &'a [String],
    pub validity_predicate_name: &'a str,
    pub view_overrides: &'a HashMap<String, String>,
    pub extra_fields: &'a HashMap<String, String>,
    pub clone_strategy: &'a HashMap<String, String>,
    pub skip_types: &'a [String],
    pub re_exports: &'a [String],
    pub extra_type_aliases: &'a HashMap<String, String>,
    pub custom_derives: &'a HashMap<String, Vec<String>>,
    pub skip_fields: &'a HashMap<String, Vec<String>>,
    pub skip_validity_types: &'a [String],
    pub skip_view_types: &'a [String],
    pub generate_clone_up_to_view_simple: bool,
    pub generate_unreachable_value_helper: bool,
    pub manual_code: Option<&'a str>,
    /// Exec type names whose non-scalar fields should be wrapped in Arc<T>.
    #[allow(dead_code)]
    pub arc_wrap_types: &'a [String],
    /// Fine-grained: specific fields per exec type to Arc-wrap.
    pub arc_wrap_fields: &'a HashMap<String, Vec<String>>,
}

fn generate_unreachable_value_helper() -> &'static str {
    r#"/// Helper for match arms that are provably unreachable.
/// The requires clause is `false`, so Verus verifies this can never be called.
#[verifier(external_body)]
pub fn unreachable_value<T>() -> (result: T)
    requires false,
{
    panic!("unreachable")
}
"#
}

/// Generate all types from a type registry with all configuration options
pub fn generate_all_types_full(cfg: &TypeGenConfig<'_>) -> GeneratedCode {
    let mut generator = TypeGenerator::new(cfg.naming.clone())
        .with_remapping(cfg.remapping.clone())
        .with_validity_predicate_name(cfg.validity_predicate_name.to_string());
    generator.set_view_overrides(cfg.view_overrides.clone());
    generator.set_extra_fields(cfg.extra_fields.clone());
    generator.set_clone_strategy(cfg.clone_strategy.clone());
    generator.set_custom_derives(cfg.custom_derives.clone());
    generator.set_skip_fields(cfg.skip_fields.clone());
    generator.set_skip_validity_types(cfg.skip_validity_types.iter().cloned().collect());
    generator.set_skip_view_types(cfg.skip_view_types.iter().cloned().collect());
    generator.set_generate_clone_up_to_view_simple(cfg.generate_clone_up_to_view_simple);

    // Detect unit enums (all variants have no fields) for Copy derive support
    let mut unit_enums = HashSet::new();
    for (name, enum_def) in &cfg.registry.enums {
        let is_unit = enum_def
            .variants
            .iter()
            .all(|v| matches!(v.fields, VariantFields::Unit));
        if is_unit {
            let exec_name = generator.get_exec_type(name);
            unit_enums.insert(exec_name);
        }
    }
    generator.set_unit_enums(unit_enums);
    generator.set_arc_wrap_types(cfg.arc_wrap_types.iter().cloned().collect());
    generator.set_arc_wrap_fields(cfg.arc_wrap_fields.clone());

    let mut all_code = String::new();
    let mut all_warnings = Vec::new();

    // Header
    all_code.push_str("// Auto-generated concrete types by verus-transpiler\n");
    all_code.push_str("// DO NOT EDIT MANUALLY\n\n");

    // Auto-inject imports required by clone strategies and Arc wrapping
    let needs_hashset_clone_import = cfg.clone_strategy.values().any(|v| v == "verified");
    let needs_arc_import = !cfg.arc_wrap_types.is_empty();

    // Custom imports (sorted case-insensitively for rustfmt compatibility)
    // Filter out self-referential types_gen imports that would cause
    // "cannot glob-import a module into itself" errors
    if cfg.custom_imports.is_empty() {
        all_code.push_str("use vstd::prelude::*;\n");
        if needs_hashset_clone_import {
            all_code.push_str("use crate::common::collections::hashsets::clone_hashset_u64;\n");
            all_code.push_str("use std::collections::HashSet;\n");
        }
        if needs_arc_import {
            all_code.push_str("use std::sync::Arc;\n");
        }
        all_code.push('\n');
    } else {
        let mut sorted_imports: Vec<String> = cfg
            .custom_imports
            .iter()
            .filter(|imp| !imp.contains("types_gen"))
            .cloned()
            .collect();
        // Add clone_hashset_u64 import when verified clone strategy is active
        if needs_hashset_clone_import {
            let hashset_import =
                "use crate::common::collections::hashsets::clone_hashset_u64;".to_string();
            if !sorted_imports
                .iter()
                .any(|i| i.contains("clone_hashset_u64"))
            {
                sorted_imports.push(hashset_import);
            }
        }
        // Add Arc import when arc_wrap_types is active
        if needs_arc_import {
            let arc_import = "use std::sync::Arc;".to_string();
            if !sorted_imports.iter().any(|i| i.contains("std::sync::Arc")) {
                sorted_imports.push(arc_import);
            }
        }
        sorted_imports.sort_by_key(|a| a.to_lowercase());
        for import in &sorted_imports {
            all_code.push_str(import);
            if !import.ends_with('\n') {
                all_code.push('\n');
            }
        }
        all_code.push('\n');
    }

    // Re-export statements (outside verus! block)
    for re_export in cfg.re_exports {
        all_code.push_str(&format!("pub use {};\n", re_export));
    }
    if !cfg.re_exports.is_empty() {
        all_code.push('\n');
    }

    all_code.push_str("verus! {\n\n");

    // Generate type aliases (in insertion order, skip those in skip_types)
    let mut emitted_alias_names: HashSet<String> = HashSet::new();
    for alias_name in &cfg.registry.alias_order {
        if cfg.skip_types.contains(alias_name) {
            continue;
        }
        if let Some(alias) = cfg.registry.aliases.get(alias_name) {
            let exec_name = generator.get_exec_alias_name(&alias.name);
            let exec_type = generator.translate_alias_type(&alias.ty);
            all_code.push_str(&format!("pub type {} = {};\n", exec_name, exec_type));
            emitted_alias_names.insert(exec_name);
        }
    }
    // Extra aliases from config (sorted for deterministic output).
    let mut extra_alias_entries: Vec<(&String, &String)> = cfg.extra_type_aliases.iter().collect();
    extra_alias_entries.sort_by_key(|(a, _)| *a);
    for (alias_name, alias_target) in extra_alias_entries {
        if emitted_alias_names.contains(alias_name.as_str()) {
            all_warnings.push(format!(
                "extra_type_aliases contains duplicate alias `{}`; skipping",
                alias_name
            ));
            continue;
        }
        all_code.push_str(&format!("pub type {} = {};\n", alias_name, alias_target));
        emitted_alias_names.insert(alias_name.clone());
    }
    if !cfg.registry.aliases.is_empty() || !cfg.extra_type_aliases.is_empty() {
        all_code.push('\n');
    }

    // Generate structs (in insertion order, skip those in skip_types)
    for struct_name in &cfg.registry.struct_order {
        if cfg.skip_types.contains(struct_name) {
            continue;
        }
        if let Some(struct_def) = cfg.registry.structs.get(struct_name) {
            if struct_def.is_spec {
                let generated = generator.generate_struct(struct_def);
                all_code.push_str(&generated.code);
                all_code.push('\n');
                all_warnings.extend(generated.warnings);
            }
        }
    }

    // Generate enums (in insertion order, skip those in skip_types)
    for enum_name in &cfg.registry.enum_order {
        if cfg.skip_types.contains(enum_name) {
            continue;
        }
        if let Some(enum_def) = cfg.registry.enums.get(enum_name) {
            if enum_def.is_spec {
                let generated = generator.generate_enum(enum_def);
                all_code.push_str(&generated.code);
                all_code.push('\n');
                all_warnings.extend(generated.warnings);
            }
        }
    }

    if cfg.generate_unreachable_value_helper
        && !cfg
            .manual_code
            .is_some_and(|manual| manual.contains("fn unreachable_value<"))
    {
        all_code.push('\n');
        all_code.push_str(generate_unreachable_value_helper());
    }

    if let Some(manual_code) = cfg.manual_code {
        let manual = manual_code.trim();
        if !manual.is_empty() {
            all_code.push('\n');
            all_code.push_str(manual);
            all_code.push('\n');
        }
    }

    all_code.push_str("} // verus!\n");

    GeneratedCode {
        code: all_code,
        warnings: all_warnings,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Generics, Path};

    fn make_config() -> NamingConfig {
        NamingConfig::default()
    }

    #[test]
    fn test_generate_simple_struct() {
        let generator = TypeGenerator::new(make_config());

        let spec = StructDef {
            name: "LAcceptor".to_string(),
            generics: Generics::default(),
            fields: vec![
                FieldDef {
                    name: "max_bal".to_string(),
                    ty: Type::Named(Path::single("Ballot".to_string())),
                    is_public: true,
                },
                FieldDef {
                    name: "votes".to_string(),
                    ty: Type::Named(Path::single("Votes".to_string())),
                    is_public: true,
                },
            ],
            is_spec: true,
        };

        let result = generator.generate_struct(&spec);

        assert!(result.code.contains("#[derive(Clone)]"));
        assert!(result.code.contains("pub struct CAcceptor"));
        assert!(result.code.contains("pub max_bal: CBallot"));
        assert!(result.code.contains("pub votes: CVotes"));
        assert!(result.code.contains("fn well_formed"));
        assert!(result.code.contains("impl View for CAcceptor"));
    }

    #[test]
    fn test_generate_struct_with_primitives() {
        let generator = TypeGenerator::new(make_config());

        let spec = StructDef {
            name: "LState".to_string(),
            generics: Generics::default(),
            fields: vec![
                FieldDef {
                    name: "count".to_string(),
                    ty: Type::Nat,
                    is_public: true,
                },
                FieldDef {
                    name: "active".to_string(),
                    ty: Type::Bool,
                    is_public: true,
                },
            ],
            is_spec: true,
        };

        let result = generator.generate_struct(&spec);

        assert!(result.code.contains("pub struct CState"));
        assert!(result.code.contains("count: u64"));
        assert!(result.code.contains("active: bool"));
    }

    #[test]
    fn test_generate_enum() {
        let generator = TypeGenerator::new(make_config());

        let spec = EnumDef {
            name: "LMessage".to_string(),
            generics: Generics::default(),
            variants: vec![
                VariantDef {
                    name: "Msg1a".to_string(),
                    fields: VariantFields::Struct(vec![FieldDef {
                        name: "bal".to_string(),
                        ty: Type::Named(Path::single("Ballot".to_string())),
                        is_public: true,
                    }]),
                },
                VariantDef {
                    name: "Empty".to_string(),
                    fields: VariantFields::Unit,
                },
            ],
            is_spec: true,
        };

        let result = generator.generate_enum(&spec);

        assert!(result.code.contains("pub enum CMessage"));
        assert!(result.code.contains("Msg1a"));
        assert!(result.code.contains("Empty"));
        assert!(result.code.contains("fn well_formed"));
        assert!(result.code.contains("impl View for CMessage"));
    }

    #[test]
    fn test_generate_struct_with_collections() {
        let generator = TypeGenerator::new(make_config());

        let spec = StructDef {
            name: "LContainer".to_string(),
            generics: Generics::default(),
            fields: vec![
                FieldDef {
                    name: "items".to_string(),
                    ty: Type::Seq(Box::new(Type::Named(Path::single("Item".to_string())))),
                    is_public: true,
                },
                FieldDef {
                    name: "cache".to_string(),
                    ty: Type::Map(
                        Box::new(Type::Named(Path::single("Key".to_string()))),
                        Box::new(Type::Named(Path::single("Value".to_string()))),
                    ),
                    is_public: true,
                },
            ],
            is_spec: true,
        };

        let result = generator.generate_struct(&spec);

        assert!(result.code.contains("items: Vec<CItem>"));
        assert!(result.code.contains("cache: HashMap<CKey, CValue>"));
    }

    #[test]
    fn test_translate_type() {
        let generator = TypeGenerator::new(make_config());

        assert_eq!(
            generator.translate_type(&Type::Named(Path::single("LAcceptor".to_string()))),
            "CAcceptor"
        );
        assert_eq!(generator.translate_type(&Type::Bool), "bool");
        assert_eq!(generator.translate_type(&Type::Int), "i64");
        assert_eq!(generator.translate_type(&Type::Nat), "u64");
        assert_eq!(
            generator.translate_type(&Type::Seq(Box::new(Type::Named(Path::single(
                "LPacket".to_string()
            ))))),
            "Vec<CPacket>"
        );

        // Test with custom int_type/nat_type
        let custom_config = NamingConfig {
            int_type: "u64".to_string(),
            nat_type: "u64".to_string(),
            ..NamingConfig::default()
        };
        let custom_gen = TypeGenerator::new(custom_config);
        assert_eq!(custom_gen.translate_type(&Type::Int), "u64");
        assert_eq!(custom_gen.translate_type(&Type::Nat), "u64");

        // Test that Rust primitive types in Named position pass through unchanged
        assert_eq!(
            custom_gen.translate_type(&Type::Named(Path::single("u64".to_string()))),
            "u64"
        );
        assert_eq!(
            custom_gen.translate_type(&Type::Named(Path::single("i64".to_string()))),
            "i64"
        );
        // Map<u64, u64> should stay as HashMap<u64, u64>, not HashMap<Cu64, Cu64>
        assert_eq!(
            custom_gen.translate_type(&Type::Map(
                Box::new(Type::Named(Path::single("u64".to_string()))),
                Box::new(Type::Named(Path::single("u64".to_string()))),
            )),
            "HashMap<u64, u64>"
        );
    }

    #[test]
    fn test_naming_config_get_exec_type() {
        let config = make_config();

        // L-prefixed types with uppercase after L -> replace L with C
        assert_eq!(config.get_exec_type("LAcceptor"), "CAcceptor");
        assert_eq!(config.get_exec_type("LState"), "CState");

        // Types without L prefix -> prepend C
        assert_eq!(config.get_exec_type("Ballot"), "CBallot");

        // L followed by lowercase -> prepend C (not replace)
        // (e.g., "LearnerTuple" should become "CLearnerTuple", not "CearnerTuple")
        assert_eq!(config.get_exec_type("LearnerTuple"), "CLearnerTuple");
    }

    #[test]
    fn test_view_impl_as_int_conversion() {
        // Test that int fields get `as int` conversion in View impl
        let generator = TypeGenerator::new(make_config());

        let spec = StructDef {
            name: "Ballot".to_string(),
            generics: Generics::default(),
            fields: vec![
                FieldDef {
                    name: "seqno".to_string(),
                    ty: Type::Int,
                    is_public: true,
                },
                FieldDef {
                    name: "proposer_id".to_string(),
                    ty: Type::Int,
                    is_public: true,
                },
            ],
            is_spec: true,
        };

        let result = generator.generate_struct(&spec);

        // Check that View impl contains `as int` conversions
        assert!(
            result.code.contains("seqno: self.seqno as int"),
            "Should have 'as int' for seqno: {}",
            result.code
        );
        assert!(
            result.code.contains("proposer_id: self.proposer_id as int"),
            "Should have 'as int' for proposer_id: {}",
            result.code
        );
    }

    #[test]
    fn test_view_impl_mixed_fields() {
        // Test struct with both int fields and complex type fields
        let generator = TypeGenerator::new(make_config());

        let spec = StructDef {
            name: "LRequest".to_string(),
            generics: Generics::default(),
            fields: vec![
                FieldDef {
                    name: "client".to_string(),
                    ty: Type::Named(Path::single("AbstractEndPoint".to_string())),
                    is_public: true,
                },
                FieldDef {
                    name: "seqno".to_string(),
                    ty: Type::Int,
                    is_public: true,
                },
            ],
            is_spec: true,
        };

        let result = generator.generate_struct(&spec);

        // client should use @ operator
        assert!(
            result.code.contains("client: self.client@"),
            "Should have '@' for client: {}",
            result.code
        );
        // seqno should use as int
        assert!(
            result.code.contains("seqno: self.seqno as int"),
            "Should have 'as int' for seqno: {}",
            result.code
        );
    }

    #[test]
    fn test_type_remapping() {
        // Test that remapping table overrides default naming
        let mut remapping = HashMap::new();
        remapping.insert("AbstractEndPoint".to_string(), "EndPoint".to_string());
        remapping.insert("AppMessage".to_string(), "CAppMessage".to_string());

        let generator = TypeGenerator::new(make_config()).with_remapping(remapping);

        let spec = StructDef {
            name: "Request".to_string(),
            generics: Generics::default(),
            fields: vec![
                FieldDef {
                    name: "client".to_string(),
                    ty: Type::Named(Path::single("AbstractEndPoint".to_string())),
                    is_public: true,
                },
                FieldDef {
                    name: "msg".to_string(),
                    ty: Type::Named(Path::single("AppMessage".to_string())),
                    is_public: true,
                },
            ],
            is_spec: true,
        };

        let result = generator.generate_struct(&spec);

        // client should use remapped EndPoint, not CAbstractEndPoint
        assert!(
            result.code.contains("client: EndPoint"),
            "Should use remapped 'EndPoint': {}",
            result.code
        );
        // msg should use remapped CAppMessage
        assert!(
            result.code.contains("msg: CAppMessage"),
            "Should use remapped 'CAppMessage': {}",
            result.code
        );
    }

    #[test]
    fn test_type_remapping_in_collections() {
        // Test that remapping works for types inside collections
        let mut remapping = HashMap::new();
        remapping.insert("AbstractEndPoint".to_string(), "EndPoint".to_string());

        let generator = TypeGenerator::new(make_config()).with_remapping(remapping);

        let spec = StructDef {
            name: "LGroup".to_string(),
            generics: Generics::default(),
            fields: vec![FieldDef {
                name: "members".to_string(),
                ty: Type::Set(Box::new(Type::Named(Path::single(
                    "AbstractEndPoint".to_string(),
                )))),
                is_public: true,
            }],
            is_spec: true,
        };

        let result = generator.generate_struct(&spec);

        // Should use remapped EndPoint inside HashSet
        assert!(
            result.code.contains("members: HashSet<EndPoint>"),
            "Should use remapped 'EndPoint' in HashSet: {}",
            result.code
        );
    }

    #[test]
    fn test_custom_validity_predicate_name() {
        // Test that builder method allows customizing the validity predicate name
        let generator =
            TypeGenerator::new(make_config()).with_validity_predicate_name("valid".to_string());

        let spec = StructDef {
            name: "Ballot".to_string(),
            generics: Generics::default(),
            fields: vec![FieldDef {
                name: "seqno".to_string(),
                ty: Type::Int,
                is_public: true,
            }],
            is_spec: true,
        };

        let result = generator.generate_struct(&spec);

        // Should use "valid" instead of "well_formed"
        assert!(
            result.code.contains("fn valid"),
            "Should use custom validity predicate 'valid': {}",
            result.code
        );
        assert!(
            !result.code.contains("fn well_formed"),
            "Should NOT contain 'well_formed' when using 'valid': {}",
            result.code
        );
    }

    #[test]
    fn test_builder_methods_chainable() {
        // Test that all builder methods can be chained together
        let mut remapping = HashMap::new();
        remapping.insert("AbstractEndPoint".to_string(), "EndPoint".to_string());

        let generator = TypeGenerator::new(make_config())
            .with_remapping(remapping)
            .with_validity_predicate_name("valid".to_string())
            .with_primitive_types(vec!["u64".to_string()]);

        let spec = StructDef {
            name: "LNode".to_string(),
            generics: Generics::default(),
            fields: vec![
                FieldDef {
                    name: "id".to_string(),
                    ty: Type::Int,
                    is_public: true,
                },
                FieldDef {
                    name: "endpoint".to_string(),
                    ty: Type::Named(Path::single("AbstractEndPoint".to_string())),
                    is_public: true,
                },
            ],
            is_spec: true,
        };

        let result = generator.generate_struct(&spec);

        // Remapping applied
        assert!(
            result.code.contains("EndPoint"),
            "Remapping should convert AbstractEndPoint to EndPoint: {}",
            result.code
        );
        // Custom validity predicate name
        assert!(
            result.code.contains("fn valid"),
            "Should use custom 'valid' predicate: {}",
            result.code
        );
    }

    #[test]
    fn test_default_validity_predicate_is_well_formed() {
        // Test that default TypeGenerator uses "well_formed"
        let generator = TypeGenerator::new(make_config());

        let spec = StructDef {
            name: "Ballot".to_string(),
            generics: Generics::default(),
            fields: vec![FieldDef {
                name: "seqno".to_string(),
                ty: Type::Int,
                is_public: true,
            }],
            is_spec: true,
        };

        let result = generator.generate_struct(&spec);

        assert!(
            result.code.contains("fn well_formed"),
            "Default should use 'well_formed': {}",
            result.code
        );
    }

    #[test]
    fn test_generate_type_alias() {
        use crate::types::TypeAlias;

        let mut registry = TypeRegistry::new();
        registry.register_alias(TypeAlias {
            name: "RequestBatch".to_string(),
            generics: Generics::default(),
            ty: Type::Seq(Box::new(Type::Named(Path::single("Request".to_string())))),
        });

        let config = make_config();
        let generated = generate_all_types_with_options(
            &registry,
            &config,
            &HashMap::new(),
            &[],
            "well_formed",
        );

        assert!(
            generated
                .code
                .contains("pub type CRequestBatch = Vec<CRequest>;"),
            "Should generate alias: {}",
            generated.code
        );
    }

    #[test]
    fn test_generate_type_alias_with_remapping() {
        use crate::types::TypeAlias;

        let mut registry = TypeRegistry::new();
        registry.register_alias(TypeAlias {
            name: "OperationNumber".to_string(),
            generics: Generics::default(),
            ty: Type::Int,
        });

        let config = NamingConfig {
            int_type: "u64".to_string(),
            ..NamingConfig::default()
        };
        let generated = generate_all_types_with_options(
            &registry,
            &config,
            &HashMap::new(),
            &[],
            "well_formed",
        );

        assert!(
            generated.code.contains("pub type COperationNumber = u64;"),
            "Should generate alias with int->u64: {}",
            generated.code
        );
    }

    #[test]
    fn test_generate_type_alias_map() {
        use crate::types::TypeAlias;

        let mut registry = TypeRegistry::new();
        registry.register_alias(TypeAlias {
            name: "Votes".to_string(),
            generics: Generics::default(),
            ty: Type::Map(
                Box::new(Type::Named(Path::single("OperationNumber".to_string()))),
                Box::new(Type::Named(Path::single("Vote".to_string()))),
            ),
        });

        let config = make_config();
        let generated = generate_all_types_with_options(
            &registry,
            &config,
            &HashMap::new(),
            &[],
            "well_formed",
        );

        assert!(
            generated
                .code
                .contains("pub type CVotes = HashMap<COperationNumber, CVote>;"),
            "Should generate map alias: {}",
            generated.code
        );
    }

    #[test]
    fn test_multi_file_registry_insertion_order() {
        use crate::types::TypeAlias;

        let mut registry = TypeRegistry::new();

        // Simulate file 1: type alias
        registry.register_alias(TypeAlias {
            name: "OperationNumber".to_string(),
            generics: Generics::default(),
            ty: Type::Int,
        });

        // Simulate file 2: struct using that alias
        registry.register_struct(StructDef {
            name: "LAcceptor".to_string(),
            generics: Generics::default(),
            fields: vec![FieldDef {
                name: "max_bal".to_string(),
                ty: Type::Named(Path::single("Ballot".to_string())),
                is_public: true,
            }],
            is_spec: true,
        });

        // Verify insertion order is preserved
        assert_eq!(registry.alias_order, vec!["OperationNumber"]);
        assert_eq!(registry.struct_order, vec!["LAcceptor"]);

        // Verify generated code has aliases before structs
        let config = NamingConfig {
            int_type: "u64".to_string(),
            ..NamingConfig::default()
        };
        let generated = generate_all_types_with_options(
            &registry,
            &config,
            &HashMap::new(),
            &[],
            "well_formed",
        );

        let alias_pos = generated.code.find("pub type COperationNumber").unwrap();
        let struct_pos = generated.code.find("pub struct CAcceptor").unwrap();
        assert!(
            alias_pos < struct_pos,
            "Aliases should appear before structs in output"
        );
    }

    #[test]
    fn test_multi_file_registry_dedup() {
        // If same type registered twice, should keep last but not duplicate in order
        let mut registry = TypeRegistry::new();

        registry.register_struct(StructDef {
            name: "LState".to_string(),
            generics: Generics::default(),
            fields: vec![FieldDef {
                name: "x".to_string(),
                ty: Type::Int,
                is_public: true,
            }],
            is_spec: true,
        });

        // Re-register same name with different fields
        registry.register_struct(StructDef {
            name: "LState".to_string(),
            generics: Generics::default(),
            fields: vec![
                FieldDef {
                    name: "x".to_string(),
                    ty: Type::Int,
                    is_public: true,
                },
                FieldDef {
                    name: "y".to_string(),
                    ty: Type::Bool,
                    is_public: true,
                },
            ],
            is_spec: true,
        });

        // Order should not have duplicates
        assert_eq!(registry.struct_order.len(), 1);
        // Should keep the latest definition (with 2 fields)
        assert_eq!(registry.structs["LState"].fields.len(), 2);
    }

    #[test]
    fn test_enum_variant_remapping() {
        let mut remapping = HashMap::new();
        remapping.insert("RslMessage1a".to_string(), "CMessage1a".to_string());
        remapping.insert("RslMessage1b".to_string(), "CMessage1b".to_string());

        let generator = TypeGenerator::new(NamingConfig::default())
            .with_remapping(remapping)
            .with_validity_predicate_name("valid".to_string());

        let spec = EnumDef {
            name: "RslMessage".to_string(),
            generics: Generics::default(),
            variants: vec![
                VariantDef {
                    name: "RslMessage1a".to_string(),
                    fields: VariantFields::Struct(vec![FieldDef {
                        name: "bal_1a".to_string(),
                        ty: Type::Named(Path::single("Ballot".to_string())),
                        is_public: true,
                    }]),
                },
                VariantDef {
                    name: "RslMessage1b".to_string(),
                    fields: VariantFields::Unit,
                },
                VariantDef {
                    name: "Heartbeat".to_string(),
                    fields: VariantFields::Unit,
                },
            ],
            is_spec: true,
        };

        let result = generator.generate_enum(&spec);

        // Exec enum should use remapped variant names
        assert!(
            result.code.contains("CMessage1a {"),
            "Should remap RslMessage1a -> CMessage1a: {}",
            result.code
        );
        assert!(
            result.code.contains("CMessage1b,"),
            "Should remap RslMessage1b -> CMessage1b: {}",
            result.code
        );
        // Unmapped variant should stay unchanged
        assert!(
            result.code.contains("Heartbeat,"),
            "Unmapped variant should stay: {}",
            result.code
        );
    }

    #[test]
    fn test_enum_variant_remapping_view_trait() {
        let mut remapping = HashMap::new();
        remapping.insert("RslMessage1a".to_string(), "CMessage1a".to_string());

        let generator = TypeGenerator::new(NamingConfig::default())
            .with_remapping(remapping)
            .with_validity_predicate_name("valid".to_string());

        let spec = EnumDef {
            name: "LMessage".to_string(),
            generics: Generics::default(),
            variants: vec![
                VariantDef {
                    name: "RslMessage1a".to_string(),
                    fields: VariantFields::Struct(vec![FieldDef {
                        name: "bal".to_string(),
                        ty: Type::Int,
                        is_public: true,
                    }]),
                },
                VariantDef {
                    name: "Active".to_string(),
                    fields: VariantFields::Unit,
                },
            ],
            is_spec: true,
        };

        let result = generator.generate_enum(&spec);

        // View trait: exec side should use remapped name, spec side should use original
        assert!(
            result
                .code
                .contains("CMessage::CMessage1a { bal } => LMessage::RslMessage1a"),
            "View should map exec CMessage1a -> spec RslMessage1a: {}",
            result.code
        );
        // Unmapped variant should use same name on both sides
        assert!(
            result.code.contains("CMessage::Active => LMessage::Active"),
            "Unmapped variant same on both sides: {}",
            result.code
        );
    }

    #[test]
    fn test_view_overrides() {
        let mut generator = TypeGenerator::new(make_config());
        let mut overrides = HashMap::new();
        overrides.insert(
            "LAcceptor.votes".to_string(),
            "abstractify_cvotes(&self.votes)".to_string(),
        );
        generator.set_view_overrides(overrides);

        let spec = StructDef {
            name: "LAcceptor".to_string(),
            generics: Generics::default(),
            fields: vec![
                FieldDef {
                    name: "max_bal".to_string(),
                    ty: Type::Named(Path::single("Ballot".to_string())),
                    is_public: true,
                },
                FieldDef {
                    name: "votes".to_string(),
                    ty: Type::Named(Path::single("Votes".to_string())),
                    is_public: true,
                },
            ],
            is_spec: true,
        };

        let result = generator.generate_struct(&spec);

        assert!(
            result
                .code
                .contains("votes: abstractify_cvotes(&self.votes)"),
            "Should use view override for votes: {}",
            result.code
        );
        // max_bal should use default view (no override)
        assert!(
            result.code.contains("max_bal: self.max_bal@"),
            "Should use default view for max_bal: {}",
            result.code
        );
    }

    #[test]
    fn test_extra_fields() {
        let mut generator = TypeGenerator::new(make_config());
        let mut extra = HashMap::new();
        extra.insert("CAcceptor.min_vote_opn".to_string(), "u64 = 0".to_string());
        generator.set_extra_fields(extra);

        let spec = StructDef {
            name: "LAcceptor".to_string(),
            generics: Generics::default(),
            fields: vec![FieldDef {
                name: "max_bal".to_string(),
                ty: Type::Named(Path::single("Ballot".to_string())),
                is_public: true,
            }],
            is_spec: true,
        };

        let result = generator.generate_struct(&spec);

        assert!(
            result.code.contains("pub min_vote_opn: u64,"),
            "Should include extra field: {}",
            result.code
        );
        // Verify struct contains both spec field and extra field
        assert!(
            result.code.contains("pub max_bal: CBallot,"),
            "Should also include spec fields: {}",
            result.code
        );
    }

    #[test]
    fn test_clone_strategy_external_body() {
        let mut generator = TypeGenerator::new(make_config());
        let mut strategy = HashMap::new();
        strategy.insert("CState".to_string(), "external_body".to_string());
        generator.set_clone_strategy(strategy);

        let spec = StructDef {
            name: "LState".to_string(),
            generics: Generics::default(),
            fields: vec![FieldDef {
                name: "value".to_string(),
                ty: Type::Int,
                is_public: true,
            }],
            is_spec: true,
        };

        let result = generator.generate_struct(&spec);

        assert!(
            !result.code.contains("#[derive(Clone)]"),
            "Should NOT have derive Clone: {}",
            result.code
        );
        assert!(
            result.code.contains("#[verifier(external_body)]"),
            "Should have external_body Clone: {}",
            result.code
        );
        assert!(
            result.code.contains("impl Clone for CState"),
            "Should have manual Clone impl: {}",
            result.code
        );
    }

    #[test]
    fn test_clone_strategy_default_is_derive() {
        let generator = TypeGenerator::new(make_config());

        let spec = StructDef {
            name: "LState".to_string(),
            generics: Generics::default(),
            fields: vec![FieldDef {
                name: "value".to_string(),
                ty: Type::Int,
                is_public: true,
            }],
            is_spec: true,
        };

        let result = generator.generate_struct(&spec);

        assert!(
            result.code.contains("#[derive(Clone)]"),
            "Default should use derive Clone: {}",
            result.code
        );
    }

    #[test]
    fn test_skip_types() {
        let mut registry = TypeRegistry::new();
        registry.register_struct(StructDef {
            name: "Ballot".to_string(),
            generics: Generics::default(),
            fields: vec![FieldDef {
                name: "seqno".to_string(),
                ty: Type::Int,
                is_public: true,
            }],
            is_spec: true,
        });
        registry.register_struct(StructDef {
            name: "LAcceptor".to_string(),
            generics: Generics::default(),
            fields: vec![FieldDef {
                name: "max_bal".to_string(),
                ty: Type::Named(Path {
                    segments: vec!["Ballot".to_string()],
                }),
                is_public: true,
            }],
            is_spec: true,
        });

        let naming = make_config();
        let remapping = HashMap::new();
        let skip_types = vec!["Ballot".to_string()];
        let cfg = TypeGenConfig {
            registry: &registry,
            naming: &naming,
            remapping: &remapping,
            custom_imports: &[],
            validity_predicate_name: "well_formed",
            view_overrides: &HashMap::new(),
            extra_fields: &HashMap::new(),
            clone_strategy: &HashMap::new(),
            skip_types: &skip_types,
            re_exports: &[],
            extra_type_aliases: &HashMap::new(),
            custom_derives: &HashMap::new(),
            skip_fields: &HashMap::new(),
            skip_validity_types: &[],
            skip_view_types: &[],
            generate_clone_up_to_view_simple: false,
            generate_unreachable_value_helper: false,
            manual_code: None,
            arc_wrap_types: &[],
            arc_wrap_fields: &HashMap::new(),
        };

        let result = generate_all_types_full(&cfg);

        // Ballot should be skipped
        assert!(
            !result.code.contains("pub struct CBallot"),
            "Ballot should be skipped: {}",
            result.code
        );
        // LAcceptor should still be generated
        assert!(
            result.code.contains("pub struct CAcceptor"),
            "LAcceptor should be generated: {}",
            result.code
        );
    }

    #[test]
    fn test_re_exports() {
        let registry = TypeRegistry::new();
        let naming = make_config();
        let remapping = HashMap::new();
        let re_exports = vec![
            "crate::implementation::RSL::types_i::*".to_string(),
            "crate::implementation::RSL::cmessage::CPacket".to_string(),
        ];
        let cfg = TypeGenConfig {
            registry: &registry,
            naming: &naming,
            remapping: &remapping,
            custom_imports: &[],
            validity_predicate_name: "well_formed",
            view_overrides: &HashMap::new(),
            extra_fields: &HashMap::new(),
            clone_strategy: &HashMap::new(),
            skip_types: &[],
            re_exports: &re_exports,
            extra_type_aliases: &HashMap::new(),
            custom_derives: &HashMap::new(),
            skip_fields: &HashMap::new(),
            skip_validity_types: &[],
            skip_view_types: &[],
            generate_clone_up_to_view_simple: false,
            generate_unreachable_value_helper: false,
            manual_code: None,
            arc_wrap_types: &[],
            arc_wrap_fields: &HashMap::new(),
        };

        let result = generate_all_types_full(&cfg);

        assert!(
            result
                .code
                .contains("pub use crate::implementation::RSL::types_i::*;"),
            "Should contain re-export: {}",
            result.code
        );
        assert!(
            result
                .code
                .contains("pub use crate::implementation::RSL::cmessage::CPacket;"),
            "Should contain re-export: {}",
            result.code
        );
    }

    #[test]
    fn test_extra_type_aliases_generated() {
        let registry = TypeRegistry::new();
        let naming = make_config();
        let remapping = HashMap::new();
        let mut extra_aliases = HashMap::new();
        extra_aliases.insert(
            "CRslIo".to_string(),
            "LIoOp<EndPoint, CMessage>".to_string(),
        );
        extra_aliases.insert(
            "CReplyMap".to_string(),
            "HashMap<EndPoint, CReply>".to_string(),
        );

        let cfg = TypeGenConfig {
            registry: &registry,
            naming: &naming,
            remapping: &remapping,
            custom_imports: &[],
            validity_predicate_name: "well_formed",
            view_overrides: &HashMap::new(),
            extra_fields: &HashMap::new(),
            clone_strategy: &HashMap::new(),
            skip_types: &[],
            re_exports: &[],
            extra_type_aliases: &extra_aliases,
            custom_derives: &HashMap::new(),
            skip_fields: &HashMap::new(),
            skip_validity_types: &[],
            skip_view_types: &[],
            generate_clone_up_to_view_simple: false,
            generate_unreachable_value_helper: false,
            manual_code: None,
            arc_wrap_types: &[],
            arc_wrap_fields: &HashMap::new(),
        };

        let result = generate_all_types_full(&cfg);
        assert!(
            result
                .code
                .contains("pub type CRslIo = LIoOp<EndPoint, CMessage>;"),
            "Should include configured CRslIo alias: {}",
            result.code
        );
        assert!(
            result
                .code
                .contains("pub type CReplyMap = HashMap<EndPoint, CReply>;"),
            "Should include configured CReplyMap alias: {}",
            result.code
        );
    }

    #[test]
    fn test_generate_clone_up_to_view_simple_for_primitive_struct() {
        let mut registry = TypeRegistry::new();
        registry.register_struct(StructDef {
            name: "LClockReading".to_string(),
            generics: Generics::default(),
            fields: vec![FieldDef {
                name: "t".to_string(),
                ty: Type::Int,
                is_public: true,
            }],
            is_spec: true,
        });

        let naming = make_config();
        let remapping = HashMap::new();
        let cfg = TypeGenConfig {
            registry: &registry,
            naming: &naming,
            remapping: &remapping,
            custom_imports: &[],
            validity_predicate_name: "valid",
            view_overrides: &HashMap::new(),
            extra_fields: &HashMap::new(),
            clone_strategy: &HashMap::new(),
            skip_types: &[],
            re_exports: &[],
            extra_type_aliases: &HashMap::new(),
            custom_derives: &HashMap::new(),
            skip_fields: &HashMap::new(),
            skip_validity_types: &[],
            skip_view_types: &[],
            generate_clone_up_to_view_simple: true,
            generate_unreachable_value_helper: false,
            manual_code: None,
            arc_wrap_types: &[],
            arc_wrap_fields: &HashMap::new(),
        };
        let result = generate_all_types_full(&cfg);
        assert!(
            result
                .code
                .contains("pub fn clone_up_to_view(&self) -> (result: Self)"),
            "primitive-only struct should get clone_up_to_view: {}",
            result.code
        );
        assert!(
            result.code.contains("t: self.t"),
            "clone_up_to_view should copy primitive fields: {}",
            result.code
        );
    }

    #[test]
    fn test_generate_clone_up_to_view_simple_skips_non_primitive_struct() {
        let mut registry = TypeRegistry::new();
        registry.register_struct(StructDef {
            name: "LState".to_string(),
            generics: Generics::default(),
            fields: vec![FieldDef {
                name: "bal".to_string(),
                ty: Type::Named(Path::single("Ballot".to_string())),
                is_public: true,
            }],
            is_spec: true,
        });

        let naming = make_config();
        let remapping = HashMap::new();
        let cfg = TypeGenConfig {
            registry: &registry,
            naming: &naming,
            remapping: &remapping,
            custom_imports: &[],
            validity_predicate_name: "valid",
            view_overrides: &HashMap::new(),
            extra_fields: &HashMap::new(),
            clone_strategy: &HashMap::new(),
            skip_types: &[],
            re_exports: &[],
            extra_type_aliases: &HashMap::new(),
            custom_derives: &HashMap::new(),
            skip_fields: &HashMap::new(),
            skip_validity_types: &[],
            skip_view_types: &[],
            generate_clone_up_to_view_simple: true,
            generate_unreachable_value_helper: false,
            manual_code: None,
            arc_wrap_types: &[],
            arc_wrap_fields: &HashMap::new(),
        };
        let result = generate_all_types_full(&cfg);
        assert!(
            !result
                .code
                .contains("pub fn clone_up_to_view(&self) -> (result: Self)"),
            "non-primitive struct should not get auto clone_up_to_view: {}",
            result.code
        );
    }

    #[test]
    fn test_skip_validity_types_suppresses_validity_generation() {
        let mut registry = TypeRegistry::new();
        registry.register_struct(StructDef {
            name: "LClockReading".to_string(),
            generics: Generics::default(),
            fields: vec![FieldDef {
                name: "t".to_string(),
                ty: Type::Int,
                is_public: true,
            }],
            is_spec: true,
        });

        let naming = make_config();
        let remapping = HashMap::new();
        let skip_validity_types = vec!["CClockReading".to_string()];
        let cfg = TypeGenConfig {
            registry: &registry,
            naming: &naming,
            remapping: &remapping,
            custom_imports: &[],
            validity_predicate_name: "valid",
            view_overrides: &HashMap::new(),
            extra_fields: &HashMap::new(),
            clone_strategy: &HashMap::new(),
            skip_types: &[],
            re_exports: &[],
            extra_type_aliases: &HashMap::new(),
            custom_derives: &HashMap::new(),
            skip_fields: &HashMap::new(),
            skip_validity_types: &skip_validity_types,
            skip_view_types: &[],
            generate_clone_up_to_view_simple: false,
            generate_unreachable_value_helper: false,
            manual_code: None,
            arc_wrap_types: &[],
            arc_wrap_fields: &HashMap::new(),
        };
        let result = generate_all_types_full(&cfg);
        assert!(
            !result
                .code
                .contains("pub open spec fn valid(&self) -> bool"),
            "CClockReading valid() should be skipped: {}",
            result.code
        );
        assert!(
            result.code.contains("impl View for CClockReading"),
            "View impl should still be generated when only validity is skipped: {}",
            result.code
        );
    }

    #[test]
    fn test_skip_view_types_suppresses_view_generation() {
        let mut registry = TypeRegistry::new();
        registry.register_struct(StructDef {
            name: "LClockReading".to_string(),
            generics: Generics::default(),
            fields: vec![FieldDef {
                name: "t".to_string(),
                ty: Type::Int,
                is_public: true,
            }],
            is_spec: true,
        });

        let naming = make_config();
        let remapping = HashMap::new();
        let skip_view_types = vec!["CClockReading".to_string()];
        let cfg = TypeGenConfig {
            registry: &registry,
            naming: &naming,
            remapping: &remapping,
            custom_imports: &[],
            validity_predicate_name: "valid",
            view_overrides: &HashMap::new(),
            extra_fields: &HashMap::new(),
            clone_strategy: &HashMap::new(),
            skip_types: &[],
            re_exports: &[],
            extra_type_aliases: &HashMap::new(),
            custom_derives: &HashMap::new(),
            skip_fields: &HashMap::new(),
            skip_validity_types: &[],
            skip_view_types: &skip_view_types,
            generate_clone_up_to_view_simple: false,
            generate_unreachable_value_helper: false,
            manual_code: None,
            arc_wrap_types: &[],
            arc_wrap_fields: &HashMap::new(),
        };
        let result = generate_all_types_full(&cfg);
        assert!(
            result
                .code
                .contains("pub open spec fn valid(&self) -> bool"),
            "valid() should still be generated when only View impl is skipped: {}",
            result.code
        );
        assert!(
            !result.code.contains("impl View for CClockReading"),
            "CClockReading View impl should be skipped: {}",
            result.code
        );
    }

    #[test]
    fn test_custom_derives_struct() {
        let mut generator = TypeGenerator::new(make_config());
        let mut derives = HashMap::new();
        derives.insert(
            "CBallot".to_string(),
            vec!["Copy".to_string(), "PartialEq".to_string()],
        );
        generator.set_custom_derives(derives);

        let spec = StructDef {
            name: "Ballot".to_string(),
            generics: Generics::default(),
            fields: vec![FieldDef {
                name: "seqno".to_string(),
                ty: Type::Int,
                is_public: true,
            }],
            is_spec: true,
        };

        let result = generator.generate_struct(&spec);

        // Should have Clone, Copy, PartialEq in derive
        assert!(
            result.code.contains("#[derive(Clone, Copy, PartialEq)]"),
            "Should have merged derives: {}",
            result.code
        );
    }

    #[test]
    fn test_custom_derives_enum() {
        let mut generator = TypeGenerator::new(make_config());
        let mut derives = HashMap::new();
        derives.insert(
            "CMessage".to_string(),
            vec!["PartialEq".to_string(), "Eq".to_string()],
        );
        generator.set_custom_derives(derives);

        let spec = EnumDef {
            name: "LMessage".to_string(),
            generics: Generics::default(),
            variants: vec![
                VariantDef {
                    name: "Ping".to_string(),
                    fields: VariantFields::Unit,
                },
                VariantDef {
                    name: "Pong".to_string(),
                    fields: VariantFields::Unit,
                },
            ],
            is_spec: true,
        };

        let result = generator.generate_enum(&spec);

        assert!(
            result.code.contains("#[derive(Clone, PartialEq, Eq)]"),
            "Should have merged derives for enum: {}",
            result.code
        );
    }

    #[test]
    fn test_custom_derives_with_external_body_clone() {
        // When clone_strategy is external_body, Clone should NOT be in derive
        // but custom derives should still be added
        let mut generator = TypeGenerator::new(make_config());
        let mut strategy = HashMap::new();
        strategy.insert("CState".to_string(), "external_body".to_string());
        generator.set_clone_strategy(strategy);
        let mut derives = HashMap::new();
        derives.insert("CState".to_string(), vec!["Copy".to_string()]);
        generator.set_custom_derives(derives);

        let spec = StructDef {
            name: "LState".to_string(),
            generics: Generics::default(),
            fields: vec![FieldDef {
                name: "value".to_string(),
                ty: Type::Int,
                is_public: true,
            }],
            is_spec: true,
        };

        let result = generator.generate_struct(&spec);

        // Should have Copy in derive (not Clone since it's external_body)
        assert!(
            result.code.contains("#[derive(Copy)]"),
            "Should have Copy derive without Clone: {}",
            result.code
        );
        assert!(
            result.code.contains("#[verifier(external_body)]"),
            "Should still have external_body Clone: {}",
            result.code
        );
    }

    #[test]
    fn test_custom_derives_no_duplicate() {
        // If Clone is already added by strategy and also in custom_derives, no duplicate
        let mut generator = TypeGenerator::new(make_config());
        let mut derives = HashMap::new();
        derives.insert(
            "CState".to_string(),
            vec!["Clone".to_string(), "Copy".to_string()],
        );
        generator.set_custom_derives(derives);

        let spec = StructDef {
            name: "LState".to_string(),
            generics: Generics::default(),
            fields: vec![FieldDef {
                name: "value".to_string(),
                ty: Type::Int,
                is_public: true,
            }],
            is_spec: true,
        };

        let result = generator.generate_struct(&spec);

        // Should have Clone, Copy (no duplicate Clone)
        assert!(
            result.code.contains("#[derive(Clone, Copy)]"),
            "Should not duplicate Clone: {}",
            result.code
        );
    }

    #[test]
    fn test_skip_fields_struct_definition() {
        let mut generator = TypeGenerator::new(make_config());
        let mut skip = HashMap::new();
        skip.insert("CState".to_string(), vec!["ghost_field".to_string()]);
        generator.set_skip_fields(skip);

        let spec = StructDef {
            name: "LState".to_string(),
            generics: Generics::default(),
            fields: vec![
                FieldDef {
                    name: "value".to_string(),
                    ty: Type::Int,
                    is_public: true,
                },
                FieldDef {
                    name: "ghost_field".to_string(),
                    ty: Type::Named(Path::single("SomeType".to_string())),
                    is_public: true,
                },
            ],
            is_spec: true,
        };

        let result = generator.generate_struct(&spec);

        // Struct should have value but not ghost_field
        assert!(
            result.code.contains("value: i64"),
            "Should include non-skipped field: {}",
            result.code
        );
        assert!(
            !result.code.contains("ghost_field"),
            "Should skip ghost_field in struct, well_formed, and View: {}",
            result.code
        );
    }

    #[test]
    fn test_skip_fields_well_formed() {
        // A skipped field with a complex type should not appear in well_formed
        let mut generator = TypeGenerator::new(make_config());
        let mut skip = HashMap::new();
        skip.insert("CState".to_string(), vec!["complex".to_string()]);
        generator.set_skip_fields(skip);

        let spec = StructDef {
            name: "LState".to_string(),
            generics: Generics::default(),
            fields: vec![
                FieldDef {
                    name: "simple".to_string(),
                    ty: Type::Named(Path::single("Item".to_string())),
                    is_public: true,
                },
                FieldDef {
                    name: "complex".to_string(),
                    ty: Type::Named(Path::single("BigType".to_string())),
                    is_public: true,
                },
            ],
            is_spec: true,
        };

        let result = generator.generate_struct(&spec);

        // well_formed should only check simple, not complex
        assert!(
            result.code.contains("self.simple.well_formed()"),
            "Should check simple field: {}",
            result.code
        );
        assert!(
            !result.code.contains("self.complex.well_formed()"),
            "Should NOT check skipped complex field: {}",
            result.code
        );
    }

    #[test]
    fn test_skip_fields_view_impl() {
        // A skipped field should not appear in View impl
        let mut generator = TypeGenerator::new(make_config());
        let mut skip = HashMap::new();
        skip.insert("CState".to_string(), vec!["hidden".to_string()]);
        generator.set_skip_fields(skip);

        let spec = StructDef {
            name: "LState".to_string(),
            generics: Generics::default(),
            fields: vec![
                FieldDef {
                    name: "visible".to_string(),
                    ty: Type::Int,
                    is_public: true,
                },
                FieldDef {
                    name: "hidden".to_string(),
                    ty: Type::Int,
                    is_public: true,
                },
            ],
            is_spec: true,
        };

        let result = generator.generate_struct(&spec);

        // View should have visible but not hidden
        assert!(
            result.code.contains("visible: self.visible as int"),
            "Should include visible in View: {}",
            result.code
        );
        assert!(
            !result.code.contains("hidden: self.hidden"),
            "Should NOT include hidden in View: {}",
            result.code
        );
    }

    #[test]
    fn test_skip_fields_with_view_override() {
        // A skipped field WITH a view_override should still appear in View impl
        // (the spec type still has the field, so View must provide a value)
        let mut generator = TypeGenerator::new(make_config());
        let mut skip = HashMap::new();
        skip.insert("CState".to_string(), vec!["ghost_ids".to_string()]);
        generator.set_skip_fields(skip);
        let mut overrides = HashMap::new();
        overrides.insert(
            "LState.ghost_ids".to_string(),
            "Set::<int>::empty()".to_string(),
        );
        generator.set_view_overrides(overrides);

        let spec = StructDef {
            name: "LState".to_string(),
            generics: Generics::default(),
            fields: vec![
                FieldDef {
                    name: "value".to_string(),
                    ty: Type::Int,
                    is_public: true,
                },
                FieldDef {
                    name: "ghost_ids".to_string(),
                    ty: Type::Set(Box::new(Type::Int)),
                    is_public: true,
                },
            ],
            is_spec: true,
        };

        let result = generator.generate_struct(&spec);

        // Struct should NOT have ghost_ids field
        assert!(
            !result.code.contains("ghost_ids: HashSet"),
            "Should skip ghost_ids from struct definition: {}",
            result.code
        );
        // well_formed should NOT check ghost_ids
        assert!(
            !result.code.contains("self.ghost_ids"),
            "Should skip ghost_ids from well_formed: {}",
            result.code
        );
        // View SHOULD include ghost_ids with the override expression
        assert!(
            result.code.contains("ghost_ids: Set::<int>::empty()"),
            "Should include ghost_ids in View with override: {}",
            result.code
        );
    }

    #[test]
    fn test_custom_derives_config_parsing() {
        let toml = r#"
            [custom_derives]
            "CBallot" = ["Copy", "PartialEq", "Eq", "Hash"]
            "CState" = ["Copy"]
        "#;

        let config =
            crate::config::TranspilerConfig::from_toml(toml).expect("Failed to parse TOML");
        assert_eq!(config.custom_derives.len(), 2);
        assert_eq!(
            config.custom_derives.get("CBallot"),
            Some(&vec![
                "Copy".to_string(),
                "PartialEq".to_string(),
                "Eq".to_string(),
                "Hash".to_string()
            ])
        );
        assert_eq!(
            config.custom_derives.get("CState"),
            Some(&vec!["Copy".to_string()])
        );
    }

    #[test]
    fn test_skip_fields_config_parsing() {
        let toml = r#"
            [skip_fields]
            "CConfiguration" = ["clientIds"]
            "CProposer" = ["ghost_state", "extra"]
        "#;

        let config =
            crate::config::TranspilerConfig::from_toml(toml).expect("Failed to parse TOML");
        assert_eq!(config.skip_fields.len(), 2);
        assert_eq!(
            config.skip_fields.get("CConfiguration"),
            Some(&vec!["clientIds".to_string()])
        );
        assert_eq!(
            config.skip_fields.get("CProposer"),
            Some(&vec!["ghost_state".to_string(), "extra".to_string()])
        );
    }

    #[test]
    fn test_custom_derives_via_type_gen_config() {
        // Test that custom_derives flows through the full generation pipeline
        let mut registry = TypeRegistry::new();
        registry.register_struct(StructDef {
            name: "Ballot".to_string(),
            generics: Generics::default(),
            fields: vec![FieldDef {
                name: "seqno".to_string(),
                ty: Type::Int,
                is_public: true,
            }],
            is_spec: true,
        });

        let naming = make_config();
        let remapping = HashMap::new();
        let mut custom_derives = HashMap::new();
        custom_derives.insert(
            "CBallot".to_string(),
            vec!["Copy".to_string(), "PartialEq".to_string()],
        );

        let cfg = TypeGenConfig {
            registry: &registry,
            naming: &naming,
            remapping: &remapping,
            custom_imports: &[],
            validity_predicate_name: "well_formed",
            view_overrides: &HashMap::new(),
            extra_fields: &HashMap::new(),
            clone_strategy: &HashMap::new(),
            skip_types: &[],
            re_exports: &[],
            extra_type_aliases: &HashMap::new(),
            custom_derives: &custom_derives,
            skip_fields: &HashMap::new(),
            skip_validity_types: &[],
            skip_view_types: &[],
            generate_clone_up_to_view_simple: false,
            generate_unreachable_value_helper: false,
            manual_code: None,
            arc_wrap_types: &[],
            arc_wrap_fields: &HashMap::new(),
        };

        let result = generate_all_types_full(&cfg);

        assert!(
            result.code.contains("#[derive(Clone, Copy, PartialEq)]"),
            "Should have custom derives via TypeGenConfig: {}",
            result.code
        );
    }

    #[test]
    fn test_skip_fields_via_type_gen_config() {
        // Test that skip_fields flows through the full generation pipeline
        let mut registry = TypeRegistry::new();
        registry.register_struct(StructDef {
            name: "LState".to_string(),
            generics: Generics::default(),
            fields: vec![
                FieldDef {
                    name: "count".to_string(),
                    ty: Type::Int,
                    is_public: true,
                },
                FieldDef {
                    name: "ghost_data".to_string(),
                    ty: Type::Named(Path::single("SomeType".to_string())),
                    is_public: true,
                },
            ],
            is_spec: true,
        });

        let naming = make_config();
        let remapping = HashMap::new();
        let mut skip_fields = HashMap::new();
        skip_fields.insert("CState".to_string(), vec!["ghost_data".to_string()]);

        let cfg = TypeGenConfig {
            registry: &registry,
            naming: &naming,
            remapping: &remapping,
            custom_imports: &[],
            validity_predicate_name: "well_formed",
            view_overrides: &HashMap::new(),
            extra_fields: &HashMap::new(),
            clone_strategy: &HashMap::new(),
            skip_types: &[],
            re_exports: &[],
            extra_type_aliases: &HashMap::new(),
            custom_derives: &HashMap::new(),
            skip_fields: &skip_fields,
            skip_validity_types: &[],
            skip_view_types: &[],
            generate_clone_up_to_view_simple: false,
            generate_unreachable_value_helper: false,
            manual_code: None,
            arc_wrap_types: &[],
            arc_wrap_fields: &HashMap::new(),
        };

        let result = generate_all_types_full(&cfg);

        assert!(
            result.code.contains("count: i64"),
            "Should include non-skipped field: {}",
            result.code
        );
        assert!(
            !result.code.contains("ghost_data"),
            "Should skip ghost_data everywhere: {}",
            result.code
        );
    }

    #[test]
    fn test_manual_code_injected_before_verus_close() {
        let registry = TypeRegistry::new();
        let naming = make_config();
        let remapping = HashMap::new();
        let manual = "pub open spec fn ManualHelper() -> bool { true }";

        let cfg = TypeGenConfig {
            registry: &registry,
            naming: &naming,
            remapping: &remapping,
            custom_imports: &[],
            validity_predicate_name: "well_formed",
            view_overrides: &HashMap::new(),
            extra_fields: &HashMap::new(),
            clone_strategy: &HashMap::new(),
            skip_types: &[],
            re_exports: &[],
            extra_type_aliases: &HashMap::new(),
            custom_derives: &HashMap::new(),
            skip_fields: &HashMap::new(),
            skip_validity_types: &[],
            skip_view_types: &[],
            generate_clone_up_to_view_simple: false,
            generate_unreachable_value_helper: false,
            manual_code: Some(manual),
            arc_wrap_types: &[],
            arc_wrap_fields: &HashMap::new(),
        };

        let result = generate_all_types_full(&cfg);
        let manual_pos = result.code.find(manual).expect("manual snippet missing");
        let close_pos = result
            .code
            .find("} // verus!")
            .expect("verus close marker missing");

        assert!(
            manual_pos < close_pos,
            "manual snippet should be inside verus block: {}",
            result.code
        );
    }

    #[test]
    fn test_generate_unreachable_value_helper_enabled() {
        let registry = TypeRegistry::new();
        let naming = make_config();
        let remapping = HashMap::new();

        let cfg = TypeGenConfig {
            registry: &registry,
            naming: &naming,
            remapping: &remapping,
            custom_imports: &[],
            validity_predicate_name: "well_formed",
            view_overrides: &HashMap::new(),
            extra_fields: &HashMap::new(),
            clone_strategy: &HashMap::new(),
            skip_types: &[],
            re_exports: &[],
            extra_type_aliases: &HashMap::new(),
            custom_derives: &HashMap::new(),
            skip_fields: &HashMap::new(),
            skip_validity_types: &[],
            skip_view_types: &[],
            generate_clone_up_to_view_simple: false,
            generate_unreachable_value_helper: true,
            manual_code: None,
            arc_wrap_types: &[],
            arc_wrap_fields: &HashMap::new(),
        };

        let result = generate_all_types_full(&cfg);
        assert!(
            result
                .code
                .contains("pub fn unreachable_value<T>() -> (result: T)"),
            "types output should include unreachable_value helper when enabled: {}",
            result.code
        );
    }

    #[test]
    fn test_generate_unreachable_value_helper_not_duplicated_from_manual_code() {
        let registry = TypeRegistry::new();
        let naming = make_config();
        let remapping = HashMap::new();
        let manual = "pub fn unreachable_value<T>() -> (result: T)\n    requires false,\n{ panic!(\"manual unreachable\") }";

        let cfg = TypeGenConfig {
            registry: &registry,
            naming: &naming,
            remapping: &remapping,
            custom_imports: &[],
            validity_predicate_name: "well_formed",
            view_overrides: &HashMap::new(),
            extra_fields: &HashMap::new(),
            clone_strategy: &HashMap::new(),
            skip_types: &[],
            re_exports: &[],
            extra_type_aliases: &HashMap::new(),
            custom_derives: &HashMap::new(),
            skip_fields: &HashMap::new(),
            skip_validity_types: &[],
            skip_view_types: &[],
            generate_clone_up_to_view_simple: false,
            generate_unreachable_value_helper: true,
            manual_code: Some(manual),
            arc_wrap_types: &[],
            arc_wrap_fields: &HashMap::new(),
        };

        let result = generate_all_types_full(&cfg);
        assert_eq!(
            result.code.matches("pub fn unreachable_value<T>()").count(),
            1,
            "helper should not be duplicated when manual code already defines it: {}",
            result.code
        );
    }

    #[test]
    fn test_view_impl_set_int_mapping() {
        // Set<int> in spec -> HashSet<u64> in exec
        // View should generate `.map(|x: u64| x as int)` to convert Set<u64> back to Set<int>
        let config = NamingConfig {
            int_type: "u64".to_string(),
            ..NamingConfig::default()
        };
        let generator = TypeGenerator::new(config);

        let spec = StructDef {
            name: "LState".to_string(),
            generics: Generics::default(),
            fields: vec![
                FieldDef {
                    name: "rm_state".to_string(),
                    ty: Type::Set(Box::new(Type::Int)),
                    is_public: true,
                },
                FieldDef {
                    name: "tm_prepared".to_string(),
                    ty: Type::Set(Box::new(Type::Int)),
                    is_public: true,
                },
            ],
            is_spec: true,
        };

        let result = generator.generate_struct(&spec);

        // View impl should map Set<u64> -> Set<int>
        assert!(
            result
                .code
                .contains("self.rm_state@.map(|x: u64| x as int)"),
            "Should map Set<int> field rm_state with .map(): {}",
            result.code
        );
        assert!(
            result
                .code
                .contains("self.tm_prepared@.map(|x: u64| x as int)"),
            "Should map Set<int> field tm_prepared with .map(): {}",
            result.code
        );
        // Should NOT just use self.field@ without map
        assert!(
            !result.code.contains("rm_state: self.rm_state@,"),
            "Should NOT use bare @ for Set<int> field: {}",
            result.code
        );
    }

    #[test]
    fn test_view_impl_seq_int_mapping() {
        // Seq<int> in spec -> Vec<u64> in exec
        // View should generate `.map(|i: int, x: u64| x as int)`
        let config = NamingConfig {
            int_type: "u64".to_string(),
            ..NamingConfig::default()
        };
        let generator = TypeGenerator::new(config);

        let spec = StructDef {
            name: "LState".to_string(),
            generics: Generics::default(),
            fields: vec![FieldDef {
                name: "values".to_string(),
                ty: Type::Seq(Box::new(Type::Int)),
                is_public: true,
            }],
            is_spec: true,
        };

        let result = generator.generate_struct(&spec);

        assert!(
            result
                .code
                .contains("self.values@.map(|i: int, x: u64| x as int)"),
            "Should map Seq<int> field with .map(|i, x|): {}",
            result.code
        );
    }

    #[test]
    fn test_view_impl_set_nat_mapping() {
        // Set<nat> in spec -> HashSet<u64> in exec
        // nat also needs `as int` conversion since nat maps to u64
        let generator = TypeGenerator::new(make_config());

        let spec = StructDef {
            name: "LState".to_string(),
            generics: Generics::default(),
            fields: vec![FieldDef {
                name: "ids".to_string(),
                ty: Type::Set(Box::new(Type::Nat)),
                is_public: true,
            }],
            is_spec: true,
        };

        let result = generator.generate_struct(&spec);

        assert!(
            result.code.contains("self.ids@.map(|x: u64| x as int)"),
            "Should map Set<nat> field with .map(): {}",
            result.code
        );
    }

    #[test]
    fn test_view_impl_set_named_type_mapping() {
        // Set<NamedType> where NamedType has its own View trait
        // Should generate .map(|x: CEndPoint| x@) to apply View on each element
        let generator = TypeGenerator::new(make_config());

        let spec = StructDef {
            name: "LState".to_string(),
            generics: Generics::default(),
            fields: vec![FieldDef {
                name: "endpoints".to_string(),
                ty: Type::Set(Box::new(Type::Named(Path::single("EndPoint".to_string())))),
                is_public: true,
            }],
            is_spec: true,
        };

        let result = generator.generate_struct(&spec);

        // Should use .map(|x| x@) for Set<NamedType> since inner type has View
        assert!(
            result
                .code
                .contains("self.endpoints@.map(|x: CEndPoint| x@)"),
            "Should map Set<NamedType> with .map(|x| x@): {}",
            result.code
        );
    }

    #[test]
    fn test_view_impl_enum_variant_set_int() {
        // Enum variant with Set<int> field should also get .map() in View
        let config = NamingConfig {
            int_type: "u64".to_string(),
            ..NamingConfig::default()
        };
        let generator = TypeGenerator::new(config);

        let spec = EnumDef {
            name: "LMsg".to_string(),
            generics: Generics::default(),
            variants: vec![
                VariantDef {
                    name: "Prepare".to_string(),
                    fields: VariantFields::Struct(vec![FieldDef {
                        name: "prepared_rms".to_string(),
                        ty: Type::Set(Box::new(Type::Int)),
                        is_public: true,
                    }]),
                },
                VariantDef {
                    name: "Empty".to_string(),
                    fields: VariantFields::Unit,
                },
            ],
            is_spec: true,
        };

        let result = generator.generate_enum(&spec);

        // Variant field should use .map() in View trait
        assert!(
            result.code.contains("prepared_rms@.map(|x: u64| x as int)"),
            "Should map Set<int> in enum variant with .map(): {}",
            result.code
        );
    }

    #[test]
    fn test_collection_view_map_expr_direct() {
        // Directly test the collection_view_map_expr method
        let config = NamingConfig {
            int_type: "u64".to_string(),
            ..NamingConfig::default()
        };
        let generator = TypeGenerator::new(config);

        // Set<int> -> should produce map expression
        let set_int = Type::Set(Box::new(Type::Int));
        assert_eq!(
            generator.collection_view_map_expr(&set_int, "self.field"),
            Some("self.field@.map(|x: u64| x as int)".to_string())
        );

        // Seq<int> -> should produce map expression with index
        let seq_int = Type::Seq(Box::new(Type::Int));
        assert_eq!(
            generator.collection_view_map_expr(&seq_int, "self.field"),
            Some("self.field@.map(|i: int, x: u64| x as int)".to_string())
        );

        // Set<nat> -> should also produce map expression
        let set_nat = Type::Set(Box::new(Type::Nat));
        assert_eq!(
            generator.collection_view_map_expr(&set_nat, "self.ids"),
            Some("self.ids@.map(|x: u64| x as int)".to_string())
        );

        // Set<NamedType> -> should generate .map(|x| x@) for View conversion
        let set_named = Type::Set(Box::new(Type::Named(Path::single("Foo".to_string()))));
        assert_eq!(
            generator.collection_view_map_expr(&set_named, "self.field"),
            Some("self.field@.map(|x: CFoo| x@)".to_string())
        );

        // Set<u64> (Rust primitive as Named) -> should return None (no conversion needed)
        let set_u64 = Type::Set(Box::new(Type::Named(Path::single("u64".to_string()))));
        assert_eq!(
            generator.collection_view_map_expr(&set_u64, "self.field"),
            None
        );

        // Map<int, int> -> should return None (Map not handled yet)
        let map_int_int = Type::Map(Box::new(Type::Int), Box::new(Type::Int));
        assert_eq!(
            generator.collection_view_map_expr(&map_int_int, "self.field"),
            None
        );

        // Bool -> should return None
        assert_eq!(
            generator.collection_view_map_expr(&Type::Bool, "self.field"),
            None
        );
    }

    #[test]
    fn test_generate_derives_default_clone() {
        let generator = TypeGenerator::new(make_config());
        let mut code = String::new();
        let strat = generator.generate_derives("CNode", &mut code);
        assert_eq!(strat, "derive");
        assert!(
            code.contains("#[derive(Clone)]"),
            "Default strategy should add Clone derive: {}",
            code
        );
    }

    #[test]
    fn test_generate_derives_external_body() {
        let mut generator = TypeGenerator::new(make_config());
        let mut strats = HashMap::new();
        strats.insert("CNode".to_string(), "external_body".to_string());
        generator.clone_strategy = strats;

        let mut code = String::new();
        let strat = generator.generate_derives("CNode", &mut code);
        assert_eq!(strat, "external_body");
        assert!(
            !code.contains("Clone"),
            "external_body strategy should NOT add Clone derive: {}",
            code
        );
    }

    #[test]
    fn test_generate_external_body_clone_output() {
        let generator = TypeGenerator::new(make_config());
        let mut code = String::new();
        generator.generate_external_body_clone("CNode", &[], &mut code);
        assert!(
            code.contains("impl Clone for CNode"),
            "Should generate Clone impl"
        );
        assert!(
            code.contains("#[verifier(external_body)]"),
            "Should mark fn as external_body"
        );
        assert!(
            code.contains("res@ == self@"),
            "Should have view preservation ensure: {}",
            code
        );
        assert!(
            code.contains("res.well_formed() == self.well_formed()"),
            "Should have validity preservation ensure: {}",
            code
        );
        // With no fields, should still contain unimplemented!()
        assert!(
            code.contains("unimplemented!()"),
            "Empty fields should produce unimplemented!(): {}",
            code
        );
    }

    #[test]
    fn test_generate_external_body_clone_with_fields() {
        let generator = TypeGenerator::new(make_config());
        let fields = [
            FieldDef {
                name: "term".to_string(),
                ty: Type::Int,
                is_public: true,
            },
            FieldDef {
                name: "log".to_string(),
                ty: Type::Seq(Box::new(Type::Int)),
                is_public: true,
            },
            FieldDef {
                name: "active".to_string(),
                ty: Type::Bool,
                is_public: true,
            },
            FieldDef {
                name: "role".to_string(),
                ty: Type::Named(Path::single("CServerRole".to_string())),
                is_public: true,
            },
        ];
        let field_refs: Vec<&FieldDef> = fields.iter().collect();
        let mut code = String::new();
        generator.generate_external_body_clone("CState", &field_refs, &mut code);
        assert!(
            code.contains("term: self.term,"),
            "Copy field should not use .clone(): {}",
            code
        );
        assert!(
            code.contains("log: self.log.clone(),"),
            "Non-copy field should use .clone(): {}",
            code
        );
        assert!(
            code.contains("active: self.active,"),
            "Bool field should not use .clone(): {}",
            code
        );
        assert!(
            !code.contains("unimplemented!()"),
            "With fields, should not contain unimplemented!(): {}",
            code
        );
        // Copy/scalar fields should have concrete ensures
        assert!(
            code.contains("res.term == self.term,"),
            "Copy field should have concrete ensures: {}",
            code
        );
        assert!(
            code.contains("res.active == self.active,"),
            "Bool field should have concrete ensures: {}",
            code
        );
        // Named types (enums) should have concrete ensures (Verus supports spec equality)
        assert!(
            code.contains("res.role == self.role,"),
            "Named type field should have concrete ensures: {}",
            code
        );
        // Non-copy container fields (like Seq) should NOT have concrete ensures
        assert!(
            !code.contains("res.log == self.log,"),
            "Non-copy field should not have concrete ensures: {}",
            code
        );
    }

    #[test]
    fn test_struct_and_enum_use_same_derive_logic() {
        // Verify struct and enum produce identical derive attributes for same config
        let mut generator = TypeGenerator::new(make_config());
        let mut strats = HashMap::new();
        strats.insert("CNode".to_string(), "external_body".to_string());
        generator.clone_strategy = strats;

        let spec_struct = StructDef {
            name: "LNode".to_string(),
            generics: Generics::default(),
            fields: vec![FieldDef {
                name: "id".to_string(),
                ty: Type::Int,
                is_public: true,
            }],
            is_spec: true,
        };
        let spec_enum = EnumDef {
            name: "LNode".to_string(),
            generics: Generics::default(),
            variants: vec![VariantDef {
                name: "NodeA".to_string(),
                fields: VariantFields::Unit,
            }],
            is_spec: true,
        };

        let struct_code = generator.generate_struct(&spec_struct).code;
        let enum_code = generator.generate_enum(&spec_enum).code;

        // Both should have external_body Clone impl
        assert!(
            struct_code.contains("#[verifier(external_body)]"),
            "Struct should have external_body clone: {}",
            struct_code
        );
        assert!(
            enum_code.contains("#[verifier(external_body)]"),
            "Enum should have external_body clone: {}",
            enum_code
        );
        // Neither should have #[derive(Clone)]
        assert!(
            !struct_code.contains("#[derive(Clone)]"),
            "Struct should not derive Clone with external_body"
        );
        assert!(
            !enum_code.contains("#[derive(Clone)]"),
            "Enum should not derive Clone with external_body"
        );
    }

    #[test]
    fn test_arc_wrap_types_wraps_non_scalar_fields() {
        let mut generator = TypeGenerator::new(make_config());
        generator.set_arc_wrap_types(
            vec!["CReplica".to_string()].into_iter().collect(),
        );

        let spec = StructDef {
            name: "LReplica".to_string(),
            generics: Generics::default(),
            fields: vec![
                FieldDef {
                    name: "proposer".to_string(),
                    ty: Type::Named(Path::single("Proposer".to_string())),
                    is_public: true,
                },
                FieldDef {
                    name: "acceptor".to_string(),
                    ty: Type::Named(Path::single("Acceptor".to_string())),
                    is_public: true,
                },
                FieldDef {
                    name: "next_heartbeat".to_string(),
                    ty: Type::Nat,
                    is_public: true,
                },
                FieldDef {
                    name: "active".to_string(),
                    ty: Type::Bool,
                    is_public: true,
                },
            ],
            is_spec: true,
        };

        let result = generator.generate_struct(&spec);

        // Non-scalar fields should be Arc-wrapped
        assert!(
            result.code.contains("pub proposer: Arc<CProposer>"),
            "Named type should be Arc-wrapped: {}",
            result.code
        );
        assert!(
            result.code.contains("pub acceptor: Arc<CAcceptor>"),
            "Named type should be Arc-wrapped: {}",
            result.code
        );
        // Scalar fields should NOT be Arc-wrapped
        assert!(
            result.code.contains("pub next_heartbeat: u64"),
            "Nat (u64) should not be Arc-wrapped: {}",
            result.code
        );
        assert!(
            result.code.contains("pub active: bool"),
            "Bool should not be Arc-wrapped: {}",
            result.code
        );
    }

    #[test]
    fn test_arc_wrap_types_does_not_affect_unlisted_structs() {
        let mut generator = TypeGenerator::new(make_config());
        generator.set_arc_wrap_types(
            vec!["CReplica".to_string()].into_iter().collect(),
        );

        // CAcceptor is NOT in arc_wrap_types
        let spec = StructDef {
            name: "LAcceptor".to_string(),
            generics: Generics::default(),
            fields: vec![FieldDef {
                name: "votes".to_string(),
                ty: Type::Named(Path::single("Votes".to_string())),
                is_public: true,
            }],
            is_spec: true,
        };

        let result = generator.generate_struct(&spec);

        // Should NOT be Arc-wrapped since CAcceptor is not in the list
        assert!(
            result.code.contains("pub votes: CVotes"),
            "Unlisted struct should not have Arc-wrapped fields: {}",
            result.code
        );
        assert!(
            !result.code.contains("Arc<CVotes>"),
            "Unlisted struct should not have Arc<> fields: {}",
            result.code
        );
    }
}
