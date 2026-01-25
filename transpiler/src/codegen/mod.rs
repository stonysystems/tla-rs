//! Code generation for exec types and implementations.
//!
//! This module generates:
//! - Concrete (exec) type definitions from spec types
//! - `well_formed()` validity predicates
//! - `View` trait implementations
//! - Clone implementations
//! - Executable code from quantifier templates

pub mod template_codegen;

pub use template_codegen::TemplateCodeGenerator;

use std::collections::HashMap;

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
}

impl TypeGenerator {
    /// Create a new type generator
    pub fn new(config: NamingConfig) -> Self {
        Self {
            config,
            remapping: HashMap::new(),
            indent: "    ".to_string(),
        }
    }

    /// Create a new type generator with remapping table
    pub fn with_remapping(config: NamingConfig, remapping: HashMap<String, String>) -> Self {
        Self {
            config,
            remapping,
            indent: "    ".to_string(),
        }
    }

    /// Generate an exec struct from a spec struct
    pub fn generate_struct(&self, spec: &StructDef) -> GeneratedCode {
        let mut code = String::new();
        let warnings = Vec::new();

        let exec_name = self.get_exec_type(&spec.name);

        // Generate derive attributes
        code.push_str("#[derive(Clone)]\n");
        // Generate struct definition
        code.push_str(&format!("pub struct {} {{\n", exec_name));
        for field in &spec.fields {
            let exec_type = self.translate_type(&field.ty);
            let vis = if field.is_public { "pub " } else { "" };
            code.push_str(&format!(
                "{}{}{}: {},\n",
                self.indent, vis, field.name, exec_type
            ));
        }
        code.push_str("}\n\n");

        // Generate well_formed predicate
        code.push_str(&self.generate_well_formed_struct(&exec_name, &spec.fields));
        code.push('\n');

        // Generate View implementation
        code.push_str(&self.generate_view_impl(&spec.name, &exec_name, &spec.fields));

        GeneratedCode { code, warnings }
    }

    /// Generate an exec enum from a spec enum
    pub fn generate_enum(&self, spec: &EnumDef) -> GeneratedCode {
        let mut code = String::new();
        let warnings = Vec::new();

        let exec_name = self.get_exec_type(&spec.name);

        // Generate derive attributes
        code.push_str("#[derive(Clone)]\n");
        // Generate enum definition
        code.push_str(&format!("pub enum {} {{\n", exec_name));
        for variant in &spec.variants {
            code.push_str(&self.generate_variant(variant));
        }
        code.push_str("}\n\n");

        // Generate well_formed predicate
        code.push_str(&self.generate_well_formed_enum(&exec_name, &spec.variants));
        code.push('\n');

        // Generate View implementation
        code.push_str(&self.generate_view_impl_enum(&spec.name, &exec_name, &spec.variants));

        GeneratedCode { code, warnings }
    }

    /// Generate a single enum variant
    fn generate_variant(&self, variant: &VariantDef) -> String {
        match &variant.fields {
            VariantFields::Unit => format!("{}{},\n", self.indent, variant.name),
            VariantFields::Tuple(types) => {
                let type_strs: Vec<_> = types.iter().map(|t| self.translate_type(t)).collect();
                format!(
                    "{}{}({}),\n",
                    self.indent,
                    variant.name,
                    type_strs.join(", ")
                )
            }
            VariantFields::Struct(fields) => {
                let mut s = format!("{}{} {{\n", self.indent, variant.name);
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

    /// Generate well_formed predicate for a struct
    fn generate_well_formed_struct(&self, exec_name: &str, fields: &[FieldDef]) -> String {
        let mut code = format!("impl {} {{\n", exec_name);
        code.push_str(&format!(
            "{}pub open spec fn well_formed(&self) -> bool {{\n",
            self.indent
        ));

        // Collect fields that need well_formed checks
        let fields_needing_check: Vec<_> = fields
            .iter()
            .filter(|f| self.needs_well_formed(&f.ty))
            .collect();

        if fields_needing_check.is_empty() {
            // All fields are primitives, just return true
            code.push_str(&format!("{}{}true\n", self.indent, self.indent));
        } else {
            // Generate conjunction of well_formed calls
            for (i, field) in fields_needing_check.iter().enumerate() {
                let prefix = if i == 0 { "    " } else { "&&& " };
                code.push_str(&format!(
                    "{}{}{}self.{}.well_formed()\n",
                    self.indent, self.indent, prefix, field.name
                ));
            }
        }

        code.push_str(&format!("{}}}\n", self.indent));
        code.push_str("}\n");
        code
    }

    /// Generate well_formed predicate for an enum
    fn generate_well_formed_enum(&self, exec_name: &str, variants: &[VariantDef]) -> String {
        let mut code = format!("impl {} {{\n", exec_name);
        code.push_str(&format!(
            "{}pub open spec fn well_formed(&self) -> bool {{\n",
            self.indent
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

    /// Generate a match arm for well_formed check
    fn generate_well_formed_variant_arm(&self, enum_name: &str, variant: &VariantDef) -> String {
        let arm_indent = format!("{}{}{}", self.indent, self.indent, self.indent);

        match &variant.fields {
            VariantFields::Unit => {
                format!("{}{}::{} => true,\n", arm_indent, enum_name, variant.name)
            }
            VariantFields::Tuple(types) => {
                let patterns: Vec<_> = (0..types.len()).map(|i| format!("v{}", i)).collect();
                let pattern = patterns.join(", ");

                let mut checks = Vec::new();
                for (i, ty) in types.iter().enumerate() {
                    if self.needs_well_formed(ty) {
                        checks.push(format!("v{}.well_formed()", i));
                    }
                }

                if checks.is_empty() {
                    format!(
                        "{}{}::{}({}) => true,\n",
                        arm_indent, enum_name, variant.name, pattern
                    )
                } else {
                    format!(
                        "{}{}::{}({}) => {},\n",
                        arm_indent,
                        enum_name,
                        variant.name,
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
                        checks.push(format!("{}.well_formed()", field.name));
                    }
                }

                if checks.is_empty() {
                    format!(
                        "{}{}::{} {{ {} }} => true,\n",
                        arm_indent, enum_name, variant.name, pattern
                    )
                } else {
                    format!(
                        "{}{}::{} {{ {} }} => {},\n",
                        arm_indent,
                        enum_name,
                        variant.name,
                        pattern,
                        checks.join(" && ")
                    )
                }
            }
        }
    }

    /// Generate View trait implementation for a struct
    fn generate_view_impl(&self, spec_name: &str, exec_name: &str, fields: &[FieldDef]) -> String {
        let mut code = format!("impl View for {} {{\n", exec_name);
        code.push_str(&format!("{}type V = {};\n\n", self.indent, spec_name));
        code.push_str(&format!(
            "{}open spec fn view(&self) -> {} {{\n",
            self.indent, spec_name
        ));
        code.push_str(&format!("{}{}{} {{\n", self.indent, self.indent, spec_name));

        for field in fields {
            let view_expr = self.generate_view_field_expr(&field.name, &field.ty);
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

    /// Generate a match arm for View implementation
    fn generate_view_variant_arm(
        &self,
        spec_name: &str,
        exec_name: &str,
        variant: &VariantDef,
    ) -> String {
        let arm_indent = format!("{}{}{}", self.indent, self.indent, self.indent);

        match &variant.fields {
            VariantFields::Unit => {
                format!(
                    "{}{}::{} => {}::{},\n",
                    arm_indent, exec_name, variant.name, spec_name, variant.name
                )
            }
            VariantFields::Tuple(types) => {
                let patterns: Vec<_> = (0..types.len()).map(|i| format!("v{}", i)).collect();
                let pattern = patterns.join(", ");

                let mut views = Vec::new();
                for (i, ty) in types.iter().enumerate() {
                    let view_expr = self.generate_view_variant_field_expr(&format!("v{}", i), ty);
                    views.push(view_expr);
                }

                format!(
                    "{}{}::{}({}) => {}::{}({}),\n",
                    arm_indent,
                    exec_name,
                    variant.name,
                    pattern,
                    spec_name,
                    variant.name,
                    views.join(", ")
                )
            }
            VariantFields::Struct(fields) => {
                let patterns: Vec<_> = fields.iter().map(|f| f.name.clone()).collect();
                let pattern = patterns.join(", ");

                let mut field_views = Vec::new();
                for field in fields {
                    let view_expr = self.generate_view_variant_field_expr(&field.name, &field.ty);
                    field_views.push(format!("{}: {}", field.name, view_expr));
                }

                format!(
                    "{}{}::{} {{ {} }} => {}::{} {{ {} }},\n",
                    arm_indent,
                    exec_name,
                    variant.name,
                    pattern,
                    spec_name,
                    variant.name,
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

    /// Translate a spec type to its exec equivalent
    fn translate_type(&self, ty: &Type) -> String {
        match ty {
            Type::Named(path) => {
                let name = path.last().unwrap_or("Unknown");
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
            Type::Int => "i64".to_string(),
            Type::Nat => "u64".to_string(),
            Type::Unit => "()".to_string(),
        }
    }

    /// Check if a type needs well_formed validation
    fn needs_well_formed(&self, ty: &Type) -> bool {
        needs_well_formed_check(ty)
    }

    /// Check if a type needs the view operator (@)
    fn needs_view(&self, ty: &Type) -> bool {
        needs_view_check(ty)
    }

    /// Generate the expression for a field in a View impl
    /// Handles:
    /// - Types needing @ operator (structs, collections, etc.)
    /// - Types needing `as int` conversion (int, nat -> i64, u64)
    /// - Simple types that need no conversion
    fn generate_view_field_expr(&self, field_name: &str, ty: &Type) -> String {
        if self.needs_view(ty) {
            format!("self.{}@", field_name)
        } else if needs_as_int_conversion(ty) {
            format!("self.{} as int", field_name)
        } else {
            format!("self.{}", field_name)
        }
    }

    /// Generate the expression for a variant field in a View impl
    /// Similar to generate_view_field_expr but for enum variant bindings
    /// (no `self.` prefix, uses `*` for dereferencing)
    fn generate_view_variant_field_expr(&self, binding_name: &str, ty: &Type) -> String {
        if self.needs_view(ty) {
            format!("{}@", binding_name)
        } else if needs_as_int_conversion(ty) {
            format!("*{} as int", binding_name)
        } else {
            format!("*{}", binding_name)
        }
    }
}

/// Check if a type needs well_formed validation (standalone function for recursion)
fn needs_well_formed_check(ty: &Type) -> bool {
    match ty {
        Type::Bool | Type::Int | Type::Nat | Type::Unit => false,
        Type::Named(_) | Type::Generic(_, _) => true,
        Type::Seq(_) | Type::Set(_) | Type::Map(_, _) => true,
        Type::Tuple(types) => types.iter().any(needs_well_formed_check),
        Type::Reference { ty, .. } => needs_well_formed_check(ty),
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
    generate_all_types_with_options(registry, config, remapping, &[])
}

/// Generate all types from a type registry with custom remapping and imports
pub fn generate_all_types_with_options(
    registry: &TypeRegistry,
    config: &NamingConfig,
    remapping: &HashMap<String, String>,
    custom_imports: &[String],
) -> GeneratedCode {
    let generator = TypeGenerator::with_remapping(config.clone(), remapping.clone());
    let mut all_code = String::new();
    let mut all_warnings = Vec::new();

    // Header
    all_code.push_str("// Auto-generated concrete types by verus-transpiler\n");
    all_code.push_str("// DO NOT EDIT MANUALLY\n\n");

    // Custom imports
    if custom_imports.is_empty() {
        all_code.push_str("use vstd::prelude::*;\n\n");
    } else {
        for import in custom_imports {
            all_code.push_str(import);
            if !import.ends_with('\n') {
                all_code.push('\n');
            }
        }
        all_code.push('\n');
    }

    all_code.push_str("verus! {\n\n");

    // Generate structs
    for struct_def in registry.structs.values() {
        if struct_def.is_spec {
            let generated = generator.generate_struct(struct_def);
            all_code.push_str(&generated.code);
            all_code.push('\n');
            all_warnings.extend(generated.warnings);
        }
    }

    // Generate enums
    for enum_def in registry.enums.values() {
        if enum_def.is_spec {
            let generated = generator.generate_enum(enum_def);
            all_code.push_str(&generated.code);
            all_code.push('\n');
            all_warnings.extend(generated.warnings);
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

        let generator = TypeGenerator::with_remapping(make_config(), remapping);

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

        let generator = TypeGenerator::with_remapping(make_config(), remapping);

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
}
