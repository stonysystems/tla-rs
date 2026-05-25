//! FieldSchema registry: maps struct/enum type names to ordered field layouts.
//!
//! Each `FieldLayout` stores the canonical field order for a type and provides
//! O(1) `name → index` lookup via a `HashMap<Symbol, usize>`. This will be used
//! by `NamedFields` in Phase 38.22.2.b.iii to replace `Vec<(Symbol, RuntimeValue)>`
//! with a flat `Vec<RuntimeValue>` indexed by field position.

use crate::modelcheck::symbol::Symbol;
use crate::spec_analyzer::SpecSchema;
use std::collections::HashMap;

/// Ordered field layout for a single struct or enum variant.
///
/// Fields are stored in declaration order (matching the `StructDef.fields` /
/// `VariantFields::Struct` order from the spec parser). The `index` map
/// provides O(1) name-to-position lookup.
#[derive(Debug, Clone)]
pub struct FieldLayout {
    /// Field names in declaration order.
    pub fields: Vec<Symbol>,
    /// name → position index.
    pub index: HashMap<Symbol, usize>,
}

impl FieldLayout {
    /// Build a layout from an ordered sequence of field names.
    pub fn from_names<I: IntoIterator<Item = Symbol>>(names: I) -> Self {
        let fields: Vec<Symbol> = names.into_iter().collect();
        let index: HashMap<Symbol, usize> =
            fields.iter().enumerate().map(|(i, s)| (*s, i)).collect();
        Self { fields, index }
    }

    /// Look up the index of a field by name. Returns `None` if not found.
    pub fn field_index(&self, name: &Symbol) -> Option<usize> {
        self.index.get(name).copied()
    }

    /// Number of fields.
    pub fn len(&self) -> usize {
        self.fields.len()
    }

    /// Whether this layout has no fields.
    pub fn is_empty(&self) -> bool {
        self.fields.is_empty()
    }
}

/// Registry mapping type names to their field layouts.
///
/// - Structs are keyed by type name (e.g., `"LState"`, `"LConstants"`).
/// - Enum variants are keyed by `"TypeName::VariantName"` (e.g.,
///   `"LMessage::Request"`).
#[derive(Debug, Clone, Default)]
pub struct FieldSchemaRegistry {
    layouts: HashMap<String, FieldLayout>,
}

impl FieldSchemaRegistry {
    pub fn new() -> Self {
        Self::default()
    }

    /// Build the registry from a `SpecSchema`.
    pub fn from_spec_schema(schema: &SpecSchema) -> Self {
        let mut reg = Self::new();

        // Register struct field layouts
        for (name, struct_def) in &schema.structs {
            let syms = struct_def.fields.iter().map(|f| Symbol::intern(&f.name));
            reg.layouts
                .insert(name.clone(), FieldLayout::from_names(syms));
        }

        // Register enum variant field layouts
        for (name, enum_def) in &schema.enums {
            for variant in &enum_def.variants {
                use crate::types::VariantFields;
                if let VariantFields::Struct(fields) = &variant.fields {
                    let key = format!("{}::{}", name, variant.name);
                    let syms = fields.iter().map(|f| Symbol::intern(&f.name));
                    reg.layouts.insert(key, FieldLayout::from_names(syms));
                }
            }
        }

        reg
    }

    /// Look up the field layout for a struct type.
    pub fn get_struct(&self, ty: &str) -> Option<&FieldLayout> {
        self.layouts.get(ty)
    }

    /// Look up the field layout for an enum variant.
    pub fn get_variant(&self, ty: &str, variant: &str) -> Option<&FieldLayout> {
        // Try "Type::Variant" key
        let key = format!("{}::{}", ty, variant);
        self.layouts.get(&key)
    }

    /// Number of registered layouts.
    pub fn len(&self) -> usize {
        self.layouts.len()
    }

    /// Whether the registry is empty.
    pub fn is_empty(&self) -> bool {
        self.layouts.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Generics, Path, Type};
    use crate::spec_analyzer::SpecSchema;
    use crate::types::{EnumDef, FieldDef, StructDef, VariantDef, VariantFields};

    fn mk_field(name: &str) -> FieldDef {
        FieldDef {
            name: name.to_string(),
            ty: Type::Named(Path::single("int".to_string())),
            is_public: true,
        }
    }

    #[test]
    fn test_struct_layout() {
        let mut schema = SpecSchema::new();
        schema.structs.insert(
            "LState".to_string(),
            StructDef {
                name: "LState".to_string(),
                generics: Generics::default(),
                fields: vec![mk_field("term"), mk_field("log"), mk_field("voted_for")],
                is_spec: true,
            },
        );

        let reg = FieldSchemaRegistry::from_spec_schema(&schema);
        let layout = reg.get_struct("LState").unwrap();

        assert_eq!(layout.len(), 3);
        assert_eq!(layout.field_index(&Symbol::intern("term")), Some(0));
        assert_eq!(layout.field_index(&Symbol::intern("log")), Some(1));
        assert_eq!(layout.field_index(&Symbol::intern("voted_for")), Some(2));
        assert_eq!(layout.field_index(&Symbol::intern("nonexistent")), None);
    }

    #[test]
    fn test_enum_variant_layout() {
        let mut schema = SpecSchema::new();
        schema.enums.insert(
            "LMessage".to_string(),
            EnumDef {
                name: "LMessage".to_string(),
                generics: Generics::default(),
                variants: vec![
                    VariantDef {
                        name: "Request".to_string(),
                        fields: VariantFields::Struct(vec![
                            mk_field("sender"),
                            mk_field("payload"),
                        ]),
                    },
                    VariantDef {
                        name: "Ack".to_string(),
                        fields: VariantFields::Unit,
                    },
                ],
                is_spec: true,
            },
        );

        let reg = FieldSchemaRegistry::from_spec_schema(&schema);

        // Struct variant should be registered
        let layout = reg.get_variant("LMessage", "Request").unwrap();
        assert_eq!(layout.len(), 2);
        assert_eq!(layout.field_index(&Symbol::intern("sender")), Some(0));
        assert_eq!(layout.field_index(&Symbol::intern("payload")), Some(1));

        // Unit variant should not be registered
        assert!(reg.get_variant("LMessage", "Ack").is_none());
    }

    #[test]
    fn test_empty_schema() {
        let schema = SpecSchema::new();
        let reg = FieldSchemaRegistry::from_spec_schema(&schema);
        assert!(reg.is_empty());
    }
}
