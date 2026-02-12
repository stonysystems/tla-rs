//! Type mapping utilities for Verus to TLA+ conversion.
//!
//! This module handles the mapping between Verus/Rust types and TLA+ types.

use std::collections::HashMap;

/// Represents a Verus type that can be mapped to TLA+.
#[derive(Debug, Clone, PartialEq)]
pub enum VerusType {
    /// Primitive integer type
    Int,
    /// Natural numbers (non-negative integers)
    Nat,
    /// Boolean type
    Bool,
    /// Sequence type: Seq<T>
    Seq(Box<VerusType>),
    /// Set type: Set<T>
    Set(Box<VerusType>),
    /// Map type: Map<K, V>
    Map(Box<VerusType>, Box<VerusType>),
    /// Option type: Option<T>
    Option(Box<VerusType>),
    /// Tuple type: (T1, T2, ...)
    Tuple(Vec<VerusType>),
    /// Named struct or enum type
    Named(String),
    /// Generic type parameter
    TypeParam(String),
    /// Unit type
    Unit,
    /// Unknown or unsupported type
    Unknown(String),
}

impl VerusType {
    /// Parse a Verus type from a string representation.
    pub fn parse(type_str: &str) -> Self {
        let type_str = type_str.trim();

        // Handle primitives
        match type_str {
            "int" => return VerusType::Int,
            "nat" => return VerusType::Nat,
            "bool" => return VerusType::Bool,
            "()" => return VerusType::Unit,
            _ => {}
        }

        // Handle generic types
        if let Some(inner) = type_str
            .strip_prefix("Seq<")
            .and_then(|s| s.strip_suffix('>'))
        {
            return VerusType::Seq(Box::new(VerusType::parse(inner)));
        }

        if let Some(inner) = type_str
            .strip_prefix("Set<")
            .and_then(|s| s.strip_suffix('>'))
        {
            return VerusType::Set(Box::new(VerusType::parse(inner)));
        }

        if let Some(inner) = type_str
            .strip_prefix("Option<")
            .and_then(|s| s.strip_suffix('>'))
        {
            return VerusType::Option(Box::new(VerusType::parse(inner)));
        }

        if let Some(inner) = type_str
            .strip_prefix("Map<")
            .and_then(|s| s.strip_suffix('>'))
        {
            // Parse Map<K, V>
            if let Some((key, value)) = Self::split_generic_args(inner) {
                return VerusType::Map(
                    Box::new(VerusType::parse(key)),
                    Box::new(VerusType::parse(value)),
                );
            }
        }

        // Handle tuples
        if type_str.starts_with('(') && type_str.ends_with(')') {
            let inner = &type_str[1..type_str.len() - 1];
            let parts = Self::split_tuple_parts(inner);
            if parts.len() > 1 {
                return VerusType::Tuple(parts.into_iter().map(VerusType::parse).collect());
            }
        }

        // Handle single uppercase letters as type parameters
        if type_str.len() == 1 && type_str.chars().next().unwrap().is_uppercase() {
            return VerusType::TypeParam(type_str.to_string());
        }

        // Named type (struct, enum, or alias)
        if type_str
            .chars()
            .next()
            .map(|c| c.is_alphabetic())
            .unwrap_or(false)
        {
            return VerusType::Named(type_str.to_string());
        }

        VerusType::Unknown(type_str.to_string())
    }

    /// Split generic arguments at the top level comma.
    fn split_generic_args(s: &str) -> Option<(&str, &str)> {
        let mut depth = 0;
        for (i, c) in s.char_indices() {
            match c {
                '<' => depth += 1,
                '>' => depth -= 1,
                ',' if depth == 0 => {
                    return Some((s[..i].trim(), s[i + 1..].trim()));
                }
                _ => {}
            }
        }
        None
    }

    /// Split tuple parts at top-level commas.
    fn split_tuple_parts(s: &str) -> Vec<&str> {
        let mut parts = Vec::new();
        let mut depth = 0;
        let mut start = 0;

        for (i, c) in s.char_indices() {
            match c {
                '<' | '(' => depth += 1,
                '>' | ')' => depth -= 1,
                ',' if depth == 0 => {
                    parts.push(s[start..i].trim());
                    start = i + 1;
                }
                _ => {}
            }
        }
        parts.push(s[start..].trim());
        parts
    }

    /// Check if this type is a primitive TLA+ type.
    pub fn is_primitive(&self) -> bool {
        matches!(
            self,
            VerusType::Int | VerusType::Nat | VerusType::Bool | VerusType::Unit
        )
    }

    /// Get the TLA+ type name for this type.
    pub fn to_tla_type(&self) -> String {
        match self {
            VerusType::Int => "Int".to_string(),
            VerusType::Nat => "Nat".to_string(),
            VerusType::Bool => "BOOLEAN".to_string(),
            VerusType::Seq(inner) => format!("Seq({})", inner.to_tla_type()),
            VerusType::Set(inner) => format!("SUBSET {}", inner.to_tla_type()),
            VerusType::Map(key, value) => {
                format!("[{} -> {}]", key.to_tla_type(), value.to_tla_type())
            }
            VerusType::Option(inner) => {
                // Option<T> becomes T ∪ {None}
                format!("({} \\cup {{None}})", inner.to_tla_type())
            }
            VerusType::Tuple(parts) => {
                let parts_str: Vec<String> = parts.iter().map(|p| p.to_tla_type()).collect();
                format!("({} \\X {})", parts_str[0], parts_str[1..].join(" \\X "))
            }
            VerusType::Named(name) => {
                // Strip L prefix for spec types
                if let Some(stripped) = name.strip_prefix('L') {
                    stripped.to_string()
                } else {
                    name.clone()
                }
            }
            VerusType::TypeParam(name) => name.clone(),
            VerusType::Unit => "{}".to_string(), // Empty set/record
            VerusType::Unknown(s) => format!("Unknown({})", s),
        }
    }
}

/// Type mapper for converting between Verus and TLA+ types.
#[derive(Debug, Clone)]
pub struct TypeMapper {
    /// Custom type mappings
    custom_mappings: HashMap<String, String>,
    /// Record type definitions (struct name -> field types)
    record_types: HashMap<String, Vec<(String, VerusType)>>,
    /// Enum type definitions (enum name -> variant names)
    enum_types: HashMap<String, Vec<String>>,
}

impl TypeMapper {
    /// Create a new type mapper with default settings.
    pub fn new() -> Self {
        Self {
            custom_mappings: HashMap::new(),
            record_types: HashMap::new(),
            enum_types: HashMap::new(),
        }
    }

    /// Add a custom type mapping.
    pub fn add_mapping(&mut self, verus_type: &str, tla_type: &str) {
        self.custom_mappings
            .insert(verus_type.to_string(), tla_type.to_string());
    }

    /// Register a record (struct) type.
    pub fn register_record(&mut self, name: &str, fields: Vec<(String, VerusType)>) {
        self.record_types.insert(name.to_string(), fields);
    }

    /// Register an enum type.
    pub fn register_enum(&mut self, name: &str, variants: Vec<String>) {
        self.enum_types.insert(name.to_string(), variants);
    }

    /// Map a Verus type to a TLA+ type string.
    pub fn map_type(&self, verus_type: &VerusType) -> String {
        // Check custom mappings first
        if let VerusType::Named(name) = verus_type {
            if let Some(tla_type) = self.custom_mappings.get(name) {
                return tla_type.clone();
            }
        }

        verus_type.to_tla_type()
    }

    /// Generate a TLA+ record type definition.
    pub fn generate_record_type_def(&self, name: &str) -> Option<String> {
        self.record_types.get(name).map(|fields| {
            let field_defs: Vec<String> = fields
                .iter()
                .map(|(fname, ftype)| format!("{}: {}", fname, self.map_type(ftype)))
                .collect();
            format!("{} == [{}]", name, field_defs.join(", "))
        })
    }

    /// Generate a TLA+ enum type definition.
    pub fn generate_enum_type_def(&self, name: &str) -> Option<String> {
        self.enum_types.get(name).map(|variants| {
            let variant_set = variants.join(", ");
            format!("{} == {{{}}}", name, variant_set)
        })
    }

    /// Get all registered record types.
    pub fn record_types(&self) -> &HashMap<String, Vec<(String, VerusType)>> {
        &self.record_types
    }

    /// Get all registered enum types.
    pub fn enum_types(&self) -> &HashMap<String, Vec<String>> {
        &self.enum_types
    }
}

impl Default for TypeMapper {
    fn default() -> Self {
        Self::new()
    }
}

/// Mapping for common Verus operators to TLA+ operators.
#[derive(Debug, Clone, Copy)]
pub enum OperatorMapping {
    /// Direct mapping (same syntax)
    Direct,
    /// Different syntax
    Mapped(&'static str),
    /// Function call in TLA+
    Function(&'static str),
    /// Not directly translatable
    Unsupported,
}

/// Get the TLA+ mapping for a Verus operator/method.
pub fn map_operator(op: &str) -> OperatorMapping {
    match op {
        // Logical operators
        "&&" | "&&&" => OperatorMapping::Mapped("/\\"),
        "||" | "|||" => OperatorMapping::Mapped("\\/"),
        "!" => OperatorMapping::Mapped("~"),
        "==>" => OperatorMapping::Mapped("=>"),
        "<==>" => OperatorMapping::Mapped("<=>"),

        // Comparison operators
        "==" => OperatorMapping::Mapped("="),
        "!=" => OperatorMapping::Mapped("#"),
        "<" => OperatorMapping::Direct,
        ">" => OperatorMapping::Direct,
        "<=" => OperatorMapping::Direct,
        ">=" => OperatorMapping::Direct,

        // Arithmetic operators
        "+" => OperatorMapping::Direct,
        "-" => OperatorMapping::Direct,
        "*" => OperatorMapping::Direct,
        "/" => OperatorMapping::Mapped("\\div"),
        "%" => OperatorMapping::Mapped("%"),

        // Sequence methods
        "len" => OperatorMapping::Function("Len"),
        "push" => OperatorMapping::Function("Append"),
        "first" => OperatorMapping::Function("Head"),
        "last" => OperatorMapping::Function("Last"),
        "subrange" => OperatorMapping::Function("SubSeq"),

        // Set methods
        "contains" => OperatorMapping::Mapped("\\in"),
        "insert" => OperatorMapping::Mapped("\\cup"),
        "remove" => OperatorMapping::Mapped("\\"),
        "union" => OperatorMapping::Mapped("\\cup"),
        "intersect" => OperatorMapping::Mapped("\\cap"),
        "subset_of" => OperatorMapping::Mapped("\\subseteq"),

        // Map methods
        "index" | "get" => OperatorMapping::Direct, // f[x]
        "contains_key" => OperatorMapping::Mapped("\\in DOMAIN"),
        "dom" => OperatorMapping::Function("DOMAIN"),

        // Quantifiers
        "forall" => OperatorMapping::Mapped("\\A"),
        "exists" => OperatorMapping::Mapped("\\E"),
        "choose" => OperatorMapping::Mapped("CHOOSE"),

        _ => OperatorMapping::Unsupported,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_primitives() {
        assert_eq!(VerusType::parse("int"), VerusType::Int);
        assert_eq!(VerusType::parse("nat"), VerusType::Nat);
        assert_eq!(VerusType::parse("bool"), VerusType::Bool);
        assert_eq!(VerusType::parse("()"), VerusType::Unit);
    }

    #[test]
    fn test_parse_generics() {
        assert_eq!(
            VerusType::parse("Seq<int>"),
            VerusType::Seq(Box::new(VerusType::Int))
        );
        assert_eq!(
            VerusType::parse("Set<nat>"),
            VerusType::Set(Box::new(VerusType::Nat))
        );
        assert_eq!(
            VerusType::parse("Option<bool>"),
            VerusType::Option(Box::new(VerusType::Bool))
        );
    }

    #[test]
    fn test_parse_map() {
        assert_eq!(
            VerusType::parse("Map<int, bool>"),
            VerusType::Map(Box::new(VerusType::Int), Box::new(VerusType::Bool))
        );
    }

    #[test]
    fn test_parse_tuple() {
        assert_eq!(
            VerusType::parse("(int, bool)"),
            VerusType::Tuple(vec![VerusType::Int, VerusType::Bool])
        );
    }

    #[test]
    fn test_parse_named() {
        assert_eq!(
            VerusType::parse("LReplica"),
            VerusType::Named("LReplica".to_string())
        );
    }

    #[test]
    fn test_to_tla_type() {
        assert_eq!(VerusType::Int.to_tla_type(), "Int");
        assert_eq!(VerusType::Nat.to_tla_type(), "Nat");
        assert_eq!(VerusType::Bool.to_tla_type(), "BOOLEAN");

        assert_eq!(
            VerusType::Seq(Box::new(VerusType::Int)).to_tla_type(),
            "Seq(Int)"
        );

        assert_eq!(
            VerusType::Map(Box::new(VerusType::Int), Box::new(VerusType::Bool)).to_tla_type(),
            "[Int -> BOOLEAN]"
        );

        assert_eq!(
            VerusType::Named("LReplica".to_string()).to_tla_type(),
            "Replica"
        );
    }

    #[test]
    fn test_type_mapper() {
        let mut mapper = TypeMapper::new();

        mapper.register_record(
            "Ballot",
            vec![
                ("seqno".to_string(), VerusType::Nat),
                ("proposer_id".to_string(), VerusType::Nat),
            ],
        );

        let def = mapper.generate_record_type_def("Ballot").unwrap();
        assert!(def.contains("Ballot == [seqno: Nat, proposer_id: Nat]"));
    }

    #[test]
    fn test_operator_mapping() {
        assert!(matches!(
            map_operator("&&&"),
            OperatorMapping::Mapped("/\\")
        ));
        assert!(matches!(
            map_operator("|||"),
            OperatorMapping::Mapped("\\/")
        ));
        assert!(matches!(
            map_operator("len"),
            OperatorMapping::Function("Len")
        ));
        assert!(matches!(map_operator("+"), OperatorMapping::Direct));
    }
}
