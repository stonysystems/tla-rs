//! TLA+ type system representation for type inference.
//!
//! This module defines types for representing inferred TLA+ types and
//! performing type inference on TLA+ specifications.

use std::collections::HashMap;
use std::fmt;

/// Represents a TLA+ type, inferred from usage patterns.
///
/// TLA+ is untyped, but we infer types from:
/// - Membership in standard sets (`\in Nat`, `\in Int`, `\in BOOLEAN`)
/// - Set/sequence/function construction syntax
/// - Record field access patterns
/// - Operator signatures
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TlaType {
    /// Unknown type (not yet inferred or truly polymorphic)
    Unknown,
    /// Type variable for unification (internal use)
    TypeVar(usize),

    // Primitive types
    /// Integer type (from `\in Int`)
    Int,
    /// Natural number type (from `\in Nat`)
    Nat,
    /// Boolean type (from `\in BOOLEAN` or logical expressions)
    Bool,
    /// String type (from string literals or `\in STRING`)
    String,

    // Collection types
    /// Set type with element type: `Set<T>`
    Set(Box<TlaType>),
    /// Sequence type with element type: `Seq<T>`
    Seq(Box<TlaType>),
    /// Finite set of integers: `1..n`
    IntRange,

    // Function/Map types
    /// Function type: `[D -> R]` where D is domain, R is range
    Function {
        domain: Box<TlaType>,
        range: Box<TlaType>,
    },
    /// Map type (finite function): `[K -> V]`
    Map {
        key: Box<TlaType>,
        value: Box<TlaType>,
    },

    // Composite types
    /// Record type with named fields
    Record(RecordType),
    /// Tuple type with positional elements
    Tuple(Vec<TlaType>),

    // Special types
    /// Action type (for state transitions)
    Action,
    /// Temporal formula type
    Temporal,
    /// Any type (escape hatch for unsupported patterns)
    Any,
}

impl TlaType {
    /// Create a set type
    pub fn set(elem_type: TlaType) -> Self {
        TlaType::Set(Box::new(elem_type))
    }

    /// Create a sequence type
    pub fn seq(elem_type: TlaType) -> Self {
        TlaType::Seq(Box::new(elem_type))
    }

    /// Create a function type
    pub fn function(domain: TlaType, range: TlaType) -> Self {
        TlaType::Function {
            domain: Box::new(domain),
            range: Box::new(range),
        }
    }

    /// Create a map type
    pub fn map(key: TlaType, value: TlaType) -> Self {
        TlaType::Map {
            key: Box::new(key),
            value: Box::new(value),
        }
    }

    /// Create a tuple type
    pub fn tuple(elements: Vec<TlaType>) -> Self {
        TlaType::Tuple(elements)
    }

    /// Check if this type is unknown or a type variable
    pub fn is_unknown(&self) -> bool {
        matches!(self, TlaType::Unknown | TlaType::TypeVar(_))
    }

    /// Check if this type is a collection type
    pub fn is_collection(&self) -> bool {
        matches!(
            self,
            TlaType::Set(_) | TlaType::Seq(_) | TlaType::Map { .. }
        )
    }

    /// Get element type for collections, if applicable
    pub fn element_type(&self) -> Option<&TlaType> {
        match self {
            TlaType::Set(elem) | TlaType::Seq(elem) => Some(elem),
            _ => None,
        }
    }

    /// Convert to Verus type string representation
    pub fn to_verus_type(&self) -> String {
        match self {
            TlaType::Unknown => "/* unknown */".to_string(),
            TlaType::TypeVar(n) => format!("T{}", n),
            TlaType::Int => "int".to_string(),
            TlaType::Nat => "nat".to_string(),
            TlaType::Bool => "bool".to_string(),
            TlaType::String => "Seq<char>".to_string(),
            TlaType::Set(elem) => format!("Set<{}>", elem.to_verus_type()),
            TlaType::Seq(elem) => format!("Seq<{}>", elem.to_verus_type()),
            TlaType::IntRange => "Set<int>".to_string(),
            TlaType::Function { domain, range } => {
                format!(
                    "spec_fn({}) -> {}",
                    domain.to_verus_type(),
                    range.to_verus_type()
                )
            }
            TlaType::Map { key, value } => {
                format!("Map<{}, {}>", key.to_verus_type(), value.to_verus_type())
            }
            TlaType::Record(rec) => rec.to_verus_type(),
            TlaType::Tuple(elems) => {
                let types: Vec<_> = elems.iter().map(|t| t.to_verus_type()).collect();
                format!("({})", types.join(", "))
            }
            TlaType::Action => "bool".to_string(),
            TlaType::Temporal => "bool".to_string(),
            TlaType::Any => "/* any */".to_string(),
        }
    }
}

impl fmt::Display for TlaType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TlaType::Unknown => write!(f, "?"),
            TlaType::TypeVar(n) => write!(f, "T{}", n),
            TlaType::Int => write!(f, "Int"),
            TlaType::Nat => write!(f, "Nat"),
            TlaType::Bool => write!(f, "Bool"),
            TlaType::String => write!(f, "String"),
            TlaType::Set(elem) => write!(f, "Set({})", elem),
            TlaType::Seq(elem) => write!(f, "Seq({})", elem),
            TlaType::IntRange => write!(f, "Int..Int"),
            TlaType::Function { domain, range } => write!(f, "[{} -> {}]", domain, range),
            TlaType::Map { key, value } => write!(f, "Map({}, {})", key, value),
            TlaType::Record(rec) => write!(f, "{}", rec),
            TlaType::Tuple(elems) => {
                let types: Vec<_> = elems.iter().map(|t| t.to_string()).collect();
                write!(f, "<<{}>>", types.join(", "))
            }
            TlaType::Action => write!(f, "Action"),
            TlaType::Temporal => write!(f, "Temporal"),
            TlaType::Any => write!(f, "Any"),
        }
    }
}

/// Record type with named fields
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecordType {
    /// Field names and their types
    pub fields: HashMap<String, TlaType>,
    /// Optional record name (for named structs)
    pub name: Option<String>,
}

impl RecordType {
    /// Create a new anonymous record type
    pub fn new() -> Self {
        Self {
            fields: HashMap::new(),
            name: None,
        }
    }

    /// Create a named record type
    pub fn named(name: impl Into<String>) -> Self {
        Self {
            fields: HashMap::new(),
            name: Some(name.into()),
        }
    }

    /// Add a field to the record
    pub fn with_field(mut self, name: impl Into<String>, ty: TlaType) -> Self {
        self.fields.insert(name.into(), ty);
        self
    }

    /// Get a field type
    pub fn get_field(&self, name: &str) -> Option<&TlaType> {
        self.fields.get(name)
    }

    /// Convert to Verus type string
    pub fn to_verus_type(&self) -> String {
        if let Some(name) = &self.name {
            name.clone()
        } else {
            // Anonymous record as a tuple-like struct
            let fields: Vec<_> = self
                .fields
                .iter()
                .map(|(k, v)| format!("{}: {}", k, v.to_verus_type()))
                .collect();
            format!("{{ {} }}", fields.join(", "))
        }
    }
}

impl Default for RecordType {
    fn default() -> Self {
        Self::new()
    }
}

impl fmt::Display for RecordType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(name) = &self.name {
            write!(f, "{}", name)
        } else {
            let fields: Vec<_> = self
                .fields
                .iter()
                .map(|(k, v)| format!("{}: {}", k, v))
                .collect();
            write!(f, "[{}]", fields.join(", "))
        }
    }
}

/// Type environment mapping identifiers to their inferred types
#[derive(Debug, Clone, Default)]
pub struct TypeEnv {
    /// Types for constants
    pub constants: HashMap<String, TlaType>,
    /// Types for variables
    pub variables: HashMap<String, TlaType>,
    /// Types for operators (as function types)
    pub operators: HashMap<String, TlaType>,
    /// Inferred record types
    pub records: HashMap<String, RecordType>,
}

impl TypeEnv {
    /// Create a new empty type environment
    pub fn new() -> Self {
        Self::default()
    }

    /// Look up a type by name (checks constants, then variables, then operators)
    pub fn lookup(&self, name: &str) -> Option<&TlaType> {
        self.constants
            .get(name)
            .or_else(|| self.variables.get(name))
            .or_else(|| self.operators.get(name))
    }

    /// Set a constant's type
    pub fn set_constant(&mut self, name: impl Into<String>, ty: TlaType) {
        self.constants.insert(name.into(), ty);
    }

    /// Set a variable's type
    pub fn set_variable(&mut self, name: impl Into<String>, ty: TlaType) {
        self.variables.insert(name.into(), ty);
    }

    /// Set an operator's type
    pub fn set_operator(&mut self, name: impl Into<String>, ty: TlaType) {
        self.operators.insert(name.into(), ty);
    }

    /// Register a record type
    pub fn register_record(&mut self, name: impl Into<String>, record: RecordType) {
        self.records.insert(name.into(), record);
    }
}

/// Known TLA+ standard modules and their type information
pub struct StandardLibrary;

impl StandardLibrary {
    /// Get the type of a standard library identifier
    pub fn get_type(module: &str, name: &str) -> Option<TlaType> {
        match (module, name) {
            // Naturals module
            ("Naturals", "Nat") => Some(TlaType::set(TlaType::Nat)),
            ("Naturals", "+") | ("Naturals", "-") | ("Naturals", "*") => Some(TlaType::function(
                TlaType::tuple(vec![TlaType::Nat, TlaType::Nat]),
                TlaType::Nat,
            )),
            ("Naturals", "\\div") | ("Naturals", "%") => Some(TlaType::function(
                TlaType::tuple(vec![TlaType::Nat, TlaType::Nat]),
                TlaType::Nat,
            )),

            // Integers module
            ("Integers", "Int") => Some(TlaType::set(TlaType::Int)),
            ("Integers", "+") | ("Integers", "-") | ("Integers", "*") => Some(TlaType::function(
                TlaType::tuple(vec![TlaType::Int, TlaType::Int]),
                TlaType::Int,
            )),

            // Sequences module
            ("Sequences", "Seq") => Some(TlaType::function(
                TlaType::set(TlaType::TypeVar(0)),
                TlaType::set(TlaType::seq(TlaType::TypeVar(0))),
            )),
            ("Sequences", "Len") => Some(TlaType::function(
                TlaType::seq(TlaType::TypeVar(0)),
                TlaType::Nat,
            )),
            ("Sequences", "Append") => Some(TlaType::function(
                TlaType::tuple(vec![TlaType::seq(TlaType::TypeVar(0)), TlaType::TypeVar(0)]),
                TlaType::seq(TlaType::TypeVar(0)),
            )),
            ("Sequences", "Head") => Some(TlaType::function(
                TlaType::seq(TlaType::TypeVar(0)),
                TlaType::TypeVar(0),
            )),
            ("Sequences", "Tail") => Some(TlaType::function(
                TlaType::seq(TlaType::TypeVar(0)),
                TlaType::seq(TlaType::TypeVar(0)),
            )),
            ("Sequences", "SubSeq") => Some(TlaType::function(
                TlaType::tuple(vec![
                    TlaType::seq(TlaType::TypeVar(0)),
                    TlaType::Nat,
                    TlaType::Nat,
                ]),
                TlaType::seq(TlaType::TypeVar(0)),
            )),

            // FiniteSets module
            ("FiniteSets", "Cardinality") => Some(TlaType::function(
                TlaType::set(TlaType::TypeVar(0)),
                TlaType::Nat,
            )),
            ("FiniteSets", "IsFiniteSet") => Some(TlaType::function(
                TlaType::set(TlaType::TypeVar(0)),
                TlaType::Bool,
            )),

            // TLC module
            ("TLC", "Print") => Some(TlaType::function(
                TlaType::tuple(vec![TlaType::String, TlaType::TypeVar(0)]),
                TlaType::TypeVar(0),
            )),

            _ => None,
        }
    }

    /// Get the type of a globally known identifier (without module prefix)
    pub fn get_global_type(name: &str) -> Option<TlaType> {
        match name {
            "Nat" => Some(TlaType::set(TlaType::Nat)),
            "Int" => Some(TlaType::set(TlaType::Int)),
            "BOOLEAN" => Some(TlaType::set(TlaType::Bool)),
            "STRING" => Some(TlaType::set(TlaType::String)),
            "TRUE" => Some(TlaType::Bool),
            "FALSE" => Some(TlaType::Bool),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_types() {
        assert_eq!(TlaType::Int.to_string(), "Int");
        assert_eq!(TlaType::Nat.to_string(), "Nat");
        assert_eq!(TlaType::Bool.to_string(), "Bool");
        assert_eq!(TlaType::String.to_string(), "String");
    }

    #[test]
    fn test_collection_types() {
        let set_int = TlaType::set(TlaType::Int);
        assert_eq!(set_int.to_string(), "Set(Int)");
        assert!(set_int.is_collection());
        assert_eq!(set_int.element_type(), Some(&TlaType::Int));

        let seq_nat = TlaType::seq(TlaType::Nat);
        assert_eq!(seq_nat.to_string(), "Seq(Nat)");
    }

    #[test]
    fn test_function_types() {
        let func = TlaType::function(TlaType::Nat, TlaType::Int);
        assert_eq!(func.to_string(), "[Nat -> Int]");

        let map_type = TlaType::map(TlaType::String, TlaType::Int);
        assert_eq!(map_type.to_string(), "Map(String, Int)");
    }

    #[test]
    fn test_record_type() {
        let rec = RecordType::new()
            .with_field("x", TlaType::Int)
            .with_field("y", TlaType::Bool);
        assert!(rec.get_field("x").is_some());
        assert!(rec.get_field("z").is_none());
    }

    #[test]
    fn test_tuple_type() {
        let tuple = TlaType::tuple(vec![TlaType::Int, TlaType::Bool, TlaType::String]);
        assert_eq!(tuple.to_string(), "<<Int, Bool, String>>");
    }

    #[test]
    fn test_verus_type_conversion() {
        assert_eq!(TlaType::Int.to_verus_type(), "int");
        assert_eq!(TlaType::Nat.to_verus_type(), "nat");
        assert_eq!(TlaType::set(TlaType::Int).to_verus_type(), "Set<int>");
        assert_eq!(TlaType::seq(TlaType::Nat).to_verus_type(), "Seq<nat>");
        assert_eq!(
            TlaType::map(TlaType::String, TlaType::Int).to_verus_type(),
            "Map<Seq<char>, int>"
        );
    }

    #[test]
    fn test_type_env() {
        let mut env = TypeEnv::new();
        env.set_constant("N", TlaType::Nat);
        env.set_variable("x", TlaType::Int);
        env.set_operator(
            "Add",
            TlaType::function(
                TlaType::tuple(vec![TlaType::Int, TlaType::Int]),
                TlaType::Int,
            ),
        );

        assert_eq!(env.lookup("N"), Some(&TlaType::Nat));
        assert_eq!(env.lookup("x"), Some(&TlaType::Int));
        assert!(env.lookup("Add").is_some());
        assert!(env.lookup("unknown").is_none());
    }

    #[test]
    fn test_standard_library() {
        assert_eq!(
            StandardLibrary::get_global_type("Nat"),
            Some(TlaType::set(TlaType::Nat))
        );
        assert_eq!(
            StandardLibrary::get_global_type("Int"),
            Some(TlaType::set(TlaType::Int))
        );
        assert_eq!(
            StandardLibrary::get_global_type("TRUE"),
            Some(TlaType::Bool)
        );
        assert!(StandardLibrary::get_type("Sequences", "Len").is_some());
    }

    #[test]
    fn test_type_unknown() {
        assert!(TlaType::Unknown.is_unknown());
        assert!(TlaType::TypeVar(0).is_unknown());
        assert!(!TlaType::Int.is_unknown());
    }

    #[test]
    fn test_named_record() {
        let rec = RecordType::named("Point")
            .with_field("x", TlaType::Int)
            .with_field("y", TlaType::Int);
        assert_eq!(rec.name, Some("Point".to_string()));
        assert_eq!(rec.to_verus_type(), "Point");
    }
}
