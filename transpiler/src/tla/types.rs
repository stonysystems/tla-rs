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

// =============================================================================
// Type Constraint Collection
// =============================================================================

use crate::tla::ast::{TlaBinOp, TlaExpr, TlaModule, TlaOperator, TlaUnaryOp};

/// A type constraint collected during AST traversal
#[derive(Debug, Clone, PartialEq)]
pub enum TypeConstraint {
    /// Variable has a specific type: `x : T`
    HasType { name: String, ty: TlaType },
    /// Variable is an element of a set: `x \in S` where S has element type T
    ElementOf { name: String, set_type: TlaType },
    /// Record has a field with a type
    RecordField {
        record_name: String,
        field_name: String,
        field_type: TlaType,
    },
    /// Function/map application: `f[x]` constrains f to be Map<typeof(x), result>
    MapApplication { map_name: String, key_type: TlaType },
    /// Operator has parameter types and return type
    OperatorType {
        name: String,
        param_types: Vec<TlaType>,
        return_type: TlaType,
    },
    /// Two types must be equal
    Equal(TlaType, TlaType),
}

impl fmt::Display for TypeConstraint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeConstraint::HasType { name, ty } => write!(f, "{}: {}", name, ty),
            TypeConstraint::ElementOf { name, set_type } => {
                write!(f, "{} ∈ {}", name, set_type)
            }
            TypeConstraint::RecordField {
                record_name,
                field_name,
                field_type,
            } => write!(f, "{}.{}: {}", record_name, field_name, field_type),
            TypeConstraint::MapApplication { map_name, key_type } => {
                write!(f, "{}[{}]", map_name, key_type)
            }
            TypeConstraint::OperatorType {
                name,
                param_types,
                return_type,
            } => {
                let params: Vec<_> = param_types.iter().map(|t| t.to_string()).collect();
                write!(f, "{}({}) -> {}", name, params.join(", "), return_type)
            }
            TypeConstraint::Equal(t1, t2) => write!(f, "{} = {}", t1, t2),
        }
    }
}

/// Collects type constraints from a TLA+ module
#[derive(Debug, Default)]
pub struct ConstraintCollector {
    /// Collected constraints
    pub constraints: Vec<TypeConstraint>,
    /// Next type variable ID for generating fresh type variables
    next_type_var: usize,
}

impl ConstraintCollector {
    /// Create a new constraint collector
    pub fn new() -> Self {
        Self::default()
    }

    /// Generate a fresh type variable
    pub fn fresh_type_var(&mut self) -> TlaType {
        let var = TlaType::TypeVar(self.next_type_var);
        self.next_type_var += 1;
        var
    }

    /// Add a constraint
    pub fn add(&mut self, constraint: TypeConstraint) {
        self.constraints.push(constraint);
    }

    /// Collect constraints from a TLA+ module
    pub fn collect_from_module(&mut self, module: &TlaModule) {
        // Variables are state - they could be any type initially
        for var in &module.variables {
            let ty = self.fresh_type_var();
            self.add(TypeConstraint::HasType {
                name: var.clone(),
                ty,
            });
        }

        // Constants could be any type initially
        for constant in &module.constants {
            let ty = self.fresh_type_var();
            self.add(TypeConstraint::HasType {
                name: constant.name.clone(),
                ty,
            });
        }

        // Process operator definitions to collect constraints from their bodies
        for op in &module.operators {
            self.collect_from_operator(op);
        }

        // Process assumptions
        for assumption in &module.assumptions {
            self.collect_from_expr(assumption);
        }
    }

    /// Collect constraints from an operator definition
    pub fn collect_from_operator(&mut self, op: &TlaOperator) {
        // Create type variables for parameters
        let param_types: Vec<TlaType> = op
            .params
            .iter()
            .map(|p| {
                let ty = self.fresh_type_var();
                self.add(TypeConstraint::HasType {
                    name: p.name.clone(),
                    ty: ty.clone(),
                });
                ty
            })
            .collect();

        // Collect constraints from body
        let return_type = self.collect_from_expr(&op.body);

        // Add operator type constraint
        self.add(TypeConstraint::OperatorType {
            name: op.name.clone(),
            param_types,
            return_type,
        });
    }

    /// Collect constraints from an expression, returning its inferred type
    pub fn collect_from_expr(&mut self, expr: &TlaExpr) -> TlaType {
        match expr {
            // Identifiers - lookup or create type variable
            TlaExpr::Ident(name) => {
                // Check for standard library types
                if let Some(ty) = StandardLibrary::get_global_type(name) {
                    return ty;
                }
                // Otherwise return a type variable (will be resolved later)
                self.fresh_type_var()
            }

            // Literals have known types
            TlaExpr::Number(_) => TlaType::Int, // Could be Nat, but Int is safer
            TlaExpr::String(_) => TlaType::String,
            TlaExpr::Bool(_) => TlaType::Bool,

            // Primed variables have the same type as unprimed
            TlaExpr::Prime(inner) => self.collect_from_expr(inner),

            // Binary operations
            TlaExpr::BinOp { op, left, right } => self.collect_from_binop(*op, left, right),

            // Unary operations
            TlaExpr::UnaryOp { op, operand } => self.collect_from_unary(*op, operand),

            // Set enumeration: {1, 2, 3}
            TlaExpr::SetEnum(elements) => {
                if elements.is_empty() {
                    TlaType::set(self.fresh_type_var())
                } else {
                    let elem_type = self.collect_from_expr(&elements[0]);
                    // All elements should have same type
                    for elem in elements.iter().skip(1) {
                        let ty = self.collect_from_expr(elem);
                        self.add(TypeConstraint::Equal(elem_type.clone(), ty));
                    }
                    TlaType::set(elem_type)
                }
            }

            // Set filter: {x \in S : P(x)}
            TlaExpr::SetFilter { var, set, filter } => {
                let set_type = self.collect_from_expr(set);
                if let TlaType::Set(elem_type) = &set_type {
                    self.add(TypeConstraint::HasType {
                        name: var.clone(),
                        ty: (**elem_type).clone(),
                    });
                }
                let filter_type = self.collect_from_expr(filter);
                self.add(TypeConstraint::Equal(filter_type, TlaType::Bool));
                set_type
            }

            // Set map: {f(x) : x \in S}
            TlaExpr::SetMap { expr, var, set } => {
                let set_type = self.collect_from_expr(set);
                if let TlaType::Set(elem_type) = &set_type {
                    self.add(TypeConstraint::HasType {
                        name: var.clone(),
                        ty: (**elem_type).clone(),
                    });
                }
                let result_type = self.collect_from_expr(expr);
                TlaType::set(result_type)
            }

            // Tuple: <<a, b, c>>
            TlaExpr::Tuple(elements) => {
                let elem_types: Vec<_> =
                    elements.iter().map(|e| self.collect_from_expr(e)).collect();
                TlaType::Tuple(elem_types)
            }

            // Record: [a |-> 1, b |-> 2]
            TlaExpr::Record(fields) => {
                let mut rec = RecordType::new();
                for (name, value) in fields {
                    let ty = self.collect_from_expr(value);
                    rec.fields.insert(name.clone(), ty);
                }
                TlaType::Record(rec)
            }

            // Record access: r.field
            TlaExpr::RecordAccess { record, field } => {
                let rec_type = self.collect_from_expr(record);
                let field_type = self.fresh_type_var();

                // Add constraint that record has this field
                if let TlaExpr::Ident(rec_name) = record.as_ref() {
                    self.add(TypeConstraint::RecordField {
                        record_name: rec_name.clone(),
                        field_name: field.clone(),
                        field_type: field_type.clone(),
                    });
                }

                // If we know it's a record type, we can get the field type
                if let TlaType::Record(rec) = rec_type {
                    if let Some(ft) = rec.get_field(field) {
                        return ft.clone();
                    }
                }

                field_type
            }

            // Function construction: [x \in S |-> f(x)]
            TlaExpr::FnConstruct { var, domain, body } => {
                let domain_type = self.collect_from_expr(domain);
                let elem_type = if let TlaType::Set(elem) = &domain_type {
                    (**elem).clone()
                } else {
                    self.fresh_type_var()
                };

                self.add(TypeConstraint::HasType {
                    name: var.clone(),
                    ty: elem_type.clone(),
                });

                let range_type = self.collect_from_expr(body);
                TlaType::map(elem_type, range_type)
            }

            // Function application: f[x]
            TlaExpr::FnApply { func, arg } => {
                let func_type = self.collect_from_expr(func);
                let arg_type = self.collect_from_expr(arg);

                if let TlaExpr::Ident(name) = func.as_ref() {
                    self.add(TypeConstraint::MapApplication {
                        map_name: name.clone(),
                        key_type: arg_type.clone(),
                    });
                }

                // If func is a map/function, return the value type
                match func_type {
                    TlaType::Map { value, .. } => *value,
                    TlaType::Function { range, .. } => *range,
                    _ => self.fresh_type_var(),
                }
            }

            // Function EXCEPT: [f EXCEPT ![i] = v]
            TlaExpr::FnExcept { func, updates: _ } => self.collect_from_expr(func),

            // Operator application: Op(a, b)
            TlaExpr::OpApply { op, args } => {
                self.collect_from_expr(op);
                for arg in args {
                    self.collect_from_expr(arg);
                }
                self.fresh_type_var()
            }

            // Quantifiers
            TlaExpr::Forall { vars, body } | TlaExpr::Exists { vars, body } => {
                for bound in vars {
                    if let Some(set_expr) = &bound.set {
                        let set_type = self.collect_from_expr(set_expr);
                        if let TlaType::Set(elem) = set_type {
                            self.add(TypeConstraint::HasType {
                                name: bound.var.clone(),
                                ty: *elem,
                            });
                        }
                    }
                }
                let body_type = self.collect_from_expr(body);
                self.add(TypeConstraint::Equal(body_type, TlaType::Bool));
                TlaType::Bool
            }

            // Choose
            TlaExpr::Choose { var, set, body } => {
                let elem_type = if let Some(set_expr) = set {
                    let set_type = self.collect_from_expr(set_expr);
                    if let TlaType::Set(elem) = set_type {
                        *elem
                    } else {
                        self.fresh_type_var()
                    }
                } else {
                    self.fresh_type_var()
                };

                self.add(TypeConstraint::HasType {
                    name: var.clone(),
                    ty: elem_type.clone(),
                });

                let body_type = self.collect_from_expr(body);
                self.add(TypeConstraint::Equal(body_type, TlaType::Bool));
                elem_type
            }

            // If-then-else
            TlaExpr::IfThenElse {
                cond,
                then_expr,
                else_expr,
            } => {
                let cond_type = self.collect_from_expr(cond);
                self.add(TypeConstraint::Equal(cond_type, TlaType::Bool));
                let then_type = self.collect_from_expr(then_expr);
                let else_type = self.collect_from_expr(else_expr);
                self.add(TypeConstraint::Equal(then_type.clone(), else_type));
                then_type
            }

            // Case expression
            TlaExpr::Case { arms, other } => {
                let result_type = self.fresh_type_var();
                for (cond, result) in arms {
                    let cond_type = self.collect_from_expr(cond);
                    self.add(TypeConstraint::Equal(cond_type, TlaType::Bool));
                    let arm_type = self.collect_from_expr(result);
                    self.add(TypeConstraint::Equal(result_type.clone(), arm_type));
                }
                if let Some(other_expr) = other {
                    let other_type = self.collect_from_expr(other_expr);
                    self.add(TypeConstraint::Equal(result_type.clone(), other_type));
                }
                result_type
            }

            // Let-in
            TlaExpr::LetIn { defs, body } => {
                for def in defs {
                    self.collect_from_operator(def);
                }
                self.collect_from_expr(body)
            }

            // Action operators
            TlaExpr::Unchanged(_) => TlaType::Bool,
            TlaExpr::Enabled(inner) => {
                self.collect_from_expr(inner);
                TlaType::Bool
            }

            // Temporal operators
            TlaExpr::Always(inner) | TlaExpr::Eventually(inner) => {
                self.collect_from_expr(inner);
                TlaType::Temporal
            }
            TlaExpr::LeadsTo { left, right } => {
                self.collect_from_expr(left);
                self.collect_from_expr(right);
                TlaType::Temporal
            }
            TlaExpr::WeakFairness { vars: _, action }
            | TlaExpr::StrongFairness { vars: _, action } => {
                self.collect_from_expr(action);
                TlaType::Temporal
            }
        }
    }

    /// Collect constraints from a binary operation
    fn collect_from_binop(&mut self, op: TlaBinOp, left: &TlaExpr, right: &TlaExpr) -> TlaType {
        let left_type = self.collect_from_expr(left);
        let right_type = self.collect_from_expr(right);

        match op {
            // Logical operators: Bool -> Bool -> Bool
            TlaBinOp::And | TlaBinOp::Or | TlaBinOp::Implies | TlaBinOp::Iff => {
                self.add(TypeConstraint::Equal(left_type, TlaType::Bool));
                self.add(TypeConstraint::Equal(right_type, TlaType::Bool));
                TlaType::Bool
            }

            // Arithmetic operators: Int -> Int -> Int
            TlaBinOp::Plus
            | TlaBinOp::Minus
            | TlaBinOp::Times
            | TlaBinOp::Div
            | TlaBinOp::Mod
            | TlaBinOp::Slash
            | TlaBinOp::Caret => {
                // Could be Nat or Int - use Int as superset
                self.add(TypeConstraint::Equal(left_type, TlaType::Int));
                self.add(TypeConstraint::Equal(right_type, TlaType::Int));
                TlaType::Int
            }

            // Comparison operators
            TlaBinOp::Eq | TlaBinOp::Neq => {
                self.add(TypeConstraint::Equal(left_type, right_type));
                TlaType::Bool
            }
            TlaBinOp::Lt | TlaBinOp::Leq | TlaBinOp::Gt | TlaBinOp::Geq => {
                // Comparison on ordered types (Int/Nat)
                TlaType::Bool
            }

            // Set membership: x \in S
            TlaBinOp::In | TlaBinOp::NotIn => {
                // This is a key pattern for type inference!
                // If we have `x \in Nat`, then x : Nat
                // If we have `x \in S` where S : Set(T), then x : T
                if let TlaExpr::Ident(var_name) = left {
                    // Check for standard sets
                    if let TlaExpr::Ident(set_name) = right {
                        if let Some(TlaType::Set(elem_type)) =
                            StandardLibrary::get_global_type(set_name)
                        {
                            self.add(TypeConstraint::HasType {
                                name: var_name.clone(),
                                ty: *elem_type,
                            });
                        }
                    }

                    // General case: constrain based on set element type
                    self.add(TypeConstraint::ElementOf {
                        name: var_name.clone(),
                        set_type: right_type.clone(),
                    });
                }

                TlaType::Bool
            }

            // Set operations
            TlaBinOp::Subseteq => {
                self.add(TypeConstraint::Equal(left_type, right_type.clone()));
                TlaType::Bool
            }
            TlaBinOp::Cup | TlaBinOp::Cap | TlaBinOp::Setminus => {
                self.add(TypeConstraint::Equal(left_type.clone(), right_type));
                left_type
            }
            TlaBinOp::CrossProd => {
                // S \X T produces Set(Tuple(elem(S), elem(T)))
                let left_elem = if let TlaType::Set(e) = left_type {
                    *e
                } else {
                    self.fresh_type_var()
                };
                let right_elem = if let TlaType::Set(e) = right_type {
                    *e
                } else {
                    self.fresh_type_var()
                };
                TlaType::set(TlaType::tuple(vec![left_elem, right_elem]))
            }

            // Range: a..b produces Set(Int)
            TlaBinOp::DotDot => {
                self.add(TypeConstraint::Equal(left_type, TlaType::Int));
                self.add(TypeConstraint::Equal(right_type, TlaType::Int));
                TlaType::IntRange
            }

            // Action composition: A \cdot B
            TlaBinOp::Compose => {
                // Both operands are actions
                self.add(TypeConstraint::Equal(left_type, TlaType::Action));
                self.add(TypeConstraint::Equal(right_type, TlaType::Action));
                TlaType::Action
            }
        }
    }

    /// Collect constraints from a unary operation
    fn collect_from_unary(&mut self, op: TlaUnaryOp, operand: &TlaExpr) -> TlaType {
        let operand_type = self.collect_from_expr(operand);

        match op {
            TlaUnaryOp::Not => {
                self.add(TypeConstraint::Equal(operand_type, TlaType::Bool));
                TlaType::Bool
            }
            TlaUnaryOp::Neg => {
                self.add(TypeConstraint::Equal(operand_type, TlaType::Int));
                TlaType::Int
            }
            TlaUnaryOp::Domain => {
                // DOMAIN f returns the domain set of a function/map
                if let TlaType::Map { key, .. } = operand_type {
                    TlaType::set(*key)
                } else {
                    TlaType::set(self.fresh_type_var())
                }
            }
            TlaUnaryOp::Subset => {
                // SUBSET S = powerset of S
                TlaType::set(operand_type)
            }
            TlaUnaryOp::Union => {
                // UNION S where S is a set of sets
                if let TlaType::Set(inner) = operand_type {
                    if let TlaType::Set(elem) = *inner {
                        return TlaType::set(*elem);
                    }
                }
                TlaType::set(self.fresh_type_var())
            }
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

    // Constraint collection tests
    use crate::tla::parser::parse_module;

    #[test]
    fn test_constraint_collector_membership() {
        let source = r"
            ---- MODULE Test ----
            VARIABLE x
            Init == x \in Nat
            ====
        ";
        let module = parse_module(source).unwrap();
        let mut collector = ConstraintCollector::new();
        collector.collect_from_module(&module);

        // Should have constraint that x is Nat
        let has_nat_constraint = collector.constraints.iter().any(|c| {
            matches!(c, TypeConstraint::HasType { name, ty } if name == "x" && *ty == TlaType::Nat)
        });
        assert!(
            has_nat_constraint,
            "Expected constraint x: Nat, got {:?}",
            collector.constraints
        );
    }

    #[test]
    fn test_constraint_collector_arithmetic() {
        let source = r"
            ---- MODULE Test ----
            Add(a, b) == a + b
            ====
        ";
        let module = parse_module(source).unwrap();
        let mut collector = ConstraintCollector::new();
        collector.collect_from_module(&module);

        // Should have operator type constraint for Add
        let has_operator_constraint = collector
            .constraints
            .iter()
            .any(|c| matches!(c, TypeConstraint::OperatorType { name, .. } if name == "Add"));
        assert!(has_operator_constraint);
    }

    #[test]
    fn test_constraint_collector_record() {
        let source = r"
            ---- MODULE Test ----
            R == [x |-> 1, y |-> TRUE]
            ====
        ";
        let module = parse_module(source).unwrap();
        let mut collector = ConstraintCollector::new();
        collector.collect_from_module(&module);

        // Should collect operator type
        assert!(!collector.constraints.is_empty());
    }

    #[test]
    fn test_constraint_collector_set_enum() {
        let source = r"
            ---- MODULE Test ----
            S == {1, 2, 3}
            ====
        ";
        let module = parse_module(source).unwrap();
        let mut collector = ConstraintCollector::new();
        collector.collect_from_module(&module);

        assert!(!collector.constraints.is_empty());
    }

    #[test]
    fn test_constraint_collector_quantifier() {
        let source = r"
            ---- MODULE Test ----
            AllPositive == \A x \in Nat : x >= 0
            ====
        ";
        let module = parse_module(source).unwrap();
        let mut collector = ConstraintCollector::new();
        collector.collect_from_module(&module);

        // Should have constraint that x is Nat from quantifier bound
        let has_nat_constraint = collector.constraints.iter().any(|c| {
            matches!(c, TypeConstraint::HasType { name, ty } if name == "x" && *ty == TlaType::Nat)
        });
        assert!(has_nat_constraint);
    }

    #[test]
    fn test_constraint_display() {
        let c1 = TypeConstraint::HasType {
            name: "x".to_string(),
            ty: TlaType::Int,
        };
        assert_eq!(c1.to_string(), "x: Int");

        let c2 = TypeConstraint::ElementOf {
            name: "y".to_string(),
            set_type: TlaType::set(TlaType::Nat),
        };
        assert_eq!(c2.to_string(), "y ∈ Set(Nat)");
    }
}
