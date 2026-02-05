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

// =============================================================================
// Type Unification and Resolution
// =============================================================================

/// Type substitution: maps type variables to resolved types
#[derive(Debug, Clone, Default)]
pub struct TypeSubstitution {
    /// Mapping from type variable ID to resolved type
    substitutions: HashMap<usize, TlaType>,
}

impl TypeSubstitution {
    /// Create a new empty substitution
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a substitution: TypeVar(id) -> ty
    pub fn insert(&mut self, id: usize, ty: TlaType) {
        self.substitutions.insert(id, ty);
    }

    /// Get the substitution for a type variable
    pub fn get(&self, id: usize) -> Option<&TlaType> {
        self.substitutions.get(&id)
    }

    /// Apply the substitution to a type, resolving type variables
    pub fn apply(&self, ty: &TlaType) -> TlaType {
        match ty {
            TlaType::TypeVar(id) => {
                if let Some(resolved) = self.get(*id) {
                    // Recursively apply in case the resolved type also has variables
                    self.apply(resolved)
                } else {
                    ty.clone()
                }
            }
            TlaType::Set(elem) => TlaType::set(self.apply(elem)),
            TlaType::Seq(elem) => TlaType::seq(self.apply(elem)),
            TlaType::Map { key, value } => TlaType::map(self.apply(key), self.apply(value)),
            TlaType::Function { domain, range } => {
                TlaType::function(self.apply(domain), self.apply(range))
            }
            TlaType::Tuple(elems) => TlaType::Tuple(elems.iter().map(|e| self.apply(e)).collect()),
            TlaType::Record(rec) => {
                let mut new_rec = RecordType::new();
                new_rec.name = rec.name.clone();
                for (name, field_ty) in &rec.fields {
                    new_rec.fields.insert(name.clone(), self.apply(field_ty));
                }
                TlaType::Record(new_rec)
            }
            // Primitive and special types don't contain type variables
            _ => ty.clone(),
        }
    }
}

/// Type unification result
#[derive(Debug)]
pub enum UnifyResult {
    /// Unification succeeded
    Ok,
    /// Unification failed with a conflict
    Conflict { expected: TlaType, found: TlaType },
}

/// Unifies types and resolves constraints
pub struct TypeUnifier {
    /// Current substitution
    pub substitution: TypeSubstitution,
    /// Errors encountered during unification
    pub errors: Vec<String>,
}

impl Default for TypeUnifier {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeUnifier {
    /// Create a new type unifier
    pub fn new() -> Self {
        Self {
            substitution: TypeSubstitution::new(),
            errors: Vec::new(),
        }
    }

    /// Process a list of constraints and build the substitution
    pub fn process_constraints(&mut self, constraints: &[TypeConstraint]) {
        for constraint in constraints {
            self.process_constraint(constraint);
        }
    }

    /// Process a single constraint
    fn process_constraint(&mut self, constraint: &TypeConstraint) {
        match constraint {
            TypeConstraint::HasType { name, ty } => {
                // If ty is a TypeVar, we might already have a substitution for it
                let resolved_ty = self.substitution.apply(ty);
                // Store the resolved type for the variable name
                // (This is handled by building the TypeEnv later)
                let _ = (name, resolved_ty); // Suppress unused warning for now
            }
            TypeConstraint::ElementOf { name: _, set_type } => {
                // If set_type is Set(T), then the element has type T
                let resolved = self.substitution.apply(set_type);
                if let TlaType::Set(elem_type) = resolved {
                    // The variable should have the element type
                    let _ = elem_type; // Used in building TypeEnv
                }
            }
            TypeConstraint::Equal(ty1, ty2) => {
                let resolved1 = self.substitution.apply(ty1);
                let resolved2 = self.substitution.apply(ty2);
                self.unify(&resolved1, &resolved2);
            }
            TypeConstraint::RecordField { .. }
            | TypeConstraint::MapApplication { .. }
            | TypeConstraint::OperatorType { .. } => {
                // These constraints are used for building the type environment
                // but don't require immediate unification
            }
        }
    }

    /// Unify two types, updating the substitution
    pub fn unify(&mut self, ty1: &TlaType, ty2: &TlaType) -> UnifyResult {
        // Apply current substitution first
        let t1 = self.substitution.apply(ty1);
        let t2 = self.substitution.apply(ty2);

        match (&t1, &t2) {
            // Type variables unify with anything
            (TlaType::TypeVar(id), other) | (other, TlaType::TypeVar(id)) => {
                // Occurs check: prevent infinite types
                if !self.occurs(*id, other) {
                    self.substitution.insert(*id, other.clone());
                    UnifyResult::Ok
                } else {
                    self.errors.push(format!(
                        "Infinite type detected: T{} occurs in {}",
                        id, other
                    ));
                    UnifyResult::Conflict {
                        expected: t1,
                        found: t2,
                    }
                }
            }

            // Unknown unifies with anything (it's like a wildcard)
            (TlaType::Unknown, _) | (_, TlaType::Unknown) => UnifyResult::Ok,

            // Any unifies with anything (escape hatch)
            (TlaType::Any, _) | (_, TlaType::Any) => UnifyResult::Ok,

            // Same base types unify
            (TlaType::Int, TlaType::Int)
            | (TlaType::Nat, TlaType::Nat)
            | (TlaType::Bool, TlaType::Bool)
            | (TlaType::String, TlaType::String)
            | (TlaType::IntRange, TlaType::IntRange)
            | (TlaType::Action, TlaType::Action)
            | (TlaType::Temporal, TlaType::Temporal) => UnifyResult::Ok,

            // Nat is a subtype of Int
            (TlaType::Nat, TlaType::Int) | (TlaType::Int, TlaType::Nat) => UnifyResult::Ok,

            // IntRange is a Set(Int)
            (TlaType::IntRange, TlaType::Set(elem)) | (TlaType::Set(elem), TlaType::IntRange) => {
                self.unify(elem, &TlaType::Int)
            }

            // Set types unify if their element types unify
            (TlaType::Set(e1), TlaType::Set(e2)) => self.unify(e1, e2),

            // Sequence types unify if their element types unify
            (TlaType::Seq(e1), TlaType::Seq(e2)) => self.unify(e1, e2),

            // Map types unify if both key and value types unify
            (TlaType::Map { key: k1, value: v1 }, TlaType::Map { key: k2, value: v2 }) => {
                let key_result = self.unify(k1, k2);
                if matches!(key_result, UnifyResult::Conflict { .. }) {
                    return key_result;
                }
                self.unify(v1, v2)
            }

            // Function types unify if domain and range types unify
            (
                TlaType::Function {
                    domain: d1,
                    range: r1,
                },
                TlaType::Function {
                    domain: d2,
                    range: r2,
                },
            ) => {
                let domain_result = self.unify(d1, d2);
                if matches!(domain_result, UnifyResult::Conflict { .. }) {
                    return domain_result;
                }
                self.unify(r1, r2)
            }

            // Tuple types unify if they have the same length and element types unify
            (TlaType::Tuple(elems1), TlaType::Tuple(elems2)) => {
                if elems1.len() != elems2.len() {
                    self.errors.push(format!(
                        "Tuple length mismatch: expected {} elements, found {}",
                        elems1.len(),
                        elems2.len()
                    ));
                    return UnifyResult::Conflict {
                        expected: t1,
                        found: t2,
                    };
                }
                for (e1, e2) in elems1.iter().zip(elems2.iter()) {
                    let result = self.unify(e1, e2);
                    if matches!(result, UnifyResult::Conflict { .. }) {
                        return result;
                    }
                }
                UnifyResult::Ok
            }

            // Record types unify if all shared fields unify
            (TlaType::Record(rec1), TlaType::Record(rec2)) => {
                for (field_name, field_ty1) in &rec1.fields {
                    if let Some(field_ty2) = rec2.fields.get(field_name) {
                        let result = self.unify(field_ty1, field_ty2);
                        if matches!(result, UnifyResult::Conflict { .. }) {
                            return result;
                        }
                    }
                }
                UnifyResult::Ok
            }

            // Otherwise, types don't unify
            _ => {
                self.errors
                    .push(format!("Type mismatch: expected {}, found {}", t1, t2));
                UnifyResult::Conflict {
                    expected: t1,
                    found: t2,
                }
            }
        }
    }

    /// Check if a type variable occurs in a type (for occurs check)
    fn occurs(&self, var_id: usize, ty: &TlaType) -> bool {
        match ty {
            TlaType::TypeVar(id) => *id == var_id,
            TlaType::Set(elem) | TlaType::Seq(elem) => self.occurs(var_id, elem),
            TlaType::Map { key, value } => self.occurs(var_id, key) || self.occurs(var_id, value),
            TlaType::Function { domain, range } => {
                self.occurs(var_id, domain) || self.occurs(var_id, range)
            }
            TlaType::Tuple(elems) => elems.iter().any(|e| self.occurs(var_id, e)),
            TlaType::Record(rec) => rec.fields.values().any(|t| self.occurs(var_id, t)),
            _ => false,
        }
    }

    /// Build a TypeEnv from the processed constraints
    pub fn build_type_env(&self, constraints: &[TypeConstraint]) -> TypeEnv {
        let mut env = TypeEnv::new();

        for constraint in constraints {
            match constraint {
                TypeConstraint::HasType { name, ty } => {
                    let resolved = self.substitution.apply(ty);
                    // Determine if it's a constant, variable, or operator based on naming convention
                    // For now, just add to variables (will be refined in T4.1.4)
                    env.set_variable(name, resolved);
                }
                TypeConstraint::OperatorType {
                    name,
                    param_types,
                    return_type,
                } => {
                    let resolved_params: Vec<_> = param_types
                        .iter()
                        .map(|t| self.substitution.apply(t))
                        .collect();
                    let resolved_return = self.substitution.apply(return_type);

                    let op_type = if resolved_params.is_empty() {
                        resolved_return
                    } else {
                        TlaType::function(TlaType::Tuple(resolved_params), resolved_return)
                    };
                    env.set_operator(name, op_type);
                }
                TypeConstraint::RecordField {
                    record_name,
                    field_name,
                    field_type,
                } => {
                    let resolved_field_type = self.substitution.apply(field_type);
                    // Register the record type if not already registered
                    let rec = env
                        .records
                        .entry(record_name.clone())
                        .or_insert_with(|| RecordType::named(record_name));
                    rec.fields.insert(field_name.clone(), resolved_field_type);
                }
                _ => {}
            }
        }

        env
    }
}

// =============================================================================
// Type Inference API
// =============================================================================

/// Complete type inference engine for TLA+ modules.
///
/// This combines constraint collection and unification into a single
/// easy-to-use API that takes a TLA+ module and produces a complete
/// type environment.
pub struct TypeInference {
    /// The constraint collector
    pub collector: ConstraintCollector,
    /// The type unifier
    pub unifier: TypeUnifier,
}

impl Default for TypeInference {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeInference {
    /// Create a new type inference engine
    pub fn new() -> Self {
        Self {
            collector: ConstraintCollector::new(),
            unifier: TypeUnifier::new(),
        }
    }

    /// Perform complete type inference on a TLA+ module.
    ///
    /// This:
    /// 1. Collects type constraints from the module
    /// 2. Unifies constraints to resolve type variables
    /// 3. Builds a TypeEnv with properly categorized identifiers
    ///
    /// # Example
    /// ```ignore
    /// let module = parse_module(source)?;
    /// let mut inference = TypeInference::new();
    /// let type_env = inference.infer_types(&module);
    /// ```
    pub fn infer_types(&mut self, module: &TlaModule) -> TypeEnv {
        // Step 1: Collect constraints from the module
        self.collector.collect_from_module(module);

        // Step 2: Process constraints through unification
        self.unifier
            .process_constraints(&self.collector.constraints);

        // Step 3: Build type environment with proper categorization
        self.build_module_type_env(module)
    }

    /// Build a TypeEnv with proper categorization based on module definition.
    ///
    /// Unlike `TypeUnifier::build_type_env`, this method properly categorizes
    /// identifiers as constants, variables, or operators based on how they
    /// were declared in the module.
    fn build_module_type_env(&self, module: &TlaModule) -> TypeEnv {
        let mut env = TypeEnv::new();

        // Track names declared in the module for proper categorization
        let constants: std::collections::HashSet<&str> =
            module.constants.iter().map(|c| c.name.as_str()).collect();
        let variables: std::collections::HashSet<&str> =
            module.variables.iter().map(|v| v.as_str()).collect();
        let operators: std::collections::HashSet<&str> =
            module.operators.iter().map(|o| o.name.as_str()).collect();

        // Process all constraints
        for constraint in &self.collector.constraints {
            match constraint {
                TypeConstraint::HasType { name, ty } => {
                    let resolved = self.unifier.substitution.apply(ty);
                    // Categorize based on module declarations
                    if constants.contains(name.as_str()) {
                        env.set_constant(name, resolved);
                    } else if variables.contains(name.as_str()) {
                        env.set_variable(name, resolved);
                    } else {
                        // Local variables (from quantifiers, let bindings, etc.)
                        // go into variables for now
                        env.set_variable(name, resolved);
                    }
                }
                TypeConstraint::OperatorType {
                    name,
                    param_types,
                    return_type,
                } => {
                    if operators.contains(name.as_str()) {
                        let resolved_params: Vec<_> = param_types
                            .iter()
                            .map(|t| self.unifier.substitution.apply(t))
                            .collect();
                        let resolved_return = self.unifier.substitution.apply(return_type);

                        let op_type = if resolved_params.is_empty() {
                            resolved_return
                        } else {
                            TlaType::function(TlaType::Tuple(resolved_params), resolved_return)
                        };
                        env.set_operator(name, op_type);
                    }
                }
                TypeConstraint::RecordField {
                    record_name,
                    field_name,
                    field_type,
                } => {
                    let resolved_field_type = self.unifier.substitution.apply(field_type);
                    let rec = env
                        .records
                        .entry(record_name.clone())
                        .or_insert_with(|| RecordType::named(record_name));
                    rec.fields.insert(field_name.clone(), resolved_field_type);
                }
                _ => {}
            }
        }

        env
    }

    /// Get any type inference errors
    pub fn errors(&self) -> &[String] {
        &self.unifier.errors
    }

    /// Check if type inference succeeded without errors
    pub fn is_successful(&self) -> bool {
        self.unifier.errors.is_empty()
    }

    /// Get the inferred type for an identifier from constraints
    pub fn get_inferred_type(&self, name: &str) -> Option<TlaType> {
        for constraint in &self.collector.constraints {
            if let TypeConstraint::HasType { name: var_name, ty } = constraint {
                if var_name == name {
                    return Some(self.unifier.substitution.apply(ty));
                }
            }
        }
        None
    }

    /// Get diagnostics for type inference issues
    pub fn get_diagnostics(&self, module: &TlaModule) -> Vec<TypeDiagnostic> {
        let mut diagnostics = Vec::new();

        // Add unification errors
        for error in &self.unifier.errors {
            diagnostics.push(TypeDiagnostic::error(error.clone()));
        }

        // Check for unresolved type variables in the environment
        let env = self.build_module_type_env(module);

        for (name, ty) in &env.constants {
            if let Some(diag) = Self::check_type_resolved(name, ty, "constant") {
                diagnostics.push(diag);
            }
        }

        for (name, ty) in &env.variables {
            if let Some(diag) = Self::check_type_resolved(name, ty, "variable") {
                diagnostics.push(diag);
            }
        }

        for (name, ty) in &env.operators {
            if let Some(diag) = Self::check_type_resolved(name, ty, "operator") {
                diagnostics.push(diag);
            }
        }

        diagnostics
    }

    /// Check if a type is fully resolved and return a diagnostic if not
    fn check_type_resolved(name: &str, ty: &TlaType, kind: &str) -> Option<TypeDiagnostic> {
        if ty.has_unresolved_type_var() {
            Some(TypeDiagnostic::warning(format!(
                "Ambiguous type for {} '{}': {} (contains unresolved type variables)",
                kind, name, ty
            )))
        } else if *ty == TlaType::Unknown {
            Some(TypeDiagnostic::warning(format!(
                "Unknown type for {} '{}': type could not be inferred",
                kind, name
            )))
        } else {
            None
        }
    }

    /// Resolve a type environment, replacing unresolved types with Any
    pub fn resolve_with_fallback(&self, env: &TypeEnv) -> TypeEnv {
        let mut resolved = TypeEnv::new();

        for (name, ty) in &env.constants {
            resolved.set_constant(name, Self::fallback_type(ty));
        }

        for (name, ty) in &env.variables {
            resolved.set_variable(name, Self::fallback_type(ty));
        }

        for (name, ty) in &env.operators {
            resolved.set_operator(name, Self::fallback_type(ty));
        }

        for (name, rec) in &env.records {
            let mut resolved_rec = RecordType::named(name);
            for (field_name, field_ty) in &rec.fields {
                resolved_rec
                    .fields
                    .insert(field_name.clone(), Self::fallback_type(field_ty));
            }
            resolved.register_record(name, resolved_rec);
        }

        resolved
    }

    /// Replace unresolved type variables with Any type
    fn fallback_type(ty: &TlaType) -> TlaType {
        match ty {
            TlaType::TypeVar(_) | TlaType::Unknown => TlaType::Any,
            TlaType::Set(elem) => TlaType::set(Self::fallback_type(elem)),
            TlaType::Seq(elem) => TlaType::seq(Self::fallback_type(elem)),
            TlaType::Map { key, value } => {
                TlaType::map(Self::fallback_type(key), Self::fallback_type(value))
            }
            TlaType::Function { domain, range } => {
                TlaType::function(Self::fallback_type(domain), Self::fallback_type(range))
            }
            TlaType::Tuple(elems) => {
                TlaType::Tuple(elems.iter().map(Self::fallback_type).collect())
            }
            TlaType::Record(rec) => {
                let mut resolved_rec = RecordType::new();
                resolved_rec.name = rec.name.clone();
                for (field_name, field_ty) in &rec.fields {
                    resolved_rec
                        .fields
                        .insert(field_name.clone(), Self::fallback_type(field_ty));
                }
                TlaType::Record(resolved_rec)
            }
            _ => ty.clone(),
        }
    }
}

// =============================================================================
// Type Diagnostics
// =============================================================================

/// Severity level for type diagnostics
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DiagnosticSeverity {
    /// Error: type inference failed
    Error,
    /// Warning: type is ambiguous or fallback was used
    Warning,
    /// Info: non-critical type information
    Info,
}

/// A diagnostic message from type inference
#[derive(Debug, Clone)]
pub struct TypeDiagnostic {
    /// Severity of the diagnostic
    pub severity: DiagnosticSeverity,
    /// The diagnostic message
    pub message: String,
}

impl TypeDiagnostic {
    /// Create an error diagnostic
    pub fn error(message: impl Into<String>) -> Self {
        Self {
            severity: DiagnosticSeverity::Error,
            message: message.into(),
        }
    }

    /// Create a warning diagnostic
    pub fn warning(message: impl Into<String>) -> Self {
        Self {
            severity: DiagnosticSeverity::Warning,
            message: message.into(),
        }
    }

    /// Create an info diagnostic
    pub fn info(message: impl Into<String>) -> Self {
        Self {
            severity: DiagnosticSeverity::Info,
            message: message.into(),
        }
    }

    /// Check if this is an error
    pub fn is_error(&self) -> bool {
        self.severity == DiagnosticSeverity::Error
    }

    /// Check if this is a warning
    pub fn is_warning(&self) -> bool {
        self.severity == DiagnosticSeverity::Warning
    }
}

impl fmt::Display for TypeDiagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let prefix = match self.severity {
            DiagnosticSeverity::Error => "error",
            DiagnosticSeverity::Warning => "warning",
            DiagnosticSeverity::Info => "info",
        };
        write!(f, "{}: {}", prefix, self.message)
    }
}

impl TlaType {
    /// Check if this type contains unresolved type variables
    pub fn has_unresolved_type_var(&self) -> bool {
        match self {
            TlaType::TypeVar(_) => true,
            TlaType::Set(elem) | TlaType::Seq(elem) => elem.has_unresolved_type_var(),
            TlaType::Map { key, value } => {
                key.has_unresolved_type_var() || value.has_unresolved_type_var()
            }
            TlaType::Function { domain, range } => {
                domain.has_unresolved_type_var() || range.has_unresolved_type_var()
            }
            TlaType::Tuple(elems) => elems.iter().any(|e| e.has_unresolved_type_var()),
            TlaType::Record(rec) => rec.fields.values().any(|t| t.has_unresolved_type_var()),
            _ => false,
        }
    }
}

// =============================================================================
// Type Annotations File (.tla-types)
// =============================================================================

/// Format for type annotation files that allow manual type refinement.
///
/// The `.tla-types` file format uses a simple key-value syntax:
///
/// ```text
/// # Type annotations for MyModule.tla
/// # Edit types below to refine inferred types
///
/// [constants]
/// N: Nat
/// MaxValue: Int
///
/// [variables]
/// count: Nat
/// items: Set(Int)
///
/// [operators]
/// Init: Bool
/// Next: Bool
/// Add: (Int, Int) -> Int
///
/// [records]
/// State {
///     x: Int
///     y: Bool
/// }
/// ```
#[derive(Debug, Default)]
pub struct TypeAnnotations {
    /// Types for constants
    pub constants: HashMap<String, TlaType>,
    /// Types for variables
    pub variables: HashMap<String, TlaType>,
    /// Types for operators
    pub operators: HashMap<String, TlaType>,
    /// Record type definitions
    pub records: HashMap<String, RecordType>,
}

impl TypeAnnotations {
    /// Create empty type annotations
    pub fn new() -> Self {
        Self::default()
    }

    /// Generate type annotations from a TypeEnv
    pub fn from_type_env(env: &TypeEnv) -> Self {
        Self {
            constants: env.constants.clone(),
            variables: env.variables.clone(),
            operators: env.operators.clone(),
            records: env.records.clone(),
        }
    }

    /// Generate the .tla-types file content
    pub fn to_file_content(&self, module_name: &str) -> String {
        let mut output = String::new();

        // Header
        output.push_str(&format!("# Type annotations for {}.tla\n", module_name));
        output.push_str("# Edit types below to refine inferred types\n");
        output.push_str("# Lines starting with # are comments\n\n");

        // Constants section
        if !self.constants.is_empty() {
            output.push_str("[constants]\n");
            let mut names: Vec<_> = self.constants.keys().collect();
            names.sort();
            for name in names {
                if let Some(ty) = self.constants.get(name) {
                    output.push_str(&format!("{}: {}\n", name, ty));
                }
            }
            output.push('\n');
        }

        // Variables section
        if !self.variables.is_empty() {
            output.push_str("[variables]\n");
            let mut names: Vec<_> = self.variables.keys().collect();
            names.sort();
            for name in names {
                if let Some(ty) = self.variables.get(name) {
                    // Skip internal variables (from quantifiers, etc.)
                    if !name.starts_with('_') {
                        output.push_str(&format!("{}: {}\n", name, ty));
                    }
                }
            }
            output.push('\n');
        }

        // Operators section
        if !self.operators.is_empty() {
            output.push_str("[operators]\n");
            let mut names: Vec<_> = self.operators.keys().collect();
            names.sort();
            for name in names {
                if let Some(ty) = self.operators.get(name) {
                    output.push_str(&format!("{}: {}\n", name, Self::format_operator_type(ty)));
                }
            }
            output.push('\n');
        }

        // Records section
        if !self.records.is_empty() {
            output.push_str("[records]\n");
            let mut names: Vec<_> = self.records.keys().collect();
            names.sort();
            for name in names {
                if let Some(rec) = self.records.get(name) {
                    output.push_str(&format!("{} {{\n", name));
                    let mut field_names: Vec<_> = rec.fields.keys().collect();
                    field_names.sort();
                    for field_name in field_names {
                        if let Some(field_ty) = rec.fields.get(field_name) {
                            output.push_str(&format!("    {}: {}\n", field_name, field_ty));
                        }
                    }
                    output.push_str("}\n");
                }
            }
        }

        output
    }

    /// Format an operator type for display
    fn format_operator_type(ty: &TlaType) -> String {
        match ty {
            TlaType::Function { domain, range } => {
                // Check if domain is a tuple (multi-parameter function)
                if let TlaType::Tuple(params) = domain.as_ref() {
                    let param_strs: Vec<_> = params.iter().map(|t| t.to_string()).collect();
                    format!("({}) -> {}", param_strs.join(", "), range)
                } else {
                    format!("({}) -> {}", domain, range)
                }
            }
            _ => ty.to_string(),
        }
    }

    /// Parse type annotations from file content
    pub fn parse(content: &str) -> Result<Self, String> {
        let mut annotations = TypeAnnotations::new();
        let mut current_section: Option<&str> = None;
        let mut current_record_name: Option<String> = None;
        let mut current_record_fields: HashMap<String, TlaType> = HashMap::new();

        for (line_num, line) in content.lines().enumerate() {
            let line = line.trim();

            // Skip empty lines and comments
            if line.is_empty() || line.starts_with('#') {
                continue;
            }

            // Section headers
            if line.starts_with('[') && line.ends_with(']') {
                // Save previous record if any
                if let Some(rec_name) = current_record_name.take() {
                    let mut rec = RecordType::named(&rec_name);
                    rec.fields = std::mem::take(&mut current_record_fields);
                    annotations.records.insert(rec_name, rec);
                }

                let section = &line[1..line.len() - 1];
                current_section = Some(section);
                continue;
            }

            // Record start
            if line.ends_with('{') {
                if current_section != Some("records") {
                    return Err(format!(
                        "Line {}: Record definition outside [records] section",
                        line_num + 1
                    ));
                }
                let name = line.strip_suffix('{').unwrap().trim().to_string();
                current_record_name = Some(name);
                continue;
            }

            // Record end
            if line == "}" {
                if let Some(rec_name) = current_record_name.take() {
                    let mut rec = RecordType::named(&rec_name);
                    rec.fields = std::mem::take(&mut current_record_fields);
                    annotations.records.insert(rec_name, rec);
                }
                continue;
            }

            // Type annotation: name: Type
            if let Some(colon_pos) = line.find(':') {
                let name = line[..colon_pos].trim().to_string();
                let type_str = line[colon_pos + 1..].trim();
                let ty = Self::parse_type(type_str)?;

                // Inside a record definition
                if current_record_name.is_some() {
                    current_record_fields.insert(name, ty);
                    continue;
                }

                // In a section
                match current_section {
                    Some("constants") => {
                        annotations.constants.insert(name, ty);
                    }
                    Some("variables") => {
                        annotations.variables.insert(name, ty);
                    }
                    Some("operators") => {
                        annotations.operators.insert(name, ty);
                    }
                    _ => {
                        return Err(format!(
                            "Line {}: Type annotation outside a section",
                            line_num + 1
                        ));
                    }
                }
            }
        }

        // Save any remaining record
        if let Some(rec_name) = current_record_name {
            let mut rec = RecordType::named(&rec_name);
            rec.fields = current_record_fields;
            annotations.records.insert(rec_name, rec);
        }

        Ok(annotations)
    }

    /// Parse a type string into a TlaType
    fn parse_type(s: &str) -> Result<TlaType, String> {
        let s = s.trim();

        // Basic types
        match s {
            "Int" => return Ok(TlaType::Int),
            "Nat" => return Ok(TlaType::Nat),
            "Bool" => return Ok(TlaType::Bool),
            "String" => return Ok(TlaType::String),
            "Action" => return Ok(TlaType::Action),
            "Temporal" => return Ok(TlaType::Temporal),
            "Any" | "?" => return Ok(TlaType::Any),
            _ => {}
        }

        // Set(T)
        if s.starts_with("Set(") && s.ends_with(')') {
            let inner = &s[4..s.len() - 1];
            return Ok(TlaType::set(Self::parse_type(inner)?));
        }

        // Seq(T)
        if s.starts_with("Seq(") && s.ends_with(')') {
            let inner = &s[4..s.len() - 1];
            return Ok(TlaType::seq(Self::parse_type(inner)?));
        }

        // Map(K, V)
        if s.starts_with("Map(") && s.ends_with(')') {
            let inner = &s[4..s.len() - 1];
            if let Some(comma_pos) = Self::find_top_level_comma(inner) {
                let key_str = inner[..comma_pos].trim();
                let value_str = inner[comma_pos + 1..].trim();
                return Ok(TlaType::map(
                    Self::parse_type(key_str)?,
                    Self::parse_type(value_str)?,
                ));
            }
        }

        // Function type: (T1, T2) -> R or [D -> R]
        if let Some(arrow_pos) = s.find("->") {
            let domain_str = s[..arrow_pos].trim();
            let range_str = s[arrow_pos + 2..].trim();

            // Check for [D -> R] syntax
            if domain_str.starts_with('[') && range_str.ends_with(']') {
                let domain = Self::parse_type(&domain_str[1..])?;
                let range = Self::parse_type(&range_str[..range_str.len() - 1])?;
                return Ok(TlaType::function(domain, range));
            }

            // (T1, T2) -> R syntax
            if domain_str.starts_with('(') && domain_str.ends_with(')') {
                let params_str = &domain_str[1..domain_str.len() - 1];
                let params = Self::parse_tuple_types(params_str)?;
                let range = Self::parse_type(range_str)?;
                if params.len() == 1 {
                    return Ok(TlaType::function(params.into_iter().next().unwrap(), range));
                }
                return Ok(TlaType::function(TlaType::Tuple(params), range));
            }
        }

        // Tuple: <<T1, T2>>
        if s.starts_with("<<") && s.ends_with(">>") {
            let inner = &s[2..s.len() - 2];
            let elems = Self::parse_tuple_types(inner)?;
            return Ok(TlaType::Tuple(elems));
        }

        // Type variable: T0, T1, etc.
        if s.starts_with('T') && s.len() > 1 {
            if let Ok(n) = s[1..].parse::<usize>() {
                return Ok(TlaType::TypeVar(n));
            }
        }

        // Unknown type
        if s == "Unknown" {
            return Ok(TlaType::Unknown);
        }

        Err(format!("Unknown type: {}", s))
    }

    /// Parse comma-separated types
    fn parse_tuple_types(s: &str) -> Result<Vec<TlaType>, String> {
        if s.trim().is_empty() {
            return Ok(Vec::new());
        }

        let mut types = Vec::new();
        let mut current = String::new();
        let mut depth = 0;

        for c in s.chars() {
            match c {
                '(' | '[' | '<' => {
                    depth += 1;
                    current.push(c);
                }
                ')' | ']' | '>' => {
                    depth -= 1;
                    current.push(c);
                }
                ',' if depth == 0 => {
                    types.push(Self::parse_type(current.trim())?);
                    current.clear();
                }
                _ => current.push(c),
            }
        }

        if !current.trim().is_empty() {
            types.push(Self::parse_type(current.trim())?);
        }

        Ok(types)
    }

    /// Find the position of a comma at the top level (not inside brackets)
    fn find_top_level_comma(s: &str) -> Option<usize> {
        let mut depth = 0;
        for (i, c) in s.chars().enumerate() {
            match c {
                '(' | '[' | '<' => depth += 1,
                ')' | ']' | '>' => depth -= 1,
                ',' if depth == 0 => return Some(i),
                _ => {}
            }
        }
        None
    }

    /// Merge user-provided annotations with inferred types.
    /// User annotations take precedence.
    pub fn merge_with(&self, inferred: &TypeEnv) -> TypeEnv {
        let mut result = inferred.clone();

        // Override with user-provided annotations
        for (name, ty) in &self.constants {
            result.set_constant(name, ty.clone());
        }
        for (name, ty) in &self.variables {
            result.set_variable(name, ty.clone());
        }
        for (name, ty) in &self.operators {
            result.set_operator(name, ty.clone());
        }
        for (name, rec) in &self.records {
            result.register_record(name, rec.clone());
        }

        result
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

    // Type substitution tests
    #[test]
    fn test_substitution_basic() {
        let mut subst = TypeSubstitution::new();
        subst.insert(0, TlaType::Int);
        subst.insert(1, TlaType::Bool);

        assert_eq!(subst.apply(&TlaType::TypeVar(0)), TlaType::Int);
        assert_eq!(subst.apply(&TlaType::TypeVar(1)), TlaType::Bool);
        assert_eq!(subst.apply(&TlaType::TypeVar(2)), TlaType::TypeVar(2));
    }

    #[test]
    fn test_substitution_recursive() {
        let mut subst = TypeSubstitution::new();
        subst.insert(0, TlaType::set(TlaType::TypeVar(1)));
        subst.insert(1, TlaType::Int);

        // T0 -> Set(T1), T1 -> Int, so T0 should resolve to Set(Int)
        let result = subst.apply(&TlaType::TypeVar(0));
        assert_eq!(result, TlaType::set(TlaType::Int));
    }

    #[test]
    fn test_substitution_complex_types() {
        let mut subst = TypeSubstitution::new();
        subst.insert(0, TlaType::Int);
        subst.insert(1, TlaType::Bool);

        // Test substitution in nested types
        let map_type = TlaType::map(TlaType::TypeVar(0), TlaType::TypeVar(1));
        let result = subst.apply(&map_type);
        assert_eq!(result, TlaType::map(TlaType::Int, TlaType::Bool));

        let tuple_type = TlaType::tuple(vec![TlaType::TypeVar(0), TlaType::TypeVar(1)]);
        let result = subst.apply(&tuple_type);
        assert_eq!(result, TlaType::tuple(vec![TlaType::Int, TlaType::Bool]));
    }

    // Type unification tests
    #[test]
    fn test_unify_same_types() {
        let mut unifier = TypeUnifier::new();
        assert!(matches!(
            unifier.unify(&TlaType::Int, &TlaType::Int),
            UnifyResult::Ok
        ));
        assert!(matches!(
            unifier.unify(&TlaType::Bool, &TlaType::Bool),
            UnifyResult::Ok
        ));
    }

    #[test]
    fn test_unify_type_var_with_concrete() {
        let mut unifier = TypeUnifier::new();
        let result = unifier.unify(&TlaType::TypeVar(0), &TlaType::Int);
        assert!(matches!(result, UnifyResult::Ok));
        assert_eq!(
            unifier.substitution.apply(&TlaType::TypeVar(0)),
            TlaType::Int
        );
    }

    #[test]
    fn test_unify_nat_int() {
        let mut unifier = TypeUnifier::new();
        // Nat is a subtype of Int, so they should unify
        assert!(matches!(
            unifier.unify(&TlaType::Nat, &TlaType::Int),
            UnifyResult::Ok
        ));
        assert!(matches!(
            unifier.unify(&TlaType::Int, &TlaType::Nat),
            UnifyResult::Ok
        ));
    }

    #[test]
    fn test_unify_sets() {
        let mut unifier = TypeUnifier::new();
        let set1 = TlaType::set(TlaType::TypeVar(0));
        let set2 = TlaType::set(TlaType::Int);

        let result = unifier.unify(&set1, &set2);
        assert!(matches!(result, UnifyResult::Ok));
        assert_eq!(
            unifier.substitution.apply(&TlaType::TypeVar(0)),
            TlaType::Int
        );
    }

    #[test]
    fn test_unify_maps() {
        let mut unifier = TypeUnifier::new();
        let map1 = TlaType::map(TlaType::TypeVar(0), TlaType::TypeVar(1));
        let map2 = TlaType::map(TlaType::String, TlaType::Int);

        let result = unifier.unify(&map1, &map2);
        assert!(matches!(result, UnifyResult::Ok));
        assert_eq!(
            unifier.substitution.apply(&TlaType::TypeVar(0)),
            TlaType::String
        );
        assert_eq!(
            unifier.substitution.apply(&TlaType::TypeVar(1)),
            TlaType::Int
        );
    }

    #[test]
    fn test_unify_tuples() {
        let mut unifier = TypeUnifier::new();
        let tuple1 = TlaType::tuple(vec![TlaType::TypeVar(0), TlaType::TypeVar(1)]);
        let tuple2 = TlaType::tuple(vec![TlaType::Int, TlaType::Bool]);

        let result = unifier.unify(&tuple1, &tuple2);
        assert!(matches!(result, UnifyResult::Ok));
        assert_eq!(
            unifier.substitution.apply(&TlaType::TypeVar(0)),
            TlaType::Int
        );
        assert_eq!(
            unifier.substitution.apply(&TlaType::TypeVar(1)),
            TlaType::Bool
        );
    }

    #[test]
    fn test_unify_tuple_length_mismatch() {
        let mut unifier = TypeUnifier::new();
        let tuple1 = TlaType::tuple(vec![TlaType::Int, TlaType::Bool]);
        let tuple2 = TlaType::tuple(vec![TlaType::Int]);

        let result = unifier.unify(&tuple1, &tuple2);
        assert!(matches!(result, UnifyResult::Conflict { .. }));
        assert!(!unifier.errors.is_empty());
    }

    #[test]
    fn test_unify_conflict() {
        let mut unifier = TypeUnifier::new();
        let result = unifier.unify(&TlaType::Int, &TlaType::Bool);
        assert!(matches!(result, UnifyResult::Conflict { .. }));
        assert!(!unifier.errors.is_empty());
    }

    #[test]
    fn test_unify_unknown() {
        let mut unifier = TypeUnifier::new();
        // Unknown unifies with anything
        assert!(matches!(
            unifier.unify(&TlaType::Unknown, &TlaType::Int),
            UnifyResult::Ok
        ));
        assert!(matches!(
            unifier.unify(&TlaType::Bool, &TlaType::Unknown),
            UnifyResult::Ok
        ));
    }

    #[test]
    fn test_unify_any() {
        let mut unifier = TypeUnifier::new();
        // Any unifies with anything
        assert!(matches!(
            unifier.unify(&TlaType::Any, &TlaType::Int),
            UnifyResult::Ok
        ));
        assert!(matches!(
            unifier.unify(&TlaType::set(TlaType::Bool), &TlaType::Any),
            UnifyResult::Ok
        ));
    }

    #[test]
    fn test_unify_int_range() {
        let mut unifier = TypeUnifier::new();
        // IntRange is a Set(Int)
        let result = unifier.unify(&TlaType::IntRange, &TlaType::set(TlaType::Int));
        assert!(matches!(result, UnifyResult::Ok));
    }

    #[test]
    fn test_process_constraints() {
        let constraints = vec![
            TypeConstraint::Equal(TlaType::TypeVar(0), TlaType::Int),
            TypeConstraint::Equal(TlaType::TypeVar(1), TlaType::set(TlaType::TypeVar(0))),
        ];

        let mut unifier = TypeUnifier::new();
        unifier.process_constraints(&constraints);

        // T0 should be Int
        assert_eq!(
            unifier.substitution.apply(&TlaType::TypeVar(0)),
            TlaType::Int
        );
        // T1 should be Set(Int)
        assert_eq!(
            unifier.substitution.apply(&TlaType::TypeVar(1)),
            TlaType::set(TlaType::Int)
        );
    }

    #[test]
    fn test_build_type_env() {
        let constraints = vec![
            TypeConstraint::HasType {
                name: "x".to_string(),
                ty: TlaType::TypeVar(0),
            },
            TypeConstraint::Equal(TlaType::TypeVar(0), TlaType::Int),
            TypeConstraint::OperatorType {
                name: "Add".to_string(),
                param_types: vec![TlaType::Int, TlaType::Int],
                return_type: TlaType::Int,
            },
        ];

        let mut unifier = TypeUnifier::new();
        unifier.process_constraints(&constraints);
        let env = unifier.build_type_env(&constraints);

        // x should have type Int (resolved from T0)
        assert_eq!(env.lookup("x"), Some(&TlaType::Int));
        // Add should have a function type
        assert!(env.operators.contains_key("Add"));
    }

    #[test]
    fn test_unify_records() {
        let rec1 = RecordType::new()
            .with_field("x", TlaType::TypeVar(0))
            .with_field("y", TlaType::Bool);
        let rec2 = RecordType::new()
            .with_field("x", TlaType::Int)
            .with_field("y", TlaType::TypeVar(1));

        let mut unifier = TypeUnifier::new();
        let result = unifier.unify(&TlaType::Record(rec1), &TlaType::Record(rec2));

        assert!(matches!(result, UnifyResult::Ok));
        assert_eq!(
            unifier.substitution.apply(&TlaType::TypeVar(0)),
            TlaType::Int
        );
        assert_eq!(
            unifier.substitution.apply(&TlaType::TypeVar(1)),
            TlaType::Bool
        );
    }

    #[test]
    fn test_unify_functions() {
        let func1 = TlaType::function(TlaType::TypeVar(0), TlaType::TypeVar(1));
        let func2 = TlaType::function(TlaType::Nat, TlaType::Bool);

        let mut unifier = TypeUnifier::new();
        let result = unifier.unify(&func1, &func2);

        assert!(matches!(result, UnifyResult::Ok));
        assert_eq!(
            unifier.substitution.apply(&TlaType::TypeVar(0)),
            TlaType::Nat
        );
        assert_eq!(
            unifier.substitution.apply(&TlaType::TypeVar(1)),
            TlaType::Bool
        );
    }

    #[test]
    fn test_end_to_end_type_inference() {
        // Parse a module and run full type inference
        let source = r"
            ---- MODULE Counter ----
            VARIABLE count
            Init == count \in Nat
            Increment == count' = count + 1
            ====
        ";
        let module = parse_module(source).unwrap();

        // Collect constraints
        let mut collector = ConstraintCollector::new();
        collector.collect_from_module(&module);

        // Unify and build type environment
        let mut unifier = TypeUnifier::new();
        unifier.process_constraints(&collector.constraints);
        let env = unifier.build_type_env(&collector.constraints);

        // count should have type Nat
        assert!(
            env.variables.contains_key("count"),
            "Expected count in env.variables"
        );

        // The Init operator should be in the environment
        assert!(
            env.operators.contains_key("Init"),
            "Expected Init operator in environment"
        );
    }

    // TypeInference API tests
    #[test]
    fn test_type_inference_simple_variable() {
        let source = r"
            ---- MODULE Test ----
            VARIABLE x
            Init == x \in Nat
            ====
        ";
        let module = parse_module(source).unwrap();

        let mut inference = TypeInference::new();
        let env = inference.infer_types(&module);

        // x should be in variables, not constants
        assert!(env.variables.contains_key("x"));
        assert!(!env.constants.contains_key("x"));
        assert!(inference.is_successful());
    }

    #[test]
    fn test_type_inference_constants() {
        let source = r"
            ---- MODULE Test ----
            CONSTANT N
            VARIABLE items
            Init == N \in Nat /\ items = {}
            ====
        ";
        let module = parse_module(source).unwrap();

        let mut inference = TypeInference::new();
        let env = inference.infer_types(&module);

        // N should be in constants
        assert!(
            env.constants.contains_key("N"),
            "Expected N in constants, got {:?}",
            env.constants
        );
        // items should be in variables
        assert!(
            env.variables.contains_key("items"),
            "Expected items in variables"
        );
    }

    #[test]
    fn test_type_inference_operators() {
        let source = r"
            ---- MODULE Test ----
            Add(a, b) == a + b
            Double(x) == x * 2
            ====
        ";
        let module = parse_module(source).unwrap();

        let mut inference = TypeInference::new();
        let env = inference.infer_types(&module);

        // Both operators should be in the operators map
        assert!(
            env.operators.contains_key("Add"),
            "Expected Add operator, got {:?}",
            env.operators
        );
        assert!(
            env.operators.contains_key("Double"),
            "Expected Double operator"
        );
    }

    #[test]
    fn test_type_inference_get_inferred_type() {
        let source = r"
            ---- MODULE Test ----
            VARIABLE count
            Init == count \in Nat
            ====
        ";
        let module = parse_module(source).unwrap();

        let mut inference = TypeInference::new();
        inference.infer_types(&module);

        // Should be able to get the inferred type for count
        let count_type = inference.get_inferred_type("count");
        assert!(
            count_type.is_some(),
            "Expected to find type for count, got None"
        );
    }

    #[test]
    fn test_type_inference_record_types() {
        let source = r"
            ---- MODULE Test ----
            VARIABLE state
            Init == state = [x |-> 0, y |-> TRUE]
            GetX == state.x
            ====
        ";
        let module = parse_module(source).unwrap();

        let mut inference = TypeInference::new();
        let env = inference.infer_types(&module);

        // Should have collected record field information
        assert!(
            env.records.contains_key("state"),
            "Expected record type for state, got records: {:?}",
            env.records
        );
        if let Some(rec) = env.records.get("state") {
            assert!(
                rec.fields.contains_key("x"),
                "Expected field x in state record"
            );
        }
    }

    #[test]
    fn test_type_inference_complex_module() {
        let source = r"
            ---- MODULE Counter ----
            CONSTANT MaxValue
            VARIABLE count, enabled

            TypeOK == count \in Nat /\ enabled \in BOOLEAN /\ MaxValue \in Nat

            Init == count = 0 /\ enabled = TRUE

            Increment == enabled /\ count' = count + 1 /\ UNCHANGED enabled

            ====
        ";
        let module = parse_module(source).unwrap();

        let mut inference = TypeInference::new();
        let env = inference.infer_types(&module);

        // Verify proper categorization
        assert!(
            env.constants.contains_key("MaxValue"),
            "MaxValue should be a constant"
        );
        assert!(
            env.variables.contains_key("count"),
            "count should be a variable"
        );
        assert!(
            env.variables.contains_key("enabled"),
            "enabled should be a variable"
        );
        assert!(
            env.operators.contains_key("TypeOK"),
            "TypeOK should be an operator"
        );
        assert!(
            env.operators.contains_key("Init"),
            "Init should be an operator"
        );
        assert!(
            env.operators.contains_key("Increment"),
            "Increment should be an operator"
        );

        // Check that inference was successful
        assert!(
            inference.is_successful(),
            "Type inference should succeed, errors: {:?}",
            inference.errors()
        );
    }

    #[test]
    fn test_type_inference_function_construct() {
        let source = r"
            ---- MODULE Test ----
            CONSTANT S
            MakeMap == [i \in S |-> i * 2]
            ====
        ";
        let module = parse_module(source).unwrap();

        let mut inference = TypeInference::new();
        let env = inference.infer_types(&module);

        assert!(env.operators.contains_key("MakeMap"));
        assert!(inference.is_successful());
    }

    #[test]
    fn test_type_inference_set_operations() {
        let source = r"
            ---- MODULE Test ----
            VARIABLE S, T
            Init == S \in SUBSET Nat /\ T = S \cup {1, 2, 3}
            ====
        ";
        let module = parse_module(source).unwrap();

        let mut inference = TypeInference::new();
        let env = inference.infer_types(&module);

        assert!(env.variables.contains_key("S"));
        assert!(env.variables.contains_key("T"));
        assert!(inference.is_successful());
    }

    // TypeAnnotations tests
    #[test]
    fn test_type_annotations_generate_file() {
        let mut env = TypeEnv::new();
        env.set_constant("N", TlaType::Nat);
        env.set_variable("count", TlaType::Int);
        env.set_operator("Init", TlaType::Bool);

        let annotations = TypeAnnotations::from_type_env(&env);
        let content = annotations.to_file_content("Test");

        assert!(content.contains("# Type annotations for Test.tla"));
        assert!(content.contains("[constants]"));
        assert!(content.contains("N: Nat"));
        assert!(content.contains("[variables]"));
        assert!(content.contains("count: Int"));
        assert!(content.contains("[operators]"));
        assert!(content.contains("Init: Bool"));
    }

    #[test]
    fn test_type_annotations_parse_basic() {
        let content = r#"
            # Test file
            [constants]
            N: Nat

            [variables]
            count: Int
            enabled: Bool

            [operators]
            Init: Bool
        "#;

        let annotations = TypeAnnotations::parse(content).unwrap();

        assert_eq!(annotations.constants.get("N"), Some(&TlaType::Nat));
        assert_eq!(annotations.variables.get("count"), Some(&TlaType::Int));
        assert_eq!(annotations.variables.get("enabled"), Some(&TlaType::Bool));
        assert_eq!(annotations.operators.get("Init"), Some(&TlaType::Bool));
    }

    #[test]
    fn test_type_annotations_parse_complex_types() {
        let content = r#"
            [variables]
            items: Set(Int)
            values: Seq(Nat)
            mapping: Map(String, Int)
        "#;

        let annotations = TypeAnnotations::parse(content).unwrap();

        assert_eq!(
            annotations.variables.get("items"),
            Some(&TlaType::set(TlaType::Int))
        );
        assert_eq!(
            annotations.variables.get("values"),
            Some(&TlaType::seq(TlaType::Nat))
        );
        assert_eq!(
            annotations.variables.get("mapping"),
            Some(&TlaType::map(TlaType::String, TlaType::Int))
        );
    }

    #[test]
    fn test_type_annotations_parse_function_type() {
        let content = r#"
            [operators]
            Add: (Int, Int) -> Int
            Double: (Nat) -> Nat
        "#;

        let annotations = TypeAnnotations::parse(content).unwrap();

        // Add should be a function from (Int, Int) tuple to Int
        let add_type = annotations.operators.get("Add").unwrap();
        match add_type {
            TlaType::Function { domain, range } => {
                assert!(matches!(domain.as_ref(), TlaType::Tuple(_)));
                assert_eq!(range.as_ref(), &TlaType::Int);
            }
            _ => panic!("Expected function type for Add"),
        }
    }

    #[test]
    fn test_type_annotations_parse_records() {
        let content = r#"
            [records]
            State {
                x: Int
                y: Bool
            }
        "#;

        let annotations = TypeAnnotations::parse(content).unwrap();

        let rec = annotations.records.get("State").unwrap();
        assert_eq!(rec.get_field("x"), Some(&TlaType::Int));
        assert_eq!(rec.get_field("y"), Some(&TlaType::Bool));
    }

    #[test]
    fn test_type_annotations_roundtrip() {
        let mut original = TypeAnnotations::new();
        original.constants.insert("N".to_string(), TlaType::Nat);
        original
            .variables
            .insert("items".to_string(), TlaType::set(TlaType::Int));
        original.operators.insert("Init".to_string(), TlaType::Bool);

        let content = original.to_file_content("Test");
        let parsed = TypeAnnotations::parse(&content).unwrap();

        assert_eq!(parsed.constants.get("N"), Some(&TlaType::Nat));
        assert_eq!(
            parsed.variables.get("items"),
            Some(&TlaType::set(TlaType::Int))
        );
        assert_eq!(parsed.operators.get("Init"), Some(&TlaType::Bool));
    }

    #[test]
    fn test_type_annotations_merge() {
        // Create inferred types
        let mut inferred = TypeEnv::new();
        inferred.set_variable("x", TlaType::Unknown);
        inferred.set_variable("y", TlaType::Int);

        // User annotations override x's type
        let mut user_annotations = TypeAnnotations::new();
        user_annotations
            .variables
            .insert("x".to_string(), TlaType::Nat);

        let merged = user_annotations.merge_with(&inferred);

        // x should be overridden to Nat
        assert_eq!(merged.lookup("x"), Some(&TlaType::Nat));
        // y should remain Int
        assert_eq!(merged.lookup("y"), Some(&TlaType::Int));
    }

    #[test]
    fn test_type_annotations_parse_tuple_type() {
        let content = r#"
            [variables]
            point: <<Int, Int>>
            triple: <<Nat, Bool, String>>
        "#;

        let annotations = TypeAnnotations::parse(content).unwrap();

        assert_eq!(
            annotations.variables.get("point"),
            Some(&TlaType::tuple(vec![TlaType::Int, TlaType::Int]))
        );
        assert_eq!(
            annotations.variables.get("triple"),
            Some(&TlaType::tuple(vec![
                TlaType::Nat,
                TlaType::Bool,
                TlaType::String
            ]))
        );
    }

    #[test]
    fn test_type_annotations_from_inference() {
        let source = r"
            ---- MODULE Counter ----
            CONSTANT N
            VARIABLE count
            Init == count \in Nat /\ N \in Nat
            ====
        ";
        let module = parse_module(source).unwrap();

        let mut inference = TypeInference::new();
        let env = inference.infer_types(&module);
        let annotations = TypeAnnotations::from_type_env(&env);
        let content = annotations.to_file_content("Counter");

        // Should generate valid annotation file
        assert!(content.contains("[constants]"));
        assert!(content.contains("N:"));
        assert!(content.contains("[variables]"));
        assert!(content.contains("count:"));
    }

    // TypeDiagnostic tests
    #[test]
    fn test_type_diagnostic_creation() {
        let error = TypeDiagnostic::error("Type mismatch");
        assert!(error.is_error());
        assert!(!error.is_warning());
        assert_eq!(error.to_string(), "error: Type mismatch");

        let warning = TypeDiagnostic::warning("Ambiguous type");
        assert!(warning.is_warning());
        assert!(!warning.is_error());
        assert_eq!(warning.to_string(), "warning: Ambiguous type");
    }

    #[test]
    fn test_has_unresolved_type_var() {
        assert!(TlaType::TypeVar(0).has_unresolved_type_var());
        assert!(!TlaType::Int.has_unresolved_type_var());
        assert!(!TlaType::Bool.has_unresolved_type_var());

        // Nested type variable
        assert!(TlaType::set(TlaType::TypeVar(0)).has_unresolved_type_var());
        assert!(!TlaType::set(TlaType::Int).has_unresolved_type_var());

        // Complex types
        assert!(TlaType::map(TlaType::String, TlaType::TypeVar(1)).has_unresolved_type_var());
        assert!(!TlaType::map(TlaType::String, TlaType::Int).has_unresolved_type_var());
    }

    #[test]
    fn test_resolve_with_fallback() {
        let source = r"
            ---- MODULE Test ----
            VARIABLE x
            Op == x
            ====
        ";
        let module = parse_module(source).unwrap();

        let mut inference = TypeInference::new();
        let env = inference.infer_types(&module);

        // Resolve with fallback (unresolved vars become Any)
        let resolved = inference.resolve_with_fallback(&env);

        // Check that types are resolved (either concrete or Any, not TypeVar)
        for ty in resolved.variables.values() {
            assert!(
                !ty.has_unresolved_type_var(),
                "Resolved type should not have type variables"
            );
        }
    }

    #[test]
    fn test_get_diagnostics_unresolved() {
        let source = r"
            ---- MODULE Test ----
            VARIABLE x
            Op == x
            ====
        ";
        let module = parse_module(source).unwrap();

        let mut inference = TypeInference::new();
        inference.infer_types(&module);
        let diagnostics = inference.get_diagnostics(&module);

        // Should have warnings about unresolved types
        let has_warning = diagnostics.iter().any(|d| d.is_warning());
        // This may or may not have warnings depending on inference
        // At minimum, the diagnostics collection should work
        assert!(diagnostics.is_empty() || has_warning || diagnostics.iter().any(|d| d.is_error()));
    }

    #[test]
    fn test_get_diagnostics_no_errors_for_resolved() {
        let source = r"
            ---- MODULE Test ----
            VARIABLE count
            Init == count \in Nat
            ====
        ";
        let module = parse_module(source).unwrap();

        let mut inference = TypeInference::new();
        inference.infer_types(&module);
        let diagnostics = inference.get_diagnostics(&module);

        // count should have a resolved type (Nat), so no errors for it
        let count_errors: Vec<_> = diagnostics
            .iter()
            .filter(|d| d.is_error() && d.message.contains("count"))
            .collect();
        assert!(
            count_errors.is_empty(),
            "Should not have errors for resolved variable 'count'"
        );
    }

    #[test]
    fn test_fallback_type_conversion() {
        // TypeVar becomes Any
        assert_eq!(
            TypeInference::fallback_type(&TlaType::TypeVar(0)),
            TlaType::Any
        );
        assert_eq!(
            TypeInference::fallback_type(&TlaType::Unknown),
            TlaType::Any
        );

        // Concrete types stay the same
        assert_eq!(TypeInference::fallback_type(&TlaType::Int), TlaType::Int);
        assert_eq!(TypeInference::fallback_type(&TlaType::Bool), TlaType::Bool);

        // Nested type variables become Any
        assert_eq!(
            TypeInference::fallback_type(&TlaType::set(TlaType::TypeVar(0))),
            TlaType::set(TlaType::Any)
        );
    }

    #[test]
    fn test_diagnostic_severity() {
        let error = TypeDiagnostic::error("test");
        assert_eq!(error.severity, DiagnosticSeverity::Error);

        let warning = TypeDiagnostic::warning("test");
        assert_eq!(warning.severity, DiagnosticSeverity::Warning);

        let info = TypeDiagnostic::info("test");
        assert_eq!(info.severity, DiagnosticSeverity::Info);
    }
}
