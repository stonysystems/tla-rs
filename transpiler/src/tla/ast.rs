//! TLA+ Abstract Syntax Tree definitions.
//!
//! This module defines the AST types used to represent parsed TLA+ specifications.
//! The AST closely mirrors TLA+ syntax and semantics.

use crate::tla::tokenizer::Span;

/// A complete TLA+ module
#[derive(Debug, Clone, PartialEq)]
pub struct TlaModule {
    /// Module name (from `---- MODULE Name ----`)
    pub name: String,
    /// Extended modules (from `EXTENDS ...`)
    pub extends: Vec<String>,
    /// Constant declarations (from `CONSTANT ...` or `CONSTANTS ...`)
    pub constants: Vec<TlaConstantDecl>,
    /// Variable declarations (from `VARIABLE ...` or `VARIABLES ...`)
    pub variables: Vec<String>,
    /// Assumptions (from `ASSUME ...`)
    pub assumptions: Vec<TlaExpr>,
    /// Operator definitions
    pub operators: Vec<TlaOperator>,
    /// Theorems (from `THEOREM ...`)
    pub theorems: Vec<TlaTheorem>,
    /// Module instances (from `INSTANCE ...`)
    pub instances: Vec<TlaInstance>,
    /// Span in source
    pub span: Option<Span>,
}

impl TlaModule {
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            extends: Vec::new(),
            constants: Vec::new(),
            variables: Vec::new(),
            assumptions: Vec::new(),
            operators: Vec::new(),
            theorems: Vec::new(),
            instances: Vec::new(),
            span: None,
        }
    }
}

/// A constant declaration, which may have a type constraint
#[derive(Debug, Clone, PartialEq)]
pub struct TlaConstantDecl {
    /// Constant name
    pub name: String,
    /// Optional type constraint (for typed TLA+)
    pub type_constraint: Option<TlaExpr>,
}

impl TlaConstantDecl {
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            type_constraint: None,
        }
    }
}

/// An operator definition
#[derive(Debug, Clone, PartialEq)]
pub struct TlaOperator {
    /// Operator name
    pub name: String,
    /// Parameters (empty for constants)
    pub params: Vec<TlaParam>,
    /// Operator body
    pub body: TlaExpr,
    /// Whether this operator is marked RECURSIVE
    pub is_recursive: bool,
    /// Whether this operator is LOCAL
    pub is_local: bool,
    /// Span in source
    pub span: Option<Span>,
}

impl TlaOperator {
    pub fn new(name: impl Into<String>, body: TlaExpr) -> Self {
        Self {
            name: name.into(),
            params: Vec::new(),
            body,
            is_recursive: false,
            is_local: false,
            span: None,
        }
    }

    pub fn with_params(mut self, params: Vec<TlaParam>) -> Self {
        self.params = params;
        self
    }

    pub fn recursive(mut self) -> Self {
        self.is_recursive = true;
        self
    }

    pub fn local(mut self) -> Self {
        self.is_local = true;
        self
    }
}

/// An operator parameter
#[derive(Debug, Clone, PartialEq)]
pub struct TlaParam {
    /// Parameter name
    pub name: String,
    /// Arity for higher-order parameters (0 for regular params)
    pub arity: usize,
}

impl TlaParam {
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            arity: 0,
        }
    }

    pub fn higher_order(name: impl Into<String>, arity: usize) -> Self {
        Self {
            name: name.into(),
            arity,
        }
    }
}

/// A theorem declaration
#[derive(Debug, Clone, PartialEq)]
pub struct TlaTheorem {
    /// Optional theorem name
    pub name: Option<String>,
    /// Theorem body (the formula being asserted)
    pub body: TlaExpr,
    /// Span in source
    pub span: Option<Span>,
}

/// A module instance
#[derive(Debug, Clone, PartialEq)]
pub struct TlaInstance {
    /// Optional local name for the instance
    pub local_name: Option<String>,
    /// Module being instantiated
    pub module_name: String,
    /// Parameter substitutions
    pub substitutions: Vec<(String, TlaExpr)>,
    /// Whether this is a LOCAL instance
    pub is_local: bool,
    /// Span in source
    pub span: Option<Span>,
}

/// TLA+ expression
#[derive(Debug, Clone, PartialEq)]
pub enum TlaExpr {
    // Identifiers and literals
    /// Variable or constant reference: `x`, `MyConst`
    Ident(String),
    /// Primed variable: `x'`
    Prime(Box<TlaExpr>),
    /// Numeric literal
    Number(TlaNumber),
    /// String literal
    String(String),
    /// Boolean literal: TRUE or FALSE
    Bool(bool),

    // Operators
    /// Binary operation: `a + b`, `a \in S`, etc.
    BinOp {
        op: TlaBinOp,
        left: Box<TlaExpr>,
        right: Box<TlaExpr>,
    },
    /// Unary operation: `~P`, `DOMAIN f`, etc.
    UnaryOp {
        op: TlaUnaryOp,
        operand: Box<TlaExpr>,
    },

    // Function/operator application
    /// Operator application: `Op(a, b)`
    OpApply {
        op: Box<TlaExpr>,
        args: Vec<TlaExpr>,
    },
    /// Function application: `f[x]`
    FnApply {
        func: Box<TlaExpr>,
        arg: Box<TlaExpr>,
    },

    // Sets
    /// Set enumeration: `{1, 2, 3}`
    SetEnum(Vec<TlaExpr>),
    /// Set comprehension with filter: `{x \in S : P(x)}`
    SetFilter {
        var: String,
        set: Box<TlaExpr>,
        filter: Box<TlaExpr>,
    },
    /// Set comprehension with map: `{f(x) : x \in S}`
    SetMap {
        expr: Box<TlaExpr>,
        var: String,
        set: Box<TlaExpr>,
    },

    // Functions
    /// Function construction: `[x \in S |-> f(x)]`
    FnConstruct {
        var: String,
        domain: Box<TlaExpr>,
        body: Box<TlaExpr>,
    },
    /// Function update (EXCEPT): `[f EXCEPT ![i] = v]`
    FnExcept {
        func: Box<TlaExpr>,
        updates: Vec<TlaExceptUpdate>,
    },
    /// Function set type: `[Domain -> Range]` (set of all functions from Domain to Range)
    FnSet {
        domain: Box<TlaExpr>,
        range: Box<TlaExpr>,
    },

    // Records
    /// Record construction: `[a |-> 1, b |-> 2]`
    Record(Vec<(String, TlaExpr)>),
    /// Record set: `[holder: 1..NP, clean: BOOLEAN]` — the set of all records
    /// with those fields drawn from those sets. Distinct from `Record`, which
    /// is a single record value.
    RecordSet(Vec<(String, TlaExpr)>),
    /// Record field access: `r.field`
    RecordAccess { record: Box<TlaExpr>, field: String },

    // Tuples/Sequences
    /// Tuple/sequence: `<<a, b, c>>`
    Tuple(Vec<TlaExpr>),

    // Quantifiers
    /// Universal quantifier: `\A x \in S : P(x)`
    Forall {
        vars: Vec<TlaQuantBound>,
        body: Box<TlaExpr>,
    },
    /// Existential quantifier: `\E x \in S : P(x)`
    Exists {
        vars: Vec<TlaQuantBound>,
        body: Box<TlaExpr>,
    },
    /// Choose operator: `CHOOSE x \in S : P(x)`
    Choose {
        var: String,
        set: Option<Box<TlaExpr>>,
        body: Box<TlaExpr>,
    },

    // Control flow
    /// If-then-else: `IF c THEN a ELSE b`
    IfThenElse {
        cond: Box<TlaExpr>,
        then_expr: Box<TlaExpr>,
        else_expr: Box<TlaExpr>,
    },
    /// Case expression
    Case {
        arms: Vec<(TlaExpr, TlaExpr)>,
        other: Option<Box<TlaExpr>>,
    },
    /// Let-in: `LET x == e1 IN e2`
    LetIn {
        defs: Vec<TlaOperator>,
        body: Box<TlaExpr>,
    },

    // Action operators
    /// UNCHANGED: `UNCHANGED <<x, y>>`
    Unchanged(Vec<TlaExpr>),
    /// ENABLED: `ENABLED A`
    Enabled(Box<TlaExpr>),

    // Temporal operators
    /// Always: `[]P`
    Always(Box<TlaExpr>),
    /// Eventually: `<>P`
    Eventually(Box<TlaExpr>),
    /// Leads-to: `P ~> Q`
    LeadsTo {
        left: Box<TlaExpr>,
        right: Box<TlaExpr>,
    },
    /// Weak fairness: `WF_vars(A)`
    WeakFairness {
        vars: Box<TlaExpr>,
        action: Box<TlaExpr>,
    },
    /// Strong fairness: `SF_vars(A)`
    StrongFairness {
        vars: Box<TlaExpr>,
        action: Box<TlaExpr>,
    },
}

impl TlaExpr {
    /// Create an identifier expression
    pub fn ident(name: impl Into<String>) -> Self {
        TlaExpr::Ident(name.into())
    }

    /// Create a number expression
    pub fn number(value: i64) -> Self {
        TlaExpr::Number(TlaNumber::Decimal(value.to_string()))
    }

    /// Create a boolean expression
    pub fn bool(value: bool) -> Self {
        TlaExpr::Bool(value)
    }

    /// Create a string expression
    pub fn string(value: impl Into<String>) -> Self {
        TlaExpr::String(value.into())
    }

    /// Create a binary operation
    pub fn binop(op: TlaBinOp, left: TlaExpr, right: TlaExpr) -> Self {
        TlaExpr::BinOp {
            op,
            left: Box::new(left),
            right: Box::new(right),
        }
    }

    /// Create a unary operation
    pub fn unary(op: TlaUnaryOp, operand: TlaExpr) -> Self {
        TlaExpr::UnaryOp {
            op,
            operand: Box::new(operand),
        }
    }

    /// Create a primed expression
    pub fn prime(expr: TlaExpr) -> Self {
        TlaExpr::Prime(Box::new(expr))
    }
}

/// A number literal with its original representation
#[derive(Debug, Clone, PartialEq)]
pub enum TlaNumber {
    /// Decimal number: `42`
    Decimal(String),
    /// Binary number: `\b1010`
    Binary(String),
    /// Octal number: `\o777`
    Octal(String),
    /// Hexadecimal number: `\hFF`
    Hex(String),
}

impl TlaNumber {
    /// Parse the number to an i64 value
    pub fn to_i64(&self) -> Option<i64> {
        match self {
            TlaNumber::Decimal(s) => s.parse().ok(),
            TlaNumber::Binary(s) => {
                let digits = s.strip_prefix("0b").unwrap_or(s);
                i64::from_str_radix(digits, 2).ok()
            }
            TlaNumber::Octal(s) => {
                let digits = s.strip_prefix("0o").unwrap_or(s);
                i64::from_str_radix(digits, 8).ok()
            }
            TlaNumber::Hex(s) => {
                let digits = s.strip_prefix("0x").unwrap_or(s);
                i64::from_str_radix(digits, 16).ok()
            }
        }
    }
}

/// Binary operators
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TlaBinOp {
    // Logical
    And,     // /\
    Or,      // \/
    Implies, // =>
    Iff,     // <=>

    // Set operations
    In,        // \in
    NotIn,     // \notin
    Subseteq,  // \subseteq
    Cup,       // \cup (union)
    Cap,       // \cap (intersection)
    Setminus,  // \ (set difference)
    CrossProd, // \X (Cartesian product)

    // Arithmetic
    Plus,
    Minus,
    Times,
    Div,    // \div (integer division)
    Mod,    // \mod (modulo)
    Slash,  // / (real division)
    Caret,  // ^ (exponentiation)
    DotDot, // .. (range)

    // Comparison
    Eq,  // =
    Neq, // # or /=
    Lt,  // <
    Gt,  // >
    Leq, // <= or =<
    Geq, // >=

    // Sequencing (for actions)
    Compose, // \cdot (action composition)
}

/// Unary operators
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TlaUnaryOp {
    // Logical
    Not, // ~ or \lnot

    // Set
    Subset, // SUBSET (power set)
    Union,  // UNION (generalized union)
    Domain, // DOMAIN (function domain)

    // Arithmetic
    Neg, // - (negation)
}

/// A bound variable in a quantifier
#[derive(Debug, Clone, PartialEq)]
pub struct TlaQuantBound {
    /// Variable name
    pub var: String,
    /// Bounding set (optional for unbounded quantification)
    pub set: Option<TlaExpr>,
}

impl TlaQuantBound {
    pub fn new(var: impl Into<String>, set: TlaExpr) -> Self {
        Self {
            var: var.into(),
            set: Some(set),
        }
    }

    pub fn unbounded(var: impl Into<String>) -> Self {
        Self {
            var: var.into(),
            set: None,
        }
    }
}

/// An update in an EXCEPT expression
#[derive(Debug, Clone, PartialEq)]
pub struct TlaExceptUpdate {
    /// Path to update: `![i]` or `!.field` or `![i].field`
    pub path: Vec<TlaExceptPath>,
    /// New value
    pub value: TlaExpr,
}

/// A path component in an EXCEPT update
#[derive(Debug, Clone, PartialEq)]
pub enum TlaExceptPath {
    /// Index access: `![i]`
    Index(TlaExpr),
    /// Field access: `!.field`
    Field(String),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_create_module() {
        let module = TlaModule::new("TestModule");
        assert_eq!(module.name, "TestModule");
        assert!(module.extends.is_empty());
        assert!(module.variables.is_empty());
    }

    #[test]
    fn test_create_operator() {
        let body = TlaExpr::binop(TlaBinOp::Eq, TlaExpr::ident("x"), TlaExpr::number(0));
        let op = TlaOperator::new("Init", body).with_params(vec![TlaParam::new("x")]);

        assert_eq!(op.name, "Init");
        assert_eq!(op.params.len(), 1);
        assert!(!op.is_recursive);
    }

    #[test]
    fn test_create_expressions() {
        // Test identifier
        let id = TlaExpr::ident("x");
        assert!(matches!(id, TlaExpr::Ident(s) if s == "x"));

        // Test number
        let num = TlaExpr::number(42);
        assert!(matches!(num, TlaExpr::Number(TlaNumber::Decimal(s)) if s == "42"));

        // Test boolean
        let b = TlaExpr::bool(true);
        assert!(matches!(b, TlaExpr::Bool(true)));

        // Test prime
        let primed = TlaExpr::prime(TlaExpr::ident("x"));
        assert!(matches!(primed, TlaExpr::Prime(_)));
    }

    #[test]
    fn test_number_conversion() {
        assert_eq!(TlaNumber::Decimal("42".to_string()).to_i64(), Some(42));
        assert_eq!(TlaNumber::Binary("0b1010".to_string()).to_i64(), Some(10));
        assert_eq!(TlaNumber::Octal("0o77".to_string()).to_i64(), Some(63));
        assert_eq!(TlaNumber::Hex("0xFF".to_string()).to_i64(), Some(255));
    }

    #[test]
    fn test_quantifier_bound() {
        let bound = TlaQuantBound::new("x", TlaExpr::ident("S"));
        assert_eq!(bound.var, "x");
        assert!(bound.set.is_some());

        let unbounded = TlaQuantBound::unbounded("y");
        assert_eq!(unbounded.var, "y");
        assert!(unbounded.set.is_none());
    }

    #[test]
    fn test_binop_expression() {
        let expr = TlaExpr::binop(
            TlaBinOp::And,
            TlaExpr::binop(TlaBinOp::Eq, TlaExpr::ident("x"), TlaExpr::number(0)),
            TlaExpr::binop(TlaBinOp::Eq, TlaExpr::ident("y"), TlaExpr::number(0)),
        );

        match expr {
            TlaExpr::BinOp {
                op: TlaBinOp::And, ..
            } => {}
            _ => panic!("Expected And binop"),
        }
    }

    #[test]
    fn test_set_enum() {
        let set = TlaExpr::SetEnum(vec![
            TlaExpr::number(1),
            TlaExpr::number(2),
            TlaExpr::number(3),
        ]);

        match set {
            TlaExpr::SetEnum(elems) => assert_eq!(elems.len(), 3),
            _ => panic!("Expected SetEnum"),
        }
    }

    #[test]
    fn test_function_construct() {
        let func = TlaExpr::FnConstruct {
            var: "x".to_string(),
            domain: Box::new(TlaExpr::ident("S")),
            body: Box::new(TlaExpr::binop(
                TlaBinOp::Plus,
                TlaExpr::ident("x"),
                TlaExpr::number(1),
            )),
        };

        match func {
            TlaExpr::FnConstruct { var, .. } => assert_eq!(var, "x"),
            _ => panic!("Expected FnConstruct"),
        }
    }

    #[test]
    fn test_record_expression() {
        let record = TlaExpr::Record(vec![
            ("a".to_string(), TlaExpr::number(1)),
            ("b".to_string(), TlaExpr::number(2)),
        ]);

        match record {
            TlaExpr::Record(fields) => {
                assert_eq!(fields.len(), 2);
                assert_eq!(fields[0].0, "a");
                assert_eq!(fields[1].0, "b");
            }
            _ => panic!("Expected Record"),
        }
    }

    #[test]
    fn test_forall_expression() {
        let forall = TlaExpr::Forall {
            vars: vec![TlaQuantBound::new("x", TlaExpr::ident("S"))],
            body: Box::new(TlaExpr::binop(
                TlaBinOp::Gt,
                TlaExpr::ident("x"),
                TlaExpr::number(0),
            )),
        };

        match forall {
            TlaExpr::Forall { vars, .. } => {
                assert_eq!(vars.len(), 1);
                assert_eq!(vars[0].var, "x");
            }
            _ => panic!("Expected Forall"),
        }
    }

    #[test]
    fn test_if_then_else() {
        let ite = TlaExpr::IfThenElse {
            cond: Box::new(TlaExpr::binop(
                TlaBinOp::Gt,
                TlaExpr::ident("x"),
                TlaExpr::number(0),
            )),
            then_expr: Box::new(TlaExpr::ident("x")),
            else_expr: Box::new(TlaExpr::unary(TlaUnaryOp::Neg, TlaExpr::ident("x"))),
        };

        assert!(matches!(ite, TlaExpr::IfThenElse { .. }));
    }

    #[test]
    fn test_except_update() {
        let update = TlaExceptUpdate {
            path: vec![TlaExceptPath::Index(TlaExpr::ident("i"))],
            value: TlaExpr::number(42),
        };

        assert_eq!(update.path.len(), 1);
        assert!(matches!(update.path[0], TlaExceptPath::Index(_)));
    }

    #[test]
    fn test_temporal_operators() {
        let always = TlaExpr::Always(Box::new(TlaExpr::ident("P")));
        assert!(matches!(always, TlaExpr::Always(_)));

        let eventually = TlaExpr::Eventually(Box::new(TlaExpr::ident("P")));
        assert!(matches!(eventually, TlaExpr::Eventually(_)));

        let leads_to = TlaExpr::LeadsTo {
            left: Box::new(TlaExpr::ident("P")),
            right: Box::new(TlaExpr::ident("Q")),
        };
        assert!(matches!(leads_to, TlaExpr::LeadsTo { .. }));
    }
}
