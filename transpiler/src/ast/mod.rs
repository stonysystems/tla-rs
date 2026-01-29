//! AST definitions for Verus spec functions.
//!
//! This module defines the abstract syntax tree types that represent
//! parsed Verus spec functions and their components.

use proc_macro2::Span;

/// A Verus spec function definition
#[derive(Debug, Clone)]
pub struct SpecFunction {
    /// Function name
    pub name: String,
    /// Generic type parameters
    pub generics: Generics,
    /// Function parameters
    pub params: Vec<Parameter>,
    /// Return type (usually bool for predicates)
    pub return_type: Type,
    /// Requires clauses (preconditions)
    pub requires: Vec<Expr>,
    /// Ensures clauses (postconditions)
    pub ensures: Vec<Expr>,
    /// Recommends clauses
    pub recommends: Vec<Expr>,
    /// Decreases clauses (for termination)
    pub decreases: Vec<Expr>,
    /// Function body
    pub body: Expr,
    /// Source span for error reporting
    pub span: Option<Span>,
}

/// Generic type parameters
#[derive(Debug, Clone, Default)]
pub struct Generics {
    pub params: Vec<GenericParam>,
    pub where_clause: Option<WhereClause>,
}

/// A single generic parameter
#[derive(Debug, Clone)]
pub enum GenericParam {
    Type {
        name: String,
        bounds: Vec<TypeBound>,
    },
    Lifetime {
        name: String,
    },
    Const {
        name: String,
        ty: Type,
    },
}

/// Type bounds for generic parameters
#[derive(Debug, Clone)]
pub struct TypeBound {
    pub path: Path,
}

/// Where clause
#[derive(Debug, Clone)]
pub struct WhereClause {
    pub predicates: Vec<WherePredicate>,
}

/// A single where predicate
#[derive(Debug, Clone)]
pub struct WherePredicate {
    pub bounded_ty: Type,
    pub bounds: Vec<TypeBound>,
}

/// Function parameter
#[derive(Debug, Clone)]
pub struct Parameter {
    /// Parameter name
    pub name: String,
    /// Parameter type
    pub ty: Type,
    /// Mode annotation (filled by mode analyzer)
    pub mode: Option<ParameterMode>,
    /// Variable mode (ghost/tracked/exec)
    pub variable_mode: VariableMode,
    /// Source span
    pub span: Option<Span>,
}

/// Parameter mode indicating whether it's an input or output
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ParameterMode {
    /// Read-only input (+)
    Input,
    /// Must be computed output (-)
    Output,
}

/// Function kind distinguishing predicates from helper functions
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum FunctionKind {
    /// Predicate function returning bool with input/output parameters
    #[default]
    Predicate,
    /// Helper function returning a value (all parameters are inputs)
    Helper,
}

/// Variable mode for Verus ghost/tracked/exec distinction
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum VariableMode {
    /// Executable code (default)
    #[default]
    Exec,
    /// Ghost code (proof only, erased at compile time)
    Ghost,
    /// Tracked code (linear permissions)
    Tracked,
}

/// Type representation
#[derive(Debug, Clone)]
pub enum Type {
    /// Named type (e.g., `Ballot`, `LAcceptor`)
    Named(Path),
    /// Generic type (e.g., `Seq<RslPacket>`)
    Generic(Path, Vec<Type>),
    /// Tuple type
    Tuple(Vec<Type>),
    /// Sequence type (Verus)
    Seq(Box<Type>),
    /// Set type (Verus)
    Set(Box<Type>),
    /// Map type (Verus)
    Map(Box<Type>, Box<Type>),
    /// Reference type
    Reference {
        ty: Box<Type>,
        mutable: bool,
    },
    /// Boolean type
    Bool,
    /// Integer types
    Int,
    Nat,
    /// Unit type
    Unit,
}

/// A path like `RSL::Acceptor::LAcceptor`
#[derive(Debug, Clone)]
pub struct Path {
    pub segments: Vec<String>,
}

impl Path {
    pub fn new(segments: Vec<String>) -> Self {
        Self { segments }
    }

    pub fn single(name: String) -> Self {
        Self {
            segments: vec![name],
        }
    }

    pub fn last(&self) -> Option<&str> {
        self.segments.last().map(|s| s.as_str())
    }
}

/// Expression AST supporting Verus constructs
#[derive(Debug, Clone)]
pub enum Expr {
    // Logical operators
    /// Conjunction (&&&)
    Conjunction(Vec<Expr>),
    /// Disjunction (|||)
    Disjunction(Vec<Expr>),
    /// Implication (==>)
    Implies(Box<Expr>, Box<Expr>),
    /// Biconditional / iff (<==>) - equivalent to (a ==> b) && (b ==> a)
    Iff(Box<Expr>, Box<Expr>),
    /// Negation (!)
    Not(Box<Expr>),

    // Quantifiers
    /// Universal quantifier
    Forall {
        vars: Vec<Binding>,
        triggers: Vec<Trigger>,
        body: Box<Expr>,
    },
    /// Existential quantifier
    Exists { vars: Vec<Binding>, body: Box<Expr> },

    // Control flow
    /// Conditional expression
    If {
        cond: Box<Expr>,
        then_branch: Box<Expr>,
        else_branch: Option<Box<Expr>>,
    },
    /// Match expression
    Match {
        scrutinee: Box<Expr>,
        arms: Vec<MatchArm>,
    },
    /// Let binding
    Let {
        binding: Binding,
        value: Box<Expr>,
        body: Box<Expr>,
    },

    // Comparisons
    /// Equality (==)
    Eq(Box<Expr>, Box<Expr>),
    /// Inequality (!=)
    Ne(Box<Expr>, Box<Expr>),
    /// Less than (<)
    Lt(Box<Expr>, Box<Expr>),
    /// Less than or equal (<=)
    Le(Box<Expr>, Box<Expr>),
    /// Greater than (>)
    Gt(Box<Expr>, Box<Expr>),
    /// Greater than or equal (>=)
    Ge(Box<Expr>, Box<Expr>),
    /// Enum variant check (expr is VariantName)
    Is(Box<Expr>, String),

    // Access
    /// Field access (expr.field)
    Field(Box<Expr>, String),
    /// Index access (expr[idx])
    Index(Box<Expr>, Box<Expr>),
    /// Arrow access for enum variants (expr->field)
    Arrow(Box<Expr>, String),

    // Struct construction
    /// Struct literal
    Struct {
        name: Path,
        fields: Vec<(String, Expr)>,
    },
    /// Struct update syntax
    StructUpdate {
        name: Option<Path>,
        base: Box<Expr>,
        fields: Vec<(String, Expr)>,
    },

    // Collections
    /// Sequence literal (seq![...])
    SeqLit(Vec<Expr>),
    /// Set literal (set![...])
    SetLit(Vec<Expr>),
    /// Map literal (map![...])
    MapLit(Vec<(Expr, Expr)>),
    /// Empty sequence (Seq::empty())
    SeqEmpty,
    /// Empty set (Set::empty())
    SetEmpty,
    /// Empty map (Map::empty())
    MapEmpty,

    // Calls
    /// Function call
    Call { func: Path, args: Vec<Expr> },
    /// Method call
    MethodCall {
        receiver: Box<Expr>,
        method: String,
        args: Vec<Expr>,
    },

    // Verus-specific
    /// View operator (expr@)
    View(Box<Expr>),
    /// Type cast (expr as Type)
    Cast(Box<Expr>, Type),

    // Primitives
    /// Identifier
    Ident(String),
    /// Literal value
    Literal(Literal),
    /// Binary operation
    Binary(Box<Expr>, BinOp, Box<Expr>),
    /// Unary operation
    Unary(UnaryOp, Box<Expr>),
}

/// Variable binding
#[derive(Debug, Clone)]
pub struct Binding {
    /// The pattern being bound (simple identifier, tuple, etc.)
    pub pattern: Pattern,
    pub ty: Option<Type>,
    /// Variable mode (ghost/tracked/exec)
    pub variable_mode: VariableMode,
}

impl Binding {
    /// Helper to get the name for simple identifier bindings
    pub fn name(&self) -> Option<&str> {
        if let Pattern::Ident(name) = &self.pattern {
            Some(name)
        } else {
            None
        }
    }

    /// Get name as a String, panics if not an identifier pattern.
    /// Used for quantifier bindings which are always simple identifiers.
    pub fn name_string(&self) -> String {
        self.name()
            .expect("Expected identifier pattern in binding")
            .to_string()
    }
}

/// Trigger for quantifiers
#[derive(Debug, Clone)]
pub struct Trigger {
    pub exprs: Vec<Expr>,
}

/// Match arm
#[derive(Debug, Clone)]
pub struct MatchArm {
    pub pattern: Pattern,
    pub guard: Option<Expr>,
    pub body: Expr,
}

/// Pattern for match expressions
#[derive(Debug, Clone)]
pub enum Pattern {
    /// Wildcard pattern (_)
    Wildcard,
    /// Identifier pattern
    Ident(String),
    /// Tuple pattern
    Tuple(Vec<Pattern>),
    /// Struct pattern
    Struct {
        name: Path,
        fields: Vec<(String, Pattern)>,
    },
    /// Enum variant pattern
    Variant { name: Path, fields: Vec<Pattern> },
    /// Literal pattern
    Literal(Literal),
}

/// Literal values
#[derive(Debug, Clone)]
pub enum Literal {
    Bool(bool),
    Int(i128),
    String(String),
}

/// Binary operators
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    And,
    Or,
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
}

/// Unary operators
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    Not,
    Neg,
    Deref,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_path_construction() {
        let path = Path::new(vec!["RSL".to_string(), "Acceptor".to_string()]);
        assert_eq!(path.segments.len(), 2);
        assert_eq!(path.last(), Some("Acceptor"));
    }

    #[test]
    fn test_parameter_mode() {
        let param = Parameter {
            name: "s".to_string(),
            ty: Type::Named(Path::single("LAcceptor".to_string())),
            mode: Some(ParameterMode::Input),
            variable_mode: VariableMode::default(),
            span: None,
        };
        assert_eq!(param.mode, Some(ParameterMode::Input));
        assert_eq!(param.variable_mode, VariableMode::Exec);
    }

    #[test]
    fn test_variable_mode() {
        assert_eq!(VariableMode::default(), VariableMode::Exec);

        let ghost_param = Parameter {
            name: "g".to_string(),
            ty: Type::Bool,
            mode: None,
            variable_mode: VariableMode::Ghost,
            span: None,
        };
        assert_eq!(ghost_param.variable_mode, VariableMode::Ghost);
    }
}
