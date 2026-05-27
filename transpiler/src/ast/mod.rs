//! AST definitions for Verus spec functions.
//!
//! This module defines the abstract syntax tree types that represent
//! parsed Verus spec functions and their components.

use proc_macro2::Span;

/// Thread-safe wrapper around `proc_macro2::Span`.
///
/// `Span` is not `Send + Sync` due to proc-macro internals, but our AST
/// spans are only used for error reporting and are never mutated after
/// parsing. This wrapper allows the AST (and thereby `SpecContext`) to be
/// shared across threads for parallel DPOR exploration (Phase 38.18.1).
///
/// # Safety
/// `Span` is internally a `u32` index into a thread-local token stream.
/// We only ever read it (via `Debug` formatting) after parsing is complete
/// on the main thread. The wrapped value is never mutated.
#[derive(Debug, Clone)]
pub struct SendSpan(Span);

// SAFETY: Span is read-only after construction. See doc comment above.
unsafe impl Send for SendSpan {}
unsafe impl Sync for SendSpan {}

impl SendSpan {
    pub fn new(span: Span) -> Self {
        Self(span)
    }
    pub fn span(&self) -> &Span {
        &self.0
    }
}

impl From<Span> for SendSpan {
    fn from(span: Span) -> Self {
        Self(span)
    }
}

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
    pub span: Option<SendSpan>,
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
    pub span: Option<SendSpan>,
}

/// Parameter mode indicating whether it's an input or output
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ParameterMode {
    /// Read-only input (+)
    Input,
    /// Must be computed output (-)
    Output,
}

impl std::fmt::Display for ParameterMode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ParameterMode::Input => write!(f, "+"),
            ParameterMode::Output => write!(f, "-"),
        }
    }
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
#[derive(Debug, Clone, PartialEq)]
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
#[derive(Debug, Clone, PartialEq)]
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

    /// Closure / lambda expression: |params| body
    Closure {
        params: Vec<Binding>,
        body: Box<Expr>,
    },

    /// Choose expression: choose |var| predicate
    /// Returns some value satisfying the predicate, or arbitrary if none exists.
    Choose { vars: Vec<Binding>, body: Box<Expr> },

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

    /// Pre-evaluated constant value (produced by constant folding at IR time).
    /// The evaluator returns this value directly without any computation.
    ConstantValue(crate::modelcheck::value::RuntimeValue),
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

impl BinOp {
    /// Returns the Rust operator string for this binary operator.
    pub fn as_str(self) -> &'static str {
        match self {
            BinOp::Add => "+",
            BinOp::Sub => "-",
            BinOp::Mul => "*",
            BinOp::Div => "/",
            BinOp::Mod => "%",
            BinOp::And => "&&",
            BinOp::Or => "||",
            BinOp::BitAnd => "&",
            BinOp::BitOr => "|",
            BinOp::BitXor => "^",
            BinOp::Shl => "<<",
            BinOp::Shr => ">>",
        }
    }
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

    // --- Binding tests ---

    #[test]
    fn test_binding_name_ident() {
        let binding = Binding {
            pattern: Pattern::Ident("x".to_string()),
            ty: None,
            variable_mode: VariableMode::Exec,
        };
        assert_eq!(binding.name(), Some("x"));
    }

    #[test]
    fn test_binding_name_wildcard() {
        let binding = Binding {
            pattern: Pattern::Wildcard,
            ty: None,
            variable_mode: VariableMode::Exec,
        };
        assert_eq!(binding.name(), None);
    }

    #[test]
    fn test_binding_name_string() {
        let binding = Binding {
            pattern: Pattern::Ident("foo".to_string()),
            ty: None,
            variable_mode: VariableMode::Exec,
        };
        assert_eq!(binding.name_string(), "foo");
    }

    // --- Type construction tests ---

    #[test]
    fn test_type_reference() {
        let immut = Type::Reference {
            ty: Box::new(Type::Bool),
            mutable: false,
        };
        let mutable = Type::Reference {
            ty: Box::new(Type::Int),
            mutable: true,
        };
        assert!(matches!(immut, Type::Reference { mutable: false, .. }));
        assert!(matches!(mutable, Type::Reference { mutable: true, .. }));
    }

    #[test]
    fn test_type_generic_multiple_args() {
        let generic = Type::Generic(
            Path::single("HashMap".to_string()),
            vec![Type::Int, Type::Bool],
        );
        if let Type::Generic(path, args) = &generic {
            assert_eq!(path.last(), Some("HashMap"));
            assert_eq!(args.len(), 2);
        } else {
            panic!("Expected Type::Generic");
        }
    }

    #[test]
    fn test_type_seq_set_map() {
        let seq = Type::Seq(Box::new(Type::Int));
        let set = Type::Set(Box::new(Type::Bool));
        let map = Type::Map(Box::new(Type::Int), Box::new(Type::Bool));
        assert!(matches!(seq, Type::Seq(_)));
        assert!(matches!(set, Type::Set(_)));
        assert!(matches!(map, Type::Map(_, _)));
    }

    // --- Path tests ---

    #[test]
    fn test_path_single_and_last() {
        let p = Path::single("Foo".to_string());
        assert_eq!(p.segments.len(), 1);
        assert_eq!(p.last(), Some("Foo"));
    }

    #[test]
    fn test_path_multiple_segments() {
        let p = Path::new(vec!["A".into(), "B".into(), "C".into()]);
        assert_eq!(p.segments.len(), 3);
        assert_eq!(p.last(), Some("C"));
    }

    // --- Expr tests ---

    #[test]
    fn test_expr_struct_fields() {
        let expr = Expr::Struct {
            name: Path::single("MyStruct".into()),
            fields: vec![
                ("a".into(), Expr::Literal(Literal::Int(1))),
                ("b".into(), Expr::Literal(Literal::Bool(true))),
                ("c".into(), Expr::Ident("x".into())),
            ],
        };
        if let Expr::Struct { name, fields } = &expr {
            assert_eq!(name.last(), Some("MyStruct"));
            assert_eq!(fields.len(), 3);
            assert_eq!(fields[0].0, "a");
            assert_eq!(fields[1].0, "b");
            assert_eq!(fields[2].0, "c");
        } else {
            panic!("Expected Expr::Struct");
        }
    }

    #[test]
    fn test_expr_match_with_arms() {
        let expr = Expr::Match {
            scrutinee: Box::new(Expr::Ident("x".into())),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Literal(Literal::Int(1)),
                    guard: None,
                    body: Expr::Literal(Literal::Bool(true)),
                },
                MatchArm {
                    pattern: Pattern::Wildcard,
                    guard: None,
                    body: Expr::Literal(Literal::Bool(false)),
                },
            ],
        };
        if let Expr::Match { arms, .. } = &expr {
            assert_eq!(arms.len(), 2);
        }
    }

    // --- SpecFunction test ---

    #[test]
    fn test_spec_function_clauses() {
        let func = SpecFunction {
            name: "my_pred".into(),
            generics: Generics::default(),
            params: vec![],
            return_type: Type::Bool,
            requires: vec![Expr::Literal(Literal::Bool(true))],
            ensures: vec![Expr::Literal(Literal::Bool(true))],
            recommends: vec![],
            decreases: vec![Expr::Ident("n".into())],
            body: Expr::Literal(Literal::Bool(true)),
            span: None,
        };
        assert_eq!(func.requires.len(), 1);
        assert_eq!(func.ensures.len(), 1);
        assert_eq!(func.decreases.len(), 1);
        assert_eq!(func.name, "my_pred");
    }

    // --- BinOp / UnaryOp tests ---

    #[test]
    fn test_binop_variants_distinct() {
        assert_ne!(BinOp::Add, BinOp::Sub);
        assert_ne!(BinOp::Sub, BinOp::Mul);
        assert_ne!(BinOp::Mul, BinOp::Div);
        assert_ne!(BinOp::Div, BinOp::Mod);
        assert_ne!(BinOp::And, BinOp::Or);
        assert_ne!(BinOp::BitAnd, BinOp::BitOr);
        assert_ne!(BinOp::Shl, BinOp::Shr);
    }

    #[test]
    fn test_binop_as_str_all_variants() {
        assert_eq!(BinOp::Add.as_str(), "+");
        assert_eq!(BinOp::Sub.as_str(), "-");
        assert_eq!(BinOp::Mul.as_str(), "*");
        assert_eq!(BinOp::Div.as_str(), "/");
        assert_eq!(BinOp::Mod.as_str(), "%");
        assert_eq!(BinOp::And.as_str(), "&&");
        assert_eq!(BinOp::Or.as_str(), "||");
        assert_eq!(BinOp::BitAnd.as_str(), "&");
        assert_eq!(BinOp::BitOr.as_str(), "|");
        assert_eq!(BinOp::BitXor.as_str(), "^");
        assert_eq!(BinOp::Shl.as_str(), "<<");
        assert_eq!(BinOp::Shr.as_str(), ">>");
    }

    #[test]
    fn test_binop_as_str_returns_static_str() {
        // Verify that as_str returns &'static str (can be used without lifetime issues)
        let op = BinOp::Add;
        let s: &'static str = op.as_str();
        assert_eq!(s, "+");
    }

    #[test]
    fn test_unaryop_variants_distinct() {
        assert_ne!(UnaryOp::Not, UnaryOp::Neg);
        assert_ne!(UnaryOp::Neg, UnaryOp::Deref);
        assert_ne!(UnaryOp::Not, UnaryOp::Deref);
    }

    // --- Literal / Pattern / VariableMode tests ---

    #[test]
    fn test_literal_variants() {
        let int_lit = Literal::Int(42);
        let bool_lit = Literal::Bool(true);
        let str_lit = Literal::String("hello".into());
        assert!(matches!(int_lit, Literal::Int(42)));
        assert!(matches!(bool_lit, Literal::Bool(true)));
        assert!(matches!(str_lit, Literal::String(s) if s == "hello"));
    }

    #[test]
    fn test_pattern_variants() {
        let w = Pattern::Wildcard;
        let i = Pattern::Ident("x".into());
        let t = Pattern::Tuple(vec![Pattern::Wildcard, Pattern::Ident("y".into())]);
        assert!(matches!(w, Pattern::Wildcard));
        assert!(matches!(i, Pattern::Ident(ref s) if s == "x"));
        assert!(matches!(t, Pattern::Tuple(ref pats) if pats.len() == 2));
    }

    #[test]
    fn test_variable_mode_distinct() {
        assert_ne!(VariableMode::Ghost, VariableMode::Tracked);
        assert_ne!(VariableMode::Tracked, VariableMode::Exec);
        assert_ne!(VariableMode::Ghost, VariableMode::Exec);
    }
}
