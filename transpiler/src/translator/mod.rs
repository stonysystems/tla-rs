//! Code generation for exec functions.
//!
//! This module transforms validated spec predicates into executable Rust/Verus
//! functions with proper proof linkage.

use crate::ast::{Binding, BinOp, Expr, FunctionKind, Literal, ParameterMode, Path, Pattern, Type};
use crate::error::{TranspileError, TranspileResult};
use crate::moder::AnnotatedFunction;
use std::collections::{HashMap, HashSet};

/// Type alias for output assignments result: (name, expression) pairs and other expressions.
pub type OutputAssignments = (Vec<(String, ExecExpr)>, Vec<ExecExpr>);

/// Type alias for helper call processing result:
/// (let_bindings, remaining_exprs, field_substitutions, bound_output_params)
pub type HelperCallResult = (
    Vec<ExecExpr>,
    Vec<Expr>,
    HashMap<(String, String), String>,
    HashSet<String>,
);

/// Configuration for method call transformation (imported from config module)
pub use crate::config::MethodCallConfig;

/// Configuration for code generation
#[derive(Debug, Clone)]
pub struct TranslatorConfig {
    /// Prefix for spec types (e.g., "L")
    pub spec_prefix: String,
    /// Prefix for exec types (e.g., "C")
    pub exec_prefix: String,
    /// Type remapping (spec type -> exec type)
    pub type_remapping: HashMap<String, String>,
    /// Function path mapping for cross-module calls
    /// Maps spec function names to their qualified exec paths
    /// e.g., "BroadcastToEveryone" -> "crate::generated::RSL::broadcast_gen::CBroadcastToEveryone"
    pub function_paths: HashMap<String, String>,
    /// Spec-only functions that should NOT have C-prefix added
    /// These are functions that only exist in the spec layer and have no exec implementation
    pub spec_only_functions: HashSet<String>,
    /// Method call mappings for spec functions that should become method calls.
    /// Maps spec function name to method call configuration.
    /// Example: "LMinQuorumSize" -> { method_name: "CMinQuorumSize", receiver_arg_index: 0 }
    pub method_calls: HashMap<String, MethodCallConfig>,
    /// Primitive types that should NOT have valid() predicates generated.
    /// These are types that don't have a valid() method (e.g., type aliases to u64, HashMap).
    pub primitive_types: HashSet<String>,
    /// Whether to generate abstraction functions
    pub generate_abstraction_fns: bool,
    /// Whether to generate validity predicates
    pub generate_validity_predicates: bool,
    /// Name of the validity predicate (default: "well_formed", RSL uses "valid")
    pub validity_predicate_name: String,
    /// Whether to generate explicit for loops instead of iterator chains.
    /// When true, generates Verus-verifiable loop code with placeholders for invariants.
    /// When false (default), generates iterator-based code (.iter().filter().collect()).
    pub generate_loops_for_verification: bool,
}

impl Default for TranslatorConfig {
    fn default() -> Self {
        Self {
            spec_prefix: "L".to_string(),
            exec_prefix: "C".to_string(),
            type_remapping: HashMap::new(),
            function_paths: HashMap::new(),
            spec_only_functions: HashSet::new(),
            method_calls: HashMap::new(),
            primitive_types: HashSet::new(),
            generate_abstraction_fns: true,
            generate_validity_predicates: true,
            validity_predicate_name: "well_formed".to_string(),
            generate_loops_for_verification: false,
        }
    }
}

impl TranslatorConfig {
    /// Check if a type should be treated as primitive (no valid() predicate).
    /// This checks both spec type names and remapped exec type names.
    pub fn is_primitive_type(&self, type_name: &str) -> bool {
        // Check if directly in primitive_types list
        if self.primitive_types.contains(type_name) {
            return true;
        }

        // Check if the remapped exec type is in primitive_types
        if let Some(exec_type) = self.type_remapping.get(type_name) {
            if self.primitive_types.contains(exec_type) {
                return true;
            }
        }

        false
    }
}

/// Generated exec function
#[derive(Debug, Clone)]
pub struct ExecFunction {
    /// Function name (e.g., "CAcceptorProcess1a")
    pub name: String,
    /// Parameters (with exec types)
    pub params: Vec<ExecParameter>,
    /// Return type (tuple of outputs)
    pub return_type: ExecType,
    /// Requires clauses
    pub requires: Vec<String>,
    /// Ensures clauses (linking to spec)
    pub ensures: Vec<String>,
    /// Decreases clauses (for recursive functions)
    pub decreases: Vec<String>,
    /// Function body
    pub body: ExecExpr,
}

/// Parameter for exec function
#[derive(Debug, Clone)]
pub struct ExecParameter {
    pub name: String,
    pub ty: ExecType,
    pub is_reference: bool,
}

/// Type for exec code
#[derive(Debug, Clone)]
pub enum ExecType {
    Named(String),
    Generic(String, Vec<ExecType>),
    Tuple(Vec<ExecType>),
    Vec(Box<ExecType>),
    HashMap(Box<ExecType>, Box<ExecType>),
    Reference(Box<ExecType>, bool), // (type, mutable)
}

impl ExecType {
    /// Convert to Rust type string
    pub fn to_rust_string(&self) -> String {
        match self {
            ExecType::Named(name) => name.clone(),
            ExecType::Generic(name, args) => {
                let args_str: Vec<_> = args.iter().map(|a| a.to_rust_string()).collect();
                format!("{}<{}>", name, args_str.join(", "))
            }
            ExecType::Tuple(types) => {
                let types_str: Vec<_> = types.iter().map(|t| t.to_rust_string()).collect();
                format!("({})", types_str.join(", "))
            }
            ExecType::Vec(inner) => format!("Vec<{}>", inner.to_rust_string()),
            ExecType::HashMap(k, v) => {
                format!("HashMap<{}, {}>", k.to_rust_string(), v.to_rust_string())
            }
            ExecType::Reference(inner, mutable) => {
                if *mutable {
                    format!("&mut {}", inner.to_rust_string())
                } else {
                    format!("&{}", inner.to_rust_string())
                }
            }
        }
    }
}

/// Expression for exec code
#[derive(Debug, Clone)]
pub enum ExecExpr {
    /// Block of statements
    Block(Vec<ExecExpr>),
    /// Let binding
    Let {
        /// Pattern as a string (e.g., "x" or "(a, b)")
        pattern: String,
        ty: Option<ExecType>,
        value: Box<ExecExpr>,
    },
    /// If expression
    If {
        cond: Box<ExecExpr>,
        then_branch: Box<ExecExpr>,
        else_branch: Option<Box<ExecExpr>>,
    },
    /// Match expression
    Match {
        scrutinee: Box<ExecExpr>,
        arms: Vec<(String, ExecExpr)>, // (pattern, body)
    },
    /// Struct construction
    Struct {
        name: String,
        fields: Vec<(String, ExecExpr)>,
    },
    /// Struct update (..base syntax)
    StructUpdate {
        name: String,
        base: Box<ExecExpr>,
        fields: Vec<(String, ExecExpr)>,
    },
    /// Clone call
    Clone(Box<ExecExpr>),
    /// Field access
    Field(Box<ExecExpr>, String),
    /// Method call
    MethodCall {
        receiver: Box<ExecExpr>,
        method: String,
        args: Vec<ExecExpr>,
    },
    /// Function call
    Call { func: String, args: Vec<ExecExpr> },
    /// Binary operation
    Binary {
        lhs: Box<ExecExpr>,
        op: String,
        rhs: Box<ExecExpr>,
    },
    /// Unary operation
    Unary { op: String, expr: Box<ExecExpr> },
    /// Variable reference
    Var(String),
    /// Literal
    Literal(String),
    /// Vec literal
    VecLit(Vec<ExecExpr>),
    /// Tuple
    Tuple(Vec<ExecExpr>),
    /// Return statement
    Return(Box<ExecExpr>),
    /// Range expression (start..end)
    Range {
        start: Box<ExecExpr>,
        end: Box<ExecExpr>,
    },
    /// Closure expression (|params| body)
    Closure {
        params: Vec<String>,
        body: Box<ExecExpr>,
    },
    /// Comment (for documentation or TODO markers)
    Comment(String),
    /// Type cast (expr as Type)
    Cast(Box<ExecExpr>, String),
    /// Map update with insert operation
    /// Generates: { let mut result = source.iter().filter().collect(); if filter(new_key) { result.insert(new_key, value); } result }
    MapUpdateWithInsert {
        source: Box<ExecExpr>,
        key_var: String,
        filter: Box<ExecExpr>,
        new_key: Box<ExecExpr>,
    },

    // === Verus Loop Constructs for Verified Code ===
    /// Verus for-in-iter loop with invariants
    /// Generates: `for var in iter:iter_name { body } invariant inv1, inv2, ...`
    ForInIter {
        /// Loop variable name (e.g., "key")
        var: String,
        /// Iterator name (e.g., "m_keys")
        iter_name: String,
        /// Source expression for iterator (e.g., "votes.keys()")
        iter_source: Box<ExecExpr>,
        /// Loop invariants (Verus spec expressions as strings)
        invariants: Vec<String>,
        /// Loop body
        body: Box<ExecExpr>,
    },

    /// Ghost variable declaration
    /// Generates: `let ghost mut name: ty = init;`
    GhostVar {
        name: String,
        ty: String,
        init: Box<ExecExpr>,
        mutable: bool,
    },

    /// Proof block
    /// Generates: `proof { stmts }`
    ProofBlock { stmts: Vec<ExecExpr> },

    /// Assume statement
    /// Generates: `assume(expr);`
    Assume(Box<ExecExpr>),

    /// Assert statement
    /// Generates: `assert(expr);`
    Assert(Box<ExecExpr>),

    /// Broadcast use statement
    /// Generates: `broadcast use path;`
    BroadcastUse(String),

    /// Break statement
    /// Generates: `break;`
    Break,

    /// Matches expression for enum variant checking
    /// Generates: `matches!(expr, Pattern { .. })` or `matches!(expr, Pattern)`
    Matches {
        expr: Box<ExecExpr>,
        /// Pattern to match (e.g., "CIncompleteBatchTimer::CIncompleteBatchTimerOff")
        pattern: String,
        /// Whether the pattern is a struct variant (needs { .. })
        is_struct_variant: bool,
    },
}

/// Context for expression transformation
pub struct TransformContext<'a> {
    pub config: &'a TranslatorConfig,
    pub output_params: Vec<String>,
    pub input_params: Vec<String>,
    /// Maps output parameter names to their types (for struct name derivation)
    pub output_types: HashMap<String, Type>,
    /// Maps (output_var, field) pairs to substitution variable names
    /// e.g., ("s_", "proposer") -> "s_proposer"
    pub field_substitutions: HashMap<(String, String), String>,
}

/// Information about a helper predicate call with output arguments
#[derive(Debug, Clone)]
pub struct HelperCallInfo {
    /// Function name
    pub func_name: String,
    /// Input arguments (already transformed)
    pub input_args: Vec<ExecExpr>,
    /// Output fields: (output_var, field_name) pairs
    /// e.g., for LProposerProcessRequest(s.proposer, s_.proposer, ...),
    /// this would be [("s_", "proposer")]
    pub output_fields: Vec<(String, String)>,
    /// Direct output parameters (not fields of a struct)
    /// e.g., for LAcceptorProcess1a(..., sent_packets), this would be ["sent_packets"]
    pub output_params: Vec<String>,
}

impl<'a> TransformContext<'a> {
    pub fn is_output(&self, name: &str) -> bool {
        self.output_params.contains(&name.to_string())
    }

    /// Check if a path like "s_.field" belongs to an output variable
    /// Returns true if the base (s_) is an output parameter
    pub fn is_output_field_path(&self, path: &str) -> bool {
        // Try direct match first
        if self.output_params.contains(&path.to_string()) {
            return true;
        }
        // Check if it's a field path like "s_.field"
        if let Some(dot_pos) = path.find('.') {
            let base = &path[..dot_pos];
            return self.output_params.contains(&base.to_string());
        }
        false
    }

    /// Check if a variable is an input parameter (passed by reference)
    pub fn is_input(&self, name: &str) -> bool {
        self.input_params.contains(&name.to_string())
    }

    /// Get the struct name for an output parameter from its type
    pub fn get_output_struct_name(&self, name: &str) -> Option<String> {
        self.output_types.get(name).and_then(|ty| match ty {
            Type::Named(path) => path.last().map(|s| s.to_string()),
            _ => None,
        })
    }

    /// Get the substitution variable name for an output field access
    /// e.g., for s_.proposer, returns Some("s_proposer") if there's a binding
    pub fn get_field_substitution(&self, var: &str, field: &str) -> Option<&String> {
        self.field_substitutions
            .get(&(var.to_string(), field.to_string()))
    }
}

/// Code translator
pub struct Translator {
    config: TranslatorConfig,
}

impl Translator {
    /// Create a new translator with the given configuration
    pub fn new(config: TranslatorConfig) -> Self {
        Self { config }
    }

    /// Wrap an expression with .clone() if it directly references an input parameter.
    /// Input parameters are passed by reference, so when assigning to struct fields
    /// (which expect owned types), we need to clone.
    fn clone_if_input_ref(&self, expr: ExecExpr, ctx: &TransformContext) -> ExecExpr {
        match &expr {
            ExecExpr::Var(name) if ctx.is_input(name) => ExecExpr::Clone(Box::new(expr)),
            _ => expr,
        }
    }

    /// Check if an expression only references input parameters (or literals/constants).
    /// Such expressions are preconditions and should not be emitted as executable code.
    /// Returns true if the expression is a "pure input" expression that:
    /// - Only references input parameters and literals
    /// - Does not reference any output parameters
    /// - Does not define any output (not an assignment to output)
    fn is_input_only_expression(expr: &Expr, ctx: &TransformContext) -> bool {
        use crate::ast::Expr;
        match expr {
            // Identifiers: only input if it's an input param, not an output
            Expr::Ident(name) => ctx.is_input(name) && !ctx.is_output(name),

            // Literals are always input-only
            Expr::Literal(_) => true,

            // Binary operations: both sides must be input-only
            Expr::Binary(lhs, _, rhs) => {
                Self::is_input_only_expression(lhs, ctx) && Self::is_input_only_expression(rhs, ctx)
            }

            // Comparison operations
            Expr::Eq(lhs, rhs)
            | Expr::Ne(lhs, rhs)
            | Expr::Lt(lhs, rhs)
            | Expr::Le(lhs, rhs)
            | Expr::Gt(lhs, rhs)
            | Expr::Ge(lhs, rhs) => {
                Self::is_input_only_expression(lhs, ctx) && Self::is_input_only_expression(rhs, ctx)
            }

            // Unary not
            Expr::Not(inner) => Self::is_input_only_expression(inner, ctx),

            // Field access: base must be input-only
            Expr::Field(base, _) => Self::is_input_only_expression(base, ctx),

            // Method call: receiver and args must be input-only
            Expr::MethodCall { receiver, args, .. } => {
                Self::is_input_only_expression(receiver, ctx)
                    && args.iter().all(|a| Self::is_input_only_expression(a, ctx))
            }

            // Function call: all args must be input-only
            Expr::Call { args, .. } => args.iter().all(|a| Self::is_input_only_expression(a, ctx)),

            // Index: base and index must be input-only
            Expr::Index(base, idx) => {
                Self::is_input_only_expression(base, ctx)
                    && Self::is_input_only_expression(idx, ctx)
            }

            // Conjunction/disjunction: all parts must be input-only
            Expr::Conjunction(parts) | Expr::Disjunction(parts) => {
                parts.iter().all(|p| Self::is_input_only_expression(p, ctx))
            }

            // If expressions: all parts must be input-only
            Expr::If {
                cond,
                then_branch,
                else_branch,
            } => {
                Self::is_input_only_expression(cond, ctx)
                    && Self::is_input_only_expression(then_branch, ctx)
                    && else_branch
                        .as_ref()
                        .is_none_or(|e| Self::is_input_only_expression(e, ctx))
            }

            // Quantifiers typically reference output or define constraints on output
            // so they are not input-only (unless they don't reference outputs)
            Expr::Forall { body, .. } | Expr::Exists { body, .. } => {
                Self::is_input_only_expression(body, ctx)
            }

            // Arrow access (enum variant): base must be input-only
            Expr::Arrow(base, _) => Self::is_input_only_expression(base, ctx),

            // Is check: base must be input-only
            Expr::Is(base, _) => Self::is_input_only_expression(base, ctx),

            // Let bindings: value and body must be input-only
            Expr::Let { value, body, .. } => {
                Self::is_input_only_expression(value, ctx)
                    && Self::is_input_only_expression(body, ctx)
            }

            // Collection literals: all elements must be input-only
            Expr::SeqLit(elems) | Expr::SetLit(elems) => {
                elems.iter().all(|e| Self::is_input_only_expression(e, ctx))
            }

            // Map literals: all keys and values must be input-only
            Expr::MapLit(pairs) => pairs.iter().all(|(k, v)| {
                Self::is_input_only_expression(k, ctx) && Self::is_input_only_expression(v, ctx)
            }),

            // Empty collections are always input-only
            Expr::SeqEmpty | Expr::SetEmpty | Expr::MapEmpty => true,

            // View operator: base must be input-only
            Expr::View(base) => Self::is_input_only_expression(base, ctx),

            // Structs: all field values must be input-only
            Expr::Struct { fields, .. } => fields
                .iter()
                .all(|(_, v)| Self::is_input_only_expression(v, ctx)),

            // StructUpdate: base and all field values must be input-only
            Expr::StructUpdate { base, fields, .. } => {
                Self::is_input_only_expression(base, ctx)
                    && fields
                        .iter()
                        .all(|(_, v)| Self::is_input_only_expression(v, ctx))
            }

            // Implication and biconditional
            Expr::Implies(lhs, rhs) | Expr::Iff(lhs, rhs) => {
                Self::is_input_only_expression(lhs, ctx) && Self::is_input_only_expression(rhs, ctx)
            }

            // Cast: inner must be input-only
            Expr::Cast(inner, _) => Self::is_input_only_expression(inner, ctx),

            // Match: scrutinee and all arm bodies must be input-only
            Expr::Match { scrutinee, arms } => {
                Self::is_input_only_expression(scrutinee, ctx)
                    && arms
                        .iter()
                        .all(|arm| Self::is_input_only_expression(&arm.body, ctx))
            }

            // Default: if we can't determine, assume it's not input-only
            _ => false,
        }
    }

    /// Convert an ExecExpr to a string representation for use in invariants.
    /// This produces a Verus spec-level expression string.
    ///
    /// `loop_var` is the name of the loop variable that should be dereferenced (e.g., "p", "io").
    /// Only references to this variable will get a `*` prefix.
    fn expr_to_invariant_string_with_var(&self, expr: &ExecExpr, loop_var: &str) -> String {
        match expr {
            ExecExpr::Var(name) => {
                // Only dereference the loop variable
                if name == loop_var {
                    format!("*{}", name)
                } else if name.starts_with('*') {
                    // Already has dereference
                    name.clone()
                } else {
                    // Non-loop variable - don't dereference
                    name.clone()
                }
            }
            ExecExpr::Binary { lhs, op, rhs } => {
                // For "is" expressions, the RHS is a variant name (not a variable to deref)
                if op == "is" {
                    let lhs_str = self.expr_to_invariant_string_with_var(lhs, loop_var);
                    // RHS is the variant name - strip any * we might have added
                    let rhs_str = match rhs.as_ref() {
                        ExecExpr::Var(name) => name.trim_start_matches('*').to_string(),
                        _ => self.expr_to_invariant_string_with_var(rhs, loop_var),
                    };
                    format!("{} {} {}", lhs_str, op, rhs_str)
                } else {
                    format!(
                        "{} {} {}",
                        self.expr_to_invariant_string_with_var(lhs, loop_var),
                        op,
                        self.expr_to_invariant_string_with_var(rhs, loop_var)
                    )
                }
            }
            ExecExpr::Field(base, field) => {
                let base_str = self.expr_to_invariant_string_with_var(base, loop_var);
                // Remove dereference for field access
                let base_str = base_str.trim_start_matches('*');
                format!("{}.{}", base_str, field)
            }
            ExecExpr::Literal(lit) => lit.clone(),
            ExecExpr::MethodCall {
                receiver,
                method,
                args,
            } => {
                let recv_str = self.expr_to_invariant_string_with_var(receiver, loop_var);
                let recv_str = recv_str.trim_start_matches('*');
                if args.is_empty() {
                    format!("{}.{}()", recv_str, method)
                } else {
                    let args_str: Vec<String> = args
                        .iter()
                        .map(|a| self.expr_to_invariant_string_with_var(a, loop_var))
                        .collect();
                    format!("{}.{}({})", recv_str, method, args_str.join(", "))
                }
            }
            ExecExpr::Call { func, args } => {
                let args_str: Vec<String> = args
                    .iter()
                    .map(|a| self.expr_to_invariant_string_with_var(a, loop_var))
                    .collect();
                format!("{}({})", func, args_str.join(", "))
            }
            ExecExpr::Unary { op, expr } => {
                // For dereference, check if we're already dereferencing the loop var
                if op == "*" {
                    match expr.as_ref() {
                        ExecExpr::Var(name) if name == loop_var => format!("*{}", name),
                        ExecExpr::Var(name) => format!("*{}", name),
                        _ => format!(
                            "{}{}",
                            op,
                            self.expr_to_invariant_string_with_var(expr, loop_var)
                        ),
                    }
                } else {
                    format!(
                        "{}{}",
                        op,
                        self.expr_to_invariant_string_with_var(expr, loop_var)
                    )
                }
            }
            ExecExpr::If {
                cond,
                then_branch,
                else_branch,
            } => {
                let cond_str = self.expr_to_invariant_string_with_var(cond, loop_var);
                let then_str = self.expr_to_invariant_string_with_var(then_branch, loop_var);
                if let Some(else_expr) = else_branch {
                    let else_str = self.expr_to_invariant_string_with_var(else_expr, loop_var);
                    format!("if {} {{ {} }} else {{ {} }}", cond_str, then_str, else_str)
                } else {
                    format!("if {} {{ {} }}", cond_str, then_str)
                }
            }
            ExecExpr::Struct { name, fields } => {
                let fields_str: Vec<String> = fields
                    .iter()
                    .map(|(field_name, field_val)| {
                        format!(
                            "{}: {}",
                            field_name,
                            self.expr_to_invariant_string_with_var(field_val, loop_var)
                        )
                    })
                    .collect();
                format!("{} {{ {} }}", name, fields_str.join(", "))
            }
            ExecExpr::Tuple(elems) => {
                let elems_str: Vec<String> = elems
                    .iter()
                    .map(|e| self.expr_to_invariant_string_with_var(e, loop_var))
                    .collect();
                format!("({})", elems_str.join(", "))
            }
            ExecExpr::Clone(inner) => {
                // For invariants, we can usually just use the inner expression
                self.expr_to_invariant_string_with_var(inner, loop_var)
            }
            ExecExpr::VecLit(elems) => {
                let elems_str: Vec<String> = elems
                    .iter()
                    .map(|e| self.expr_to_invariant_string_with_var(e, loop_var))
                    .collect();
                format!("seq![{}]", elems_str.join(", "))
            }
            ExecExpr::Block(stmts) => {
                // For a block, convert the last statement (if any)
                if let Some(last) = stmts.last() {
                    self.expr_to_invariant_string_with_var(last, loop_var)
                } else {
                    "()".to_string()
                }
            }
            _ => "/* unsupported expr */".to_string(),
        }
    }

    /// Convert an ExecExpr to a string representation for use in invariants.
    /// This produces a Verus spec-level expression string.
    /// Assumes any variable should be dereferenced (legacy behavior).
    fn expr_to_invariant_string(&self, expr: &ExecExpr) -> String {
        // For backward compatibility, deref all Var expressions
        // This is used by map_filter which has a different pattern
        match expr {
            ExecExpr::Var(name) => {
                if name.starts_with('*') {
                    name.clone()
                } else {
                    format!("*{}", name)
                }
            }
            ExecExpr::Binary { lhs, op, rhs } => {
                format!(
                    "{} {} {}",
                    self.expr_to_invariant_string(lhs),
                    op,
                    self.expr_to_invariant_string(rhs)
                )
            }
            ExecExpr::Field(base, field) => {
                let base_str = self.expr_to_invariant_string(base);
                let base_str = base_str.trim_start_matches('*');
                format!("{}.{}", base_str, field)
            }
            ExecExpr::Literal(lit) => lit.clone(),
            ExecExpr::MethodCall {
                receiver,
                method,
                args,
            } => {
                let recv_str = self.expr_to_invariant_string(receiver);
                let recv_str = recv_str.trim_start_matches('*');
                if args.is_empty() {
                    format!("{}.{}()", recv_str, method)
                } else {
                    let args_str: Vec<String> = args
                        .iter()
                        .map(|a| self.expr_to_invariant_string(a))
                        .collect();
                    format!("{}.{}({})", recv_str, method, args_str.join(", "))
                }
            }
            ExecExpr::Call { func, args } => {
                let args_str: Vec<String> = args
                    .iter()
                    .map(|a| self.expr_to_invariant_string(a))
                    .collect();
                format!("{}({})", func, args_str.join(", "))
            }
            ExecExpr::Unary { op, expr } => {
                if op == "*" {
                    match expr.as_ref() {
                        ExecExpr::Var(name) => format!("*{}", name),
                        _ => format!("{}{}", op, self.expr_to_invariant_string(expr)),
                    }
                } else {
                    format!("{}{}", op, self.expr_to_invariant_string(expr))
                }
            }
            ExecExpr::If {
                cond,
                then_branch,
                else_branch,
            } => {
                let cond_str = self.expr_to_invariant_string(cond);
                let then_str = self.expr_to_invariant_string(then_branch);
                if let Some(else_expr) = else_branch {
                    let else_str = self.expr_to_invariant_string(else_expr);
                    format!("if {} {{ {} }} else {{ {} }}", cond_str, then_str, else_str)
                } else {
                    format!("if {} {{ {} }}", cond_str, then_str)
                }
            }
            ExecExpr::Struct { name, fields } => {
                let fields_str: Vec<String> = fields
                    .iter()
                    .map(|(field_name, field_val)| {
                        format!(
                            "{}: {}",
                            field_name,
                            self.expr_to_invariant_string(field_val)
                        )
                    })
                    .collect();
                format!("{} {{ {} }}", name, fields_str.join(", "))
            }
            ExecExpr::Tuple(elems) => {
                let elems_str: Vec<String> = elems
                    .iter()
                    .map(|e| self.expr_to_invariant_string(e))
                    .collect();
                format!("({})", elems_str.join(", "))
            }
            ExecExpr::Clone(inner) => self.expr_to_invariant_string(inner),
            ExecExpr::VecLit(elems) => {
                let elems_str: Vec<String> = elems
                    .iter()
                    .map(|e| self.expr_to_invariant_string(e))
                    .collect();
                format!("seq![{}]", elems_str.join(", "))
            }
            ExecExpr::Block(stmts) => {
                if let Some(last) = stmts.last() {
                    self.expr_to_invariant_string(last)
                } else {
                    "()".to_string()
                }
            }
            _ => "/* unsupported expr */".to_string(),
        }
    }

    /// Substitute loop variable references with indexed iterator access in invariant strings.
    ///
    /// For a loop variable `x` in a `for x in iter:x_iter` loop, invariants need to reference
    /// elements by index: `x_iter@.1[i]`. This function replaces both `*x` and standalone `x`
    /// with `x_iter@.1[i]`.
    fn substitute_var_with_index(&self, pred_str: &str, var_name: &str) -> String {
        let indexed = format!("{}_iter@.1[i]", var_name);

        // First replace *var_name (dereferenced form)
        let dereferenced = format!("*{}", var_name);
        let result = pred_str.replace(&dereferenced, &indexed);

        // Then replace var_name when it appears at start of field access (var_name.)
        // This handles cases like "p.src" where we stripped the * for field access
        let field_access = format!("{}.", var_name);
        let indexed_field = format!("{}.", indexed);
        result.replace(&field_access, &indexed_field)
    }

    /// Generate loop invariants for map filter pattern.
    ///
    /// For a map filter operation like `votes.iter().filter(|k| k >= threshold).collect()`,
    /// generates invariants that track iteration progress and establish the postcondition.
    fn generate_map_filter_invariants(
        &self,
        source_map: &str,
        key_var: &str,
        filter_pred: &str,
    ) -> Vec<String> {
        vec![
            // Track which keys we've processed
            format!("seen_keys.subset_of({}@.dom())", source_map),
            // All seen keys are in source
            format!(
                "forall |{k}| seen_keys.contains({k}) ==> {src}@.contains_key({k})",
                k = key_var,
                src = source_map
            ),
            // Result only contains keys that satisfy filter and are in source
            format!(
                "forall |{k}| result@.contains_key({k}) ==> ({pred}) && {src}@.contains_key({k})",
                k = key_var,
                pred = filter_pred,
                src = source_map
            ),
            // Result only contains keys we've seen
            format!(
                "forall |{k}| result@.contains_key({k}) ==> seen_keys.contains({k})",
                k = key_var
            ),
            // All seen keys matching filter are in result
            format!(
                "forall |{k}| seen_keys.contains({k}) && ({pred}) ==> result@.contains_key({k})",
                k = key_var,
                pred = filter_pred
            ),
        ]
    }

    /// Generate pre-loop assertions for map filter pattern.
    /// These help Verus understand the initial state before the loop.
    fn generate_pre_loop_assertions(&self, iter_name: &str, source_map: &str) -> Vec<ExecExpr> {
        vec![
            // assert(m_keys@.0 == 0);
            ExecExpr::Assert(Box::new(ExecExpr::Binary {
                lhs: Box::new(ExecExpr::Field(
                    Box::new(ExecExpr::Var(format!("{}@", iter_name))),
                    "0".to_string(),
                )),
                op: "==".to_string(),
                rhs: Box::new(ExecExpr::Literal("0".to_string())),
            })),
            // assume(m_keys@.1.len() == source@.len());
            ExecExpr::Assume(Box::new(ExecExpr::Binary {
                lhs: Box::new(ExecExpr::MethodCall {
                    receiver: Box::new(ExecExpr::Field(
                        Box::new(ExecExpr::Var(format!("{}@", iter_name))),
                        "1".to_string(),
                    )),
                    method: "len".to_string(),
                    args: vec![],
                }),
                op: "==".to_string(),
                rhs: Box::new(ExecExpr::MethodCall {
                    receiver: Box::new(ExecExpr::Var(format!("{}@", source_map))),
                    method: "len".to_string(),
                    args: vec![],
                }),
            })),
            // assert(m_keys@.1.to_set() =~= source@.dom());
            ExecExpr::Assert(Box::new(ExecExpr::Binary {
                lhs: Box::new(ExecExpr::MethodCall {
                    receiver: Box::new(ExecExpr::Field(
                        Box::new(ExecExpr::Var(format!("{}@", iter_name))),
                        "1".to_string(),
                    )),
                    method: "to_set".to_string(),
                    args: vec![],
                }),
                op: "=~=".to_string(),
                rhs: Box::new(ExecExpr::MethodCall {
                    receiver: Box::new(ExecExpr::Var(format!("{}@", source_map))),
                    method: "dom".to_string(),
                    args: vec![],
                }),
            })),
        ]
    }

    /// Generate in-loop assertions for map filter pattern.
    /// These help Verus verify the loop body maintains invariants.
    fn generate_in_loop_assertions(&self, key_var: &str, source_map: &str) -> Vec<ExecExpr> {
        vec![
            // broadcast use vstd::std_specs::hash::group_hash_axioms;
            ExecExpr::BroadcastUse("vstd::std_specs::hash::group_hash_axioms".to_string()),
            // assume(source@.contains_key(*key));
            ExecExpr::Assume(Box::new(ExecExpr::MethodCall {
                receiver: Box::new(ExecExpr::Var(format!("{}@", source_map))),
                method: "contains_key".to_string(),
                args: vec![ExecExpr::Unary {
                    op: "*".to_string(),
                    expr: Box::new(ExecExpr::Var(key_var.to_string())),
                }],
            })),
        ]
    }

    /// Generate post-loop assertions for map filter pattern.
    /// These help Verus establish the postcondition after the loop terminates.
    fn generate_post_loop_assertions(
        &self,
        iter_name: &str,
        source_map: &str,
        key_var: &str,
        filter_pred: &str,
    ) -> Vec<ExecExpr> {
        vec![
            // assert(seen_keys.subset_of(source@.dom()));
            ExecExpr::Assert(Box::new(ExecExpr::MethodCall {
                receiver: Box::new(ExecExpr::Var("seen_keys".to_string())),
                method: "subset_of".to_string(),
                args: vec![ExecExpr::MethodCall {
                    receiver: Box::new(ExecExpr::Var(format!("{}@", source_map))),
                    method: "dom".to_string(),
                    args: vec![],
                }],
            })),
            // assume(m_keys@.0 == m_keys@.1.len()); - iterator completed
            ExecExpr::Assume(Box::new(ExecExpr::Binary {
                lhs: Box::new(ExecExpr::Field(
                    Box::new(ExecExpr::Var(format!("{}@", iter_name))),
                    "0".to_string(),
                )),
                op: "==".to_string(),
                rhs: Box::new(ExecExpr::MethodCall {
                    receiver: Box::new(ExecExpr::Field(
                        Box::new(ExecExpr::Var(format!("{}@", iter_name))),
                        "1".to_string(),
                    )),
                    method: "len".to_string(),
                    args: vec![],
                }),
            })),
            // assume(seen_keys.len() == m_keys@.0);
            ExecExpr::Assume(Box::new(ExecExpr::Binary {
                lhs: Box::new(ExecExpr::MethodCall {
                    receiver: Box::new(ExecExpr::Var("seen_keys".to_string())),
                    method: "len".to_string(),
                    args: vec![],
                }),
                op: "==".to_string(),
                rhs: Box::new(ExecExpr::Field(
                    Box::new(ExecExpr::Var(format!("{}@", iter_name))),
                    "0".to_string(),
                )),
            })),
            // proof { subset_len_equal_implies_equal(seen_keys, source@.dom()) };
            ExecExpr::ProofBlock {
                stmts: vec![ExecExpr::Call {
                    func: "subset_len_equal_implies_equal".to_string(),
                    args: vec![
                        ExecExpr::Var("seen_keys".to_string()),
                        ExecExpr::MethodCall {
                            receiver: Box::new(ExecExpr::Var(format!("{}@", source_map))),
                            method: "dom".to_string(),
                            args: vec![],
                        },
                    ],
                }],
            },
            // assert(seen_keys == source@.dom());
            ExecExpr::Assert(Box::new(ExecExpr::Binary {
                lhs: Box::new(ExecExpr::Var("seen_keys".to_string())),
                op: "==".to_string(),
                rhs: Box::new(ExecExpr::MethodCall {
                    receiver: Box::new(ExecExpr::Var(format!("{}@", source_map))),
                    method: "dom".to_string(),
                    args: vec![],
                }),
            })),
            // assert(forall |k| result@.contains_key(k) ==> filter_pred(k) && source@.contains_key(k) && result@[k] == source@[k]);
            ExecExpr::Comment(format!(
                "assert(forall |{}| result@.contains_key({}) ==> ({}) && {}@.contains_key({}) && result@[{}] == {}@[{}]);",
                key_var, key_var, filter_pred, source_map, key_var, key_var, source_map, key_var
            )),
            // assert(forall |k| source@.contains_key(k) && filter_pred(k) ==> result@.contains_key(k));
            ExecExpr::Comment(format!(
                "assert(forall |{}| {}@.contains_key({}) && ({}) ==> result@.contains_key({}));",
                key_var, source_map, key_var, filter_pred, key_var
            )),
        ]
    }

    /// Generate explicit for loop for map filter pattern.
    /// Used when `generate_loops_for_verification` is enabled.
    ///
    /// Generates:
    /// ```ignore
    /// {
    ///     broadcast use vstd::std_specs::hash::group_hash_axioms;
    ///     let m_keys = source.keys();
    ///     assert(m_keys@.0 == 0);
    ///     assume(m_keys@.1.len() == source@.len());
    ///     assert(m_keys@.1.to_set() =~= source@.dom());
    ///     let ghost mut seen_keys = Set::<K>::empty();
    ///     let mut result: HashMap<K, V> = HashMap::new();
    ///     for key in iter:m_keys
    ///     invariant
    ///         seen_keys.subset_of(source@.dom()),
    ///         forall |k| seen_keys.contains(k) ==> source@.contains_key(k),
    ///         forall |k| result@.contains_key(k) ==> filter_pred(k) && source@.contains_key(k),
    ///         forall |k| result@.contains_key(k) ==> seen_keys.contains(k),
    ///         forall |k| seen_keys.contains(k) && filter_pred(k) ==> result@.contains_key(k),
    ///     {
    ///         broadcast use vstd::std_specs::hash::group_hash_axioms;
    ///         assume(source@.contains_key(*key));
    ///         proof { seen_keys = seen_keys.insert(*key); }
    ///         if filter_condition {
    ///             let value = source.get(&key);
    ///             match value {
    ///                 Some(v) => { result.insert(*key, v.clone()); }
    ///                 None => { }
    ///             }
    ///         }
    ///     }
    ///     result
    /// }
    /// ```
    fn generate_map_filter_loop(
        &self,
        source_map: &str,
        key_var: &str,
        filter_expr: ExecExpr,
    ) -> ExecExpr {
        let iter_name = format!("{}_keys", source_map);

        // Convert filter expression to string for use in invariants
        let filter_pred = self.expr_to_invariant_string(&filter_expr);

        // Generate the invariants for this map filter pattern
        let invariants = self.generate_map_filter_invariants(source_map, key_var, &filter_pred);

        // Generate pre-loop assertions
        let pre_loop_assertions = self.generate_pre_loop_assertions(&iter_name, source_map);

        // Generate in-loop assertions
        let in_loop_assertions = self.generate_in_loop_assertions(key_var, source_map);

        // Build the loop body: in-loop assertions + proof block + if statement
        let mut loop_body = in_loop_assertions;
        // proof { seen_keys = seen_keys.insert(*key); }
        loop_body.push(ExecExpr::ProofBlock {
            stmts: vec![ExecExpr::Binary {
                lhs: Box::new(ExecExpr::Var("seen_keys".to_string())),
                op: "=".to_string(),
                rhs: Box::new(ExecExpr::MethodCall {
                    receiver: Box::new(ExecExpr::Var("seen_keys".to_string())),
                    method: "insert".to_string(),
                    args: vec![ExecExpr::Unary {
                        op: "*".to_string(),
                        expr: Box::new(ExecExpr::Var(key_var.to_string())),
                    }],
                }),
            }],
        });
        // if filter_condition { ... }
        loop_body.push(ExecExpr::If {
            cond: Box::new(filter_expr),
            then_branch: Box::new(ExecExpr::Block(vec![
                // let value = source.get(&key);
                ExecExpr::Let {
                    pattern: "value".to_string(),
                    ty: None,
                    value: Box::new(ExecExpr::MethodCall {
                        receiver: Box::new(ExecExpr::Var(source_map.to_string())),
                        method: "get".to_string(),
                        args: vec![ExecExpr::Var(key_var.to_string())],
                    }),
                },
                // match value { Some(v) => ..., None => {} }
                ExecExpr::Match {
                    scrutinee: Box::new(ExecExpr::Var("value".to_string())),
                    arms: vec![
                        (
                            "Some(v)".to_string(),
                            ExecExpr::MethodCall {
                                receiver: Box::new(ExecExpr::Var("result".to_string())),
                                method: "insert".to_string(),
                                args: vec![
                                    ExecExpr::Unary {
                                        op: "*".to_string(),
                                        expr: Box::new(ExecExpr::Var(key_var.to_string())),
                                    },
                                    ExecExpr::MethodCall {
                                        receiver: Box::new(ExecExpr::Var("v".to_string())),
                                        method: "clone".to_string(),
                                        args: vec![],
                                    },
                                ],
                            },
                        ),
                        ("None".to_string(), ExecExpr::Block(vec![])),
                    ],
                },
            ])),
            else_branch: None,
        });

        // Build the full block
        let mut stmts = vec![
            // broadcast use vstd::std_specs::hash::group_hash_axioms;
            ExecExpr::BroadcastUse("vstd::std_specs::hash::group_hash_axioms".to_string()),
            // let m_keys = source.keys();
            ExecExpr::Let {
                pattern: iter_name.clone(),
                ty: None,
                value: Box::new(ExecExpr::MethodCall {
                    receiver: Box::new(ExecExpr::Var(source_map.to_string())),
                    method: "keys".to_string(),
                    args: vec![],
                }),
            },
        ];
        // Add pre-loop assertions
        stmts.extend(pre_loop_assertions);
        // let ghost mut seen_keys = Set::empty();
        stmts.push(ExecExpr::GhostVar {
            name: "seen_keys".to_string(),
            ty: "Set<_>".to_string(),
            init: Box::new(ExecExpr::Call {
                func: "Set::empty".to_string(),
                args: vec![],
            }),
            mutable: true,
        });
        // let mut result = HashMap::new();
        stmts.push(ExecExpr::Let {
            pattern: "mut result".to_string(),
            ty: Some(ExecType::Named("HashMap<_, _>".to_string())),
            value: Box::new(ExecExpr::Call {
                func: "HashMap::new".to_string(),
                args: vec![],
            }),
        });
        // for key in iter:m_keys { ... }
        stmts.push(ExecExpr::ForInIter {
            var: key_var.to_string(),
            iter_name: iter_name.clone(),
            iter_source: Box::new(ExecExpr::Var(iter_name.clone())),
            invariants,
            body: Box::new(ExecExpr::Block(loop_body)),
        });
        // Add post-loop assertions
        let post_loop_assertions =
            self.generate_post_loop_assertions(&iter_name, source_map, key_var, &filter_pred);
        stmts.extend(post_loop_assertions);
        // result
        stmts.push(ExecExpr::Var("result".to_string()));

        ExecExpr::Block(stmts)
    }

    /// Generate explicit for loop for `.iter().any()` pattern.
    /// Used when `generate_loops_for_verification` is enabled.
    ///
    /// Generates:
    /// ```ignore
    /// {
    ///     let mut found = false;
    ///     for x in container.iter() {
    ///         if pred(&x) {
    ///             found = true;
    ///             break;
    ///         }
    ///     }
    ///     found
    /// }
    /// ```
    fn generate_any_loop(
        &self,
        container: ExecExpr,
        var_name: &str,
        predicate: ExecExpr,
    ) -> ExecExpr {
        // Convert predicate to invariant string and substitute indexed access
        let pred_str = self.expr_to_invariant_string_with_var(&predicate, var_name);
        let indexed_pred = self.substitute_var_with_index(&pred_str, var_name);

        let stmts = vec![
            // let mut found = false;
            ExecExpr::Let {
                pattern: "mut found".to_string(),
                ty: Some(ExecType::Named("bool".to_string())),
                value: Box::new(ExecExpr::Literal("false".to_string())),
            },
            // for x in container.iter() { ... }
            ExecExpr::ForInIter {
                var: var_name.to_string(),
                iter_name: format!("{}_iter", var_name),
                iter_source: Box::new(ExecExpr::MethodCall {
                    receiver: Box::new(container),
                    method: "iter".to_string(),
                    args: vec![],
                }),
                invariants: vec![
                    // found ==> exists|i: int| 0 <= i < idx && pred(container[i])
                    format!(
                        "found ==> exists|i: int| 0 <= i < {}_iter@.0 && {}",
                        var_name, indexed_pred
                    ),
                ],
                body: Box::new(ExecExpr::If {
                    cond: Box::new(predicate),
                    then_branch: Box::new(ExecExpr::Block(vec![
                        ExecExpr::Binary {
                            lhs: Box::new(ExecExpr::Var("found".to_string())),
                            op: "=".to_string(),
                            rhs: Box::new(ExecExpr::Literal("true".to_string())),
                        },
                        // break
                        ExecExpr::Break,
                    ])),
                    else_branch: None,
                }),
            },
            // found
            ExecExpr::Var("found".to_string()),
        ];

        ExecExpr::Block(stmts)
    }

    /// Generate explicit for loop for `.iter().all()` pattern.
    /// Used when `generate_loops_for_verification` is enabled.
    ///
    /// Generates:
    /// ```ignore
    /// {
    ///     let mut all_match = true;
    ///     for x in container.iter() {
    ///         if !pred(&x) {
    ///             all_match = false;
    ///             break;
    ///         }
    ///     }
    ///     all_match
    /// }
    /// ```
    fn generate_all_loop(
        &self,
        container: ExecExpr,
        var_name: &str,
        predicate: ExecExpr,
    ) -> ExecExpr {
        // Convert predicate to invariant string and substitute indexed access
        let pred_str = self.expr_to_invariant_string_with_var(&predicate, var_name);
        let indexed_pred = self.substitute_var_with_index(&pred_str, var_name);

        let stmts = vec![
            // let mut all_match = true;
            ExecExpr::Let {
                pattern: "mut all_match".to_string(),
                ty: Some(ExecType::Named("bool".to_string())),
                value: Box::new(ExecExpr::Literal("true".to_string())),
            },
            // for x in container.iter() { ... }
            ExecExpr::ForInIter {
                var: var_name.to_string(),
                iter_name: format!("{}_iter", var_name),
                iter_source: Box::new(ExecExpr::MethodCall {
                    receiver: Box::new(container),
                    method: "iter".to_string(),
                    args: vec![],
                }),
                invariants: vec![
                    // all_match <==> forall|i: int| 0 <= i < idx ==> pred(container[i])
                    format!(
                        "all_match <==> forall|i: int| 0 <= i < {}_iter@.0 ==> {}",
                        var_name, indexed_pred
                    ),
                ],
                body: Box::new(ExecExpr::If {
                    cond: Box::new(ExecExpr::Unary {
                        op: "!".to_string(),
                        expr: Box::new(predicate),
                    }),
                    then_branch: Box::new(ExecExpr::Block(vec![
                        ExecExpr::Binary {
                            lhs: Box::new(ExecExpr::Var("all_match".to_string())),
                            op: "=".to_string(),
                            rhs: Box::new(ExecExpr::Literal("false".to_string())),
                        },
                        // break
                        ExecExpr::Break,
                    ])),
                    else_branch: None,
                }),
            },
            // all_match
            ExecExpr::Var("all_match".to_string()),
        ];

        ExecExpr::Block(stmts)
    }

    /// Generate explicit for loops for `.iter().chain(other.iter()).any()` pattern.
    /// Used when `generate_loops_for_verification` is enabled.
    ///
    /// Generates:
    /// ```ignore
    /// {
    ///     let mut found = false;
    ///     for x in c1.iter() {
    ///         if pred(&x) {
    ///             found = true;
    ///             break;
    ///         }
    ///     }
    ///     if !found {
    ///         for x in c2.iter() {
    ///             if pred(&x) {
    ///                 found = true;
    ///                 break;
    ///             }
    ///         }
    ///     }
    ///     found
    /// }
    /// ```
    fn generate_chain_any_loop(
        &self,
        containers: Vec<ExecExpr>,
        var_name: &str,
        predicate: ExecExpr,
    ) -> ExecExpr {
        // Convert predicate to invariant string
        let pred_str = self.expr_to_invariant_string_with_var(&predicate, var_name);

        let mut stmts = vec![
            // let mut found = false;
            ExecExpr::Let {
                pattern: "mut found".to_string(),
                ty: Some(ExecType::Named("bool".to_string())),
                value: Box::new(ExecExpr::Literal("false".to_string())),
            },
        ];

        // Generate a loop for each container
        // Each subsequent loop is wrapped in `if !found { ... }`
        let mut remaining_loops: Vec<ExecExpr> = Vec::new();

        for (idx, container) in containers.into_iter().enumerate() {
            let iter_name = format!("{}_{}_iter", var_name, idx);
            // Substitute with index for this specific iterator
            let indexed_pred =
                pred_str.replace(&format!("*{}", var_name), &format!("{}@.1[i]", iter_name));

            let loop_stmt = ExecExpr::ForInIter {
                var: var_name.to_string(),
                iter_name: iter_name.clone(),
                iter_source: Box::new(ExecExpr::MethodCall {
                    receiver: Box::new(container),
                    method: "iter".to_string(),
                    args: vec![],
                }),
                invariants: vec![format!(
                    "found ==> exists|i: int| 0 <= i < {}@.0 && {}",
                    iter_name, indexed_pred
                )],
                body: Box::new(ExecExpr::If {
                    cond: Box::new(predicate.clone()),
                    then_branch: Box::new(ExecExpr::Block(vec![
                        ExecExpr::Binary {
                            lhs: Box::new(ExecExpr::Var("found".to_string())),
                            op: "=".to_string(),
                            rhs: Box::new(ExecExpr::Literal("true".to_string())),
                        },
                        ExecExpr::Break,
                    ])),
                    else_branch: None,
                }),
            };

            if idx == 0 {
                // First container loop goes directly in stmts
                stmts.push(loop_stmt);
            } else {
                // Subsequent loops wrapped in if !found
                remaining_loops.push(loop_stmt);
            }
        }

        // Wrap remaining loops in nested if !found blocks
        if !remaining_loops.is_empty() {
            let mut nested = remaining_loops.pop().unwrap();
            while let Some(loop_stmt) = remaining_loops.pop() {
                nested = ExecExpr::Block(vec![
                    loop_stmt,
                    ExecExpr::If {
                        cond: Box::new(ExecExpr::Unary {
                            op: "!".to_string(),
                            expr: Box::new(ExecExpr::Var("found".to_string())),
                        }),
                        then_branch: Box::new(nested),
                        else_branch: None,
                    },
                ]);
            }
            stmts.push(ExecExpr::If {
                cond: Box::new(ExecExpr::Unary {
                    op: "!".to_string(),
                    expr: Box::new(ExecExpr::Var("found".to_string())),
                }),
                then_branch: Box::new(nested),
                else_branch: None,
            });
        }

        // found
        stmts.push(ExecExpr::Var("found".to_string()));

        ExecExpr::Block(stmts)
    }

    /// Translate an annotated spec function to an exec function
    pub fn translate(&self, func: &AnnotatedFunction) -> TranspileResult<ExecFunction> {
        if !func.is_functionalizable {
            return Err(TranspileError::CodeGen {
                message: format!(
                    "Function '{}' cannot be functionalized: {}",
                    func.spec_fn.name,
                    func.non_functionalizable_reason
                        .as_deref()
                        .unwrap_or("unknown reason")
                ),
                span: None, // TODO: Convert proc_macro2::Span to miette::SourceSpan
            });
        }

        // Recursive functions are not yet supported for automatic translation.
        // They require complex proof blocks and helper functions.
        // Use manual implementation instead.
        if func.is_recursive {
            return Err(TranspileError::CodeGen {
                message: format!(
                    "Function '{}' is recursive and cannot be automatically translated. \
                     Recursive functions require manual implementation with proof blocks. \
                     Remove from annotation file or implement manually.",
                    func.spec_fn.name
                ),
                span: None,
            });
        }

        // Dispatch based on function kind
        match func.kind {
            FunctionKind::Helper => self.translate_helper(func),
            FunctionKind::Predicate => self.translate_predicate(func),
        }
    }

    /// Translate a predicate (existing logic)
    fn translate_predicate(&self, func: &AnnotatedFunction) -> TranspileResult<ExecFunction> {
        // Generate exec function name (use simple name for definitions, not qualified paths)
        let exec_name = self.translate_definition_name(&func.spec_fn.name);

        // Translate parameters
        let (params, output_names) = self.translate_params(func)?;

        // Build return type (tuple of outputs)
        let return_type = self.build_return_type(func)?;

        // Build requires clauses
        let requires = self.build_requires(func);

        // Build ensures clauses
        let ensures = self.build_ensures(func, &output_names);

        // Build output types map for struct name derivation
        let output_types: HashMap<String, Type> = func
            .spec_fn
            .params
            .iter()
            .zip(&func.param_modes)
            .filter(|(_, m)| **m == ParameterMode::Output)
            .map(|(p, _)| (p.name.clone(), p.ty.clone()))
            .collect();

        // Transform function body
        let ctx = TransformContext {
            config: &self.config,
            output_params: output_names,
            input_params: func
                .spec_fn
                .params
                .iter()
                .zip(&func.param_modes)
                .filter(|(_, m)| **m == ParameterMode::Input)
                .map(|(p, _)| p.name.clone())
                .collect(),
            output_types,
            field_substitutions: HashMap::new(),
        };
        let body = self.transform_expr(&func.spec_fn.body, &ctx)?;

        Ok(ExecFunction {
            name: exec_name,
            params,
            return_type,
            requires,
            ensures,
            decreases: Vec::new(), // Predicates are not recursive
            body,
        })
    }

    /// Translate a helper function (all params are inputs, return value is computed)
    fn translate_helper(&self, func: &AnnotatedFunction) -> TranspileResult<ExecFunction> {
        // Generate exec function name (use simple name for definitions, not qualified paths)
        let exec_name = self.translate_definition_name(&func.spec_fn.name);

        // Translate parameters (all inputs for helpers)
        let params = self.translate_helper_params(func);

        // Build return type from annotation
        let return_type = self.build_helper_return_type(func)?;

        // Build requires clauses (validity for inputs)
        let requires = self.build_helper_requires(func);

        // Build ensures clauses (result.valid() + result@ == spec_call)
        let ensures = self.build_helper_ensures(func);

        // Transform function body - no output extraction needed
        let ctx = TransformContext {
            config: &self.config,
            output_params: Vec::new(), // helpers have no output params
            input_params: func.spec_fn.params.iter().map(|p| p.name.clone()).collect(),
            output_types: HashMap::new(),
            field_substitutions: HashMap::new(),
        };
        let body = self.transform_expr(&func.spec_fn.body, &ctx)?;

        // Build decreases clause for recursive functions
        let decreases = self.build_decreases(func);

        Ok(ExecFunction {
            name: exec_name,
            params,
            return_type,
            requires,
            ensures,
            decreases,
            body,
        })
    }

    /// Build decreases clauses for recursive functions
    fn build_decreases(&self, func: &AnnotatedFunction) -> Vec<String> {
        if !func.is_recursive {
            return Vec::new();
        }

        // If the spec function has explicit decreases clauses, use them
        if !func.spec_fn.decreases.is_empty() {
            return func
                .spec_fn
                .decreases
                .iter()
                .map(|expr| self.expr_to_simple_string(expr))
                .collect();
        }

        // Otherwise, try to infer decreases from function structure
        // For functions operating on sequences, typically use first param's length
        for param in &func.spec_fn.params {
            if let crate::ast::Type::Seq(_) = &param.ty {
                return vec![format!("{}.len()", param.name)];
            }
        }

        // Default: empty (will require manual annotation)
        Vec::new()
    }

    /// Translate helper function parameters (all inputs passed by reference)
    fn translate_helper_params(&self, func: &AnnotatedFunction) -> Vec<ExecParameter> {
        func.spec_fn
            .params
            .iter()
            .map(|param| ExecParameter {
                name: param.name.clone(),
                ty: ExecType::Reference(Box::new(self.translate_type(&param.ty)), false),
                is_reference: true,
            })
            .collect()
    }

    /// Build return type for helper function from annotation
    fn build_helper_return_type(&self, func: &AnnotatedFunction) -> TranspileResult<ExecType> {
        if let Some(ref return_type_str) = func.return_type {
            Ok(self.translate_type_string(return_type_str))
        } else {
            // Fall back to the spec function's return type
            Ok(self.translate_type(&func.spec_fn.return_type))
        }
    }

    /// Translate a type string from annotation to ExecType
    fn translate_type_string(&self, type_str: &str) -> ExecType {
        // Handle generic types like Seq<Request>
        if let Some(open) = type_str.find('<') {
            let base = &type_str[..open];
            let inner_end = type_str.rfind('>').unwrap_or(type_str.len());
            let inner = &type_str[open + 1..inner_end];

            match base {
                "Seq" => ExecType::Vec(Box::new(self.translate_type_string(inner))),
                "Set" => ExecType::Generic(
                    "HashSet".to_string(),
                    vec![self.translate_type_string(inner)],
                ),
                "Map" => {
                    // Handle Map<K, V>
                    let parts: Vec<&str> = inner.split(',').map(|s| s.trim()).collect();
                    if parts.len() == 2 {
                        ExecType::HashMap(
                            Box::new(self.translate_type_string(parts[0])),
                            Box::new(self.translate_type_string(parts[1])),
                        )
                    } else {
                        ExecType::Named(self.translate_name(type_str))
                    }
                }
                _ => ExecType::Generic(
                    self.translate_name(base),
                    vec![self.translate_type_string(inner)],
                ),
            }
        } else {
            // Simple named type
            match type_str {
                "bool" => ExecType::Named("bool".to_string()),
                "int" => ExecType::Named("i64".to_string()),
                "nat" => ExecType::Named("u64".to_string()),
                _ => ExecType::Named(self.translate_name(type_str)),
            }
        }
    }

    /// Build requires clauses for helper function
    fn build_helper_requires(&self, func: &AnnotatedFunction) -> Vec<String> {
        let mut requires = Vec::new();

        // Add validity requirements for all input params
        // Skip primitive types and types in config's primitive_types list
        let validity_pred = &self.config.validity_predicate_name;
        for param in &func.spec_fn.params {
            if !self.should_skip_valid(&param.ty) {
                requires.push(format!("{}.{}()", param.name, validity_pred));
            }
        }

        // Add recommends clauses from the spec as requires
        for recommends_expr in &func.spec_fn.recommends {
            requires.push(self.expr_to_requires_string(recommends_expr));
        }

        requires
    }

    /// Build ensures clauses for helper function
    fn build_helper_ensures(&self, func: &AnnotatedFunction) -> Vec<String> {
        let mut ensures = Vec::new();

        // Check if return type should skip valid() predicate
        let skip_valid = if let Some(ref return_type_str) = func.return_type {
            self.should_skip_valid_str(return_type_str)
        } else {
            self.should_skip_valid(&func.spec_fn.return_type)
        };

        // Add result.valid() if not primitive/skipped
        if !skip_valid {
            let validity_pred = &self.config.validity_predicate_name;
            ensures.push(format!("result.{}()", validity_pred));
        }

        // Add linkage to spec: result@ == spec_fn(param1@, param2@, ...)
        let spec_call = self.build_helper_spec_call(func);
        ensures.push(spec_call);

        ensures
    }

    /// Build spec call for helper function ensures clause
    fn build_helper_spec_call(&self, func: &AnnotatedFunction) -> String {
        let args: Vec<String> = func
            .spec_fn
            .params
            .iter()
            .map(|param| format!("{}@", param.name))
            .collect();

        format!("result@ == {}({})", func.spec_fn.name, args.join(", "))
    }

    /// Translate spec name to exec name for function DEFINITIONS (L* -> C*)
    /// This never uses qualified paths - just simple name translation.
    fn translate_definition_name(&self, spec_name: &str) -> String {
        // Check if type is in explicit remapping
        if let Some(remapped) = self.config.type_remapping.get(spec_name) {
            return remapped.clone();
        }

        // Check if type starts with spec prefix (e.g., "L") followed by an uppercase letter
        // This distinguishes LAcceptor (L prefix) from LearnerTuple (part of "Learner")
        if spec_name.starts_with(&self.config.spec_prefix) {
            let rest = &spec_name[self.config.spec_prefix.len()..];
            // Only strip prefix if followed by uppercase letter (real prefix pattern like LAcceptor)
            if rest.chars().next().is_some_and(|c| c.is_ascii_uppercase()) {
                return format!("{}{}", self.config.exec_prefix, rest);
            }
        }

        // Otherwise, prepend exec prefix to the full name
        format!("{}{}", self.config.exec_prefix, spec_name)
    }

    /// Translate spec name to exec name for function CALLS (L* -> C* or qualified path)
    /// This checks function_paths for cross-module calls first, then spec_only_functions,
    /// then falls back to simple translation.
    fn translate_name(&self, spec_name: &str) -> String {
        // First check function_paths for qualified paths (cross-module calls)
        // This handles functions like "BroadcastToEveryone" -> "crate::generated::RSL::broadcast_gen::CBroadcastToEveryone"
        if let Some(qualified_path) = self.config.function_paths.get(spec_name) {
            return qualified_path.clone();
        }
        // Also check with L prefix stripped (for LBroadcastToEveryone -> BroadcastToEveryone lookup)
        if spec_name.starts_with(&self.config.spec_prefix) {
            let base_name = &spec_name[self.config.spec_prefix.len()..];
            if let Some(qualified_path) = self.config.function_paths.get(base_name) {
                return qualified_path.clone();
            }
        }

        // Check if this is a spec-only function (no C-prefix should be added)
        // These are functions that only exist in the spec layer
        if self.config.spec_only_functions.contains(spec_name) {
            return spec_name.to_string();
        }
        // Also check with L prefix stripped
        if spec_name.starts_with(&self.config.spec_prefix) {
            let base_name = &spec_name[self.config.spec_prefix.len()..];
            if self.config.spec_only_functions.contains(base_name) {
                return spec_name.to_string();
            }
        }

        // Fall back to simple name translation
        self.translate_definition_name(spec_name)
    }

    /// Translate a full path (potentially an enum variant like RslMessage::RslMessage1b)
    /// Each segment is translated individually:
    /// - RslMessage::RslMessage1b -> CMessage::CMessage1b
    ///
    /// Handles both multi-segment Paths and single-segment paths that contain "::"
    /// (the parser sometimes stores "Type::Variant" as a single segment)
    ///
    /// Special case: If a segment's remapped value already contains "::" (e.g.,
    /// "RslMessage1b" -> "CMessage::CMessage1b"), use just that remapping as the result.
    /// This prevents double-prefixing like "CMessage::CMessage::CMessage1b".
    fn translate_path(&self, path: &Path) -> String {
        if path.segments.len() == 1 {
            let segment = &path.segments[0];
            // Check if this single segment contains "::" (parser quirk)
            if segment.contains("::") {
                // Split and translate each part, but check if any translation already has ::
                let parts: Vec<&str> = segment.split("::").collect();
                // Translate the last part first - if it already contains ::, use it directly
                if let Some(last) = parts.last() {
                    let translated_last = self.translate_name(last);
                    if translated_last.contains("::") {
                        // The last segment's remapping already includes the enum type
                        return translated_last;
                    }
                }
                // Normal case: translate each part and join
                let translated: Vec<String> = parts
                    .iter()
                    .map(|s| self.translate_name(s))
                    .collect();
                translated.join("::")
            } else {
                // Simple name, just translate it
                self.translate_name(segment.as_str())
            }
        } else {
            // Multi-segment path (enum variant like Type::Variant)
            // Check if the last segment's translation already contains "::"
            // This happens when the remapping includes the full path (e.g., "RslMessage1b" -> "CMessage::CMessage1b")
            if let Some(last_segment) = path.segments.last() {
                let translated_last = self.translate_name(last_segment);
                if translated_last.contains("::") {
                    // The last segment's remapping already includes the enum type
                    // Use it directly instead of joining all segments
                    return translated_last;
                }
            }
            // Normal case: translate each segment individually
            let translated_segments: Vec<String> = path
                .segments
                .iter()
                .map(|s| self.translate_name(s))
                .collect();
            translated_segments.join("::")
        }
    }

    /// Derive nested struct name from field name
    /// e.g., "max_bal" -> "CBallot" (assuming Ballot is the type)
    /// Falls back to PascalCase: "max_bal" -> "CMaxBal"
    fn derive_nested_struct_name(&self, field_name: &str) -> String {
        // Convert snake_case to PascalCase and add exec prefix
        let pascal_case: String = field_name
            .split('_')
            .map(|s| {
                let mut chars = s.chars();
                match chars.next() {
                    Some(c) => c.to_uppercase().chain(chars).collect::<String>(),
                    None => String::new(),
                }
            })
            .collect();
        format!("{}{}", self.config.exec_prefix, pascal_case)
    }

    /// Translate spec type to exec type
    fn translate_type(&self, ty: &Type) -> ExecType {
        match ty {
            Type::Named(path) => {
                let name = path.last().unwrap_or("Unknown");
                if let Some(remapped) = self.config.type_remapping.get(name) {
                    ExecType::Named(remapped.clone())
                } else {
                    ExecType::Named(self.translate_name(name))
                }
            }
            Type::Generic(path, args) => {
                let name = path.last().unwrap_or("Unknown");
                let translated_args: Vec<_> = args.iter().map(|a| self.translate_type(a)).collect();
                ExecType::Generic(self.translate_name(name), translated_args)
            }
            Type::Seq(inner) => ExecType::Vec(Box::new(self.translate_type(inner))),
            Type::Map(k, v) => ExecType::HashMap(
                Box::new(self.translate_type(k)),
                Box::new(self.translate_type(v)),
            ),
            Type::Tuple(types) => {
                ExecType::Tuple(types.iter().map(|t| self.translate_type(t)).collect())
            }
            Type::Reference { ty, mutable } => {
                ExecType::Reference(Box::new(self.translate_type(ty)), *mutable)
            }
            Type::Bool => ExecType::Named("bool".to_string()),
            Type::Int => ExecType::Named("i64".to_string()),
            Type::Nat => ExecType::Named("u64".to_string()),
            Type::Unit => ExecType::Named("()".to_string()),
            Type::Set(inner) => {
                ExecType::Generic("HashSet".to_string(), vec![self.translate_type(inner)])
            }
        }
    }

    /// Translate parameters
    fn translate_params(
        &self,
        func: &AnnotatedFunction,
    ) -> TranspileResult<(Vec<ExecParameter>, Vec<String>)> {
        let mut params = Vec::new();
        let mut output_names = Vec::new();

        for (param, mode) in func.spec_fn.params.iter().zip(&func.param_modes) {
            match mode {
                ParameterMode::Input => {
                    params.push(ExecParameter {
                        name: param.name.clone(),
                        ty: ExecType::Reference(Box::new(self.translate_type(&param.ty)), false),
                        is_reference: true,
                    });
                }
                ParameterMode::Output => {
                    output_names.push(param.name.clone());
                    // Output params are not in the function signature,
                    // they become part of the return type
                }
            }
        }

        Ok((params, output_names))
    }

    /// Build return type from output parameters
    fn build_return_type(&self, func: &AnnotatedFunction) -> TranspileResult<ExecType> {
        let output_types: Vec<_> = func
            .spec_fn
            .params
            .iter()
            .zip(&func.param_modes)
            .filter(|(_, m)| **m == ParameterMode::Output)
            .map(|(p, _)| self.translate_type(&p.ty))
            .collect();

        match output_types.len() {
            0 => Ok(ExecType::Named("()".to_string())),
            1 => Ok(output_types.into_iter().next().unwrap()),
            _ => Ok(ExecType::Tuple(output_types)),
        }
    }

    /// Check if a type is a primitive type that doesn't have a valid() predicate
    fn is_primitive_type(ty: &crate::ast::Type) -> bool {
        use crate::ast::Type;
        match ty {
            Type::Bool | Type::Int | Type::Nat | Type::Unit => true,
            Type::Named(path) => {
                // Get the last segment of the path as the type name
                if let Some(name) = path.last() {
                    // Common primitive type names
                    matches!(
                        name,
                        "int"
                            | "nat"
                            | "bool"
                            | "i8"
                            | "i16"
                            | "i32"
                            | "i64"
                            | "i128"
                            | "isize"
                            | "u8"
                            | "u16"
                            | "u32"
                            | "u64"
                            | "u128"
                            | "usize"
                            | "char"
                            | "str"
                            | "f32"
                            | "f64"
                    )
                } else {
                    false
                }
            }
            Type::Reference { ty, .. } => Self::is_primitive_type(ty),
            _ => false,
        }
    }

    /// Check if a type should skip valid() predicate generation.
    /// Combines AST-level primitive check with config-based primitive_types list.
    fn should_skip_valid(&self, ty: &crate::ast::Type) -> bool {
        use crate::ast::Type;

        // First check AST-level primitives
        if Self::is_primitive_type(ty) {
            return true;
        }

        // Then check config-based primitive_types list
        match ty {
            Type::Named(path) => {
                if let Some(name) = path.last() {
                    // Check if type name is in primitive_types config
                    self.config.is_primitive_type(name)
                } else {
                    false
                }
            }
            Type::Reference { ty, .. } => self.should_skip_valid(ty),
            Type::Map(_, _) => {
                // Maps (HashMap) don't have valid() by default
                true
            }
            Type::Seq(_) => {
                // Sequences (Vec) don't have valid() by default in std Rust
                // Vec<T> doesn't have a built-in valid() method
                true
            }
            Type::Set(_) => {
                // Sets (HashSet) don't have valid() by default
                true
            }
            Type::Generic(path, _) => {
                // Generic types like Seq<T>, Vec<T> don't have valid() by default
                if let Some(name) = path.last() {
                    // Common collection types that don't have valid()
                    let name_str: &str = name;
                    matches!(name_str, "Vec" | "Seq" | "Set" | "HashSet" | "HashMap" | "Map")
                        || self.config.is_primitive_type(name)
                } else {
                    false
                }
            }
            _ => false,
        }
    }

    /// Check if a type string should skip valid() predicate generation.
    fn should_skip_valid_str(&self, type_str: &str) -> bool {
        // Check common primitive type strings
        if matches!(
            type_str,
            "bool" | "int" | "nat" | "i64" | "u64" | "i32" | "u32" | "usize" | "isize"
        ) {
            return true;
        }

        // Check for collection types (Vec<T>, Seq<T>, etc.)
        // These don't have valid() methods in std Rust
        if type_str.starts_with("Vec<")
            || type_str.starts_with("Seq<")
            || type_str.starts_with("Set<")
            || type_str.starts_with("HashSet<")
            || type_str.starts_with("HashMap<")
            || type_str.starts_with("Map<")
        {
            return true;
        }

        // Check config-based primitive_types list
        self.config.is_primitive_type(type_str)
    }

    /// Build requires clauses
    fn build_requires(&self, func: &AnnotatedFunction) -> Vec<String> {
        let mut requires = Vec::new();

        // Add validity requirements for input params (configurable predicate name)
        // Skip primitive types and types in config's primitive_types list
        let validity_pred = &self.config.validity_predicate_name;
        for (param, mode) in func.spec_fn.params.iter().zip(&func.param_modes) {
            if *mode == ParameterMode::Input && !self.should_skip_valid(&param.ty) {
                requires.push(format!("{}.{}()", param.name, validity_pred));
            }
        }

        // Add recommends clauses from the spec as requires
        // (recommends in spec functions become requires in exec functions)
        for recommends_expr in &func.spec_fn.recommends {
            // Convert the expression to a string for the exec function
            requires.push(self.expr_to_requires_string(recommends_expr));
        }

        requires
    }

    /// Convert an expression to a requires clause string
    fn expr_to_requires_string(&self, expr: &Expr) -> String {
        // For now, use a simple string representation
        // This can be enhanced to properly translate the expression
        match expr {
            Expr::Is(expr, variant) => {
                // Pattern: inp.msg is RslMessage1a -> inp.msg is CMessage1a
                let base = self.expr_to_simple_string(expr);
                // Translate the variant name using remapping
                let translated_variant = self.translate_name(variant);
                // For spec mode (is expression), extract just the variant part
                // since Verus doesn't allow EnumType::Variant in `is` expressions
                let spec_variant = self.extract_variant_name(&translated_variant);
                format!("{} is {}", base, spec_variant)
            }
            _ => self.expr_to_simple_string(expr),
        }
    }

    /// Extract just the variant name from a potentially qualified path.
    /// e.g., "CRslIo::CSend" -> "CSend", "CSend" -> "CSend"
    fn extract_variant_name<'a>(&self, path: &'a str) -> &'a str {
        if let Some(pos) = path.rfind("::") {
            &path[pos + 2..]
        } else {
            path
        }
    }

    /// Convert an expression to a simple string representation
    fn expr_to_simple_string(&self, expr: &Expr) -> String {
        match expr {
            Expr::Ident(name) => name.clone(),
            Expr::Field(base, field) => {
                format!("{}.{}", self.expr_to_simple_string(base), field)
            }
            Expr::Arrow(base, field) => {
                // Arrow access: expr->field becomes expr.get_field() in exec
                format!("{}.get_{}()", self.expr_to_simple_string(base), field)
            }
            Expr::MethodCall {
                receiver,
                method,
                args,
            } => {
                let recv = self.expr_to_simple_string(receiver);
                let args_str: Vec<_> = args.iter().map(|a| self.expr_to_simple_string(a)).collect();
                format!("{}.{}({})", recv, method, args_str.join(", "))
            }
            Expr::Call { func, args } => {
                // Check if this should be transformed to a method call
                if func.segments.len() == 1 {
                    let func_name = &func.segments[0];
                    if let Some(method_config) = self.config.method_calls.get(func_name) {
                        // Transform to method call
                        if method_config.receiver_arg_index < args.len() {
                            let receiver = self.expr_to_simple_string(&args[method_config.receiver_arg_index]);
                            let other_args: Vec<_> = args
                                .iter()
                                .enumerate()
                                .filter(|(i, _)| *i != method_config.receiver_arg_index)
                                .map(|(_, a)| self.expr_to_simple_string(a))
                                .collect();
                            if other_args.is_empty() {
                                return format!("{}.{}()", receiver, method_config.method_name);
                            } else {
                                return format!("{}.{}({})", receiver, method_config.method_name, other_args.join(", "));
                            }
                        }
                    }
                }

                // Function call: translate function name using translate_name (respects spec_only_functions)
                let func_name = if func.segments.len() == 1 {
                    self.translate_name(&func.segments[0])
                } else {
                    func.segments.join("::")
                };
                let args_str: Vec<_> = args.iter().map(|a| self.expr_to_simple_string(a)).collect();
                format!("{}({})", func_name, args_str.join(", "))
            }
            Expr::Is(base, variant) => {
                // Translate the variant name using remapping (e.g., RslMessage1a -> CMessage1a)
                let translated_variant = self.translate_name(variant);
                // For spec mode (is expression), extract just the variant part
                // since Verus doesn't allow EnumType::Variant in `is` expressions
                let spec_variant = self.extract_variant_name(&translated_variant);
                format!("{} is {}", self.expr_to_simple_string(base), spec_variant)
            }
            Expr::Eq(lhs, rhs) => {
                format!(
                    "({} == {})",
                    self.expr_to_simple_string(lhs),
                    self.expr_to_simple_string(rhs)
                )
            }
            Expr::Ne(lhs, rhs) => {
                format!(
                    "({} != {})",
                    self.expr_to_simple_string(lhs),
                    self.expr_to_simple_string(rhs)
                )
            }
            Expr::Lt(lhs, rhs) => {
                format!(
                    "({} < {})",
                    self.expr_to_simple_string(lhs),
                    self.expr_to_simple_string(rhs)
                )
            }
            Expr::Le(lhs, rhs) => {
                format!(
                    "({} <= {})",
                    self.expr_to_simple_string(lhs),
                    self.expr_to_simple_string(rhs)
                )
            }
            Expr::Gt(lhs, rhs) => {
                format!(
                    "({} > {})",
                    self.expr_to_simple_string(lhs),
                    self.expr_to_simple_string(rhs)
                )
            }
            Expr::Ge(lhs, rhs) => {
                format!(
                    "({} >= {})",
                    self.expr_to_simple_string(lhs),
                    self.expr_to_simple_string(rhs)
                )
            }
            Expr::Binary(lhs, op, rhs) => {
                let op_str = match op {
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
                };
                format!(
                    "({} {} {})",
                    self.expr_to_simple_string(lhs),
                    op_str,
                    self.expr_to_simple_string(rhs)
                )
            }
            Expr::Not(inner) => {
                format!("!{}", self.expr_to_simple_string(inner))
            }
            Expr::Literal(lit) => match lit {
                Literal::Bool(b) => b.to_string(),
                Literal::Int(i) => i.to_string(),
                Literal::String(s) => format!("\"{}\"", s),
            },
            Expr::Implies(lhs, rhs) => {
                format!(
                    "({} ==> {})",
                    self.expr_to_simple_string(lhs),
                    self.expr_to_simple_string(rhs)
                )
            }
            Expr::Forall { vars, triggers: _, body } => {
                let vars_str = self.bindings_to_string(vars);
                format!("forall |{}| {}", vars_str, self.expr_to_simple_string(body))
            }
            Expr::Exists { vars, body } => {
                let vars_str = self.bindings_to_string(vars);
                format!("exists |{}| {}", vars_str, self.expr_to_simple_string(body))
            }
            Expr::Index(base, idx) => {
                format!(
                    "{}.index({})",
                    self.expr_to_simple_string(base),
                    self.expr_to_simple_string(idx)
                )
            }
            _ => format!("{:?}", expr),
        }
    }

    /// Convert bindings to string representation for forall/exists
    fn bindings_to_string(&self, bindings: &[Binding]) -> String {
        bindings
            .iter()
            .map(|b| {
                let name = match &b.pattern {
                    Pattern::Ident(n) => n.clone(),
                    _ => "_".to_string(),
                };
                if let Some(ty) = &b.ty {
                    format!("{}: {}", name, self.type_to_simple_string(ty))
                } else {
                    name
                }
            })
            .collect::<Vec<_>>()
            .join(", ")
    }

    /// Convert type to simple string representation
    fn type_to_simple_string(&self, ty: &Type) -> String {
        match ty {
            Type::Named(path) => {
                // Apply naming convention transformation for known types
                let name = path.segments.last().map(|s| s.as_str()).unwrap_or("_");
                self.translate_name(name)
            }
            Type::Generic(path, args) => {
                let name = path.segments.last().map(|s| s.as_str()).unwrap_or("_");
                let args_str: Vec<_> = args.iter().map(|a| self.type_to_simple_string(a)).collect();
                format!("{}<{}>", name, args_str.join(", "))
            }
            Type::Seq(inner) => format!("Seq<{}>", self.type_to_simple_string(inner)),
            Type::Set(inner) => format!("Set<{}>", self.type_to_simple_string(inner)),
            Type::Map(k, v) => format!("Map<{}, {}>", self.type_to_simple_string(k), self.type_to_simple_string(v)),
            Type::Tuple(types) => {
                let parts: Vec<_> = types.iter().map(|t| self.type_to_simple_string(t)).collect();
                format!("({})", parts.join(", "))
            }
            Type::Bool => "bool".to_string(),
            Type::Int => "int".to_string(),
            Type::Nat => "nat".to_string(),
            Type::Unit => "()".to_string(),
            Type::Reference { ty, mutable } => {
                if *mutable {
                    format!("&mut {}", self.type_to_simple_string(ty))
                } else {
                    format!("&{}", self.type_to_simple_string(ty))
                }
            }
        }
    }

    /// Build ensures clauses linking to spec
    fn build_ensures(&self, func: &AnnotatedFunction, output_names: &[String]) -> Vec<String> {
        let mut ensures = Vec::new();

        // Build output types map for type checking
        let output_types: HashMap<String, crate::ast::Type> = func
            .spec_fn
            .params
            .iter()
            .zip(&func.param_modes)
            .filter(|(_, m)| **m == ParameterMode::Output)
            .map(|(p, _)| (p.name.clone(), p.ty.clone()))
            .collect();

        // Add validity ensures for outputs (configurable predicate name)
        // Skip primitive types and types in config's primitive_types list
        let validity_pred = &self.config.validity_predicate_name;
        for (i, name) in output_names.iter().enumerate() {
            // Check if this output's type should skip valid()
            let should_skip = output_types
                .get(name)
                .map(|ty| self.should_skip_valid(ty))
                .unwrap_or(false);

            if !should_skip {
                let accessor = if output_names.len() == 1 {
                    "result".to_string()
                } else {
                    format!("result.{}", i)
                };
                ensures.push(format!("{}.{}()", accessor, validity_pred));
            }
        }

        // Add linkage to original spec predicate
        let spec_call = self.build_spec_call(func, output_names);
        ensures.push(spec_call);

        ensures
    }

    /// Build call to spec predicate for ensures clause
    fn build_spec_call(&self, func: &AnnotatedFunction, output_names: &[String]) -> String {
        let args: Vec<_> = func
            .spec_fn
            .params
            .iter()
            .zip(&func.param_modes)
            .map(|(param, mode)| match mode {
                ParameterMode::Input => format!("{}@", param.name),
                ParameterMode::Output => {
                    let output_idx = output_names
                        .iter()
                        .position(|n| n == &param.name)
                        .unwrap_or(0);
                    if output_names.len() == 1 {
                        "result@".to_string()
                    } else {
                        format!("result.{}@", output_idx)
                    }
                }
            })
            .collect();

        format!("{}({})", func.spec_fn.name, args.join(", "))
    }

    /// Transform a spec expression to an exec expression (public interface)
    pub fn transform_expr_public(
        &self,
        expr: &Expr,
        ctx: &TransformContext,
    ) -> TranspileResult<ExecExpr> {
        self.transform_expr(expr, ctx)
    }

    /// Transform a spec expression to an exec expression
    fn transform_expr(&self, expr: &Expr, ctx: &TransformContext) -> TranspileResult<ExecExpr> {
        match expr {
            Expr::Literal(lit) => Ok(ExecExpr::Literal(self.format_literal(lit))),

            Expr::Ident(name) => Ok(ExecExpr::Var(name.clone())),

            Expr::Field(base, field) => {
                // Check if this is an output field access that has a substitution
                // e.g., s_.proposer -> s_proposer
                if let Expr::Ident(var_name) = base.as_ref() {
                    if let Some(subst) = ctx.get_field_substitution(var_name, field) {
                        return Ok(ExecExpr::Var(subst.clone()));
                    }
                }
                let base_expr = self.transform_expr(base, ctx)?;
                Ok(ExecExpr::Field(Box::new(base_expr), field.clone()))
            }

            Expr::Index(base, idx) => {
                let base_expr = self.transform_expr(base, ctx)?;
                let idx_expr = self.transform_expr(idx, ctx)?;
                Ok(ExecExpr::MethodCall {
                    receiver: Box::new(base_expr),
                    method: "index".to_string(),
                    args: vec![idx_expr],
                })
            }

            Expr::If {
                cond,
                then_branch,
                else_branch,
            } => {
                // Check for special pattern: helper predicate in then-branch, simple copy in else-branch
                // Pattern: if cond { LHelper(input, output, ...) } else { output == input }
                if let Some(helper_info) = self.detect_helper_call(then_branch, ctx) {
                    // Check if else branch is a simple copy: s_.field == s.field
                    if let Some(else_expr) = else_branch {
                        if let Some(copy_source) =
                            self.extract_simple_copy_source(else_expr, &helper_info, ctx)
                        {
                            // Generate: if cond { CHelper(&input, ...) } else { source_value }
                            let cond_expr = self.transform_expr(cond, ctx)?;
                            let helper_call = ExecExpr::Call {
                                func: self.translate_name(&helper_info.func_name),
                                args: helper_info.input_args.clone(),
                            };
                            let else_value = self.transform_expr(&copy_source, ctx)?;
                            return Ok(ExecExpr::If {
                                cond: Box::new(cond_expr),
                                then_branch: Box::new(helper_call),
                                else_branch: Some(Box::new(else_value)),
                            });
                        }
                    }
                }

                let cond_expr = self.transform_expr(cond, ctx)?;
                let then_expr = self.transform_expr(then_branch, ctx)?;
                let else_expr = else_branch
                    .as_ref()
                    .map(|e| self.transform_expr(e, ctx))
                    .transpose()?;
                Ok(ExecExpr::If {
                    cond: Box::new(cond_expr),
                    then_branch: Box::new(then_expr),
                    else_branch: else_expr.map(Box::new),
                })
            }

            Expr::Conjunction(exprs) => {
                // First, check if this is an output sequence comprehension pattern:
                // - output.len() == input_length_expr (length constraint)
                // - forall |i| 0 <= i < output.len() ==> output[i] == element_expr
                // When both are present, generate: (0..input_length_expr).map(|i| element_expr).collect()
                if let Some((output_name, length_expr, index_var, element_expr)) =
                    self.try_extract_output_seq_comprehension(exprs, ctx)
                {
                    // Generate: (0..length_expr).map(|i| element_expr).collect()
                    let length = self.transform_expr(&length_expr, ctx)?;
                    let element = self.transform_expr(&element_expr, ctx)?;

                    // Filter out the output name from the result since we're computing it here
                    let _ = output_name; // Used for verification but we're generating the whole value

                    return Ok(ExecExpr::MethodCall {
                        receiver: Box::new(ExecExpr::MethodCall {
                            receiver: Box::new(ExecExpr::Range {
                                start: Box::new(ExecExpr::Literal("0".to_string())),
                                end: Box::new(length),
                            }),
                            method: "map".to_string(),
                            args: vec![ExecExpr::Closure {
                                params: vec![index_var],
                                body: Box::new(element),
                            }],
                        }),
                        method: "collect".to_string(),
                        args: vec![],
                    });
                }

                // Next, check if this is a map update with insert pattern
                // (domain biconditional forall + value conditional forall)
                if let Some((
                    source_map,
                    key_var,
                    filter_pred,
                    new_key,
                    new_value,
                    old_value_expr,
                )) = self.try_extract_map_update_with_value(exprs, ctx)
                {
                    // Generate complete map update code:
                    // {
                    //   let mut result = source.iter().filter(|(k,_)| filter).map(|(k,v)| (k.clone(), v.clone())).collect();
                    //   result.insert(new_key.clone(), new_value.clone());
                    //   result
                    // }
                    // But we need to handle the conditional value (if k == new_key then new_value else old_value)
                    let filter_expr = self.transform_expr(&filter_pred, ctx)?;
                    let new_key_expr = self.transform_expr(&new_key, ctx)?;
                    let new_value_expr = self.transform_expr(&new_value, ctx)?;
                    let old_value = self.transform_expr(&old_value_expr, ctx)?;

                    // Generate: source.iter().filter().map(value_fn).collect() then insert new_key
                    return Ok(ExecExpr::Block(vec![
                        ExecExpr::Let {
                            pattern: "mut __result".to_string(),
                            ty: None,
                            value: Box::new(ExecExpr::MethodCall {
                                receiver: Box::new(ExecExpr::MethodCall {
                                    receiver: Box::new(ExecExpr::MethodCall {
                                        receiver: Box::new(ExecExpr::MethodCall {
                                            receiver: Box::new(ExecExpr::Var(source_map.clone())),
                                            method: "iter".to_string(),
                                            args: vec![],
                                        }),
                                        method: "filter".to_string(),
                                        args: vec![ExecExpr::Closure {
                                            params: vec![format!("({}, _)", key_var)],
                                            body: Box::new(filter_expr.clone()),
                                        }],
                                    }),
                                    method: "map".to_string(),
                                    args: vec![ExecExpr::Closure {
                                        params: vec![format!("({}, {})", key_var, "__v")],
                                        body: Box::new(ExecExpr::Tuple(vec![
                                            ExecExpr::Clone(Box::new(ExecExpr::Var(
                                                key_var.clone(),
                                            ))),
                                            old_value,
                                        ])),
                                    }],
                                }),
                                method: "collect".to_string(),
                                args: vec![],
                            }),
                        },
                        // Insert new key with new value
                        ExecExpr::MethodCall {
                            receiver: Box::new(ExecExpr::Var("__result".to_string())),
                            method: "insert".to_string(),
                            args: vec![
                                ExecExpr::Clone(Box::new(new_key_expr)),
                                ExecExpr::Clone(Box::new(new_value_expr)),
                            ],
                        },
                        ExecExpr::Var("__result".to_string()),
                    ]));
                }

                // Next, check if this is a map filter conjunction pattern
                // (multiple foralls that together define filtering a map)
                if let Some((source_map, output_map, key_var, filter_pred)) =
                    self.try_extract_map_filter_conjunction(exprs, ctx)
                {
                    // Generate: source.iter().filter(|(k, _)| predicate).cloned().collect()
                    let filter_expr = self.transform_expr(&filter_pred, ctx)?;

                    let filter_collect = ExecExpr::MethodCall {
                        receiver: Box::new(ExecExpr::MethodCall {
                            receiver: Box::new(ExecExpr::MethodCall {
                                receiver: Box::new(ExecExpr::MethodCall {
                                    receiver: Box::new(ExecExpr::Var(source_map.clone())),
                                    method: "iter".to_string(),
                                    args: vec![],
                                }),
                                method: "filter".to_string(),
                                args: vec![ExecExpr::Closure {
                                    params: vec![format!("({}, _)", key_var)],
                                    body: Box::new(filter_expr),
                                }],
                            }),
                            method: "cloned".to_string(),
                            args: vec![],
                        }),
                        method: "collect".to_string(),
                        args: vec![],
                    };

                    // Check if there's a struct literal that uses this map as a self-referential field
                    // Pattern: s_ == Struct{..., field: s_.field} where field is output_map
                    if let Some((output_var, struct_expr_with_self_ref)) =
                        self.find_self_referential_struct_literal(exprs, &output_map, ctx)
                    {
                        // Extract the field name from output_map (e.g., "s_.unexecuted_learner_state" -> "unexecuted_learner_state")
                        let field_name = self.extract_field_name_from_output_map(&output_map);

                        // Generate an intermediate variable name
                        let intermediate_var = format!("__{}", output_map.replace('.', "_"));

                        // Generate let binding: let __intermediate = filter_collect;
                        let let_binding = ExecExpr::Let {
                            pattern: intermediate_var.clone(),
                            ty: None,
                            value: Box::new(filter_collect),
                        };

                        // Transform the struct, substituting the self-referential field
                        let struct_result = self.transform_struct_with_field_substitution(
                            &struct_expr_with_self_ref,
                            &output_var,
                            &field_name,
                            &intermediate_var,
                            ctx,
                        )?;

                        return Ok(ExecExpr::Block(vec![let_binding, struct_result]));
                    }

                    // No self-referential struct literal, return just the filter
                    return Ok(filter_collect);
                }

                // Next, process any helper calls in the conjunction
                // This generates let bindings, field substitutions, and tracks bound outputs
                let (let_bindings, remaining_exprs, substitutions, bound_outputs) =
                    self.process_helper_calls_in_conjunction(exprs, ctx);

                // Create updated context with field substitutions if any helper calls were found
                let updated_ctx = if !substitutions.is_empty() {
                    Self::with_field_substitutions(ctx, substitutions)
                } else {
                    // No substitutions, use original context
                    TransformContext {
                        config: ctx.config,
                        output_params: ctx.output_params.clone(),
                        input_params: ctx.input_params.clone(),
                        output_types: ctx.output_types.clone(),
                        field_substitutions: ctx.field_substitutions.clone(),
                    }
                };

                // Use remaining exprs if we processed helper calls, otherwise use original
                let exprs_to_process = if !let_bindings.is_empty() {
                    &remaining_exprs
                } else {
                    exprs
                };

                // Check if this is a struct construction pattern (s_.f1 == e1 &&& s_.f2 == e2)
                if let Some(struct_expr) =
                    self.try_extract_struct_construction(exprs_to_process, &updated_ctx)?
                {
                    // If we have let bindings, wrap them in a block with the struct
                    if !let_bindings.is_empty() {
                        // If there are bound outputs (like sent_packets from helper calls),
                        // we need to return a tuple with the struct and those outputs
                        if !bound_outputs.is_empty() {
                            // Collect outputs: first the struct, then any helper-bound outputs
                            let mut outputs = vec![struct_expr];
                            for bound_output in &bound_outputs {
                                // Direct output params like sent_packets
                                if ctx.is_output(bound_output) {
                                    outputs.push(ExecExpr::Var(bound_output.clone()));
                                }
                            }

                            let mut block = let_bindings;
                            if outputs.len() > 1 {
                                block.push(ExecExpr::Tuple(outputs));
                            } else {
                                block.push(outputs.pop().unwrap());
                            }
                            return Ok(ExecExpr::Block(block));
                        }
                        let mut block = let_bindings;
                        block.push(struct_expr);
                        return Ok(ExecExpr::Block(block));
                    }
                    return Ok(struct_expr);
                }

                // Check if we have multiple output assignments that should be wrapped as a tuple
                // Exclude outputs that were already bound by helper calls
                let (mut output_exprs, other_exprs) = self
                    .categorize_output_assignments_with_exclusions(
                        exprs_to_process,
                        &updated_ctx,
                        &bound_outputs,
                    )?;

                // Add bound direct output params (like sent_packets) to output_exprs
                // These were bound by helper calls and need to be included in the return tuple
                for bound_output in &bound_outputs {
                    // Only include direct output params, not substitution variable names
                    if ctx.is_output(bound_output) {
                        output_exprs
                            .push((bound_output.clone(), ExecExpr::Var(bound_output.clone())));
                    }
                }

                if output_exprs.len() > 1 {
                    // Multiple outputs should be returned as a tuple
                    // Sort by output parameter order if possible
                    let sorted_outputs =
                        self.sort_outputs_by_param_order(&output_exprs, &updated_ctx);

                    // Combine let bindings + other expressions + tuple
                    let mut block = let_bindings;
                    block.extend(other_exprs);
                    block.push(ExecExpr::Tuple(sorted_outputs));
                    if block.len() == 1 {
                        Ok(block.pop().unwrap())
                    } else {
                        Ok(ExecExpr::Block(block))
                    }
                } else if output_exprs.len() == 1 {
                    // Single output - extract the ExecExpr from the tuple
                    let (_, single_output) = output_exprs.into_iter().next().unwrap();
                    let mut block = let_bindings;
                    block.extend(other_exprs);
                    block.push(single_output);
                    if block.len() == 1 {
                        Ok(block.pop().unwrap())
                    } else {
                        Ok(ExecExpr::Block(block))
                    }
                } else {
                    // No outputs detected, transform as block
                    // But first filter out spec-level constraints:
                    // - Input-only expressions (preconditions)
                    // - Equality constraints that aren't output assignments
                    // - Unmatched quantifiers (spec constraints)
                    let filtered_exprs: Vec<_> = exprs_to_process
                        .iter()
                        .filter(|e| {
                            // Skip input-only expressions (preconditions)
                            if Self::is_input_only_expression(e, &updated_ctx) {
                                return false;
                            }
                            // Skip equality constraints that aren't output assignments
                            if let Expr::Eq(lhs, rhs) = e {
                                // Only keep if one side is a direct output variable
                                let lhs_is_output = matches!(lhs.as_ref(), Expr::Ident(name) if updated_ctx.is_output(name));
                                let rhs_is_output = matches!(rhs.as_ref(), Expr::Ident(name) if updated_ctx.is_output(name));
                                if !lhs_is_output && !rhs_is_output {
                                    return false;
                                }
                            }
                            true
                        })
                        .collect();

                    let stmts: TranspileResult<Vec<_>> = filtered_exprs
                        .iter()
                        .map(|e| self.transform_expr(e, &updated_ctx))
                        .collect();
                    let mut block = let_bindings;
                    block.extend(stmts?);
                    if block.is_empty() {
                        Ok(ExecExpr::Block(vec![]))
                    } else if block.len() == 1 {
                        Ok(block.pop().unwrap())
                    } else {
                        Ok(ExecExpr::Block(block))
                    }
                }
            }

            Expr::Eq(lhs, rhs) => self.transform_equality(lhs, rhs, ctx),

            Expr::Call { func, args } => {
                let func_name = func.last().unwrap_or("unknown");

                // Check for empty collection constructors: Set::empty(), Seq::empty(), Map::empty()
                // These should be converted to proper constructors, not translated with C prefix
                if func_name == "empty" && args.is_empty() {
                    // Get the type from the path (e.g., "Set" from "Set::<int>::empty")
                    if !func.segments.is_empty() {
                        let type_part = &func.segments[0];
                        // Check if it's a collection type (may have type params like "Set::<int>")
                        if type_part.starts_with("Set") {
                            return Ok(ExecExpr::Call {
                                func: "HashSet::new".to_string(),
                                args: vec![],
                            });
                        } else if type_part.starts_with("Seq") {
                            return Ok(ExecExpr::VecLit(vec![]));
                        } else if type_part.starts_with("Map") {
                            return Ok(ExecExpr::Call {
                                func: "HashMap::new".to_string(),
                                args: vec![],
                            });
                        }
                    }
                }

                // Check if this is a helper call with output parameters
                // A helper call has output parameters if any argument is an output variable
                // In that case, we should only pass input arguments and the call returns the outputs
                if let Some(helper_info) = self.detect_helper_call(expr, ctx) {
                    // Check if this should also be transformed to a method call
                    if let Some(method_config) = self.config.method_calls.get(&helper_info.func_name) {
                        // The receiver_arg_index refers to position in original args
                        // We need to figure out which position in input_args this corresponds to

                        let receiver_orig_pos = method_config.receiver_arg_index;

                        // Check if the receiver position is an input (not an output)
                        let is_receiver_input = if receiver_orig_pos < args.len() {
                            match &args[receiver_orig_pos] {
                                Expr::Field(base, _) | Expr::Arrow(base, _) => {
                                    if let Expr::Ident(name) = base.as_ref() {
                                        !ctx.is_output(name)
                                    } else {
                                        true
                                    }
                                }
                                Expr::Ident(name) => !ctx.is_output(name),
                                _ => true,
                            }
                        } else {
                            false
                        };

                        if is_receiver_input {
                            // Count input args before the receiver in the original args
                            let inputs_before_receiver = args[..receiver_orig_pos]
                                .iter()
                                .filter(|a| {
                                    match a {
                                        Expr::Field(base, _) | Expr::Arrow(base, _) => {
                                            if let Expr::Ident(name) = base.as_ref() {
                                                !ctx.is_output(name)
                                            } else {
                                                true
                                            }
                                        }
                                        Expr::Ident(name) => !ctx.is_output(name),
                                        _ => true,
                                    }
                                })
                                .count();

                            let receiver_input_pos = inputs_before_receiver;

                            if receiver_input_pos < helper_info.input_args.len() {
                                // Get the receiver (might have & prefix, remove it for method call)
                                let receiver = match &helper_info.input_args[receiver_input_pos] {
                                    ExecExpr::Unary { op, expr } if op == "&" => (**expr).clone(),
                                    other => other.clone(),
                                };

                                let other_args: Vec<_> = helper_info.input_args
                                    .iter()
                                    .enumerate()
                                    .filter(|(i, _)| *i != receiver_input_pos)
                                    .map(|(_, a)| a.clone())
                                    .collect();

                                return Ok(ExecExpr::MethodCall {
                                    receiver: Box::new(receiver),
                                    method: method_config.method_name.clone(),
                                    args: other_args,
                                });
                            }
                        }
                    }

                    // This is a helper call - use only input args (outputs are stripped)
                    return Ok(ExecExpr::Call {
                        func: self.translate_name(&helper_info.func_name),
                        args: helper_info.input_args,
                    });
                }

                // Check if this should be transformed to a method call
                // (e.g., LMinQuorumSize(config) -> config.CMinQuorumSize())
                if func.segments.len() == 1 {
                    if let Some(method_config) = self.config.method_calls.get(func_name) {
                        if method_config.receiver_arg_index < args.len() {
                            // Transform the receiver
                            let receiver = self.transform_expr(&args[method_config.receiver_arg_index], ctx)?;

                            // Transform remaining arguments (excluding the receiver)
                            let other_args: TranspileResult<Vec<_>> = args
                                .iter()
                                .enumerate()
                                .filter(|(i, _)| *i != method_config.receiver_arg_index)
                                .map(|(_, a)| {
                                    let transformed = self.transform_expr(a, ctx)?;
                                    // Add reference for field accesses, identifiers, etc.
                                    let needs_ref = match a {
                                        Expr::Field(..) | Expr::MethodCall { .. } | Expr::Arrow(..) => true,
                                        Expr::Ident(name) => !ctx.is_output(name),
                                        _ => false,
                                    };
                                    if needs_ref {
                                        Ok(ExecExpr::Unary {
                                            op: "&".to_string(),
                                            expr: Box::new(transformed),
                                        })
                                    } else {
                                        Ok(transformed)
                                    }
                                })
                                .collect();

                            return Ok(ExecExpr::MethodCall {
                                receiver: Box::new(receiver),
                                method: method_config.method_name.clone(),
                                args: other_args?,
                            });
                        }
                    }
                }

                // Transform arguments, adding reference prefixes where appropriate
                let translated_args: TranspileResult<Vec<_>> = args
                    .iter()
                    .map(|a| {
                        let transformed = self.transform_expr(a, ctx)?;
                        // Add reference for most argument types:
                        // - Field accesses (s.field)
                        // - Method calls (obj.method())
                        // - Arrow accesses (msg->field)
                        // - Input parameters and local variables (identifiers)
                        // Do NOT add reference for:
                        // - Literals (0, "string", true)
                        // - Struct construction
                        let needs_ref = match a {
                            Expr::Field(..) | Expr::MethodCall { .. } | Expr::Arrow(..) => true,
                            Expr::Ident(name) => {
                                // Add & for input params and local variables (not outputs)
                                !ctx.is_output(name)
                            }
                            _ => false,
                        };
                        if needs_ref {
                            Ok(ExecExpr::Unary {
                                op: "&".to_string(),
                                expr: Box::new(transformed),
                            })
                        } else {
                            Ok(transformed)
                        }
                    })
                    .collect();
                Ok(ExecExpr::Call {
                    func: self.translate_name(func_name),
                    args: translated_args?,
                })
            }

            Expr::MethodCall {
                receiver,
                method,
                args,
            } => {
                let recv_expr = self.transform_expr(receiver, ctx)?;
                let translated_args: TranspileResult<Vec<_>> =
                    args.iter().map(|a| self.transform_expr(a, ctx)).collect();
                Ok(ExecExpr::MethodCall {
                    receiver: Box::new(recv_expr),
                    method: method.clone(),
                    args: translated_args?,
                })
            }

            Expr::Let {
                binding,
                value,
                body,
            } => {
                let value_expr = self.transform_expr(value, ctx)?;
                let body_expr = self.transform_expr(body, ctx)?;
                let pattern_str = self.format_binding_pattern(&binding.pattern);
                Ok(ExecExpr::Block(vec![
                    ExecExpr::Let {
                        pattern: pattern_str,
                        ty: None,
                        value: Box::new(value_expr),
                    },
                    body_expr,
                ]))
            }

            Expr::Match { scrutinee, arms } => {
                let scrut_expr = self.transform_expr(scrutinee, ctx)?;
                let mut translated_arms = Vec::new();
                for arm in arms {
                    let pattern = self.format_pattern(&arm.pattern);
                    let body = self.transform_expr(&arm.body, ctx)?;
                    translated_arms.push((pattern, body));
                }
                Ok(ExecExpr::Match {
                    scrutinee: Box::new(scrut_expr),
                    arms: translated_arms,
                })
            }

            Expr::View(inner) => {
                // @ operator - in exec code, this is typically just the value
                // For exec types, we don't need the view in most cases
                self.transform_expr(inner, ctx)
            }

            Expr::Arrow(base, field) => {
                // -> operator (enum variant field access)
                // In exec code: base.get_field() or match-based access
                let base_expr = self.transform_expr(base, ctx)?;
                Ok(ExecExpr::MethodCall {
                    receiver: Box::new(base_expr),
                    method: format!("get_{}", field),
                    args: vec![],
                })
            }

            Expr::Struct { name, fields } => {
                // Use translate_path to handle both simple struct names and enum variants
                // e.g., "Struct" -> "CStruct" or "RslMessage::RslMessage1b" -> "CMessage::CMessage1b"
                let exec_name = self.translate_path(name);
                let translated_fields: TranspileResult<Vec<_>> = fields
                    .iter()
                    .map(|(fname, fexpr)| {
                        let expr = self.transform_expr(fexpr, ctx)?;
                        // Clone input parameters when assigning to struct fields
                        let expr = self.clone_if_input_ref(expr, ctx);
                        Ok((fname.clone(), expr))
                    })
                    .collect();
                Ok(ExecExpr::Struct {
                    name: exec_name,
                    fields: translated_fields?,
                })
            }

            Expr::StructUpdate { base, fields, name } => {
                let base_expr = self.transform_expr(base, ctx)?;
                let translated_fields: TranspileResult<Vec<_>> = fields
                    .iter()
                    .map(|(fname, fexpr)| {
                        let expr = self.transform_expr(fexpr, ctx)?;
                        // Clone input parameters when assigning to struct fields
                        let expr = self.clone_if_input_ref(expr, ctx);
                        Ok((fname.clone(), expr))
                    })
                    .collect();
                // Use provided name if available, otherwise try to derive from base
                // Use translate_path to handle both struct names and enum variants
                let struct_name = if let Some(n) = name {
                    self.translate_path(n)
                } else {
                    "Unknown".to_string()
                };
                Ok(ExecExpr::StructUpdate {
                    name: struct_name,
                    base: Box::new(base_expr),
                    fields: translated_fields?,
                })
            }

            // Binary operators from Expr::Binary
            Expr::Binary(lhs, op, rhs) => {
                let op_str = match op {
                    crate::ast::BinOp::Add => "+",
                    crate::ast::BinOp::Sub => "-",
                    crate::ast::BinOp::Mul => "*",
                    crate::ast::BinOp::Div => "/",
                    crate::ast::BinOp::Mod => "%",
                    crate::ast::BinOp::And => "&&",
                    crate::ast::BinOp::Or => "||",
                    crate::ast::BinOp::BitAnd => "&",
                    crate::ast::BinOp::BitOr => "|",
                    crate::ast::BinOp::BitXor => "^",
                    crate::ast::BinOp::Shl => "<<",
                    crate::ast::BinOp::Shr => ">>",
                };
                self.transform_binary_op(lhs, rhs, op_str, ctx)
            }

            // Comparison operators as dedicated AST nodes
            Expr::Lt(lhs, rhs) => self.transform_binary_op(lhs, rhs, "<", ctx),
            Expr::Le(lhs, rhs) => self.transform_binary_op(lhs, rhs, "<=", ctx),
            Expr::Gt(lhs, rhs) => self.transform_binary_op(lhs, rhs, ">", ctx),
            Expr::Ge(lhs, rhs) => self.transform_binary_op(lhs, rhs, ">=", ctx),
            Expr::Ne(lhs, rhs) => self.transform_binary_op(lhs, rhs, "!=", ctx),

            // Enum variant check: expr is VariantName
            // In exec code, this becomes matches!(expr, Pattern { .. }) or matches!(expr, Pattern)
            Expr::Is(inner, variant) => {
                let inner_expr = self.transform_expr(inner, ctx)?;
                // Translate the variant name (e.g., RslMessage1a -> CMessage1a)
                let translated_variant = self.translate_name(variant);
                // Determine if this is a struct variant (has fields) by checking naming conventions
                // Most enum variants in this codebase are struct variants (e.g., CMessage1a { ... })
                // Unit variants like CIncompleteBatchTimerOff don't have fields
                // For safety, we assume struct variant since most variants are structs
                // The pattern will include { .. } which works for both struct variants and is harmless for unit variants
                let is_struct_variant = !translated_variant.ends_with("Off")
                    && !translated_variant.ends_with("None")
                    && !translated_variant.ends_with("Unit");
                Ok(ExecExpr::Matches {
                    expr: Box::new(inner_expr),
                    pattern: translated_variant,
                    is_struct_variant,
                })
            }

            // Unary operators
            Expr::Not(inner) => {
                let inner_expr = self.transform_expr(inner, ctx)?;
                Ok(ExecExpr::Unary {
                    op: "!".to_string(),
                    expr: Box::new(inner_expr),
                })
            }

            Expr::Unary(op, inner) => {
                let inner_expr = self.transform_expr(inner, ctx)?;
                let op_str = match op {
                    crate::ast::UnaryOp::Not => "!",
                    crate::ast::UnaryOp::Neg => "-",
                    crate::ast::UnaryOp::Deref => "*",
                };
                Ok(ExecExpr::Unary {
                    op: op_str.to_string(),
                    expr: Box::new(inner_expr),
                })
            }

            Expr::Implies(lhs, rhs) => {
                // a ==> b is equivalent to !a || b
                let lhs_expr = self.transform_expr(lhs, ctx)?;
                let rhs_expr = self.transform_expr(rhs, ctx)?;
                Ok(ExecExpr::Binary {
                    lhs: Box::new(ExecExpr::Unary {
                        op: "!".to_string(),
                        expr: Box::new(lhs_expr),
                    }),
                    op: "||".to_string(),
                    rhs: Box::new(rhs_expr),
                })
            }

            Expr::Iff(lhs, rhs) => {
                // a <==> b is equivalent to (a ==> b) && (b ==> a), which is (!a || b) && (!b || a)
                // But for exec code, we just use ==
                let lhs_expr = self.transform_expr(lhs, ctx)?;
                let rhs_expr = self.transform_expr(rhs, ctx)?;
                Ok(ExecExpr::Binary {
                    lhs: Box::new(lhs_expr),
                    op: "==".to_string(),
                    rhs: Box::new(rhs_expr),
                })
            }

            Expr::Disjunction(exprs) => {
                // Transform ||| to chain of ||
                if exprs.is_empty() {
                    return Ok(ExecExpr::Literal("false".to_string()));
                }
                let mut result = self.transform_expr(&exprs[0], ctx)?;
                for e in &exprs[1..] {
                    let next = self.transform_expr(e, ctx)?;
                    result = ExecExpr::Binary {
                        lhs: Box::new(result),
                        op: "||".to_string(),
                        rhs: Box::new(next),
                    };
                }
                Ok(result)
            }

            Expr::SeqEmpty => Ok(ExecExpr::VecLit(vec![])),

            Expr::SetEmpty => Ok(ExecExpr::Call {
                func: "HashSet::new".to_string(),
                args: vec![],
            }),

            Expr::MapEmpty => Ok(ExecExpr::Call {
                func: "HashMap::new".to_string(),
                args: vec![],
            }),

            Expr::SetLit(elems) => {
                // Generate HashSet::from([...])
                let translated: TranspileResult<Vec<_>> =
                    elems.iter().map(|e| self.transform_expr(e, ctx)).collect();
                Ok(ExecExpr::Call {
                    func: "HashSet::from".to_string(),
                    args: vec![ExecExpr::VecLit(translated?)],
                })
            }

            Expr::MapLit(pairs) => {
                // Generate HashMap::from([...])
                let translated: TranspileResult<Vec<_>> = pairs
                    .iter()
                    .map(|(k, v)| {
                        let key = self.transform_expr(k, ctx)?;
                        let val = self.transform_expr(v, ctx)?;
                        Ok(ExecExpr::Tuple(vec![key, val]))
                    })
                    .collect();
                Ok(ExecExpr::Call {
                    func: "HashMap::from".to_string(),
                    args: vec![ExecExpr::VecLit(translated?)],
                })
            }

            Expr::SeqLit(elems) => {
                let translated: TranspileResult<Vec<_>> =
                    elems.iter().map(|e| self.transform_expr(e, ctx)).collect();
                Ok(ExecExpr::VecLit(translated?))
            }

            Expr::Forall { vars, body, .. } => {
                // Try to match to a known template using the checker module
                use crate::checker::TemplateMatcher;

                if let Some(template) = TemplateMatcher::match_template(expr) {
                    self.translate_quantifier_template(&template, ctx)
                } else {
                    Err(TranspileError::UnsupportedPattern {
                        message: format!(
                            "Forall quantifier with vars {:?} doesn't match any known template",
                            vars.iter().map(|v| &v.pattern).collect::<Vec<_>>()
                        ),
                        span: None,
                        help: Some(format!(
                            "Body structure: {:?}. Consider restructuring to match a known pattern.",
                            std::mem::discriminant(body.as_ref())
                        )),
                    })
                }
            }

            Expr::Exists { vars, body, .. } => {
                // Try to translate exists quantifier to .any() or .iter().any()
                // Common pattern: exists |x| container.contains(x) && pred(x)
                // Translates to: container.iter().any(|x| pred(x))

                if vars.len() != 1 {
                    return Err(TranspileError::UnsupportedPattern {
                        message: format!(
                            "Exists quantifier with {} variables not supported (only single variable)",
                            vars.len()
                        ),
                        span: None,
                        help: Some("Consider restructuring to use a single bound variable".to_string()),
                    });
                }

                let var = &vars[0];
                let var_name = var.name_string();

                // Try to extract container(s) and predicate from body
                // Handles both single container and disjunction of containers
                if let Some((containers, predicate)) =
                    self.extract_exists_containers_and_pred(body, &var_name)
                {
                    let pred_expr = self.transform_expr(&predicate, ctx)?;

                    if self.config.generate_loops_for_verification {
                        // Generate explicit for loops for Verus verification
                        if containers.len() == 1 {
                            let container_expr = self.transform_expr(&containers[0], ctx)?;
                            Ok(self.generate_any_loop(container_expr, &var_name, pred_expr))
                        } else {
                            // Multiple containers: generate sequential loops
                            let container_exprs: TranspileResult<Vec<_>> = containers
                                .iter()
                                .map(|c| self.transform_expr(c, ctx))
                                .collect();
                            Ok(
                                self.generate_chain_any_loop(
                                    container_exprs?,
                                    &var_name,
                                    pred_expr,
                                ),
                            )
                        }
                    } else if containers.len() == 1 {
                        // Single container: container.iter().any(|x| pred(x))
                        let container_expr = self.transform_expr(&containers[0], ctx)?;
                        Ok(ExecExpr::MethodCall {
                            receiver: Box::new(ExecExpr::MethodCall {
                                receiver: Box::new(container_expr),
                                method: "iter".to_string(),
                                args: vec![],
                            }),
                            method: "any".to_string(),
                            args: vec![ExecExpr::Closure {
                                params: vec![var_name],
                                body: Box::new(pred_expr),
                            }],
                        })
                    } else {
                        // Multiple containers: container1.iter().chain(container2.iter()).any(|x| pred(x))
                        // Build the chained iterator
                        let first_container = self.transform_expr(&containers[0], ctx)?;
                        let mut chained = ExecExpr::MethodCall {
                            receiver: Box::new(first_container),
                            method: "iter".to_string(),
                            args: vec![],
                        };

                        for container in containers.iter().skip(1) {
                            let container_expr = self.transform_expr(container, ctx)?;
                            chained = ExecExpr::MethodCall {
                                receiver: Box::new(chained),
                                method: "chain".to_string(),
                                args: vec![ExecExpr::MethodCall {
                                    receiver: Box::new(container_expr),
                                    method: "iter".to_string(),
                                    args: vec![],
                                }],
                            };
                        }

                        Ok(ExecExpr::MethodCall {
                            receiver: Box::new(chained),
                            method: "any".to_string(),
                            args: vec![ExecExpr::Closure {
                                params: vec![var_name],
                                body: Box::new(pred_expr),
                            }],
                        })
                    }
                } else {
                    // Fallback: try to handle simple exists without container extraction
                    // Pattern: exists |x| pred(x) where pred doesn't have container.contains(x)
                    Err(TranspileError::UnsupportedPattern {
                        message: format!(
                            "Exists quantifier pattern not recognized. Expected: exists |{}| container.contains({}) && pred({})",
                            var_name, var_name, var_name
                        ),
                        span: None,
                        help: Some("Restructure to: exists |x| container.contains(x) && predicate(x) or (c1.contains(x) || c2.contains(x)) && predicate(x)".to_string()),
                    })
                }
            }

            Expr::Cast(inner_expr, target_type) => {
                let inner = self.transform_expr(inner_expr, ctx)?;
                let exec_type = self.translate_type(target_type);
                Ok(ExecExpr::Cast(Box::new(inner), exec_type.to_rust_string()))
            }
        }
    }

    /// Transform an equality expression
    fn transform_equality(
        &self,
        lhs: &Expr,
        rhs: &Expr,
        ctx: &TransformContext,
    ) -> TranspileResult<ExecExpr> {
        // Check if this is a simple output assignment: s_ == expr
        if let Expr::Ident(name) = lhs {
            if ctx.is_output(name) {
                // Check if rhs is also an identifier (copy case)
                if let Expr::Ident(rhs_name) = rhs {
                    if ctx.input_params.contains(rhs_name) {
                        return Ok(ExecExpr::Clone(Box::new(ExecExpr::Var(rhs_name.clone()))));
                    }
                }
                return self.transform_expr(rhs, ctx);
            }
        }

        // Check if this is a field assignment: s_.field == expr
        if let Expr::Field(base, _field) = lhs {
            if let Expr::Ident(name) = base.as_ref() {
                if ctx.is_output(name) {
                    // This is a field assignment - will be collected by try_extract_struct_construction
                    return self.transform_expr(rhs, ctx);
                }
            }
        }

        // Regular equality comparison
        let lhs_expr = self.transform_expr(lhs, ctx)?;
        let rhs_expr = self.transform_expr(rhs, ctx)?;
        Ok(ExecExpr::Binary {
            lhs: Box::new(lhs_expr),
            op: "==".to_string(),
            rhs: Box::new(rhs_expr),
        })
    }

    /// Categorize expressions in a conjunction into output assignments and other expressions.
    ///
    /// Excludes outputs that have already been bound (e.g., by helper calls).
    /// Returns: (Vec of output expressions with their param name, Vec of other expressions)
    fn categorize_output_assignments_with_exclusions(
        &self,
        exprs: &[Expr],
        ctx: &TransformContext,
        exclude_outputs: &HashSet<String>,
    ) -> TranspileResult<OutputAssignments> {
        let mut output_exprs: Vec<(String, ExecExpr)> = Vec::new();
        let mut other_exprs: Vec<ExecExpr> = Vec::new();

        for expr in exprs {
            if let Expr::Eq(lhs, rhs) = expr {
                // Check if LHS is an output parameter: s_ == expr or sent_packets == expr
                if let Expr::Ident(name) = lhs.as_ref() {
                    if ctx.is_output(name) && !exclude_outputs.contains(name) {
                        // Check if RHS is an input param - if so, generate clone
                        if let Expr::Ident(rhs_name) = rhs.as_ref() {
                            if ctx.input_params.contains(rhs_name) {
                                output_exprs.push((
                                    name.clone(),
                                    ExecExpr::Clone(Box::new(ExecExpr::Var(rhs_name.clone()))),
                                ));
                                continue;
                            }
                        }
                        let transformed = self.transform_expr(rhs, ctx)?;
                        output_exprs.push((name.clone(), transformed));
                        continue;
                    }
                }
                // Also check if RHS is an output parameter: expr == s_
                if let Expr::Ident(name) = rhs.as_ref() {
                    if ctx.is_output(name) && !exclude_outputs.contains(name) {
                        // Check if LHS is an input param - if so, generate clone
                        if let Expr::Ident(lhs_name) = lhs.as_ref() {
                            if ctx.input_params.contains(lhs_name) {
                                output_exprs.push((
                                    name.clone(),
                                    ExecExpr::Clone(Box::new(ExecExpr::Var(lhs_name.clone()))),
                                ));
                                continue;
                            }
                        }
                        let transformed = self.transform_expr(lhs, ctx)?;
                        output_exprs.push((name.clone(), transformed));
                        continue;
                    }
                }

                // Skip equality constraints that are NOT direct output assignments
                // These are spec-level constraints (like `output.len() == expected_len`)
                // that don't translate to executable code
                continue;
            }

            // Skip input-only expressions - these are preconditions that should not
            // be emitted as executable code (they belong in requires clause)
            if Self::is_input_only_expression(expr, ctx) {
                // Skip this expression - it's a precondition constraint
                continue;
            }

            // Skip quantifier expressions that don't produce direct output assignments
            // (they define constraints, not computations, unless handled by special patterns)
            // Note: quantifiers that define output values should be handled by special patterns
            // earlier in the conjunction handling (like seq comprehension, map filter, etc.)
            if matches!(expr, Expr::Forall { .. } | Expr::Exists { .. }) {
                // Forall/exists that weren't handled by special patterns should be skipped
                // They're spec-level constraints
                continue;
            }

            // Not an output assignment, add to other expressions
            let transformed = self.transform_expr(expr, ctx)?;
            other_exprs.push(transformed);
        }

        Ok((output_exprs, other_exprs))
    }

    /// Sort output expressions by their parameter order in the context
    fn sort_outputs_by_param_order(
        &self,
        outputs: &[(String, ExecExpr)],
        ctx: &TransformContext,
    ) -> Vec<ExecExpr> {
        let mut sorted: Vec<_> = outputs.to_vec();
        sorted.sort_by(|a, b| {
            let a_idx = ctx
                .output_params
                .iter()
                .position(|p| p == &a.0)
                .unwrap_or(usize::MAX);
            let b_idx = ctx
                .output_params
                .iter()
                .position(|p| p == &b.0)
                .unwrap_or(usize::MAX);
            a_idx.cmp(&b_idx)
        });
        sorted.into_iter().map(|(_, e)| e).collect()
    }

    /// Detect helper predicate calls with output parameters
    /// A helper call has output parameters if any argument is `output_var.field` or a direct output var
    fn detect_helper_call(&self, expr: &Expr, ctx: &TransformContext) -> Option<HelperCallInfo> {
        if let Expr::Call { func, args } = expr {
            let func_name = func.last()?.to_string();
            let mut input_args = Vec::new();
            let mut output_fields = Vec::new();
            let mut output_params = Vec::new();

            for arg in args {
                // Check if argument is output_var.field (e.g., s_.proposer)
                if let Expr::Field(base, field) = arg {
                    if let Expr::Ident(var_name) = base.as_ref() {
                        if ctx.is_output(var_name) {
                            // This is an output field argument
                            output_fields.push((var_name.clone(), field.clone()));
                            continue;
                        }
                    }
                }
                // Check if argument is a direct output parameter (e.g., sent_packets)
                if let Expr::Ident(var_name) = arg {
                    if ctx.is_output(var_name) {
                        // This is a direct output parameter
                        output_params.push(var_name.clone());
                        continue;
                    }
                }
                // Not an output, it's an input
                // Transform it and add to inputs with reference prefix where appropriate
                if let Ok(transformed) = self.transform_expr(arg, ctx) {
                    // Add reference for most argument types:
                    // - Field accesses (s.field)
                    // - Method calls (obj.method())
                    // - Arrow accesses (msg->field)
                    // - Input parameters and local variables (not outputs)
                    let needs_ref = match arg {
                        Expr::Field(..) | Expr::MethodCall { .. } | Expr::Arrow(..) => true,
                        Expr::Ident(name) => {
                            // Add & for input params and local variables (not outputs)
                            !ctx.is_output(name)
                        }
                        _ => false,
                    };
                    if needs_ref {
                        input_args.push(ExecExpr::Unary {
                            op: "&".to_string(),
                            expr: Box::new(transformed),
                        });
                    } else {
                        input_args.push(transformed);
                    }
                }
            }

            if !output_fields.is_empty() || !output_params.is_empty() {
                return Some(HelperCallInfo {
                    func_name,
                    input_args,
                    output_fields,
                    output_params,
                });
            }
        }
        None
    }

    /// Generate a let binding for a helper call with output parameters
    /// Examples:
    /// - LProposerProcessRequest(s.proposer, s_.proposer, packet)
    ///   Generates: let s_proposer = CProposerProcessRequest(&s.proposer, &packet);
    /// - LAcceptorProcess1a(s.acceptor, s_.acceptor, packet, sent_packets)
    ///   Generates: let (s_acceptor, sent_packets) = CAcceptorProcess1a(&s.acceptor, &packet);
    fn generate_helper_let_binding(&self, info: &HelperCallInfo) -> ExecExpr {
        // Collect all output variable names
        let mut output_names: Vec<String> = Vec::new();

        // Add field outputs: (output_var, field) -> "var_field"
        for (var, field) in &info.output_fields {
            output_names.push(format!("{}_{}", var.trim_end_matches('_'), field));
        }

        // Add direct output params
        output_names.extend(info.output_params.clone());

        // Generate the pattern
        let pattern = if output_names.len() == 1 {
            output_names[0].clone()
        } else {
            format!("({})", output_names.join(", "))
        };

        // Build the function call (or method call if configured)
        let call = if let Some(method_config) = self.config.method_calls.get(&info.func_name) {
            // This function should be a method call
            // receiver_arg_index should be 0 in most cases for this pattern
            if method_config.receiver_arg_index < info.input_args.len() {
                // Get the receiver (might have & prefix, remove it for method call)
                let receiver = match &info.input_args[method_config.receiver_arg_index] {
                    ExecExpr::Unary { op, expr } if op == "&" => (**expr).clone(),
                    other => other.clone(),
                };

                let other_args: Vec<_> = info.input_args
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| *i != method_config.receiver_arg_index)
                    .map(|(_, a)| a.clone())
                    .collect();

                ExecExpr::MethodCall {
                    receiver: Box::new(receiver),
                    method: method_config.method_name.clone(),
                    args: other_args,
                }
            } else {
                // Fall back to function call if receiver index is invalid
                ExecExpr::Call {
                    func: self.translate_name(&info.func_name),
                    args: info.input_args.clone(),
                }
            }
        } else {
            ExecExpr::Call {
                func: self.translate_name(&info.func_name),
                args: info.input_args.clone(),
            }
        };

        ExecExpr::Let {
            pattern,
            ty: None,
            value: Box::new(call),
        }
    }

    /// Extract simple copy source from else branch of conditional helper
    /// Pattern: s_.field == s.field returns Some(s.field)
    /// Pattern: s_.field == expr returns Some(expr) if field matches helper output
    fn extract_simple_copy_source(
        &self,
        expr: &Expr,
        helper_info: &HelperCallInfo,
        ctx: &TransformContext,
    ) -> Option<Expr> {
        // Check for equality: s_.field == s.field or s_.field == other_expr
        if let Expr::Eq(lhs, rhs) = expr {
            // Check if LHS is an output field that matches one of the helper's output fields
            if let Expr::Field(base, field) = lhs.as_ref() {
                if let Expr::Ident(var_name) = base.as_ref() {
                    if ctx.is_output(var_name) {
                        // Check if this field is one of the helper's outputs
                        for (out_var, out_field) in &helper_info.output_fields {
                            if var_name == out_var && field == out_field {
                                // Return the RHS as the copy source
                                return Some((**rhs).clone());
                            }
                        }
                    }
                }
            }
            // Also check swapped: s.field == s_.field
            if let Expr::Field(base, field) = rhs.as_ref() {
                if let Expr::Ident(var_name) = base.as_ref() {
                    if ctx.is_output(var_name) {
                        for (out_var, out_field) in &helper_info.output_fields {
                            if var_name == out_var && field == out_field {
                                return Some((**lhs).clone());
                            }
                        }
                    }
                }
            }
        }
        None
    }

    /// Get the substitution map from helper call info
    /// Maps "s_.proposer" style access to variable name "s_proposer"
    fn get_helper_substitutions(info: &HelperCallInfo) -> HashMap<(String, String), String> {
        let mut map = HashMap::new();
        for (var, field) in &info.output_fields {
            let var_name = format!("{}_{}", var.trim_end_matches('_'), field);
            map.insert((var.clone(), field.clone()), var_name);
        }
        map
    }

    /// Transform a conditional field assignment pattern
    /// Pattern: if cond { helper_call } else { source_value }
    fn transform_conditional_field(
        &self,
        cond: &Expr,
        helper_info: &HelperCallInfo,
        copy_source: &Expr,
        ctx: &TransformContext,
    ) -> TranspileResult<ExecExpr> {
        // Transform condition
        let cond_expr = self.transform_expr(cond, ctx)?;

        // Build the helper call
        let helper_call = ExecExpr::Call {
            func: self.translate_name(&helper_info.func_name),
            args: helper_info.input_args.clone(),
        };

        // Transform the else (copy) source
        let else_value = self.transform_expr(copy_source, ctx)?;

        Ok(ExecExpr::If {
            cond: Box::new(cond_expr),
            then_branch: Box::new(helper_call),
            else_branch: Some(Box::new(else_value)),
        })
    }

    /// Process helper calls in a conjunction, generating let bindings and collecting substitutions.
    ///
    /// Returns: (let_bindings, remaining_exprs, combined_substitutions, bound_outputs)
    /// where bound_outputs tracks which direct output params (like sent_packets) were bound by helper calls.
    fn process_helper_calls_in_conjunction(
        &self,
        exprs: &[Expr],
        ctx: &TransformContext,
    ) -> HelperCallResult {
        let mut let_bindings = Vec::new();
        let mut remaining_exprs = Vec::new();
        let mut combined_substitutions = HashMap::new();
        let mut bound_outputs: HashSet<String> = HashSet::new();

        for expr in exprs {
            if let Some(info) = self.detect_helper_call(expr, ctx) {
                // Generate let binding for this helper call
                let let_binding = self.generate_helper_let_binding(&info);
                let_bindings.push(let_binding);

                // Add substitutions from this helper call (for field accesses)
                let subs = Self::get_helper_substitutions(&info);
                combined_substitutions.extend(subs);

                // Track which direct outputs were bound
                bound_outputs.extend(info.output_params.clone());

                // Also track field-based outputs that map to substitutions
                for (var, field) in &info.output_fields {
                    let sub_name = format!("{}_{}", var.trim_end_matches('_'), field);
                    // Mark that this field has been handled
                    bound_outputs.insert(sub_name);
                }
            } else {
                // Not a helper call, keep for later processing
                remaining_exprs.push(expr.clone());
            }
        }

        (
            let_bindings,
            remaining_exprs,
            combined_substitutions,
            bound_outputs,
        )
    }

    /// Create a new context with additional field substitutions
    fn with_field_substitutions<'b>(
        ctx: &'b TransformContext<'b>,
        additional: HashMap<(String, String), String>,
    ) -> TransformContext<'b> {
        let mut new_subs = ctx.field_substitutions.clone();
        new_subs.extend(additional);
        TransformContext {
            config: ctx.config,
            output_params: ctx.output_params.clone(),
            input_params: ctx.input_params.clone(),
            output_types: ctx.output_types.clone(),
            field_substitutions: new_subs,
        }
    }

    /// Try to extract struct construction from a conjunction of field assignments
    fn try_extract_struct_construction(
        &self,
        exprs: &[Expr],
        ctx: &TransformContext,
    ) -> TranspileResult<Option<ExecExpr>> {
        // Track direct field assignments: output_var -> [(field_name, expr)]
        let mut field_assignments: HashMap<String, Vec<(String, Expr)>> = HashMap::new();
        // Track nested field assignments: output_var -> { outer_field -> [(inner_field, expr)] }
        let mut nested_assignments: HashMap<String, HashMap<String, Vec<(String, Expr)>>> =
            HashMap::new();
        // Track pre-translated nested structs: output_var -> [(field_name, ExecExpr)]
        let mut pre_translated: HashMap<String, Vec<(String, ExecExpr)>> = HashMap::new();
        let mut other_exprs = Vec::new();

        for expr in exprs {
            if let Expr::Eq(lhs, rhs) = expr {
                // Check for nested field: s_.outer.inner == expr
                if let Expr::Field(mid, inner_field) = lhs.as_ref() {
                    if let Expr::Field(base, outer_field) = mid.as_ref() {
                        if let Expr::Ident(name) = base.as_ref() {
                            if ctx.is_output(name) {
                                nested_assignments
                                    .entry(name.clone())
                                    .or_default()
                                    .entry(outer_field.clone())
                                    .or_default()
                                    .push((inner_field.clone(), *rhs.clone()));
                                continue;
                            }
                        }
                    }
                }
                // Check for direct field: s_.field == expr
                if let Expr::Field(base, field) = lhs.as_ref() {
                    if let Expr::Ident(name) = base.as_ref() {
                        if ctx.is_output(name) {
                            field_assignments
                                .entry(name.clone())
                                .or_default()
                                .push((field.clone(), *rhs.clone()));
                            continue;
                        }
                    }
                }
                // Check for s_ == s (full copy)
                if let Expr::Ident(name) = lhs.as_ref() {
                    if ctx.is_output(name) {
                        other_exprs.push(expr.clone());
                        continue;
                    }
                }
            }
            // Pattern 2: !s_.field (equivalent to s_.field == false)
            else if let Expr::Not(inner) = expr {
                if let Expr::Field(base, field) = inner.as_ref() {
                    if let Expr::Ident(name) = base.as_ref() {
                        if ctx.is_output(name) {
                            field_assignments.entry(name.clone()).or_default().push((
                                field.clone(),
                                Expr::Literal(crate::ast::Literal::Bool(false)),
                            ));
                            continue;
                        }
                    }
                }
            }
            // Pattern 3: s_.field (equivalent to s_.field == true)
            else if let Expr::Field(base, field) = expr {
                if let Expr::Ident(name) = base.as_ref() {
                    if ctx.is_output(name) {
                        field_assignments.entry(name.clone()).or_default().push((
                            field.clone(),
                            Expr::Literal(crate::ast::Literal::Bool(true)),
                        ));
                        continue;
                    }
                }
            }
            // Pattern 3b: s_.field is Variant (field should be initialized to enum variant)
            // Example: s.incomplete_batch_timer is IncompleteBatchTimerOff
            // Becomes: incomplete_batch_timer: CIncompleteBatchTimer::CIncompleteBatchTimerOff
            else if let Expr::Is(base_expr, variant) = expr {
                if let Expr::Field(base, field) = base_expr.as_ref() {
                    if let Expr::Ident(name) = base.as_ref() {
                        if ctx.is_output(name) {
                            // Translate the variant name using remapping
                            // The remapping should provide the fully qualified path like
                            // "IncompleteBatchTimerOff" -> "CIncompleteBatchTimer::CIncompleteBatchTimerOff"
                            let translated_variant = self.translate_name(variant);
                            // Store as a Var expression with the translated variant name
                            pre_translated
                                .entry(name.clone())
                                .or_default()
                                .push((field.clone(), ExecExpr::Var(translated_variant)));
                            continue;
                        }
                    }
                }
            }
            // Pattern 4: if cond { helper_call(..., output.field, ...) } else { output.field == input.field }
            // This pattern sets a field conditionally via helper predicate
            else if let Expr::If {
                cond: if_cond,
                then_branch,
                else_branch: Some(else_br),
            } = expr
            {
                // First, try the helper call pattern
                if let Some(helper_info) = self.detect_helper_call(then_branch, ctx) {
                    // Check if else branch is output.field == source
                    if let Some(copy_source) =
                        self.extract_simple_copy_source(else_br, &helper_info, ctx)
                    {
                        // Found conditional field assignment pattern
                        // Get the output field from helper_info
                        if let Some((out_var, field_name)) = helper_info.output_fields.first() {
                            // Transform the conditional and store as pre-translated field
                            if let Ok(transformed) = self.transform_conditional_field(
                                if_cond,
                                &helper_info,
                                &copy_source,
                                ctx,
                            ) {
                                pre_translated
                                    .entry(out_var.clone())
                                    .or_default()
                                    .push((field_name.clone(), transformed));
                                continue;
                            }
                        }
                    }
                }

                // Pattern 5: Conditional field assignments
                // if cond { s_.field1 == val1 && s_.field2 == val2 } else { s_.field1 == val3 && s_.field2 == val4 }
                if let Some(conditional_fields) = self.try_extract_conditional_field_assignments(
                    if_cond,
                    then_branch,
                    else_br,
                    ctx,
                ) {
                    // Add each conditional field to field_assignments
                    for (output_var, field_name, then_expr, else_expr) in conditional_fields {
                        // Generate: if cond { then_val } else { else_val }
                        let conditional_expr = Expr::If {
                            cond: if_cond.clone(),
                            then_branch: Box::new(then_expr),
                            else_branch: Some(Box::new(else_expr)),
                        };
                        field_assignments
                            .entry(output_var)
                            .or_default()
                            .push((field_name, conditional_expr));
                    }
                    continue;
                }

                // Pattern 6: Conditional helper calls that compute output fields
                // if cond { Helper1(s.field, s_.field, ios) } else { Helper2(s.field, idx, s_.field, ios) }
                if let Some(conditional_helper_info) =
                    self.try_extract_conditional_helper_calls(if_cond, then_branch, else_br, ctx)
                {
                    // Transform the condition
                    if let Ok(cond_expr) = self.transform_expr(if_cond, ctx) {
                        // Add each output field from the helper calls as a pre-translated conditional
                        for (output_var, field_name, then_call, else_call) in
                            conditional_helper_info
                        {
                            // Create a conditional ExecExpr that calls the appropriate helper
                            let conditional_exec = ExecExpr::If {
                                cond: Box::new(cond_expr.clone()),
                                then_branch: Box::new(then_call),
                                else_branch: Some(Box::new(else_call)),
                            };
                            pre_translated
                                .entry(output_var)
                                .or_default()
                                .push((field_name, conditional_exec));
                        }
                        continue;
                    }
                }
            }
            other_exprs.push(expr.clone());
        }

        // Check for sequence initialization patterns: length constraint + forall element constraint
        // Pattern: output.field.len() == length && forall |i| ... ==> output.field[i] == element
        if let Some((out_var, field_name, length_expr, element_expr)) =
            self.try_extract_seq_init_pattern(exprs, ctx)
        {
            // Generate: (0..length).map(|_| element).collect()
            let length = self.transform_expr(&length_expr, ctx)?;
            let element = self.transform_expr(&element_expr, ctx)?;
            let seq_init = ExecExpr::MethodCall {
                receiver: Box::new(ExecExpr::MethodCall {
                    receiver: Box::new(ExecExpr::Range {
                        start: Box::new(ExecExpr::Literal("0".to_string())),
                        end: Box::new(length),
                    }),
                    method: "map".to_string(),
                    args: vec![ExecExpr::Closure {
                        params: vec!["_".to_string()],
                        body: Box::new(element),
                    }],
                }),
                method: "collect".to_string(),
                args: vec![],
            };

            // Store pre-translated (don't add placeholder to field_assignments)
            pre_translated
                .entry(out_var)
                .or_default()
                .push((field_name, seq_init));

            // Remove the length and forall expressions from other_exprs since they're now handled
            other_exprs.retain(|e| {
                // Keep expressions that aren't the length constraint or forall
                if let Expr::Eq(lhs, rhs) = e {
                    if let Expr::MethodCall { method, .. } = lhs.as_ref() {
                        if method == "len" {
                            return false;
                        }
                    }
                    if let Expr::MethodCall { method, .. } = rhs.as_ref() {
                        if method == "len" {
                            return false;
                        }
                    }
                }
                if let Expr::Forall { .. } = e {
                    return false;
                }
                true
            });
        }

        // Convert nested assignments to pre-translated struct constructions
        for (output_name, nested_map) in nested_assignments {
            for (outer_field, inner_fields) in nested_map {
                // Build a nested struct construction for this outer field
                let struct_name = self.derive_nested_struct_name(&outer_field);
                let translated_inner: TranspileResult<Vec<_>> = inner_fields
                    .into_iter()
                    .map(|(fname, fexpr)| {
                        let expr = self.transform_expr(&fexpr, ctx)?;
                        // Clone input parameters when assigning to struct fields
                        let expr = self.clone_if_input_ref(expr, ctx);
                        Ok((fname, expr))
                    })
                    .collect();
                let inner_struct = ExecExpr::Struct {
                    name: struct_name,
                    fields: translated_inner?,
                };
                // Store pre-translated nested struct
                pre_translated
                    .entry(output_name.clone())
                    .or_default()
                    .push((outer_field, inner_struct));
            }
        }

        // If we have field assignments or pre-translated fields, construct the struct
        if !field_assignments.is_empty() || !pre_translated.is_empty() {
            let mut results = Vec::new();

            // Check if any other_expr is a struct literal (s_ == Struct{...}) that
            // corresponds to an output with field assignments. If so, we should NOT
            // generate a separate struct from field_assignments - instead, we'll
            // substitute field values when processing the struct literal.
            let mut outputs_with_struct_literals: std::collections::HashSet<String> =
                std::collections::HashSet::new();
            for expr in &other_exprs {
                if let Expr::Eq(lhs, rhs) = expr {
                    if let Expr::Ident(output_name) = lhs.as_ref() {
                        if ctx.is_output(output_name) {
                            if let Expr::Struct { .. } = rhs.as_ref() {
                                outputs_with_struct_literals.insert(output_name.clone());
                            }
                        }
                    }
                }
            }

            // Collect all output variable names
            let mut all_outputs: std::collections::HashSet<String> =
                field_assignments.keys().cloned().collect();
            all_outputs.extend(pre_translated.keys().cloned());

            for output_name in all_outputs {
                // Skip outputs that have a corresponding struct literal in other_exprs
                // Those will be handled with substitution in the other_exprs loop
                if outputs_with_struct_literals.contains(&output_name) {
                    continue;
                }

                // Get the struct name from the output parameter's type
                let struct_name = ctx
                    .get_output_struct_name(&output_name)
                    .map(|n| self.translate_name(&n))
                    .unwrap_or_else(|| {
                        // Fallback: derive from variable name
                        self.translate_name(output_name.trim_end_matches('_'))
                    });

                // Find the input variable this is based on (usually same name without _)
                let base_name = output_name.trim_end_matches('_');
                let base_input = if ctx.input_params.contains(&base_name.to_string()) {
                    Some(base_name.to_string())
                } else {
                    None
                };

                // Translate direct field expressions
                let direct_fields = field_assignments.remove(&output_name).unwrap_or_default();
                let mut translated_fields: Vec<_> = direct_fields
                    .into_iter()
                    .map(|(fname, fexpr)| {
                        let expr = self.transform_expr(&fexpr, ctx)?;
                        // Clone input parameters when assigning to struct fields
                        let expr = self.clone_if_input_ref(expr, ctx);
                        Ok((fname, expr))
                    })
                    .collect::<TranspileResult<Vec<_>>>()?;

                // Add pre-translated nested struct fields
                if let Some(nested_fields) = pre_translated.remove(&output_name) {
                    translated_fields.extend(nested_fields);
                }

                // Add fields from helper call substitutions (e.g., election_state from ElectionStateInit)
                // Look for substitutions where the output variable matches (with trailing _ removed)
                let output_base = output_name.trim_end_matches('_');
                for ((subst_var, field_name), var_name) in &ctx.field_substitutions {
                    let subst_base = subst_var.trim_end_matches('_');
                    if subst_base == output_base {
                        // Check if this field is already in translated_fields
                        let already_present = translated_fields.iter().any(|(f, _)| f == field_name);
                        if !already_present {
                            translated_fields.push((field_name.clone(), ExecExpr::Var(var_name.clone())));
                        }
                    }
                }

                if let Some(base) = base_input {
                    // Struct update syntax: S { field: value, ..base.clone() }
                    results.push(ExecExpr::StructUpdate {
                        name: struct_name,
                        base: Box::new(ExecExpr::Clone(Box::new(ExecExpr::Var(base)))),
                        fields: translated_fields,
                    });
                } else {
                    // Generate a struct literal
                    results.push(ExecExpr::Struct {
                        name: struct_name,
                        fields: translated_fields,
                    });
                }
            }

            // Add any other expressions, filtering out input-only preconditions
            // Also handle self-referential struct literals by substituting field values
            for expr in other_exprs {
                // Skip input-only expressions - these are preconditions
                if Self::is_input_only_expression(&expr, ctx) {
                    continue;
                }

                // Check if this is s_ == Struct{...} with self-referential fields
                if let Expr::Eq(lhs, rhs) = &expr {
                    if let Expr::Ident(output_name) = lhs.as_ref() {
                        if ctx.is_output(output_name) {
                            if let Expr::Struct { name, fields } = rhs.as_ref() {
                                // Check for self-referential fields and substitute from field_assignments
                                let exec_name =
                                    self.translate_name(name.last().unwrap_or("Unknown"));
                                let base_name = output_name.trim_end_matches('_');
                                let base_input =
                                    if ctx.input_params.contains(&base_name.to_string()) {
                                        Some(base_name.to_string())
                                    } else {
                                        None
                                    };

                                let translated_fields: TranspileResult<Vec<_>> = fields
                                    .iter()
                                    .map(|(fname, fexpr)| {
                                        // Check if this field is self-referential (field: output.field)
                                        if let Expr::Field(field_base, field_name) = fexpr {
                                            if let Expr::Ident(ref_name) = field_base.as_ref() {
                                                if ref_name == output_name && field_name == fname {
                                                    // Self-referential! Look for field assignment
                                                    if let Some(assignments) =
                                                        field_assignments.get(output_name)
                                                    {
                                                        for (assigned_field, assigned_expr) in
                                                            assignments
                                                        {
                                                            if assigned_field == fname {
                                                                let e = self.transform_expr(
                                                                    assigned_expr,
                                                                    ctx,
                                                                )?;
                                                                return Ok((fname.clone(), e));
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                        // Normal field - transform as usual
                                        let e = self.transform_expr(fexpr, ctx)?;
                                        let e = self.clone_if_input_ref(e, ctx);
                                        Ok((fname.clone(), e))
                                    })
                                    .collect();

                                if let Some(base) = base_input {
                                    results.push(ExecExpr::StructUpdate {
                                        name: exec_name,
                                        base: Box::new(ExecExpr::Clone(Box::new(ExecExpr::Var(
                                            base,
                                        )))),
                                        fields: translated_fields?,
                                    });
                                } else {
                                    results.push(ExecExpr::Struct {
                                        name: exec_name,
                                        fields: translated_fields?,
                                    });
                                }
                                continue;
                            }
                        }
                    }
                }

                results.push(self.transform_expr(&expr, ctx)?);
            }

            if results.len() == 1 {
                return Ok(Some(results.into_iter().next().unwrap()));
            } else {
                return Ok(Some(ExecExpr::Tuple(results)));
            }
        }

        Ok(None)
    }

    /// Transform a binary operation
    fn transform_binary_op(
        &self,
        lhs: &Expr,
        rhs: &Expr,
        op: &str,
        ctx: &TransformContext,
    ) -> TranspileResult<ExecExpr> {
        let lhs_expr = self.transform_expr(lhs, ctx)?;
        let rhs_expr = self.transform_expr(rhs, ctx)?;
        Ok(ExecExpr::Binary {
            lhs: Box::new(lhs_expr),
            op: op.to_string(),
            rhs: Box::new(rhs_expr),
        })
    }

    /// Format a literal value
    fn format_literal(&self, lit: &crate::ast::Literal) -> String {
        match lit {
            crate::ast::Literal::Bool(b) => b.to_string(),
            crate::ast::Literal::Int(i) => i.to_string(),
            crate::ast::Literal::String(s) => format!("\"{}\"", s),
        }
    }

    /// Format a binding pattern for let expressions
    fn format_binding_pattern(&self, pattern: &crate::ast::Pattern) -> String {
        self.format_pattern(pattern)
    }

    /// Format a pattern for match arms
    fn format_pattern(&self, pattern: &crate::ast::Pattern) -> String {
        match pattern {
            crate::ast::Pattern::Wildcard => "_".to_string(),
            crate::ast::Pattern::Ident(name) => name.clone(),
            crate::ast::Pattern::Tuple(patterns) => {
                let parts: Vec<_> = patterns.iter().map(|p| self.format_pattern(p)).collect();
                format!("({})", parts.join(", "))
            }
            crate::ast::Pattern::Struct { name, fields } => {
                let field_strs: Vec<_> = fields
                    .iter()
                    .map(|(fname, fpat)| format!("{}: {}", fname, self.format_pattern(fpat)))
                    .collect();
                // Use translate_path to handle both struct names and enum variant paths
                // e.g., RslMessage::RslMessage1a -> CMessage::CMessage1a
                format!(
                    "{} {{ {} }}",
                    self.translate_path(name),
                    field_strs.join(", ")
                )
            }
            crate::ast::Pattern::Variant { name, fields } => {
                // Use translate_path to handle full enum variant paths
                // e.g., RslMessage::RslMessageInvalid -> CMessage::CMessageInvalid
                let variant_path = self.translate_path(name);
                if fields.is_empty() {
                    variant_path
                } else {
                    let field_strs: Vec<_> =
                        fields.iter().map(|p| self.format_pattern(p)).collect();
                    format!("{}({})", variant_path, field_strs.join(", "))
                }
            }
            crate::ast::Pattern::Literal(lit) => self.format_literal(lit),
        }
    }

    /// Extract source map and filter predicate from a domain predicate
    /// Returns (source_map_name, filter_predicate) if the pattern is recognized
    ///
    /// Handles patterns like:
    /// - `source.contains_key(k) && filter_pred`
    /// - `filter_pred && source.contains_key(k)`
    /// - `source.dom().contains(k) && filter_pred`
    fn extract_source_and_filter(&self, pred: &Expr, key_var: &str) -> Option<(String, Expr)> {
        use crate::ast::Expr;

        // Check for conjunction (&&)
        if let Expr::Conjunction(parts) = pred {
            // Look for source.contains_key(k) in the parts
            for (i, part) in parts.iter().enumerate() {
                if let Some(source_map) = self.extract_contains_key_source(part, key_var) {
                    // Collect all other parts as the filter predicate
                    let other_parts: Vec<Expr> = parts
                        .iter()
                        .enumerate()
                        .filter(|(j, _)| *j != i)
                        .map(|(_, p)| p.clone())
                        .collect();

                    let filter = if other_parts.len() == 1 {
                        other_parts.into_iter().next().unwrap()
                    } else {
                        Expr::Conjunction(other_parts)
                    };

                    return Some((source_map, filter));
                }
            }
        }

        // Check for binary && (Binary with && op)
        if let Expr::Binary(lhs, crate::ast::BinOp::And, rhs) = pred {
            if let Some(source_map) = self.extract_contains_key_source(lhs, key_var) {
                return Some((source_map, (**rhs).clone()));
            }
            if let Some(source_map) = self.extract_contains_key_source(rhs, key_var) {
                return Some((source_map, (**lhs).clone()));
            }
        }

        // Pattern: just source.contains_key(k) without filter (returns true as filter)
        if let Some(source_map) = self.extract_contains_key_source(pred, key_var) {
            return Some((source_map, Expr::Literal(crate::ast::Literal::Bool(true))));
        }

        None
    }

    /// Try to extract "map update with insert" pattern from domain predicate
    /// Pattern: filter && (source.contains(k) || k == new_key)
    /// Returns: (source_map, filter_pred, new_key_expr) if pattern matches
    fn extract_map_update_with_insert(
        &self,
        pred: &Expr,
        key_var: &str,
    ) -> Option<(String, Expr, Expr)> {
        use crate::ast::{BinOp, Expr};

        // Look for: filter && (source.contains(k) || k == new_key)
        if let Expr::Binary(lhs, BinOp::And, rhs) = pred {
            // Check if RHS is the OR clause: source.contains(k) || k == new_key
            if let Some((source, new_key)) = self.extract_contains_or_equals(rhs, key_var) {
                return Some((source, (**lhs).clone(), new_key));
            }
            // Check LHS as well (filter might be on the right)
            if let Some((source, new_key)) = self.extract_contains_or_equals(lhs, key_var) {
                return Some((source, (**rhs).clone(), new_key));
            }
        }

        // Check for Conjunction form
        if let Expr::Conjunction(parts) = pred {
            // Look for the OR clause among the parts
            for (i, part) in parts.iter().enumerate() {
                if let Some((source, new_key)) = self.extract_contains_or_equals(part, key_var) {
                    // Collect remaining parts as filter
                    let filter_parts: Vec<_> = parts
                        .iter()
                        .enumerate()
                        .filter(|(j, _)| *j != i)
                        .map(|(_, p)| p.clone())
                        .collect();
                    let filter = if filter_parts.len() == 1 {
                        filter_parts.into_iter().next().unwrap()
                    } else {
                        Expr::Conjunction(filter_parts)
                    };
                    return Some((source, filter, new_key));
                }
            }
        }

        None
    }

    /// Extract pattern: source.contains(k) || k == new_key
    /// Returns: (source_map, new_key_expr)
    fn extract_contains_or_equals(&self, expr: &Expr, key_var: &str) -> Option<(String, Expr)> {
        use crate::ast::{BinOp, Expr};

        if let Expr::Binary(lhs, BinOp::Or, rhs) = expr {
            // Check: source.contains(k) || k == new_key
            if let Some(source) = self.extract_contains_key_source(lhs, key_var) {
                if let Some(new_key) = self.extract_key_equals(rhs, key_var) {
                    return Some((source, new_key));
                }
            }
            // Check: k == new_key || source.contains(k)
            if let Some(source) = self.extract_contains_key_source(rhs, key_var) {
                if let Some(new_key) = self.extract_key_equals(lhs, key_var) {
                    return Some((source, new_key));
                }
            }
        }

        None
    }

    /// Extract pattern: k == expr (where k is the key variable)
    /// Returns the expr that k equals
    fn extract_key_equals(&self, expr: &Expr, key_var: &str) -> Option<Expr> {
        use crate::ast::Expr;

        if let Expr::Eq(lhs, rhs) = expr {
            // Check: k == expr
            if let Expr::Ident(name) = lhs.as_ref() {
                if name == key_var {
                    return Some((**rhs).clone());
                }
            }
            // Check: expr == k
            if let Expr::Ident(name) = rhs.as_ref() {
                if name == key_var {
                    return Some((**lhs).clone());
                }
            }
        }

        None
    }

    /// Try to extract map update with value pattern from conjunction of foralls.
    ///
    /// Try to extract output sequence comprehension pattern from a conjunction.
    /// Pattern: conjunction of:
    /// 1. Length constraint: output.len() == input_length_expr
    /// 2. Element forall: forall |i| 0 <= i < output.len() ==> output[i] == element_expr
    ///
    /// Returns: (output_name, input_length_expr, index_var, element_expr)
    fn try_extract_output_seq_comprehension(
        &self,
        exprs: &[Expr],
        ctx: &TransformContext,
    ) -> Option<(String, Expr, String, Expr)> {
        use crate::ast::Expr;

        // Look for length constraint: output.len() == input_length_expr
        // where output is an output parameter
        let mut length_constraints: Vec<(String, Expr)> = Vec::new();
        for expr in exprs {
            if let Expr::Eq(lhs, rhs) = expr {
                // Check output.len() == rhs
                if let Some(output_name) = self.extract_output_len_call(lhs, ctx) {
                    // Check that rhs doesn't reference the output
                    if Self::is_input_only_expression(rhs, ctx) {
                        length_constraints.push((output_name, *rhs.clone()));
                    }
                }
                // Check lhs == output.len()
                else if let Some(output_name) = self.extract_output_len_call(rhs, ctx) {
                    // Check that lhs doesn't reference the output
                    if Self::is_input_only_expression(lhs, ctx) {
                        length_constraints.push((output_name, *lhs.clone()));
                    }
                }
            }
        }

        if length_constraints.is_empty() {
            return None;
        }

        // For each output with a length constraint, look for corresponding forall
        for (output_name, length_expr) in length_constraints {
            // Look for forall |i| 0 <= i < output.len() ==> output[i] == element_expr
            for expr in exprs {
                if let Expr::Forall { vars, body, .. } = expr {
                    if vars.len() != 1 {
                        continue;
                    }
                    let index_var = vars[0].name_string();

                    // Body should be: bounds ==> assignment
                    if let Expr::Implies(bounds_expr, assign_expr) = body.as_ref() {
                        // Check bounds: 0 <= i < output.len()
                        if !self.is_seq_bounds(bounds_expr, &index_var, &output_name) {
                            continue;
                        }

                        // Check assignment: output[i] == element_expr
                        if let Some(element_expr) = self.extract_direct_seq_element_assignment(
                            assign_expr,
                            &index_var,
                            &output_name,
                        ) {
                            return Some((
                                output_name.clone(),
                                length_expr,
                                index_var,
                                element_expr,
                            ));
                        }
                    }
                }
            }
        }

        None
    }

    /// Extract output name if expr is output.len() and output is an output parameter
    fn extract_output_len_call(&self, expr: &Expr, ctx: &TransformContext) -> Option<String> {
        use crate::ast::Expr;
        if let Expr::MethodCall {
            receiver,
            method,
            args,
        } = expr
        {
            if method == "len" && args.is_empty() {
                if let Expr::Ident(name) = receiver.as_ref() {
                    if ctx.is_output(name) {
                        return Some(name.clone());
                    }
                }
                // Also check for output.field.len() pattern
                if let Expr::Field(base, _) = receiver.as_ref() {
                    if let Expr::Ident(name) = base.as_ref() {
                        if ctx.is_output(name) {
                            return Some(name.clone());
                        }
                    }
                }
            }
        }
        None
    }

    /// Check if bounds_expr is: 0 <= idx < output.len()
    fn is_seq_bounds(&self, bounds_expr: &Expr, idx_var: &str, output_name: &str) -> bool {
        use crate::ast::Expr;

        // Common patterns:
        // 1. Conjunction: 0 <= idx &&& idx < output.len()
        // 2. Binary and: (0 <= idx) && (idx < output.len())
        // 3. Chained: 0 <= idx < output.len() (parsed as conjunction of comparisons)

        match bounds_expr {
            Expr::Conjunction(parts) => {
                // Need: lower bound check (0 <= idx) and upper bound check (idx < output.len())
                let has_lower = parts.iter().any(|p| self.is_lower_bound_check(p, idx_var));
                let has_upper = parts
                    .iter()
                    .any(|p| self.is_upper_bound_check(p, idx_var, output_name));
                has_lower && has_upper
            }
            Expr::Binary(lhs, crate::ast::BinOp::And, rhs) => {
                // Check both sub-expressions
                let lhs_is_lower = self.is_lower_bound_check(lhs, idx_var);
                let rhs_is_lower = self.is_lower_bound_check(rhs, idx_var);
                let lhs_is_upper = self.is_upper_bound_check(lhs, idx_var, output_name);
                let rhs_is_upper = self.is_upper_bound_check(rhs, idx_var, output_name);

                (lhs_is_lower && rhs_is_upper) || (rhs_is_lower && lhs_is_upper)
            }
            _ => false,
        }
    }

    /// Check if expr is: 0 <= idx
    fn is_lower_bound_check(&self, expr: &Expr, idx_var: &str) -> bool {
        use crate::ast::Expr;
        match expr {
            Expr::Le(lhs, rhs) => {
                // 0 <= idx
                matches!(lhs.as_ref(), Expr::Literal(crate::ast::Literal::Int(0)))
                    && matches!(rhs.as_ref(), Expr::Ident(v) if v == idx_var)
            }
            Expr::Ge(lhs, rhs) => {
                // idx >= 0
                matches!(lhs.as_ref(), Expr::Ident(v) if v == idx_var)
                    && matches!(rhs.as_ref(), Expr::Literal(crate::ast::Literal::Int(0)))
            }
            _ => false,
        }
    }

    /// Check if expr is: idx < output.len()
    fn is_upper_bound_check(&self, expr: &Expr, idx_var: &str, output_name: &str) -> bool {
        use crate::ast::Expr;
        match expr {
            Expr::Lt(lhs, rhs) => {
                // idx < output.len()
                let lhs_is_idx = matches!(lhs.as_ref(), Expr::Ident(v) if v == idx_var);
                let rhs_is_len = self.is_output_len(rhs, output_name);
                lhs_is_idx && rhs_is_len
            }
            Expr::Gt(lhs, rhs) => {
                // output.len() > idx
                let lhs_is_len = self.is_output_len(lhs, output_name);
                let rhs_is_idx = matches!(rhs.as_ref(), Expr::Ident(v) if v == idx_var);
                lhs_is_len && rhs_is_idx
            }
            _ => false,
        }
    }

    /// Check if expr is output.len()
    fn is_output_len(&self, expr: &Expr, output_name: &str) -> bool {
        use crate::ast::Expr;
        if let Expr::MethodCall {
            receiver,
            method,
            args,
        } = expr
        {
            if method == "len" && args.is_empty() {
                if let Expr::Ident(name) = receiver.as_ref() {
                    return name == output_name;
                }
            }
        }
        false
    }

    /// Extract element expression from: output[i] == element_expr or output[i] =~= element_expr
    fn extract_direct_seq_element_assignment(
        &self,
        expr: &Expr,
        idx_var: &str,
        output_name: &str,
    ) -> Option<Expr> {
        use crate::ast::Expr;

        match expr {
            Expr::Eq(lhs, rhs) => {
                // output[i] == element_expr
                if self.is_output_indexed(lhs, idx_var, output_name) {
                    return Some(*rhs.clone());
                }
                // element_expr == output[i]
                if self.is_output_indexed(rhs, idx_var, output_name) {
                    return Some(*lhs.clone());
                }
            }
            // Also handle extensional equality (=~=) which parses as MethodCall
            Expr::MethodCall {
                receiver,
                method,
                args,
            } if method == "ext_equal" && args.len() == 1 => {
                if self.is_output_indexed(receiver, idx_var, output_name) {
                    return Some(args[0].clone());
                }
            }
            _ => {}
        }
        None
    }

    /// Check if expr is output[idx_var]
    fn is_output_indexed(&self, expr: &Expr, idx_var: &str, output_name: &str) -> bool {
        use crate::ast::Expr;
        if let Expr::Index(base, idx) = expr {
            let base_is_output = matches!(base.as_ref(), Expr::Ident(name) if name == output_name);
            let idx_is_var = matches!(idx.as_ref(), Expr::Ident(v) if v == idx_var);
            base_is_output && idx_is_var
        } else {
            false
        }
    }

    /// Pattern: conjunction of:
    /// 1. Domain: forall |k| output.dom().contains(k) <==> filter && (source.contains(k) || k == new_key)
    /// 2. Value: forall |k| output.dom().contains(k) ==> output[k] == (if k == new_key then new_value else source[k])
    ///
    /// Returns: (source_map, key_var, filter_pred, new_key, new_value, old_value_expr)
    fn try_extract_map_update_with_value(
        &self,
        exprs: &[Expr],
        _ctx: &TransformContext,
    ) -> Option<(String, String, Expr, Expr, Expr, Expr)> {
        use crate::ast::Expr;

        // Collect foralls from the expressions
        let foralls: Vec<_> = exprs
            .iter()
            .filter_map(|e| {
                if let Expr::Forall { vars, body, .. } = e {
                    if vars.len() == 1 {
                        Some((vars[0].name_string(), body.as_ref()))
                    } else {
                        None
                    }
                } else {
                    None
                }
            })
            .collect();

        if foralls.len() < 2 {
            return None;
        }

        // All foralls should use the same variable
        let key_var = &foralls[0].0;
        if !foralls.iter().all(|(v, _)| v == key_var) {
            return None;
        }

        let mut source_map: Option<String> = None;
        let mut filter_pred: Option<Expr> = None;
        let mut new_key: Option<Expr> = None;
        let mut new_value: Option<Expr> = None;
        let mut old_value_expr: Option<Expr> = None;

        for (_, body) in &foralls {
            // Check for domain biconditional: dom().contains(k) <==> filter && (source.contains(k) || k == new_key)
            if let Expr::Iff(lhs, rhs) = body {
                // Check if lhs is output.dom().contains(k)
                if self.is_dom_contains(lhs, key_var).is_some() {
                    // Try to extract the complex predicate from rhs
                    if let Some((src, flt, nk)) = self.extract_map_update_with_insert(rhs, key_var)
                    {
                        source_map = Some(src);
                        filter_pred = Some(flt);
                        new_key = Some(nk);
                    }
                }
            }

            // Check for value conditional: dom().contains(k) ==> output[k] == (if k == new_key then new_value else source[k])
            if let Expr::Implies(lhs, rhs) = body {
                // LHS should be dom().contains(k)
                if self.is_dom_contains(lhs, key_var).is_some() {
                    // RHS should be: output[k] == (if k == new_key then new_value else source[k])
                    if let Some((nv, ov)) = self.extract_conditional_value(rhs, key_var) {
                        new_value = Some(nv);
                        old_value_expr = Some(ov);
                    }
                }
            }
        }

        // Return if we have all components
        if let (Some(src), Some(flt), Some(nk), Some(nv), Some(ov)) =
            (source_map, filter_pred, new_key, new_value, old_value_expr)
        {
            return Some((src, key_var.clone(), flt, nk, nv, ov));
        }

        None
    }

    /// Check if expr is output.dom().contains(key_var)
    fn is_dom_contains(&self, expr: &Expr, key_var: &str) -> Option<String> {
        use crate::ast::Expr;

        if let Expr::MethodCall {
            receiver,
            method,
            args,
        } = expr
        {
            if method == "contains" && args.len() == 1 {
                if let Expr::Ident(arg_name) = &args[0] {
                    if arg_name == key_var {
                        if let Expr::MethodCall {
                            receiver: inner_recv,
                            method: inner_method,
                            args: inner_args,
                        } = receiver.as_ref()
                        {
                            if inner_method == "dom" && inner_args.is_empty() {
                                if let Expr::Ident(output_name) = inner_recv.as_ref() {
                                    return Some(output_name.clone());
                                }
                            }
                        }
                    }
                }
            }
        }
        None
    }

    /// Extract conditional value from: output[k] == (if k == new_key then new_value else source[k])
    /// Returns: (new_value, old_value_expr)
    fn extract_conditional_value(&self, expr: &Expr, key_var: &str) -> Option<(Expr, Expr)> {
        use crate::ast::Expr;

        if let Expr::Eq(lhs, rhs) = expr {
            // Check if lhs is output[k]
            if let Expr::Index(_, idx) = lhs.as_ref() {
                if let Expr::Ident(idx_name) = idx.as_ref() {
                    if idx_name == key_var {
                        // Check if rhs is if-then-else
                        if let Expr::If {
                            cond,
                            then_branch,
                            else_branch,
                        } = rhs.as_ref()
                        {
                            // Condition should involve k == new_key
                            if self.extract_key_equals(cond, key_var).is_some() {
                                // then_branch is the new_value
                                // else_branch is the old_value (source[k])
                                if let Some(else_expr) = else_branch {
                                    return Some(((**then_branch).clone(), (**else_expr).clone()));
                                }
                            }
                        }
                    }
                }
            }
        }
        None
    }

    /// Try to extract a sequence initialization pattern from conjunction expressions.
    ///
    /// Pattern:
    /// 1. Length constraint: output.field.len() == length_expr
    /// 2. Element forall: forall |i| 0 <= i < output.field.len() ==> output.field[i] == element_expr
    ///
    /// Returns: (output_var, field_name, length_expr, element_expr) if pattern matches.
    fn try_extract_seq_init_pattern(
        &self,
        exprs: &[Expr],
        ctx: &TransformContext,
    ) -> Option<(String, String, Expr, Expr)> {
        use crate::ast::Expr;

        // Look for length constraint: output.field.len() == expr
        let mut length_info: Option<(String, String, Expr)> = None;
        for expr in exprs {
            if let Expr::Eq(lhs, rhs) = expr {
                // Check: output.field.len() == expr
                if let Expr::MethodCall {
                    receiver,
                    method,
                    args,
                } = lhs.as_ref()
                {
                    if method == "len" && args.is_empty() {
                        if let Expr::Field(base, field) = receiver.as_ref() {
                            if let Expr::Ident(var_name) = base.as_ref() {
                                if ctx.is_output(var_name) {
                                    length_info =
                                        Some((var_name.clone(), field.clone(), (**rhs).clone()));
                                }
                            }
                        }
                    }
                }
                // Also check: expr == output.field.len()
                if let Expr::MethodCall {
                    receiver,
                    method,
                    args,
                } = rhs.as_ref()
                {
                    if method == "len" && args.is_empty() {
                        if let Expr::Field(base, field) = receiver.as_ref() {
                            if let Expr::Ident(var_name) = base.as_ref() {
                                if ctx.is_output(var_name) {
                                    length_info =
                                        Some((var_name.clone(), field.clone(), (**lhs).clone()));
                                }
                            }
                        }
                    }
                }
            }
        }

        let (out_var, field_name, length_expr) = length_info?;

        // Look for element forall: forall |i| 0 <= i < output.field.len() ==> output.field[i] == element
        for expr in exprs {
            if let Expr::Forall { vars, body, .. } = expr {
                if vars.len() != 1 {
                    continue;
                }
                let idx_var = vars[0].name_string();

                // Body should be: bounds ==> output.field[i] == element
                if let Expr::Implies(lhs, rhs) = body.as_ref() {
                    // Check LHS is bounds: 0 <= i < n
                    // Check RHS is: output.field[i] == element
                    if let Some(element_expr) =
                        self.extract_seq_element_assignment(rhs, &idx_var, &out_var, &field_name)
                    {
                        // Verify LHS is proper bounds (uses the same field.len())
                        if self.is_valid_seq_bounds(lhs, &idx_var, &out_var, &field_name) {
                            return Some((out_var, field_name, length_expr, element_expr));
                        }
                    }
                }
            }
        }

        None
    }

    /// Extract element expression from output.field[i] == element
    fn extract_seq_element_assignment(
        &self,
        expr: &Expr,
        idx_var: &str,
        out_var: &str,
        field_name: &str,
    ) -> Option<Expr> {
        use crate::ast::Expr;

        if let Expr::Eq(lhs, rhs) = expr {
            // Check: output.field[i] == element
            if let Some(element) = self.match_field_index(lhs, idx_var, out_var, field_name) {
                if element {
                    return Some((**rhs).clone());
                }
            }
            // Also check: element == output.field[i]
            if let Some(element) = self.match_field_index(rhs, idx_var, out_var, field_name) {
                if element {
                    return Some((**lhs).clone());
                }
            }
        }
        None
    }

    /// Check if expr matches output.field[idx_var]
    fn match_field_index(
        &self,
        expr: &Expr,
        idx_var: &str,
        out_var: &str,
        field_name: &str,
    ) -> Option<bool> {
        use crate::ast::Expr;

        // Pattern: output.field[idx]
        if let Expr::Index(base, idx) = expr {
            if let Expr::Ident(idx_name) = idx.as_ref() {
                if idx_name == idx_var {
                    if let Expr::Field(base_obj, fname) = base.as_ref() {
                        if fname == field_name {
                            if let Expr::Ident(obj_name) = base_obj.as_ref() {
                                if obj_name == out_var {
                                    return Some(true);
                                }
                            }
                        }
                    }
                }
            }
        }
        None
    }

    /// Check if expr is valid bounds: 0 <= idx < output.field.len()
    fn is_valid_seq_bounds(
        &self,
        _expr: &Expr,
        _idx_var: &str,
        _out_var: &str,
        _field_name: &str,
    ) -> bool {
        // For now, accept any bounds - we can make this more strict later
        // A more complete check would verify:
        // - lower bound: 0 <= idx or idx >= 0
        // - upper bound: idx < output.field.len()
        true
    }

    /// Try to extract conditional field assignments from an if-expression.
    ///
    /// Pattern: if cond { s_.f1 == v1 && s_.f2 == v2 } else { s_.f1 == v3 && s_.f2 == v4 }
    /// Returns: Vec<(output_var, field_name, then_expr, else_expr)>
    fn try_extract_conditional_field_assignments(
        &self,
        _cond: &Expr,
        then_branch: &Expr,
        else_branch: &Expr,
        ctx: &TransformContext,
    ) -> Option<Vec<(String, String, Expr, Expr)>> {
        // Extract field assignments from then branch
        let then_assignments = self.extract_field_assignments_from_branch(then_branch, ctx)?;
        // Extract field assignments from else branch
        let else_assignments = self.extract_field_assignments_from_branch(else_branch, ctx)?;

        // Check that we have matching field names in both branches
        let mut results = Vec::new();
        for (output_var, field_name, then_val) in &then_assignments {
            // Find matching assignment in else branch
            for (else_out, else_field, else_val) in &else_assignments {
                if output_var == else_out && field_name == else_field {
                    results.push((
                        output_var.clone(),
                        field_name.clone(),
                        then_val.clone(),
                        else_val.clone(),
                    ));
                }
            }
        }

        if results.is_empty() {
            None
        } else {
            Some(results)
        }
    }

    /// Extract field assignments from a branch expression (could be conjunction or single assignment)
    fn extract_field_assignments_from_branch(
        &self,
        expr: &Expr,
        ctx: &TransformContext,
    ) -> Option<Vec<(String, String, Expr)>> {
        let mut assignments = Vec::new();

        // Handle conjunction: s_.f1 == v1 && s_.f2 == v2
        if let Expr::Conjunction(parts) = expr {
            for part in parts {
                if let Some((out, field, val)) = self.extract_single_field_assignment(part, ctx) {
                    assignments.push((out, field, val));
                }
            }
        }
        // Handle binary AND: s_.f1 == v1 && s_.f2 == v2
        else if let Expr::Binary(lhs, crate::ast::BinOp::And, rhs) = expr {
            if let Some((out, field, val)) = self.extract_single_field_assignment(lhs, ctx) {
                assignments.push((out, field, val));
            }
            if let Some((out, field, val)) = self.extract_single_field_assignment(rhs, ctx) {
                assignments.push((out, field, val));
            }
        }
        // Handle single assignment: s_.field == val
        else if let Some((out, field, val)) = self.extract_single_field_assignment(expr, ctx) {
            assignments.push((out, field, val));
        }

        if assignments.is_empty() {
            None
        } else {
            Some(assignments)
        }
    }

    /// Try to extract conditional helper calls that compute output fields.
    ///
    /// Pattern: if cond { Helper1(s.field, s_.field, ios) } else { Helper2(s.field, idx, s_.field, ios) }
    /// Returns: Vec<(output_var, field_name, then_exec_expr, else_exec_expr)>
    /// where each exec_expr is a transformed function call (already an ExecExpr)
    fn try_extract_conditional_helper_calls(
        &self,
        _cond: &Expr,
        then_branch: &Expr,
        else_branch: &Expr,
        ctx: &TransformContext,
    ) -> Option<Vec<(String, String, ExecExpr, ExecExpr)>> {
        // Detect helper call in then branch
        let then_info = self.detect_helper_call(then_branch, ctx)?;
        // Detect helper call in else branch
        let else_info = self.detect_helper_call(else_branch, ctx)?;

        // Check that both have matching output fields
        let mut results = Vec::new();
        for (then_out_var, then_field) in &then_info.output_fields {
            for (else_out_var, else_field) in &else_info.output_fields {
                if then_out_var == else_out_var && then_field == else_field {
                    // The helper call already has input_args transformed
                    // Create exec function call expressions
                    let then_call = self.create_exec_helper_call(&then_info);
                    let else_call = self.create_exec_helper_call(&else_info);
                    results.push((
                        then_out_var.clone(),
                        then_field.clone(),
                        then_call,
                        else_call,
                    ));
                }
            }
        }

        if results.is_empty() {
            None
        } else {
            Some(results)
        }
    }

    /// Create an exec function call expression from helper call info
    fn create_exec_helper_call(&self, info: &HelperCallInfo) -> ExecExpr {
        // Translate function name (L -> C prefix)
        let exec_func_name = self.translate_name(&info.func_name);
        ExecExpr::Call {
            func: exec_func_name,
            args: info.input_args.clone(),
        }
    }

    /// Extract a single field assignment: s_.field == value
    /// Returns (output_var, field_name, value_expr)
    fn extract_single_field_assignment(
        &self,
        expr: &Expr,
        ctx: &TransformContext,
    ) -> Option<(String, String, Expr)> {
        if let Expr::Eq(lhs, rhs) = expr {
            // Check: s_.field == value
            if let Expr::Field(base, field) = lhs.as_ref() {
                if let Expr::Ident(var_name) = base.as_ref() {
                    if ctx.is_output(var_name) {
                        return Some((var_name.clone(), field.clone(), (**rhs).clone()));
                    }
                }
            }
            // Also check: value == s_.field
            if let Expr::Field(base, field) = rhs.as_ref() {
                if let Expr::Ident(var_name) = base.as_ref() {
                    if ctx.is_output(var_name) {
                        return Some((var_name.clone(), field.clone(), (**lhs).clone()));
                    }
                }
            }
        }
        None
    }

    /// Try to recognize a conjunction of foralls as a map filter pattern.
    ///
    /// Pattern: conjunction of 3 foralls that together define filtering a map:
    /// 1. Preservation: forall |k| output.contains_key(k) ==> source.contains_key(k) && output[k] == source[k]
    /// 2. Exclusion: forall |k| k < threshold ==> !output.contains_key(k)
    /// 3. Inclusion: forall |k| k >= threshold && source.contains_key(k) ==> output.contains_key(k)
    ///
    /// Returns: (source_map, output_map, key_var, filter_predicate) if pattern matches.
    fn try_extract_map_filter_conjunction(
        &self,
        exprs: &[Expr],
        ctx: &TransformContext,
    ) -> Option<(String, String, String, Expr)> {
        use crate::ast::Expr;

        // We need at least 2-3 forall expressions
        let foralls: Vec<_> = exprs
            .iter()
            .filter_map(|e| {
                if let Expr::Forall { vars, body, .. } = e {
                    if vars.len() == 1 {
                        Some((vars[0].name_string(), body.as_ref()))
                    } else {
                        None
                    }
                } else {
                    None
                }
            })
            .collect();

        if foralls.len() < 2 {
            return None;
        }

        // Check all foralls use the same variable
        let key_var = &foralls[0].0;
        if !foralls.iter().all(|(v, _)| v == key_var) {
            return None;
        }

        let mut source_map: Option<String> = None;
        let mut output_map: Option<String> = None;
        let mut filter_predicate: Option<Expr> = None;

        for (_, body) in &foralls {
            // Pattern 0: Biconditional domain definition
            // output.contains_key(k) <==> filter_pred && source.contains_key(k)
            if let Expr::Iff(lhs, rhs) = body {
                // Check which side has output.contains_key(k)
                if let Some(map_name) = self.extract_contains_key_source(lhs, key_var) {
                    if ctx.is_output_field_path(&map_name) {
                        output_map = Some(map_name.clone());
                        // The RHS is: filter_pred && source.contains_key(k)
                        if let Some((src, filter)) = self.extract_source_and_filter(rhs, key_var) {
                            source_map = Some(src);
                            // Only set filter if it's not just "true"
                            if !matches!(filter, Expr::Literal(Literal::Bool(true))) {
                                filter_predicate = Some(filter);
                            }
                        }
                        continue;
                    }
                }
                if let Some(map_name) = self.extract_contains_key_source(rhs, key_var) {
                    if ctx.is_output_field_path(&map_name) {
                        output_map = Some(map_name.clone());
                        // The LHS is: filter_pred && source.contains_key(k)
                        if let Some((src, filter)) = self.extract_source_and_filter(lhs, key_var) {
                            source_map = Some(src);
                            if !matches!(filter, Expr::Literal(Literal::Bool(true))) {
                                filter_predicate = Some(filter);
                            }
                        }
                        continue;
                    }
                }
            }

            // Pattern 1: Preservation - output.contains_key(k) ==> source.contains_key(k) && output[k] == source[k]
            if let Expr::Implies(premise, conclusion) = body {
                // Check for output.contains_key(k) in premise
                if let Some(map_name) = self.extract_contains_key_source(premise, key_var) {
                    if ctx.is_output_field_path(&map_name) {
                        output_map = Some(map_name.clone());
                        // Try to find source in conclusion
                        if let Expr::Binary(lhs, crate::ast::BinOp::And, rhs) = conclusion.as_ref()
                        {
                            if let Some(src) = self.extract_contains_key_source(lhs, key_var) {
                                if !ctx.is_output_field_path(&src) {
                                    source_map = Some(src);
                                }
                            }
                            if let Some(src) = self.extract_contains_key_source(rhs, key_var) {
                                if !ctx.is_output_field_path(&src) {
                                    source_map = Some(src);
                                }
                            }
                        }
                        if let Expr::Conjunction(parts) = conclusion.as_ref() {
                            for part in parts {
                                if let Some(src) = self.extract_contains_key_source(part, key_var) {
                                    if !ctx.is_output_field_path(&src) {
                                        source_map = Some(src);
                                    }
                                }
                            }
                        }
                        continue;
                    }
                }

                // Pattern 2: Exclusion - k < threshold ==> !output.contains_key(k)
                // Check if conclusion is negation of contains_key on output
                if let Expr::Not(inner) = conclusion.as_ref() {
                    if let Some(map_name) = self.extract_contains_key_source(inner, key_var) {
                        if ctx.is_output_field_path(&map_name) {
                            output_map = Some(map_name.clone());
                            // The premise is the exclusion condition, we want the opposite for filter
                            // If k < threshold excludes, then k >= threshold includes
                            match premise.as_ref() {
                                // k < threshold, so filter is k >= threshold
                                Expr::Lt(lhs, rhs) if Self::is_var_expr(lhs, key_var) => {
                                    filter_predicate = Some(Expr::Ge(lhs.clone(), rhs.clone()));
                                }
                                // k <= threshold, so filter is k > threshold
                                Expr::Le(lhs, rhs) if Self::is_var_expr(lhs, key_var) => {
                                    filter_predicate = Some(Expr::Gt(lhs.clone(), rhs.clone()));
                                }
                                _ => {}
                            }
                            continue;
                        }
                    }
                }

                // Pattern 3: Inclusion - k >= threshold && source.contains_key(k) ==> output.contains_key(k)
                if let Some(map_name) = self.extract_contains_key_source(conclusion, key_var) {
                    if ctx.is_output_field_path(&map_name) {
                        output_map = Some(map_name.clone());
                        // The premise contains the filter predicate and source membership
                        if let Expr::Binary(lhs, crate::ast::BinOp::And, rhs) = premise.as_ref() {
                            if let Some(src) = self.extract_contains_key_source(lhs, key_var) {
                                if !ctx.is_output_field_path(&src) {
                                    source_map = Some(src);
                                    // The other part is the filter
                                    filter_predicate = Some((**rhs).clone());
                                }
                            }
                            if let Some(src) = self.extract_contains_key_source(rhs, key_var) {
                                if !ctx.is_output_field_path(&src) {
                                    source_map = Some(src);
                                    // The other part is the filter
                                    filter_predicate = Some((**lhs).clone());
                                }
                            }
                        }
                    }
                }
            }
        }

        // If we found all components, return them
        if let (Some(src), Some(out), Some(filter)) = (source_map, output_map, filter_predicate) {
            Some((src, out, key_var.clone(), filter))
        } else {
            None
        }
    }

    /// Find a struct literal in the expressions that has a self-referential field
    /// Pattern: s_ == Struct{..., field: s_.field}
    /// Returns (output_var_name, struct_expr) if found
    fn find_self_referential_struct_literal(
        &self,
        exprs: &[Expr],
        output_map: &str,
        ctx: &TransformContext,
    ) -> Option<(String, Expr)> {
        for expr in exprs {
            // Look for: output_var == Struct{...}
            if let Expr::Eq(lhs, rhs) = expr {
                if let Expr::Ident(var_name) = lhs.as_ref() {
                    if ctx.is_output(var_name) {
                        if let Expr::Struct { fields, .. } = rhs.as_ref() {
                            // Check if any field is self-referential (references the output)
                            for (field_name, field_expr) in fields {
                                if self.is_self_referential_field(field_expr, var_name, field_name)
                                {
                                    // Check if this field corresponds to the output_map
                                    // output_map might be "s_.unexecuted_learner_state"
                                    // or just the field name
                                    let expected_ref = format!("{}.{}", var_name, field_name);
                                    if output_map == expected_ref
                                        || output_map.ends_with(field_name)
                                    {
                                        return Some((var_name.clone(), rhs.as_ref().clone()));
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        None
    }

    /// Check if a field expression is self-referential
    /// Pattern: output.field where output is the output variable
    fn is_self_referential_field(
        &self,
        field_expr: &Expr,
        output_var: &str,
        _expected_field: &str,
    ) -> bool {
        // Check for: output_var.field_name
        if let Expr::Field(base, _field_name) = field_expr {
            if let Expr::Ident(var_name) = base.as_ref() {
                return var_name == output_var;
            }
        }
        false
    }

    /// Extract the field name from an output map reference
    /// "s_.unexecuted_learner_state" -> "unexecuted_learner_state"
    fn extract_field_name_from_output_map(&self, output_map: &str) -> String {
        if let Some(dot_pos) = output_map.rfind('.') {
            output_map[dot_pos + 1..].to_string()
        } else {
            output_map.to_string()
        }
    }

    /// Transform a struct with a field substitution for self-referential field
    fn transform_struct_with_field_substitution(
        &self,
        struct_expr: &Expr,
        _output_var: &str,
        self_ref_field: &str,
        replacement_var: &str,
        ctx: &TransformContext,
    ) -> TranspileResult<ExecExpr> {
        if let Expr::Struct { name, fields } = struct_expr {
            let exec_name = self.translate_name(name.last().unwrap_or("Unknown"));
            let translated_fields: TranspileResult<Vec<_>> = fields
                .iter()
                .map(|(fname, fexpr)| {
                    let expr = if fname == self_ref_field {
                        // Substitute with the intermediate variable
                        ExecExpr::Var(replacement_var.to_string())
                    } else {
                        let e = self.transform_expr(fexpr, ctx)?;
                        // Clone input parameters when assigning to struct fields
                        self.clone_if_input_ref(e, ctx)
                    };
                    Ok((fname.clone(), expr))
                })
                .collect();
            Ok(ExecExpr::Struct {
                name: exec_name,
                fields: translated_fields?,
            })
        } else {
            // Fallback to normal transformation
            self.transform_expr(struct_expr, ctx)
        }
    }

    /// Check if an expression is a variable with the given name
    fn is_var_expr(expr: &Expr, var_name: &str) -> bool {
        matches!(expr, Expr::Ident(name) if name == var_name)
    }

    /// Extract containers from a disjunction of contains calls
    /// Handles: (container1.contains(x) || container2.contains(x))
    /// Returns a list of container expressions
    fn extract_contains_disjunction(&self, expr: &Expr, element_var: &str) -> Option<Vec<Expr>> {
        use crate::ast::Expr;

        // Check for disjunction
        if let Expr::Disjunction(parts) = expr {
            let mut containers = Vec::new();
            for part in parts {
                if let Some(container) = self.extract_contains_receiver(part, element_var) {
                    containers.push(container);
                } else {
                    // Not a pure disjunction of contains calls
                    return None;
                }
            }
            if !containers.is_empty() {
                return Some(containers);
            }
        }

        // Check for binary ||
        if let Expr::Binary(lhs, crate::ast::BinOp::Or, rhs) = expr {
            let mut containers = Vec::new();
            // Try to extract from lhs
            if let Some(container) = self.extract_contains_receiver(lhs, element_var) {
                containers.push(container);
            } else if let Some(mut nested) = self.extract_contains_disjunction(lhs, element_var) {
                containers.append(&mut nested);
            } else {
                return None;
            }
            // Try to extract from rhs
            if let Some(container) = self.extract_contains_receiver(rhs, element_var) {
                containers.push(container);
            } else if let Some(mut nested) = self.extract_contains_disjunction(rhs, element_var) {
                containers.append(&mut nested);
            } else {
                return None;
            }
            return Some(containers);
        }

        // Single contains
        if let Some(container) = self.extract_contains_receiver(expr, element_var) {
            return Some(vec![container]);
        }

        None
    }

    /// Extract container(s) and predicate from exists body
    /// Handles: container.contains(x) && pred(x)
    /// Also handles: (container1.contains(x) || container2.contains(x)) && pred(x)
    /// Returns (containers, predicate_without_contains)
    fn extract_exists_containers_and_pred(
        &self,
        body: &Expr,
        var_name: &str,
    ) -> Option<(Vec<Expr>, Expr)> {
        use crate::ast::Expr;

        // Check for conjunction: (container_expr) && pred(x)
        if let Expr::Conjunction(parts) = body {
            for (i, part) in parts.iter().enumerate() {
                // Try to extract containers from this part (single or disjunction)
                if let Some(containers) = self.extract_contains_disjunction(part, var_name) {
                    // Found container(s), rest is predicate
                    let other_parts: Vec<Expr> = parts
                        .iter()
                        .enumerate()
                        .filter(|(j, _)| *j != i)
                        .map(|(_, p)| p.clone())
                        .collect();

                    let predicate = if other_parts.len() == 1 {
                        other_parts.into_iter().next().unwrap()
                    } else if other_parts.is_empty() {
                        Expr::Literal(crate::ast::Literal::Bool(true))
                    } else {
                        Expr::Conjunction(other_parts)
                    };

                    return Some((containers, predicate));
                }
            }
        }

        // Check for binary &&: (container_expr) && pred(x)
        if let Expr::Binary(lhs, crate::ast::BinOp::And, rhs) = body {
            if let Some(containers) = self.extract_contains_disjunction(lhs, var_name) {
                return Some((containers, (**rhs).clone()));
            }
            if let Some(containers) = self.extract_contains_disjunction(rhs, var_name) {
                return Some((containers, (**lhs).clone()));
            }
        }

        // Check for just container.contains(x) or disjunction without additional predicate
        if let Some(containers) = self.extract_contains_disjunction(body, var_name) {
            return Some((containers, Expr::Literal(crate::ast::Literal::Bool(true))));
        }

        None
    }

    /// Extract container and predicate from exists body (single container case)
    /// Handles: container.contains(x) && pred(x)
    /// Returns (container, predicate_without_contains)
    #[cfg(test)]
    fn extract_exists_container_and_pred(
        &self,
        body: &Expr,
        var_name: &str,
    ) -> Option<(Expr, Expr)> {
        // Use the new function and extract single container
        if let Some((containers, predicate)) =
            self.extract_exists_containers_and_pred(body, var_name)
        {
            if containers.len() == 1 {
                return Some((containers.into_iter().next().unwrap(), predicate));
            }
        }
        None
    }

    /// Extract the receiver expression from a contains call
    /// Returns the full expression (e.g., s.acceptor.last_checkpointed_operation)
    fn extract_contains_receiver(&self, expr: &Expr, element_var: &str) -> Option<Expr> {
        use crate::ast::Expr;

        if let Expr::MethodCall {
            receiver,
            method,
            args,
        } = expr
        {
            if method == "contains" && args.len() == 1 {
                if let Expr::Ident(arg_name) = &args[0] {
                    if arg_name == element_var {
                        return Some((**receiver).clone());
                    }
                }
            }
        }
        None
    }

    /// Extract source set and filter predicate from a domain predicate (for sets)
    /// Handles: source.contains(x) && filter_pred
    fn extract_source_set_and_filter(
        &self,
        pred: &Expr,
        element_var: &str,
    ) -> Option<(String, Expr)> {
        use crate::ast::Expr;

        // Check for conjunction
        if let Expr::Conjunction(parts) = pred {
            for (i, part) in parts.iter().enumerate() {
                if let Some(source) = self.extract_set_contains_source(part, element_var) {
                    let other_parts: Vec<Expr> = parts
                        .iter()
                        .enumerate()
                        .filter(|(j, _)| *j != i)
                        .map(|(_, p)| p.clone())
                        .collect();

                    let filter = if other_parts.len() == 1 {
                        other_parts.into_iter().next().unwrap()
                    } else {
                        Expr::Conjunction(other_parts)
                    };

                    return Some((source, filter));
                }
            }
        }

        // Check for binary &&
        if let Expr::Binary(lhs, crate::ast::BinOp::And, rhs) = pred {
            if let Some(source) = self.extract_set_contains_source(lhs, element_var) {
                return Some((source, (**rhs).clone()));
            }
            if let Some(source) = self.extract_set_contains_source(rhs, element_var) {
                return Some((source, (**lhs).clone()));
            }
        }

        // Just contains without filter
        if let Some(source) = self.extract_set_contains_source(pred, element_var) {
            return Some((source, Expr::Literal(crate::ast::Literal::Bool(true))));
        }

        None
    }

    /// Extract source set name from a contains expression
    fn extract_set_contains_source(&self, expr: &Expr, element_var: &str) -> Option<String> {
        use crate::ast::Expr;

        if let Expr::MethodCall {
            receiver,
            method,
            args,
        } = expr
        {
            if method == "contains" && args.len() == 1 {
                if let Expr::Ident(arg_name) = &args[0] {
                    if arg_name == element_var {
                        // Use expr_to_name to handle arbitrary nesting depth
                        return Some(Self::expr_to_name_static(receiver));
                    }
                }
            }
        }
        None
    }

    /// Convert an expression to a string name (for collection names)
    /// Handles identifiers and nested field access chains
    fn expr_to_name_static(expr: &Expr) -> String {
        use crate::ast::Expr;

        match expr {
            Expr::Ident(name) => name.clone(),
            Expr::Field(base, field) => {
                format!("{}.{}", Self::expr_to_name_static(base), field)
            }
            // For other expression types, use a placeholder
            _ => "_expr_".to_string(),
        }
    }

    /// Extract source map from a conditional value expression
    /// Handles: if cond { v1 } else { source[k] }
    fn extract_source_from_conditional_value(&self, expr: &Expr, key_var: &str) -> Option<String> {
        use crate::ast::Expr;

        match expr {
            // if cond { v1 } else { source[k] }
            Expr::If {
                else_branch: Some(else_branch),
                ..
            } => {
                // Check if else branch is source[k]
                if let Expr::Index(source, idx) = else_branch.as_ref() {
                    if let Expr::Ident(idx_name) = idx.as_ref() {
                        if idx_name == key_var {
                            if let Expr::Ident(source_name) = source.as_ref() {
                                return Some(source_name.clone());
                            }
                            if let Expr::Field(base, field) = source.as_ref() {
                                if let Expr::Ident(base_name) = base.as_ref() {
                                    return Some(format!("{}.{}", base_name, field));
                                }
                            }
                        }
                    }
                }
                // Recursively check then branch
                if let Expr::If { then_branch, .. } = expr {
                    if let Some(source) =
                        self.extract_source_from_conditional_value(then_branch, key_var)
                    {
                        return Some(source);
                    }
                }
            }
            // source[k] directly
            Expr::Index(source, idx) => {
                if let Expr::Ident(idx_name) = idx.as_ref() {
                    if idx_name == key_var {
                        if let Expr::Ident(source_name) = source.as_ref() {
                            return Some(source_name.clone());
                        }
                    }
                }
            }
            _ => {}
        }
        None
    }

    /// Extract the source map name from a contains_key expression
    /// Handles: source.contains_key(k), source.dom().contains(k)
    fn extract_contains_key_source(&self, expr: &Expr, key_var: &str) -> Option<String> {
        use crate::ast::Expr;

        match expr {
            // source.contains_key(k)
            Expr::MethodCall {
                receiver,
                method,
                args,
            } if method == "contains_key" && args.len() == 1 => {
                if let Expr::Ident(arg_name) = &args[0] {
                    if arg_name == key_var {
                        if let Expr::Ident(source) = receiver.as_ref() {
                            return Some(source.clone());
                        }
                        // Also handle field access like s.votes.contains_key(k)
                        if let Expr::Field(base, field) = receiver.as_ref() {
                            if let Expr::Ident(base_name) = base.as_ref() {
                                return Some(format!("{}.{}", base_name, field));
                            }
                        }
                    }
                }
            }
            // source.dom().contains(k)
            Expr::MethodCall {
                receiver,
                method,
                args,
            } if method == "contains" && args.len() == 1 => {
                if let Expr::Ident(arg_name) = &args[0] {
                    if arg_name == key_var {
                        // Check if receiver is source.dom()
                        if let Expr::MethodCall {
                            receiver: inner_recv,
                            method: inner_method,
                            args: inner_args,
                        } = receiver.as_ref()
                        {
                            if inner_method == "dom" && inner_args.is_empty() {
                                if let Expr::Ident(source) = inner_recv.as_ref() {
                                    return Some(source.clone());
                                }
                            }
                        }
                    }
                }
            }
            _ => {}
        }
        None
    }

    /// Translate a matched quantifier template to executable code
    fn translate_quantifier_template(
        &self,
        template: &crate::checker::QuantifierTemplate,
        ctx: &TransformContext,
    ) -> TranspileResult<ExecExpr> {
        use crate::checker::QuantifierTemplate;

        match template {
            QuantifierTemplate::SeqComprehension {
                length_expr,
                element_expr,
                index_var,
            } => {
                // Generate: (0..length).map(|i| element).collect::<Vec<_>>()
                let length = self.transform_expr(length_expr, ctx)?;
                let element = self.transform_expr(element_expr, ctx)?;

                Ok(ExecExpr::MethodCall {
                    receiver: Box::new(ExecExpr::MethodCall {
                        receiver: Box::new(ExecExpr::Range {
                            start: Box::new(ExecExpr::Literal("0".to_string())),
                            end: Box::new(length),
                        }),
                        method: "map".to_string(),
                        args: vec![ExecExpr::Closure {
                            params: vec![index_var.clone()],
                            body: Box::new(element),
                        }],
                    }),
                    method: "collect".to_string(),
                    args: vec![],
                })
            }

            QuantifierTemplate::MapDomainBiconditional {
                output_map: _,
                key_var,
                domain_predicate,
            } => {
                // First try "map update with insert" pattern:
                // filter && (source.contains(k) || k == new_key)
                // This generates: filter source, then insert new_key
                if let Some((source_map, filter_pred, new_key_expr)) =
                    self.extract_map_update_with_insert(domain_predicate, key_var)
                {
                    let filter_expr = self.transform_expr(&filter_pred, ctx)?;
                    let new_key = self.transform_expr(&new_key_expr, ctx)?;

                    // Generate a block that:
                    // 1. Creates filtered map from source
                    // 2. Inserts new_key (value will be set by MapConditionalValue)
                    // For now, just generate the filter part with a marker for insert
                    // The value setting will be handled by MapConditionalValue template
                    return Ok(ExecExpr::MapUpdateWithInsert {
                        source: Box::new(ExecExpr::Var(source_map)),
                        key_var: key_var.clone(),
                        filter: Box::new(filter_expr),
                        new_key: Box::new(new_key),
                    });
                }

                // Try simple filter pattern: source.contains_key(k) && filter_pred
                if let Some((source_map, filter_pred)) =
                    self.extract_source_and_filter(domain_predicate, key_var)
                {
                    // Generate: source.iter().filter(|(k, _)| filter_pred).cloned().collect()
                    let filter_expr = self.transform_expr(&filter_pred, ctx)?;

                    Ok(ExecExpr::MethodCall {
                        receiver: Box::new(ExecExpr::MethodCall {
                            receiver: Box::new(ExecExpr::MethodCall {
                                receiver: Box::new(ExecExpr::MethodCall {
                                    receiver: Box::new(ExecExpr::Var(source_map)),
                                    method: "iter".to_string(),
                                    args: vec![],
                                }),
                                method: "filter".to_string(),
                                args: vec![ExecExpr::Closure {
                                    params: vec![format!("({}, _)", key_var)],
                                    body: Box::new(filter_expr),
                                }],
                            }),
                            method: "cloned".to_string(),
                            args: vec![],
                        }),
                        method: "collect".to_string(),
                        args: vec![],
                    })
                } else {
                    // Fallback: generate a comment if we can't extract the pattern
                    let pred = self.transform_expr(domain_predicate, ctx)?;
                    Ok(ExecExpr::Comment(format!(
                        "TODO: Map domain constraint - {} in output <==> {:?}",
                        key_var, pred
                    )))
                }
            }

            QuantifierTemplate::MapPreservation {
                source_map,
                output_map: _,
                key_var: _,
            } => {
                // Generate: source.clone() - this preserves all values
                // Filtering is done by combining with domain constraint
                Ok(ExecExpr::Clone(Box::new(ExecExpr::Var(source_map.clone()))))
            }

            QuantifierTemplate::MapConditionalValue {
                output_map: _,
                key_var,
                value_expr,
            } => {
                // This pattern indicates how values should be computed
                // For patterns like: output[k] == if cond { v1 } else { source[k] }
                // We need a source map to iterate over
                //
                // Try to extract source map from the value expression
                if let Some(source_map) =
                    self.extract_source_from_conditional_value(value_expr, key_var)
                {
                    // Generate: source.iter().map(|(k, v)| (k.clone(), value_expr)).collect()
                    let value = self.transform_expr(value_expr, ctx)?;

                    Ok(ExecExpr::MethodCall {
                        receiver: Box::new(ExecExpr::MethodCall {
                            receiver: Box::new(ExecExpr::MethodCall {
                                receiver: Box::new(ExecExpr::Var(source_map)),
                                method: "iter".to_string(),
                                args: vec![],
                            }),
                            method: "map".to_string(),
                            args: vec![ExecExpr::Closure {
                                params: vec![format!("({}, v)", key_var)],
                                body: Box::new(ExecExpr::Tuple(vec![
                                    ExecExpr::MethodCall {
                                        receiver: Box::new(ExecExpr::Var(key_var.clone())),
                                        method: "clone".to_string(),
                                        args: vec![],
                                    },
                                    value,
                                ])),
                            }],
                        }),
                        method: "collect".to_string(),
                        args: vec![],
                    })
                } else {
                    // Fallback: generate a comment if we can't extract the source
                    let value = self.transform_expr(value_expr, ctx)?;
                    Ok(ExecExpr::Comment(format!(
                        "TODO: Value mapping - output[{}] = {:?}",
                        key_var, value
                    )))
                }
            }

            QuantifierTemplate::MapFilter {
                source_map,
                output_map: _,
                key_var,
                filter_predicate,
            } => {
                let pred = self.transform_expr(filter_predicate, ctx)?;

                if self.config.generate_loops_for_verification {
                    // Generate explicit for loop for Verus verification
                    Ok(self.generate_map_filter_loop(source_map, key_var, pred))
                } else {
                    // Generate: source.iter().filter(|(k, _)| predicate).collect()
                    Ok(ExecExpr::MethodCall {
                        receiver: Box::new(ExecExpr::MethodCall {
                            receiver: Box::new(ExecExpr::MethodCall {
                                receiver: Box::new(ExecExpr::Var(source_map.clone())),
                                method: "iter".to_string(),
                                args: vec![],
                            }),
                            method: "filter".to_string(),
                            args: vec![ExecExpr::Closure {
                                params: vec![format!("({}, _)", key_var)],
                                body: Box::new(pred),
                            }],
                        }),
                        method: "collect".to_string(),
                        args: vec![],
                    })
                }
            }

            QuantifierTemplate::SetComprehension {
                domain_predicate,
                element_var,
            } => {
                // Try to extract source set from domain predicate
                // Pattern: source.contains(x) && filter_pred
                if let Some((source_set, filter_pred)) =
                    self.extract_source_set_and_filter(domain_predicate, element_var)
                {
                    let filter_expr = self.transform_expr(&filter_pred, ctx)?;

                    // Generate: source.iter().filter(|x| filter_pred).cloned().collect()
                    Ok(ExecExpr::MethodCall {
                        receiver: Box::new(ExecExpr::MethodCall {
                            receiver: Box::new(ExecExpr::MethodCall {
                                receiver: Box::new(ExecExpr::MethodCall {
                                    receiver: Box::new(ExecExpr::Var(source_set)),
                                    method: "iter".to_string(),
                                    args: vec![],
                                }),
                                method: "filter".to_string(),
                                args: vec![ExecExpr::Closure {
                                    params: vec![element_var.clone()],
                                    body: Box::new(filter_expr),
                                }],
                            }),
                            method: "cloned".to_string(),
                            args: vec![],
                        }),
                        method: "collect".to_string(),
                        args: vec![],
                    })
                } else {
                    // Fallback
                    let pred = self.transform_expr(domain_predicate, ctx)?;
                    Ok(ExecExpr::Comment(format!(
                        "TODO: Set comprehension - {} in output <==> {:?}",
                        element_var, pred
                    )))
                }
            }

            QuantifierTemplate::MapComprehension {
                domain_predicate,
                value_expr,
                key_var,
            } => {
                // Try to extract source from domain predicate
                if let Some((source_map, filter_pred)) =
                    self.extract_source_and_filter(domain_predicate, key_var)
                {
                    let filter_expr = self.transform_expr(&filter_pred, ctx)?;
                    let value = self.transform_expr(value_expr, ctx)?;

                    // Generate: source.iter().filter(|(k, _)| filter_pred).map(|(k, v)| (k.clone(), value)).collect()
                    Ok(ExecExpr::MethodCall {
                        receiver: Box::new(ExecExpr::MethodCall {
                            receiver: Box::new(ExecExpr::MethodCall {
                                receiver: Box::new(ExecExpr::MethodCall {
                                    receiver: Box::new(ExecExpr::Var(source_map)),
                                    method: "iter".to_string(),
                                    args: vec![],
                                }),
                                method: "filter".to_string(),
                                args: vec![ExecExpr::Closure {
                                    params: vec![format!("({}, _)", key_var)],
                                    body: Box::new(filter_expr),
                                }],
                            }),
                            method: "map".to_string(),
                            args: vec![ExecExpr::Closure {
                                params: vec![format!("({}, v)", key_var)],
                                body: Box::new(ExecExpr::Tuple(vec![
                                    ExecExpr::MethodCall {
                                        receiver: Box::new(ExecExpr::Var(key_var.clone())),
                                        method: "clone".to_string(),
                                        args: vec![],
                                    },
                                    value,
                                ])),
                            }],
                        }),
                        method: "collect".to_string(),
                        args: vec![],
                    })
                } else {
                    // Fallback
                    let pred = self.transform_expr(domain_predicate, ctx)?;
                    let value = self.transform_expr(value_expr, ctx)?;
                    Ok(ExecExpr::Comment(format!(
                        "TODO: Map comprehension - {} where {:?} -> {:?}",
                        key_var, pred, value
                    )))
                }
            }

            QuantifierTemplate::MapExclusion {
                output_map: _,
                key_var,
                exclusion_predicate,
            } => {
                // This is a constraint pattern - keys matching predicate are NOT in output
                // In the context of map construction, this combines with other constraints
                let pred = self.transform_expr(exclusion_predicate, ctx)?;
                Ok(ExecExpr::Comment(format!(
                    "Exclusion constraint: when {:?}, {} is NOT in output",
                    pred, key_var
                )))
            }

            QuantifierTemplate::MapInclusion {
                output_map: _,
                source_map,
                key_var,
                inclusion_predicate,
            } => {
                // This is a constraint pattern - keys matching predicate (and in source) ARE in output
                let pred = self.transform_expr(inclusion_predicate, ctx)?;
                Ok(ExecExpr::Comment(format!(
                    "Inclusion constraint: when {:?}{}, {} is in output",
                    pred,
                    source_map
                        .as_ref()
                        .map(|s| format!(" and in {}", s))
                        .unwrap_or_default(),
                    key_var
                )))
            }

            QuantifierTemplate::CollectionCheck {
                container,
                element_var,
                predicate,
            } => {
                // Pattern: forall |x| container.contains(x) ==> pred(x)
                let container_expr = self.transform_expr(container, ctx)?;
                let pred_expr = self.transform_expr(predicate, ctx)?;

                if self.config.generate_loops_for_verification {
                    // Generate explicit for loop for Verus verification
                    Ok(self.generate_all_loop(container_expr, element_var, pred_expr))
                } else {
                    // Generate: container.iter().all(|x| predicate)
                    Ok(ExecExpr::MethodCall {
                        receiver: Box::new(ExecExpr::MethodCall {
                            receiver: Box::new(container_expr),
                            method: "iter".to_string(),
                            args: vec![],
                        }),
                        method: "all".to_string(),
                        args: vec![ExecExpr::Closure {
                            params: vec![element_var.clone()],
                            body: Box::new(pred_expr),
                        }],
                    })
                }
            }
        }
    }
}

impl Default for Translator {
    fn default() -> Self {
        Self::new(TranslatorConfig::default())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Literal, Path};

    #[test]
    fn test_translate_name() {
        let translator = Translator::default();
        // L prefix followed by uppercase -> strip L, add C
        assert_eq!(translator.translate_name("LAcceptor"), "CAcceptor");
        assert_eq!(translator.translate_name("LLearner"), "CLearner");
        // No L prefix -> add C
        assert_eq!(translator.translate_name("Ballot"), "CBallot");
        // L is part of word (not prefix) -> add C, keep full name
        // LearnerTuple starts with L but 'e' is lowercase, so "Learner" is the word
        assert_eq!(translator.translate_name("LearnerTuple"), "CLearnerTuple");
        assert_eq!(translator.translate_name("Listen"), "CListen");
    }

    #[test]
    fn test_translate_name_with_remapping() {
        use std::collections::HashMap;
        let mut remapping = HashMap::new();
        remapping.insert("RslMessage".to_string(), "CMessage".to_string());
        remapping.insert("RslMessage1a".to_string(), "CMessage1a".to_string());
        remapping.insert("RslMessage1b".to_string(), "CMessage1b".to_string());

        let config = TranslatorConfig {
            type_remapping: remapping,
            ..TranslatorConfig::default()
        };
        let translator = Translator::new(config);

        // Test remapping takes priority
        assert_eq!(translator.translate_name("RslMessage"), "CMessage");
        assert_eq!(translator.translate_name("RslMessage1a"), "CMessage1a");
        assert_eq!(translator.translate_name("RslMessage1b"), "CMessage1b");
    }

    #[test]
    fn test_translate_path() {
        use std::collections::HashMap;
        let mut remapping = HashMap::new();
        remapping.insert("RslMessage".to_string(), "CMessage".to_string());
        remapping.insert("RslMessage1b".to_string(), "CMessage1b".to_string());

        let config = TranslatorConfig {
            type_remapping: remapping,
            ..TranslatorConfig::default()
        };
        let translator = Translator::new(config);

        // Single segment (simple name)
        let path_single = Path::single("RslMessage".to_string());
        assert_eq!(translator.translate_path(&path_single), "CMessage");

        // Multi-segment (enum variant)
        let path_variant = Path::new(vec!["RslMessage".to_string(), "RslMessage1b".to_string()]);
        assert_eq!(translator.translate_path(&path_variant), "CMessage::CMessage1b");

        // Single segment containing :: (parser quirk - stores "Type::Variant" as one string)
        let path_combined = Path::single("RslMessage::RslMessage1b".to_string());
        assert_eq!(translator.translate_path(&path_combined), "CMessage::CMessage1b");
    }

    #[test]
    fn test_translate_type() {
        let translator = Translator::default();

        let named = Type::Named(Path::single("LAcceptor".to_string()));
        let result = translator.translate_type(&named);
        assert!(matches!(result, ExecType::Named(n) if n == "CAcceptor"));

        let seq = Type::Seq(Box::new(Type::Named(Path::single("LPacket".to_string()))));
        let result = translator.translate_type(&seq);
        assert!(matches!(result, ExecType::Vec(_)));
    }

    #[test]
    fn test_exec_type_to_string() {
        let ty = ExecType::Vec(Box::new(ExecType::Named("CPacket".to_string())));
        assert_eq!(ty.to_rust_string(), "Vec<CPacket>");

        let tuple = ExecType::Tuple(vec![
            ExecType::Named("CAcceptor".to_string()),
            ExecType::Vec(Box::new(ExecType::Named("CPacket".to_string()))),
        ]);
        assert_eq!(tuple.to_rust_string(), "(CAcceptor, Vec<CPacket>)");
    }

    fn make_ctx() -> TransformContext<'static> {
        static CONFIG: std::sync::OnceLock<TranslatorConfig> = std::sync::OnceLock::new();
        let mut output_types = HashMap::new();
        output_types.insert(
            "s_".to_string(),
            Type::Named(Path::single("LState".to_string())),
        );
        TransformContext {
            config: CONFIG.get_or_init(TranslatorConfig::default),
            output_params: vec!["s_".to_string()],
            input_params: vec!["s".to_string(), "inp".to_string()],
            output_types,
            field_substitutions: HashMap::new(),
        }
    }

    #[test]
    fn test_transform_literal() {
        let translator = Translator::default();
        let ctx = make_ctx();

        let expr = Expr::Literal(Literal::Int(42));
        let result = translator.transform_expr(&expr, &ctx).unwrap();
        assert!(matches!(result, ExecExpr::Literal(s) if s == "42"));
    }

    #[test]
    fn test_transform_field_access() {
        let translator = Translator::default();
        let ctx = make_ctx();

        let expr = Expr::Field(
            Box::new(Expr::Ident("s".to_string())),
            "max_bal".to_string(),
        );
        let result = translator.transform_expr(&expr, &ctx).unwrap();
        match result {
            ExecExpr::Field(base, field) => {
                assert_eq!(field, "max_bal");
                assert!(matches!(*base, ExecExpr::Var(name) if name == "s"));
            }
            _ => panic!("Expected Field, got {:?}", result),
        }
    }

    #[test]
    fn test_transform_if_else() {
        let translator = Translator::default();
        let ctx = make_ctx();

        let expr = Expr::If {
            cond: Box::new(Expr::Literal(Literal::Bool(true))),
            then_branch: Box::new(Expr::Literal(Literal::Int(1))),
            else_branch: Some(Box::new(Expr::Literal(Literal::Int(2)))),
        };
        let result = translator.transform_expr(&expr, &ctx).unwrap();
        assert!(matches!(result, ExecExpr::If { .. }));
    }

    #[test]
    fn test_transform_binary_comparison() {
        let translator = Translator::default();
        let ctx = make_ctx();

        let expr = Expr::Lt(
            Box::new(Expr::Ident("a".to_string())),
            Box::new(Expr::Ident("b".to_string())),
        );
        let result = translator.transform_expr(&expr, &ctx).unwrap();
        match result {
            ExecExpr::Binary { op, .. } => {
                assert_eq!(op, "<");
            }
            _ => panic!("Expected Binary, got {:?}", result),
        }
    }

    #[test]
    fn test_transform_clone_output() {
        let translator = Translator::default();
        let ctx = make_ctx();

        // s_ == s should produce clone
        let expr = Expr::Eq(
            Box::new(Expr::Ident("s_".to_string())),
            Box::new(Expr::Ident("s".to_string())),
        );
        let result = translator.transform_expr(&expr, &ctx).unwrap();
        assert!(matches!(result, ExecExpr::Clone(_)));
    }

    #[test]
    fn test_transform_seq_empty() {
        let translator = Translator::default();
        let ctx = make_ctx();

        let expr = Expr::SeqEmpty;
        let result = translator.transform_expr(&expr, &ctx).unwrap();
        assert!(matches!(result, ExecExpr::VecLit(v) if v.is_empty()));
    }

    #[test]
    fn test_transform_set_empty() {
        let translator = Translator::default();
        let ctx = make_ctx();

        let expr = Expr::SetEmpty;
        let result = translator.transform_expr(&expr, &ctx).unwrap();
        match result {
            ExecExpr::Call { func, args } => {
                assert_eq!(func, "HashSet::new");
                assert!(args.is_empty());
            }
            _ => panic!("Expected Call, got {:?}", result),
        }
    }

    #[test]
    fn test_transform_map_empty() {
        let translator = Translator::default();
        let ctx = make_ctx();

        let expr = Expr::MapEmpty;
        let result = translator.transform_expr(&expr, &ctx).unwrap();
        match result {
            ExecExpr::Call { func, args } => {
                assert_eq!(func, "HashMap::new");
                assert!(args.is_empty());
            }
            _ => panic!("Expected Call, got {:?}", result),
        }
    }

    #[test]
    fn test_clone_input_ref_in_struct_field() {
        let translator = Translator::default();
        // Create context where 'c' is an input parameter
        let mut ctx = make_ctx();
        ctx.input_params = vec!["c".to_string()];

        // Struct { constants: c } where c is an input param should produce Clone
        let expr = Expr::Struct {
            name: crate::ast::Path::single("LAcceptor".to_string()),
            fields: vec![("constants".to_string(), Expr::Ident("c".to_string()))],
        };
        let result = translator.transform_expr(&expr, &ctx).unwrap();

        match result {
            ExecExpr::Struct { name, fields } => {
                assert_eq!(name, "CAcceptor");
                assert_eq!(fields.len(), 1);
                let (field_name, field_val) = &fields[0];
                assert_eq!(field_name, "constants");
                // Field value should be Clone(Var("c"))
                match field_val {
                    ExecExpr::Clone(inner) => match inner.as_ref() {
                        ExecExpr::Var(name) => assert_eq!(name, "c"),
                        _ => panic!("Expected Var inside Clone, got {:?}", inner),
                    },
                    _ => panic!("Expected Clone, got {:?}", field_val),
                }
            }
            _ => panic!("Expected Struct, got {:?}", result),
        }
    }

    #[test]
    fn test_no_clone_for_non_input_in_struct_field() {
        let translator = Translator::default();
        // Create context where 'local_var' is NOT an input parameter
        let mut ctx = make_ctx();
        ctx.input_params = vec!["c".to_string()]; // Only 'c' is input

        // Struct { field: local_var } should NOT produce Clone
        let expr = Expr::Struct {
            name: crate::ast::Path::single("LStruct".to_string()),
            fields: vec![("field".to_string(), Expr::Ident("local_var".to_string()))],
        };
        let result = translator.transform_expr(&expr, &ctx).unwrap();

        match result {
            ExecExpr::Struct { name, fields } => {
                assert_eq!(name, "CStruct");
                assert_eq!(fields.len(), 1);
                let (field_name, field_val) = &fields[0];
                assert_eq!(field_name, "field");
                // Field value should NOT be Clone, just Var
                match field_val {
                    ExecExpr::Var(name) => assert_eq!(name, "local_var"),
                    _ => panic!("Expected Var (not Clone), got {:?}", field_val),
                }
            }
            _ => panic!("Expected Struct, got {:?}", result),
        }
    }

    #[test]
    fn test_extract_source_and_filter() {
        let translator = Translator::default();

        // Test: source.contains_key(k) && k >= threshold
        let contains_key = Expr::MethodCall {
            receiver: Box::new(Expr::Ident("source".to_string())),
            method: "contains_key".to_string(),
            args: vec![Expr::Ident("k".to_string())],
        };
        let filter = Expr::Ge(
            Box::new(Expr::Ident("k".to_string())),
            Box::new(Expr::Ident("threshold".to_string())),
        );
        let pred = Expr::Conjunction(vec![contains_key, filter.clone()]);

        let result = translator.extract_source_and_filter(&pred, "k");
        assert!(result.is_some());
        let (source, extracted_filter) = result.unwrap();
        assert_eq!(source, "source");
        // Filter should be the Ge expression
        assert!(matches!(extracted_filter, Expr::Ge(..)));
    }

    #[test]
    fn test_extract_source_dom_contains() {
        let translator = Translator::default();

        // Test: source.dom().contains(k)
        let dom = Expr::MethodCall {
            receiver: Box::new(Expr::Ident("source".to_string())),
            method: "dom".to_string(),
            args: vec![],
        };
        let contains = Expr::MethodCall {
            receiver: Box::new(dom),
            method: "contains".to_string(),
            args: vec![Expr::Ident("k".to_string())],
        };

        let result = translator.extract_contains_key_source(&contains, "k");
        assert!(result.is_some());
        assert_eq!(result.unwrap(), "source");
    }

    #[test]
    fn test_extract_source_from_conditional_value() {
        let translator = Translator::default();

        // Test: if cond { new_value } else { source[k] }
        let source_index = Expr::Index(
            Box::new(Expr::Ident("source".to_string())),
            Box::new(Expr::Ident("k".to_string())),
        );
        let conditional = Expr::If {
            cond: Box::new(Expr::Literal(Literal::Bool(true))),
            then_branch: Box::new(Expr::Ident("new_value".to_string())),
            else_branch: Some(Box::new(source_index)),
        };

        let result = translator.extract_source_from_conditional_value(&conditional, "k");
        assert!(result.is_some());
        assert_eq!(result.unwrap(), "source");
    }

    #[test]
    fn test_exists_with_container_contains() {
        let translator = Translator::default();
        let ctx = make_ctx();

        // Test: exists |p| S.contains(p) && pred(p)
        // Build S.contains(p)
        let contains = Expr::MethodCall {
            receiver: Box::new(Expr::Ident("S".to_string())),
            method: "contains".to_string(),
            args: vec![Expr::Ident("p".to_string())],
        };
        // Build pred(p) as p.valid
        let pred = Expr::Field(Box::new(Expr::Ident("p".to_string())), "valid".to_string());
        // Build conjunction
        let body = Expr::Conjunction(vec![contains, pred]);

        // Build exists expression
        let exists = Expr::Exists {
            vars: vec![crate::ast::Binding {
                pattern: crate::ast::Pattern::Ident("p".to_string()),
                ty: None,
                variable_mode: crate::ast::VariableMode::Exec,
            }],
            body: Box::new(body),
        };

        let result = translator.transform_expr(&exists, &ctx);
        assert!(
            result.is_ok(),
            "exists should transform successfully: {:?}",
            result
        );

        // Check the result is a method call to .any()
        let exec_expr = result.unwrap();
        match &exec_expr {
            ExecExpr::MethodCall { method, .. } => {
                assert_eq!(method, "any", "Should generate .any() call");
            }
            _ => panic!("Expected MethodCall, got {:?}", exec_expr),
        }
    }

    #[test]
    fn test_extract_exists_container_and_pred() {
        let translator = Translator::default();

        // Test: S.contains(p) && pred_call(p)
        let contains = Expr::MethodCall {
            receiver: Box::new(Expr::Ident("S".to_string())),
            method: "contains".to_string(),
            args: vec![Expr::Ident("p".to_string())],
        };
        let pred = Expr::Call {
            func: crate::ast::Path::single("some_pred".to_string()),
            args: vec![Expr::Ident("p".to_string())],
        };
        let body = Expr::Conjunction(vec![contains, pred.clone()]);

        let result = translator.extract_exists_container_and_pred(&body, "p");
        assert!(result.is_some());
        let (container, predicate) = result.unwrap();

        // Container should be S
        if let Expr::Ident(name) = container {
            assert_eq!(name, "S");
        } else {
            panic!("Container should be identifier");
        }

        // Predicate should be the call expression
        assert!(matches!(predicate, Expr::Call { .. }));
    }

    #[test]
    fn test_extract_exists_disjunction_containers() {
        let translator = Translator::default();

        // Test: (S1.contains(x) || S2.contains(x)) && pred(x)
        let contains1 = Expr::MethodCall {
            receiver: Box::new(Expr::Ident("S1".to_string())),
            method: "contains".to_string(),
            args: vec![Expr::Ident("x".to_string())],
        };
        let contains2 = Expr::MethodCall {
            receiver: Box::new(Expr::Ident("S2".to_string())),
            method: "contains".to_string(),
            args: vec![Expr::Ident("x".to_string())],
        };
        let disjunction = Expr::Disjunction(vec![contains1, contains2]);
        let pred = Expr::Call {
            func: crate::ast::Path::single("some_pred".to_string()),
            args: vec![Expr::Ident("x".to_string())],
        };
        let body = Expr::Conjunction(vec![disjunction, pred.clone()]);

        let result = translator.extract_exists_containers_and_pred(&body, "x");
        assert!(result.is_some());
        let (containers, predicate) = result.unwrap();

        // Should have 2 containers
        assert_eq!(containers.len(), 2);

        // First container should be S1
        if let Expr::Ident(name) = &containers[0] {
            assert_eq!(name, "S1");
        } else {
            panic!("First container should be identifier");
        }

        // Second container should be S2
        if let Expr::Ident(name) = &containers[1] {
            assert_eq!(name, "S2");
        } else {
            panic!("Second container should be identifier");
        }

        // Predicate should be the call expression
        assert!(matches!(predicate, Expr::Call { .. }));
    }

    #[test]
    fn test_collection_check_template() {
        let translator = Translator::default();
        let ctx = make_ctx();

        // Test: forall |p| packets.contains(p) ==> p.src != other.src
        // Build packets.contains(p)
        let contains = Expr::MethodCall {
            receiver: Box::new(Expr::Ident("packets".to_string())),
            method: "contains".to_string(),
            args: vec![Expr::Ident("p".to_string())],
        };
        // Build p.src != other.src
        let pred = Expr::Ne(
            Box::new(Expr::Field(
                Box::new(Expr::Ident("p".to_string())),
                "src".to_string(),
            )),
            Box::new(Expr::Field(
                Box::new(Expr::Ident("other".to_string())),
                "src".to_string(),
            )),
        );
        // Build implication
        let body = Expr::Implies(Box::new(contains), Box::new(pred));

        // Build forall expression
        let forall = Expr::Forall {
            vars: vec![crate::ast::Binding {
                pattern: crate::ast::Pattern::Ident("p".to_string()),
                ty: None,
                variable_mode: crate::ast::VariableMode::Exec,
            }],
            triggers: vec![],
            body: Box::new(body),
        };

        let result = translator.transform_expr(&forall, &ctx);
        assert!(
            result.is_ok(),
            "forall collection check should transform: {:?}",
            result
        );

        // Check the result is a method call to .all()
        let exec_expr = result.unwrap();
        match &exec_expr {
            ExecExpr::MethodCall { method, .. } => {
                assert_eq!(method, "all", "Should generate .all() call");
            }
            _ => panic!("Expected MethodCall with .all(), got {:?}", exec_expr),
        }
    }

    #[test]
    fn test_tuple_return_generation() {
        let translator = Translator::default();

        // Create context with two output params: s_ and sent_packets
        let config = TranslatorConfig::default();
        let ctx = TransformContext {
            config: &config,
            output_params: vec!["s_".to_string(), "sent_packets".to_string()],
            input_params: vec!["s".to_string()],
            output_types: HashMap::new(),
            field_substitutions: HashMap::new(),
        };

        // Build: s_ == s &&& sent_packets == Seq::empty()
        let s_assign = Expr::Eq(
            Box::new(Expr::Ident("s_".to_string())),
            Box::new(Expr::Ident("s".to_string())),
        );
        let packets_assign = Expr::Eq(
            Box::new(Expr::Ident("sent_packets".to_string())),
            Box::new(Expr::SeqEmpty),
        );
        let conjunction = Expr::Conjunction(vec![s_assign, packets_assign]);

        let result = translator.transform_expr(&conjunction, &ctx);
        assert!(result.is_ok(), "Conjunction should transform: {:?}", result);

        // Check that result is a Tuple with two elements
        let exec_expr = result.unwrap();
        match &exec_expr {
            ExecExpr::Tuple(elems) => {
                assert_eq!(elems.len(), 2, "Should have 2 tuple elements");
                // First should be clone of s (or Var if not recognized as clone)
                assert!(
                    matches!(&elems[0], ExecExpr::Clone(_))
                        || matches!(&elems[0], ExecExpr::Var(_)),
                    "First element should be Clone or Var, got {:?}",
                    elems[0]
                );
                // Second should be empty vec
                assert!(matches!(&elems[1], ExecExpr::VecLit(v) if v.is_empty()));
            }
            _ => panic!("Expected Tuple, got {:?}", exec_expr),
        }
    }

    #[test]
    fn test_detect_helper_call_with_output() {
        let translator = Translator::default();

        // Create context with s_ as output
        let config = TranslatorConfig::default();
        let ctx = TransformContext {
            config: &config,
            output_params: vec!["s_".to_string()],
            input_params: vec!["s".to_string(), "received_packet".to_string()],
            output_types: HashMap::new(),
            field_substitutions: HashMap::new(),
        };

        // Build: LProposerProcessRequest(s.proposer, s_.proposer, received_packet)
        let call = Expr::Call {
            func: crate::ast::Path::single("LProposerProcessRequest".to_string()),
            args: vec![
                // s.proposer (input)
                Expr::Field(
                    Box::new(Expr::Ident("s".to_string())),
                    "proposer".to_string(),
                ),
                // s_.proposer (output)
                Expr::Field(
                    Box::new(Expr::Ident("s_".to_string())),
                    "proposer".to_string(),
                ),
                // received_packet (input)
                Expr::Ident("received_packet".to_string()),
            ],
        };

        let result = translator.detect_helper_call(&call, &ctx);
        assert!(result.is_some(), "Should detect helper call");

        let info = result.unwrap();
        assert_eq!(info.func_name, "LProposerProcessRequest");
        assert_eq!(info.input_args.len(), 2, "Should have 2 input args");
        assert_eq!(info.output_fields.len(), 1, "Should have 1 output field");
        assert_eq!(
            info.output_fields[0],
            ("s_".to_string(), "proposer".to_string())
        );
    }

    #[test]
    fn test_generate_helper_let_binding() {
        let translator = Translator::default();

        // Create a HelperCallInfo for LProposerProcessRequest
        let info = crate::translator::HelperCallInfo {
            func_name: "LProposerProcessRequest".to_string(),
            input_args: vec![
                ExecExpr::Field(
                    Box::new(ExecExpr::Var("s".to_string())),
                    "proposer".to_string(),
                ),
                ExecExpr::Var("received_packet".to_string()),
            ],
            output_fields: vec![("s_".to_string(), "proposer".to_string())],
            output_params: vec![],
        };

        let let_binding = translator.generate_helper_let_binding(&info);

        // Check that it generates a Let expression
        match &let_binding {
            ExecExpr::Let { pattern, value, .. } => {
                assert_eq!(pattern, "s_proposer", "Variable name should be s_proposer");
                match value.as_ref() {
                    ExecExpr::Call { func, args } => {
                        assert_eq!(func, "CProposerProcessRequest");
                        assert_eq!(args.len(), 2);
                    }
                    _ => panic!("Expected Call, got {:?}", value),
                }
            }
            _ => panic!("Expected Let, got {:?}", let_binding),
        }
    }

    #[test]
    fn test_field_substitution() {
        let translator = Translator::default();
        let config = TranslatorConfig::default();

        // Create context with a field substitution
        let mut field_substitutions = HashMap::new();
        field_substitutions.insert(
            ("s_".to_string(), "proposer".to_string()),
            "s_proposer".to_string(),
        );

        let ctx = TransformContext {
            config: &config,
            output_params: vec!["s_".to_string()],
            input_params: vec!["s".to_string()],
            output_types: HashMap::new(),
            field_substitutions,
        };

        // Test: s_.proposer should be substituted to s_proposer
        let field_access = Expr::Field(
            Box::new(Expr::Ident("s_".to_string())),
            "proposer".to_string(),
        );

        let result = translator.transform_expr(&field_access, &ctx);
        assert!(result.is_ok(), "Should transform successfully");

        match result.unwrap() {
            ExecExpr::Var(name) => {
                assert_eq!(name, "s_proposer", "Should substitute to s_proposer");
            }
            other => panic!("Expected Var, got {:?}", other),
        }
    }

    #[test]
    fn test_multiple_helper_calls_in_conjunction() {
        // Test pattern from LReplicaNextProcess1b:
        // &&& LProposerProcess1b(s.proposer, s_.proposer, received_packet)
        // &&& LAcceptorTruncateLog(s.acceptor, s_.acceptor, truncation_point)
        // &&& sent_packets == Seq::empty()
        // &&& s_ == LReplica { ..., proposer: s_.proposer, acceptor: s_.acceptor, ... }

        let translator = Translator::default();
        let config = TranslatorConfig::default();

        let ctx = TransformContext {
            config: &config,
            output_params: vec!["s_".to_string(), "sent_packets".to_string()],
            input_params: vec!["s".to_string(), "received_packet".to_string()],
            output_types: HashMap::new(),
            field_substitutions: HashMap::new(),
        };

        // Build the conjunction
        let conjunction = Expr::Conjunction(vec![
            // LProposerProcess1b(s.proposer, s_.proposer, received_packet)
            Expr::Call {
                func: crate::ast::Path::single("LProposerProcess1b".to_string()),
                args: vec![
                    Expr::Field(
                        Box::new(Expr::Ident("s".to_string())),
                        "proposer".to_string(),
                    ),
                    Expr::Field(
                        Box::new(Expr::Ident("s_".to_string())),
                        "proposer".to_string(),
                    ),
                    Expr::Ident("received_packet".to_string()),
                ],
            },
            // LAcceptorTruncateLog(s.acceptor, s_.acceptor, truncation_point)
            Expr::Call {
                func: crate::ast::Path::single("LAcceptorTruncateLog".to_string()),
                args: vec![
                    Expr::Field(
                        Box::new(Expr::Ident("s".to_string())),
                        "acceptor".to_string(),
                    ),
                    Expr::Field(
                        Box::new(Expr::Ident("s_".to_string())),
                        "acceptor".to_string(),
                    ),
                    Expr::Ident("truncation_point".to_string()),
                ],
            },
            // sent_packets == Seq::empty()
            Expr::Eq(
                Box::new(Expr::Ident("sent_packets".to_string())),
                Box::new(Expr::MethodCall {
                    receiver: Box::new(Expr::Ident("Seq".to_string())),
                    method: "empty".to_string(),
                    args: vec![],
                }),
            ),
            // s_ == LReplica { proposer: s_.proposer, acceptor: s_.acceptor }
            Expr::Eq(
                Box::new(Expr::Ident("s_".to_string())),
                Box::new(Expr::Struct {
                    name: crate::ast::Path::single("LReplica".to_string()),
                    fields: vec![
                        (
                            "constants".to_string(),
                            Expr::Field(
                                Box::new(Expr::Ident("s".to_string())),
                                "constants".to_string(),
                            ),
                        ),
                        (
                            "proposer".to_string(),
                            Expr::Field(
                                Box::new(Expr::Ident("s_".to_string())),
                                "proposer".to_string(),
                            ),
                        ),
                        (
                            "acceptor".to_string(),
                            Expr::Field(
                                Box::new(Expr::Ident("s_".to_string())),
                                "acceptor".to_string(),
                            ),
                        ),
                    ],
                }),
            ),
        ]);

        let result = translator.transform_expr(&conjunction, &ctx);
        assert!(result.is_ok(), "Should transform conjunction: {:?}", result);

        // The result should be a Block with:
        // 1. let s_proposer = CProposerProcess1b(...)
        // 2. let s_acceptor = CAcceptorTruncateLog(...)
        // 3. Tuple((struct, Seq::empty()))
        match result.unwrap() {
            ExecExpr::Block(stmts) => {
                assert!(
                    stmts.len() >= 2,
                    "Should have at least 2 statements (let bindings), got {}",
                    stmts.len()
                );

                // Check first let binding
                match &stmts[0] {
                    ExecExpr::Let { pattern, .. } => {
                        assert_eq!(pattern, "s_proposer", "First let should bind s_proposer");
                    }
                    other => panic!("Expected Let for first statement, got {:?}", other),
                }

                // Check second let binding
                match &stmts[1] {
                    ExecExpr::Let { pattern, .. } => {
                        assert_eq!(pattern, "s_acceptor", "Second let should bind s_acceptor");
                    }
                    other => panic!("Expected Let for second statement, got {:?}", other),
                }
            }
            other => panic!("Expected Block, got {:?}", other),
        }
    }

    #[test]
    fn test_helper_call_with_both_field_and_param_outputs() {
        // Test pattern from LReplicaNextProcess1a:
        // &&& LAcceptorProcess1a(s.acceptor, s_.acceptor, received_packet, sent_packets)
        // &&& s_ == LReplica { ..., acceptor: s_.acceptor, ... }
        // Here the helper call outputs both s_.acceptor AND sent_packets

        let translator = Translator::default();
        let config = TranslatorConfig::default();

        let ctx = TransformContext {
            config: &config,
            output_params: vec!["s_".to_string(), "sent_packets".to_string()],
            input_params: vec!["s".to_string(), "received_packet".to_string()],
            output_types: HashMap::new(),
            field_substitutions: HashMap::new(),
        };

        // Build the conjunction
        let conjunction = Expr::Conjunction(vec![
            // LAcceptorProcess1a(s.acceptor, s_.acceptor, received_packet, sent_packets)
            Expr::Call {
                func: crate::ast::Path::single("LAcceptorProcess1a".to_string()),
                args: vec![
                    Expr::Field(
                        Box::new(Expr::Ident("s".to_string())),
                        "acceptor".to_string(),
                    ),
                    Expr::Field(
                        Box::new(Expr::Ident("s_".to_string())),
                        "acceptor".to_string(),
                    ),
                    Expr::Ident("received_packet".to_string()),
                    Expr::Ident("sent_packets".to_string()),
                ],
            },
            // s_ == LReplica { acceptor: s_.acceptor, ... }
            Expr::Eq(
                Box::new(Expr::Ident("s_".to_string())),
                Box::new(Expr::Struct {
                    name: crate::ast::Path::single("LReplica".to_string()),
                    fields: vec![
                        (
                            "constants".to_string(),
                            Expr::Field(
                                Box::new(Expr::Ident("s".to_string())),
                                "constants".to_string(),
                            ),
                        ),
                        (
                            "acceptor".to_string(),
                            Expr::Field(
                                Box::new(Expr::Ident("s_".to_string())),
                                "acceptor".to_string(),
                            ),
                        ),
                    ],
                }),
            ),
        ]);

        let result = translator.transform_expr(&conjunction, &ctx);
        assert!(result.is_ok(), "Should transform conjunction: {:?}", result);

        // The result should be a Block with:
        // 1. let (s_acceptor, sent_packets) = CAcceptorProcess1a(...)
        // 2. (CReplica { ..., acceptor: s_acceptor }, sent_packets)
        match result.unwrap() {
            ExecExpr::Block(stmts) => {
                assert_eq!(
                    stmts.len(),
                    2,
                    "Should have 2 statements: let binding and tuple return"
                );

                // Check let binding has tuple pattern
                match &stmts[0] {
                    ExecExpr::Let { pattern, .. } => {
                        assert!(
                            pattern.contains("s_acceptor"),
                            "Pattern should contain s_acceptor: {}",
                            pattern
                        );
                        assert!(
                            pattern.contains("sent_packets"),
                            "Pattern should contain sent_packets: {}",
                            pattern
                        );
                    }
                    other => panic!("Expected Let for first statement, got {:?}", other),
                }

                // Check return is a tuple with struct and sent_packets
                match &stmts[1] {
                    ExecExpr::Tuple(elements) => {
                        assert_eq!(elements.len(), 2, "Tuple should have 2 elements");
                        // First element should be struct
                        match &elements[0] {
                            ExecExpr::Struct { .. } => {}
                            other => {
                                panic!("Expected Struct as first tuple element, got {:?}", other)
                            }
                        }
                        // Second element should be sent_packets variable
                        match &elements[1] {
                            ExecExpr::Var(name) => {
                                assert_eq!(
                                    name, "sent_packets",
                                    "Second element should be sent_packets"
                                );
                            }
                            other => panic!(
                                "Expected Var(sent_packets) as second tuple element, got {:?}",
                                other
                            ),
                        }
                    }
                    other => panic!("Expected Tuple as second statement, got {:?}", other),
                }
            }
            other => panic!("Expected Block, got {:?}", other),
        }
    }

    #[test]
    fn test_map_filter_conjunction() {
        // Test pattern from RemoveVotesBeforeLogTruncationPoint:
        // &&& forall |opn| votes_.contains_key(opn) ==> votes.contains_key(opn) && votes_[opn] == votes[opn]
        // &&& forall |opn| opn < log_truncation_point ==> !votes_.contains_key(opn)
        // &&& forall |opn| opn >= log_truncation_point && votes.contains_key(opn) ==> votes_.contains_key(opn)

        let translator = Translator::default();
        let config = TranslatorConfig::default();

        let ctx = TransformContext {
            config: &config,
            output_params: vec!["votes_".to_string()],
            input_params: vec!["votes".to_string(), "log_truncation_point".to_string()],
            output_types: HashMap::new(),
            field_substitutions: HashMap::new(),
        };

        // Build the three foralls
        let binding = crate::ast::Binding {
            pattern: crate::ast::Pattern::Ident("opn".to_string()),
            ty: None,
            variable_mode: crate::ast::VariableMode::Exec,
        };

        // Forall 1: votes_.contains_key(opn) ==> votes.contains_key(opn) && votes_[opn] == votes[opn]
        let forall1 = Expr::Forall {
            vars: vec![binding.clone()],
            triggers: vec![],
            body: Box::new(Expr::Implies(
                Box::new(Expr::MethodCall {
                    receiver: Box::new(Expr::Ident("votes_".to_string())),
                    method: "contains_key".to_string(),
                    args: vec![Expr::Ident("opn".to_string())],
                }),
                Box::new(Expr::Binary(
                    Box::new(Expr::MethodCall {
                        receiver: Box::new(Expr::Ident("votes".to_string())),
                        method: "contains_key".to_string(),
                        args: vec![Expr::Ident("opn".to_string())],
                    }),
                    crate::ast::BinOp::And,
                    Box::new(Expr::Eq(
                        Box::new(Expr::Index(
                            Box::new(Expr::Ident("votes_".to_string())),
                            Box::new(Expr::Ident("opn".to_string())),
                        )),
                        Box::new(Expr::Index(
                            Box::new(Expr::Ident("votes".to_string())),
                            Box::new(Expr::Ident("opn".to_string())),
                        )),
                    )),
                )),
            )),
        };

        // Forall 2: opn < log_truncation_point ==> !votes_.contains_key(opn)
        let forall2 = Expr::Forall {
            vars: vec![binding.clone()],
            triggers: vec![],
            body: Box::new(Expr::Implies(
                Box::new(Expr::Lt(
                    Box::new(Expr::Ident("opn".to_string())),
                    Box::new(Expr::Ident("log_truncation_point".to_string())),
                )),
                Box::new(Expr::Not(Box::new(Expr::MethodCall {
                    receiver: Box::new(Expr::Ident("votes_".to_string())),
                    method: "contains_key".to_string(),
                    args: vec![Expr::Ident("opn".to_string())],
                }))),
            )),
        };

        // Forall 3: opn >= log_truncation_point && votes.contains_key(opn) ==> votes_.contains_key(opn)
        let forall3 = Expr::Forall {
            vars: vec![binding.clone()],
            triggers: vec![],
            body: Box::new(Expr::Implies(
                Box::new(Expr::Binary(
                    Box::new(Expr::Ge(
                        Box::new(Expr::Ident("opn".to_string())),
                        Box::new(Expr::Ident("log_truncation_point".to_string())),
                    )),
                    crate::ast::BinOp::And,
                    Box::new(Expr::MethodCall {
                        receiver: Box::new(Expr::Ident("votes".to_string())),
                        method: "contains_key".to_string(),
                        args: vec![Expr::Ident("opn".to_string())],
                    }),
                )),
                Box::new(Expr::MethodCall {
                    receiver: Box::new(Expr::Ident("votes_".to_string())),
                    method: "contains_key".to_string(),
                    args: vec![Expr::Ident("opn".to_string())],
                }),
            )),
        };

        let conjunction = Expr::Conjunction(vec![forall1, forall2, forall3]);

        let result = translator.transform_expr(&conjunction, &ctx);
        assert!(
            result.is_ok(),
            "Should transform map filter conjunction: {:?}",
            result
        );

        // Should generate: votes.iter().filter(|(opn, _)| opn >= log_truncation_point).cloned().collect()
        match result.unwrap() {
            ExecExpr::MethodCall {
                method, receiver, ..
            } => {
                assert_eq!(method, "collect", "Should end with .collect()");
                match receiver.as_ref() {
                    ExecExpr::MethodCall {
                        method, receiver, ..
                    } => {
                        assert_eq!(method, "cloned", "Should have .cloned() before collect");
                        match receiver.as_ref() {
                            ExecExpr::MethodCall { method, args, .. } => {
                                assert_eq!(method, "filter", "Should have .filter()");
                                assert_eq!(args.len(), 1, "Filter should have closure arg");
                                match &args[0] {
                                    ExecExpr::Closure { params, .. } => {
                                        assert!(
                                            params[0].contains("opn"),
                                            "Closure param should contain opn"
                                        );
                                    }
                                    _ => panic!("Expected Closure"),
                                }
                            }
                            _ => panic!("Expected MethodCall for filter"),
                        }
                    }
                    _ => panic!("Expected MethodCall for cloned"),
                }
            }
            other => panic!("Expected MethodCall with collect, got {:?}", other),
        }
    }

    #[test]
    fn test_expr_to_simple_string() {
        let translator = Translator::default();

        // Test: simple identifier
        let ident = Expr::Ident("x".to_string());
        assert_eq!(translator.expr_to_simple_string(&ident), "x");

        // Test: field access
        let field = Expr::Field(
            Box::new(Expr::Ident("obj".to_string())),
            "field".to_string(),
        );
        assert_eq!(translator.expr_to_simple_string(&field), "obj.field");

        // Test: arrow access (enum field)
        let arrow = Expr::Arrow(
            Box::new(Expr::Ident("msg".to_string())),
            "bal_1a".to_string(),
        );
        assert_eq!(translator.expr_to_simple_string(&arrow), "msg.get_bal_1a()");

        // Test: method call
        let method_call = Expr::MethodCall {
            receiver: Box::new(Expr::Ident("list".to_string())),
            method: "contains".to_string(),
            args: vec![Expr::Ident("item".to_string())],
        };
        assert_eq!(
            translator.expr_to_simple_string(&method_call),
            "list.contains(item)"
        );

        // Test: function call with C prefix
        let func_call = Expr::Call {
            func: crate::ast::Path::single("BalLeq".to_string()),
            args: vec![Expr::Ident("a".to_string()), Expr::Ident("b".to_string())],
        };
        assert_eq!(
            translator.expr_to_simple_string(&func_call),
            "CBalLeq(a, b)"
        );

        // Test: is expression - variant name gets translated with C prefix
        let is_expr = Expr::Is(
            Box::new(Expr::Field(
                Box::new(Expr::Ident("inp".to_string())),
                "msg".to_string(),
            )),
            "RslMessage1a".to_string(),
        );
        // Note: Default translator (without remapping) applies C prefix rule
        assert_eq!(
            translator.expr_to_simple_string(&is_expr),
            "inp.msg is CRslMessage1a"
        );

        // Test: comparison
        let lt = Expr::Lt(
            Box::new(Expr::Ident("x".to_string())),
            Box::new(Expr::Ident("y".to_string())),
        );
        assert_eq!(translator.expr_to_simple_string(&lt), "(x < y)");

        // Test: binary operation (and)
        let binary_and = Expr::Binary(
            Box::new(Expr::Ident("a".to_string())),
            BinOp::And,
            Box::new(Expr::Ident("b".to_string())),
        );
        assert_eq!(translator.expr_to_simple_string(&binary_and), "(a && b)");

        // Test: literal
        let lit_int = Expr::Literal(Literal::Int(42));
        assert_eq!(translator.expr_to_simple_string(&lit_int), "42");

        let lit_bool = Expr::Literal(Literal::Bool(true));
        assert_eq!(translator.expr_to_simple_string(&lit_bool), "true");
    }

    #[test]
    fn test_method_calls_transformation() {
        use crate::config::MethodCallConfig;

        let mut config = TranslatorConfig::default();
        config.method_calls.insert(
            "LMinQuorumSize".to_string(),
            MethodCallConfig {
                method_name: "CMinQuorumSize".to_string(),
                receiver_arg_index: 0,
            },
        );
        config.method_calls.insert(
            "GetReplicaIndex".to_string(),
            MethodCallConfig {
                method_name: "CGetReplicaIndex".to_string(),
                receiver_arg_index: 1,
            },
        );
        config.method_calls.insert(
            "LReplicaConstantsValid".to_string(),
            MethodCallConfig {
                method_name: "CReplicaConstantsValid".to_string(),
                receiver_arg_index: 0,
            },
        );

        let translator = Translator::new(config);

        // Test LMinQuorumSize(config) -> config.CMinQuorumSize()
        let call1 = Expr::Call {
            func: crate::ast::Path::single("LMinQuorumSize".to_string()),
            args: vec![Expr::Ident("config".to_string())],
        };
        assert_eq!(
            translator.expr_to_simple_string(&call1),
            "config.CMinQuorumSize()"
        );

        // Test GetReplicaIndex(id, config) -> config.CGetReplicaIndex(id)
        let call2 = Expr::Call {
            func: crate::ast::Path::single("GetReplicaIndex".to_string()),
            args: vec![
                Expr::Ident("id".to_string()),
                Expr::Ident("config".to_string()),
            ],
        };
        assert_eq!(
            translator.expr_to_simple_string(&call2),
            "config.CGetReplicaIndex(id)"
        );

        // Test LReplicaConstantsValid(c) -> c.CReplicaConstantsValid()
        let call3 = Expr::Call {
            func: crate::ast::Path::single("LReplicaConstantsValid".to_string()),
            args: vec![Expr::Field(
                Box::new(Expr::Ident("s".to_string())),
                "constants".to_string(),
            )],
        };
        assert_eq!(
            translator.expr_to_simple_string(&call3),
            "s.constants.CReplicaConstantsValid()"
        );
    }

    #[test]
    fn test_seq_init_pattern() {
        let translator = Translator::default();
        let config = TranslatorConfig::default();

        let ctx = TransformContext {
            config: &config,
            output_params: vec!["a".to_string()],
            input_params: vec!["c".to_string()],
            output_types: HashMap::new(),
            field_substitutions: HashMap::new(),
        };

        // Build the pattern:
        // a.seq_field.len() == c.items.len()
        // forall |idx| 0 <= idx < a.seq_field.len() ==> a.seq_field[idx] == 0
        let length_expr = Expr::Eq(
            Box::new(Expr::MethodCall {
                receiver: Box::new(Expr::Field(
                    Box::new(Expr::Ident("a".to_string())),
                    "seq_field".to_string(),
                )),
                method: "len".to_string(),
                args: vec![],
            }),
            Box::new(Expr::MethodCall {
                receiver: Box::new(Expr::Field(
                    Box::new(Expr::Ident("c".to_string())),
                    "items".to_string(),
                )),
                method: "len".to_string(),
                args: vec![],
            }),
        );

        let binding = crate::ast::Binding {
            pattern: crate::ast::Pattern::Ident("idx".to_string()),
            ty: None,
            variable_mode: crate::ast::VariableMode::Exec,
        };

        let forall_expr = Expr::Forall {
            vars: vec![binding],
            triggers: vec![],
            body: Box::new(Expr::Implies(
                Box::new(Expr::Binary(
                    Box::new(Expr::Le(
                        Box::new(Expr::Literal(Literal::Int(0))),
                        Box::new(Expr::Ident("idx".to_string())),
                    )),
                    BinOp::And,
                    Box::new(Expr::Lt(
                        Box::new(Expr::Ident("idx".to_string())),
                        Box::new(Expr::MethodCall {
                            receiver: Box::new(Expr::Field(
                                Box::new(Expr::Ident("a".to_string())),
                                "seq_field".to_string(),
                            )),
                            method: "len".to_string(),
                            args: vec![],
                        }),
                    )),
                )),
                Box::new(Expr::Eq(
                    Box::new(Expr::Index(
                        Box::new(Expr::Field(
                            Box::new(Expr::Ident("a".to_string())),
                            "seq_field".to_string(),
                        )),
                        Box::new(Expr::Ident("idx".to_string())),
                    )),
                    Box::new(Expr::Literal(Literal::Int(0))),
                )),
            )),
        };

        // Test try_extract_seq_init_pattern
        let exprs = vec![length_expr, forall_expr];
        let result = translator.try_extract_seq_init_pattern(&exprs, &ctx);

        assert!(result.is_some(), "Should detect seq init pattern");
        let (out_var, field_name, _length, element) = result.unwrap();
        assert_eq!(out_var, "a");
        assert_eq!(field_name, "seq_field");
        // Element should be the literal 0
        assert!(matches!(element, Expr::Literal(Literal::Int(0))));
    }

    #[test]
    fn test_map_update_with_insert_pattern() {
        // Test the pattern for CAddVoteAndRemoveOldOnes:
        // Domain: votes_.dom().contains(opn) <==> opn >= log_truncation_point && (votes.dom().contains(opn) || opn == new_opn)
        // Value: votes_.dom().contains(opn) ==> votes_[opn] == (if opn == new_opn {new_vote} else {votes[opn]})

        let translator = Translator::default();
        let ctx = TransformContext {
            config: &translator.config,
            output_params: vec!["votes_".to_string()],
            input_params: vec![
                "votes".to_string(),
                "new_opn".to_string(),
                "new_vote".to_string(),
                "log_truncation_point".to_string(),
            ],
            output_types: std::collections::HashMap::new(),
            field_substitutions: std::collections::HashMap::new(),
        };

        let binding = crate::ast::Binding {
            pattern: crate::ast::Pattern::Ident("opn".to_string()),
            ty: None,
            variable_mode: crate::ast::VariableMode::Exec,
        };

        // Domain biconditional forall:
        // forall opn: votes_.dom().contains(opn) <==> opn >= log_truncation_point && (votes.dom().contains(opn) || opn == new_opn)
        let domain_forall = Expr::Forall {
            vars: vec![binding.clone()],
            triggers: vec![],
            body: Box::new(Expr::Iff(
                Box::new(Expr::MethodCall {
                    receiver: Box::new(Expr::MethodCall {
                        receiver: Box::new(Expr::Ident("votes_".to_string())),
                        method: "dom".to_string(),
                        args: vec![],
                    }),
                    method: "contains".to_string(),
                    args: vec![Expr::Ident("opn".to_string())],
                }),
                Box::new(Expr::Binary(
                    Box::new(Expr::Ge(
                        Box::new(Expr::Ident("opn".to_string())),
                        Box::new(Expr::Ident("log_truncation_point".to_string())),
                    )),
                    crate::ast::BinOp::And,
                    Box::new(Expr::Binary(
                        Box::new(Expr::MethodCall {
                            receiver: Box::new(Expr::MethodCall {
                                receiver: Box::new(Expr::Ident("votes".to_string())),
                                method: "dom".to_string(),
                                args: vec![],
                            }),
                            method: "contains".to_string(),
                            args: vec![Expr::Ident("opn".to_string())],
                        }),
                        crate::ast::BinOp::Or,
                        Box::new(Expr::Eq(
                            Box::new(Expr::Ident("opn".to_string())),
                            Box::new(Expr::Ident("new_opn".to_string())),
                        )),
                    )),
                )),
            )),
        };

        // Value conditional forall:
        // forall opn: votes_.dom().contains(opn) ==> votes_[opn] == (if opn == new_opn {new_vote} else {votes[opn]})
        let value_forall = Expr::Forall {
            vars: vec![binding.clone()],
            triggers: vec![],
            body: Box::new(Expr::Implies(
                Box::new(Expr::MethodCall {
                    receiver: Box::new(Expr::MethodCall {
                        receiver: Box::new(Expr::Ident("votes_".to_string())),
                        method: "dom".to_string(),
                        args: vec![],
                    }),
                    method: "contains".to_string(),
                    args: vec![Expr::Ident("opn".to_string())],
                }),
                Box::new(Expr::Eq(
                    Box::new(Expr::Index(
                        Box::new(Expr::Ident("votes_".to_string())),
                        Box::new(Expr::Ident("opn".to_string())),
                    )),
                    Box::new(Expr::If {
                        cond: Box::new(Expr::Eq(
                            Box::new(Expr::Ident("opn".to_string())),
                            Box::new(Expr::Ident("new_opn".to_string())),
                        )),
                        then_branch: Box::new(Expr::Ident("new_vote".to_string())),
                        else_branch: Some(Box::new(Expr::Index(
                            Box::new(Expr::Ident("votes".to_string())),
                            Box::new(Expr::Ident("opn".to_string())),
                        ))),
                    }),
                )),
            )),
        };

        let conjunction = Expr::Conjunction(vec![domain_forall, value_forall]);

        let result = translator.transform_expr(&conjunction, &ctx);
        assert!(
            result.is_ok(),
            "Should transform map update with insert: {:?}",
            result
        );

        // Should generate a block with:
        // 1. let mut __result = source.iter().filter().map().collect()
        // 2. __result.insert(new_key, new_value)
        // 3. __result
        match result.unwrap() {
            ExecExpr::Block(stmts) => {
                assert_eq!(stmts.len(), 3, "Block should have 3 statements");

                // First should be let binding
                match &stmts[0] {
                    ExecExpr::Let { pattern, .. } => {
                        assert!(
                            pattern.contains("__result"),
                            "Should declare __result variable"
                        );
                    }
                    other => panic!("Expected Let binding, got {:?}", other),
                }

                // Second should be insert call
                match &stmts[1] {
                    ExecExpr::MethodCall { method, args, .. } => {
                        assert_eq!(method, "insert", "Should call insert");
                        assert_eq!(args.len(), 2, "Insert should have 2 args (key, value)");
                    }
                    other => panic!("Expected MethodCall for insert, got {:?}", other),
                }

                // Third should be __result
                match &stmts[2] {
                    ExecExpr::Var(name) => {
                        assert_eq!(name, "__result", "Should return __result");
                    }
                    other => panic!("Expected Var(__result), got {:?}", other),
                }
            }
            other => panic!("Expected Block, got {:?}", other),
        }
    }

    #[test]
    fn test_configurable_validity_predicate_name() {
        // Test that the validity predicate name is configurable
        let config = TranslatorConfig {
            validity_predicate_name: "valid".to_string(),
            ..Default::default()
        };

        let translator = Translator::new(config);

        // The translator should use "valid" instead of "well_formed"
        // We can't easily test build_requires/build_ensures directly,
        // but we can verify the config is stored correctly
        assert_eq!(
            translator.config.validity_predicate_name, "valid",
            "Should use configured validity predicate name"
        );
    }

    #[test]
    fn test_generate_map_filter_loop() {
        // Test that generate_loops_for_verification produces loop code with invariants
        let config = TranslatorConfig {
            generate_loops_for_verification: true,
            ..Default::default()
        };

        let translator = Translator::new(config);

        // Generate a simple filter expression
        let filter_expr = ExecExpr::Binary {
            lhs: Box::new(ExecExpr::Unary {
                op: "*".to_string(),
                expr: Box::new(ExecExpr::Var("opn".to_string())),
            }),
            op: ">=".to_string(),
            rhs: Box::new(ExecExpr::Var("threshold".to_string())),
        };

        let result = translator.generate_map_filter_loop("votes", "opn", filter_expr);

        // Should be a Block with 16 statements:
        // 0: BroadcastUse, 1: Let (keys), 2-4: pre-loop assertions,
        // 5: GhostVar, 6: Let (result), 7: ForInIter, 8-14: post-loop assertions, 15: Var
        match result {
            ExecExpr::Block(stmts) => {
                assert_eq!(stmts.len(), 16, "Block should have 16 statements");

                // First statement: broadcast use
                match &stmts[0] {
                    ExecExpr::BroadcastUse(path) => {
                        assert!(path.contains("hash"), "Should broadcast hash axioms");
                    }
                    _ => panic!("First statement should be BroadcastUse"),
                }

                // Second statement: let iter_name = source.keys()
                match &stmts[1] {
                    ExecExpr::Let { pattern, .. } => {
                        assert_eq!(pattern, "votes_keys", "Should create votes_keys iterator");
                    }
                    _ => panic!("Second statement should be Let"),
                }

                // Statements 2-4: pre-loop assertions
                match &stmts[2] {
                    ExecExpr::Assert(_) => {}
                    _ => panic!("Statement 2 should be Assert"),
                }
                match &stmts[3] {
                    ExecExpr::Assume(_) => {}
                    _ => panic!("Statement 3 should be Assume"),
                }
                match &stmts[4] {
                    ExecExpr::Assert(_) => {}
                    _ => panic!("Statement 4 should be Assert"),
                }

                // Statement 5: let ghost mut seen_keys = Set::empty()
                match &stmts[5] {
                    ExecExpr::GhostVar { name, mutable, .. } => {
                        assert_eq!(name, "seen_keys", "Should create seen_keys ghost var");
                        assert!(mutable, "Ghost var should be mutable");
                    }
                    _ => panic!("Statement 5 should be GhostVar"),
                }

                // Statement 6: let mut result = HashMap::new()
                match &stmts[6] {
                    ExecExpr::Let { pattern, .. } => {
                        assert!(pattern.contains("result"), "Should create result variable");
                    }
                    _ => panic!("Statement 6 should be Let"),
                }

                // Statement 7: ForInIter with invariants
                match &stmts[7] {
                    ExecExpr::ForInIter {
                        var,
                        iter_name,
                        invariants,
                        body,
                        ..
                    } => {
                        assert_eq!(var, "opn", "Loop variable should be opn");
                        assert_eq!(iter_name, "votes_keys", "Should iterate votes_keys");

                        // Should have 5 invariants for map filter pattern
                        assert_eq!(invariants.len(), 5, "Should have 5 invariants");
                        assert!(
                            invariants[0].contains("seen_keys.subset_of"),
                            "First invariant: seen subset"
                        );
                        assert!(
                            invariants[1].contains("seen_keys.contains"),
                            "Second invariant: seen in source"
                        );
                        assert!(
                            invariants[2].contains("result@.contains_key"),
                            "Third invariant: result satisfies filter"
                        );
                        assert!(
                            invariants[3].contains("seen_keys.contains"),
                            "Fourth invariant: result from seen"
                        );
                        assert!(
                            invariants[4].contains("result@.contains_key"),
                            "Fifth invariant: all matching in result"
                        );

                        // Body should contain in-loop assertions, proof block, and if
                        match body.as_ref() {
                            ExecExpr::Block(body_stmts) => {
                                assert_eq!(body_stmts.len(), 4, "Body should have 4 statements");
                            }
                            _ => panic!("Body should be Block"),
                        }
                    }
                    _ => panic!("Statement 7 should be ForInIter"),
                }

                // Statements 8-14: post-loop assertions (7 items)
                // 8: Assert (seen_keys.subset_of)
                match &stmts[8] {
                    ExecExpr::Assert(_) => {}
                    _ => panic!("Statement 8 should be Assert"),
                }
                // 9: Assume (iterator completed)
                match &stmts[9] {
                    ExecExpr::Assume(_) => {}
                    _ => panic!("Statement 9 should be Assume"),
                }
                // 10: Assume (seen_keys.len)
                match &stmts[10] {
                    ExecExpr::Assume(_) => {}
                    _ => panic!("Statement 10 should be Assume"),
                }
                // 11: ProofBlock (subset_len_equal_implies_equal)
                match &stmts[11] {
                    ExecExpr::ProofBlock { .. } => {}
                    _ => panic!("Statement 11 should be ProofBlock"),
                }
                // 12: Assert (seen_keys == source@.dom())
                match &stmts[12] {
                    ExecExpr::Assert(_) => {}
                    _ => panic!("Statement 12 should be Assert"),
                }
                // 13-14: Comments for postcondition assertions
                match &stmts[13] {
                    ExecExpr::Comment(_) => {}
                    _ => panic!("Statement 13 should be Comment"),
                }
                match &stmts[14] {
                    ExecExpr::Comment(_) => {}
                    _ => panic!("Statement 14 should be Comment"),
                }

                // Statement 15: result
                match &stmts[15] {
                    ExecExpr::Var(name) => {
                        assert_eq!(name, "result", "Should return result");
                    }
                    _ => panic!("Statement 15 should be Var(result)"),
                }
            }
            _ => panic!("Expected Block, got {:?}", result),
        }
    }

    #[test]
    fn test_generate_loops_config_default_false() {
        let config = TranslatorConfig::default();
        assert!(
            !config.generate_loops_for_verification,
            "Default should be false"
        );
    }

    #[test]
    fn test_expr_to_invariant_string() {
        let config = TranslatorConfig::default();
        let translator = Translator::new(config);

        // Test variable (should add dereference)
        let var = ExecExpr::Var("key".to_string());
        assert_eq!(translator.expr_to_invariant_string(&var), "*key");

        // Test binary expression
        let binary = ExecExpr::Binary {
            lhs: Box::new(ExecExpr::Unary {
                op: "*".to_string(),
                expr: Box::new(ExecExpr::Var("opn".to_string())),
            }),
            op: ">=".to_string(),
            rhs: Box::new(ExecExpr::Var("threshold".to_string())),
        };
        assert_eq!(
            translator.expr_to_invariant_string(&binary),
            "*opn >= *threshold"
        );

        // Test literal
        let lit = ExecExpr::Literal("42".to_string());
        assert_eq!(translator.expr_to_invariant_string(&lit), "42");

        // Test field access
        let field = ExecExpr::Field(
            Box::new(ExecExpr::Var("s".to_string())),
            "votes".to_string(),
        );
        assert_eq!(translator.expr_to_invariant_string(&field), "s.votes");
    }

    #[test]
    fn test_generate_map_filter_invariants() {
        let config = TranslatorConfig::default();
        let translator = Translator::new(config);

        let invariants =
            translator.generate_map_filter_invariants("votes", "opn", "*opn >= threshold");

        assert_eq!(invariants.len(), 5, "Should generate 5 invariants");

        // Check invariant content
        assert!(invariants[0].contains("seen_keys.subset_of(votes@.dom())"));
        assert!(invariants[1].contains("forall |opn|"));
        assert!(invariants[1].contains("seen_keys.contains(opn)"));
        assert!(invariants[1].contains("votes@.contains_key(opn)"));
        assert!(invariants[2].contains("*opn >= threshold"));
        assert!(invariants[4].contains("*opn >= threshold"));
    }

    #[test]
    fn test_generate_pre_loop_assertions() {
        let config = TranslatorConfig::default();
        let translator = Translator::new(config);

        let assertions = translator.generate_pre_loop_assertions("m_keys", "votes");

        // Should generate 3 pre-loop assertions
        assert_eq!(assertions.len(), 3, "Should generate 3 pre-loop assertions");

        // First assertion: m_keys@.0 == 0
        match &assertions[0] {
            ExecExpr::Assert(_) => {}
            _ => panic!("First pre-loop should be Assert"),
        }

        // Second assertion: assume iterator length
        match &assertions[1] {
            ExecExpr::Assume(_) => {}
            _ => panic!("Second pre-loop should be Assume"),
        }

        // Third assertion: iterator to_set matches dom
        match &assertions[2] {
            ExecExpr::Assert(_) => {}
            _ => panic!("Third pre-loop should be Assert"),
        }
    }

    #[test]
    fn test_generate_in_loop_assertions() {
        let config = TranslatorConfig::default();
        let translator = Translator::new(config);

        let assertions = translator.generate_in_loop_assertions("key", "votes");

        // Should generate 2 in-loop statements
        assert_eq!(assertions.len(), 2, "Should generate 2 in-loop statements");

        // First: broadcast use hash axioms
        match &assertions[0] {
            ExecExpr::BroadcastUse(path) => {
                assert!(path.contains("hash"), "Should broadcast hash axioms");
            }
            _ => panic!("First in-loop should be BroadcastUse"),
        }

        // Second: assume key is in source
        match &assertions[1] {
            ExecExpr::Assume(_) => {}
            _ => panic!("Second in-loop should be Assume"),
        }
    }

    #[test]
    fn test_generate_post_loop_assertions() {
        let config = TranslatorConfig::default();
        let translator = Translator::new(config);

        let assertions =
            translator.generate_post_loop_assertions("m_keys", "votes", "opn", "*opn >= threshold");

        // Should generate 7 post-loop statements
        assert_eq!(
            assertions.len(),
            7,
            "Should generate 7 post-loop statements"
        );

        // 0: Assert (seen_keys.subset_of)
        match &assertions[0] {
            ExecExpr::Assert(_) => {}
            _ => panic!("assertions[0] should be Assert"),
        }

        // 1: Assume (iterator completed)
        match &assertions[1] {
            ExecExpr::Assume(_) => {}
            _ => panic!("assertions[1] should be Assume"),
        }

        // 2: Assume (seen_keys.len)
        match &assertions[2] {
            ExecExpr::Assume(_) => {}
            _ => panic!("assertions[2] should be Assume"),
        }

        // 3: ProofBlock (subset_len_equal_implies_equal)
        match &assertions[3] {
            ExecExpr::ProofBlock { stmts } => {
                assert_eq!(stmts.len(), 1, "ProofBlock should have 1 statement");
                match &stmts[0] {
                    ExecExpr::Call { func, .. } => {
                        assert!(func.contains("subset_len_equal_implies_equal"));
                    }
                    _ => panic!("ProofBlock should contain Call"),
                }
            }
            _ => panic!("assertions[3] should be ProofBlock"),
        }

        // 4: Assert (seen_keys == source@.dom())
        match &assertions[4] {
            ExecExpr::Assert(_) => {}
            _ => panic!("assertions[4] should be Assert"),
        }

        // 5-6: Comments for postcondition assertions
        match &assertions[5] {
            ExecExpr::Comment(s) => {
                assert!(s.contains("result@.contains_key"));
            }
            _ => panic!("assertions[5] should be Comment"),
        }
        match &assertions[6] {
            ExecExpr::Comment(s) => {
                assert!(s.contains("votes@.contains_key"));
            }
            _ => panic!("assertions[6] should be Comment"),
        }
    }

    /// Test that demonstrates the full generated loop code structure.
    /// This test prints the generated code to help verify it matches
    /// the expected Verus pattern from CRemoveVotesBeforeLogTruncationPoint.
    #[test]
    fn test_generated_loop_code_output() {
        use crate::printer::Printer;

        let config = TranslatorConfig {
            generate_loops_for_verification: true,
            ..Default::default()
        };

        let translator = Translator::new(config);

        // Generate a map filter pattern similar to RemoveVotesBeforeLogTruncationPoint
        // Filter condition: *opn >= log_truncation_point
        let filter_expr = ExecExpr::Binary {
            lhs: Box::new(ExecExpr::Unary {
                op: "*".to_string(),
                expr: Box::new(ExecExpr::Var("opn".to_string())),
            }),
            op: ">=".to_string(),
            rhs: Box::new(ExecExpr::Var("log_truncation_point".to_string())),
        };

        let loop_expr = translator.generate_map_filter_loop("votes", "opn", filter_expr);

        // Print the generated code
        let mut printer = Printer::default();
        let code = printer.print_expr_to_string(&loop_expr);

        // Print for manual inspection (cargo test -- --nocapture)
        println!(
            "\n=== Generated Map Filter Loop ===\n{}\n=================================\n",
            code
        );

        // Verify key patterns are present in the output
        assert!(code.contains("broadcast use"), "Should have broadcast use");
        assert!(code.contains("votes.keys()"), "Should get keys from votes");
        assert!(
            code.contains("ghost mut seen_keys"),
            "Should have ghost variable"
        );
        assert!(
            code.contains("for opn in iter:"),
            "Should have for-in-iter loop"
        );
        assert!(code.contains("invariant"), "Should have invariants");
        assert!(
            code.contains("seen_keys.subset_of"),
            "Should have subset invariant"
        );
        assert!(code.contains("proof"), "Should have proof blocks");
        assert!(code.contains("votes.get"), "Should get value from votes");
        assert!(code.contains("result.insert"), "Should insert into result");
        assert!(
            code.contains("subset_len_equal_implies_equal"),
            "Should call lemma"
        );
    }

    #[test]
    fn test_expr_to_invariant_string_with_var() {
        let config = TranslatorConfig::default();
        let translator = Translator::new(config);

        // Test that only the loop variable gets dereferenced
        let var_loop = ExecExpr::Var("p".to_string());
        assert_eq!(
            translator.expr_to_invariant_string_with_var(&var_loop, "p"),
            "*p"
        );

        // Test that other variables don't get dereferenced
        let var_other = ExecExpr::Var("received_packet".to_string());
        assert_eq!(
            translator.expr_to_invariant_string_with_var(&var_other, "p"),
            "received_packet"
        );

        // Test field access
        let field = ExecExpr::Field(Box::new(ExecExpr::Var("p".to_string())), "src".to_string());
        assert_eq!(
            translator.expr_to_invariant_string_with_var(&field, "p"),
            "p.src"
        );

        // Test "is" expression - variant name should not be dereferenced
        let is_expr = ExecExpr::Binary {
            lhs: Box::new(ExecExpr::Var("io".to_string())),
            op: "is".to_string(),
            rhs: Box::new(ExecExpr::Var("Send".to_string())),
        };
        assert_eq!(
            translator.expr_to_invariant_string_with_var(&is_expr, "io"),
            "*io is Send"
        );

        // Test binary != with loop var and non-loop var
        let binary = ExecExpr::Binary {
            lhs: Box::new(ExecExpr::Field(
                Box::new(ExecExpr::Var("p".to_string())),
                "src".to_string(),
            )),
            op: "!=".to_string(),
            rhs: Box::new(ExecExpr::Field(
                Box::new(ExecExpr::Var("received_packet".to_string())),
                "src".to_string(),
            )),
        };
        assert_eq!(
            translator.expr_to_invariant_string_with_var(&binary, "p"),
            "p.src != received_packet.src"
        );
    }

    #[test]
    fn test_substitute_var_with_index() {
        let config = TranslatorConfig::default();
        let translator = Translator::new(config);

        // Basic substitution with dereference
        let pred = "*p is Send";
        let result = translator.substitute_var_with_index(pred, "p");
        assert_eq!(result, "p_iter@.1[i] is Send");

        // Multiple occurrences with dereference
        let pred2 = "*p.src != other && *p.valid";
        let result2 = translator.substitute_var_with_index(pred2, "p");
        assert_eq!(result2, "p_iter@.1[i].src != other && p_iter@.1[i].valid");

        // Field access without dereference (from stripped field access)
        let pred3 = "p.src != received_packet.src";
        let result3 = translator.substitute_var_with_index(pred3, "p");
        assert_eq!(result3, "p_iter@.1[i].src != received_packet.src");
    }

    #[test]
    fn test_generate_any_loop_has_proper_invariant() {
        let config = TranslatorConfig {
            generate_loops_for_verification: true,
            ..Default::default()
        };
        let translator = Translator::new(config);

        // Create a simple predicate: p.src != other.src
        let predicate = ExecExpr::Binary {
            lhs: Box::new(ExecExpr::Field(
                Box::new(ExecExpr::Var("p".to_string())),
                "src".to_string(),
            )),
            op: "!=".to_string(),
            rhs: Box::new(ExecExpr::Field(
                Box::new(ExecExpr::Var("other".to_string())),
                "src".to_string(),
            )),
        };

        let container = ExecExpr::Var("packets".to_string());
        let result = translator.generate_any_loop(container, "p", predicate);

        // Get the invariants from the generated loop
        if let ExecExpr::Block(stmts) = result {
            // Second statement should be ForInIter
            if let ExecExpr::ForInIter { invariants, .. } = &stmts[1] {
                assert_eq!(invariants.len(), 1, "Should have 1 invariant");
                // Invariant should reference p_iter@.1[i], not *p
                assert!(
                    invariants[0].contains("p_iter@.1[i].src"),
                    "Invariant should use indexed access: {}",
                    invariants[0]
                );
                assert!(
                    invariants[0].contains("other.src"),
                    "Invariant should keep other.src as is: {}",
                    invariants[0]
                );
            } else {
                panic!("Expected ForInIter");
            }
        } else {
            panic!("Expected Block");
        }
    }

    #[test]
    fn test_generate_all_loop_has_proper_invariant() {
        let config = TranslatorConfig {
            generate_loops_for_verification: true,
            ..Default::default()
        };
        let translator = Translator::new(config);

        // Create a simple predicate: io is Send
        let predicate = ExecExpr::Binary {
            lhs: Box::new(ExecExpr::Var("io".to_string())),
            op: "is".to_string(),
            rhs: Box::new(ExecExpr::Var("Send".to_string())),
        };

        let container = ExecExpr::Var("ios".to_string());
        let result = translator.generate_all_loop(container, "io", predicate);

        // Get the invariants from the generated loop
        if let ExecExpr::Block(stmts) = result {
            // Second statement should be ForInIter
            if let ExecExpr::ForInIter { invariants, .. } = &stmts[1] {
                assert_eq!(invariants.len(), 1, "Should have 1 invariant");
                // Invariant should reference io_iter@.1[i], not *io
                assert!(
                    invariants[0].contains("io_iter@.1[i]"),
                    "Invariant should use indexed access: {}",
                    invariants[0]
                );
                // Variant name Send should not have a *
                assert!(
                    invariants[0].contains("is Send"),
                    "Variant name should not be dereferenced: {}",
                    invariants[0]
                );
                assert!(
                    !invariants[0].contains("is *Send"),
                    "Variant name should not have *: {}",
                    invariants[0]
                );
            } else {
                panic!("Expected ForInIter");
            }
        } else {
            panic!("Expected Block");
        }
    }

    #[test]
    fn test_expr_to_invariant_string_if_expression() {
        let config = TranslatorConfig::default();
        let translator = Translator::new(config);

        // Test if-then-else expression
        let if_expr = ExecExpr::If {
            cond: Box::new(ExecExpr::Binary {
                lhs: Box::new(ExecExpr::Var("x".to_string())),
                op: ">".to_string(),
                rhs: Box::new(ExecExpr::Literal("0".to_string())),
            }),
            then_branch: Box::new(ExecExpr::Literal("true".to_string())),
            else_branch: Some(Box::new(ExecExpr::Literal("false".to_string()))),
        };
        let result = translator.expr_to_invariant_string_with_var(&if_expr, "x");
        assert_eq!(result, "if *x > 0 { true } else { false }");
    }

    #[test]
    fn test_expr_to_invariant_string_struct() {
        let config = TranslatorConfig::default();
        let translator = Translator::new(config);

        // Test struct expression
        let struct_expr = ExecExpr::Struct {
            name: "Point".to_string(),
            fields: vec![
                ("x".to_string(), ExecExpr::Literal("1".to_string())),
                ("y".to_string(), ExecExpr::Literal("2".to_string())),
            ],
        };
        let result = translator.expr_to_invariant_string_with_var(&struct_expr, "p");
        assert_eq!(result, "Point { x: 1, y: 2 }");
    }

    #[test]
    fn test_expr_to_invariant_string_tuple() {
        let config = TranslatorConfig::default();
        let translator = Translator::new(config);

        // Test tuple expression
        let tuple_expr = ExecExpr::Tuple(vec![
            ExecExpr::Literal("1".to_string()),
            ExecExpr::Literal("2".to_string()),
        ]);
        let result = translator.expr_to_invariant_string_with_var(&tuple_expr, "x");
        assert_eq!(result, "(1, 2)");
    }

    #[test]
    fn test_expr_to_invariant_string_clone() {
        let config = TranslatorConfig::default();
        let translator = Translator::new(config);

        // Test clone expression - should just return the inner value
        let clone_expr = ExecExpr::Clone(Box::new(ExecExpr::Var("s".to_string())));
        let result = translator.expr_to_invariant_string_with_var(&clone_expr, "x");
        assert_eq!(result, "s");
    }

    #[test]
    fn test_expr_to_invariant_string_vec_lit() {
        let config = TranslatorConfig::default();
        let translator = Translator::new(config);

        // Test vec literal expression - should become seq![]
        let vec_expr = ExecExpr::VecLit(vec![
            ExecExpr::Literal("1".to_string()),
            ExecExpr::Literal("2".to_string()),
        ]);
        let result = translator.expr_to_invariant_string_with_var(&vec_expr, "x");
        assert_eq!(result, "seq![1, 2]");
    }

    #[test]
    fn test_translate_type_string_simple() {
        let translator = Translator::default();

        // Simple type
        assert!(matches!(
            translator.translate_type_string("Ballot"),
            ExecType::Named(n) if n == "CBallot"
        ));

        // Primitive types
        assert!(matches!(
            translator.translate_type_string("bool"),
            ExecType::Named(n) if n == "bool"
        ));
        assert!(matches!(
            translator.translate_type_string("int"),
            ExecType::Named(n) if n == "i64"
        ));
        assert!(matches!(
            translator.translate_type_string("nat"),
            ExecType::Named(n) if n == "u64"
        ));
    }

    #[test]
    fn test_translate_type_string_generic() {
        let translator = Translator::default();

        // Seq<Request> -> Vec<CRequest>
        let seq_type = translator.translate_type_string("Seq<Request>");
        assert!(matches!(seq_type, ExecType::Vec(_)));

        // Set<int> -> HashSet<i64>
        let set_type = translator.translate_type_string("Set<int>");
        match set_type {
            ExecType::Generic(name, args) => {
                assert_eq!(name, "HashSet");
                assert_eq!(args.len(), 1);
            }
            _ => panic!("Expected Generic type for Set<int>"),
        }
    }

    #[test]
    fn test_translate_helper_simple() {
        use crate::ast::{Generics, Parameter, Path};

        let translator = Translator::default();

        // Create a simple helper function: ComputeSuccessorView(b: Ballot, c: LConstants) -> Ballot
        let spec_fn = crate::ast::SpecFunction {
            name: "ComputeSuccessorView".to_string(),
            generics: Generics::default(),
            params: vec![
                Parameter {
                    name: "b".to_string(),
                    ty: Type::Named(Path::single("Ballot".to_string())),
                    mode: None,
                    variable_mode: crate::ast::VariableMode::Exec,
                    span: None,
                },
                Parameter {
                    name: "c".to_string(),
                    ty: Type::Named(Path::single("LConstants".to_string())),
                    mode: None,
                    variable_mode: crate::ast::VariableMode::Exec,
                    span: None,
                },
            ],
            return_type: Type::Named(Path::single("Ballot".to_string())),
            requires: vec![],
            ensures: vec![],
            recommends: vec![],
            decreases: vec![],
            body: Expr::Struct {
                name: Path::single("Ballot".to_string()),
                fields: vec![
                    ("seqno".to_string(), Expr::Literal(Literal::Int(0))),
                    ("proposer_id".to_string(), Expr::Literal(Literal::Int(0))),
                ],
            },
            span: None,
        };

        let annotated = crate::moder::AnnotatedFunction {
            spec_fn,
            kind: FunctionKind::Helper,
            param_modes: vec![ParameterMode::Input, ParameterMode::Input],
            return_type: Some("Ballot".to_string()),
            is_recursive: false,
            is_functionalizable: true,
            non_functionalizable_reason: None,
        };

        let result = translator.translate(&annotated).unwrap();

        // Check function name
        assert_eq!(result.name, "CComputeSuccessorView");

        // All parameters should be inputs (references)
        assert_eq!(result.params.len(), 2);
        for param in &result.params {
            assert!(param.is_reference);
        }

        // Return type should be CBallot
        assert!(matches!(&result.return_type, ExecType::Named(n) if n == "CBallot"));

        // Requires should include validity checks
        // Default validity predicate is "well_formed"
        assert!(result
            .requires
            .iter()
            .any(|r| r.contains("b.well_formed()")));
        assert!(result
            .requires
            .iter()
            .any(|r| r.contains("c.well_formed()")));

        // Ensures should include result.valid() and spec linkage
        // Default validity predicate is "well_formed"
        assert!(result
            .ensures
            .iter()
            .any(|e| e.contains("result.well_formed()")));
        assert!(result
            .ensures
            .iter()
            .any(|e| e.contains("result@ == ComputeSuccessorView(b@, c@)")));
    }

    #[test]
    fn test_translate_helper_bool_return() {
        use crate::ast::{Generics, Parameter, Path};

        let translator = Translator::default();

        // Create a helper function returning bool: RequestsMatch(a, b) -> bool
        let spec_fn = crate::ast::SpecFunction {
            name: "RequestsMatch".to_string(),
            generics: Generics::default(),
            params: vec![
                Parameter {
                    name: "a".to_string(),
                    ty: Type::Named(Path::single("Request".to_string())),
                    mode: None,
                    variable_mode: crate::ast::VariableMode::Exec,
                    span: None,
                },
                Parameter {
                    name: "b".to_string(),
                    ty: Type::Named(Path::single("Request".to_string())),
                    mode: None,
                    variable_mode: crate::ast::VariableMode::Exec,
                    span: None,
                },
            ],
            return_type: Type::Bool,
            requires: vec![],
            ensures: vec![],
            recommends: vec![],
            decreases: vec![],
            body: Expr::Literal(Literal::Bool(true)),
            span: None,
        };

        let annotated = crate::moder::AnnotatedFunction {
            spec_fn,
            kind: FunctionKind::Helper,
            param_modes: vec![ParameterMode::Input, ParameterMode::Input],
            return_type: Some("bool".to_string()),
            is_recursive: false,
            is_functionalizable: true,
            non_functionalizable_reason: None,
        };

        let result = translator.translate(&annotated).unwrap();

        // Return type should be bool
        assert!(matches!(&result.return_type, ExecType::Named(n) if n == "bool"));

        // For bool return, no result.valid() should be generated
        // For bool return, no result.well_formed() should be generated
        assert!(!result
            .ensures
            .iter()
            .any(|e| e.contains("result.well_formed()")));

        // But spec linkage should still be present
        assert!(result
            .ensures
            .iter()
            .any(|e| e.contains("result@ == RequestsMatch(a@, b@)")));
    }

    #[test]
    fn test_translate_helper_seq_return() {
        use crate::ast::{Generics, Parameter, Path};

        let translator = Translator::default();

        // Create a helper function returning Seq<Request>
        let spec_fn = crate::ast::SpecFunction {
            name: "BoundRequestSequence".to_string(),
            generics: Generics::default(),
            params: vec![
                Parameter {
                    name: "s".to_string(),
                    ty: Type::Seq(Box::new(Type::Named(Path::single("Request".to_string())))),
                    mode: None,
                    variable_mode: crate::ast::VariableMode::Exec,
                    span: None,
                },
                Parameter {
                    name: "bound".to_string(),
                    ty: Type::Named(Path::single("UpperBound".to_string())),
                    mode: None,
                    variable_mode: crate::ast::VariableMode::Exec,
                    span: None,
                },
            ],
            return_type: Type::Seq(Box::new(Type::Named(Path::single("Request".to_string())))),
            requires: vec![],
            ensures: vec![],
            recommends: vec![],
            decreases: vec![],
            body: Expr::Ident("s".to_string()),
            span: None,
        };

        let annotated = crate::moder::AnnotatedFunction {
            spec_fn,
            kind: FunctionKind::Helper,
            param_modes: vec![ParameterMode::Input, ParameterMode::Input],
            return_type: Some("Seq<Request>".to_string()),
            is_recursive: false,
            is_functionalizable: true,
            non_functionalizable_reason: None,
        };

        let result = translator.translate(&annotated).unwrap();

        // Return type should be Vec<CRequest>
        assert!(matches!(&result.return_type, ExecType::Vec(_)));

        // Check spec linkage
        assert!(result
            .ensures
            .iter()
            .any(|e| e.contains("result@ == BoundRequestSequence(s@, bound@)")));
    }

    #[test]
    fn test_build_helper_spec_call() {
        use crate::ast::{Generics, Parameter, Path};

        let translator = Translator::default();

        let spec_fn = crate::ast::SpecFunction {
            name: "MyHelper".to_string(),
            generics: Generics::default(),
            params: vec![
                Parameter {
                    name: "a".to_string(),
                    ty: Type::Named(Path::single("TypeA".to_string())),
                    mode: None,
                    variable_mode: crate::ast::VariableMode::Exec,
                    span: None,
                },
                Parameter {
                    name: "b".to_string(),
                    ty: Type::Named(Path::single("TypeB".to_string())),
                    mode: None,
                    variable_mode: crate::ast::VariableMode::Exec,
                    span: None,
                },
                Parameter {
                    name: "c".to_string(),
                    ty: Type::Named(Path::single("TypeC".to_string())),
                    mode: None,
                    variable_mode: crate::ast::VariableMode::Exec,
                    span: None,
                },
            ],
            return_type: Type::Named(Path::single("Result".to_string())),
            requires: vec![],
            ensures: vec![],
            recommends: vec![],
            decreases: vec![],
            body: Expr::Literal(Literal::Bool(true)),
            span: None,
        };

        let annotated = crate::moder::AnnotatedFunction {
            spec_fn,
            kind: FunctionKind::Helper,
            param_modes: vec![
                ParameterMode::Input,
                ParameterMode::Input,
                ParameterMode::Input,
            ],
            return_type: Some("Result".to_string()),
            is_recursive: false,
            is_functionalizable: true,
            non_functionalizable_reason: None,
        };

        let spec_call = translator.build_helper_spec_call(&annotated);
        assert_eq!(spec_call, "result@ == MyHelper(a@, b@, c@)");
    }

    #[test]
    fn test_recursive_function_rejected() {
        use crate::ast::{Generics, Parameter, Path};

        let translator = Translator::default();

        // Create a recursive function
        let spec_fn = crate::ast::SpecFunction {
            name: "RecursiveFunc".to_string(),
            generics: Generics::default(),
            params: vec![Parameter {
                name: "s".to_string(),
                ty: Type::Seq(Box::new(Type::Named(Path::single("Request".to_string())))),
                mode: None,
                variable_mode: crate::ast::VariableMode::Exec,
                span: None,
            }],
            return_type: Type::Seq(Box::new(Type::Named(Path::single("Request".to_string())))),
            requires: vec![],
            ensures: vec![],
            recommends: vec![],
            decreases: vec![Expr::MethodCall {
                receiver: Box::new(Expr::Ident("s".to_string())),
                method: "len".to_string(),
                args: vec![],
            }],
            body: Expr::Ident("s".to_string()),
            span: None,
        };

        let annotated = crate::moder::AnnotatedFunction {
            spec_fn,
            kind: FunctionKind::Helper,
            param_modes: vec![ParameterMode::Input],
            return_type: Some("Seq<Request>".to_string()),
            is_recursive: true, // Mark as recursive
            is_functionalizable: true,
            non_functionalizable_reason: None,
        };

        let result = translator.translate(&annotated);
        assert!(result.is_err());
        let err = result.unwrap_err();
        let msg = format!("{}", err);
        assert!(msg.contains("recursive"));
        assert!(msg.contains("cannot be automatically translated"));
    }
}
