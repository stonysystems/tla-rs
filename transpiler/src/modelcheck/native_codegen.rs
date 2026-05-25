//! Native Rust source code generator for spec expressions.
//!
//! Translates `Expr` AST nodes into Rust source code strings that operate on
//! `RuntimeValue` values directly, avoiding AST interpretation overhead.
//! This is the first stage of the native codegen pipeline (Phase 38.22.1.c).
//!
//! The generated code is intended to be compiled to a shared library and
//! loaded at runtime for ~100-200x speedup over AST interpretation.

use std::collections::HashMap;
use std::fmt::Write;

use crate::ast::{BinOp, Expr, Literal, UnaryOp};
/// Context for code generation, tracking variable name → Rust expression mappings.
#[derive(Debug, Clone)]
pub struct CodegenCtx {
    /// Maps spec variable names to Rust expression strings (e.g., "s" → "env[0]")
    pub locals: HashMap<String, String>,
    /// Counter for generating unique temporary variable names
    tmp_counter: usize,
}

impl CodegenCtx {
    pub fn new(env_names: &[String]) -> Self {
        let mut locals = HashMap::new();
        for (i, name) in env_names.iter().enumerate() {
            locals.insert(name.clone(), format!("env[{}]", i));
        }
        CodegenCtx {
            locals,
            tmp_counter: 0,
        }
    }

    fn fresh_tmp(&mut self) -> String {
        let name = format!("_t{}", self.tmp_counter);
        self.tmp_counter += 1;
        name
    }

    fn with_local(&self, name: &str, expr: &str) -> Self {
        let mut ctx = self.clone();
        ctx.locals.insert(name.to_string(), expr.to_string());
        ctx
    }
}

/// Error returned when an expression cannot be translated to Rust source.
#[derive(Debug)]
pub struct CodegenError {
    pub message: String,
}

impl std::fmt::Display for CodegenError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "native codegen: {}", self.message)
    }
}

impl std::error::Error for CodegenError {}

type CodegenResult<T> = Result<T, CodegenError>;

fn codegen_err(msg: &str) -> CodegenError {
    CodegenError {
        message: msg.to_string(),
    }
}

/// Translate an `Expr` into a Rust source expression string that evaluates
/// to `TranspileResult<RuntimeValue>`.
///
/// The generated code assumes these are in scope:
/// - `env: &[RuntimeValue]` — environment variables by index
/// - `RuntimeValue`, `NamedFields`, `Symbol`, etc. from the runtime
/// - Helper functions: `rt_field`, `rt_index`, `rt_binop`, etc.
pub fn expr_to_rust(expr: &Expr, ctx: &mut CodegenCtx) -> CodegenResult<String> {
    match expr {
        Expr::ConstantValue(v) => Ok(format!("Ok(CONSTANTS[{}].clone())", const_placeholder(v))),

        Expr::Literal(lit) => match lit {
            Literal::Bool(b) => Ok(format!("Ok(RuntimeValue::Bool({}))", b)),
            Literal::Int(n) => Ok(format!("Ok(RuntimeValue::Int({}))", n)),
            Literal::String(s) => Ok(format!("Ok(RuntimeValue::String({:?}.to_string()))", s)),
        },

        Expr::Ident(name) => {
            if let Some(rust_expr) = ctx.locals.get(name) {
                Ok(format!("Ok({}.clone())", rust_expr))
            } else if let Some((ty, variant)) = split_variant_path(name) {
                Ok(format!(
                    "RuntimeValue::enum_value({:?}, {:?}, Vec::new())",
                    ty, variant
                ))
            } else {
                Err(codegen_err(&format!("unknown variable `{}`", name)))
            }
        }

        Expr::Field(base, field) | Expr::Arrow(base, field) => {
            let base_code = expr_to_rust_val(base, ctx)?;
            Ok(format!("rt_field(&{}, {:?})", base_code, field))
        }

        Expr::Index(base, idx) => {
            let base_code = expr_to_rust_val(base, ctx)?;
            let idx_code = expr_to_rust_val(idx, ctx)?;
            Ok(format!("rt_index(&{}, &{})", base_code, idx_code))
        }

        Expr::Eq(lhs, rhs) => {
            let l = expr_to_rust_val(lhs, ctx)?;
            let r = expr_to_rust_val(rhs, ctx)?;
            Ok(format!("Ok(RuntimeValue::Bool({} == {}))", l, r))
        }

        Expr::Ne(lhs, rhs) => {
            let l = expr_to_rust_val(lhs, ctx)?;
            let r = expr_to_rust_val(rhs, ctx)?;
            Ok(format!("Ok(RuntimeValue::Bool({} != {}))", l, r))
        }

        Expr::Lt(lhs, rhs) => cmp_expr(lhs, rhs, "<", ctx),
        Expr::Le(lhs, rhs) => cmp_expr(lhs, rhs, "<=", ctx),
        Expr::Gt(lhs, rhs) => cmp_expr(lhs, rhs, ">", ctx),
        Expr::Ge(lhs, rhs) => cmp_expr(lhs, rhs, ">=", ctx),

        Expr::Not(inner) => {
            let inner_code = expr_to_rust_val(inner, ctx)?;
            Ok(format!(
                "Ok(RuntimeValue::Bool(!rt_expect_bool(&{})?))",
                inner_code
            ))
        }

        Expr::Conjunction(items) => {
            if items.is_empty() {
                return Ok("Ok(RuntimeValue::Bool(true))".to_string());
            }
            let mut parts = Vec::new();
            for item in items {
                parts.push(expr_to_rust_val(item, ctx)?);
            }
            // Short-circuit conjunction
            let mut code = String::new();
            write!(code, "{{ let mut _conj = true; ").unwrap();
            for (i, part) in parts.iter().enumerate() {
                // Use a block to compute each part only if still true
                if i == 0 {
                    write!(
                        code,
                        "let _c{} = {}; _conj = rt_expect_bool(&_c{})?; ",
                        i, part, i
                    )
                    .unwrap();
                } else {
                    write!(
                        code,
                        "if _conj {{ let _c{} = {}; _conj = rt_expect_bool(&_c{})?; }} ",
                        i, part, i
                    )
                    .unwrap();
                }
            }
            write!(code, "Ok(RuntimeValue::Bool(_conj)) }}").unwrap();
            Ok(code)
        }

        Expr::Disjunction(items) => {
            if items.is_empty() {
                return Ok("Ok(RuntimeValue::Bool(false))".to_string());
            }
            let mut parts = Vec::new();
            for item in items {
                parts.push(expr_to_rust_val(item, ctx)?);
            }
            let mut code = String::new();
            write!(code, "{{ let mut _disj = false; ").unwrap();
            for (i, part) in parts.iter().enumerate() {
                if i == 0 {
                    write!(
                        code,
                        "let _d{} = {}; _disj = rt_expect_bool(&_d{})?; ",
                        i, part, i
                    )
                    .unwrap();
                } else {
                    write!(
                        code,
                        "if !_disj {{ let _d{} = {}; _disj = rt_expect_bool(&_d{})?; }} ",
                        i, part, i
                    )
                    .unwrap();
                }
            }
            write!(code, "Ok(RuntimeValue::Bool(_disj)) }}").unwrap();
            Ok(code)
        }

        Expr::Implies(lhs, rhs) => {
            let l = expr_to_rust_val(lhs, ctx)?;
            let r = expr_to_rust_val(rhs, ctx)?;
            Ok(format!(
                "{{ let _ant = {}; if !rt_expect_bool(&_ant)? {{ Ok(RuntimeValue::Bool(true)) }} else {{ let _con = {}; Ok(RuntimeValue::Bool(rt_expect_bool(&_con)?)) }} }}",
                l, r
            ))
        }

        Expr::Iff(lhs, rhs) => {
            let l = expr_to_rust_val(lhs, ctx)?;
            let r = expr_to_rust_val(rhs, ctx)?;
            Ok(format!(
                "Ok(RuntimeValue::Bool(rt_expect_bool(&{})? == rt_expect_bool(&{})?))",
                l, r
            ))
        }

        Expr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            let cond_code = expr_to_rust_val(cond, ctx)?;
            let then_code = expr_to_rust(then_branch, ctx)?;
            let else_code = match else_branch {
                Some(e) => expr_to_rust(e, ctx)?,
                None => "Ok(RuntimeValue::Unit)".to_string(),
            };
            Ok(format!(
                "if rt_expect_bool(&{})? {{ {} }} else {{ {} }}",
                cond_code, then_code, else_code
            ))
        }

        Expr::Binary(lhs, op, rhs) => {
            // Short-circuit for And/Or
            match op {
                BinOp::And => {
                    let l = expr_to_rust_val(lhs, ctx)?;
                    let r = expr_to_rust_val(rhs, ctx)?;
                    return Ok(format!(
                        "{{ let _l = {}; if _l == RuntimeValue::Bool(false) {{ Ok(RuntimeValue::Bool(false)) }} else {{ let _r = {}; rt_binop(&_l, BinOp::And, &_r) }} }}",
                        l, r
                    ));
                }
                BinOp::Or => {
                    let l = expr_to_rust_val(lhs, ctx)?;
                    let r = expr_to_rust_val(rhs, ctx)?;
                    return Ok(format!(
                        "{{ let _l = {}; if _l == RuntimeValue::Bool(true) {{ Ok(RuntimeValue::Bool(true)) }} else {{ let _r = {}; rt_binop(&_l, BinOp::Or, &_r) }} }}",
                        l, r
                    ));
                }
                _ => {}
            }
            let l = expr_to_rust_val(lhs, ctx)?;
            let r = expr_to_rust_val(rhs, ctx)?;
            let op_str = binop_to_str(*op);
            Ok(format!("rt_binop(&{}, BinOp::{}, &{})", l, op_str, r))
        }

        Expr::Unary(op, inner) => {
            let inner_code = expr_to_rust_val(inner, ctx)?;
            match op {
                UnaryOp::Not => Ok(format!(
                    "Ok(RuntimeValue::Bool(!rt_expect_bool(&{})?))",
                    inner_code
                )),
                UnaryOp::Neg => Ok(format!("rt_negate(&{})", inner_code)),
                UnaryOp::Deref => Ok(format!("Ok({}.clone())", inner_code)),
            }
        }

        Expr::Is(base, variant) => {
            let base_code = expr_to_rust_val(base, ctx)?;
            Ok(format!(
                "Ok(RuntimeValue::Bool(rt_is_variant(&{}, {:?})))",
                base_code, variant
            ))
        }

        Expr::SetLit(items) => collection_lit(items, "set_bounded", ctx),
        Expr::SeqLit(items) => collection_lit(items, "seq_bounded", ctx),
        Expr::SetEmpty => Ok("RuntimeValue::set_bounded(Vec::new(), &BOUNDS)".to_string()),
        Expr::SeqEmpty => Ok("RuntimeValue::seq_bounded(Vec::new(), &BOUNDS)".to_string()),
        Expr::MapEmpty => Ok("RuntimeValue::map_bounded(Vec::new(), &BOUNDS)".to_string()),

        Expr::MapLit(entries) => {
            let mut parts = Vec::new();
            for (k, v) in entries {
                let kc = expr_to_rust_val(k, ctx)?;
                let vc = expr_to_rust_val(v, ctx)?;
                parts.push(format!("({}, {})", kc, vc));
            }
            Ok(format!(
                "RuntimeValue::map_bounded(vec![{}], &BOUNDS)",
                parts.join(", ")
            ))
        }

        Expr::View(inner) => expr_to_rust(inner, ctx),
        Expr::Cast(inner, _ty) => expr_to_rust(inner, ctx),

        Expr::Let {
            binding,
            value,
            body,
        } => {
            let val_code = expr_to_rust_val(value, ctx)?;
            let name = match &binding.pattern {
                crate::ast::Pattern::Ident(n) => n.clone(),
                _ => return Err(codegen_err("non-identifier let binding")),
            };
            let tmp = ctx.fresh_tmp();
            let mut inner_ctx = ctx.with_local(&name, &tmp);
            let body_code = expr_to_rust(body, &mut inner_ctx)?;
            Ok(format!("{{ let {} = {}; {} }}", tmp, val_code, body_code))
        }

        // Expressions that need Phase 38.22.1.c.ii (quantifiers, struct, method calls)
        Expr::Struct { .. }
        | Expr::StructUpdate { .. }
        | Expr::MethodCall { .. }
        | Expr::Call { .. }
        | Expr::Forall { .. }
        | Expr::Exists { .. }
        | Expr::Choose { .. }
        | Expr::Match { .. }
        | Expr::Closure { .. } => Err(codegen_err(&format!(
            "unsupported expression type: {}",
            expr_type_name(expr)
        ))),
    }
}

/// Like `expr_to_rust`, but unwraps the Result — generates code that produces
/// a `RuntimeValue` directly (using `?` for error propagation).
fn expr_to_rust_val(expr: &Expr, ctx: &mut CodegenCtx) -> CodegenResult<String> {
    let code = expr_to_rust(expr, ctx)?;
    // If the code is already a simple Ok(...) wrapper, unwrap it
    if let Some(inner) = code.strip_prefix("Ok(").and_then(|s| s.strip_suffix(')')) {
        // Only unwrap simple cases (no nested Ok/Err)
        if !inner.contains("Ok(") && !inner.contains("Err(") {
            return Ok(inner.to_string());
        }
    }
    // Otherwise, wrap with ? operator
    let tmp = ctx.fresh_tmp();
    Ok(format!("{{ let {} = ({})?; {} }}", tmp, code, tmp))
}

fn cmp_expr(lhs: &Expr, rhs: &Expr, op: &str, ctx: &mut CodegenCtx) -> CodegenResult<String> {
    let l = expr_to_rust_val(lhs, ctx)?;
    let r = expr_to_rust_val(rhs, ctx)?;
    Ok(format!(
        "Ok(RuntimeValue::Bool(rt_expect_int(&{})? {} rt_expect_int(&{})?))",
        l, op, r
    ))
}

fn collection_lit(items: &[Expr], method: &str, ctx: &mut CodegenCtx) -> CodegenResult<String> {
    let mut parts = Vec::new();
    for item in items {
        parts.push(expr_to_rust_val(item, ctx)?);
    }
    Ok(format!(
        "RuntimeValue::{}(vec![{}], &BOUNDS)",
        method,
        parts.join(", ")
    ))
}

fn binop_to_str(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => "Add",
        BinOp::Sub => "Sub",
        BinOp::Mul => "Mul",
        BinOp::Div => "Div",
        BinOp::Mod => "Mod",
        BinOp::And => "And",
        BinOp::Or => "Or",
        BinOp::BitAnd => "BitAnd",
        BinOp::BitOr => "BitOr",
        BinOp::BitXor => "BitXor",
        BinOp::Shl => "Shl",
        BinOp::Shr => "Shr",
    }
}

fn expr_type_name(expr: &Expr) -> &'static str {
    match expr {
        Expr::Conjunction(_) => "Conjunction",
        Expr::Disjunction(_) => "Disjunction",
        Expr::Implies(_, _) => "Implies",
        Expr::Iff(_, _) => "Iff",
        Expr::Not(_) => "Not",
        Expr::Forall { .. } => "Forall",
        Expr::Exists { .. } => "Exists",
        Expr::Closure { .. } => "Closure",
        Expr::Choose { .. } => "Choose",
        Expr::If { .. } => "If",
        Expr::Match { .. } => "Match",
        Expr::Let { .. } => "Let",
        Expr::Eq(_, _) => "Eq",
        Expr::Ne(_, _) => "Ne",
        Expr::Lt(_, _) => "Lt",
        Expr::Le(_, _) => "Le",
        Expr::Gt(_, _) => "Gt",
        Expr::Ge(_, _) => "Ge",
        Expr::Is(_, _) => "Is",
        Expr::Field(_, _) => "Field",
        Expr::Index(_, _) => "Index",
        Expr::Arrow(_, _) => "Arrow",
        Expr::Struct { .. } => "Struct",
        Expr::StructUpdate { .. } => "StructUpdate",
        Expr::SeqLit(_) => "SeqLit",
        Expr::SetLit(_) => "SetLit",
        Expr::MapLit(_) => "MapLit",
        Expr::SeqEmpty => "SeqEmpty",
        Expr::SetEmpty => "SetEmpty",
        Expr::MapEmpty => "MapEmpty",
        Expr::Call { .. } => "Call",
        Expr::MethodCall { .. } => "MethodCall",
        Expr::View(_) => "View",
        Expr::Cast(_, _) => "Cast",
        Expr::Ident(_) => "Ident",
        Expr::Literal(_) => "Literal",
        Expr::Binary(_, _, _) => "Binary",
        Expr::Unary(_, _) => "Unary",
        Expr::ConstantValue(_) => "ConstantValue",
    }
}

/// Check if a name like "LTPCMessage::Prepare" is an enum variant path.
fn split_variant_path(name: &str) -> Option<(&str, &str)> {
    let idx = name.find("::")?;
    let ty = &name[..idx];
    let variant = &name[idx + 2..];
    if ty.is_empty() || variant.is_empty() {
        return None;
    }
    Some((ty, variant))
}

/// Placeholder for constant values — in the final codegen, these will be
/// indices into a constants table passed to the compiled function.
fn const_placeholder(v: &crate::modelcheck::value::RuntimeValue) -> String {
    // For now, use a hash-based identifier. The actual integration (38.22.1.c.v)
    // will replace this with a proper constants table index.
    format!("/*const:{:?}*/0", v.fingerprint())
}

/// Generate a complete Rust function body for evaluating an expression.
/// Returns the function source code as a string, or an error if the expression
/// contains unsupported constructs.
///
/// The generated function has the signature:
/// ```ignore
/// fn eval(env: &[RuntimeValue]) -> TranspileResult<RuntimeValue>
/// ```
pub fn generate_eval_function(expr: &Expr, env_names: &[String]) -> CodegenResult<String> {
    let mut ctx = CodegenCtx::new(env_names);
    let body = expr_to_rust(expr, &mut ctx)?;
    Ok(format!(
        "fn eval(env: &[RuntimeValue]) -> TranspileResult<RuntimeValue> {{\n    {}\n}}",
        body
    ))
}

/// Check whether an expression can be fully translated to native Rust.
/// Returns `Ok(())` if all sub-expressions are supported, or `Err` with
/// the first unsupported construct found.
pub fn check_codegen_support(expr: &Expr) -> CodegenResult<()> {
    let mut ctx = CodegenCtx::new(&[]);
    // Add a dummy binding for any ident we encounter
    ctx.locals.insert("_".to_string(), "env[0]".to_string());
    match check_support_recursive(expr) {
        Ok(()) => Ok(()),
        Err(e) => Err(e),
    }
}

fn check_support_recursive(expr: &Expr) -> CodegenResult<()> {
    match expr {
        Expr::ConstantValue(_)
        | Expr::Literal(_)
        | Expr::Ident(_)
        | Expr::SetEmpty
        | Expr::SeqEmpty
        | Expr::MapEmpty => Ok(()),

        Expr::Field(base, _)
        | Expr::Arrow(base, _)
        | Expr::Not(base)
        | Expr::View(base)
        | Expr::Cast(base, _)
        | Expr::Unary(_, base) => check_support_recursive(base),

        Expr::Eq(l, r)
        | Expr::Ne(l, r)
        | Expr::Lt(l, r)
        | Expr::Le(l, r)
        | Expr::Gt(l, r)
        | Expr::Ge(l, r)
        | Expr::Binary(l, _, r)
        | Expr::Implies(l, r)
        | Expr::Iff(l, r) => {
            check_support_recursive(l)?;
            check_support_recursive(r)
        }

        Expr::Index(base, idx) => {
            check_support_recursive(base)?;
            check_support_recursive(idx)
        }

        Expr::Conjunction(items)
        | Expr::Disjunction(items)
        | Expr::SetLit(items)
        | Expr::SeqLit(items) => {
            for item in items {
                check_support_recursive(item)?;
            }
            Ok(())
        }

        Expr::MapLit(entries) => {
            for (k, v) in entries {
                check_support_recursive(k)?;
                check_support_recursive(v)?;
            }
            Ok(())
        }

        Expr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            check_support_recursive(cond)?;
            check_support_recursive(then_branch)?;
            if let Some(e) = else_branch {
                check_support_recursive(e)?;
            }
            Ok(())
        }

        Expr::Is(base, _) => check_support_recursive(base),

        Expr::Let {
            value,
            body,
            binding,
        } => {
            match &binding.pattern {
                crate::ast::Pattern::Ident(_) => {}
                _ => return Err(codegen_err("non-identifier let binding")),
            }
            check_support_recursive(value)?;
            check_support_recursive(body)
        }

        // Unsupported in Phase 38.22.1.c.i
        Expr::Struct { .. }
        | Expr::StructUpdate { .. }
        | Expr::MethodCall { .. }
        | Expr::Call { .. }
        | Expr::Forall { .. }
        | Expr::Exists { .. }
        | Expr::Choose { .. }
        | Expr::Match { .. }
        | Expr::Closure { .. } => Err(codegen_err(&format!(
            "unsupported: {}",
            expr_type_name(expr)
        ))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Binding, Literal, Pattern, VariableMode};

    #[test]
    fn test_literal_int() {
        let expr = Expr::Literal(Literal::Int(42));
        let mut ctx = CodegenCtx::new(&[]);
        let code = expr_to_rust(&expr, &mut ctx).unwrap();
        assert!(code.contains("42"), "code should contain 42: {}", code);
        assert!(code.contains("RuntimeValue::Int"), "code: {}", code);
    }

    #[test]
    fn test_literal_bool() {
        let expr = Expr::Literal(Literal::Bool(true));
        let mut ctx = CodegenCtx::new(&[]);
        let code = expr_to_rust(&expr, &mut ctx).unwrap();
        assert!(code.contains("true"), "code: {}", code);
    }

    #[test]
    fn test_literal_string() {
        let expr = Expr::Literal(Literal::String("hello".to_string()));
        let mut ctx = CodegenCtx::new(&[]);
        let code = expr_to_rust(&expr, &mut ctx).unwrap();
        assert!(code.contains("hello"), "code: {}", code);
    }

    #[test]
    fn test_ident_from_env() {
        let names = vec!["x".to_string()];
        let mut ctx = CodegenCtx::new(&names);
        let expr = Expr::Ident("x".to_string());
        let code = expr_to_rust(&expr, &mut ctx).unwrap();
        assert!(code.contains("env[0]"), "code: {}", code);
    }

    #[test]
    fn test_ident_unknown_errors() {
        let mut ctx = CodegenCtx::new(&[]);
        let expr = Expr::Ident("unknown_var".to_string());
        let result = expr_to_rust(&expr, &mut ctx);
        assert!(result.is_err());
    }

    #[test]
    fn test_enum_variant_ident() {
        let mut ctx = CodegenCtx::new(&[]);
        let expr = Expr::Ident("MyEnum::Variant".to_string());
        let code = expr_to_rust(&expr, &mut ctx).unwrap();
        assert!(code.contains("enum_value"), "code: {}", code);
        assert!(code.contains("MyEnum"), "code: {}", code);
        assert!(code.contains("Variant"), "code: {}", code);
    }

    #[test]
    fn test_eq() {
        let expr = Expr::Eq(
            Box::new(Expr::Literal(Literal::Int(1))),
            Box::new(Expr::Literal(Literal::Int(2))),
        );
        let mut ctx = CodegenCtx::new(&[]);
        let code = expr_to_rust(&expr, &mut ctx).unwrap();
        assert!(code.contains("=="), "code: {}", code);
    }

    #[test]
    fn test_ne() {
        let expr = Expr::Ne(
            Box::new(Expr::Literal(Literal::Int(1))),
            Box::new(Expr::Literal(Literal::Int(2))),
        );
        let mut ctx = CodegenCtx::new(&[]);
        let code = expr_to_rust(&expr, &mut ctx).unwrap();
        assert!(code.contains("!="), "code: {}", code);
    }

    #[test]
    fn test_comparison_lt() {
        let expr = Expr::Lt(
            Box::new(Expr::Literal(Literal::Int(1))),
            Box::new(Expr::Literal(Literal::Int(2))),
        );
        let mut ctx = CodegenCtx::new(&[]);
        let code = expr_to_rust(&expr, &mut ctx).unwrap();
        assert!(code.contains("<"), "code: {}", code);
        assert!(code.contains("rt_expect_int"), "code: {}", code);
    }

    #[test]
    fn test_conjunction_short_circuit() {
        let expr = Expr::Conjunction(vec![
            Expr::Literal(Literal::Bool(true)),
            Expr::Literal(Literal::Bool(false)),
        ]);
        let mut ctx = CodegenCtx::new(&[]);
        let code = expr_to_rust(&expr, &mut ctx).unwrap();
        assert!(
            code.contains("_conj"),
            "should use short-circuit var: {}",
            code
        );
    }

    #[test]
    fn test_disjunction_short_circuit() {
        let expr = Expr::Disjunction(vec![
            Expr::Literal(Literal::Bool(false)),
            Expr::Literal(Literal::Bool(true)),
        ]);
        let mut ctx = CodegenCtx::new(&[]);
        let code = expr_to_rust(&expr, &mut ctx).unwrap();
        assert!(
            code.contains("_disj"),
            "should use short-circuit var: {}",
            code
        );
    }

    #[test]
    fn test_implies() {
        let expr = Expr::Implies(
            Box::new(Expr::Literal(Literal::Bool(true))),
            Box::new(Expr::Literal(Literal::Bool(false))),
        );
        let mut ctx = CodegenCtx::new(&[]);
        let code = expr_to_rust(&expr, &mut ctx).unwrap();
        assert!(code.contains("_ant"), "should have antecedent: {}", code);
    }

    #[test]
    fn test_if_then_else() {
        let expr = Expr::If {
            cond: Box::new(Expr::Literal(Literal::Bool(true))),
            then_branch: Box::new(Expr::Literal(Literal::Int(1))),
            else_branch: Some(Box::new(Expr::Literal(Literal::Int(2)))),
        };
        let mut ctx = CodegenCtx::new(&[]);
        let code = expr_to_rust(&expr, &mut ctx).unwrap();
        assert!(code.contains("if"), "code: {}", code);
        assert!(code.contains("else"), "code: {}", code);
    }

    #[test]
    fn test_binary_add() {
        let expr = Expr::Binary(
            Box::new(Expr::Literal(Literal::Int(1))),
            BinOp::Add,
            Box::new(Expr::Literal(Literal::Int(2))),
        );
        let mut ctx = CodegenCtx::new(&[]);
        let code = expr_to_rust(&expr, &mut ctx).unwrap();
        assert!(code.contains("BinOp::Add"), "code: {}", code);
        assert!(code.contains("rt_binop"), "code: {}", code);
    }

    #[test]
    fn test_binary_and_short_circuit() {
        let expr = Expr::Binary(
            Box::new(Expr::Literal(Literal::Bool(false))),
            BinOp::And,
            Box::new(Expr::Literal(Literal::Bool(true))),
        );
        let mut ctx = CodegenCtx::new(&[]);
        let code = expr_to_rust(&expr, &mut ctx).unwrap();
        assert!(
            code.contains("Bool(false)"),
            "should short-circuit: {}",
            code
        );
    }

    #[test]
    fn test_set_lit() {
        let expr = Expr::SetLit(vec![
            Expr::Literal(Literal::Int(1)),
            Expr::Literal(Literal::Int(2)),
        ]);
        let mut ctx = CodegenCtx::new(&[]);
        let code = expr_to_rust(&expr, &mut ctx).unwrap();
        assert!(code.contains("set_bounded"), "code: {}", code);
    }

    #[test]
    fn test_seq_lit() {
        let expr = Expr::SeqLit(vec![Expr::Literal(Literal::Int(10))]);
        let mut ctx = CodegenCtx::new(&[]);
        let code = expr_to_rust(&expr, &mut ctx).unwrap();
        assert!(code.contains("seq_bounded"), "code: {}", code);
    }

    #[test]
    fn test_map_lit() {
        let expr = Expr::MapLit(vec![(
            Expr::Literal(Literal::Int(1)),
            Expr::Literal(Literal::Bool(true)),
        )]);
        let mut ctx = CodegenCtx::new(&[]);
        let code = expr_to_rust(&expr, &mut ctx).unwrap();
        assert!(code.contains("map_bounded"), "code: {}", code);
    }

    #[test]
    fn test_field_access() {
        let expr = Expr::Field(Box::new(Expr::Ident("s".to_string())), "foo".to_string());
        let names = vec!["s".to_string()];
        let mut ctx = CodegenCtx::new(&names);
        let code = expr_to_rust(&expr, &mut ctx).unwrap();
        assert!(code.contains("rt_field"), "code: {}", code);
        assert!(code.contains("foo"), "code: {}", code);
    }

    #[test]
    fn test_index_access() {
        let expr = Expr::Index(
            Box::new(Expr::Ident("s".to_string())),
            Box::new(Expr::Literal(Literal::Int(0))),
        );
        let names = vec!["s".to_string()];
        let mut ctx = CodegenCtx::new(&names);
        let code = expr_to_rust(&expr, &mut ctx).unwrap();
        assert!(code.contains("rt_index"), "code: {}", code);
    }

    #[test]
    fn test_is_variant() {
        let expr = Expr::Is(
            Box::new(Expr::Ident("msg".to_string())),
            "Prepare".to_string(),
        );
        let names = vec!["msg".to_string()];
        let mut ctx = CodegenCtx::new(&names);
        let code = expr_to_rust(&expr, &mut ctx).unwrap();
        assert!(code.contains("rt_is_variant"), "code: {}", code);
        assert!(code.contains("Prepare"), "code: {}", code);
    }

    #[test]
    fn test_let_binding() {
        let expr = Expr::Let {
            binding: Binding {
                pattern: Pattern::Ident("x".to_string()),
                ty: None,
                variable_mode: VariableMode::default(),
            },
            value: Box::new(Expr::Literal(Literal::Int(42))),
            body: Box::new(Expr::Ident("x".to_string())),
        };
        let mut ctx = CodegenCtx::new(&[]);
        let code = expr_to_rust(&expr, &mut ctx).unwrap();
        assert!(code.contains("let"), "code: {}", code);
        // The body should reference the temp var, not "x" directly
        assert!(code.contains("_t"), "should use temp var: {}", code);
    }

    #[test]
    fn test_not() {
        let expr = Expr::Not(Box::new(Expr::Literal(Literal::Bool(true))));
        let mut ctx = CodegenCtx::new(&[]);
        let code = expr_to_rust(&expr, &mut ctx).unwrap();
        assert!(code.contains("!"), "code: {}", code);
    }

    #[test]
    fn test_empty_collections() {
        let mut ctx = CodegenCtx::new(&[]);
        let code = expr_to_rust(&Expr::SetEmpty, &mut ctx).unwrap();
        assert!(code.contains("set_bounded"), "code: {}", code);
        let code = expr_to_rust(&Expr::SeqEmpty, &mut ctx).unwrap();
        assert!(code.contains("seq_bounded"), "code: {}", code);
        let code = expr_to_rust(&Expr::MapEmpty, &mut ctx).unwrap();
        assert!(code.contains("map_bounded"), "code: {}", code);
    }

    #[test]
    fn test_unsupported_forall_errors() {
        let expr = Expr::Forall {
            vars: vec![],
            triggers: vec![],
            body: Box::new(Expr::Literal(Literal::Bool(true))),
        };
        let mut ctx = CodegenCtx::new(&[]);
        let result = expr_to_rust(&expr, &mut ctx);
        assert!(result.is_err());
        assert!(result.unwrap_err().message.contains("Forall"));
    }

    #[test]
    fn test_unsupported_method_call_errors() {
        let expr = Expr::MethodCall {
            receiver: Box::new(Expr::Ident("s".to_string())),
            method: "contains".to_string(),
            args: vec![Expr::Literal(Literal::Int(1))],
        };
        let mut ctx = CodegenCtx::new(&["s".to_string()]);
        let result = expr_to_rust(&expr, &mut ctx);
        assert!(result.is_err());
    }

    #[test]
    fn test_generate_eval_function() {
        let expr = Expr::Eq(
            Box::new(Expr::Ident("x".to_string())),
            Box::new(Expr::Literal(Literal::Int(42))),
        );
        let names = vec!["x".to_string()];
        let code = generate_eval_function(&expr, &names).unwrap();
        assert!(
            code.contains("fn eval(env: &[RuntimeValue])"),
            "code: {}",
            code
        );
        assert!(
            code.contains("TranspileResult<RuntimeValue>"),
            "code: {}",
            code
        );
    }

    #[test]
    fn test_check_codegen_support_simple() {
        let expr = Expr::Eq(
            Box::new(Expr::Literal(Literal::Int(1))),
            Box::new(Expr::Literal(Literal::Int(2))),
        );
        assert!(check_codegen_support(&expr).is_ok());
    }

    #[test]
    fn test_check_codegen_support_rejects_forall() {
        let expr = Expr::Forall {
            vars: vec![],
            triggers: vec![],
            body: Box::new(Expr::Literal(Literal::Bool(true))),
        };
        assert!(check_codegen_support(&expr).is_err());
    }

    #[test]
    fn test_check_codegen_support_nested() {
        // If { cond: true, then: Forall{...}, else: 1 } — should fail
        let expr = Expr::If {
            cond: Box::new(Expr::Literal(Literal::Bool(true))),
            then_branch: Box::new(Expr::Forall {
                vars: vec![],
                triggers: vec![],
                body: Box::new(Expr::Literal(Literal::Bool(true))),
            }),
            else_branch: Some(Box::new(Expr::Literal(Literal::Int(1)))),
        };
        assert!(check_codegen_support(&expr).is_err());
    }

    #[test]
    fn test_split_variant_path() {
        assert_eq!(
            split_variant_path("MyEnum::Variant"),
            Some(("MyEnum", "Variant"))
        );
        assert_eq!(split_variant_path("no_colons"), None);
        assert_eq!(split_variant_path("::empty_ty"), None);
        assert_eq!(split_variant_path("empty_var::"), None);
    }

    #[test]
    fn test_nested_expression() {
        // (x + 1) == (y - 2)
        let expr = Expr::Eq(
            Box::new(Expr::Binary(
                Box::new(Expr::Ident("x".to_string())),
                BinOp::Add,
                Box::new(Expr::Literal(Literal::Int(1))),
            )),
            Box::new(Expr::Binary(
                Box::new(Expr::Ident("y".to_string())),
                BinOp::Sub,
                Box::new(Expr::Literal(Literal::Int(2))),
            )),
        );
        let names = vec!["x".to_string(), "y".to_string()];
        let mut ctx = CodegenCtx::new(&names);
        let code = expr_to_rust(&expr, &mut ctx).unwrap();
        assert!(code.contains("env[0]"), "should ref x as env[0]: {}", code);
        assert!(code.contains("env[1]"), "should ref y as env[1]: {}", code);
        assert!(code.contains("BinOp::Add"), "code: {}", code);
        assert!(code.contains("BinOp::Sub"), "code: {}", code);
    }

    #[test]
    fn test_iff() {
        let expr = Expr::Iff(
            Box::new(Expr::Literal(Literal::Bool(true))),
            Box::new(Expr::Literal(Literal::Bool(false))),
        );
        let mut ctx = CodegenCtx::new(&[]);
        let code = expr_to_rust(&expr, &mut ctx).unwrap();
        assert!(code.contains("rt_expect_bool"), "code: {}", code);
        assert!(code.contains("=="), "code: {}", code);
    }

    #[test]
    fn test_unary_neg() {
        let expr = Expr::Unary(UnaryOp::Neg, Box::new(Expr::Literal(Literal::Int(5))));
        let mut ctx = CodegenCtx::new(&[]);
        let code = expr_to_rust(&expr, &mut ctx).unwrap();
        assert!(code.contains("rt_negate"), "code: {}", code);
    }
}
