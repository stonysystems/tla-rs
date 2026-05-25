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

        // --- Phase 38.22.1.c.ii: struct, method, call, quantifier, match ---
        Expr::Struct { name, fields } => {
            let ty_name = path_to_string(name);
            if let Some((ty, variant)) = split_variant_path(&ty_name) {
                // Enum variant construction
                let mut field_parts = Vec::new();
                for (fname, fexpr) in fields {
                    if fname == ".." {
                        return Err(codegen_err("struct spread in enum variant"));
                    }
                    let fcode = expr_to_rust_val(fexpr, ctx)?;
                    field_parts.push(format!("({:?}.to_string(), {})", fname, fcode));
                }
                Ok(format!(
                    "RuntimeValue::enum_value({:?}, {:?}, vec![{}])",
                    ty,
                    variant,
                    field_parts.join(", ")
                ))
            } else {
                // Check for spread (..) base
                let mut has_spread = false;
                let mut base_code = String::new();
                let mut field_parts = Vec::new();
                for (fname, fexpr) in fields {
                    if fname == ".." {
                        has_spread = true;
                        base_code = expr_to_rust_val(fexpr, ctx)?;
                    } else {
                        let fcode = expr_to_rust_val(fexpr, ctx)?;
                        field_parts.push(format!("({:?}.to_string(), {})", fname, fcode));
                    }
                }
                if has_spread {
                    Ok(format!(
                        "rt_struct_update(&{}, vec![{}])",
                        base_code,
                        field_parts.join(", ")
                    ))
                } else {
                    Ok(format!(
                        "RuntimeValue::struct_value({:?}, vec![{}])",
                        ty_name,
                        field_parts.join(", ")
                    ))
                }
            }
        }

        Expr::StructUpdate { name, base, fields } => {
            let base_code = expr_to_rust_val(base, ctx)?;
            let mut field_parts = Vec::new();
            for (fname, fexpr) in fields {
                let fcode = expr_to_rust_val(fexpr, ctx)?;
                field_parts.push(format!("({:?}.to_string(), {})", fname, fcode));
            }
            if let Some(n) = name {
                Ok(format!(
                    "rt_struct_update_named({:?}, &{}, vec![{}])",
                    path_to_string(n),
                    base_code,
                    field_parts.join(", ")
                ))
            } else {
                Ok(format!(
                    "rt_struct_update(&{}, vec![{}])",
                    base_code,
                    field_parts.join(", ")
                ))
            }
        }

        Expr::MethodCall {
            receiver,
            method,
            args,
        } => {
            let recv_code = expr_to_rust_val(receiver, ctx)?;
            let mut arg_codes = Vec::new();
            for arg in args {
                arg_codes.push(expr_to_rust_val(arg, ctx)?);
            }
            Ok(format!(
                "rt_method_call(&{}, {:?}, &[{}], &BOUNDS)",
                recv_code,
                method,
                arg_codes.join(", ")
            ))
        }

        Expr::Call { func, args } => {
            let mut arg_codes = Vec::new();
            for arg in args {
                arg_codes.push(expr_to_rust_val(arg, ctx)?);
            }
            let func_name = path_to_string(func);
            Ok(format!(
                "rt_call({:?}, &[{}], &BOUNDS)",
                func_name,
                arg_codes.join(", ")
            ))
        }

        Expr::Forall { vars, body, .. } => {
            quantifier_codegen(vars, body, "true", "false", "&&", ctx)
        }

        Expr::Exists { vars, body } => quantifier_codegen(vars, body, "false", "true", "||", ctx),

        Expr::Choose { vars, body } => choose_codegen(vars, body, ctx),

        Expr::Match { scrutinee, arms } => match_codegen(scrutinee, arms, ctx),

        // Closures are handled at call sites (Set::new, Map::new)
        Expr::Closure { .. } => Err(codegen_err("standalone Closure not supported")),
    }
}

fn path_to_string(path: &crate::ast::Path) -> String {
    path.segments.join("::")
}

/// Generate code for forall/exists quantifiers.
/// `init` is the initial accumulator ("true" for forall, "false" for exists).
/// `short` is the short-circuit value ("false" for forall, "true" for exists).
fn quantifier_codegen(
    vars: &[crate::ast::Binding],
    body: &Expr,
    init: &str,
    short: &str,
    _op: &str,
    ctx: &mut CodegenCtx,
) -> CodegenResult<String> {
    if vars.is_empty() {
        let body_code = expr_to_rust_val(body, ctx)?;
        return Ok(format!(
            "Ok(RuntimeValue::Bool(rt_expect_bool(&{})?))",
            body_code
        ));
    }

    // Build nested loops, one per quantified variable
    let mut code = String::new();
    let mut tmps = Vec::new();
    write!(code, "{{ let mut _qr = {}; ", init).unwrap();

    for var in vars {
        let name = match &var.pattern {
            crate::ast::Pattern::Ident(n) => n.clone(),
            _ => return Err(codegen_err("quantifier with non-identifier binding")),
        };
        let tmp = ctx.fresh_tmp();
        // Domain is computed by the runtime via quantifier_domain callback
        write!(
            code,
            "'q{}: for {} in rt_quantifier_domain({})?.iter() {{ ",
            tmps.len(),
            tmp,
            var_binding_index(vars, &name)
        )
        .unwrap();
        ctx.locals.insert(name, tmp.clone());
        tmps.push(tmp);
    }

    // Body evaluation
    let body_code = expr_to_rust_val(body, ctx)?;
    write!(
        code,
        "let _bv = rt_expect_bool(&{})?; if _bv == {} {{ _qr = {}; break 'q0; }}",
        body_code, short, short
    )
    .unwrap();

    // Close all loops
    for _ in vars {
        write!(code, " }}").unwrap();
    }
    write!(code, " Ok(RuntimeValue::Bool(_qr)) }}").unwrap();

    // Clean up ctx locals (they were temporary)
    for var in vars {
        if let crate::ast::Pattern::Ident(n) = &var.pattern {
            ctx.locals.remove(n);
        }
    }
    Ok(code)
}

fn var_binding_index(vars: &[crate::ast::Binding], name: &str) -> usize {
    vars.iter()
        .position(|v| matches!(&v.pattern, crate::ast::Pattern::Ident(n) if n == name))
        .unwrap_or(0)
}

/// Generate code for CHOOSE expressions.
fn choose_codegen(
    vars: &[crate::ast::Binding],
    body: &Expr,
    ctx: &mut CodegenCtx,
) -> CodegenResult<String> {
    if vars.is_empty() {
        return Err(codegen_err("CHOOSE with no bound variables"));
    }

    let mut code = String::new();
    let mut tmps = Vec::new();
    write!(
        code,
        "{{ let mut _choose_result: Option<RuntimeValue> = None; "
    )
    .unwrap();

    for (i, var) in vars.iter().enumerate() {
        let name = match &var.pattern {
            crate::ast::Pattern::Ident(n) => n.clone(),
            _ => return Err(codegen_err("CHOOSE with non-identifier binding")),
        };
        let tmp = ctx.fresh_tmp();
        write!(
            code,
            "'ch{}: for {} in rt_quantifier_domain({})?.iter() {{ ",
            i,
            tmp,
            var_binding_index(vars, &name)
        )
        .unwrap();
        ctx.locals.insert(name, tmp.clone());
        tmps.push(tmp);
    }

    let body_code = expr_to_rust_val(body, ctx)?;
    write!(
        code,
        "if rt_expect_bool(&{})? {{ _choose_result = Some({}.clone()); break 'ch0; }}",
        body_code, tmps[0]
    )
    .unwrap();

    for _ in vars {
        write!(code, " }}").unwrap();
    }
    write!(
        code,
        " match _choose_result {{ Some(v) => Ok(v), None => Err(rt_error(\"CHOOSE: no satisfying value\")) }} }}"
    )
    .unwrap();

    for var in vars {
        if let crate::ast::Pattern::Ident(n) = &var.pattern {
            ctx.locals.remove(n);
        }
    }
    Ok(code)
}

/// Generate code for match expressions.
fn match_codegen(
    scrutinee: &Expr,
    arms: &[crate::ast::MatchArm],
    ctx: &mut CodegenCtx,
) -> CodegenResult<String> {
    let scrut_code = expr_to_rust_val(scrutinee, ctx)?;
    let scrut_tmp = ctx.fresh_tmp();

    let mut code = String::new();
    write!(code, "{{ let {} = {}; ", scrut_tmp, scrut_code).unwrap();

    for (i, arm) in arms.iter().enumerate() {
        let (condition, bindings) = pattern_to_condition(&arm.pattern, &scrut_tmp, ctx)?;

        if i > 0 {
            write!(code, " else ").unwrap();
        }
        write!(code, "if {} {{ ", condition).unwrap();

        // Add pattern bindings to context
        let mut inner_ctx = ctx.clone();
        for (name, expr_str) in &bindings {
            inner_ctx.locals.insert(name.clone(), expr_str.clone());
        }

        // Guard
        if let Some(guard) = &arm.guard {
            let guard_code = expr_to_rust_val(guard, &mut inner_ctx)?;
            write!(code, "if rt_expect_bool(&{})? {{ ", guard_code).unwrap();
            let body_code = expr_to_rust(&arm.body, &mut inner_ctx)?;
            write!(code, "{} }} else {{ rt_match_fallthrough() }}", body_code).unwrap();
        } else {
            let body_code = expr_to_rust(&arm.body, &mut inner_ctx)?;
            write!(code, "{}", body_code).unwrap();
        }

        write!(code, " }}").unwrap();
    }

    write!(
        code,
        " else {{ Err(rt_error(\"match: no arm matched\")) }} }}"
    )
    .unwrap();
    Ok(code)
}

/// Convert a pattern to a boolean condition string and binding list.
fn pattern_to_condition(
    pattern: &crate::ast::Pattern,
    scrutinee: &str,
    ctx: &mut CodegenCtx,
) -> CodegenResult<(String, Vec<(String, String)>)> {
    match pattern {
        crate::ast::Pattern::Wildcard => Ok(("true".to_string(), Vec::new())),

        crate::ast::Pattern::Ident(name) => Ok((
            "true".to_string(),
            vec![(name.clone(), format!("{}.clone()", scrutinee))],
        )),

        crate::ast::Pattern::Literal(lit) => {
            let lit_code = match lit {
                Literal::Bool(b) => format!("RuntimeValue::Bool({})", b),
                Literal::Int(n) => format!("RuntimeValue::Int({})", n),
                Literal::String(s) => format!("RuntimeValue::String({:?}.to_string())", s),
            };
            Ok((format!("{} == {}", scrutinee, lit_code), Vec::new()))
        }

        crate::ast::Pattern::Struct { name, fields } => {
            let ty_name = path_to_string(name);
            let mut bindings = Vec::new();
            let mut conditions = vec![format!("rt_is_struct(&{}, {:?})", scrutinee, ty_name)];
            for (fname, fpat) in fields {
                let field_access = format!("rt_field_val(&{}, {:?})", scrutinee, fname);
                let (sub_cond, sub_binds) = pattern_to_condition(fpat, &field_access, ctx)?;
                if sub_cond != "true" {
                    conditions.push(sub_cond);
                }
                bindings.extend(sub_binds);
            }
            Ok((conditions.join(" && "), bindings))
        }

        crate::ast::Pattern::Variant { name, fields } => {
            let full_name = path_to_string(name);
            let variant = name.segments.last().cloned().unwrap_or_default();
            let mut bindings = Vec::new();
            let mut conditions = vec![format!("rt_is_variant(&{}, {:?})", scrutinee, variant)];
            // Positional fields accessed by index
            for (i, fpat) in fields.iter().enumerate() {
                let field_access = format!("rt_variant_field(&{}, {})", scrutinee, i);
                let (sub_cond, sub_binds) = pattern_to_condition(fpat, &field_access, ctx)?;
                if sub_cond != "true" {
                    conditions.push(sub_cond);
                }
                bindings.extend(sub_binds);
            }
            let _ = full_name; // used for error context if needed
            Ok((conditions.join(" && "), bindings))
        }

        crate::ast::Pattern::Tuple(patterns) => {
            let mut bindings = Vec::new();
            let mut conditions = Vec::new();
            for (i, pat) in patterns.iter().enumerate() {
                let elem_access = format!("rt_tuple_field(&{}, {})", scrutinee, i);
                let (sub_cond, sub_binds) = pattern_to_condition(pat, &elem_access, ctx)?;
                if sub_cond != "true" {
                    conditions.push(sub_cond);
                }
                bindings.extend(sub_binds);
            }
            let cond = if conditions.is_empty() {
                "true".to_string()
            } else {
                conditions.join(" && ")
            };
            Ok((cond, bindings))
        }
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

        // Phase 38.22.1.c.ii: struct, method, call, quantifier, match
        Expr::Struct { fields, .. } => {
            for (_, fexpr) in fields {
                check_support_recursive(fexpr)?;
            }
            Ok(())
        }

        Expr::StructUpdate { base, fields, .. } => {
            check_support_recursive(base)?;
            for (_, fexpr) in fields {
                check_support_recursive(fexpr)?;
            }
            Ok(())
        }

        Expr::MethodCall { receiver, args, .. } => {
            check_support_recursive(receiver)?;
            for arg in args {
                check_support_recursive(arg)?;
            }
            Ok(())
        }

        Expr::Call { args, .. } => {
            for arg in args {
                check_support_recursive(arg)?;
            }
            Ok(())
        }

        Expr::Forall { vars, body, .. } | Expr::Exists { vars, body } => {
            for var in vars {
                if !matches!(&var.pattern, crate::ast::Pattern::Ident(_)) {
                    return Err(codegen_err("quantifier with non-identifier binding"));
                }
            }
            check_support_recursive(body)
        }

        Expr::Choose { vars, body } => {
            for var in vars {
                if !matches!(&var.pattern, crate::ast::Pattern::Ident(_)) {
                    return Err(codegen_err("CHOOSE with non-identifier binding"));
                }
            }
            check_support_recursive(body)
        }

        Expr::Match { scrutinee, arms } => {
            check_support_recursive(scrutinee)?;
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    check_support_recursive(guard)?;
                }
                check_support_recursive(&arm.body)?;
            }
            Ok(())
        }

        // Closures only supported at call sites, not standalone
        Expr::Closure { .. } => Err(codegen_err("standalone Closure")),
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
    fn test_forall_empty_vars_returns_body() {
        let expr = Expr::Forall {
            vars: vec![],
            triggers: vec![],
            body: Box::new(Expr::Literal(Literal::Bool(true))),
        };
        let mut ctx = CodegenCtx::new(&[]);
        let result = expr_to_rust(&expr, &mut ctx);
        assert!(result.is_ok());
        let code = result.unwrap();
        assert!(code.contains("Bool"), "code: {}", code);
    }

    #[test]
    fn test_method_call_generates_rt_method_call() {
        let expr = Expr::MethodCall {
            receiver: Box::new(Expr::Ident("s".to_string())),
            method: "contains".to_string(),
            args: vec![Expr::Literal(Literal::Int(1))],
        };
        let mut ctx = CodegenCtx::new(&["s".to_string()]);
        let result = expr_to_rust(&expr, &mut ctx);
        assert!(result.is_ok());
        let code = result.unwrap();
        assert!(code.contains("rt_method_call"), "code: {}", code);
        assert!(code.contains("contains"), "code: {}", code);
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
    fn test_check_codegen_support_accepts_forall() {
        use crate::ast::Binding;
        let expr = Expr::Forall {
            vars: vec![Binding {
                pattern: crate::ast::Pattern::Ident("x".to_string()),
                ty: None,
                variable_mode: Default::default(),
            }],
            triggers: vec![],
            body: Box::new(Expr::Literal(Literal::Bool(true))),
        };
        assert!(check_codegen_support(&expr).is_ok());
    }

    #[test]
    fn test_check_codegen_support_nested_with_forall() {
        use crate::ast::Binding;
        // If { cond: true, then: Forall{...}, else: 1 } — should succeed now
        let expr = Expr::If {
            cond: Box::new(Expr::Literal(Literal::Bool(true))),
            then_branch: Box::new(Expr::Forall {
                vars: vec![Binding {
                    pattern: crate::ast::Pattern::Ident("x".to_string()),
                    ty: None,
                    variable_mode: Default::default(),
                }],
                triggers: vec![],
                body: Box::new(Expr::Literal(Literal::Bool(true))),
            }),
            else_branch: Some(Box::new(Expr::Literal(Literal::Int(1)))),
        };
        assert!(check_codegen_support(&expr).is_ok());
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

    // --- Phase 38.22.1.c.ii tests ---

    #[test]
    fn test_struct_construction() {
        let expr = Expr::Struct {
            name: crate::ast::Path::new(vec!["LState".to_string()]),
            fields: vec![
                ("x".to_string(), Expr::Literal(Literal::Int(1))),
                ("y".to_string(), Expr::Literal(Literal::Int(2))),
            ],
        };
        let mut ctx = CodegenCtx::new(&[]);
        let code = expr_to_rust(&expr, &mut ctx).unwrap();
        assert!(code.contains("struct_value"), "code: {}", code);
        assert!(code.contains("LState"), "code: {}", code);
    }

    #[test]
    fn test_enum_variant_construction() {
        let expr = Expr::Struct {
            name: crate::ast::Path::new(vec!["Msg".to_string(), "Prepare".to_string()]),
            fields: vec![("bal".to_string(), Expr::Literal(Literal::Int(1)))],
        };
        let mut ctx = CodegenCtx::new(&[]);
        let code = expr_to_rust(&expr, &mut ctx).unwrap();
        assert!(code.contains("enum_value"), "code: {}", code);
        assert!(code.contains("Msg"), "code: {}", code);
        assert!(code.contains("Prepare"), "code: {}", code);
    }

    #[test]
    fn test_struct_update() {
        let expr = Expr::StructUpdate {
            name: Some(crate::ast::Path::new(vec!["LState".to_string()])),
            base: Box::new(Expr::Ident("s".to_string())),
            fields: vec![("x".to_string(), Expr::Literal(Literal::Int(42)))],
        };
        let names = vec!["s".to_string()];
        let mut ctx = CodegenCtx::new(&names);
        let code = expr_to_rust(&expr, &mut ctx).unwrap();
        assert!(code.contains("rt_struct_update_named"), "code: {}", code);
    }

    #[test]
    fn test_method_call() {
        let expr = Expr::MethodCall {
            receiver: Box::new(Expr::Ident("s".to_string())),
            method: "contains".to_string(),
            args: vec![Expr::Literal(Literal::Int(1))],
        };
        let names = vec!["s".to_string()];
        let mut ctx = CodegenCtx::new(&names);
        let code = expr_to_rust(&expr, &mut ctx).unwrap();
        assert!(code.contains("rt_method_call"), "code: {}", code);
        assert!(code.contains("contains"), "code: {}", code);
    }

    #[test]
    fn test_function_call() {
        let expr = Expr::Call {
            func: crate::ast::Path::new(vec!["Helper".to_string(), "compute".to_string()]),
            args: vec![Expr::Literal(Literal::Int(1))],
        };
        let mut ctx = CodegenCtx::new(&[]);
        let code = expr_to_rust(&expr, &mut ctx).unwrap();
        assert!(code.contains("rt_call"), "code: {}", code);
        assert!(code.contains("Helper::compute"), "code: {}", code);
    }

    #[test]
    fn test_forall_quantifier() {
        let expr = Expr::Forall {
            vars: vec![Binding {
                pattern: Pattern::Ident("i".to_string()),
                ty: Some(crate::ast::Type::Int),
                variable_mode: VariableMode::default(),
            }],
            triggers: vec![],
            body: Box::new(Expr::Literal(Literal::Bool(true))),
        };
        let mut ctx = CodegenCtx::new(&[]);
        let code = expr_to_rust(&expr, &mut ctx).unwrap();
        assert!(code.contains("rt_quantifier_domain"), "code: {}", code);
        assert!(
            code.contains("_qr"),
            "should have quantifier result: {}",
            code
        );
    }

    #[test]
    fn test_exists_quantifier() {
        let expr = Expr::Exists {
            vars: vec![Binding {
                pattern: Pattern::Ident("x".to_string()),
                ty: Some(crate::ast::Type::Int),
                variable_mode: VariableMode::default(),
            }],
            body: Box::new(Expr::Eq(
                Box::new(Expr::Ident("x".to_string())),
                Box::new(Expr::Literal(Literal::Int(1))),
            )),
        };
        let mut ctx = CodegenCtx::new(&[]);
        let code = expr_to_rust(&expr, &mut ctx).unwrap();
        assert!(
            code.contains("false"),
            "exists init should be false: {}",
            code
        );
        assert!(
            code.contains("true"),
            "exists short-circuit to true: {}",
            code
        );
    }

    #[test]
    fn test_choose() {
        let expr = Expr::Choose {
            vars: vec![Binding {
                pattern: Pattern::Ident("v".to_string()),
                ty: Some(crate::ast::Type::Int),
                variable_mode: VariableMode::default(),
            }],
            body: Box::new(Expr::Literal(Literal::Bool(true))),
        };
        let mut ctx = CodegenCtx::new(&[]);
        let code = expr_to_rust(&expr, &mut ctx).unwrap();
        assert!(code.contains("_choose_result"), "code: {}", code);
        assert!(code.contains("rt_quantifier_domain"), "code: {}", code);
    }

    #[test]
    fn test_match_simple() {
        let expr = Expr::Match {
            scrutinee: Box::new(Expr::Ident("msg".to_string())),
            arms: vec![crate::ast::MatchArm {
                pattern: Pattern::Ident("x".to_string()),
                guard: None,
                body: Expr::Literal(Literal::Int(1)),
            }],
        };
        let names = vec!["msg".to_string()];
        let mut ctx = CodegenCtx::new(&names);
        let code = expr_to_rust(&expr, &mut ctx).unwrap();
        assert!(code.contains("if true"), "wildcard-like match: {}", code);
    }

    #[test]
    fn test_match_variant_pattern() {
        let expr = Expr::Match {
            scrutinee: Box::new(Expr::Ident("msg".to_string())),
            arms: vec![crate::ast::MatchArm {
                pattern: Pattern::Variant {
                    name: crate::ast::Path::new(vec!["Msg".to_string(), "Prepare".to_string()]),
                    fields: vec![Pattern::Ident("bal".to_string())],
                },
                guard: None,
                body: Expr::Ident("bal".to_string()),
            }],
        };
        let names = vec!["msg".to_string()];
        let mut ctx = CodegenCtx::new(&names);
        let code = expr_to_rust(&expr, &mut ctx).unwrap();
        assert!(
            code.contains("rt_is_variant"),
            "should check variant: {}",
            code
        );
        assert!(code.contains("Prepare"), "should check Prepare: {}", code);
    }

    #[test]
    fn test_struct_spread() {
        // LState { x: 1, ..s }
        let expr = Expr::Struct {
            name: crate::ast::Path::new(vec!["LState".to_string()]),
            fields: vec![
                ("x".to_string(), Expr::Literal(Literal::Int(1))),
                ("..".to_string(), Expr::Ident("s".to_string())),
            ],
        };
        let names = vec!["s".to_string()];
        let mut ctx = CodegenCtx::new(&names);
        let code = expr_to_rust(&expr, &mut ctx).unwrap();
        assert!(
            code.contains("rt_struct_update"),
            "should use struct update for spread: {}",
            code
        );
    }

    #[test]
    fn test_check_support_struct() {
        let expr = Expr::Struct {
            name: crate::ast::Path::new(vec!["S".to_string()]),
            fields: vec![("x".to_string(), Expr::Literal(Literal::Int(1)))],
        };
        assert!(check_codegen_support(&expr).is_ok());
    }

    #[test]
    fn test_check_support_forall() {
        let expr = Expr::Forall {
            vars: vec![Binding {
                pattern: Pattern::Ident("i".to_string()),
                ty: Some(crate::ast::Type::Int),
                variable_mode: VariableMode::default(),
            }],
            triggers: vec![],
            body: Box::new(Expr::Literal(Literal::Bool(true))),
        };
        assert!(check_codegen_support(&expr).is_ok());
    }

    #[test]
    fn test_check_support_match() {
        let expr = Expr::Match {
            scrutinee: Box::new(Expr::Literal(Literal::Int(1))),
            arms: vec![crate::ast::MatchArm {
                pattern: Pattern::Wildcard,
                guard: None,
                body: Expr::Literal(Literal::Int(2)),
            }],
        };
        assert!(check_codegen_support(&expr).is_ok());
    }

    #[test]
    fn test_check_support_closure_rejected() {
        let expr = Expr::Closure {
            params: vec![],
            body: Box::new(Expr::Literal(Literal::Bool(true))),
        };
        assert!(check_codegen_support(&expr).is_err());
    }
}
