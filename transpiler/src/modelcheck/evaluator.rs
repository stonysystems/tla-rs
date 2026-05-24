use crate::ast::{BinOp, Binding, Expr, MatchArm, Path, Pattern, Type, UnaryOp};
use crate::error::{TranspileError, TranspileResult};
use crate::modelcheck::symbol::Symbol;
use crate::modelcheck::value::{RuntimeCollectionBounds, RuntimeValue};
use std::collections::BTreeMap;

pub type CallEvaluator<'a> = dyn Fn(&Path, &[RuntimeValue]) -> TranspileResult<RuntimeValue> + 'a;
pub type MethodEvaluator<'a> =
    dyn Fn(&RuntimeValue, &str, &[RuntimeValue]) -> TranspileResult<RuntimeValue> + 'a;
pub type QuantifierDomainEvaluator<'a> =
    dyn Fn(&Binding) -> TranspileResult<Vec<RuntimeValue>> + 'a;

/// Runtime evaluator context for source-first model checking.
#[derive(Clone)]
pub struct EvalContext<'a> {
    bindings: BTreeMap<String, RuntimeValue>,
    bounds: RuntimeCollectionBounds,
    call_evaluator: Option<&'a CallEvaluator<'a>>,
    method_evaluator: Option<&'a MethodEvaluator<'a>>,
    quantifier_domain_evaluator: Option<&'a QuantifierDomainEvaluator<'a>>,
}

impl<'a> EvalContext<'a> {
    pub fn new(bounds: RuntimeCollectionBounds) -> Self {
        Self {
            bindings: BTreeMap::new(),
            bounds,
            call_evaluator: None,
            method_evaluator: None,
            quantifier_domain_evaluator: None,
        }
    }

    pub fn with_binding(mut self, name: impl Into<String>, value: RuntimeValue) -> Self {
        self.bindings.insert(name.into(), value);
        self
    }

    pub fn with_call_evaluator(mut self, evaluator: &'a CallEvaluator<'a>) -> Self {
        self.call_evaluator = Some(evaluator);
        self
    }

    pub fn with_method_evaluator(mut self, evaluator: &'a MethodEvaluator<'a>) -> Self {
        self.method_evaluator = Some(evaluator);
        self
    }

    pub fn with_quantifier_domain_evaluator(
        mut self,
        evaluator: &'a QuantifierDomainEvaluator<'a>,
    ) -> Self {
        self.quantifier_domain_evaluator = Some(evaluator);
        self
    }

    fn child_with_binding(&self, name: String, value: RuntimeValue) -> Self {
        let mut bindings = self.bindings.clone();
        bindings.insert(name, value);
        Self {
            bindings,
            bounds: self.bounds,
            call_evaluator: self.call_evaluator,
            method_evaluator: self.method_evaluator,
            quantifier_domain_evaluator: self.quantifier_domain_evaluator,
        }
    }
}

/// Phase 38.22.1.a — eval_expr profile counters. Per-Expr-variant call
/// counts that ground-truth where AST-traversal time goes. Gated on
/// the `TLARS_EVAL_PROFILE=1` environment variable so the increment is
/// branch-prediction-friendly when disabled. Counts are dumped to
/// stderr at process exit by `dump_eval_expr_profile()`.
#[derive(Default, Debug)]
pub struct EvalExprProfile {
    pub conjunction: u64,
    pub disjunction: u64,
    pub implies: u64,
    pub iff: u64,
    pub not: u64,
    pub if_expr: u64,
    pub literal: u64,
    pub ident: u64,
    pub view: u64,
    pub cast: u64,
    pub field: u64,
    pub arrow: u64,
    pub call: u64,
    pub method_call: u64,
    pub binary: u64,
    pub eq: u64,
    pub ne: u64,
    pub lt: u64,
    pub le: u64,
    pub gt: u64,
    pub ge: u64,
    pub set_lit: u64,
    pub seq_lit: u64,
    pub map_lit: u64,
    pub tuple: u64,
    pub set_empty: u64,
    pub seq_empty: u64,
    pub map_empty: u64,
    pub forall: u64,
    pub exists: u64,
    pub choose: u64,
    pub closure: u64,
    pub struct_lit: u64,
    pub struct_update: u64,
    pub is_check: u64,
    pub match_expr: u64,
    pub other: u64,
}

thread_local! {
    static EVAL_EXPR_PROFILE: std::cell::RefCell<EvalExprProfile> =
        std::cell::RefCell::new(EvalExprProfile::default());
    static EVAL_EXPR_PROFILE_ENABLED: std::cell::Cell<bool> =
        std::cell::Cell::new(std::env::var("TLARS_EVAL_PROFILE").is_ok());
}

#[inline(always)]
fn bump_profile<F: FnOnce(&mut EvalExprProfile)>(f: F) {
    if EVAL_EXPR_PROFILE_ENABLED.with(|c| c.get()) {
        EVAL_EXPR_PROFILE.with(|p| f(&mut p.borrow_mut()));
    }
}

/// Print the accumulated eval_expr profile to stderr and reset the
/// counters. Called once at the end of a model-check run when the
/// `TLARS_EVAL_PROFILE` env var is set.
pub fn dump_eval_expr_profile() {
    if !EVAL_EXPR_PROFILE_ENABLED.with(|c| c.get()) {
        return;
    }
    EVAL_EXPR_PROFILE.with(|p| {
        let p = p.borrow();
        let total = p.conjunction
            + p.disjunction
            + p.implies
            + p.iff
            + p.not
            + p.if_expr
            + p.literal
            + p.ident
            + p.view
            + p.cast
            + p.field
            + p.arrow
            + p.call
            + p.method_call
            + p.binary
            + p.eq
            + p.ne
            + p.lt
            + p.le
            + p.gt
            + p.ge
            + p.set_lit
            + p.seq_lit
            + p.map_lit
            + p.tuple
            + p.set_empty
            + p.seq_empty
            + p.map_empty
            + p.forall
            + p.exists
            + p.choose
            + p.closure
            + p.struct_lit
            + p.struct_update
            + p.is_check
            + p.match_expr
            + p.other;
        eprintln!("=== eval_expr profile (Phase 38.22.1.a) ===");
        eprintln!("total calls: {}", total);
        let mut entries: Vec<(&str, u64)> = vec![
            ("Conjunction", p.conjunction),
            ("Disjunction", p.disjunction),
            ("Implies", p.implies),
            ("Iff", p.iff),
            ("Not", p.not),
            ("If", p.if_expr),
            ("Literal", p.literal),
            ("Ident", p.ident),
            ("View", p.view),
            ("Cast", p.cast),
            ("Field", p.field),
            ("Arrow", p.arrow),
            ("Call", p.call),
            ("MethodCall", p.method_call),
            ("Binary", p.binary),
            ("Eq", p.eq),
            ("Ne", p.ne),
            ("Lt", p.lt),
            ("Le", p.le),
            ("Gt", p.gt),
            ("Ge", p.ge),
            ("SetLit", p.set_lit),
            ("SeqLit", p.seq_lit),
            ("MapLit", p.map_lit),
            ("Tuple", p.tuple),
            ("SetEmpty", p.set_empty),
            ("SeqEmpty", p.seq_empty),
            ("MapEmpty", p.map_empty),
            ("Forall", p.forall),
            ("Exists", p.exists),
            ("Choose", p.choose),
            ("Closure", p.closure),
            ("Struct", p.struct_lit),
            ("StructUpdate", p.struct_update),
            ("Is", p.is_check),
            ("Match", p.match_expr),
            ("(other)", p.other),
        ];
        entries.sort_by(|a, b| b.1.cmp(&a.1));
        for (name, count) in entries.iter().filter(|(_, c)| *c > 0) {
            let pct = if total > 0 {
                100.0 * (*count as f64) / (total as f64)
            } else {
                0.0
            };
            eprintln!("  {:<14} {:>12}  {:>6.2}%", name, count, pct);
        }
    });
}

/// Evaluate a spec expression into a concrete runtime value.
pub fn eval_expr(expr: &Expr, ctx: &EvalContext<'_>) -> TranspileResult<RuntimeValue> {
    bump_profile(|p| match expr {
        Expr::Conjunction(_) => p.conjunction += 1,
        Expr::Disjunction(_) => p.disjunction += 1,
        Expr::Implies(_, _) => p.implies += 1,
        Expr::Iff(_, _) => p.iff += 1,
        Expr::Not(_) => p.not += 1,
        Expr::If { .. } => p.if_expr += 1,
        Expr::Eq(_, _) => p.eq += 1,
        Expr::Ne(_, _) => p.ne += 1,
        Expr::Lt(_, _) => p.lt += 1,
        Expr::Le(_, _) => p.le += 1,
        Expr::Gt(_, _) => p.gt += 1,
        Expr::Ge(_, _) => p.ge += 1,
        Expr::Field(_, _) => p.field += 1,
        Expr::Arrow(_, _) => p.arrow += 1,
        Expr::Call { .. } => p.call += 1,
        Expr::MethodCall { .. } => p.method_call += 1,
        Expr::View(_) => p.view += 1,
        Expr::Cast(_, _) => p.cast += 1,
        Expr::Ident(_) => p.ident += 1,
        Expr::Literal(_) => p.literal += 1,
        Expr::Binary(_, _, _) => p.binary += 1,
        Expr::SetLit(_) => p.set_lit += 1,
        Expr::SeqLit(_) => p.seq_lit += 1,
        Expr::MapLit(_) => p.map_lit += 1,
        Expr::SetEmpty => p.set_empty += 1,
        Expr::SeqEmpty => p.seq_empty += 1,
        Expr::MapEmpty => p.map_empty += 1,
        Expr::Forall { .. } => p.forall += 1,
        Expr::Exists { .. } => p.exists += 1,
        Expr::Choose { .. } => p.choose += 1,
        Expr::Closure { .. } => p.closure += 1,
        Expr::Struct { .. } => p.struct_lit += 1,
        Expr::StructUpdate { .. } => p.struct_update += 1,
        Expr::Is(_, _) => p.is_check += 1,
        Expr::Match { .. } => p.match_expr += 1,
        _ => p.other += 1,
    });
    match expr {
        Expr::Conjunction(items) => {
            for item in items {
                if !expect_bool(&eval_expr(item, ctx)?, "conjunction operand")? {
                    return Ok(RuntimeValue::Bool(false));
                }
            }
            Ok(RuntimeValue::Bool(true))
        }
        Expr::Disjunction(items) => {
            for item in items {
                if expect_bool(&eval_expr(item, ctx)?, "disjunction operand")? {
                    return Ok(RuntimeValue::Bool(true));
                }
            }
            Ok(RuntimeValue::Bool(false))
        }
        Expr::Implies(lhs, rhs) => {
            if !expect_bool(&eval_expr(lhs, ctx)?, "implication antecedent")? {
                return Ok(RuntimeValue::Bool(true));
            }
            Ok(RuntimeValue::Bool(expect_bool(
                &eval_expr(rhs, ctx)?,
                "implication consequent",
            )?))
        }
        Expr::Iff(lhs, rhs) => {
            let left = expect_bool(&eval_expr(lhs, ctx)?, "iff left operand")?;
            let right = expect_bool(&eval_expr(rhs, ctx)?, "iff right operand")?;
            Ok(RuntimeValue::Bool(left == right))
        }
        Expr::Not(inner) => Ok(RuntimeValue::Bool(!expect_bool(
            &eval_expr(inner, ctx)?,
            "negation operand",
        )?)),
        Expr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            if expect_bool(&eval_expr(cond, ctx)?, "if condition")? {
                eval_expr(then_branch, ctx)
            } else if let Some(else_branch) = else_branch {
                eval_expr(else_branch, ctx)
            } else {
                Ok(RuntimeValue::Unit)
            }
        }
        Expr::Let {
            binding,
            value,
            body,
        } => {
            let value = eval_expr(value, ctx)?;
            let Pattern::Ident(name) = &binding.pattern else {
                return Err(unsupported_construct("non-identifier let binding"));
            };
            let nested = ctx.child_with_binding(name.clone(), value);
            eval_expr(body, &nested)
        }
        Expr::Eq(lhs, rhs) => {
            let lhs = eval_expr(lhs, ctx)?;
            let rhs = eval_expr(rhs, ctx)?;
            Ok(RuntimeValue::Bool(lhs == rhs))
        }
        Expr::Ne(lhs, rhs) => {
            let lhs = eval_expr(lhs, ctx)?;
            let rhs = eval_expr(rhs, ctx)?;
            Ok(RuntimeValue::Bool(lhs != rhs))
        }
        Expr::Lt(lhs, rhs) => compare_numbers(lhs, rhs, ctx, |l, r| l < r),
        Expr::Le(lhs, rhs) => compare_numbers(lhs, rhs, ctx, |l, r| l <= r),
        Expr::Gt(lhs, rhs) => compare_numbers(lhs, rhs, ctx, |l, r| l > r),
        Expr::Ge(lhs, rhs) => compare_numbers(lhs, rhs, ctx, |l, r| l >= r),
        Expr::Is(base, variant) => {
            let base = eval_expr(base, ctx)?;
            match base {
                RuntimeValue::Enum {
                    variant: active, ..
                } => Ok(RuntimeValue::Bool(active == *variant)),
                other => Err(type_error(
                    format!(
                        "`is` operator expects enum value, got `{}`.",
                        other.canonical_key()
                    )
                    .as_str(),
                )),
            }
        }
        Expr::Field(base, field) | Expr::Arrow(base, field) => {
            let base = eval_expr(base, ctx)?;
            match base.field(field).cloned() {
                Some(value) => Ok(value),
                None if field == "tag" => {
                    // Enum discriminator pattern: s.role.tag where role is an int
                    // (from TLA+ `s.role.tag = Primary` with hash-encoded enums).
                    // Treat .tag as identity — the int IS the tag value.
                    Ok(base)
                }
                None => Err(type_error(
                    format!(
                        "Field access `.{}` is not valid for `{}`.",
                        field,
                        base.canonical_key()
                    )
                    .as_str(),
                )),
            }
        }
        Expr::Index(base, idx) => {
            let base = eval_expr(base, ctx)?;
            let idx = eval_expr(idx, ctx)?;
            match base {
                RuntimeValue::Seq(items) | RuntimeValue::Tuple(items) => {
                    let position = expect_index(&idx, "sequence/tuple index")?;
                    items.get(position).cloned().ok_or_else(|| {
                        type_error(
                            format!(
                                "Index {} out of bounds for length {}.",
                                position,
                                items.len()
                            )
                            .as_str(),
                        )
                    })
                }
                RuntimeValue::Map(entries) => entries.get(&idx).cloned().ok_or_else(|| {
                    type_error(
                        format!("Map key `{}` does not exist.", idx.canonical_key()).as_str(),
                    )
                }),
                other => Err(type_error(
                    format!(
                        "Index access expects Seq/Tuple/Map, got `{}`.",
                        other.canonical_key()
                    )
                    .as_str(),
                )),
            }
        }
        Expr::Struct { name, fields } => eval_struct_expr(name, fields, ctx),
        Expr::StructUpdate { name, base, fields } => {
            eval_struct_update_expr(name.as_ref(), base, fields, ctx)
        }
        Expr::SeqLit(items) => {
            let values = items
                .iter()
                .map(|item| eval_expr(item, ctx))
                .collect::<TranspileResult<Vec<_>>>()?;
            RuntimeValue::seq_bounded(values, &ctx.bounds)
        }
        Expr::SetLit(items) => {
            let values = items
                .iter()
                .map(|item| eval_expr(item, ctx))
                .collect::<TranspileResult<Vec<_>>>()?;
            RuntimeValue::set_bounded(values, &ctx.bounds)
        }
        Expr::MapLit(entries) => {
            let values = entries
                .iter()
                .map(|(key, value)| Ok((eval_expr(key, ctx)?, eval_expr(value, ctx)?)))
                .collect::<TranspileResult<Vec<_>>>()?;
            RuntimeValue::map_bounded(values, &ctx.bounds)
        }
        Expr::SeqEmpty => RuntimeValue::seq_bounded(Vec::new(), &ctx.bounds),
        Expr::SetEmpty => RuntimeValue::set_bounded(Vec::new(), &ctx.bounds),
        Expr::MapEmpty => RuntimeValue::map_bounded(Vec::new(), &ctx.bounds),
        Expr::Call { func, args } => {
            // Special case: Set::new(|x| predicate) — evaluate predicate over int domain
            if path_name(func) == "Set::new" && args.len() == 1 {
                if let Expr::Closure { params, body } = &args[0] {
                    return eval_set_new_with_closure(params, body, ctx);
                }
            }
            // Special case: Map::new(domain, |key| value) — evaluate closure per domain element
            if path_name(func) == "Map::new" && args.len() == 2 {
                if let Expr::Closure { params, body } = &args[1] {
                    let domain = eval_expr(&args[0], ctx)?;
                    return eval_map_new_with_closure(&domain, params, body, ctx);
                }
            }

            let args = args
                .iter()
                .map(|arg| eval_expr(arg, ctx))
                .collect::<TranspileResult<Vec<_>>>()?;
            if let Some(value) = eval_builtin_static_call(func, &args, ctx.bounds)? {
                return Ok(value);
            }
            if let Some(evaluator) = ctx.call_evaluator {
                return evaluator(func, &args);
            }
            Err(unsupported_construct(
                format!("call `{}` without call evaluator hook", path_name(func)).as_str(),
            ))
        }
        Expr::MethodCall {
            receiver,
            method,
            args,
        } => {
            // Special case: Set.map(|x| expr) — evaluate closure per element
            if method == "map" && args.len() == 1 {
                if let Expr::Closure { params, body } = &args[0] {
                    let receiver = eval_expr(receiver, ctx)?;
                    return eval_set_map_with_closure(&receiver, params, body, ctx);
                }
            }

            let receiver = eval_expr(receiver, ctx)?;
            let args = args
                .iter()
                .map(|arg| eval_expr(arg, ctx))
                .collect::<TranspileResult<Vec<_>>>()?;

            if let Some(value) = eval_builtin_method(&receiver, method, &args, ctx.bounds)? {
                return Ok(value);
            }
            if let Some(evaluator) = ctx.method_evaluator {
                return evaluator(&receiver, method, &args);
            }
            Err(unsupported_construct(
                format!("method call `.{}(...)`", method).as_str(),
            ))
        }
        Expr::View(inner) => eval_expr(inner, ctx),
        Expr::Cast(inner, ty) => cast_value(eval_expr(inner, ctx)?, ty),
        Expr::Ident(name) => {
            if let Some(value) = ctx.bindings.get(name) {
                return Ok(value.clone());
            }
            if let Some((ty, variant)) = split_variant_path(name) {
                return RuntimeValue::enum_value(ty, variant, Vec::new());
            }
            Err(type_error(
                format!("Unknown evaluator variable `{}`.", name).as_str(),
            ))
        }
        Expr::Literal(lit) => Ok(match lit {
            crate::ast::Literal::Bool(v) => RuntimeValue::Bool(*v),
            crate::ast::Literal::Int(v) => RuntimeValue::Int(*v),
            crate::ast::Literal::String(v) => RuntimeValue::String(v.clone()),
        }),
        Expr::Binary(lhs, op, rhs) => {
            // Short-circuit evaluation for logical operators
            if *op == crate::ast::BinOp::And {
                let lhs_val = eval_expr(lhs, ctx)?;
                if lhs_val == RuntimeValue::Bool(false) {
                    return Ok(RuntimeValue::Bool(false));
                }
                let rhs_val = eval_expr(rhs, ctx)?;
                return eval_binary(&lhs_val, *op, &rhs_val);
            }
            if *op == crate::ast::BinOp::Or {
                let lhs_val = eval_expr(lhs, ctx)?;
                if lhs_val == RuntimeValue::Bool(true) {
                    return Ok(RuntimeValue::Bool(true));
                }
                let rhs_val = eval_expr(rhs, ctx)?;
                return eval_binary(&lhs_val, *op, &rhs_val);
            }
            let lhs = eval_expr(lhs, ctx)?;
            let rhs = eval_expr(rhs, ctx)?;
            eval_binary(&lhs, *op, &rhs)
        }
        Expr::Unary(op, inner) => {
            let inner = eval_expr(inner, ctx)?;
            eval_unary(*op, &inner)
        }
        Expr::Forall { vars, body, .. } => eval_quantifier(vars, body, ctx, QuantifierKind::Forall),
        Expr::Exists { vars, body } => eval_quantifier(vars, body, ctx, QuantifierKind::Exists),
        Expr::Choose { vars, body } => {
            // Choose: find any value satisfying the predicate
            eval_choose(vars, body, ctx)
        }
        Expr::Match { scrutinee, arms } => eval_match_expr(scrutinee, arms, ctx),
        Expr::Closure { params: _, body: _ } => {
            // Closures are used in Map::new(domain, |x| val) style expressions.
            // For model checking, closures should be handled at the call site.
            Err(type_error(
                "Closure expressions (|...| ...) are not directly evaluable in model-check mode. \
                 They should be used only in Map::new or similar collection constructors.",
            ))
        }
    }
}

#[derive(Clone, Copy)]
enum QuantifierKind {
    Forall,
    Exists,
}

impl QuantifierKind {
    fn label(self) -> &'static str {
        match self {
            QuantifierKind::Forall => "forall",
            QuantifierKind::Exists => "exists",
        }
    }
}

fn eval_quantifier(
    vars: &[Binding],
    body: &Expr,
    ctx: &EvalContext<'_>,
    kind: QuantifierKind,
) -> TranspileResult<RuntimeValue> {
    if vars.is_empty() {
        let result = expect_bool(&eval_expr(body, ctx)?, "quantifier body")?;
        return Ok(RuntimeValue::Bool(result));
    }

    let domain_evaluator = ctx.quantifier_domain_evaluator.ok_or_else(|| {
        unsupported_construct(
            format!("{} quantifier without domain resolver hook", kind.label()).as_str(),
        )
    })?;
    let result = eval_quantifier_bindings(vars, 0, body, ctx, kind, domain_evaluator)?;
    Ok(RuntimeValue::Bool(result))
}

fn eval_quantifier_bindings(
    vars: &[Binding],
    idx: usize,
    body: &Expr,
    ctx: &EvalContext<'_>,
    kind: QuantifierKind,
    domain_evaluator: &QuantifierDomainEvaluator<'_>,
) -> TranspileResult<bool> {
    if idx == vars.len() {
        return expect_bool(
            &eval_expr(body, ctx)?,
            match kind {
                QuantifierKind::Forall => "forall body",
                QuantifierKind::Exists => "exists body",
            },
        );
    }

    let binding = &vars[idx];
    let Pattern::Ident(name) = &binding.pattern else {
        return Err(unsupported_construct(
            format!("{} quantifier with non-identifier binding", kind.label()).as_str(),
        ));
    };
    let domain = domain_evaluator(binding)?;
    if domain.is_empty() {
        return Ok(matches!(kind, QuantifierKind::Forall));
    }

    match kind {
        QuantifierKind::Forall => {
            for value in domain {
                let nested = ctx.child_with_binding(name.clone(), value);
                if !eval_quantifier_bindings(vars, idx + 1, body, &nested, kind, domain_evaluator)?
                {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        QuantifierKind::Exists => {
            for value in domain {
                let nested = ctx.child_with_binding(name.clone(), value);
                if eval_quantifier_bindings(vars, idx + 1, body, &nested, kind, domain_evaluator)? {
                    return Ok(true);
                }
            }
            Ok(false)
        }
    }
}

/// Evaluate a CHOOSE expression: find any value in the domain satisfying the predicate.
/// Returns the first satisfying value, or an error if none exists.
fn eval_choose(
    vars: &[Binding],
    body: &Expr,
    ctx: &EvalContext<'_>,
) -> TranspileResult<RuntimeValue> {
    if vars.is_empty() {
        return Err(unsupported_construct("CHOOSE with no bound variables"));
    }

    let domain_evaluator = ctx.quantifier_domain_evaluator.ok_or_else(|| {
        unsupported_construct("CHOOSE quantifier without domain resolver hook")
    })?;

    // Default untyped choose bindings to `int` (same as quantifier default)
    let vars_with_types: Vec<Binding> = vars
        .iter()
        .map(|b| {
            if b.ty.is_none() {
                Binding {
                    pattern: b.pattern.clone(),
                    ty: Some(crate::ast::Type::Int),
                    variable_mode: b.variable_mode.clone(),
                }
            } else {
                b.clone()
            }
        })
        .collect();

    eval_choose_bindings(&vars_with_types, 0, body, ctx, domain_evaluator)
}

fn eval_choose_bindings(
    vars: &[Binding],
    idx: usize,
    body: &Expr,
    ctx: &EvalContext<'_>,
    domain_evaluator: &QuantifierDomainEvaluator<'_>,
) -> TranspileResult<RuntimeValue> {
    if idx == vars.len() {
        let satisfied = expect_bool(&eval_expr(body, ctx)?, "CHOOSE body")?;
        if satisfied {
            // Return the value of the first (outermost) bound variable
            let Pattern::Ident(name) = &vars[0].pattern else {
                return Err(unsupported_construct("CHOOSE with non-identifier binding"));
            };
            return ctx.bindings.get(name).cloned().ok_or_else(|| {
                type_error("CHOOSE variable not found in context")
            });
        }
        return Err(type_error("CHOOSE: no satisfying value found"));
    }

    let binding = &vars[idx];
    let Pattern::Ident(name) = &binding.pattern else {
        return Err(unsupported_construct("CHOOSE with non-identifier binding"));
    };
    let domain = domain_evaluator(binding)?;

    for value in domain {
        let nested = ctx.child_with_binding(name.clone(), value);
        match eval_choose_bindings(vars, idx + 1, body, &nested, domain_evaluator) {
            Ok(result) => return Ok(result),
            Err(_) => continue, // try next value
        }
    }
    Err(type_error("CHOOSE: no satisfying value found in domain"))
}

fn eval_struct_expr(
    name: &Path,
    fields: &[(String, Expr)],
    ctx: &EvalContext<'_>,
) -> TranspileResult<RuntimeValue> {
    let mut base_expr = None;
    let mut resolved = Vec::with_capacity(fields.len());
    for (field, value_expr) in fields {
        if field == ".." {
            if base_expr.is_some() {
                return Err(type_error(
                    "struct update expression must contain at most one `..base` entry.",
                ));
            }
            base_expr = Some(value_expr);
            continue;
        }
        resolved.push((field.clone(), eval_expr(value_expr, ctx)?));
    }

    if let Some(base_expr) = base_expr {
        let expected_name = if name.segments.is_empty() {
            None
        } else {
            Some(name)
        };
        let base = eval_expr(base_expr, ctx)?;
        return apply_struct_update(expected_name, base, resolved);
    }

    let ty_or_variant = path_name(name);
    if let Some((ty, variant)) = split_variant_path(&ty_or_variant) {
        RuntimeValue::enum_value(ty, variant, resolved)
    } else {
        RuntimeValue::struct_value(ty_or_variant, resolved)
    }
}

fn eval_struct_update_expr(
    name: Option<&Path>,
    base: &Expr,
    fields: &[(String, Expr)],
    ctx: &EvalContext<'_>,
) -> TranspileResult<RuntimeValue> {
    let base = eval_expr(base, ctx)?;
    let mut resolved = Vec::with_capacity(fields.len());
    for (field, value_expr) in fields {
        if field == ".." {
            return Err(type_error(
                "struct update fields must not contain nested `..base` entries.",
            ));
        }
        resolved.push((field.clone(), eval_expr(value_expr, ctx)?));
    }
    apply_struct_update(name, base, resolved)
}

fn apply_struct_update(
    expected_name: Option<&Path>,
    base: RuntimeValue,
    updates: Vec<(String, RuntimeValue)>,
) -> TranspileResult<RuntimeValue> {
    match base {
        RuntimeValue::Struct { ty, mut fields, .. } => {
            validate_struct_update_target(expected_name, &ty, None)?;
            for (field, value) in updates {
                let sym = Symbol::intern(&field);
                if !fields.contains_key(&sym) {
                    return Err(type_error(
                        format!(
                            "struct update field `{}` does not exist on struct `{}`.",
                            field, ty
                        )
                        .as_str(),
                    ));
                }
                fields.insert(sym, value);
            }
            Ok(RuntimeValue::struct_value_sym(ty, fields))
        }
        RuntimeValue::Enum {
            ty,
            variant,
            mut fields,
            ..
        } => {
            validate_struct_update_target(expected_name, &ty, Some(&variant))?;
            for (field, value) in updates {
                let sym = Symbol::intern(&field);
                if !fields.contains_key(&sym) {
                    return Err(type_error(
                        format!(
                            "struct update field `{}` does not exist on enum variant `{}::{}`.",
                            field, ty, variant
                        )
                        .as_str(),
                    ));
                }
                fields.insert(sym, value);
            }
            Ok(RuntimeValue::enum_value_sym(ty, variant, fields))
        }
        other => Err(type_error(
            format!(
                "struct update base expects struct/enum value, got `{}`.",
                other.canonical_key()
            )
            .as_str(),
        )),
    }
}

fn validate_struct_update_target(
    expected_name: Option<&Path>,
    runtime_ty: &str,
    runtime_variant: Option<&str>,
) -> TranspileResult<()> {
    let Some(expected_name) = expected_name else {
        return Ok(());
    };
    if expected_name.segments.is_empty() {
        return Ok(());
    }

    let matches = match runtime_variant {
        Some(runtime_variant) => {
            path_matches_runtime_type(expected_name, runtime_ty)
                || path_matches_enum_variant(expected_name, runtime_ty, runtime_variant)
        }
        None => path_matches_runtime_type(expected_name, runtime_ty),
    };
    if matches {
        return Ok(());
    }

    let expected = path_name(expected_name);
    let actual = match runtime_variant {
        Some(runtime_variant) => format!("{}::{}", runtime_ty, runtime_variant),
        None => runtime_ty.to_string(),
    };
    Err(type_error(
        format!(
            "struct update type mismatch: expected `{}`, got `{}`.",
            expected, actual
        )
        .as_str(),
    ))
}

fn eval_match_expr(
    scrutinee: &Expr,
    arms: &[MatchArm],
    ctx: &EvalContext<'_>,
) -> TranspileResult<RuntimeValue> {
    let scrutinee_value = eval_expr(scrutinee, ctx)?;

    for arm in arms {
        let mut bindings = BTreeMap::new();
        if !match_pattern(&arm.pattern, &scrutinee_value, &mut bindings)? {
            continue;
        }

        let mut nested = ctx.clone();
        for (name, value) in bindings {
            nested = nested.child_with_binding(name, value);
        }

        if let Some(guard) = &arm.guard {
            if !expect_bool(&eval_expr(guard, &nested)?, "match guard")? {
                continue;
            }
        }

        return eval_expr(&arm.body, &nested);
    }

    Err(type_error("match expression has no matching arm."))
}

fn match_pattern(
    pattern: &Pattern,
    value: &RuntimeValue,
    bindings: &mut BTreeMap<String, RuntimeValue>,
) -> TranspileResult<bool> {
    match pattern {
        Pattern::Wildcard => Ok(true),
        Pattern::Ident(name) => {
            if let Some(existing) = bindings.get(name) {
                Ok(existing == value)
            } else {
                bindings.insert(name.clone(), value.clone());
                Ok(true)
            }
        }
        Pattern::Literal(lit) => Ok(match_literal_pattern(lit, value)),
        Pattern::Tuple(patterns) => {
            let RuntimeValue::Tuple(items) = value else {
                return Ok(false);
            };
            if patterns.len() != items.len() {
                return Ok(false);
            }

            for (pattern, item) in patterns.iter().zip(items.iter()) {
                if !match_pattern(pattern, item, bindings)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        Pattern::Struct { name, fields } => match value {
            RuntimeValue::Struct {
                ty,
                fields: runtime_fields,
                ..
            } => {
                if !path_matches_runtime_type(name, ty) {
                    return Ok(false);
                }
                match_named_pattern_fields(fields, runtime_fields, bindings)
            }
            RuntimeValue::Enum {
                ty,
                variant,
                fields: runtime_fields,
                ..
            } => {
                if !path_matches_enum_variant(name, ty, variant) {
                    return Ok(false);
                }
                match_named_pattern_fields(fields, runtime_fields, bindings)
            }
            _ => Ok(false),
        },
        Pattern::Variant { name, fields } => {
            let RuntimeValue::Enum {
                ty,
                variant,
                fields: runtime_fields,
                ..
            } = value
            else {
                return Ok(false);
            };
            if !path_matches_enum_variant(name, ty, variant) {
                return Ok(false);
            }
            match_variant_pattern_fields(fields, runtime_fields, bindings)
        }
    }
}

fn match_named_pattern_fields(
    fields: &[(String, Pattern)],
    runtime_fields: &crate::modelcheck::value::NamedFields,
    bindings: &mut BTreeMap<String, RuntimeValue>,
) -> TranspileResult<bool> {
    for (field_name, field_pattern) in fields {
        let sym = Symbol::intern(field_name);
        let Some(field_value) = runtime_fields.get(&sym) else {
            return Ok(false);
        };
        if !match_pattern(field_pattern, field_value, bindings)? {
            return Ok(false);
        }
    }
    Ok(true)
}

fn match_variant_pattern_fields(
    fields: &[Pattern],
    runtime_fields: &crate::modelcheck::value::NamedFields,
    bindings: &mut BTreeMap<String, RuntimeValue>,
) -> TranspileResult<bool> {
    if fields.len() != runtime_fields.len() {
        return Ok(false);
    }

    for (idx, field_pattern) in fields.iter().enumerate() {
        let indexed_key = Symbol::intern(&format!("_{idx}"));
        let plain_key = Symbol::intern(&idx.to_string());
        let Some(field_value) = runtime_fields
            .get(&indexed_key)
            .or_else(|| runtime_fields.get(&plain_key))
        else {
            return Ok(false);
        };
        if !match_pattern(field_pattern, field_value, bindings)? {
            return Ok(false);
        }
    }
    Ok(true)
}

fn match_literal_pattern(lit: &crate::ast::Literal, value: &RuntimeValue) -> bool {
    match lit {
        crate::ast::Literal::Bool(expected) => {
            matches!(value, RuntimeValue::Bool(actual) if actual == expected)
        }
        crate::ast::Literal::Int(expected) => match value {
            RuntimeValue::Int(actual) => actual == expected,
            RuntimeValue::Nat(actual) => *expected >= 0 && (*actual as i128) == *expected,
            _ => false,
        },
        crate::ast::Literal::String(expected) => {
            matches!(value, RuntimeValue::String(actual) if actual == expected)
        }
    }
}

fn path_matches_runtime_type(pattern_path: &Path, runtime_ty: &str) -> bool {
    normalized_path_segments(pattern_path) == normalized_runtime_path_segments(runtime_ty)
}

fn path_matches_enum_variant(pattern_path: &Path, runtime_ty: &str, runtime_variant: &str) -> bool {
    let pattern_segments = normalized_path_segments(pattern_path);
    if pattern_segments.is_empty() {
        return false;
    }

    if pattern_segments.len() == 1 {
        return pattern_segments[0] == runtime_variant;
    }

    let Some(pattern_variant) = pattern_segments.last() else {
        return false;
    };
    if pattern_variant != runtime_variant {
        return false;
    }

    let runtime_ty_segments = normalized_runtime_path_segments(runtime_ty);
    pattern_segments[..pattern_segments.len() - 1] == runtime_ty_segments[..]
}

fn compare_numbers<F>(
    lhs: &Expr,
    rhs: &Expr,
    ctx: &EvalContext<'_>,
    cmp: F,
) -> TranspileResult<RuntimeValue>
where
    F: Fn(i128, i128) -> bool,
{
    let lhs = expect_number(&eval_expr(lhs, ctx)?, "comparison lhs")?;
    let rhs = expect_number(&eval_expr(rhs, ctx)?, "comparison rhs")?;
    Ok(RuntimeValue::Bool(cmp(lhs, rhs)))
}

fn eval_builtin_method(
    receiver: &RuntimeValue,
    method: &str,
    args: &[RuntimeValue],
    bounds: RuntimeCollectionBounds,
) -> TranspileResult<Option<RuntimeValue>> {
    match method {
        "len" => {
            if !args.is_empty() {
                return Err(type_error("`.len()` expects zero arguments."));
            }
            let len = match receiver {
                RuntimeValue::Seq(items) => items.len(),
                RuntimeValue::Set(items) => items.len(),
                RuntimeValue::Map(entries) => entries.len(),
                RuntimeValue::Tuple(items) => items.len(),
                RuntimeValue::String(value) => value.len(),
                other => {
                    return Err(type_error(
                        format!(
                            "`.len()` expects Seq/Set/Map/Tuple/String, got `{}`.",
                            other.canonical_key()
                        )
                        .as_str(),
                    ))
                }
            };
            Ok(Some(RuntimeValue::Nat(len as u64)))
        }
        "contains" => {
            if args.len() != 1 {
                return Err(type_error("`.contains(...)` expects one argument."));
            }
            let needle = &args[0];
            let present = match receiver {
                RuntimeValue::Set(items) => items.contains(needle),
                RuntimeValue::Seq(items) => items.iter().any(|item| item == needle),
                other => {
                    return Err(type_error(
                        format!(
                            "`.contains(...)` expects Set/Seq receiver, got `{}`.",
                            other.canonical_key()
                        )
                        .as_str(),
                    ))
                }
            };
            Ok(Some(RuntimeValue::Bool(present)))
        }
        "contains_key" => {
            if args.len() != 1 {
                return Err(type_error("`.contains_key(...)` expects one argument."));
            }
            let needle = &args[0];
            let present = match receiver {
                RuntimeValue::Map(entries) => entries.contains_key(needle),
                other => {
                    return Err(type_error(
                        format!(
                            "`.contains_key(...)` expects Map receiver, got `{}`.",
                            other.canonical_key()
                        )
                        .as_str(),
                    ))
                }
            };
            Ok(Some(RuntimeValue::Bool(present)))
        }
        "dom" => {
            if !args.is_empty() {
                return Err(type_error("`.dom()` expects zero arguments."));
            }
            match receiver {
                RuntimeValue::Map(entries) => {
                    let keys = entries.keys().cloned().collect();
                    Ok(Some(RuntimeValue::Set(keys)))
                }
                other => Err(type_error(
                    format!(
                        "`.dom()` expects Map receiver, got `{}`.",
                        other.canonical_key()
                    )
                    .as_str(),
                )),
            }
        }
        "insert" => {
            match receiver {
                RuntimeValue::Set(items) => {
                    if args.len() != 1 {
                        return Err(type_error("Set `.insert(...)` expects one argument."));
                    }
                    let mut next = items.clone();
                    next.insert(args[0].clone());
                    Ok(Some(RuntimeValue::Set(next)))
                }
                RuntimeValue::Map(entries) => {
                    if args.len() != 2 {
                        return Err(type_error("Map `.insert(key, value)` expects two arguments."));
                    }
                    let mut next = entries.clone();
                    next.insert(args[0].clone(), args[1].clone());
                    Ok(Some(RuntimeValue::Map(next)))
                }
                other => Err(type_error(
                    format!(
                        "`.insert(...)` expects Set or Map receiver, got `{}`.",
                        other.canonical_key()
                    )
                    .as_str(),
                )),
            }
        }
        "remove" => {
            if args.len() != 1 {
                return Err(type_error("`.remove(...)` expects one argument."));
            }
            match receiver {
                RuntimeValue::Set(items) => {
                    let mut next = items.clone();
                    next.remove(&args[0]);
                    Ok(Some(RuntimeValue::Set(next)))
                }
                other => Err(type_error(
                    format!(
                        "`.remove(...)` currently expects Set receiver, got `{}`.",
                        other.canonical_key()
                    )
                    .as_str(),
                )),
            }
        }
        "union" => {
            if args.len() != 1 {
                return Err(type_error("`.union(...)` expects one argument."));
            }
            match (receiver, &args[0]) {
                (RuntimeValue::Set(a), RuntimeValue::Set(b)) => {
                    let result: std::collections::BTreeSet<_> = a.union(b).cloned().collect();
                    Ok(Some(RuntimeValue::Set(result)))
                }
                _ => Err(type_error("`.union(...)` expects Set receiver and Set argument.")),
            }
        }
        "difference" => {
            if args.len() != 1 {
                return Err(type_error("`.difference(...)` expects one argument."));
            }
            match (receiver, &args[0]) {
                (RuntimeValue::Set(a), RuntimeValue::Set(b)) => {
                    let result: std::collections::BTreeSet<_> = a.difference(b).cloned().collect();
                    Ok(Some(RuntimeValue::Set(result)))
                }
                _ => Err(type_error("`.difference(...)` expects Set receiver and Set argument.")),
            }
        }
        "intersect" | "intersection" => {
            if args.len() != 1 {
                return Err(type_error("`.intersect(...)` expects one argument."));
            }
            match (receiver, &args[0]) {
                (RuntimeValue::Set(a), RuntimeValue::Set(b)) => {
                    let result: std::collections::BTreeSet<_> = a.intersection(b).cloned().collect();
                    Ok(Some(RuntimeValue::Set(result)))
                }
                _ => Err(type_error("`.intersect(...)` expects Set receiver and Set argument.")),
            }
        }
        "push" => {
            if args.len() != 1 {
                return Err(type_error("`.push(...)` expects one argument."));
            }
            match receiver {
                RuntimeValue::Seq(items) => {
                    let mut next = items.clone();
                    next.push(args[0].clone());
                    Ok(Some(RuntimeValue::seq_bounded(next, &bounds)?))
                }
                _ => Err(type_error("`.push(...)` expects Seq receiver.")),
            }
        }
        _ => Ok(None),
    }
}

fn eval_builtin_static_call(
    func: &Path,
    args: &[RuntimeValue],
    bounds: RuntimeCollectionBounds,
) -> TranspileResult<Option<RuntimeValue>> {
    if args.is_empty() {
        if let Some(value) = eval_arbitrary_call(path_name(func).as_str(), bounds)? {
            return Ok(Some(value));
        }
    }

    let segments = normalized_path_segments(func);
    if segments.len() != 2 {
        return Ok(None);
    }
    if !args.is_empty() {
        return Ok(None);
    }
    match (segments[0].as_str(), segments[1].as_str()) {
        ("Seq", "empty") => Ok(Some(RuntimeValue::seq_bounded(Vec::new(), &bounds)?)),
        ("Set", "empty") => Ok(Some(RuntimeValue::set_bounded(Vec::new(), &bounds)?)),
        ("Map", "empty") => Ok(Some(RuntimeValue::map_bounded(Vec::new(), &bounds)?)),
        _ => Ok(None),
    }
}

fn eval_arbitrary_call(
    raw_path: &str,
    bounds: RuntimeCollectionBounds,
) -> TranspileResult<Option<RuntimeValue>> {
    let has_arbitrary = raw_path.contains("arbitrary::<")
        || raw_path
            .split("::")
            .last()
            .map(|segment| segment.trim() == "arbitrary")
            .unwrap_or(false);
    if !has_arbitrary {
        return Ok(None);
    }

    let ty_hint = raw_path.find("arbitrary::<").and_then(|idx| {
        let rest = &raw_path[idx + "arbitrary::<".len()..];
        rest.rfind('>').map(|end| rest[..end].trim().to_string())
    });

    let value = match ty_hint.as_deref() {
        Some("bool") => RuntimeValue::Bool(false),
        Some("nat") | Some("u64") | Some("u32") | Some("u16") | Some("u8") | Some("usize") => {
            RuntimeValue::Nat(0)
        }
        Some("Seq<char>") | Some("vstd::seq::Seq<char>") => RuntimeValue::String(String::new()),
        Some(ty) if ty.starts_with("Seq<") || ty.contains("::Seq<") => {
            RuntimeValue::seq_bounded(Vec::new(), &bounds)?
        }
        Some(ty) if ty.starts_with("Set<") || ty.contains("::Set<") => {
            RuntimeValue::set_bounded(Vec::new(), &bounds)?
        }
        Some(ty) if ty.starts_with("Map<") || ty.contains("::Map<") => {
            RuntimeValue::map_bounded(Vec::new(), &bounds)?
        }
        // Unknown/opaque type arguments default to `0int` to keep
        // generated helper predicates evaluable under bounded search.
        _ => RuntimeValue::Int(0),
    };
    Ok(Some(value))
}

/// Evaluate Map::new(domain_set, |key| value) by applying the closure to each domain element.
/// Evaluate `Set::new(|x: T| predicate)` — a set comprehension.
///
/// Enumerates the int domain from the model config and collects values
/// where the predicate closure returns true. This is how TLA+ `a..b`
/// range expressions (translated to `Set::new(|x: int| a <= x && x <= b)`)
/// are evaluated.
fn eval_set_new_with_closure(
    params: &[crate::ast::Binding],
    body: &Expr,
    ctx: &EvalContext<'_>,
) -> TranspileResult<RuntimeValue> {
    if params.is_empty() {
        return Err(type_error("Set::new closure must have at least one parameter."));
    }

    let param_name = params[0].name().ok_or_else(|| {
        type_error("Set::new closure parameter must be a named identifier.")
    })?;

    // Try to determine the domain to enumerate from the closure body.
    // For `|x: int| lo <= x && x <= hi`, we extract lo and hi and enumerate.
    // Fallback: enumerate the configured int domain.
    let candidates = extract_range_bounds_from_closure(param_name, body, ctx);

    let int_values: Vec<i128> = if let Some((lo, hi)) = candidates {
        (lo..=hi).collect()
    } else {
        // Fallback: use the full int domain from bounds context
        // We use a reasonable default range
        (-10..=100).collect()
    };

    let mut elements = Vec::new();
    for val in &int_values {
        let rv = RuntimeValue::Int(*val);
        let mut inner_ctx = ctx.clone();
        inner_ctx.bindings.insert(param_name.to_string(), rv.clone());
        match eval_expr(body, &inner_ctx) {
            Ok(RuntimeValue::Bool(true)) => {
                elements.push(rv);
            }
            Ok(RuntimeValue::Bool(false)) => {}
            Ok(_) => {
                return Err(type_error(
                    "Set::new closure must return bool.",
                ));
            }
            Err(_) => {
                // If evaluation fails for this value, skip it
            }
        }
    }

    RuntimeValue::set_bounded(elements, &ctx.bounds)
}

/// Try to extract constant range bounds from a Set::new closure like `|x: int| lo <= x && x <= hi`.
fn extract_range_bounds_from_closure(
    param: &str,
    body: &Expr,
    ctx: &EvalContext<'_>,
) -> Option<(i128, i128)> {
    // Pattern: Binary(Le(lo_expr, param), And, Le(param, hi_expr))
    if let Expr::Binary(left, crate::ast::BinOp::And, right) = body {
        let lo = extract_lower_bound(param, left, ctx);
        let hi = extract_upper_bound(param, right, ctx);
        if let (Some(lo), Some(hi)) = (lo, hi) {
            return Some((lo, hi));
        }
        // Try reversed order
        let lo = extract_lower_bound(param, right, ctx);
        let hi = extract_upper_bound(param, left, ctx);
        if let (Some(lo), Some(hi)) = (lo, hi) {
            return Some((lo, hi));
        }
    }
    None
}

fn extract_lower_bound(param: &str, expr: &Expr, ctx: &EvalContext<'_>) -> Option<i128> {
    // Pattern: lo <= param
    if let Expr::Le(lo_expr, rhs) = expr {
        if is_ident(rhs, param) {
            return eval_to_int(lo_expr, ctx);
        }
    }
    None
}

fn extract_upper_bound(param: &str, expr: &Expr, ctx: &EvalContext<'_>) -> Option<i128> {
    // Pattern: param <= hi
    if let Expr::Le(lhs, hi_expr) = expr {
        if is_ident(lhs, param) {
            return eval_to_int(hi_expr, ctx);
        }
    }
    None
}

fn is_ident(expr: &Expr, name: &str) -> bool {
    matches!(expr, Expr::Ident(n) if n == name)
}

fn eval_to_int(expr: &Expr, ctx: &EvalContext<'_>) -> Option<i128> {
    match eval_expr(expr, ctx) {
        Ok(RuntimeValue::Int(v)) => Some(v),
        Ok(RuntimeValue::Nat(v)) => Some(v as i128),
        _ => None,
    }
}

/// Evaluate `set.map(|x| expr)` — applies closure to each element, returns new Set.
fn eval_set_map_with_closure(
    receiver: &RuntimeValue,
    params: &[crate::ast::Binding],
    body: &Expr,
    ctx: &EvalContext<'_>,
) -> TranspileResult<RuntimeValue> {
    let elements = match receiver {
        RuntimeValue::Set(items) => items.iter().cloned().collect::<Vec<_>>(),
        _ => {
            return Err(type_error(
                "`.map(|x| ...)` receiver must be a Set.",
            ));
        }
    };

    if params.is_empty() {
        return Err(type_error("`.map(|x| ...)` closure must have at least one parameter."));
    }

    let param_name = params[0].name().ok_or_else(|| {
        type_error("`.map(|x| ...)` closure parameter must be a named identifier.")
    })?;

    let mut result = std::collections::BTreeSet::new();
    for elem in &elements {
        let mut inner_ctx = ctx.clone();
        inner_ctx.bindings.insert(param_name.to_string(), elem.clone());
        let value = eval_expr(body, &inner_ctx)?;
        result.insert(value);
    }

    Ok(RuntimeValue::Set(result))
}

fn eval_map_new_with_closure(
    domain: &RuntimeValue,
    params: &[crate::ast::Binding],
    body: &Expr,
    ctx: &EvalContext<'_>,
) -> TranspileResult<RuntimeValue> {
    // Domain should be a Set
    let keys = match domain {
        RuntimeValue::Set(elements) => elements.iter().cloned().collect::<Vec<_>>(),
        _ => {
            return Err(type_error(
                "Map::new first argument must be a Set (domain).",
            ));
        }
    };

    if params.is_empty() {
        return Err(type_error("Map::new closure must have at least one parameter."));
    }

    let param_name = params[0].name().ok_or_else(|| {
        type_error("Map::new closure parameter must be a named identifier.")
    })?;

    let mut entries = Vec::new();
    for key in &keys {
        let mut inner_ctx = ctx.clone();
        inner_ctx.bindings.insert(param_name.to_string(), key.clone());
        let value = eval_expr(body, &inner_ctx)?;
        entries.push((key.clone(), value));
    }

    RuntimeValue::map_bounded(entries, &ctx.bounds)
}

fn cast_value(value: RuntimeValue, ty: &Type) -> TranspileResult<RuntimeValue> {
    match ty {
        Type::Int => Ok(RuntimeValue::Int(expect_number(&value, "cast to int")?)),
        Type::Nat => {
            let v = expect_number(&value, "cast to nat")?;
            if v < 0 {
                return Err(type_error("Cannot cast negative value to nat."));
            }
            Ok(RuntimeValue::Nat(v as u64))
        }
        Type::Bool => Ok(RuntimeValue::Bool(expect_bool(&value, "cast to bool")?)),
        _ => Err(unsupported_construct(
            format!("cast to type `{:?}`", ty).as_str(),
        )),
    }
}

fn eval_binary(lhs: &RuntimeValue, op: BinOp, rhs: &RuntimeValue) -> TranspileResult<RuntimeValue> {
    match op {
        BinOp::Add => Ok(RuntimeValue::Int(
            expect_number(lhs, "addition lhs")? + expect_number(rhs, "addition rhs")?,
        )),
        BinOp::Sub => Ok(RuntimeValue::Int(
            expect_number(lhs, "subtraction lhs")? - expect_number(rhs, "subtraction rhs")?,
        )),
        BinOp::Mul => Ok(RuntimeValue::Int(
            expect_number(lhs, "multiplication lhs")? * expect_number(rhs, "multiplication rhs")?,
        )),
        BinOp::Div => {
            let rhs = expect_number(rhs, "division rhs")?;
            if rhs == 0 {
                return Err(type_error("Division by zero."));
            }
            Ok(RuntimeValue::Int(expect_number(lhs, "division lhs")? / rhs))
        }
        BinOp::Mod => {
            let rhs = expect_number(rhs, "modulo rhs")?;
            if rhs == 0 {
                return Err(type_error("Modulo by zero."));
            }
            Ok(RuntimeValue::Int(expect_number(lhs, "modulo lhs")? % rhs))
        }
        BinOp::And => Ok(RuntimeValue::Bool(
            expect_bool(lhs, "boolean and lhs")? && expect_bool(rhs, "boolean and rhs")?,
        )),
        BinOp::Or => Ok(RuntimeValue::Bool(
            expect_bool(lhs, "boolean or lhs")? || expect_bool(rhs, "boolean or rhs")?,
        )),
        BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor | BinOp::Shl | BinOp::Shr => {
            Err(unsupported_construct("bitwise/shift binary operator"))
        }
    }
}

fn eval_unary(op: UnaryOp, value: &RuntimeValue) -> TranspileResult<RuntimeValue> {
    match op {
        UnaryOp::Not => Ok(RuntimeValue::Bool(!expect_bool(value, "negation operand")?)),
        UnaryOp::Neg => Ok(RuntimeValue::Int(-expect_number(
            value,
            "numeric negation operand",
        )?)),
        UnaryOp::Deref => Ok(value.clone()),
    }
}

fn expect_bool(value: &RuntimeValue, context: &str) -> TranspileResult<bool> {
    match value {
        RuntimeValue::Bool(v) => Ok(*v),
        _ => Err(type_error(
            format!(
                "Evaluator {} expects bool, got `{}`.",
                context,
                value.canonical_key()
            )
            .as_str(),
        )),
    }
}

fn expect_number(value: &RuntimeValue, context: &str) -> TranspileResult<i128> {
    match value {
        RuntimeValue::Int(v) => Ok(*v),
        RuntimeValue::Nat(v) => Ok((*v).into()),
        _ => Err(type_error(
            format!(
                "Evaluator {} expects numeric value, got `{}`.",
                context,
                value.canonical_key()
            )
            .as_str(),
        )),
    }
}

fn expect_index(value: &RuntimeValue, context: &str) -> TranspileResult<usize> {
    let idx = expect_number(value, context)?;
    if idx < 0 {
        return Err(type_error("Index must be non-negative."));
    }
    usize::try_from(idx).map_err(|_| type_error("Index does not fit into usize."))
}

fn path_name(path: &Path) -> String {
    path.segments.join("::")
}

fn normalized_path_segments(path: &Path) -> Vec<String> {
    path.segments
        .iter()
        .flat_map(|segment| {
            let trimmed = if let Some(idx) = segment.find("::<") {
                &segment[..idx]
            } else {
                segment.as_str()
            };
            trimmed
                .split("::")
                .map(|part| part.to_string())
                .collect::<Vec<_>>()
        })
        .collect()
}

fn normalized_runtime_path_segments(path: &str) -> Vec<String> {
    path.split("::")
        .map(|segment| {
            if let Some(idx) = segment.find("::<") {
                segment[..idx].to_string()
            } else {
                segment.to_string()
            }
        })
        .filter(|segment| !segment.is_empty())
        .collect()
}

fn split_variant_path(path: &str) -> Option<(String, String)> {
    let mut segments = path.split("::");
    let first = segments.next()?;
    let mut collected = vec![first.to_string()];
    collected.extend(segments.map(|s| s.to_string()));
    if collected.len() < 2 {
        return None;
    }
    let variant = collected.pop()?;
    let ty = collected.join("::");
    if ty.is_empty() || variant.is_empty() {
        return None;
    }
    Some((ty, variant))
}

fn unsupported_construct(construct: &str) -> TranspileError {
    TranspileError::UnsupportedPattern {
        message: format!("Model-check evaluator does not support `{}`.", construct),
        span: None,
        help: Some(
            "Extend `modelcheck::evaluator` with this construct instead of falling back silently."
                .to_string(),
        ),
    }
}

fn type_error(message: &str) -> TranspileError {
    TranspileError::Config {
        message: format!("Model-check evaluator error: {}", message),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Binding, Literal, MatchArm, Path, Pattern, Type, VariableMode};

    fn test_bounds() -> RuntimeCollectionBounds {
        RuntimeCollectionBounds {
            max_seq_len: 8,
            max_set_len: 8,
            max_map_len: 8,
        }
    }

    #[test]
    fn test_eval_boolean_arithmetic_and_compare() {
        let expr = Expr::Conjunction(vec![
            Expr::Eq(
                Box::new(Expr::Binary(
                    Box::new(Expr::Literal(Literal::Int(1))),
                    BinOp::Add,
                    Box::new(Expr::Literal(Literal::Int(2))),
                )),
                Box::new(Expr::Literal(Literal::Int(3))),
            ),
            Expr::Gt(
                Box::new(Expr::Literal(Literal::Int(5))),
                Box::new(Expr::Literal(Literal::Int(2))),
            ),
        ]);
        let out = eval_expr(&expr, &EvalContext::new(test_bounds())).unwrap();
        assert_eq!(out, RuntimeValue::Bool(true));
    }

    #[test]
    fn test_eval_let_if_and_index() {
        let expr = Expr::Let {
            binding: crate::ast::Binding {
                pattern: Pattern::Ident("xs".to_string()),
                ty: None,
                variable_mode: crate::ast::VariableMode::Exec,
            },
            value: Box::new(Expr::SeqLit(vec![
                Expr::Literal(Literal::Int(10)),
                Expr::Literal(Literal::Int(20)),
            ])),
            body: Box::new(Expr::If {
                cond: Box::new(Expr::Literal(Literal::Bool(true))),
                then_branch: Box::new(Expr::Index(
                    Box::new(Expr::Ident("xs".to_string())),
                    Box::new(Expr::Literal(Literal::Int(1))),
                )),
                else_branch: Some(Box::new(Expr::Literal(Literal::Int(0)))),
            }),
        };
        let out = eval_expr(&expr, &EvalContext::new(test_bounds())).unwrap();
        assert_eq!(out, RuntimeValue::Int(20));
    }

    #[test]
    fn test_eval_arbitrary_call_defaults_by_type_hint() {
        let int_expr = Expr::Call {
            func: Path::single("arbitrary::<int>".to_string()),
            args: vec![],
        };
        let int_out = eval_expr(&int_expr, &EvalContext::new(test_bounds())).unwrap();
        assert_eq!(int_out, RuntimeValue::Int(0));

        let bool_expr = Expr::Call {
            func: Path::single("arbitrary::<bool>".to_string()),
            args: vec![],
        };
        let bool_out = eval_expr(&bool_expr, &EvalContext::new(test_bounds())).unwrap();
        assert_eq!(bool_out, RuntimeValue::Bool(false));

        let seq_expr = Expr::Call {
            func: Path::single("arbitrary::<Seq<int>>".to_string()),
            args: vec![],
        };
        let seq_out = eval_expr(&seq_expr, &EvalContext::new(test_bounds())).unwrap();
        assert_eq!(seq_out, RuntimeValue::Seq(Vec::new()));
    }

    #[test]
    fn test_eval_struct_field_and_methods() {
        let struct_expr = Expr::Field(
            Box::new(Expr::Struct {
                name: Path::single("State".to_string()),
                fields: vec![("count".to_string(), Expr::Literal(Literal::Int(7)))],
            }),
            "count".to_string(),
        );
        let field = eval_expr(&struct_expr, &EvalContext::new(test_bounds())).unwrap();
        assert_eq!(field, RuntimeValue::Int(7));

        let len_expr = Expr::MethodCall {
            receiver: Box::new(Expr::SeqLit(vec![
                Expr::Literal(Literal::Int(1)),
                Expr::Literal(Literal::Int(2)),
            ])),
            method: "len".to_string(),
            args: vec![],
        };
        let len = eval_expr(&len_expr, &EvalContext::new(test_bounds())).unwrap();
        assert_eq!(len, RuntimeValue::Nat(2));

        let contains_expr = Expr::MethodCall {
            receiver: Box::new(Expr::SetLit(vec![
                Expr::Literal(Literal::Int(3)),
                Expr::Literal(Literal::Int(4)),
            ])),
            method: "contains".to_string(),
            args: vec![Expr::Literal(Literal::Int(4))],
        };
        let contains = eval_expr(&contains_expr, &EvalContext::new(test_bounds())).unwrap();
        assert_eq!(contains, RuntimeValue::Bool(true));

        let insert_expr = Expr::MethodCall {
            receiver: Box::new(Expr::SetLit(vec![Expr::Literal(Literal::Int(3))])),
            method: "insert".to_string(),
            args: vec![Expr::Literal(Literal::Int(4))],
        };
        let insert_out = eval_expr(&insert_expr, &EvalContext::new(test_bounds())).unwrap();
        assert_eq!(
            insert_out,
            RuntimeValue::Set(
                [RuntimeValue::Int(3), RuntimeValue::Int(4)]
                    .into_iter()
                    .collect()
            )
        );

        let remove_expr = Expr::MethodCall {
            receiver: Box::new(Expr::SetLit(vec![
                Expr::Literal(Literal::Int(3)),
                Expr::Literal(Literal::Int(4)),
            ])),
            method: "remove".to_string(),
            args: vec![Expr::Literal(Literal::Int(3))],
        };
        let remove_out = eval_expr(&remove_expr, &EvalContext::new(test_bounds())).unwrap();
        assert_eq!(
            remove_out,
            RuntimeValue::Set([RuntimeValue::Int(4)].into_iter().collect())
        );

        let push_expr = Expr::MethodCall {
            receiver: Box::new(Expr::SeqLit(vec![Expr::Literal(Literal::Int(3))])),
            method: "push".to_string(),
            args: vec![Expr::Literal(Literal::Int(4))],
        };
        let push_out = eval_expr(&push_expr, &EvalContext::new(test_bounds())).unwrap();
        assert_eq!(
            push_out,
            RuntimeValue::Seq(vec![RuntimeValue::Int(3), RuntimeValue::Int(4)])
        );
    }

    #[test]
    fn test_eval_call_hook_and_method_hook() {
        let call_hook = |func: &Path, args: &[RuntimeValue]| -> TranspileResult<RuntimeValue> {
            if func.last() == Some("BalLt") {
                let l = match &args[0] {
                    RuntimeValue::Int(v) => *v,
                    _ => 0,
                };
                let r = match &args[1] {
                    RuntimeValue::Int(v) => *v,
                    _ => 0,
                };
                return Ok(RuntimeValue::Bool(l < r));
            }
            Err(type_error("unexpected call"))
        };
        let method_hook = |_receiver: &RuntimeValue,
                           method: &str,
                           _args: &[RuntimeValue]|
         -> TranspileResult<RuntimeValue> {
            if method == "custom_check" {
                return Ok(RuntimeValue::Bool(true));
            }
            Err(type_error("unexpected method"))
        };

        let ctx = EvalContext::new(test_bounds())
            .with_call_evaluator(&call_hook)
            .with_method_evaluator(&method_hook);

        let call_expr = Expr::Call {
            func: Path::single("BalLt".to_string()),
            args: vec![
                Expr::Literal(Literal::Int(1)),
                Expr::Literal(Literal::Int(2)),
            ],
        };
        let call_out = eval_expr(&call_expr, &ctx).unwrap();
        assert_eq!(call_out, RuntimeValue::Bool(true));

        let method_expr = Expr::MethodCall {
            receiver: Box::new(Expr::Literal(Literal::Int(0))),
            method: "custom_check".to_string(),
            args: vec![],
        };
        let method_out = eval_expr(&method_expr, &ctx).unwrap();
        assert_eq!(method_out, RuntimeValue::Bool(true));
    }

    #[test]
    fn test_eval_short_circuit_boolean_connectives() {
        let no_hook_call = Expr::Call {
            func: Path::single("NeverReached".to_string()),
            args: vec![],
        };

        let conjunction = Expr::Conjunction(vec![
            Expr::Literal(Literal::Bool(false)),
            no_hook_call.clone(),
        ]);
        let conjunction_out = eval_expr(&conjunction, &EvalContext::new(test_bounds())).unwrap();
        assert_eq!(conjunction_out, RuntimeValue::Bool(false));

        let disjunction = Expr::Disjunction(vec![
            Expr::Literal(Literal::Bool(true)),
            no_hook_call.clone(),
        ]);
        let disjunction_out = eval_expr(&disjunction, &EvalContext::new(test_bounds())).unwrap();
        assert_eq!(disjunction_out, RuntimeValue::Bool(true));

        let implication = Expr::Implies(
            Box::new(Expr::Literal(Literal::Bool(false))),
            Box::new(no_hook_call),
        );
        let implication_out = eval_expr(&implication, &EvalContext::new(test_bounds())).unwrap();
        assert_eq!(implication_out, RuntimeValue::Bool(true));
    }

    #[test]
    fn test_eval_if_without_else_returns_unit() {
        let expr = Expr::If {
            cond: Box::new(Expr::Literal(Literal::Bool(false))),
            then_branch: Box::new(Expr::Literal(Literal::Int(1))),
            else_branch: None,
        };

        let out = eval_expr(&expr, &EvalContext::new(test_bounds())).unwrap();
        assert_eq!(out, RuntimeValue::Unit);
    }

    #[test]
    fn test_eval_iff_not_and_nat_cast() {
        let iff_expr = Expr::Iff(
            Box::new(Expr::Not(Box::new(Expr::Literal(Literal::Bool(false))))),
            Box::new(Expr::Literal(Literal::Bool(true))),
        );
        let iff_out = eval_expr(&iff_expr, &EvalContext::new(test_bounds())).unwrap();
        assert_eq!(iff_out, RuntimeValue::Bool(true));

        let cast_expr = Expr::Cast(Box::new(Expr::Literal(Literal::Int(5))), Type::Nat);
        let cast_out = eval_expr(&cast_expr, &EvalContext::new(test_bounds())).unwrap();
        assert_eq!(cast_out, RuntimeValue::Nat(5));

        let bad_cast_expr = Expr::Cast(Box::new(Expr::Literal(Literal::Int(-1))), Type::Nat);
        let err = eval_expr(&bad_cast_expr, &EvalContext::new(test_bounds())).unwrap_err();
        assert!(err
            .to_string()
            .contains("Cannot cast negative value to nat"));
    }

    #[test]
    fn test_eval_map_index_and_contains_key() {
        let map_expr = Expr::MapLit(vec![(
            Expr::Literal(Literal::Int(1)),
            Expr::Literal(Literal::String("one".to_string())),
        )]);

        let index_expr = Expr::Index(
            Box::new(map_expr.clone()),
            Box::new(Expr::Literal(Literal::Int(1))),
        );
        let index_out = eval_expr(&index_expr, &EvalContext::new(test_bounds())).unwrap();
        assert_eq!(index_out, RuntimeValue::String("one".to_string()));

        let contains_key_expr = Expr::MethodCall {
            receiver: Box::new(map_expr),
            method: "contains_key".to_string(),
            args: vec![Expr::Literal(Literal::Int(1))],
        };
        let contains_key_out =
            eval_expr(&contains_key_expr, &EvalContext::new(test_bounds())).unwrap();
        assert_eq!(contains_key_out, RuntimeValue::Bool(true));

        let dom_contains_expr = Expr::MethodCall {
            receiver: Box::new(Expr::MethodCall {
                receiver: Box::new(Expr::MapLit(vec![(
                    Expr::Literal(Literal::Int(1)),
                    Expr::Literal(Literal::Bool(true)),
                )])),
                method: "dom".to_string(),
                args: vec![],
            }),
            method: "contains".to_string(),
            args: vec![Expr::Literal(Literal::Int(1))],
        };
        let dom_contains_out =
            eval_expr(&dom_contains_expr, &EvalContext::new(test_bounds())).unwrap();
        assert_eq!(dom_contains_out, RuntimeValue::Bool(true));
    }

    #[test]
    fn test_eval_map_dom_method_returns_key_set() {
        let dom_expr = Expr::MethodCall {
            receiver: Box::new(Expr::MapLit(vec![
                (
                    Expr::Literal(Literal::Int(1)),
                    Expr::Literal(Literal::Bool(true)),
                ),
                (
                    Expr::Literal(Literal::Int(2)),
                    Expr::Literal(Literal::Bool(false)),
                ),
            ])),
            method: "dom".to_string(),
            args: vec![],
        };

        let dom_out = eval_expr(&dom_expr, &EvalContext::new(test_bounds())).unwrap();
        let RuntimeValue::Set(keys) = dom_out else {
            panic!("expected map.dom() to evaluate to a set");
        };
        assert_eq!(keys.len(), 2);
        assert!(keys.contains(&RuntimeValue::Int(1)));
        assert!(keys.contains(&RuntimeValue::Int(2)));
    }

    #[test]
    fn test_eval_map_dom_method_rejects_non_map_receiver() {
        let dom_expr = Expr::MethodCall {
            receiver: Box::new(Expr::SeqLit(vec![Expr::Literal(Literal::Int(1))])),
            method: "dom".to_string(),
            args: vec![],
        };

        let err = eval_expr(&dom_expr, &EvalContext::new(test_bounds())).unwrap_err();
        assert!(err.to_string().contains("`.dom()` expects Map receiver"));
    }

    #[test]
    fn test_eval_ident_resolves_enum_unit_variant_path() {
        let expr = Expr::Ident("LNodeRole::Primary".to_string());
        let out = eval_expr(&expr, &EvalContext::new(test_bounds())).unwrap();
        assert_eq!(
            out,
            RuntimeValue::enum_value("LNodeRole", "Primary", Vec::new()).unwrap()
        );
    }

    #[test]
    fn test_eval_struct_with_path_resolves_enum_payload_constructor() {
        let expr = Expr::Struct {
            name: Path::single("LPBMessage::Replicate".to_string()),
            fields: vec![("val".to_string(), Expr::Literal(Literal::Int(7)))],
        };
        let out = eval_expr(&expr, &EvalContext::new(test_bounds())).unwrap();
        assert_eq!(
            out,
            RuntimeValue::enum_value(
                "LPBMessage",
                "Replicate",
                vec![("val".to_string(), RuntimeValue::Int(7))]
            )
            .unwrap()
        );
    }

    #[test]
    fn test_eval_struct_update_expression_updates_struct_fields() {
        let ctx = EvalContext::new(test_bounds()).child_with_binding(
            "s".to_string(),
            RuntimeValue::struct_value(
                "LState",
                vec![
                    ("x".to_string(), RuntimeValue::Int(0)),
                    ("y".to_string(), RuntimeValue::Bool(true)),
                ],
            )
            .unwrap(),
        );

        let updated = eval_expr(
            &Expr::StructUpdate {
                name: Some(Path::single("LState".to_string())),
                base: Box::new(Expr::Ident("s".to_string())),
                fields: vec![("x".to_string(), Expr::Literal(Literal::Int(9)))],
            },
            &ctx,
        )
        .unwrap();
        assert_eq!(
            updated,
            RuntimeValue::struct_value(
                "LState",
                vec![
                    ("x".to_string(), RuntimeValue::Int(9)),
                    ("y".to_string(), RuntimeValue::Bool(true)),
                ],
            )
            .unwrap()
        );
    }

    #[test]
    fn test_eval_struct_update_parser_form_with_dotdot_base() {
        let ctx = EvalContext::new(test_bounds()).child_with_binding(
            "base".to_string(),
            RuntimeValue::struct_value(
                "LState",
                vec![
                    ("x".to_string(), RuntimeValue::Int(2)),
                    ("y".to_string(), RuntimeValue::Bool(false)),
                ],
            )
            .unwrap(),
        );

        let updated = eval_expr(
            &Expr::Struct {
                name: Path::single("LState".to_string()),
                fields: vec![
                    ("x".to_string(), Expr::Literal(Literal::Int(7))),
                    ("..".to_string(), Expr::Ident("base".to_string())),
                ],
            },
            &ctx,
        )
        .unwrap();
        assert_eq!(
            updated,
            RuntimeValue::struct_value(
                "LState",
                vec![
                    ("x".to_string(), RuntimeValue::Int(7)),
                    ("y".to_string(), RuntimeValue::Bool(false)),
                ],
            )
            .unwrap()
        );
    }

    #[test]
    fn test_eval_builtin_static_empty_calls() {
        let ctx = EvalContext::new(test_bounds());

        let seq_empty = eval_expr(
            &Expr::Call {
                func: Path {
                    segments: vec!["Seq::<LPBMessage>".to_string(), "empty".to_string()],
                },
                args: vec![],
            },
            &ctx,
        )
        .unwrap();
        assert_eq!(seq_empty, RuntimeValue::Seq(Vec::new()));

        let set_empty = eval_expr(
            &Expr::Call {
                func: Path {
                    segments: vec!["Set".to_string(), "empty".to_string()],
                },
                args: vec![],
            },
            &ctx,
        )
        .unwrap();
        assert_eq!(set_empty, RuntimeValue::Set(Default::default()));

        let map_empty = eval_expr(
            &Expr::Call {
                func: Path {
                    segments: vec!["Map".to_string(), "empty".to_string()],
                },
                args: vec![],
            },
            &ctx,
        )
        .unwrap();
        assert_eq!(map_empty, RuntimeValue::Map(Default::default()));
    }

    #[test]
    fn test_eval_unsupported_constructs_are_explicit_errors() {
        let unsupported = Expr::Binary(
            Box::new(Expr::Literal(Literal::Int(1))),
            BinOp::BitAnd,
            Box::new(Expr::Literal(Literal::Int(1))),
        );
        let err = eval_expr(&unsupported, &EvalContext::new(test_bounds())).unwrap_err();
        assert!(err
            .to_string()
            .contains("does not support `bitwise/shift binary operator`"));

        let no_hook_call = Expr::Call {
            func: Path::single("Helper".to_string()),
            args: vec![],
        };
        let err = eval_expr(&no_hook_call, &EvalContext::new(test_bounds())).unwrap_err();
        assert!(err.to_string().contains("without call evaluator hook"));
    }

    #[test]
    fn test_eval_type_errors_are_explicit() {
        let bad_cmp = Expr::Lt(
            Box::new(Expr::Literal(Literal::Bool(true))),
            Box::new(Expr::Literal(Literal::Int(1))),
        );
        let err = eval_expr(&bad_cmp, &EvalContext::new(test_bounds())).unwrap_err();
        assert!(err.to_string().contains("expects numeric value"));
    }

    #[test]
    fn test_eval_match_expression_variant_binding_and_guard() {
        let msg = RuntimeValue::enum_value(
            "LMsg",
            "Data",
            vec![("_0".to_string(), RuntimeValue::Int(2))],
        )
        .unwrap();
        let ctx = EvalContext::new(test_bounds()).child_with_binding("msg".to_string(), msg);

        let expr = Expr::Match {
            scrutinee: Box::new(Expr::Ident("msg".to_string())),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Variant {
                        name: Path::new(vec!["LMsg".to_string(), "Data".to_string()]),
                        fields: vec![Pattern::Ident("v".to_string())],
                    },
                    guard: Some(Expr::Gt(
                        Box::new(Expr::Ident("v".to_string())),
                        Box::new(Expr::Literal(Literal::Int(1))),
                    )),
                    body: Expr::Ident("v".to_string()),
                },
                MatchArm {
                    pattern: Pattern::Wildcard,
                    guard: None,
                    body: Expr::Literal(Literal::Int(-1)),
                },
            ],
        };

        assert_eq!(eval_expr(&expr, &ctx).unwrap(), RuntimeValue::Int(2));
    }

    #[test]
    fn test_eval_match_expression_struct_pattern_binds_fields() {
        let state = RuntimeValue::struct_value(
            "LState",
            vec![
                ("x".to_string(), RuntimeValue::Int(3)),
                ("y".to_string(), RuntimeValue::Int(4)),
            ],
        )
        .unwrap();
        let ctx = EvalContext::new(test_bounds()).child_with_binding("state".to_string(), state);

        let expr = Expr::Match {
            scrutinee: Box::new(Expr::Ident("state".to_string())),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Struct {
                        name: Path::single("LState".to_string()),
                        fields: vec![
                            ("x".to_string(), Pattern::Ident("captured_x".to_string())),
                            ("y".to_string(), Pattern::Literal(Literal::Int(4))),
                        ],
                    },
                    guard: None,
                    body: Expr::Ident("captured_x".to_string()),
                },
                MatchArm {
                    pattern: Pattern::Wildcard,
                    guard: None,
                    body: Expr::Literal(Literal::Int(0)),
                },
            ],
        };

        assert_eq!(eval_expr(&expr, &ctx).unwrap(), RuntimeValue::Int(3));
    }

    #[test]
    fn test_eval_match_expression_errors_when_no_arm_matches() {
        let expr = Expr::Match {
            scrutinee: Box::new(Expr::Literal(Literal::Bool(true))),
            arms: vec![MatchArm {
                pattern: Pattern::Literal(Literal::Bool(false)),
                guard: None,
                body: Expr::Literal(Literal::Int(0)),
            }],
        };
        let err = eval_expr(&expr, &EvalContext::new(test_bounds())).unwrap_err();
        assert!(err
            .to_string()
            .contains("match expression has no matching arm"));
    }

    fn int_binding(name: &str) -> Binding {
        Binding {
            pattern: Pattern::Ident(name.to_string()),
            ty: Some(Type::Int),
            variable_mode: VariableMode::Exec,
        }
    }

    #[test]
    fn test_eval_quantifiers_with_finite_domain_resolver() {
        let quantifier_domain = |binding: &Binding| -> TranspileResult<Vec<RuntimeValue>> {
            let Some(Type::Int) = binding.ty else {
                return Err(TranspileError::Config {
                    message: "test resolver expects int quantifier type".to_string(),
                });
            };
            Ok(vec![RuntimeValue::Int(0), RuntimeValue::Int(1)])
        };
        let ctx =
            EvalContext::new(test_bounds()).with_quantifier_domain_evaluator(&quantifier_domain);

        let forall_expr = Expr::Forall {
            vars: vec![int_binding("i")],
            triggers: vec![],
            body: Box::new(Expr::Ge(
                Box::new(Expr::Ident("i".to_string())),
                Box::new(Expr::Literal(Literal::Int(0))),
            )),
        };
        let forall_out = eval_expr(&forall_expr, &ctx).unwrap();
        assert_eq!(forall_out, RuntimeValue::Bool(true));

        let exists_expr = Expr::Exists {
            vars: vec![int_binding("k")],
            body: Box::new(Expr::Eq(
                Box::new(Expr::Ident("k".to_string())),
                Box::new(Expr::Literal(Literal::Int(1))),
            )),
        };
        let exists_out = eval_expr(&exists_expr, &ctx).unwrap();
        assert_eq!(exists_out, RuntimeValue::Bool(true));
    }

    #[test]
    fn test_eval_quantifiers_require_domain_resolver() {
        let forall_expr = Expr::Forall {
            vars: vec![int_binding("i")],
            triggers: vec![],
            body: Box::new(Expr::Literal(Literal::Bool(true))),
        };
        let err = eval_expr(&forall_expr, &EvalContext::new(test_bounds())).unwrap_err();
        assert!(err
            .to_string()
            .contains("does not support `forall quantifier without domain resolver hook`"));
    }

    #[test]
    fn test_eval_multi_variable_quantifiers_use_bounded_nested_expansion() {
        let multi_exists = Expr::Exists {
            vars: vec![int_binding("a"), int_binding("b")],
            body: Box::new(Expr::Conjunction(vec![
                Expr::Eq(
                    Box::new(Expr::Ident("a".to_string())),
                    Box::new(Expr::Literal(Literal::Int(1))),
                ),
                Expr::Eq(
                    Box::new(Expr::Ident("b".to_string())),
                    Box::new(Expr::Literal(Literal::Int(0))),
                ),
            ])),
        };
        let quantifier_domain = |_binding: &Binding| -> TranspileResult<Vec<RuntimeValue>> {
            Ok(vec![RuntimeValue::Int(0), RuntimeValue::Int(1)])
        };
        let ctx =
            EvalContext::new(test_bounds()).with_quantifier_domain_evaluator(&quantifier_domain);
        let exists_out = eval_expr(&multi_exists, &ctx).unwrap();
        assert_eq!(exists_out, RuntimeValue::Bool(true));

        let multi_forall_false = Expr::Forall {
            vars: vec![int_binding("x"), int_binding("y")],
            triggers: vec![],
            body: Box::new(Expr::Eq(
                Box::new(Expr::Ident("x".to_string())),
                Box::new(Expr::Ident("y".to_string())),
            )),
        };
        let forall_out = eval_expr(&multi_forall_false, &ctx).unwrap();
        assert_eq!(forall_out, RuntimeValue::Bool(false));
    }

    #[test]
    fn test_eval_multi_variable_quantifiers_handle_empty_domains() {
        let multi_forall = Expr::Forall {
            vars: vec![int_binding("a"), int_binding("b")],
            triggers: vec![],
            body: Box::new(Expr::Literal(Literal::Bool(false))),
        };
        let multi_exists = Expr::Exists {
            vars: vec![int_binding("a"), int_binding("b")],
            body: Box::new(Expr::Literal(Literal::Bool(true))),
        };
        let quantifier_domain = |binding: &Binding| -> TranspileResult<Vec<RuntimeValue>> {
            let name = binding.name().unwrap_or_default();
            if name == "b" {
                Ok(vec![])
            } else {
                Ok(vec![RuntimeValue::Int(0)])
            }
        };
        let ctx =
            EvalContext::new(test_bounds()).with_quantifier_domain_evaluator(&quantifier_domain);
        assert_eq!(
            eval_expr(&multi_forall, &ctx).unwrap(),
            RuntimeValue::Bool(true)
        );
        assert_eq!(
            eval_expr(&multi_exists, &ctx).unwrap(),
            RuntimeValue::Bool(false)
        );
    }
}
