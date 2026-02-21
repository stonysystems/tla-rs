use crate::ast::{BinOp, Expr, Path, Pattern, Type, UnaryOp};
use crate::error::{TranspileError, TranspileResult};
use crate::modelcheck::value::{RuntimeCollectionBounds, RuntimeValue};
use std::collections::BTreeMap;

pub type CallEvaluator<'a> =
    dyn Fn(&Path, &[RuntimeValue]) -> TranspileResult<RuntimeValue> + 'a;
pub type MethodEvaluator<'a> =
    dyn Fn(&RuntimeValue, &str, &[RuntimeValue]) -> TranspileResult<RuntimeValue> + 'a;

/// Runtime evaluator context for source-first model checking.
#[derive(Clone)]
pub struct EvalContext<'a> {
    bindings: BTreeMap<String, RuntimeValue>,
    bounds: RuntimeCollectionBounds,
    call_evaluator: Option<&'a CallEvaluator<'a>>,
    method_evaluator: Option<&'a MethodEvaluator<'a>>,
}

impl<'a> EvalContext<'a> {
    pub fn new(bounds: RuntimeCollectionBounds) -> Self {
        Self {
            bindings: BTreeMap::new(),
            bounds,
            call_evaluator: None,
            method_evaluator: None,
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

    fn child_with_binding(&self, name: String, value: RuntimeValue) -> Self {
        let mut bindings = self.bindings.clone();
        bindings.insert(name, value);
        Self {
            bindings,
            bounds: self.bounds,
            call_evaluator: self.call_evaluator,
            method_evaluator: self.method_evaluator,
        }
    }
}

/// Evaluate a spec expression into a concrete runtime value.
pub fn eval_expr(expr: &Expr, ctx: &EvalContext<'_>) -> TranspileResult<RuntimeValue> {
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
            base.field(field).cloned().ok_or_else(|| {
                type_error(
                    format!(
                        "Field access `.{}` is not valid for `{}`.",
                        field,
                        base.canonical_key()
                    )
                    .as_str(),
                )
            })
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
        Expr::Struct { name, fields } => {
            let ty_or_variant = path_name(name);
            let mut resolved = Vec::with_capacity(fields.len());
            for (field, value_expr) in fields {
                resolved.push((field.clone(), eval_expr(value_expr, ctx)?));
            }
            if let Some((ty, variant)) = split_variant_path(&ty_or_variant) {
                RuntimeValue::enum_value(ty, variant, resolved)
            } else {
                RuntimeValue::struct_value(ty_or_variant, resolved)
            }
        }
        Expr::StructUpdate { .. } => Err(unsupported_construct("struct update expression")),
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
            let receiver = eval_expr(receiver, ctx)?;
            let args = args
                .iter()
                .map(|arg| eval_expr(arg, ctx))
                .collect::<TranspileResult<Vec<_>>>()?;

            if let Some(value) = eval_builtin_method(&receiver, method, &args)? {
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
            let lhs = eval_expr(lhs, ctx)?;
            let rhs = eval_expr(rhs, ctx)?;
            eval_binary(&lhs, *op, &rhs)
        }
        Expr::Unary(op, inner) => {
            let inner = eval_expr(inner, ctx)?;
            eval_unary(*op, &inner)
        }
        Expr::Forall { .. } => Err(unsupported_construct("forall quantifier")),
        Expr::Exists { .. } => Err(unsupported_construct("exists quantifier")),
        Expr::Match { .. } => Err(unsupported_construct("match expression")),
    }
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
        "insert" => {
            if args.len() != 1 {
                return Err(type_error("`.insert(...)` expects one argument."));
            }
            match receiver {
                RuntimeValue::Set(items) => {
                    let mut next = items.clone();
                    next.insert(args[0].clone());
                    Ok(Some(RuntimeValue::Set(next)))
                }
                other => Err(type_error(
                    format!(
                        "`.insert(...)` currently expects Set receiver, got `{}`.",
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
        _ => Ok(None),
    }
}

fn eval_builtin_static_call(
    func: &Path,
    args: &[RuntimeValue],
    bounds: RuntimeCollectionBounds,
) -> TranspileResult<Option<RuntimeValue>> {
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
    use crate::ast::{Literal, Path};

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
        let unsupported = Expr::Exists {
            vars: vec![],
            body: Box::new(Expr::Literal(Literal::Bool(true))),
        };
        let err = eval_expr(&unsupported, &EvalContext::new(test_bounds())).unwrap_err();
        assert!(err
            .to_string()
            .contains("does not support `exists quantifier`"));

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
}
