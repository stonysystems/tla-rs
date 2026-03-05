use crate::ast::{SpecFunction, Type};
use crate::error::{TranspileError, TranspileResult};
use crate::modelcheck::evaluator::{
    eval_expr, CallEvaluator, EvalContext, MethodEvaluator, QuantifierDomainEvaluator,
};
use crate::modelcheck::value::{RuntimeCollectionBounds, RuntimeValue};
use std::collections::BTreeMap;

/// Optional evaluator hooks used while checking state invariants.
#[derive(Clone, Copy, Default)]
pub struct InvariantHooks<'a> {
    pub call_evaluator: Option<&'a CallEvaluator<'a>>,
    pub method_evaluator: Option<&'a MethodEvaluator<'a>>,
    pub quantifier_domain_evaluator: Option<&'a QuantifierDomainEvaluator<'a>>,
}

/// Resolve user-selected invariant names to concrete spec functions in user order.
pub fn resolve_selected_invariants<'a>(
    functions: &'a [SpecFunction],
    selected_names: &[String],
) -> TranspileResult<Vec<&'a SpecFunction>> {
    let mut by_name = BTreeMap::new();
    for function in functions {
        by_name.insert(function.name.as_str(), function);
    }

    let mut resolved = Vec::with_capacity(selected_names.len());
    for name in selected_names {
        let function = by_name.get(name.as_str()).ok_or_else(|| TranspileError::Config {
            message: format!(
                "Invariant `{}` was selected in model config but was not found in parsed spec functions.",
                name
            ),
        })?;
        resolved.push(*function);
    }

    Ok(resolved)
}

/// Evaluate user-selected invariants against one reached state.
///
/// Returns `Ok(Some(name))` for the first invariant that evaluates to `false`.
/// Returns `Ok(None)` when all invariants hold.
pub fn first_invariant_violation(
    invariants: &[SpecFunction],
    state: &RuntimeValue,
    constants: Option<&RuntimeValue>,
    bounds: RuntimeCollectionBounds,
    hooks: InvariantHooks<'_>,
) -> TranspileResult<Option<String>> {
    for invariant in invariants {
        let (state_param, constants_param) = validate_invariant_signature(invariant, constants)?;
        let mut ctx = EvalContext::new(bounds).with_binding(state_param.to_string(), state.clone());
        if let (Some(param_name), Some(constants_value)) = (constants_param, constants) {
            ctx = ctx.with_binding(param_name.to_string(), constants_value.clone());
        }
        if let Some(call_evaluator) = hooks.call_evaluator {
            ctx = ctx.with_call_evaluator(call_evaluator);
        }
        if let Some(method_evaluator) = hooks.method_evaluator {
            ctx = ctx.with_method_evaluator(method_evaluator);
        }
        if let Some(quantifier_domain_evaluator) = hooks.quantifier_domain_evaluator {
            ctx = ctx.with_quantifier_domain_evaluator(quantifier_domain_evaluator);
        }

        let holds = eval_expr(&invariant.body, &ctx).map_err(|err| TranspileError::Config {
            message: format!(
                "Failed to evaluate invariant `{}` on reached state: {}",
                invariant.name, err
            ),
        })?;
        match holds {
            RuntimeValue::Bool(true) => {}
            RuntimeValue::Bool(false) => return Ok(Some(invariant.name.clone())),
            other => {
                return Err(TranspileError::Config {
                    message: format!(
                        "Invariant `{}` did not evaluate to bool (got `{}`).",
                        invariant.name,
                        other.canonical_key()
                    ),
                });
            }
        }
    }
    Ok(None)
}

fn validate_invariant_signature<'a>(
    invariant_fn: &'a SpecFunction,
    constants: Option<&RuntimeValue>,
) -> TranspileResult<(&'a str, Option<&'a str>)> {
    if invariant_fn.params.is_empty() {
        return Err(TranspileError::Config {
            message: format!(
                "Cannot evaluate invariant `{}`: expected at least one parameter (state).",
                invariant_fn.name
            ),
        });
    }
    if invariant_fn.params.len() > 2 {
        return Err(TranspileError::Config {
            message: format!(
                "Cannot evaluate invariant `{}`: expected signature `(state[, constants])`, found {} parameters.",
                invariant_fn.name,
                invariant_fn.params.len()
            ),
        });
    }
    if !matches!(invariant_fn.return_type, Type::Bool) {
        return Err(TranspileError::Config {
            message: format!(
                "Cannot evaluate invariant `{}`: expected bool return type.",
                invariant_fn.name
            ),
        });
    }

    let state_param = invariant_fn.params[0].name.as_str();
    let constants_param = invariant_fn.params.get(1).map(|param| param.name.as_str());
    if constants_param.is_some() && constants.is_none() {
        return Err(TranspileError::Config {
            message: format!(
                "Cannot evaluate invariant `{}`: constants argument is required by signature but missing.",
                invariant_fn.name
            ),
        });
    }

    Ok((state_param, constants_param))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Expr, Generics, Literal, Parameter, Path, SpecFunction, Type, VariableMode};

    fn state(x: i128) -> RuntimeValue {
        RuntimeValue::struct_value("LState", vec![("x".to_string(), RuntimeValue::Int(x))]).unwrap()
    }

    fn constants(limit: i128) -> RuntimeValue {
        RuntimeValue::struct_value(
            "LConstants",
            vec![("limit".to_string(), RuntimeValue::Int(limit))],
        )
        .unwrap()
    }

    fn param(name: &str, ty: Type) -> Parameter {
        Parameter {
            name: name.to_string(),
            ty,
            mode: None,
            variable_mode: VariableMode::Exec,
            span: None,
        }
    }

    fn invariant_fn(name: &str, params: Vec<Parameter>, body: Expr) -> SpecFunction {
        SpecFunction {
            name: name.to_string(),
            generics: Generics::default(),
            params,
            return_type: Type::Bool,
            requires: vec![],
            ensures: vec![],
            recommends: vec![],
            decreases: vec![],
            body,
            span: None,
        }
    }

    fn bounds() -> RuntimeCollectionBounds {
        RuntimeCollectionBounds {
            max_seq_len: 4,
            max_set_len: 4,
            max_map_len: 4,
        }
    }

    #[test]
    fn test_resolve_selected_invariants_preserves_user_order() {
        let f1 = invariant_fn(
            "LTypeOK",
            vec![param("s", Type::Named(Path::single("LState".to_string())))],
            Expr::Literal(Literal::Bool(true)),
        );
        let f2 = invariant_fn(
            "LSafety",
            vec![param("s", Type::Named(Path::single("LState".to_string())))],
            Expr::Literal(Literal::Bool(true)),
        );

        let functions = vec![f1.clone(), f2.clone()];
        let selected = vec!["LSafety".to_string(), "LTypeOK".to_string()];
        let resolved = resolve_selected_invariants(&functions, &selected).unwrap();
        assert_eq!(resolved[0].name, "LSafety");
        assert_eq!(resolved[1].name, "LTypeOK");
    }

    #[test]
    fn test_resolve_selected_invariants_rejects_unknown_name() {
        let f1 = invariant_fn(
            "LTypeOK",
            vec![param("s", Type::Named(Path::single("LState".to_string())))],
            Expr::Literal(Literal::Bool(true)),
        );
        let err = resolve_selected_invariants(&[f1], &["LUnknown".to_string()]).unwrap_err();
        assert!(err.to_string().contains("LUnknown"));
    }

    #[test]
    fn test_first_invariant_violation_returns_first_failing_name() {
        let type_ok = invariant_fn(
            "LTypeOK",
            vec![param("s", Type::Named(Path::single("LState".to_string())))],
            Expr::Literal(Literal::Bool(true)),
        );
        let safety = invariant_fn(
            "LSafety",
            vec![param("s", Type::Named(Path::single("LState".to_string())))],
            Expr::Lt(
                Box::new(Expr::Field(
                    Box::new(Expr::Ident("s".to_string())),
                    "x".to_string(),
                )),
                Box::new(Expr::Literal(Literal::Int(1))),
            ),
        );

        let violation = first_invariant_violation(
            &[type_ok, safety],
            &state(2),
            None,
            bounds(),
            InvariantHooks::default(),
        )
        .unwrap();
        assert_eq!(violation, Some("LSafety".to_string()));
    }

    #[test]
    fn test_first_invariant_violation_binds_constants_parameter() {
        let bounded = invariant_fn(
            "LBounded",
            vec![
                param("s", Type::Named(Path::single("LState".to_string()))),
                param("c", Type::Named(Path::single("LConstants".to_string()))),
            ],
            Expr::Le(
                Box::new(Expr::Field(
                    Box::new(Expr::Ident("s".to_string())),
                    "x".to_string(),
                )),
                Box::new(Expr::Field(
                    Box::new(Expr::Ident("c".to_string())),
                    "limit".to_string(),
                )),
            ),
        );

        let violation = first_invariant_violation(
            &[bounded],
            &state(2),
            Some(&constants(1)),
            bounds(),
            InvariantHooks::default(),
        )
        .unwrap();
        assert_eq!(violation, Some("LBounded".to_string()));
    }

    #[test]
    fn test_first_invariant_violation_requires_constants_when_signature_needs_it() {
        let bounded = invariant_fn(
            "LBounded",
            vec![
                param("s", Type::Named(Path::single("LState".to_string()))),
                param("c", Type::Named(Path::single("LConstants".to_string()))),
            ],
            Expr::Literal(Literal::Bool(true)),
        );

        let err = first_invariant_violation(
            &[bounded],
            &state(0),
            None,
            bounds(),
            InvariantHooks::default(),
        )
        .unwrap_err();
        assert!(err.to_string().contains("constants argument is required"));
    }

    #[test]
    fn test_first_invariant_violation_rejects_non_bool_result() {
        let mut broken = invariant_fn(
            "LBroken",
            vec![param("s", Type::Named(Path::single("LState".to_string())))],
            Expr::Literal(Literal::Int(1)),
        );
        broken.return_type = Type::Int;

        let err = first_invariant_violation(
            &[broken],
            &state(0),
            None,
            bounds(),
            InvariantHooks::default(),
        )
        .unwrap_err();
        assert!(err.to_string().contains("expected bool return type"));
    }
}
