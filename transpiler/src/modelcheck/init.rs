use crate::ast::{SpecFunction, Type};
use crate::error::{TranspileError, TranspileResult};
use crate::modelcheck::evaluator::{eval_expr, CallEvaluator, EvalContext, MethodEvaluator};
use crate::modelcheck::value::{RuntimeCollectionBounds, RuntimeValue};
use std::collections::BTreeSet;

/// Optional evaluator hooks used while checking `LInit`.
#[derive(Clone, Copy, Default)]
pub struct InitHooks<'a> {
    pub call_evaluator: Option<&'a CallEvaluator>,
    pub method_evaluator: Option<&'a MethodEvaluator>,
}

/// Build concrete initial states by checking which candidate states satisfy `LInit`.
///
/// Candidate states are canonical-key deduplicated in stable input order before checking.
pub fn construct_initial_states(
    init_fn: &SpecFunction,
    candidate_states: &[RuntimeValue],
    constants: Option<&RuntimeValue>,
    bounds: RuntimeCollectionBounds,
    hooks: InitHooks<'_>,
) -> TranspileResult<Vec<RuntimeValue>> {
    let (state_param, constants_param) = validate_init_signature(init_fn, constants)?;

    let mut seen = BTreeSet::new();
    let mut initial_states = Vec::new();
    for candidate in candidate_states {
        if !seen.insert(candidate.canonical_key()) {
            continue;
        }

        let mut ctx =
            EvalContext::new(bounds).with_binding(state_param.to_string(), candidate.clone());
        if let (Some(param_name), Some(constants_value)) = (constants_param, constants) {
            ctx = ctx.with_binding(param_name.to_string(), constants_value.clone());
        }
        if let Some(call_evaluator) = hooks.call_evaluator {
            ctx = ctx.with_call_evaluator(call_evaluator);
        }
        if let Some(method_evaluator) = hooks.method_evaluator {
            ctx = ctx.with_method_evaluator(method_evaluator);
        }

        let holds = eval_expr(&init_fn.body, &ctx).map_err(|err| TranspileError::Config {
            message: format!(
                "Failed to evaluate `{}` for initial-state construction: {}",
                init_fn.name, err
            ),
        })?;
        match holds {
            RuntimeValue::Bool(true) => initial_states.push(candidate.clone()),
            RuntimeValue::Bool(false) => {}
            other => {
                return Err(TranspileError::Config {
                    message: format!(
                        "Initial-state predicate `{}` did not evaluate to bool (got `{}`).",
                        init_fn.name,
                        other.canonical_key()
                    ),
                });
            }
        }
    }

    Ok(initial_states)
}

fn validate_init_signature<'a>(
    init_fn: &'a SpecFunction,
    constants: Option<&RuntimeValue>,
) -> TranspileResult<(&'a str, Option<&'a str>)> {
    if init_fn.params.is_empty() {
        return Err(TranspileError::Config {
            message: format!(
                "Cannot construct initial states from `{}`: expected at least one parameter (state).",
                init_fn.name
            ),
        });
    }
    if init_fn.params.len() > 2 {
        return Err(TranspileError::Config {
            message: format!(
                "Cannot construct initial states from `{}`: expected signature `(state[, constants])`, found {} parameters.",
                init_fn.name,
                init_fn.params.len()
            ),
        });
    }
    if !matches!(init_fn.return_type, Type::Bool) {
        return Err(TranspileError::Config {
            message: format!(
                "Cannot construct initial states from `{}`: expected bool return type.",
                init_fn.name
            ),
        });
    }

    let state_param = init_fn.params[0].name.as_str();
    let constants_param = init_fn.params.get(1).map(|param| param.name.as_str());
    if constants_param.is_some() && constants.is_none() {
        return Err(TranspileError::Config {
            message: format!(
                "Cannot construct initial states from `{}`: constants argument is required by signature but missing.",
                init_fn.name
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

    fn init_fn(params: Vec<Parameter>, body: Expr) -> SpecFunction {
        SpecFunction {
            name: "LInit".to_string(),
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
    fn test_construct_initial_states_filters_and_deduplicates_candidates() {
        let init = init_fn(
            vec![param("s", Type::Named(Path::single("LState".to_string())))],
            Expr::Eq(
                Box::new(Expr::Field(
                    Box::new(Expr::Ident("s".to_string())),
                    "x".to_string(),
                )),
                Box::new(Expr::Literal(Literal::Int(1))),
            ),
        );

        let result = construct_initial_states(
            &init,
            &[state(0), state(1), state(1)],
            None,
            bounds(),
            InitHooks::default(),
        )
        .unwrap();

        assert_eq!(result, vec![state(1)]);
    }

    #[test]
    fn test_construct_initial_states_supports_disjunction() {
        let init = init_fn(
            vec![param("s", Type::Named(Path::single("LState".to_string())))],
            Expr::Disjunction(vec![
                Expr::Eq(
                    Box::new(Expr::Field(
                        Box::new(Expr::Ident("s".to_string())),
                        "x".to_string(),
                    )),
                    Box::new(Expr::Literal(Literal::Int(0))),
                ),
                Expr::Eq(
                    Box::new(Expr::Field(
                        Box::new(Expr::Ident("s".to_string())),
                        "x".to_string(),
                    )),
                    Box::new(Expr::Literal(Literal::Int(2))),
                ),
            ]),
        );

        let result = construct_initial_states(
            &init,
            &[state(0), state(1), state(2)],
            None,
            bounds(),
            InitHooks::default(),
        )
        .unwrap();

        assert_eq!(result, vec![state(0), state(2)]);
    }

    #[test]
    fn test_construct_initial_states_binds_constants_parameter() {
        let init = init_fn(
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

        let result = construct_initial_states(
            &init,
            &[state(0), state(1), state(2)],
            Some(&constants(1)),
            bounds(),
            InitHooks::default(),
        )
        .unwrap();

        assert_eq!(result, vec![state(0), state(1)]);
    }

    #[test]
    fn test_construct_initial_states_requires_constants_when_signature_needs_it() {
        let init = init_fn(
            vec![
                param("s", Type::Named(Path::single("LState".to_string()))),
                param("c", Type::Named(Path::single("LConstants".to_string()))),
            ],
            Expr::Literal(Literal::Bool(true)),
        );

        let err =
            construct_initial_states(&init, &[state(0)], None, bounds(), InitHooks::default())
                .unwrap_err();
        assert!(err.to_string().contains("constants argument is required"));
    }

    #[test]
    fn test_construct_initial_states_rejects_non_bool_linit_result() {
        let init = init_fn(
            vec![param("s", Type::Named(Path::single("LState".to_string())))],
            Expr::Literal(Literal::Int(1)),
        );

        let err =
            construct_initial_states(&init, &[state(0)], None, bounds(), InitHooks::default())
                .unwrap_err();
        assert!(err.to_string().contains("did not evaluate to bool"));
    }

    #[test]
    fn test_construct_initial_states_rejects_invalid_signature() {
        let init = init_fn(vec![], Expr::Literal(Literal::Bool(true)));
        let err =
            construct_initial_states(&init, &[], None, bounds(), InitHooks::default()).unwrap_err();
        assert!(err.to_string().contains("at least one parameter"));
    }
}
