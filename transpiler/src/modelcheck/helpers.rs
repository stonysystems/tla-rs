//! Model-check helper evaluation functions.
//!
//! Extracted from main.rs (Phase 38.8.2.c) to enable the DPOR crate
//! and other library consumers to evaluate spec functions, resolve
//! call paths, and expand quantifier domains.

use crate::ast::{Binding, Path, SpecFunction};
use crate::error::{TranspileError, TranspileResult};
use crate::modelcheck::config::ModelConfig;
use crate::modelcheck::domain::expand_branch_existentials;
use crate::modelcheck::evaluator::{eval_expr, EvalContext};
use crate::modelcheck::ir::{ExistentialVarIr, TransitionBranchIr};
use crate::modelcheck::value::{RuntimeCollectionBounds, RuntimeValue};
use crate::spec_analyzer::SpecSchema;
use std::collections::BTreeSet;

/// Normalize a call path by splitting `::` segments and stripping generics.
pub fn normalize_call_path(path: &Path) -> String {
    path.segments
        .iter()
        .flat_map(|segment| segment.split("::"))
        .map(|segment| {
            if let Some(idx) = segment.find("::<") {
                segment[..idx].to_string()
            } else {
                segment.to_string()
            }
        })
        .collect::<Vec<_>>()
        .join("::")
}

/// Expand a quantifier binding into its finite domain of concrete values.
pub fn expand_quantifier_domain_for_binding(
    binding: &Binding,
    schema: &SpecSchema,
    model_config: &ModelConfig,
) -> TranspileResult<Vec<RuntimeValue>> {
    let var_name = binding.name().ok_or_else(|| TranspileError::Config {
        message: "Model-check quantifier evaluation requires identifier bindings.".to_string(),
    })?;
    let branch = TransitionBranchIr {
        label: "__quantifier_domain__".to_string(),
        existential_vars: vec![ExistentialVarIr {
            name: var_name.to_string(),
            ty: binding.ty.clone(),
        }],
        constraints: vec![],
    };
    let assignments = expand_branch_existentials(&branch, schema, model_config)?;

    let mut seen = BTreeSet::new();
    let mut out = Vec::new();
    for assignment in assignments {
        let value = assignment
            .get(var_name)
            .ok_or_else(|| TranspileError::Config {
                message: format!(
                    "Internal model-check error: quantifier domain assignment missing `{}`.",
                    var_name
                ),
            })?;
        if seen.insert(value.canonical_key()) {
            out.push(value.clone());
        }
    }

    Ok(out)
}

/// Resolve a function call path to a parsed spec function.
pub fn resolve_called_spec_function<'a>(
    functions: &'a [SpecFunction],
    path: &Path,
) -> TranspileResult<&'a SpecFunction> {
    let normalized = normalize_call_path(path);
    let short_name = normalized
        .rsplit("::")
        .next()
        .unwrap_or(normalized.as_str());

    let exact_matches: Vec<&SpecFunction> =
        functions.iter().filter(|f| f.name == normalized).collect();
    if exact_matches.len() == 1 {
        return Ok(exact_matches[0]);
    }
    if exact_matches.len() > 1 {
        return Err(TranspileError::Config {
            message: format!(
                "Ambiguous model-check helper call `{}`: multiple exact function matches found.",
                normalized
            ),
        });
    }

    let short_matches: Vec<&SpecFunction> =
        functions.iter().filter(|f| f.name == short_name).collect();
    if short_matches.len() == 1 {
        return Ok(short_matches[0]);
    }
    if short_matches.len() > 1 {
        return Err(TranspileError::Config {
            message: format!(
                "Ambiguous model-check helper call `{}`: short name `{}` matches multiple functions. \
                 Use uniquely named helper predicates.",
                normalized, short_name
            ),
        });
    }

    Err(TranspileError::UnsupportedPattern {
        message: format!(
            "Model-check evaluator could not resolve helper call `{}` to a parsed spec function.",
            normalized
        ),
        span: None,
        help: Some(
            "Ensure helper predicates are in the ingested protocol sources and have unique names."
                .to_string(),
        ),
    })
}

/// Evaluate a spec function call recursively, resolving nested helper calls.
///
/// This is the core evaluator used by the model checker to evaluate
/// spec predicates (Init, Next, invariants, helper functions).
pub fn eval_spec_function_call_recursive(
    functions: &[SpecFunction],
    schema: &SpecSchema,
    model_config: &ModelConfig,
    func_path: &Path,
    args: &[RuntimeValue],
    bounds: RuntimeCollectionBounds,
    depth: usize,
) -> TranspileResult<RuntimeValue> {
    if depth > 32 {
        return Err(TranspileError::UnsupportedPattern {
            message: format!(
                "Model-check helper-call recursion exceeded depth limit while evaluating `{}`.",
                normalize_call_path(func_path)
            ),
            span: None,
            help: Some(
                "Add a finite non-recursive helper subset for model checking or increase evaluator support."
                    .to_string(),
            ),
        });
    }

    let function = resolve_called_spec_function(functions, func_path)?;
    if function.params.len() != args.len() {
        return Err(TranspileError::Config {
            message: format!(
                "Model-check helper call `{}` arity mismatch: expected {} args, got {}.",
                function.name,
                function.params.len(),
                args.len()
            ),
        });
    }

    let mut ctx = EvalContext::new(bounds);
    for (param, value) in function.params.iter().zip(args.iter()) {
        ctx = ctx.with_binding(param.name.clone(), value.clone());
    }
    let recursive_call =
        |inner_path: &Path, inner_args: &[RuntimeValue]| -> TranspileResult<RuntimeValue> {
            eval_spec_function_call_recursive(
                functions,
                schema,
                model_config,
                inner_path,
                inner_args,
                bounds,
                depth + 1,
            )
        };
    let quantifier_domain = |binding: &Binding| -> TranspileResult<Vec<RuntimeValue>> {
        expand_quantifier_domain_for_binding(binding, schema, model_config)
    };
    ctx = ctx.with_call_evaluator(&recursive_call);
    ctx = ctx.with_quantifier_domain_evaluator(&quantifier_domain);

    eval_expr(&function.body, &ctx).map_err(|err| TranspileError::Config {
        message: format!(
            "Failed to evaluate helper call `{}` via `{}`: {}",
            normalize_call_path(func_path),
            function.name,
            err
        ),
    })
}
