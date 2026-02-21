use crate::error::{TranspileError, TranspileResult};
use crate::tla::{parse_module, TlaModule, TlaOperator};
use std::collections::HashSet;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct McWrapperOptions {
    pub init_operator: String,
    pub next_operator: String,
    pub wrapper_suffix: String,
    pub invariants: Vec<String>,
}

impl Default for McWrapperOptions {
    fn default() -> Self {
        Self {
            init_operator: "Init".to_string(),
            next_operator: "Next".to_string(),
            wrapper_suffix: "_MC".to_string(),
            invariants: Vec::new(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct McWrapperArtifacts {
    pub wrapper_module_name: String,
    pub wrapper_tla: String,
    pub cfg: String,
}

pub fn generate_relational_mc_wrapper(
    source: &str,
    options: &McWrapperOptions,
) -> TranspileResult<McWrapperArtifacts> {
    if options.wrapper_suffix.trim().is_empty() {
        return Err(TranspileError::Config {
            message: "Wrapper suffix cannot be empty.".to_string(),
        });
    }

    let module = parse_module(source).map_err(|e| TranspileError::Parse {
        message: format!("Failed to parse input TLA+ module: {}", e),
        span: None,
    })?;

    let init = find_operator(&module, &options.init_operator)?;
    let next = find_operator(&module, &options.next_operator)?;
    validate_arity(init, 2)?;
    validate_arity(next, 3)?;

    let invariants = normalize_invariants(&options.invariants)?;
    let wrapper_module_name = format!("{}{}", module.name, options.wrapper_suffix);
    let wrapper_tla = render_wrapper_tla(
        &module,
        &wrapper_module_name,
        &options.init_operator,
        &options.next_operator,
    );
    let cfg = render_cfg(&invariants);

    Ok(McWrapperArtifacts {
        wrapper_module_name,
        wrapper_tla,
        cfg,
    })
}

fn find_operator<'a>(module: &'a TlaModule, name: &str) -> TranspileResult<&'a TlaOperator> {
    module
        .operators
        .iter()
        .find(|op| op.name == name)
        .ok_or_else(|| TranspileError::Config {
            message: format!(
                "Cannot generate model-check wrapper: missing operator `{}` in module `{}`.",
                name, module.name
            ),
        })
}

fn validate_arity(op: &TlaOperator, expected: usize) -> TranspileResult<()> {
    if op.params.len() != expected {
        return Err(TranspileError::Config {
            message: format!(
                "Cannot generate model-check wrapper: operator `{}` must have {} parameters, found {}.",
                op.name,
                expected,
                op.params.len()
            ),
        });
    }
    Ok(())
}

fn normalize_invariants(raw: &[String]) -> TranspileResult<Vec<String>> {
    let mut seen = HashSet::new();
    let mut out = Vec::with_capacity(raw.len());
    for item in raw {
        let trimmed = item.trim();
        if trimmed.is_empty() {
            return Err(TranspileError::Config {
                message: "Invariant names cannot be empty.".to_string(),
            });
        }
        let owned = trimmed.to_string();
        if !seen.insert(owned.clone()) {
            return Err(TranspileError::Config {
                message: format!("Duplicate invariant `{}`.", owned),
            });
        }
        out.push(owned);
    }
    Ok(out)
}

fn render_wrapper_tla(
    module: &TlaModule,
    wrapper_module_name: &str,
    init_operator: &str,
    next_operator: &str,
) -> String {
    let has_state_set = module.constants.iter().any(|c| c.name == "State");
    let has_constants_set = module.constants.iter().any(|c| c.name == "Constants");
    let state_quantifier = if has_state_set {
        "\\E state_ \\in State :"
    } else {
        "\\E state_ :"
    };

    let mut out = String::new();
    out.push_str(&format!("---- MODULE {} ----\n", wrapper_module_name));
    out.push_str("\\* Auto-generated model-check wrapper for relational spec pattern.\n");
    out.push_str(&format!("\\* Source module: {}\n\n", module.name));
    out.push_str(&format!("EXTENDS {}\n\n", module.name));

    out.push_str("VARIABLE state, constants\n\n");

    out.push_str("StateInit ==\n");
    if has_state_set {
        out.push_str("    /\\ state \\in State\n");
    }
    if has_constants_set {
        out.push_str("    /\\ constants \\in Constants\n");
    }
    out.push_str(&format!("    /\\ {}(state, constants)\n\n", init_operator));

    out.push_str("StateNext ==\n");
    out.push_str(&format!("    /\\ {}\n", state_quantifier));
    out.push_str(&format!(
        "        /\\ {}(state, state_, constants)\n",
        next_operator
    ));
    out.push_str("        /\\ state' = state_\n");
    out.push_str("    /\\ UNCHANGED constants\n\n");

    out.push_str("vars == <<state, constants>>\n\n");
    out.push_str("Spec == StateInit /\\ [][StateNext]_vars\n\n");
    out.push_str("====\n");

    out
}

fn render_cfg(invariants: &[String]) -> String {
    let mut out = String::from("SPECIFICATION Spec\nCHECK_DEADLOCK FALSE\n");
    if !invariants.is_empty() {
        out.push_str("\nINVARIANTS\n");
        for invariant in invariants {
            out.push_str("    ");
            out.push_str(invariant);
            out.push('\n');
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_module() -> &'static str {
        r#"
---- MODULE Demo ----
EXTENDS Integers

CONSTANTS Constants, State

Init(s, c) == s \in State /\ c \in Constants
Next(s, s_, c) == s_ = s

====
"#
    }

    #[test]
    fn test_generate_relational_mc_wrapper_happy_path() {
        let opts = McWrapperOptions::default();
        let generated = generate_relational_mc_wrapper(sample_module(), &opts).unwrap();

        assert_eq!(generated.wrapper_module_name, "Demo_MC");
        assert!(generated.wrapper_tla.contains("---- MODULE Demo_MC ----"));
        assert!(generated.wrapper_tla.contains("EXTENDS Demo"));
        assert!(generated.wrapper_tla.contains("/\\ state \\in State"));
        assert!(generated.wrapper_tla.contains("/\\ constants \\in Constants"));
        assert!(generated.wrapper_tla.contains("Init(state, constants)"));
        assert!(generated.wrapper_tla.contains("\\E state_ \\in State :"));
        assert!(generated.wrapper_tla.contains("Next(state, state_, constants)"));
        assert!(generated.cfg.contains("SPECIFICATION Spec"));
        assert!(generated.cfg.contains("CHECK_DEADLOCK FALSE"));
    }

    #[test]
    fn test_generate_relational_mc_wrapper_unbounded_state_fallback() {
        let source = r#"
---- MODULE Demo ----
CONSTANTS Constants
Init(s, c) == TRUE
Next(s, s_, c) == TRUE
====
"#;
        let generated = generate_relational_mc_wrapper(source, &McWrapperOptions::default()).unwrap();
        assert!(generated.wrapper_tla.contains("\\E state_ :"));
    }

    #[test]
    fn test_generate_relational_mc_wrapper_rejects_missing_operator() {
        let source = r#"
---- MODULE Demo ----
Init(s, c) == TRUE
====
"#;
        let err = generate_relational_mc_wrapper(source, &McWrapperOptions::default()).unwrap_err();
        assert!(err.to_string().contains("missing operator `Next`"));
    }

    #[test]
    fn test_generate_relational_mc_wrapper_rejects_duplicate_invariants() {
        let opts = McWrapperOptions {
            invariants: vec!["InvA".to_string(), "InvA".to_string()],
            ..McWrapperOptions::default()
        };
        let err = generate_relational_mc_wrapper(sample_module(), &opts).unwrap_err();
        assert!(err.to_string().contains("Duplicate invariant `InvA`"));
    }
}
