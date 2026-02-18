//! Scheduler generation from LNext disjunction structure.
//!
//! Analyzes the LNext spec function body to extract the list of protocol
//! actions, their existential parameters, and generates a scheduler config
//! that can be used to produce the runtime host/scheduler code.

use crate::ast::{Binding, Expr, Path, SpecFunction, Type};

/// A single protocol action extracted from an LNext disjunction branch.
#[derive(Debug, Clone)]
pub struct SchedulerAction {
    /// Spec function name (e.g., "LTMSendPrepare")
    pub spec_name: String,
    /// Exec function name (e.g., "CTMSendPrepare")
    pub exec_name: String,
    /// Existential parameters: (name, type_string) pairs
    /// Empty if the branch is a direct call (no exists quantifier)
    pub existential_params: Vec<(String, String)>,
    /// The fixed args passed through from LNext (e.g., ["s", "s_", "c"])
    pub fixed_args: Vec<String>,
}

/// Complete scheduler configuration extracted from an LNext function.
#[derive(Debug, Clone)]
pub struct SchedulerConfig {
    /// The name of the LNext function (usually "LNext")
    pub next_fn_name: String,
    /// Parameter names of LNext (e.g., ["s", "s_", "c"])
    pub params: Vec<String>,
    /// Extracted actions from the disjunction body
    pub actions: Vec<SchedulerAction>,
}

/// Extract actions from an LNext spec function body.
///
/// The body is expected to be `Expr::Disjunction(branches)` where each branch is:
/// - `Expr::Call { func, args }` — a direct action call
/// - `Expr::Exists { vars, body: Expr::Call { func, args } }` — a quantified action
///
/// Returns None if the body is not a disjunction.
pub fn extract_lnext_actions(
    spec_fn: &SpecFunction,
    spec_prefix: &str,
    exec_prefix: &str,
) -> Option<SchedulerConfig> {
    let branches = match &spec_fn.body {
        Expr::Disjunction(branches) => branches,
        _ => return None,
    };

    let params: Vec<String> = spec_fn
        .params
        .iter()
        .map(|p| p.name.clone())
        .collect();

    let mut actions = Vec::new();

    for branch in branches {
        if let Some(action) = extract_action_from_branch(branch, spec_prefix, exec_prefix) {
            actions.push(action);
        }
    }

    Some(SchedulerConfig {
        next_fn_name: spec_fn.name.clone(),
        params,
        actions,
    })
}

/// Extract a single action from a disjunction branch.
fn extract_action_from_branch(
    expr: &Expr,
    spec_prefix: &str,
    exec_prefix: &str,
) -> Option<SchedulerAction> {
    match expr {
        // Direct call: LAction(s, s_, c)
        Expr::Call { func, args } => {
            let spec_name = func_name(func);
            let exec_name = spec_to_exec_name(&spec_name, spec_prefix, exec_prefix);
            let fixed_args = args.iter().filter_map(expr_to_ident).collect();
            Some(SchedulerAction {
                spec_name,
                exec_name,
                existential_params: vec![],
                fixed_args,
            })
        }
        // Quantified: exists |param: Type| LAction(s, s_, c, param)
        Expr::Exists { vars, body } => {
            let existential_params = extract_bindings(vars);
            match body.as_ref() {
                Expr::Call { func, args } => {
                    let spec_name = func_name(func);
                    let exec_name = spec_to_exec_name(&spec_name, spec_prefix, exec_prefix);
                    let fixed_args = args.iter().filter_map(expr_to_ident).collect();
                    Some(SchedulerAction {
                        spec_name,
                        exec_name,
                        existential_params,
                        fixed_args,
                    })
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// Get the function name from a Path.
fn func_name(path: &Path) -> String {
    path.last().unwrap_or("unknown").to_string()
}

/// Convert a spec function name to an exec function name.
/// E.g., "LTMSendPrepare" → "CTMSendPrepare" (replace L prefix with C prefix)
fn spec_to_exec_name(spec_name: &str, spec_prefix: &str, exec_prefix: &str) -> String {
    if spec_name.starts_with(spec_prefix) {
        format!("{}{}", exec_prefix, &spec_name[spec_prefix.len()..])
    } else {
        format!("{}{}", exec_prefix, spec_name)
    }
}

/// Try to extract an identifier name from an expression.
fn expr_to_ident(expr: &Expr) -> Option<String> {
    match expr {
        Expr::Ident(name) => Some(name.clone()),
        _ => None,
    }
}

/// Extract binding names and types from quantifier variables.
fn extract_bindings(bindings: &[Binding]) -> Vec<(String, String)> {
    bindings
        .iter()
        .map(|b| {
            let name = b.name_string();
            let ty = b
                .ty
                .as_ref()
                .map(type_to_string)
                .unwrap_or_else(|| "int".to_string());
            (name, ty)
        })
        .collect()
}

/// Convert a Type to a string representation.
fn type_to_string(ty: &Type) -> String {
    match ty {
        Type::Int => "int".to_string(),
        Type::Nat => "nat".to_string(),
        Type::Bool => "bool".to_string(),
        Type::Named(path) => func_name(path),
        Type::Generic(path, args) => {
            let args_str: Vec<String> = args.iter().map(type_to_string).collect();
            format!("{}<{}>", func_name(path), args_str.join(", "))
        }
        _ => "unknown".to_string(),
    }
}

/// Format a SchedulerConfig as TOML for inclusion in protocol config files.
pub fn scheduler_config_to_toml(config: &SchedulerConfig) -> String {
    let mut out = String::new();
    out.push_str(&format!(
        "# Auto-generated from {} — {} actions\n",
        config.next_fn_name,
        config.actions.len()
    ));
    out.push_str("[scheduler]\n");
    out.push_str(&format!(
        "next_fn = \"{}\"\n",
        config.next_fn_name
    ));
    out.push_str(&format!(
        "params = [{}]\n",
        config
            .params
            .iter()
            .map(|p| format!("\"{}\"", p))
            .collect::<Vec<_>>()
            .join(", ")
    ));
    out.push_str(&format!("action_count = {}\n\n", config.actions.len()));

    for (i, action) in config.actions.iter().enumerate() {
        out.push_str(&format!("[[scheduler.actions]]\n"));
        out.push_str(&format!("spec_name = \"{}\"\n", action.spec_name));
        out.push_str(&format!("exec_name = \"{}\"\n", action.exec_name));
        if !action.existential_params.is_empty() {
            let params: Vec<String> = action
                .existential_params
                .iter()
                .map(|(name, ty)| format!("[\"{}\", \"{}\"]", name, ty))
                .collect();
            out.push_str(&format!(
                "existential_params = [{}]\n",
                params.join(", ")
            ));
        }
        if i < config.actions.len() - 1 {
            out.push('\n');
        }
    }

    out
}

/// Find and analyze the LNext function in a list of parsed spec functions.
pub fn find_and_analyze_lnext(
    spec_fns: &[SpecFunction],
    next_fn_name: &str,
    spec_prefix: &str,
    exec_prefix: &str,
) -> Option<SchedulerConfig> {
    spec_fns
        .iter()
        .find(|f| f.name == next_fn_name)
        .and_then(|f| extract_lnext_actions(f, spec_prefix, exec_prefix))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::VerusParser;

    fn parse_spec_fns(source: &str) -> Vec<SpecFunction> {
        let parser = VerusParser::new(source.to_string());
        parser.parse_spec_functions().unwrap()
    }

    #[test]
    fn test_extract_simple_disjunction() {
        let source = r#"
            verus! {
                pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
                    ||| LAction1(s, s_, c)
                    ||| LAction2(s, s_, c)
                    ||| LAction3(s, s_, c)
                }
            }
        "#;
        let fns = parse_spec_fns(source);
        let config = find_and_analyze_lnext(&fns, "LNext", "L", "C").unwrap();
        assert_eq!(config.actions.len(), 3);
        assert_eq!(config.actions[0].spec_name, "LAction1");
        assert_eq!(config.actions[0].exec_name, "CAction1");
        assert_eq!(config.actions[1].spec_name, "LAction2");
        assert_eq!(config.actions[2].spec_name, "LAction3");
        assert!(config.actions[0].existential_params.is_empty());
    }

    #[test]
    fn test_extract_with_existentials() {
        let source = r#"
            verus! {
                pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
                    ||| LDirect(s, s_, c)
                    ||| (exists |rm: int| LQuantified(s, s_, c, rm))
                    ||| (exists |a: int, b: int| LMultiParam(s, s_, c, a, b))
                }
            }
        "#;
        let fns = parse_spec_fns(source);
        let config = find_and_analyze_lnext(&fns, "LNext", "L", "C").unwrap();
        assert_eq!(config.actions.len(), 3);

        // Direct call — no existentials
        assert_eq!(config.actions[0].spec_name, "LDirect");
        assert!(config.actions[0].existential_params.is_empty());

        // Single existential
        assert_eq!(config.actions[1].spec_name, "LQuantified");
        assert_eq!(config.actions[1].existential_params.len(), 1);
        assert_eq!(config.actions[1].existential_params[0].0, "rm");
        assert_eq!(config.actions[1].existential_params[0].1, "int");

        // Multiple existentials
        assert_eq!(config.actions[2].spec_name, "LMultiParam");
        assert_eq!(config.actions[2].existential_params.len(), 2);
        assert_eq!(config.actions[2].existential_params[0].0, "a");
        assert_eq!(config.actions[2].existential_params[1].0, "b");
    }

    #[test]
    fn test_extract_params() {
        let source = r#"
            verus! {
                pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
                    ||| LAction(s, s_, c)
                }
            }
        "#;
        let fns = parse_spec_fns(source);
        let config = find_and_analyze_lnext(&fns, "LNext", "L", "C").unwrap();
        assert_eq!(config.params, vec!["s", "s_", "c"]);
        assert_eq!(config.next_fn_name, "LNext");
    }

    #[test]
    fn test_spec_to_exec_name() {
        assert_eq!(spec_to_exec_name("LAction", "L", "C"), "CAction");
        assert_eq!(
            spec_to_exec_name("LTMSendPrepare", "L", "C"),
            "CTMSendPrepare"
        );
        assert_eq!(spec_to_exec_name("NoPrefix", "L", "C"), "CNoPrefix");
    }

    #[test]
    fn test_toml_output() {
        let config = SchedulerConfig {
            next_fn_name: "LNext".to_string(),
            params: vec!["s".to_string(), "s_".to_string(), "c".to_string()],
            actions: vec![
                SchedulerAction {
                    spec_name: "LDirect".to_string(),
                    exec_name: "CDirect".to_string(),
                    existential_params: vec![],
                    fixed_args: vec!["s".to_string(), "s_".to_string(), "c".to_string()],
                },
                SchedulerAction {
                    spec_name: "LQuantified".to_string(),
                    exec_name: "CQuantified".to_string(),
                    existential_params: vec![("rm".to_string(), "int".to_string())],
                    fixed_args: vec![
                        "s".to_string(),
                        "s_".to_string(),
                        "c".to_string(),
                        "rm".to_string(),
                    ],
                },
            ],
        };
        let toml = scheduler_config_to_toml(&config);
        assert!(toml.contains("[scheduler]"));
        assert!(toml.contains("next_fn = \"LNext\""));
        assert!(toml.contains("action_count = 2"));
        assert!(toml.contains("spec_name = \"LDirect\""));
        assert!(toml.contains("exec_name = \"CDirect\""));
        assert!(toml.contains("spec_name = \"LQuantified\""));
        assert!(toml.contains("existential_params = [[\"rm\", \"int\"]]"));
    }

    #[test]
    fn test_non_disjunction_returns_none() {
        let source = r#"
            verus! {
                pub open spec fn LInit(s: LState, c: LConstants) -> bool {
                    &&& s.value == 0
                    &&& s.ready == true
                }
            }
        "#;
        let fns = parse_spec_fns(source);
        let result = find_and_analyze_lnext(&fns, "LInit", "L", "C");
        assert!(result.is_none(), "Non-disjunction body should return None");
    }

    #[test]
    fn test_missing_function_returns_none() {
        let source = r#"
            verus! {
                pub open spec fn LInit(s: LState) -> bool {
                    s.value == 0
                }
            }
        "#;
        let fns = parse_spec_fns(source);
        let result = find_and_analyze_lnext(&fns, "LNext", "L", "C");
        assert!(result.is_none(), "Missing function should return None");
    }

    #[test]
    fn test_twophase_lnext() {
        let source = std::fs::read_to_string("../src/protocol/TwoPhase/twophase.rs")
            .expect("Failed to read TwoPhase spec");
        let fns = parse_spec_fns(&source);
        let config = find_and_analyze_lnext(&fns, "LNext", "L", "C").unwrap();
        assert_eq!(config.actions.len(), 8, "TwoPhase LNext has 8 branches");

        // Check specific actions
        let names: Vec<&str> = config.actions.iter().map(|a| a.spec_name.as_str()).collect();
        assert!(names.contains(&"LTMSendPrepare"));
        assert!(names.contains(&"LRMReceivePrepare"));
        assert!(names.contains(&"LTMRcvPrepared"));
        assert!(names.contains(&"LTMSendCommit"));
        assert!(names.contains(&"LTMSendAbort"));

        // LTMSendPrepare is direct (no existential)
        let send_prepare = config.actions.iter().find(|a| a.spec_name == "LTMSendPrepare").unwrap();
        assert!(send_prepare.existential_params.is_empty());

        // LRMReceivePrepare has exists |rm: int|
        let rcv_prepare = config.actions.iter().find(|a| a.spec_name == "LRMReceivePrepare").unwrap();
        assert_eq!(rcv_prepare.existential_params.len(), 1);
        assert_eq!(rcv_prepare.existential_params[0].0, "rm");
    }

    #[test]
    fn test_raft_lnext() {
        let source = std::fs::read_to_string("../src/protocol/Raft/raft.rs")
            .expect("Failed to read Raft spec");
        let fns = parse_spec_fns(&source);
        let config = find_and_analyze_lnext(&fns, "LNext", "L", "C").unwrap();
        assert_eq!(config.actions.len(), 11, "Raft LNext has 11 branches");

        let names: Vec<&str> = config.actions.iter().map(|a| a.spec_name.as_str()).collect();
        assert!(names.contains(&"LTimeout"));
        assert!(names.contains(&"LGrantVote"));
        assert!(names.contains(&"LBecomeLeader"));
        assert!(names.contains(&"LClientRequest"));
        assert!(names.contains(&"LAdvanceCommitIndex"));
    }

    #[test]
    fn test_epaxos_lnext() {
        let source = std::fs::read_to_string("../src/protocol/EPaxos/epaxos.rs")
            .expect("Failed to read EPaxos spec");
        let fns = parse_spec_fns(&source);
        let config = find_and_analyze_lnext(&fns, "LNext", "L", "C").unwrap();
        assert_eq!(config.actions.len(), 11, "EPaxos LNext has 11 branches");
    }
}
