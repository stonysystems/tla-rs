//! Scheduler generation from LNext disjunction structure.
//!
//! Analyzes the LNext spec function body to extract the list of protocol
//! actions, their existential parameters, and generates a scheduler config
//! that can be used to produce the runtime host/scheduler code.
//!
//! Phase 17.4.2 adds action classification (message_driven vs timer_driven)
//! using name-based heuristics and optional message variant mapping.

use crate::ast::{Binding, Expr, Path, SpecFunction, Type};

/// How an action is triggered at runtime.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ActionKind {
    /// Triggered by receiving a specific message variant.
    MessageDriven,
    /// Triggered by a timer/timeout event (round-robin scheduled).
    TimerDriven,
}

impl std::fmt::Display for ActionKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ActionKind::MessageDriven => write!(f, "message_driven"),
            ActionKind::TimerDriven => write!(f, "timer_driven"),
        }
    }
}

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
    /// Whether this action is message_driven or timer_driven.
    pub kind: ActionKind,
    /// For message_driven actions, the message variant that triggers it.
    /// E.g., "Prepare", "Promise", etc.
    pub message_variant: Option<String>,
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
/// The kind and message_variant are set to defaults here;
/// classification happens in a separate pass via `classify_actions`.
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
                kind: ActionKind::TimerDriven,
                message_variant: None,
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
                        kind: ActionKind::TimerDriven,
                        message_variant: None,
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

/// Classify actions in a SchedulerConfig as message_driven or timer_driven
/// using name-based heuristics and optional message variant names.
///
/// Heuristics (applied to the spec name after removing the spec prefix):
/// - Contains "Receive", "Rcv", or "Handle" → message_driven
/// - Starts with "GrantVote", "BecomeLeader", "StepDown" → message_driven (response to received message)
/// - Contains "Timeout", "DetectFailure" → timer_driven
/// - Specific known patterns per protocol (e.g., Paxos "Send1b"/"Send2b" are responses)
///
/// If `message_variants` is provided (from the [messages] TOML section), we also
/// try to match actions to message variants for the `message_variant` field.
pub fn classify_actions(config: &mut SchedulerConfig, message_variants: &[String]) {
    for action in &mut config.actions {
        let (kind, variant) = classify_single_action(&action.spec_name, message_variants);
        action.kind = kind;
        action.message_variant = variant;
    }
}

/// Classify a single action by its spec name.
/// Returns (ActionKind, Option<message_variant_name>).
fn classify_single_action(
    spec_name: &str,
    message_variants: &[String],
) -> (ActionKind, Option<String>) {
    // Normalize: strip common spec prefix "L" for pattern matching
    let name = if spec_name.starts_with('L') {
        &spec_name[1..]
    } else {
        spec_name
    };
    let name_lower = name.to_lowercase();

    // Strong message-driven indicators
    let message_keywords = ["receive", "rcv", "recv", "handle"];
    if message_keywords.iter().any(|kw| name_lower.contains(kw)) {
        let variant = find_matching_variant(name, message_variants);
        return (ActionKind::MessageDriven, variant);
    }

    // Known message-driven response patterns (triggered by incoming messages
    // even though their names don't contain "Receive"/"Rcv"):
    // - Paxos: Send1b (response to Prepare), Send2b (response to Accept)
    // - LeaderElection: SendAnswer (response to Election)
    // - Raft: GrantVote (response to RequestVote), BecomeLeader, StepDown,
    //         FollowerAppendEntries (response to AppendEntries)
    // - EPaxos: SendPreAcceptOk, SendAcceptOk
    let message_response_patterns = [
        "Send1b", "Send2b",        // Paxos
        "SendAnswer",              // LeaderElection (response to Election msg)
        "GrantVote",               // Raft
        "BecomeLeader",            // Raft (triggered after collecting votes)
        "StepDown",                // Raft (triggered by higher-term message)
        "FollowerAppendEntries",   // Raft
        "SendPreAcceptOk",         // EPaxos
        "SendAcceptOk",            // EPaxos
        "SendPromise",             // VerticalPaxos
        "WitnessSync",             // VerticalPaxos (response to Sync message)
        "Sync",                    // VerticalPaxos (joining new config via Sync)
        "PrePrepare",              // PBFT (response to ClientRequest)
        "EnterCommit",             // PBFT (triggered by Prepare quorum)
        "ExecuteReply",            // PBFT (triggered by Commit quorum)
        "PrimaryWrite",            // PrimaryBackup (response to ClientRequest)
        "ClientRead",              // ChainReplication (tail responds to read)
    ];
    if message_response_patterns.iter().any(|p| name.contains(p)) {
        let variant = find_matching_variant(name, message_variants);
        return (ActionKind::MessageDriven, variant);
    }

    // Strong timer-driven indicators
    let timer_keywords = ["timeout", "detectfailure"];
    if timer_keywords.iter().any(|kw| name_lower.contains(kw)) {
        return (ActionKind::TimerDriven, None);
    }

    // Default: actions without receive/response patterns are timer-driven
    // (spontaneous actions triggered by round-robin scheduling)
    (ActionKind::TimerDriven, None)
}

/// Try to find a matching message variant for an action name.
/// Uses multiple strategies with priority ordering:
/// 1. Keyword extraction (most precise): strip role prefix + verb, match against variants
/// 2. Full variant name containment in action name (longest wins)
fn find_matching_variant(action_suffix: &str, message_variants: &[String]) -> Option<String> {
    // Strategy 1 (most precise): Extract keyword, find best variant match.
    // E.g., "TMRcvPrepared" → keyword "Prepared" → variant "PreparedVote"
    let keyword = extract_action_keyword(action_suffix);
    if !keyword.is_empty() {
        let keyword_lower = keyword.to_lowercase();

        // 1a: Exact match (keyword == variant name, case-insensitive)
        for variant in message_variants {
            if variant.to_lowercase() == keyword_lower {
                return Some(variant.clone());
            }
        }

        // 1b: Variant name starts with keyword, prefer shortest variant
        // (closest to the keyword, e.g., "Prepare" over "PreparedVote")
        let mut best: Option<&String> = None;
        for variant in message_variants {
            let variant_lower = variant.to_lowercase();
            if variant_lower.starts_with(&keyword_lower) {
                if best.map_or(true, |b| variant.len() < b.len()) {
                    best = Some(variant);
                }
            }
        }
        if let Some(variant) = best {
            return Some(variant.clone());
        }

        // 1b: Keyword starts with variant name (e.g., keyword "Prepared" starts with "Prepare")
        // or exact containment between keyword and variant
        let mut best_match: Option<(usize, &String)> = None;
        for variant in message_variants {
            let variant_lower = variant.to_lowercase();
            if keyword_lower.contains(&variant_lower) || variant_lower.contains(&keyword_lower) {
                let len = variant.len();
                if best_match.map_or(true, |(best_len, _)| len > best_len) {
                    best_match = Some((len, variant));
                }
            }
        }
        if let Some((_, variant)) = best_match {
            return Some(variant.clone());
        }
    }

    // Strategy 2: Full variant name appears in the action name (longest match wins)
    let action_lower = action_suffix.to_lowercase();
    let mut best_match: Option<(usize, &String)> = None;
    for variant in message_variants {
        let variant_lower = variant.to_lowercase();
        if action_lower.contains(&variant_lower) {
            let len = variant.len();
            if best_match.map_or(true, |(best_len, _)| len > best_len) {
                best_match = Some((len, variant));
            }
        }
    }
    if let Some((_, variant)) = best_match {
        return Some(variant.clone());
    }

    None
}

/// Extract the "keyword" part of an action name by stripping:
/// - Role prefixes (TM, RM, Primary, etc.)
/// - Action verbs (Receive, Rcv, Recv, Handle, Send)
/// E.g., "TMRcvPrepared" → "Prepared", "RMReceiveCommit" → "Commit"
fn extract_action_keyword(name: &str) -> &str {
    let stripped = strip_role_prefix(name);
    // Strip action verb prefixes
    let verb_prefixes = ["Receive", "Rcv", "Recv", "Handle", "Send"];
    for prefix in &verb_prefixes {
        if stripped.starts_with(prefix) {
            return &stripped[prefix.len()..];
        }
    }
    stripped
}

/// Strip common role prefixes from action names for variant matching.
fn strip_role_prefix(name: &str) -> &str {
    let role_prefixes = [
        "TM", "RM", "Primary", "Backup", "Head", "Tail", "Middle",
        "Follower", "Leader", "Candidate",
    ];
    for prefix in &role_prefixes {
        if name.starts_with(prefix) {
            return &name[prefix.len()..];
        }
    }
    name
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
        out.push_str("[[scheduler.actions]]\n");
        out.push_str(&format!("spec_name = \"{}\"\n", action.spec_name));
        out.push_str(&format!("exec_name = \"{}\"\n", action.exec_name));
        out.push_str(&format!("kind = \"{}\"\n", action.kind));
        if let Some(ref variant) = action.message_variant {
            out.push_str(&format!("message_variant = \"{}\"\n", variant));
        }
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
                    kind: ActionKind::TimerDriven,
                    message_variant: None,
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
                    kind: ActionKind::MessageDriven,
                    message_variant: Some("Prepare".to_string()),
                },
            ],
        };
        let toml = scheduler_config_to_toml(&config);
        assert!(toml.contains("[scheduler]"));
        assert!(toml.contains("next_fn = \"LNext\""));
        assert!(toml.contains("action_count = 2"));
        assert!(toml.contains("spec_name = \"LDirect\""));
        assert!(toml.contains("exec_name = \"CDirect\""));
        assert!(toml.contains("kind = \"timer_driven\""));
        assert!(toml.contains("kind = \"message_driven\""));
        assert!(toml.contains("message_variant = \"Prepare\""));
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

    // --- Classification tests ---

    #[test]
    fn test_classify_receive_keyword() {
        let (kind, _) = classify_single_action("LRMReceivePrepare", &[]);
        assert_eq!(kind, ActionKind::MessageDriven);
    }

    #[test]
    fn test_classify_rcv_keyword() {
        let (kind, _) = classify_single_action("LTMRcvPrepared", &[]);
        assert_eq!(kind, ActionKind::MessageDriven);
    }

    #[test]
    fn test_classify_handle_keyword() {
        let (kind, _) = classify_single_action("LHandleAppendResponse", &[]);
        assert_eq!(kind, ActionKind::MessageDriven);
    }

    #[test]
    fn test_classify_timeout() {
        let (kind, _) = classify_single_action("LTimeout", &[]);
        assert_eq!(kind, ActionKind::TimerDriven);
    }

    #[test]
    fn test_classify_detect_failure() {
        let (kind, _) = classify_single_action("LDetectFailure", &[]);
        assert_eq!(kind, ActionKind::TimerDriven);
    }

    #[test]
    fn test_classify_paxos_send1b_message_response() {
        let (kind, _) = classify_single_action("LSend1b", &[]);
        assert_eq!(kind, ActionKind::MessageDriven, "Send1b is a response to Prepare");
    }

    #[test]
    fn test_classify_paxos_send2b_message_response() {
        let (kind, _) = classify_single_action("LSend2b", &[]);
        assert_eq!(kind, ActionKind::MessageDriven, "Send2b is a response to Accept");
    }

    #[test]
    fn test_classify_grant_vote() {
        let (kind, _) = classify_single_action("LGrantVote", &[]);
        assert_eq!(kind, ActionKind::MessageDriven);
    }

    #[test]
    fn test_classify_become_leader() {
        let (kind, _) = classify_single_action("LBecomeLeader", &[]);
        assert_eq!(kind, ActionKind::MessageDriven);
    }

    #[test]
    fn test_classify_send_prepare_timer() {
        // TMSendPrepare is a spontaneous action (TM initiates prepare)
        let (kind, _) = classify_single_action("LTMSendPrepare", &[]);
        assert_eq!(kind, ActionKind::TimerDriven);
    }

    #[test]
    fn test_classify_send1a_timer() {
        // Send1a is Paxos proposer initiating Phase 1
        let (kind, _) = classify_single_action("LSend1a", &[]);
        assert_eq!(kind, ActionKind::TimerDriven);
    }

    #[test]
    fn test_classify_learn_timer() {
        let (kind, _) = classify_single_action("LLearn", &[]);
        assert_eq!(kind, ActionKind::TimerDriven);
    }

    #[test]
    fn test_classify_client_request_timer() {
        let (kind, _) = classify_single_action("LClientRequest", &[]);
        assert_eq!(kind, ActionKind::TimerDriven);
    }

    #[test]
    fn test_classify_with_variant_matching() {
        let variants = vec!["Prepare".to_string(), "Promise".to_string()];
        let (kind, variant) = classify_single_action("LRMReceivePrepare", &variants);
        assert_eq!(kind, ActionKind::MessageDriven);
        assert_eq!(variant, Some("Prepare".to_string()));
    }

    #[test]
    fn test_classify_rcv_with_variant_matching() {
        let variants = vec!["Prepare".to_string(), "PreparedVote".to_string()];
        let (kind, variant) = classify_single_action("LTMRcvPrepared", &variants);
        assert_eq!(kind, ActionKind::MessageDriven);
        assert_eq!(variant, Some("PreparedVote".to_string()));
    }

    #[test]
    fn test_strip_role_prefix() {
        assert_eq!(strip_role_prefix("TMSendPrepare"), "SendPrepare");
        assert_eq!(strip_role_prefix("RMReceivePrepare"), "ReceivePrepare");
        assert_eq!(strip_role_prefix("FollowerAppendEntries"), "AppendEntries");
        assert_eq!(strip_role_prefix("PrimaryWrite"), "Write");
        assert_eq!(strip_role_prefix("NoPrefix"), "NoPrefix");
    }

    #[test]
    fn test_classify_twophase_full() {
        let source = std::fs::read_to_string("../src/protocol/TwoPhase/twophase.rs")
            .expect("Failed to read TwoPhase spec");
        let fns = parse_spec_fns(&source);
        let mut config = find_and_analyze_lnext(&fns, "LNext", "L", "C").unwrap();
        let variants = vec![
            "Prepare".to_string(),
            "PreparedVote".to_string(),
            "Commit".to_string(),
            "Abort".to_string(),
        ];
        classify_actions(&mut config, &variants);

        let find = |name: &str| config.actions.iter().find(|a| a.spec_name == name).unwrap();

        // Timer-driven: TM initiates
        assert_eq!(find("LTMSendPrepare").kind, ActionKind::TimerDriven);
        assert_eq!(find("LTMSendCommit").kind, ActionKind::TimerDriven);
        assert_eq!(find("LTMSendAbort").kind, ActionKind::TimerDriven);

        // Message-driven: RM receives, TM receives
        assert_eq!(find("LRMReceivePrepare").kind, ActionKind::MessageDriven);
        assert_eq!(find("LRMReceiveCommit").kind, ActionKind::MessageDriven);
        assert_eq!(find("LRMReceiveAbort").kind, ActionKind::MessageDriven);
        assert_eq!(find("LTMRcvPrepared").kind, ActionKind::MessageDriven);

        // Variant matching
        assert_eq!(find("LRMReceivePrepare").message_variant, Some("Prepare".to_string()));
        assert_eq!(find("LRMReceiveCommit").message_variant, Some("Commit".to_string()));
        assert_eq!(find("LTMRcvPrepared").message_variant, Some("PreparedVote".to_string()));
    }

    #[test]
    fn test_classify_paxos_full() {
        let source = std::fs::read_to_string("../src/protocol/Paxos/paxos.rs")
            .expect("Failed to read Paxos spec");
        let fns = parse_spec_fns(&source);
        let mut config = find_and_analyze_lnext(&fns, "LNext", "L", "C").unwrap();
        let variants = vec![
            "Prepare".to_string(),
            "Promise".to_string(),
            "Accept".to_string(),
            "Accepted".to_string(),
        ];
        classify_actions(&mut config, &variants);

        let find = |name: &str| config.actions.iter().find(|a| a.spec_name == name).unwrap();

        // Timer-driven: Proposer initiates
        assert_eq!(find("LSend1a").kind, ActionKind::TimerDriven);
        assert_eq!(find("LSend2a").kind, ActionKind::TimerDriven);
        assert_eq!(find("LLearn").kind, ActionKind::TimerDriven);

        // Message-driven: responses
        assert_eq!(find("LSend1b").kind, ActionKind::MessageDriven);
        assert_eq!(find("LRecvPromise").kind, ActionKind::MessageDriven);
        assert_eq!(find("LSend2b").kind, ActionKind::MessageDriven);
        assert_eq!(find("LRecvAccepted").kind, ActionKind::MessageDriven);
    }

    #[test]
    fn test_classify_raft_full() {
        let source = std::fs::read_to_string("../src/protocol/Raft/raft.rs")
            .expect("Failed to read Raft spec");
        let fns = parse_spec_fns(&source);
        let mut config = find_and_analyze_lnext(&fns, "LNext", "L", "C").unwrap();
        let variants = vec![
            "RequestVote".to_string(),
            "VoteResponse".to_string(),
            "AppendEntries".to_string(),
            "AppendResponse".to_string(),
        ];
        classify_actions(&mut config, &variants);

        let find = |name: &str| config.actions.iter().find(|a| a.spec_name == name).unwrap();

        // Timer-driven
        assert_eq!(find("LTimeout").kind, ActionKind::TimerDriven);
        assert_eq!(find("LSendAppendEntries").kind, ActionKind::TimerDriven);
        assert_eq!(find("LAdvanceCommitIndex").kind, ActionKind::TimerDriven);
        assert_eq!(find("LClientRequest").kind, ActionKind::TimerDriven);

        // Message-driven
        assert_eq!(find("LGrantVote").kind, ActionKind::MessageDriven);
        assert_eq!(find("LReceiveVoteGranted").kind, ActionKind::MessageDriven);
        assert_eq!(find("LFollowerAppendEntries").kind, ActionKind::MessageDriven);
        assert_eq!(find("LBecomeLeader").kind, ActionKind::MessageDriven);
        assert_eq!(find("LStepDown").kind, ActionKind::MessageDriven);
        assert_eq!(find("LHandleAppendResponse").kind, ActionKind::MessageDriven);
        assert_eq!(find("LHandleAppendReject").kind, ActionKind::MessageDriven);
    }

    #[test]
    fn test_classify_leader_election_full() {
        let source = std::fs::read_to_string("../src/protocol/LeaderElection/election.rs")
            .expect("Failed to read LeaderElection spec");
        let fns = parse_spec_fns(&source);
        let mut config = find_and_analyze_lnext(&fns, "LNext", "L", "C").unwrap();
        let variants = vec![
            "Election".to_string(),
            "Answer".to_string(),
            "Coordinator".to_string(),
        ];
        classify_actions(&mut config, &variants);

        let find = |name: &str| config.actions.iter().find(|a| a.spec_name == name).unwrap();

        // Timer-driven
        assert_eq!(find("LDetectFailure").kind, ActionKind::TimerDriven);
        assert_eq!(find("LStartElection").kind, ActionKind::TimerDriven);
        assert_eq!(find("LSendCoordinator").kind, ActionKind::TimerDriven);
        assert_eq!(find("LNodeFail").kind, ActionKind::TimerDriven);

        // Message-driven
        assert_eq!(find("LSendAnswer").kind, ActionKind::MessageDriven);
        assert_eq!(find("LReceiveAnswer").kind, ActionKind::MessageDriven);
        assert_eq!(find("LReceiveCoordinator").kind, ActionKind::MessageDriven);

        // Variant matching
        assert_eq!(find("LReceiveAnswer").message_variant, Some("Answer".to_string()));
        assert_eq!(find("LReceiveCoordinator").message_variant, Some("Coordinator".to_string()));
    }

    #[test]
    fn test_classify_primary_backup_full() {
        let source = std::fs::read_to_string("../src/protocol/PrimaryBackup/primarybackup.rs")
            .expect("Failed to read PrimaryBackup spec");
        let fns = parse_spec_fns(&source);
        let mut config = find_and_analyze_lnext(&fns, "LNext", "L", "C").unwrap();
        let variants = vec![
            "Replicate".to_string(),
            "Ack".to_string(),
            "ClientRequest".to_string(),
        ];
        classify_actions(&mut config, &variants);

        let find = |name: &str| config.actions.iter().find(|a| a.spec_name == name).unwrap();

        // Timer-driven
        assert_eq!(find("LPrimarySendReplicate").kind, ActionKind::TimerDriven);
        assert_eq!(find("LBackupSendAck").kind, ActionKind::TimerDriven);
        assert_eq!(find("LPrimaryCommit").kind, ActionKind::TimerDriven);
        assert_eq!(find("LPrimaryFail").kind, ActionKind::TimerDriven);
        assert_eq!(find("LBackupPromote").kind, ActionKind::TimerDriven);

        // Message-driven
        assert_eq!(find("LPrimaryWrite").kind, ActionKind::MessageDriven);
        assert_eq!(find("LBackupReceiveReplicate").kind, ActionKind::MessageDriven);
        assert_eq!(find("LPrimaryReceiveAck").kind, ActionKind::MessageDriven);

        // Variant matching
        assert_eq!(find("LBackupReceiveReplicate").message_variant, Some("Replicate".to_string()));
        assert_eq!(find("LPrimaryReceiveAck").message_variant, Some("Ack".to_string()));
    }

    #[test]
    fn test_classify_chain_replication_full() {
        let source = std::fs::read_to_string("../src/protocol/ChainReplication/chain.rs")
            .expect("Failed to read ChainReplication spec");
        let fns = parse_spec_fns(&source);
        let mut config = find_and_analyze_lnext(&fns, "LNext", "L", "C").unwrap();
        let variants = vec![
            "Forward".to_string(),
            "Ack".to_string(),
            "ClientWrite".to_string(),
            "ClientRead".to_string(),
        ];
        classify_actions(&mut config, &variants);

        let find = |name: &str| config.actions.iter().find(|a| a.spec_name == name).unwrap();

        // Timer-driven
        assert_eq!(find("LForwardToSuccessor").kind, ActionKind::TimerDriven);
        assert_eq!(find("LTailCommit").kind, ActionKind::TimerDriven);
        assert_eq!(find("LNodeFail").kind, ActionKind::TimerDriven);
        assert_eq!(find("LReconfigure").kind, ActionKind::TimerDriven);

        // Message-driven
        assert_eq!(find("LHeadReceiveWrite").kind, ActionKind::MessageDriven);
        assert_eq!(find("LReceiveUpdate").kind, ActionKind::MessageDriven);
        assert_eq!(find("LReceiveAck").kind, ActionKind::MessageDriven);
        assert_eq!(find("LClientRead").kind, ActionKind::MessageDriven);

        // Variant matching
        assert_eq!(find("LReceiveAck").message_variant, Some("Ack".to_string()));
    }

    #[test]
    fn test_classify_pbft_full() {
        let source = std::fs::read_to_string("../src/protocol/PBFT/pbft.rs")
            .expect("Failed to read PBFT spec");
        let fns = parse_spec_fns(&source);
        let mut config = find_and_analyze_lnext(&fns, "LNext", "L", "C").unwrap();
        let variants = vec![
            "PrePrepare".to_string(),
            "Prepare".to_string(),
            "Commit".to_string(),
            "ClientRequest".to_string(),
        ];
        classify_actions(&mut config, &variants);

        let find = |name: &str| config.actions.iter().find(|a| a.spec_name == name).unwrap();

        // Timer-driven
        assert_eq!(find("LCheckpoint").kind, ActionKind::TimerDriven);
        assert_eq!(find("LViewChange").kind, ActionKind::TimerDriven);
        assert_eq!(find("LNewRound").kind, ActionKind::TimerDriven);

        // Message-driven
        assert_eq!(find("LPrePrepare").kind, ActionKind::MessageDriven);
        assert_eq!(find("LReceivePrePrepare").kind, ActionKind::MessageDriven);
        assert_eq!(find("LReceivePrepare").kind, ActionKind::MessageDriven);
        assert_eq!(find("LEnterCommit").kind, ActionKind::MessageDriven);
        assert_eq!(find("LReceiveCommit").kind, ActionKind::MessageDriven);
        assert_eq!(find("LExecuteReply").kind, ActionKind::MessageDriven);

        // Variant matching
        assert_eq!(find("LReceivePrePrepare").message_variant, Some("PrePrepare".to_string()));
        assert_eq!(find("LReceivePrepare").message_variant, Some("Prepare".to_string()));
        assert_eq!(find("LReceiveCommit").message_variant, Some("Commit".to_string()));
    }

    #[test]
    fn test_classify_vertical_paxos_full() {
        let source = std::fs::read_to_string("../src/protocol/VerticalPaxos/vpaxos.rs")
            .expect("Failed to read VerticalPaxos spec");
        let fns = parse_spec_fns(&source);
        let mut config = find_and_analyze_lnext(&fns, "LNext", "L", "C").unwrap();
        let variants = vec![
            "Prepare".to_string(),
            "Promise".to_string(),
            "Accept".to_string(),
            "AcceptOk".to_string(),
            "Commit".to_string(),
            "Sync".to_string(),
        ];
        classify_actions(&mut config, &variants);

        let find = |name: &str| config.actions.iter().find(|a| a.spec_name == name).unwrap();

        // Timer-driven
        assert_eq!(find("LPrepare").kind, ActionKind::TimerDriven);
        assert_eq!(find("LAccept").kind, ActionKind::TimerDriven);
        assert_eq!(find("LCommit").kind, ActionKind::TimerDriven);
        assert_eq!(find("LReconfigure").kind, ActionKind::TimerDriven);
        assert_eq!(find("LDeactivate").kind, ActionKind::TimerDriven);

        // Message-driven
        assert_eq!(find("LSendPromise").kind, ActionKind::MessageDriven);
        assert_eq!(find("LReceivePromise").kind, ActionKind::MessageDriven);
        assert_eq!(find("LReceiveAccepted").kind, ActionKind::MessageDriven);
        assert_eq!(find("LWitnessSync").kind, ActionKind::MessageDriven);
        assert_eq!(find("LSync").kind, ActionKind::MessageDriven);
    }

    #[test]
    fn test_classify_epaxos_full() {
        let source = std::fs::read_to_string("../src/protocol/EPaxos/epaxos.rs")
            .expect("Failed to read EPaxos spec");
        let fns = parse_spec_fns(&source);
        let mut config = find_and_analyze_lnext(&fns, "LNext", "L", "C").unwrap();
        let variants = vec![
            "PreAccept".to_string(),
            "PreAcceptOk".to_string(),
            "Accept".to_string(),
            "AcceptOk".to_string(),
            "CommitMsg".to_string(),
        ];
        classify_actions(&mut config, &variants);

        let find = |name: &str| config.actions.iter().find(|a| a.spec_name == name).unwrap();

        // Timer-driven
        assert_eq!(find("LPropose").kind, ActionKind::TimerDriven);
        assert_eq!(find("LFastCommit").kind, ActionKind::TimerDriven);
        assert_eq!(find("LStartAccept").kind, ActionKind::TimerDriven);
        assert_eq!(find("LSlowCommit").kind, ActionKind::TimerDriven);
        assert_eq!(find("LExecute").kind, ActionKind::TimerDriven);
        assert_eq!(find("LRecover").kind, ActionKind::TimerDriven);
        assert_eq!(find("LNewInstance").kind, ActionKind::TimerDriven);

        // Message-driven
        assert_eq!(find("LSendPreAcceptOk").kind, ActionKind::MessageDriven);
        assert_eq!(find("LReceivePreAcceptOk").kind, ActionKind::MessageDriven);
        assert_eq!(find("LSendAcceptOk").kind, ActionKind::MessageDriven);
        assert_eq!(find("LReceiveAcceptOk").kind, ActionKind::MessageDriven);

        // Variant matching
        assert_eq!(find("LReceivePreAcceptOk").message_variant, Some("PreAcceptOk".to_string()));
        assert_eq!(find("LReceiveAcceptOk").message_variant, Some("AcceptOk".to_string()));
    }

    #[test]
    fn test_action_kind_display() {
        assert_eq!(format!("{}", ActionKind::MessageDriven), "message_driven");
        assert_eq!(format!("{}", ActionKind::TimerDriven), "timer_driven");
    }

    #[test]
    fn test_classify_no_variants_still_works() {
        // Classification should work even without message variants (no variant matching)
        let (kind, variant) = classify_single_action("LReceivePrepare", &[]);
        assert_eq!(kind, ActionKind::MessageDriven);
        assert!(variant.is_none());
    }
}
