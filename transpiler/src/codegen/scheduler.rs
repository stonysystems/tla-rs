//! Scheduler generation from LNext disjunction structure.
//!
//! Analyzes the LNext spec function body to extract the list of protocol
//! actions, their existential parameters, and generates a scheduler config
//! that can be used to produce the runtime host/scheduler code.
//!
//! Phase 17.4.2 adds action classification (message_driven vs timer_driven)
//! using name-based heuristics and optional message variant mapping.

use crate::ast::{Binding, Expr, Path, SpecFunction, Type};
use crate::config::{MessageVariant, SchedulerActionConfig};

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

/// Parameters for generating a host.rs scaffold.
pub struct HostScaffoldParams {
    /// Protocol name in PascalCase (e.g., "Paxos", "TwoPhase")
    pub protocol_name: String,
    /// Module name in snake_case (e.g., "paxos", "twophase")
    pub module_name: String,
    /// Generated module name (e.g., "paxos_gen")
    pub gen_module: String,
    /// Message enum name (e.g., "PaxosMessage")
    pub message_enum: String,
    /// Message variants with their fields
    pub message_variants: Vec<MessageVariant>,
    /// Scheduler actions from the TOML config
    pub actions: Vec<SchedulerActionConfig>,
}

/// Generate a host.rs scaffold from a scheduler config and message config.
///
/// The scaffold includes:
/// - Config struct with `ProtocolConfig` trait impl
/// - Host struct with `ProtocolHost` trait impl
/// - Message dispatch in `next()` method
/// - Round-robin timer dispatch
/// - Stub handler methods with TODO comments
///
/// The generated code compiles but handler stubs return `GenericOutbound::None`.
/// Protocol-specific guard logic and outbound message construction must be
/// hand-edited.
pub fn generate_host_scaffold(params: &HostScaffoldParams) -> String {
    let mut out = String::new();

    // Module doc comment
    emit_header(&mut out, params);

    // Imports
    emit_imports(&mut out, params);

    // Config struct + ProtocolConfig impl
    emit_config(&mut out, params);

    // Host struct
    emit_host_struct(&mut out, params);

    // Handler methods (message-driven + timer-driven stubs)
    emit_handler_methods(&mut out, params);

    // ProtocolHost trait impl (init + next)
    emit_protocol_host_impl(&mut out, params);

    out
}

fn emit_header(out: &mut String, params: &HostScaffoldParams) {
    out.push_str(&format!(
        "//! {} protocol host implementation.\n",
        params.protocol_name
    ));
    out.push_str("//!\n");
    out.push_str("//! Auto-generated scaffold by the transpiler.\n");
    out.push_str("//! TODO: Add protocol-specific guard logic and outbound message construction.\n");
    out.push('\n');
}

fn emit_imports(out: &mut String, params: &HostScaffoldParams) {
    out.push_str("use crate::common::framework::args_t::*;\n");
    out.push_str("use crate::common::framework::protocol_trait::*;\n");
    out.push_str("use crate::common::native::io_s::*;\n");
    out.push_str(&format!(
        "use crate::generated::{}::{};\n",
        params.protocol_name, params.gen_module
    ));
    out.push_str(&format!(
        "use crate::generated::{}::types_gen::*;\n",
        params.protocol_name
    ));
    out.push_str(&format!(
        "use crate::implementation::{}::message::*;\n",
        params.protocol_name
    ));
    out.push_str("use std::collections::HashSet;\n");
    out.push('\n');
}

fn emit_config(out: &mut String, params: &HostScaffoldParams) {
    // Config struct
    out.push_str(&format!(
        "/// {} protocol configuration.\n",
        params.protocol_name
    ));
    out.push_str(&format!("pub struct {}Config {{\n", params.protocol_name));
    out.push_str("    /// All peer endpoints (ordered by node index).\n");
    out.push_str("    pub peers: Vec<EndPoint>,\n");
    out.push_str("    /// This node's index in the peers list.\n");
    out.push_str("    pub my_index: u64,\n");
    out.push_str("    /// Protocol constants.\n");
    out.push_str("    pub constants: CConstants,\n");
    out.push_str("}\n\n");

    // ProtocolConfig impl
    out.push_str(&format!(
        "impl ProtocolConfig for {}Config {{\n",
        params.protocol_name
    ));
    out.push_str("    fn parse_config(me: &EndPoint, args: &Args) -> Option<Self> {\n");
    out.push_str("        if args.len() < 2 {\n");
    out.push_str(&format!(
        "            eprintln!(\"{}: need at least 2 args (self + peers)\");\n",
        params.protocol_name
    ));
    out.push_str("            return None;\n");
    out.push_str("        }\n\n");
    out.push_str("        let mut peers: Vec<EndPoint> = Vec::new();\n");
    out.push_str("        let mut my_index: Option<u64> = None;\n\n");
    out.push_str("        for i in 0..args.len() {\n");
    out.push_str("            let ep = EndPoint { id: args[i].clone() };\n");
    out.push_str("            if ep.id == me.id {\n");
    out.push_str("                my_index = Some(i as u64);\n");
    out.push_str("            }\n");
    out.push_str("            peers.push(ep);\n");
    out.push_str("        }\n\n");
    out.push_str("        let my_index = match my_index {\n");
    out.push_str("            Some(idx) => idx,\n");
    out.push_str("            None => {\n");
    out.push_str(&format!(
        "                eprintln!(\"{}: own endpoint not found in args\");\n",
        params.protocol_name
    ));
    out.push_str("                return None;\n");
    out.push_str("            },\n");
    out.push_str("        };\n\n");
    out.push_str("        // TODO: Build protocol-specific constants from peers\n");
    out.push_str("        let constants = CConstants::default(); // FIXME: initialize properly\n\n");
    out.push_str(&format!(
        "        Some({}Config {{\n",
        params.protocol_name
    ));
    out.push_str("            peers,\n");
    out.push_str("            my_index,\n");
    out.push_str("            constants,\n");
    out.push_str("        })\n");
    out.push_str("    }\n\n");
    out.push_str("    fn get_peers(&self) -> &Vec<EndPoint> {\n");
    out.push_str("        &self.peers\n");
    out.push_str("    }\n");
    out.push_str("}\n\n");
}

fn emit_host_struct(out: &mut String, params: &HostScaffoldParams) {
    out.push_str(&format!(
        "/// The {} host wrapping protocol state.\n",
        params.protocol_name
    ));
    out.push_str(&format!("pub struct {}Host {{\n", params.protocol_name));
    out.push_str("    /// The verified protocol state.\n");
    out.push_str("    pub state: CState,\n");
    out.push_str("    /// Round-robin action index for timer-driven actions.\n");
    out.push_str("    pub action_index: u64,\n");
    out.push_str("}\n\n");
}

fn emit_handler_methods(out: &mut String, params: &HostScaffoldParams) {
    let config_type = format!("{}Config", params.protocol_name);
    let msg_type = &params.message_enum;

    out.push_str(&format!("impl {}Host {{\n", params.protocol_name));

    // Helper: resolve_sender_index
    out.push_str("    /// Resolve the sender's node index from their endpoint.\n");
    out.push_str(&format!(
        "    fn resolve_sender_index(config: &{}, src: &EndPoint) -> Option<u64> {{\n",
        config_type
    ));
    out.push_str("        for i in 0..config.peers.len() {\n");
    out.push_str("            if config.peers[i].id == src.id {\n");
    out.push_str("                return Some(i as u64);\n");
    out.push_str("            }\n");
    out.push_str("        }\n");
    out.push_str("        None\n");
    out.push_str("    }\n\n");

    // Helper: other_peers
    out.push_str("    /// Collect all peer endpoints except self for broadcasting.\n");
    out.push_str(&format!(
        "    fn other_peers(config: &{}) -> Vec<EndPoint> {{\n",
        config_type
    ));
    out.push_str("        let mut others = Vec::new();\n");
    out.push_str("        for i in 0..config.peers.len() {\n");
    out.push_str("            if i as u64 != config.my_index {\n");
    out.push_str("                others.push(config.peers[i].clone_up_to_view());\n");
    out.push_str("            }\n");
    out.push_str("        }\n");
    out.push_str("        others\n");
    out.push_str("    }\n");

    // Message-driven handler stubs
    let msg_actions: Vec<&SchedulerActionConfig> = params
        .actions
        .iter()
        .filter(|a| a.is_message_driven())
        .collect();

    if !msg_actions.is_empty() {
        out.push_str("\n    // ---------------------------------------------------------------\n");
        out.push_str("    // Message-driven actions (called when a packet arrives)\n");
        out.push_str("    // ---------------------------------------------------------------\n");
    }

    for action in &msg_actions {
        let handler_name = to_snake_case(&action.exec_name);
        let variant_name = action
            .message_variant
            .as_deref()
            .unwrap_or("Unknown");

        // Find the message variant to get its fields
        let variant_fields = params
            .message_variants
            .iter()
            .find(|v| v.name == variant_name);

        out.push_str(&format!(
            "\n    /// Handle incoming {} message → {}.\n",
            variant_name, action.exec_name
        ));
        out.push_str(&format!(
            "    fn handle_{}(\n        &mut self,\n        config: &{},\n        _src: &EndPoint,\n        _sender_id: u64,\n",
            handler_name, config_type
        ));

        // Add message fields as parameters
        if let Some(variant) = variant_fields {
            for field in &variant.fields {
                if field.len() >= 2 {
                    out.push_str(&format!(
                        "        _{}: {},\n",
                        field[0], field[1]
                    ));
                }
            }
        }

        out.push_str(&format!("    ) -> StepResult<{}> {{\n", msg_type));
        out.push_str("        // TODO: Add guard checks (spec preconditions)\n");
        out.push_str(&format!(
            "        // TODO: Call {}::{}(&self.state, &config.constants, ...)\n",
            params.gen_module, action.exec_name
        ));
        out.push_str("        // TODO: Construct outbound message\n");
        out.push_str("        StepResult { ok: true, outbound: GenericOutbound::None }\n");
        out.push_str("    }\n");
    }

    // Timer-driven handler stubs
    let timer_actions: Vec<&SchedulerActionConfig> = params
        .actions
        .iter()
        .filter(|a| !a.is_message_driven())
        .collect();

    if !timer_actions.is_empty() {
        out.push_str("\n    // ---------------------------------------------------------------\n");
        out.push_str("    // Timer-driven actions (called on timeout, round-robin)\n");
        out.push_str("    // ---------------------------------------------------------------\n");
    }

    for action in &timer_actions {
        let handler_name = to_snake_case(&action.exec_name);

        out.push_str(&format!(
            "\n    /// Timer action: {} (round-robin scheduled).\n",
            action.exec_name
        ));
        out.push_str(&format!(
            "    fn try_{}(\n        &mut self,\n        config: &{},\n    ) -> StepResult<{}> {{\n",
            handler_name, config_type, msg_type
        ));
        out.push_str("        // TODO: Add guard checks (spec preconditions)\n");
        out.push_str(&format!(
            "        // TODO: Call {}::{}(&self.state, &config.constants, ...)\n",
            params.gen_module, action.exec_name
        ));
        out.push_str("        // TODO: Construct outbound message if needed\n");
        out.push_str("        StepResult { ok: true, outbound: GenericOutbound::None }\n");
        out.push_str("    }\n");
    }

    out.push_str("}\n\n");
}

fn emit_protocol_host_impl(out: &mut String, params: &HostScaffoldParams) {
    let config_type = format!("{}Config", params.protocol_name);
    let host_type = format!("{}Host", params.protocol_name);
    let msg_type = &params.message_enum;

    out.push_str(&format!("impl ProtocolHost for {} {{\n", host_type));
    out.push_str(&format!("    type Msg = {};\n", msg_type));
    out.push_str(&format!("    type Cfg = {};\n\n", config_type));

    // init()
    out.push_str("    fn init(config: &Self::Cfg) -> Option<Self> {\n");
    out.push_str(&format!(
        "        let state = {}::CInit(&config.constants);\n",
        params.gen_module
    ));
    out.push_str(&format!("        Some({} {{\n", host_type));
    out.push_str("            state,\n");
    out.push_str("            action_index: 0,\n");
    out.push_str("        })\n");
    out.push_str("    }\n\n");

    // next()
    out.push_str("    fn next(\n");
    out.push_str("        &mut self,\n");
    out.push_str("        config: &Self::Cfg,\n");
    out.push_str("        packet: Option<GenericPacket<Self::Msg>>,\n");
    out.push_str("    ) -> StepResult<Self::Msg> {\n");

    // Message dispatch
    out.push_str("        // Handle incoming message\n");
    out.push_str("        if let Some(pkt) = packet {\n");
    out.push_str("            let sender_id = Self::resolve_sender_index(config, &pkt.src);\n");
    out.push_str("            let sender_id = match sender_id {\n");
    out.push_str("                Some(id) => id,\n");
    out.push_str("                None => {\n");
    out.push_str("                    return StepResult { ok: true, outbound: GenericOutbound::None };\n");
    out.push_str("                },\n");
    out.push_str("            };\n\n");
    out.push_str("            return match pkt.msg {\n");

    // Match arms for each message variant
    for variant in &params.message_variants {
        let field_names: Vec<&str> = variant
            .fields
            .iter()
            .filter_map(|f| f.first().map(|s| s.as_str()))
            .collect();

        let fields_pattern = if field_names.is_empty() {
            String::new()
        } else {
            format!(" {{ {} }}", field_names.join(", "))
        };

        // Find the message-driven action that maps to this variant
        let handler = params.actions.iter().find(|a| {
            a.is_message_driven()
                && a.message_variant.as_deref() == Some(&variant.name)
        });

        if let Some(action) = handler {
            let handler_name = to_snake_case(&action.exec_name);
            let field_args = if field_names.is_empty() {
                String::new()
            } else {
                format!(", {}", field_names.join(", "))
            };
            out.push_str(&format!(
                "                {}::{}{} => {{\n",
                msg_type, variant.name, fields_pattern
            ));
            out.push_str(&format!(
                "                    self.handle_{}(config, &pkt.src, sender_id{})\n",
                handler_name, field_args
            ));
            out.push_str("                },\n");
        } else {
            // No handler for this variant — no-op
            out.push_str(&format!(
                "                {}::{}{} => {{\n",
                msg_type, variant.name, fields_pattern
            ));
            out.push_str("                    // TODO: No handler mapped for this variant\n");
            out.push_str("                    StepResult { ok: true, outbound: GenericOutbound::None }\n");
            out.push_str("                },\n");
        }
    }

    out.push_str("            };\n");
    out.push_str("        }\n\n");

    // Timer dispatch (round-robin)
    let timer_actions: Vec<&SchedulerActionConfig> = params
        .actions
        .iter()
        .filter(|a| !a.is_message_driven())
        .collect();

    let timer_count = timer_actions.len();

    out.push_str("        // No message -- run timer-driven actions round-robin\n");
    if timer_count > 0 {
        out.push_str(&format!(
            "        let result = match self.action_index % {} {{\n",
            timer_count
        ));
        for (i, action) in timer_actions.iter().enumerate() {
            let handler_name = to_snake_case(&action.exec_name);
            if i == timer_count - 1 {
                out.push_str(&format!(
                    "            _ => self.try_{}(config),\n",
                    handler_name
                ));
            } else {
                out.push_str(&format!(
                    "            {} => self.try_{}(config),\n",
                    i, handler_name
                ));
            }
        }
        out.push_str("        };\n");
        out.push_str("        self.action_index = self.action_index.wrapping_add(1);\n");
        out.push_str("        result\n");
    } else {
        out.push_str("        StepResult { ok: true, outbound: GenericOutbound::None }\n");
    }

    out.push_str("    }\n");
    out.push_str("}\n");
}

/// Convert a CamelCase exec name to snake_case for method names.
/// E.g., "CSend1a" → "c_send1a", "CRecvPromise" → "c_recv_promise"
fn to_snake_case(name: &str) -> String {
    let mut result = String::new();
    let mut prev_was_upper = false;
    let mut prev_was_digit = false;

    for (i, ch) in name.chars().enumerate() {
        if ch.is_uppercase() {
            if i > 0 && !prev_was_upper {
                result.push('_');
            }
            result.push(ch.to_lowercase().next().unwrap());
            prev_was_upper = true;
            prev_was_digit = false;
        } else if ch.is_ascii_digit() {
            if i > 0 && !prev_was_digit && !prev_was_upper {
                // Don't add underscore before digit if preceding was uppercase
            }
            result.push(ch);
            prev_was_upper = false;
            prev_was_digit = true;
        } else {
            prev_was_upper = false;
            prev_was_digit = false;
            result.push(ch);
        }
    }

    result
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

    // ---------------------------------------------------------------
    // Phase 17.4.3: to_snake_case tests
    // ---------------------------------------------------------------

    #[test]
    fn test_to_snake_case_basic() {
        // Consecutive uppercase letters (CS, CR) are treated as one run
        assert_eq!(to_snake_case("CSend1a"), "csend1a");
        assert_eq!(to_snake_case("CRecvPromise"), "crecv_promise");
        assert_eq!(to_snake_case("CSend2a"), "csend2a");
        assert_eq!(to_snake_case("CSend2b"), "csend2b");
    }

    #[test]
    fn test_to_snake_case_multi_word() {
        assert_eq!(to_snake_case("CRecvAccepted"), "crecv_accepted");
        assert_eq!(to_snake_case("CLearn"), "clearn");
        assert_eq!(to_snake_case("CInit"), "cinit");
    }

    #[test]
    fn test_to_snake_case_all_lower() {
        assert_eq!(to_snake_case("hello"), "hello");
        assert_eq!(to_snake_case("world"), "world");
    }

    #[test]
    fn test_to_snake_case_consecutive_upper() {
        // Consecutive uppercase letters don't add extra underscores
        assert_eq!(to_snake_case("CRMPrepare"), "crmprepare");
        assert_eq!(to_snake_case("CTMSendPrepare"), "ctmsend_prepare");
    }

    #[test]
    fn test_to_snake_case_complex_names() {
        assert_eq!(
            to_snake_case("CFollowerAppendEntries"),
            "cfollower_append_entries"
        );
        assert_eq!(
            to_snake_case("CGrantVoteForCandidate"),
            "cgrant_vote_for_candidate"
        );
    }

    // ---------------------------------------------------------------
    // Phase 17.4.3: generate_host_scaffold tests
    // ---------------------------------------------------------------

    fn make_paxos_params() -> HostScaffoldParams {
        HostScaffoldParams {
            protocol_name: "Paxos".to_string(),
            module_name: "paxos".to_string(),
            gen_module: "paxos_gen".to_string(),
            message_enum: "PaxosMessage".to_string(),
            message_variants: vec![
                MessageVariant {
                    name: "Prepare".to_string(),
                    doc: "Phase 1a".to_string(),
                    fields: vec![vec!["ballot".to_string(), "u64".to_string()]],
                },
                MessageVariant {
                    name: "Promise".to_string(),
                    doc: "Phase 1b".to_string(),
                    fields: vec![
                        vec!["ballot".to_string(), "u64".to_string()],
                        vec!["accepted_bal".to_string(), "u64".to_string()],
                        vec!["accepted_val".to_string(), "u64".to_string()],
                    ],
                },
                MessageVariant {
                    name: "Accept".to_string(),
                    doc: "Phase 2a".to_string(),
                    fields: vec![
                        vec!["ballot".to_string(), "u64".to_string()],
                        vec!["value".to_string(), "u64".to_string()],
                    ],
                },
                MessageVariant {
                    name: "Accepted".to_string(),
                    doc: "Phase 2b".to_string(),
                    fields: vec![
                        vec!["ballot".to_string(), "u64".to_string()],
                        vec!["value".to_string(), "u64".to_string()],
                    ],
                },
            ],
            actions: vec![
                SchedulerActionConfig {
                    spec_name: "LSend1a".to_string(),
                    exec_name: "CSend1a".to_string(),
                    kind: "timer_driven".to_string(),
                    message_variant: None,
                    existential_params: vec![vec!["b".to_string(), "int".to_string()]],
                },
                SchedulerActionConfig {
                    spec_name: "LSend1b".to_string(),
                    exec_name: "CSend1b".to_string(),
                    kind: "message_driven".to_string(),
                    message_variant: None,
                    existential_params: vec![vec!["b".to_string(), "int".to_string()]],
                },
                SchedulerActionConfig {
                    spec_name: "LRecvPromise".to_string(),
                    exec_name: "CRecvPromise".to_string(),
                    kind: "message_driven".to_string(),
                    message_variant: Some("Promise".to_string()),
                    existential_params: vec![
                        vec!["a".to_string(), "int".to_string()],
                        vec!["ab".to_string(), "int".to_string()],
                        vec!["av".to_string(), "int".to_string()],
                    ],
                },
                SchedulerActionConfig {
                    spec_name: "LSend2a".to_string(),
                    exec_name: "CSend2a".to_string(),
                    kind: "timer_driven".to_string(),
                    message_variant: None,
                    existential_params: vec![vec!["v".to_string(), "int".to_string()]],
                },
                SchedulerActionConfig {
                    spec_name: "LSend2b".to_string(),
                    exec_name: "CSend2b".to_string(),
                    kind: "message_driven".to_string(),
                    message_variant: None,
                    existential_params: vec![
                        vec!["b".to_string(), "int".to_string()],
                        vec!["v".to_string(), "int".to_string()],
                    ],
                },
                SchedulerActionConfig {
                    spec_name: "LRecvAccepted".to_string(),
                    exec_name: "CRecvAccepted".to_string(),
                    kind: "message_driven".to_string(),
                    message_variant: Some("Accepted".to_string()),
                    existential_params: vec![vec!["a".to_string(), "int".to_string()]],
                },
                SchedulerActionConfig {
                    spec_name: "LLearn".to_string(),
                    exec_name: "CLearn".to_string(),
                    kind: "timer_driven".to_string(),
                    message_variant: None,
                    existential_params: vec![],
                },
            ],
        }
    }

    #[test]
    fn test_scaffold_contains_header() {
        let params = make_paxos_params();
        let code = generate_host_scaffold(&params);
        assert!(code.contains("//! Paxos protocol host implementation."));
        assert!(code.contains("Auto-generated scaffold"));
    }

    #[test]
    fn test_scaffold_contains_imports() {
        let params = make_paxos_params();
        let code = generate_host_scaffold(&params);
        assert!(code.contains("use crate::common::framework::protocol_trait::*;"));
        assert!(code.contains("use crate::generated::Paxos::paxos_gen;"));
        assert!(code.contains("use crate::generated::Paxos::types_gen::*;"));
        assert!(code.contains("use crate::implementation::Paxos::message::*;"));
    }

    #[test]
    fn test_scaffold_contains_config_struct() {
        let params = make_paxos_params();
        let code = generate_host_scaffold(&params);
        assert!(code.contains("pub struct PaxosConfig {"));
        assert!(code.contains("pub peers: Vec<EndPoint>"));
        assert!(code.contains("pub my_index: u64"));
        assert!(code.contains("pub constants: CConstants"));
        assert!(code.contains("impl ProtocolConfig for PaxosConfig {"));
        assert!(code.contains("fn parse_config(me: &EndPoint, args: &Args) -> Option<Self>"));
        assert!(code.contains("fn get_peers(&self) -> &Vec<EndPoint>"));
    }

    #[test]
    fn test_scaffold_contains_host_struct() {
        let params = make_paxos_params();
        let code = generate_host_scaffold(&params);
        assert!(code.contains("pub struct PaxosHost {"));
        assert!(code.contains("pub state: CState"));
        assert!(code.contains("pub action_index: u64"));
    }

    #[test]
    fn test_scaffold_message_driven_handlers() {
        let params = make_paxos_params();
        let code = generate_host_scaffold(&params);
        // Message-driven handlers should be generated (CSend1b → csend1b, etc.)
        assert!(code.contains("fn handle_csend1b("));
        assert!(code.contains("fn handle_crecv_promise("));
        assert!(code.contains("fn handle_csend2b("));
        assert!(code.contains("fn handle_crecv_accepted("));
        // They should reference the message variant
        assert!(code.contains("Handle incoming Promise message"));
        assert!(code.contains("Handle incoming Accepted message"));
    }

    #[test]
    fn test_scaffold_timer_driven_handlers() {
        let params = make_paxos_params();
        let code = generate_host_scaffold(&params);
        // Timer-driven handlers use try_ prefix (CSend1a → csend1a, etc.)
        assert!(code.contains("fn try_csend1a("));
        assert!(code.contains("fn try_csend2a("));
        assert!(code.contains("fn try_clearn("));
        // Timer section marker
        assert!(code.contains("Timer-driven actions (called on timeout, round-robin)"));
    }

    #[test]
    fn test_scaffold_protocol_host_impl() {
        let params = make_paxos_params();
        let code = generate_host_scaffold(&params);
        assert!(code.contains("impl ProtocolHost for PaxosHost {"));
        assert!(code.contains("type Msg = PaxosMessage;"));
        assert!(code.contains("type Cfg = PaxosConfig;"));
        assert!(code.contains("fn init(config: &Self::Cfg) -> Option<Self>"));
        assert!(code.contains("fn next("));
    }

    #[test]
    fn test_scaffold_init_fn() {
        let params = make_paxos_params();
        let code = generate_host_scaffold(&params);
        assert!(code.contains("paxos_gen::CInit(&config.constants)"));
        assert!(code.contains("Some(PaxosHost {"));
        assert!(code.contains("action_index: 0"));
    }

    #[test]
    fn test_scaffold_message_dispatch() {
        let params = make_paxos_params();
        let code = generate_host_scaffold(&params);
        // Match arms for message variants with mapped handlers
        assert!(code.contains("PaxosMessage::Promise { ballot, accepted_bal, accepted_val }"));
        assert!(code.contains("self.handle_crecv_promise(config, &pkt.src, sender_id, ballot, accepted_bal, accepted_val)"));
        assert!(code.contains("PaxosMessage::Accepted { ballot, value }"));
        assert!(code.contains("self.handle_crecv_accepted(config, &pkt.src, sender_id, ballot, value)"));
    }

    #[test]
    fn test_scaffold_timer_dispatch() {
        let params = make_paxos_params();
        let code = generate_host_scaffold(&params);
        // Timer round-robin with 3 timer actions (CSend1a, CSend2a, CLearn)
        assert!(code.contains("self.action_index % 3"));
        assert!(code.contains("0 => self.try_csend1a(config)"));
        assert!(code.contains("1 => self.try_csend2a(config)"));
        assert!(code.contains("_ => self.try_clearn(config)"));
        assert!(code.contains("self.action_index = self.action_index.wrapping_add(1)"));
    }

    #[test]
    fn test_scaffold_unmapped_variant_noop() {
        // Prepare and Accept message variants have no mapped handler actions
        // (Send1b is message_driven but has no message_variant set,
        //  and Send2b is similar — they don't map to Prepare/Accept by variant)
        let params = make_paxos_params();
        let code = generate_host_scaffold(&params);
        // Prepare variant should have a no-op arm
        assert!(code.contains("PaxosMessage::Prepare { ballot }"));
        // Accept variant should have a no-op arm
        assert!(code.contains("PaxosMessage::Accept { ballot, value }"));
    }

    #[test]
    fn test_scaffold_resolve_sender() {
        let params = make_paxos_params();
        let code = generate_host_scaffold(&params);
        assert!(code.contains("fn resolve_sender_index(config: &PaxosConfig, src: &EndPoint)"));
        assert!(code.contains("fn other_peers(config: &PaxosConfig)"));
    }

    #[test]
    fn test_scaffold_empty_actions() {
        let params = HostScaffoldParams {
            protocol_name: "Empty".to_string(),
            module_name: "empty".to_string(),
            gen_module: "empty_gen".to_string(),
            message_enum: "EmptyMessage".to_string(),
            message_variants: vec![],
            actions: vec![],
        };
        let code = generate_host_scaffold(&params);
        // Should still generate valid structure
        assert!(code.contains("pub struct EmptyConfig {"));
        assert!(code.contains("pub struct EmptyHost {"));
        assert!(code.contains("impl ProtocolHost for EmptyHost {"));
        // No timer actions — should emit GenericOutbound::None
        assert!(code.contains("StepResult { ok: true, outbound: GenericOutbound::None }"));
    }

    #[test]
    fn test_scaffold_all_timer_driven() {
        let params = HostScaffoldParams {
            protocol_name: "AllTimer".to_string(),
            module_name: "all_timer".to_string(),
            gen_module: "all_timer_gen".to_string(),
            message_enum: "AllTimerMessage".to_string(),
            message_variants: vec![],
            actions: vec![
                SchedulerActionConfig {
                    spec_name: "LAction1".to_string(),
                    exec_name: "CAction1".to_string(),
                    kind: "timer_driven".to_string(),
                    message_variant: None,
                    existential_params: vec![],
                },
                SchedulerActionConfig {
                    spec_name: "LAction2".to_string(),
                    exec_name: "CAction2".to_string(),
                    kind: "timer_driven".to_string(),
                    message_variant: None,
                    existential_params: vec![],
                },
            ],
        };
        let code = generate_host_scaffold(&params);
        // Both timer actions (CAction1 → caction1, etc.)
        assert!(code.contains("fn try_caction1("));
        assert!(code.contains("fn try_caction2("));
        assert!(code.contains("self.action_index % 2"));
        // No message-driven section
        assert!(!code.contains("Message-driven actions"));
    }

    #[test]
    fn test_scaffold_all_message_driven() {
        let params = HostScaffoldParams {
            protocol_name: "AllMsg".to_string(),
            module_name: "all_msg".to_string(),
            gen_module: "all_msg_gen".to_string(),
            message_enum: "AllMsgMessage".to_string(),
            message_variants: vec![MessageVariant {
                name: "Ping".to_string(),
                doc: String::new(),
                fields: vec![vec!["id".to_string(), "u64".to_string()]],
            }],
            actions: vec![SchedulerActionConfig {
                spec_name: "LHandlePing".to_string(),
                exec_name: "CHandlePing".to_string(),
                kind: "message_driven".to_string(),
                message_variant: Some("Ping".to_string()),
                existential_params: vec![],
            }],
        };
        let code = generate_host_scaffold(&params);
        assert!(code.contains("fn handle_chandle_ping("));
        assert!(code.contains("AllMsgMessage::Ping { id }"));
        assert!(code.contains("self.handle_chandle_ping(config, &pkt.src, sender_id, id)"));
        // No timer section
        assert!(!code.contains("Timer-driven actions"));
        // Timer dispatch still generates the no-op fallback
        assert!(code.contains("StepResult { ok: true, outbound: GenericOutbound::None }"));
    }
}
