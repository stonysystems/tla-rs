//! Scheduler generation from LNext disjunction structure.
//!
//! Analyzes the LNext spec function body to extract the list of protocol
//! actions, their existential parameters, and generates a scheduler config
//! that can be used to produce the runtime host/scheduler code.
//!
//! Phase 17.4.2 adds action classification (message_driven vs timer_driven)
//! using name-based heuristics and optional message variant mapping.

use crate::ast::{Binding, Expr, Path, SpecFunction, Type};
#[cfg(test)]
use crate::config::RoleConfig;
use crate::config::{MessageVariant, RoleDispatchConfig, SchedulerActionConfig};

/// Protocol-specific overrides for action classification.
/// These override or supplement the default keyword-based heuristics.
#[derive(Debug, Clone, Default)]
pub struct ActionClassificationOverrides {
    /// Action name patterns classified as message-driven responses.
    /// Supplements the default keyword heuristics (receive/rcv/handle).
    pub message_response_overrides: Vec<String>,
    /// Role prefixes to strip from action names for variant matching.
    /// Supplements (and takes priority over) the default role prefix list.
    pub role_prefixes: Vec<String>,
    /// Action name patterns forced to timer-driven even when they contain
    /// message keywords. Checked before keyword matching.
    pub timer_overrides: Vec<String>,
}

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

    let params: Vec<String> = spec_fn.params.iter().map(|p| p.name.clone()).collect();

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
    let suffix = spec_name.strip_prefix(spec_prefix).unwrap_or(spec_name);
    format!("{}{}", exec_prefix, suffix)
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
            let ty =
                b.ty.as_ref()
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
        Type::Seq(inner) => format!("Seq<{}>", type_to_string(inner)),
        Type::Set(inner) => format!("Set<{}>", type_to_string(inner)),
        Type::Map(k, v) => format!("Map<{}, {}>", type_to_string(k), type_to_string(v)),
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
pub fn classify_actions(
    config: &mut SchedulerConfig,
    message_variants: &[String],
    overrides: &ActionClassificationOverrides,
) {
    for action in &mut config.actions {
        let (kind, variant) =
            classify_single_action(&action.spec_name, message_variants, overrides);
        action.kind = kind;
        action.message_variant = variant;
    }
}

/// Classify a single action by its spec name.
/// Returns (ActionKind, Option<message_variant_name>).
fn classify_single_action(
    spec_name: &str,
    message_variants: &[String],
    overrides: &ActionClassificationOverrides,
) -> (ActionKind, Option<String>) {
    // Normalize: strip common spec prefix "L" for pattern matching
    let name = spec_name.strip_prefix('L').unwrap_or(spec_name);
    let name_lower = name.to_lowercase();

    // Timer-driven override: checked FIRST because some action names contain
    // message keywords (like "Handle") but are actually timer/state-driven.
    // Uses TOML overrides only — no hardcoded defaults.
    if overrides
        .timer_overrides
        .iter()
        .any(|p| name.contains(p.as_str()))
    {
        return (ActionKind::TimerDriven, None);
    }

    // Strong message-driven indicators (generic keywords, not protocol-specific)
    let message_keywords = ["receive", "rcv", "recv", "handle"];
    if message_keywords.iter().any(|kw| name_lower.contains(kw)) {
        let variant = find_matching_variant(name, message_variants, &overrides.role_prefixes);
        return (ActionKind::MessageDriven, variant);
    }

    // Protocol-specific message-driven response patterns from TOML config.
    // These are actions triggered by incoming messages even though their names
    // don't contain standard message keywords (receive/rcv/handle).
    if overrides
        .message_response_overrides
        .iter()
        .any(|p| name.contains(p.as_str()))
    {
        let variant = find_matching_variant(name, message_variants, &overrides.role_prefixes);
        return (ActionKind::MessageDriven, variant);
    }

    // Strong timer-driven indicators (generic keywords, not protocol-specific)
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
fn find_matching_variant(
    action_suffix: &str,
    message_variants: &[String],
    role_prefixes: &[String],
) -> Option<String> {
    // Strategy 1 (most precise): Extract keyword, find best variant match.
    // E.g., "TMRcvPrepared" → keyword "Prepared" → variant "PreparedVote"
    let keyword = extract_action_keyword(action_suffix, role_prefixes);
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
            if variant_lower.starts_with(&keyword_lower)
                && best.is_none_or(|b| variant.len() < b.len())
            {
                best = Some(variant);
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
            if (keyword_lower.contains(&variant_lower) || variant_lower.contains(&keyword_lower))
                && best_match.is_none_or(|(best_len, _)| variant.len() > best_len)
            {
                best_match = Some((variant.len(), variant));
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
        if action_lower.contains(&variant_lower)
            && best_match.is_none_or(|(best_len, _)| variant.len() > best_len)
        {
            best_match = Some((variant.len(), variant));
        }
    }
    if let Some((_, variant)) = best_match {
        return Some(variant.clone());
    }

    None
}

/// Extract the "keyword" part of an action name by stripping:
/// - Role prefixes (from TOML config + defaults)
/// - Action verbs (Receive, Rcv, Recv, Handle, Send)
///
/// E.g., "TMRcvPrepared" → "Prepared", "RMReceiveCommit" → "Commit"
fn extract_action_keyword<'a>(name: &'a str, role_prefixes: &[String]) -> &'a str {
    let stripped = strip_role_prefix(name, role_prefixes);
    // Strip action verb prefixes
    let verb_prefixes = ["Receive", "Rcv", "Recv", "Handle", "Send"];
    for prefix in &verb_prefixes {
        if let Some(rest) = stripped.strip_prefix(prefix) {
            return rest;
        }
    }
    stripped
}

/// Default role prefixes used when no TOML overrides are provided.
const DEFAULT_ROLE_PREFIXES: &[&str] = &[
    "TM",
    "RM",
    "Primary",
    "Backup",
    "Head",
    "Tail",
    "Middle",
    "Follower",
    "Leader",
    "Candidate",
];

/// Strip role prefixes from action names for variant matching.
/// If TOML `role_prefixes` is non-empty, uses those exclusively;
/// otherwise falls back to the built-in default list.
fn strip_role_prefix<'a>(name: &'a str, role_prefixes: &[String]) -> &'a str {
    if !role_prefixes.is_empty() {
        for prefix in role_prefixes {
            if let Some(rest) = name.strip_prefix(prefix.as_str()) {
                return rest;
            }
        }
    } else {
        for prefix in DEFAULT_ROLE_PREFIXES {
            if let Some(rest) = name.strip_prefix(prefix) {
                return rest;
            }
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
    out.push_str(&format!("next_fn = \"{}\"\n", config.next_fn_name));
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
            out.push_str(&format!("existential_params = [{}]\n", params.join(", ")));
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
    /// Optional role-based dispatch configuration
    pub role_dispatch: Option<RoleDispatchConfig>,
}

/// Validate scaffold params for common configuration errors.
///
/// Returns a list of warning strings. An empty list means no issues.
/// Checks:
/// - Every message_driven action has a message_variant
/// - Every message_variant references an existing message variant name
/// - No two message_driven actions map to the same variant (shared variant conflict)
pub fn validate_scaffold_params(params: &HostScaffoldParams) -> Vec<String> {
    let mut warnings = Vec::new();
    let variant_names: Vec<&str> = params
        .message_variants
        .iter()
        .map(|v| v.name.as_str())
        .collect();

    // Track variant → action mapping for conflict detection
    let mut variant_to_actions: std::collections::HashMap<&str, Vec<&str>> =
        std::collections::HashMap::new();

    for action in &params.actions {
        if action.is_message_driven() {
            match &action.message_variant {
                None => {
                    warnings.push(format!(
                        "message_driven action '{}' has no message_variant",
                        action.spec_name
                    ));
                }
                Some(variant) => {
                    if !variant_names.contains(&variant.as_str()) {
                        warnings.push(format!(
                            "action '{}' references non-existent message_variant '{}'",
                            action.spec_name, variant
                        ));
                    }
                    variant_to_actions
                        .entry(variant.as_str())
                        .or_default()
                        .push(&action.spec_name);
                }
            }
        }
    }

    // Report shared variant conflicts
    for (variant, actions) in &variant_to_actions {
        if actions.len() > 1 {
            warnings.push(format!(
                "multiple actions map to variant '{}': {} (only first will be dispatched)",
                variant,
                actions.join(", ")
            ));
        }
    }

    warnings
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

    if params.role_dispatch.is_some() {
        // Per-role step methods + role-dispatching ProtocolHost impl
        emit_role_step_methods(&mut out, params);
        emit_role_dispatch_host_impl(&mut out, params);
    } else {
        // Flat ProtocolHost trait impl (init + next)
        emit_protocol_host_impl(&mut out, params);
    }

    out
}

fn emit_header(out: &mut String, params: &HostScaffoldParams) {
    out.push_str(&format!(
        "//! {} protocol host implementation.\n",
        params.protocol_name
    ));
    out.push_str("//!\n");
    out.push_str("//! Auto-generated scaffold by the transpiler.\n");
    out.push_str(
        "//! TODO: Add protocol-specific guard logic and outbound message construction.\n",
    );
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
    out.push_str(
        "        let constants = CConstants::default(); // FIXME: initialize properly\n\n",
    );
    out.push_str(&format!("        Some({}Config {{\n", params.protocol_name));
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
        let variant_name = action.message_variant.as_deref().unwrap_or("Unknown");

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
                    // If this field is referenced in flag_injections, emit without _ prefix
                    let is_used = action
                        .flag_injections
                        .iter()
                        .any(|inj| inj.len() >= 2 && inj[1] == field[0]);
                    let prefix = if is_used { "" } else { "_" };
                    out.push_str(&format!("        {}{}: {},\n", prefix, field[0], field[1]));
                }
            }
        }

        out.push_str(&format!("    ) -> StepResult<{}> {{\n", msg_type));

        // Emit flag injections before the TODO stubs
        if action.has_flag_injections() {
            out.push_str("        // Flag injection: simulate receiving the message\n");
            for inj in &action.flag_injections {
                if inj.len() >= 2 {
                    out.push_str(&format!("        self.state.{} = {};\n", inj[0], inj[1]));
                }
            }
            out.push('\n');
        }

        emit_guard_checks(out, action);
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
        emit_guard_checks(out, action);
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

/// Emit per-role step methods when role_dispatch is configured.
///
/// Each role gets a `{role}_step()` method that handles message dispatch
/// (filtered to that role's message-driven actions) and timer round-robin
/// (filtered to that role's timer-driven actions).
fn emit_role_step_methods(out: &mut String, params: &HostScaffoldParams) {
    let rd = match &params.role_dispatch {
        Some(rd) => rd,
        None => return,
    };

    let config_type = format!("{}Config", params.protocol_name);
    let host_type = format!("{}Host", params.protocol_name);
    let msg_type = &params.message_enum;

    out.push_str(&format!("impl {} {{\n", host_type));

    for role in &rd.roles {
        // Collect this role's actions from the full action list
        let role_actions: Vec<&SchedulerActionConfig> = params
            .actions
            .iter()
            .filter(|a| role.actions.contains(&a.exec_name))
            .collect();

        let role_msg_actions: Vec<&&SchedulerActionConfig> = role_actions
            .iter()
            .filter(|a| a.is_message_driven())
            .collect();

        let role_timer_actions: Vec<&&SchedulerActionConfig> = role_actions
            .iter()
            .filter(|a| !a.is_message_driven())
            .collect();

        out.push_str(&format!(
            "    /// Step function for the {} role.\n",
            role.name
        ));
        out.push_str(&format!(
            "    fn {}_step(\n        &mut self,\n        config: &{},\n        packet: Option<GenericPacket<{}>>,\n    ) -> StepResult<{}> {{\n",
            role.name, config_type, msg_type, msg_type
        ));

        // Message dispatch for this role
        if !role_msg_actions.is_empty() || !params.message_variants.is_empty() {
            out.push_str("        if let Some(pkt) = packet {\n");
            out.push_str(
                "            let sender_id = Self::resolve_sender_index(config, &pkt.src);\n",
            );
            out.push_str("            let sender_id = match sender_id {\n");
            out.push_str("                Some(id) => id,\n");
            out.push_str("                None => {\n");
            out.push_str("                    return StepResult { ok: true, outbound: GenericOutbound::None };\n");
            out.push_str("                },\n");
            out.push_str("            };\n\n");
            out.push_str("            return match pkt.msg {\n");

            // Reserved names
            let reserved_names = ["config", "self", "pkt", "sender_id", "result"];

            for variant in &params.message_variants {
                let raw_field_names: Vec<&str> = variant
                    .fields
                    .iter()
                    .filter_map(|f| f.first().map(|s| s.as_str()))
                    .collect();

                let field_names: Vec<String> = raw_field_names
                    .iter()
                    .map(|name| {
                        if reserved_names.contains(name) {
                            format!("msg_{}", name)
                        } else {
                            name.to_string()
                        }
                    })
                    .collect();

                let fields_pattern = if field_names.is_empty() {
                    String::new()
                } else if raw_field_names.iter().any(|n| reserved_names.contains(n)) {
                    let bindings: Vec<String> = raw_field_names
                        .iter()
                        .zip(field_names.iter())
                        .map(|(raw, renamed)| {
                            if *raw != renamed.as_str() {
                                format!("{}: {}", raw, renamed)
                            } else {
                                renamed.clone()
                            }
                        })
                        .collect();
                    format!(" {{ {} }}", bindings.join(", "))
                } else {
                    format!(" {{ {} }}", field_names.join(", "))
                };

                // Find handler for this variant that belongs to this role
                let handler = params.actions.iter().find(|a| {
                    a.is_message_driven()
                        && a.message_variant.as_deref() == Some(&variant.name)
                        && role.actions.contains(&a.exec_name)
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
                    // Not handled by this role — no-op
                    out.push_str(&format!(
                        "                {}::{}{} => {{\n",
                        msg_type, variant.name, fields_pattern
                    ));
                    out.push_str("                    StepResult { ok: true, outbound: GenericOutbound::None }\n");
                    out.push_str("                },\n");
                }
            }

            out.push_str("            };\n");
            out.push_str("        }\n\n");
        }

        // Timer dispatch for this role
        let timer_count = role_timer_actions.len();
        out.push_str("        // Timer-driven actions for this role\n");
        if timer_count > 0 {
            out.push_str(&format!(
                "        let result = match self.action_index % {} {{\n",
                timer_count
            ));
            for (i, action) in role_timer_actions.iter().enumerate() {
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

        out.push_str("    }\n\n");
    }

    out.push_str("}\n\n");
}

/// Emit the ProtocolHost impl with role-based dispatch in `next()`.
fn emit_role_dispatch_host_impl(out: &mut String, params: &HostScaffoldParams) {
    let rd = match &params.role_dispatch {
        Some(rd) => rd,
        None => return,
    };

    let config_type = format!("{}Config", params.protocol_name);
    let host_type = format!("{}Host", params.protocol_name);
    let msg_type = &params.message_enum;

    out.push_str(&format!("impl ProtocolHost for {} {{\n", host_type));
    out.push_str(&format!("    type Msg = {};\n", msg_type));
    out.push_str(&format!("    type Cfg = {};\n\n", config_type));

    // init() — same as flat dispatch
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

    // next() — role-dispatching
    out.push_str("    fn next(\n");
    out.push_str("        &mut self,\n");
    out.push_str("        config: &Self::Cfg,\n");
    out.push_str("        packet: Option<GenericPacket<Self::Msg>>,\n");
    out.push_str("    ) -> StepResult<Self::Msg> {\n");

    match rd.dispatch_style.as_str() {
        "config_index" => {
            // Cascading if-else
            for (i, role) in rd.roles.iter().enumerate() {
                if i == 0 {
                    out.push_str(&format!("        if {} {{\n", role.condition));
                } else if role.condition.is_empty() || i == rd.roles.len() - 1 {
                    // Last role or empty condition = else
                    out.push_str("        } else {\n");
                } else {
                    out.push_str(&format!("        }} else if {} {{\n", role.condition));
                }
                out.push_str(&format!(
                    "            self.{}_step(config, packet)\n",
                    role.name
                ));
            }
            out.push_str("        }\n");
        }
        _ => {
            // Match on the dispatch field
            out.push_str(&format!("        match {} {{\n", rd.dispatch_field));
            for (i, role) in rd.roles.iter().enumerate() {
                if i == rd.roles.len() - 1 {
                    out.push_str(&format!(
                        "            _ => self.{}_step(config, packet),\n",
                        role.name
                    ));
                } else {
                    out.push_str(&format!(
                        "            {} => self.{}_step(config, packet),\n",
                        role.condition, role.name
                    ));
                }
            }
            out.push_str("        }\n");
        }
    }

    out.push_str("    }\n");
    out.push_str("}\n");
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
    out.push_str(
        "                    return StepResult { ok: true, outbound: GenericOutbound::None };\n",
    );
    out.push_str("                },\n");
    out.push_str("            };\n\n");
    out.push_str("            return match pkt.msg {\n");

    // Match arms for each message variant
    // Reserved names that conflict with scaffold variables
    let reserved_names = ["config", "self", "pkt", "sender_id", "result"];

    for variant in &params.message_variants {
        let raw_field_names: Vec<&str> = variant
            .fields
            .iter()
            .filter_map(|f| f.first().map(|s| s.as_str()))
            .collect();

        // Rename fields that conflict with scaffold variables
        let field_names: Vec<String> = raw_field_names
            .iter()
            .map(|name| {
                if reserved_names.contains(name) {
                    format!("msg_{}", name)
                } else {
                    name.to_string()
                }
            })
            .collect();

        let fields_pattern = if field_names.is_empty() {
            String::new()
        } else if raw_field_names.iter().any(|n| reserved_names.contains(n)) {
            // Use rename syntax: OrigName: msg_origname
            let bindings: Vec<String> = raw_field_names
                .iter()
                .zip(field_names.iter())
                .map(|(raw, renamed)| {
                    if *raw != renamed.as_str() {
                        format!("{}: {}", raw, renamed)
                    } else {
                        renamed.clone()
                    }
                })
                .collect();
            format!(" {{ {} }}", bindings.join(", "))
        } else {
            format!(" {{ {} }}", field_names.join(", "))
        };

        // Find the message-driven action that maps to this variant
        let handler = params
            .actions
            .iter()
            .find(|a| a.is_message_driven() && a.message_variant.as_deref() == Some(&variant.name));

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
            out.push_str(
                "                    StepResult { ok: true, outbound: GenericOutbound::None }\n",
            );
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

/// Emit guard check if-return blocks for an action.
///
/// When `guard_checks` is configured, emits one `if !(...) { return noop }` block
/// per guard condition. When empty, emits the TODO comment as a placeholder.
fn emit_guard_checks(out: &mut String, action: &SchedulerActionConfig) {
    if action.has_guard_checks() {
        for guard in &action.guard_checks {
            out.push_str(&format!("        if !({}) {{\n", guard));
            out.push_str(
                "            return StepResult { ok: true, outbound: GenericOutbound::None };\n",
            );
            out.push_str("        }\n");
        }
    } else {
        out.push_str("        // TODO: Add guard checks (spec preconditions)\n");
    }
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
        // Reader semantics: these tests classify function bodies and are fed
        // real protocol sources, which carry inline `// @automan` directives
        // since the Phase 55 migration. The modes are irrelevant here.
        let parser = VerusParser::new(source.to_string());
        parser
            .parse_spec_functions_annotated()
            .unwrap()
            .into_iter()
            .map(|(func, _)| func)
            .collect()
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
        let names: Vec<&str> = config
            .actions
            .iter()
            .map(|a| a.spec_name.as_str())
            .collect();
        assert!(names.contains(&"LTMSendPrepare"));
        assert!(names.contains(&"LRMReceivePrepare"));
        assert!(names.contains(&"LTMRcvPrepared"));
        assert!(names.contains(&"LTMSendCommit"));
        assert!(names.contains(&"LTMSendAbort"));

        // LTMSendPrepare has exists |sent_packets|
        let send_prepare = config
            .actions
            .iter()
            .find(|a| a.spec_name == "LTMSendPrepare")
            .unwrap();
        assert_eq!(send_prepare.existential_params.len(), 1);
        assert_eq!(send_prepare.existential_params[0].0, "sent_packets");

        // LRMReceivePrepare has exists |rm: int, sent_packets|
        let rcv_prepare = config
            .actions
            .iter()
            .find(|a| a.spec_name == "LRMReceivePrepare")
            .unwrap();
        assert_eq!(rcv_prepare.existential_params.len(), 2);
        assert_eq!(rcv_prepare.existential_params[0].0, "rm");
    }

    #[test]
    fn test_raft_lnext() {
        let source = std::fs::read_to_string("../src/protocol/Raft/raft.rs")
            .expect("Failed to read Raft spec");
        let fns = parse_spec_fns(&source);
        let config = find_and_analyze_lnext(&fns, "LNext", "L", "C").unwrap();
        // Phase 27.4: LNext now uses composite actions (5 branches)
        // - LTimeout, LClientRequest, LSendAppendEntries (timer-driven)
        // - LHandleMessage (composite message dispatch)
        // - LTryAdvanceCommitIndex (composite commit advancement)
        assert_eq!(
            config.actions.len(),
            5,
            "Raft LNext has 5 composite branches"
        );

        let names: Vec<&str> = config
            .actions
            .iter()
            .map(|a| a.spec_name.as_str())
            .collect();
        assert!(names.contains(&"LTimeout"));
        assert!(names.contains(&"LClientRequest"));
        assert!(names.contains(&"LSendAppendEntries"));
        assert!(names.contains(&"LHandleMessage"));
        assert!(names.contains(&"LTryAdvanceCommitIndex"));
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
        let (kind, _) = classify_single_action(
            "LRMReceivePrepare",
            &[],
            &ActionClassificationOverrides::default(),
        );
        assert_eq!(kind, ActionKind::MessageDriven);
    }

    #[test]
    fn test_classify_rcv_keyword() {
        let (kind, _) = classify_single_action(
            "LTMRcvPrepared",
            &[],
            &ActionClassificationOverrides::default(),
        );
        assert_eq!(kind, ActionKind::MessageDriven);
    }

    #[test]
    fn test_classify_handle_keyword() {
        let (kind, _) = classify_single_action(
            "LHandleAppendResponse",
            &[],
            &ActionClassificationOverrides::default(),
        );
        assert_eq!(kind, ActionKind::MessageDriven);
    }

    #[test]
    fn test_classify_timeout() {
        let (kind, _) =
            classify_single_action("LTimeout", &[], &ActionClassificationOverrides::default());
        assert_eq!(kind, ActionKind::TimerDriven);
    }

    #[test]
    fn test_classify_detect_failure() {
        let (kind, _) = classify_single_action(
            "LDetectFailure",
            &[],
            &ActionClassificationOverrides::default(),
        );
        assert_eq!(kind, ActionKind::TimerDriven);
    }

    #[test]
    fn test_classify_paxos_send1b_message_response() {
        let overrides = ActionClassificationOverrides {
            message_response_overrides: vec!["Send1b".to_string()],
            ..Default::default()
        };
        let (kind, _) = classify_single_action("LSend1b", &[], &overrides);
        assert_eq!(
            kind,
            ActionKind::MessageDriven,
            "Send1b is a response to Prepare (via TOML override)"
        );
    }

    #[test]
    fn test_classify_paxos_send2b_message_response() {
        let overrides = ActionClassificationOverrides {
            message_response_overrides: vec!["Send2b".to_string()],
            ..Default::default()
        };
        let (kind, _) = classify_single_action("LSend2b", &[], &overrides);
        assert_eq!(
            kind,
            ActionKind::MessageDriven,
            "Send2b is a response to Accept (via TOML override)"
        );
    }

    #[test]
    fn test_classify_grant_vote() {
        let overrides = ActionClassificationOverrides {
            message_response_overrides: vec!["GrantVote".to_string()],
            ..Default::default()
        };
        let (kind, _) = classify_single_action("LGrantVote", &[], &overrides);
        assert_eq!(kind, ActionKind::MessageDriven);
    }

    #[test]
    fn test_classify_become_leader() {
        // BecomeLeader is a quorum state transition (votes_granted >= quorum_size),
        // not a response to a specific message variant.
        let (kind, _) = classify_single_action(
            "LBecomeLeader",
            &[],
            &ActionClassificationOverrides::default(),
        );
        assert_eq!(kind, ActionKind::TimerDriven);
    }

    #[test]
    fn test_classify_handle_append_reject_timer() {
        // HandleAppendReject contains "Handle" keyword but is a failure sub-case
        // of the AppendResponse handler — should be timer_driven via TOML override.
        let overrides = ActionClassificationOverrides {
            timer_overrides: vec!["HandleAppendReject".to_string()],
            ..Default::default()
        };
        let (kind, _) = classify_single_action("LHandleAppendReject", &[], &overrides);
        assert_eq!(kind, ActionKind::TimerDriven);
    }

    #[test]
    fn test_classify_step_down_timer() {
        // StepDown detects higher terms from any message — cross-cutting concern,
        // not a single-variant message handler.
        let (kind, _) =
            classify_single_action("LStepDown", &[], &ActionClassificationOverrides::default());
        assert_eq!(kind, ActionKind::TimerDriven);
    }

    #[test]
    fn test_classify_pre_prepare_timer() {
        // PrePrepare is the primary initiating a round — not responding to a message.
        let (kind, _) = classify_single_action(
            "LPrePrepare",
            &[],
            &ActionClassificationOverrides::default(),
        );
        assert_eq!(kind, ActionKind::TimerDriven);
    }

    #[test]
    fn test_classify_enter_commit_timer() {
        // EnterCommit is a quorum state transition (prepare_senders >= threshold).
        let (kind, _) = classify_single_action(
            "LEnterCommit",
            &[],
            &ActionClassificationOverrides::default(),
        );
        assert_eq!(kind, ActionKind::TimerDriven);
    }

    #[test]
    fn test_classify_execute_reply_timer() {
        // ExecuteReply is a quorum state transition (commit_senders >= threshold).
        let (kind, _) = classify_single_action(
            "LExecuteReply",
            &[],
            &ActionClassificationOverrides::default(),
        );
        assert_eq!(kind, ActionKind::TimerDriven);
    }

    #[test]
    fn test_classify_primary_write_timer() {
        // PrimaryWrite is a client request action, not triggered by network message.
        let (kind, _) = classify_single_action(
            "LPrimaryWrite",
            &[],
            &ActionClassificationOverrides::default(),
        );
        assert_eq!(kind, ActionKind::TimerDriven);
    }

    #[test]
    fn test_classify_send_prepare_timer() {
        // TMSendPrepare is a spontaneous action (TM initiates prepare)
        let (kind, _) = classify_single_action(
            "LTMSendPrepare",
            &[],
            &ActionClassificationOverrides::default(),
        );
        assert_eq!(kind, ActionKind::TimerDriven);
    }

    #[test]
    fn test_classify_send1a_timer() {
        // Send1a is Paxos proposer initiating Phase 1
        let (kind, _) =
            classify_single_action("LSend1a", &[], &ActionClassificationOverrides::default());
        assert_eq!(kind, ActionKind::TimerDriven);
    }

    #[test]
    fn test_classify_learn_timer() {
        let (kind, _) =
            classify_single_action("LLearn", &[], &ActionClassificationOverrides::default());
        assert_eq!(kind, ActionKind::TimerDriven);
    }

    #[test]
    fn test_classify_client_request_timer() {
        let (kind, _) = classify_single_action(
            "LClientRequest",
            &[],
            &ActionClassificationOverrides::default(),
        );
        assert_eq!(kind, ActionKind::TimerDriven);
    }

    #[test]
    fn test_classify_with_variant_matching() {
        let variants = vec!["Prepare".to_string(), "Promise".to_string()];
        let (kind, variant) = classify_single_action(
            "LRMReceivePrepare",
            &variants,
            &ActionClassificationOverrides::default(),
        );
        assert_eq!(kind, ActionKind::MessageDriven);
        assert_eq!(variant, Some("Prepare".to_string()));
    }

    #[test]
    fn test_classify_rcv_with_variant_matching() {
        let variants = vec!["Prepare".to_string(), "PreparedVote".to_string()];
        let (kind, variant) = classify_single_action(
            "LTMRcvPrepared",
            &variants,
            &ActionClassificationOverrides::default(),
        );
        assert_eq!(kind, ActionKind::MessageDriven);
        assert_eq!(variant, Some("PreparedVote".to_string()));
    }

    #[test]
    fn test_strip_role_prefix() {
        assert_eq!(strip_role_prefix("TMSendPrepare", &[]), "SendPrepare");
        assert_eq!(strip_role_prefix("RMReceivePrepare", &[]), "ReceivePrepare");
        assert_eq!(
            strip_role_prefix("FollowerAppendEntries", &[]),
            "AppendEntries"
        );
        assert_eq!(strip_role_prefix("PrimaryWrite", &[]), "Write");
        assert_eq!(strip_role_prefix("NoPrefix", &[]), "NoPrefix");
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
        classify_actions(
            &mut config,
            &variants,
            &ActionClassificationOverrides::default(),
        );

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
        assert_eq!(
            find("LRMReceivePrepare").message_variant,
            Some("Prepare".to_string())
        );
        assert_eq!(
            find("LRMReceiveCommit").message_variant,
            Some("Commit".to_string())
        );
        assert_eq!(
            find("LTMRcvPrepared").message_variant,
            Some("PreparedVote".to_string())
        );
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
        let overrides = ActionClassificationOverrides {
            message_response_overrides: vec!["Send1b".to_string(), "Send2b".to_string()],
            ..Default::default()
        };
        classify_actions(&mut config, &variants, &overrides);

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
        // Phase 27.4: LNext now uses composite actions (5 branches)
        let variants = vec![
            "RequestVote".to_string(),
            "VoteResponse".to_string(),
            "AppendEntries".to_string(),
            "AppendResponse".to_string(),
        ];
        let overrides = ActionClassificationOverrides::default();
        classify_actions(&mut config, &variants, &overrides);

        let find = |name: &str| config.actions.iter().find(|a| a.spec_name == name).unwrap();

        // Timer-driven actions
        assert_eq!(find("LTimeout").kind, ActionKind::TimerDriven);
        assert_eq!(find("LSendAppendEntries").kind, ActionKind::TimerDriven);
        assert_eq!(find("LClientRequest").kind, ActionKind::TimerDriven);
        assert_eq!(find("LTryAdvanceCommitIndex").kind, ActionKind::TimerDriven);

        // Message-driven: LHandleMessage dispatches all incoming messages
        assert_eq!(find("LHandleMessage").kind, ActionKind::MessageDriven);
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
        let overrides = ActionClassificationOverrides {
            message_response_overrides: vec!["SendAnswer".to_string()],
            ..Default::default()
        };
        classify_actions(&mut config, &variants, &overrides);

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
        assert_eq!(
            find("LReceiveAnswer").message_variant,
            Some("Answer".to_string())
        );
        assert_eq!(
            find("LReceiveCoordinator").message_variant,
            Some("Coordinator".to_string())
        );
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
        classify_actions(
            &mut config,
            &variants,
            &ActionClassificationOverrides::default(),
        );

        let find = |name: &str| config.actions.iter().find(|a| a.spec_name == name).unwrap();

        // Timer-driven (including client request action)
        assert_eq!(find("LPrimarySendReplicate").kind, ActionKind::TimerDriven);
        assert_eq!(find("LBackupSendAck").kind, ActionKind::TimerDriven);
        assert_eq!(find("LPrimaryCommit").kind, ActionKind::TimerDriven);
        assert_eq!(find("LPrimaryFail").kind, ActionKind::TimerDriven);
        assert_eq!(find("LBackupPromote").kind, ActionKind::TimerDriven);
        assert_eq!(find("LPrimaryWrite").kind, ActionKind::TimerDriven); // client request, no msgs_* flags

        // Message-driven
        assert_eq!(
            find("LBackupReceiveReplicate").kind,
            ActionKind::MessageDriven
        );
        assert_eq!(find("LPrimaryReceiveAck").kind, ActionKind::MessageDriven);

        // Variant matching
        assert_eq!(
            find("LBackupReceiveReplicate").message_variant,
            Some("Replicate".to_string())
        );
        assert_eq!(
            find("LPrimaryReceiveAck").message_variant,
            Some("Ack".to_string())
        );
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
        let overrides = ActionClassificationOverrides {
            message_response_overrides: vec!["ClientRead".to_string()],
            ..Default::default()
        };
        classify_actions(&mut config, &variants, &overrides);

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
        classify_actions(
            &mut config,
            &variants,
            &ActionClassificationOverrides::default(),
        );

        let find = |name: &str| config.actions.iter().find(|a| a.spec_name == name).unwrap();

        // Timer-driven (including quorum state transitions and primary initiation)
        assert_eq!(find("LCheckpoint").kind, ActionKind::TimerDriven);
        assert_eq!(find("LViewChange").kind, ActionKind::TimerDriven);
        assert_eq!(find("LNewRound").kind, ActionKind::TimerDriven);
        assert_eq!(find("LPrePrepare").kind, ActionKind::TimerDriven); // primary initiates, no incoming msg
        assert_eq!(find("LEnterCommit").kind, ActionKind::TimerDriven); // quorum state transition
        assert_eq!(find("LExecuteReply").kind, ActionKind::TimerDriven); // quorum state transition

        // Message-driven (actions that check msgs_* flags)
        assert_eq!(find("LReceivePrePrepare").kind, ActionKind::MessageDriven);
        assert_eq!(find("LReceivePrepare").kind, ActionKind::MessageDriven);
        assert_eq!(find("LReceiveCommit").kind, ActionKind::MessageDriven);

        // Variant matching
        assert_eq!(
            find("LReceivePrePrepare").message_variant,
            Some("PrePrepare".to_string())
        );
        assert_eq!(
            find("LReceivePrepare").message_variant,
            Some("Prepare".to_string())
        );
        assert_eq!(
            find("LReceiveCommit").message_variant,
            Some("Commit".to_string())
        );
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
        let overrides = ActionClassificationOverrides {
            message_response_overrides: vec![
                "SendPromise".to_string(),
                "WitnessSync".to_string(),
                "Sync".to_string(),
            ],
            ..Default::default()
        };
        classify_actions(&mut config, &variants, &overrides);

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
        let overrides = ActionClassificationOverrides {
            message_response_overrides: vec![
                "SendPreAcceptOk".to_string(),
                "SendAcceptOk".to_string(),
            ],
            ..Default::default()
        };
        classify_actions(&mut config, &variants, &overrides);

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
        assert_eq!(
            find("LReceivePreAcceptOk").message_variant,
            Some("PreAcceptOk".to_string())
        );
        assert_eq!(
            find("LReceiveAcceptOk").message_variant,
            Some("AcceptOk".to_string())
        );
    }

    #[test]
    fn test_action_kind_display() {
        assert_eq!(format!("{}", ActionKind::MessageDriven), "message_driven");
        assert_eq!(format!("{}", ActionKind::TimerDriven), "timer_driven");
    }

    #[test]
    fn test_classify_no_variants_still_works() {
        // Classification should work even without message variants (no variant matching)
        let (kind, variant) = classify_single_action(
            "LReceivePrepare",
            &[],
            &ActionClassificationOverrides::default(),
        );
        assert_eq!(kind, ActionKind::MessageDriven);
        assert!(variant.is_none());
    }

    // ---------------------------------------------------------------
    // TOML-driven classification tests (Phase 25.3)
    // ---------------------------------------------------------------

    #[test]
    fn test_toml_message_response_override_beats_default_timer() {
        // Without override: "Send1b" has no message keywords → TimerDriven
        let (kind, _) =
            classify_single_action("LSend1b", &[], &ActionClassificationOverrides::default());
        assert_eq!(kind, ActionKind::TimerDriven);

        // With override: "Send1b" is explicitly marked as message-driven
        let overrides = ActionClassificationOverrides {
            message_response_overrides: vec!["Send1b".to_string()],
            ..Default::default()
        };
        let (kind, _) = classify_single_action("LSend1b", &[], &overrides);
        assert_eq!(kind, ActionKind::MessageDriven);
    }

    #[test]
    fn test_toml_timer_override_beats_message_keyword() {
        // Without override: "HandleAppendReject" contains "Handle" → MessageDriven
        let (kind, _) = classify_single_action(
            "LHandleAppendReject",
            &[],
            &ActionClassificationOverrides::default(),
        );
        assert_eq!(kind, ActionKind::MessageDriven);

        // With timer override: explicitly marked as timer-driven despite "Handle" keyword
        let overrides = ActionClassificationOverrides {
            timer_overrides: vec!["HandleAppendReject".to_string()],
            ..Default::default()
        };
        let (kind, _) = classify_single_action("LHandleAppendReject", &[], &overrides);
        assert_eq!(kind, ActionKind::TimerDriven);
    }

    #[test]
    fn test_toml_timer_override_priority_over_message_response() {
        // If both timer and message overrides match, timer wins (checked first)
        let overrides = ActionClassificationOverrides {
            message_response_overrides: vec!["Foo".to_string()],
            timer_overrides: vec!["Foo".to_string()],
            ..Default::default()
        };
        let (kind, _) = classify_single_action("LFoo", &[], &overrides);
        assert_eq!(kind, ActionKind::TimerDriven);
    }

    #[test]
    fn test_toml_custom_role_prefixes_for_variant_matching() {
        let variants = vec!["Write".to_string(), "Read".to_string()];
        // With custom role prefix "Node", "NodeReceiveWrite" → strip "Node" → "ReceiveWrite"
        // → keyword "Write" matches variant "Write"
        let overrides = ActionClassificationOverrides {
            role_prefixes: vec!["Node".to_string()],
            ..Default::default()
        };
        let (kind, variant) = classify_single_action("LNodeReceiveWrite", &variants, &overrides);
        assert_eq!(kind, ActionKind::MessageDriven);
        assert_eq!(variant, Some("Write".to_string()));
    }

    #[test]
    fn test_toml_custom_role_prefixes_override_defaults() {
        let variants = vec!["Prepare".to_string()];
        // With custom role prefix that doesn't include "TM", "TMRcvPrepare" won't strip "TM"
        let overrides = ActionClassificationOverrides {
            role_prefixes: vec!["Node".to_string()],
            ..Default::default()
        };
        let (kind, variant) = classify_single_action("LTMRcvPrepare", &variants, &overrides);
        assert_eq!(kind, ActionKind::MessageDriven);
        // Since "TM" is NOT in custom role_prefixes, it won't strip "TM"
        // but "Rcv" verb is stripped → keyword "TMRcv" doesn't work
        // However, strategy 2 (containment) should still find "Prepare" in "TMRcvPrepare"
        assert_eq!(variant, Some("Prepare".to_string()));
    }

    #[test]
    fn test_toml_empty_overrides_use_defaults() {
        // Empty overrides should use DEFAULT_ROLE_PREFIXES for stripping
        let variants = vec!["Prepare".to_string()];
        let (kind, variant) = classify_single_action(
            "LTMRcvPrepare",
            &variants,
            &ActionClassificationOverrides::default(),
        );
        assert_eq!(kind, ActionKind::MessageDriven);
        assert_eq!(variant, Some("Prepare".to_string()));
    }

    #[test]
    fn test_strip_role_prefix_custom_list() {
        let custom = vec!["Node".to_string(), "Shard".to_string()];
        assert_eq!(
            strip_role_prefix("NodeReceiveWrite", &custom),
            "ReceiveWrite"
        );
        assert_eq!(strip_role_prefix("ShardForward", &custom), "Forward");
        // Default prefixes NOT used when custom list provided
        assert_eq!(strip_role_prefix("TMSendPrepare", &custom), "TMSendPrepare");
    }

    #[test]
    fn test_toml_scheduler_config_deserializes_overrides() {
        let toml_str = r#"
[naming]
spec_prefix = "L"
exec_prefix = "C"

[scheduler]
next_fn = "LNext"
params = ["s", "s_"]
action_count = 2
message_response_overrides = ["Send1b", "Send2b"]
role_prefixes = ["Node"]
timer_overrides = ["HandleReject"]

[[scheduler.actions]]
spec_name = "LSend1b"
exec_name = "CSend1b"
kind = "message_driven"
existential_params = []

[[scheduler.actions]]
spec_name = "LTimeout"
exec_name = "CTimeout"
kind = "timer_driven"
existential_params = []
"#;
        let config: crate::config::TranspilerConfig =
            toml::from_str(toml_str).expect("Failed to parse TOML with overrides");
        let sched = config.scheduler.expect("Should have scheduler section");
        assert_eq!(
            sched.message_response_overrides,
            vec!["Send1b".to_string(), "Send2b".to_string()]
        );
        assert_eq!(sched.role_prefixes, vec!["Node".to_string()]);
        assert_eq!(sched.timer_overrides, vec!["HandleReject".to_string()]);
    }

    #[test]
    fn test_toml_scheduler_config_defaults_when_omitted() {
        let toml_str = r#"
[naming]
spec_prefix = "L"
exec_prefix = "C"

[scheduler]
next_fn = "LNext"
params = ["s", "s_"]
action_count = 0
"#;
        let config: crate::config::TranspilerConfig =
            toml::from_str(toml_str).expect("Failed to parse TOML without overrides");
        let sched = config.scheduler.expect("Should have scheduler section");
        assert!(sched.message_response_overrides.is_empty());
        assert!(sched.role_prefixes.is_empty());
        assert!(sched.timer_overrides.is_empty());
    }

    #[test]
    fn test_message_response_override_gets_variant_matching() {
        // A message_response_override should still participate in variant matching
        let variants = vec!["PreAcceptOk".to_string(), "AcceptOk".to_string()];
        let overrides = ActionClassificationOverrides {
            message_response_overrides: vec!["SendPreAcceptOk".to_string()],
            ..Default::default()
        };
        let (kind, variant) = classify_single_action("LSendPreAcceptOk", &variants, &overrides);
        assert_eq!(kind, ActionKind::MessageDriven);
        assert_eq!(variant, Some("PreAcceptOk".to_string()));
    }

    // ---------------------------------------------------------------
    // validate_scaffold_params tests
    // ---------------------------------------------------------------

    fn make_action(spec_name: &str, kind: &str, variant: Option<&str>) -> SchedulerActionConfig {
        SchedulerActionConfig {
            spec_name: spec_name.to_string(),
            exec_name: format!("C{}", &spec_name[1..]),
            kind: kind.to_string(),
            message_variant: variant.map(|s| s.to_string()),
            existential_params: vec![],
            flag_injections: vec![],
            guard_checks: vec![],
        }
    }

    fn make_variant(name: &str) -> MessageVariant {
        MessageVariant {
            name: name.to_string(),
            fields: vec![],
            doc: String::new(),
        }
    }

    fn make_params(
        actions: Vec<SchedulerActionConfig>,
        variants: Vec<MessageVariant>,
    ) -> HostScaffoldParams {
        HostScaffoldParams {
            protocol_name: "Test".to_string(),
            module_name: "test".to_string(),
            gen_module: "test_gen".to_string(),
            message_enum: "TestMessage".to_string(),
            message_variants: variants,
            actions,
            role_dispatch: None,
        }
    }

    #[test]
    fn test_validate_no_warnings_when_valid() {
        let params = make_params(
            vec![
                make_action("LReceivePrepare", "message_driven", Some("Prepare")),
                make_action("LSend1a", "timer_driven", None),
            ],
            vec![make_variant("Prepare")],
        );
        let warnings = validate_scaffold_params(&params);
        assert!(
            warnings.is_empty(),
            "expected no warnings, got: {:?}",
            warnings
        );
    }

    #[test]
    fn test_validate_missing_message_variant() {
        let params = make_params(
            vec![make_action("LReceivePrepare", "message_driven", None)],
            vec![make_variant("Prepare")],
        );
        let warnings = validate_scaffold_params(&params);
        assert_eq!(warnings.len(), 1);
        assert!(warnings[0].contains("no message_variant"));
        assert!(warnings[0].contains("LReceivePrepare"));
    }

    #[test]
    fn test_validate_nonexistent_variant_reference() {
        let params = make_params(
            vec![make_action(
                "LReceivePrepare",
                "message_driven",
                Some("Bogus"),
            )],
            vec![make_variant("Prepare")],
        );
        let warnings = validate_scaffold_params(&params);
        assert_eq!(warnings.len(), 1);
        assert!(warnings[0].contains("non-existent"));
        assert!(warnings[0].contains("Bogus"));
    }

    #[test]
    fn test_validate_shared_variant_conflict() {
        let params = make_params(
            vec![
                make_action("LReceivePrepare", "message_driven", Some("Prepare")),
                make_action("LSendPromise", "message_driven", Some("Prepare")),
            ],
            vec![make_variant("Prepare")],
        );
        let warnings = validate_scaffold_params(&params);
        assert_eq!(warnings.len(), 1);
        assert!(warnings[0].contains("multiple actions"));
        assert!(warnings[0].contains("Prepare"));
        assert!(warnings[0].contains("LReceivePrepare"));
        assert!(warnings[0].contains("LSendPromise"));
    }

    #[test]
    fn test_validate_timer_driven_ignored() {
        // Timer-driven actions should not be checked for message_variant
        let params = make_params(
            vec![make_action("LPropose", "timer_driven", None)],
            vec![make_variant("Prepare")],
        );
        let warnings = validate_scaffold_params(&params);
        assert!(warnings.is_empty());
    }

    #[test]
    fn test_validate_multiple_issues() {
        let params = make_params(
            vec![
                make_action("LReceivePrepare", "message_driven", None), // missing variant
                make_action("LSendPromise", "message_driven", Some("Bogus")), // non-existent
                make_action("LRecvAccepted", "message_driven", Some("Accept")), // shared
                make_action("LSend2b", "message_driven", Some("Accept")), // shared
            ],
            vec![make_variant("Prepare"), make_variant("Accept")],
        );
        let warnings = validate_scaffold_params(&params);
        assert!(
            warnings.len() >= 3,
            "expected >=3 warnings, got: {:?}",
            warnings
        );
        // Should have: missing variant, non-existent reference, shared conflict
        let joined = warnings.join(" | ");
        assert!(joined.contains("no message_variant"));
        assert!(joined.contains("non-existent"));
        assert!(joined.contains("multiple actions"));
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
                    flag_injections: vec![],
                    guard_checks: vec![],
                },
                SchedulerActionConfig {
                    spec_name: "LSend1b".to_string(),
                    exec_name: "CSend1b".to_string(),
                    kind: "message_driven".to_string(),
                    message_variant: None,
                    existential_params: vec![vec!["b".to_string(), "int".to_string()]],
                    flag_injections: vec![],
                    guard_checks: vec![],
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
                    flag_injections: vec![],
                    guard_checks: vec![],
                },
                SchedulerActionConfig {
                    spec_name: "LSend2a".to_string(),
                    exec_name: "CSend2a".to_string(),
                    kind: "timer_driven".to_string(),
                    message_variant: None,
                    existential_params: vec![vec!["v".to_string(), "int".to_string()]],
                    flag_injections: vec![],
                    guard_checks: vec![],
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
                    flag_injections: vec![],
                    guard_checks: vec![],
                },
                SchedulerActionConfig {
                    spec_name: "LRecvAccepted".to_string(),
                    exec_name: "CRecvAccepted".to_string(),
                    kind: "message_driven".to_string(),
                    message_variant: Some("Accepted".to_string()),
                    existential_params: vec![vec!["a".to_string(), "int".to_string()]],
                    flag_injections: vec![],
                    guard_checks: vec![],
                },
                SchedulerActionConfig {
                    spec_name: "LLearn".to_string(),
                    exec_name: "CLearn".to_string(),
                    kind: "timer_driven".to_string(),
                    message_variant: None,
                    existential_params: vec![],
                    flag_injections: vec![],
                    guard_checks: vec![],
                },
            ],
            role_dispatch: None,
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
        assert!(
            code.contains("self.handle_crecv_accepted(config, &pkt.src, sender_id, ballot, value)")
        );
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
            role_dispatch: None,
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
                    flag_injections: vec![],
                    guard_checks: vec![],
                },
                SchedulerActionConfig {
                    spec_name: "LAction2".to_string(),
                    exec_name: "CAction2".to_string(),
                    kind: "timer_driven".to_string(),
                    message_variant: None,
                    existential_params: vec![],
                    flag_injections: vec![],
                    guard_checks: vec![],
                },
            ],
            role_dispatch: None,
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
                flag_injections: vec![],
                guard_checks: vec![],
            }],
            role_dispatch: None,
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

    // ---------------------------------------------------------------
    // Phase 17.4.4a: Role-based dispatch tests
    // ---------------------------------------------------------------

    /// Helper: TwoPhase-like params with config_index dispatch (TM vs RM).
    fn make_twophase_role_params() -> HostScaffoldParams {
        HostScaffoldParams {
            protocol_name: "TwoPhase".to_string(),
            module_name: "twophase".to_string(),
            gen_module: "twophase_gen".to_string(),
            message_enum: "TwoPhaseMessage".to_string(),
            message_variants: vec![
                MessageVariant {
                    name: "Prepare".to_string(),
                    doc: String::new(),
                    fields: vec![],
                },
                MessageVariant {
                    name: "PreparedVote".to_string(),
                    doc: String::new(),
                    fields: vec![vec!["sender".to_string(), "u64".to_string()]],
                },
                MessageVariant {
                    name: "Commit".to_string(),
                    doc: String::new(),
                    fields: vec![],
                },
                MessageVariant {
                    name: "Abort".to_string(),
                    doc: String::new(),
                    fields: vec![],
                },
            ],
            actions: vec![
                SchedulerActionConfig {
                    spec_name: "LTMSendPrepare".to_string(),
                    exec_name: "CTMSendPrepare".to_string(),
                    kind: "timer_driven".to_string(),
                    message_variant: None,
                    existential_params: vec![],
                    flag_injections: vec![],
                    guard_checks: vec![],
                },
                SchedulerActionConfig {
                    spec_name: "LTMSendCommit".to_string(),
                    exec_name: "CTMSendCommit".to_string(),
                    kind: "timer_driven".to_string(),
                    message_variant: None,
                    existential_params: vec![],
                    flag_injections: vec![],
                    guard_checks: vec![],
                },
                SchedulerActionConfig {
                    spec_name: "LTMSendAbort".to_string(),
                    exec_name: "CTMSendAbort".to_string(),
                    kind: "timer_driven".to_string(),
                    message_variant: None,
                    existential_params: vec![],
                    flag_injections: vec![],
                    guard_checks: vec![],
                },
                SchedulerActionConfig {
                    spec_name: "LTMRecvPrepared".to_string(),
                    exec_name: "CTMRecvPrepared".to_string(),
                    kind: "message_driven".to_string(),
                    message_variant: Some("PreparedVote".to_string()),
                    existential_params: vec![],
                    flag_injections: vec![],
                    guard_checks: vec![],
                },
                SchedulerActionConfig {
                    spec_name: "LRMRecvPrepare".to_string(),
                    exec_name: "CRMRecvPrepare".to_string(),
                    kind: "message_driven".to_string(),
                    message_variant: Some("Prepare".to_string()),
                    existential_params: vec![],
                    flag_injections: vec![],
                    guard_checks: vec![],
                },
                SchedulerActionConfig {
                    spec_name: "LRMRecvCommit".to_string(),
                    exec_name: "CRMRecvCommit".to_string(),
                    kind: "message_driven".to_string(),
                    message_variant: Some("Commit".to_string()),
                    existential_params: vec![],
                    flag_injections: vec![],
                    guard_checks: vec![],
                },
                SchedulerActionConfig {
                    spec_name: "LRMRecvAbort".to_string(),
                    exec_name: "CRMRecvAbort".to_string(),
                    kind: "message_driven".to_string(),
                    message_variant: Some("Abort".to_string()),
                    existential_params: vec![],
                    flag_injections: vec![],
                    guard_checks: vec![],
                },
            ],
            role_dispatch: Some(RoleDispatchConfig {
                dispatch_style: "config_index".to_string(),
                dispatch_field: "config.my_index".to_string(),
                roles: vec![
                    RoleConfig {
                        name: "tm".to_string(),
                        condition: "config.my_index == 0".to_string(),
                        actions: vec![
                            "CTMSendPrepare".to_string(),
                            "CTMSendCommit".to_string(),
                            "CTMSendAbort".to_string(),
                            "CTMRecvPrepared".to_string(),
                        ],
                    },
                    RoleConfig {
                        name: "rm".to_string(),
                        condition: String::new(),
                        actions: vec![
                            "CRMRecvPrepare".to_string(),
                            "CRMRecvCommit".to_string(),
                            "CRMRecvAbort".to_string(),
                        ],
                    },
                ],
            }),
        }
    }

    /// Helper: ChainReplication-like params with state_field dispatch (3 roles).
    fn make_chain_role_params() -> HostScaffoldParams {
        HostScaffoldParams {
            protocol_name: "Chain".to_string(),
            module_name: "chain".to_string(),
            gen_module: "chain_gen".to_string(),
            message_enum: "ChainMessage".to_string(),
            message_variants: vec![
                MessageVariant {
                    name: "ClientWrite".to_string(),
                    doc: String::new(),
                    fields: vec![vec!["value".to_string(), "u64".to_string()]],
                },
                MessageVariant {
                    name: "Forward".to_string(),
                    doc: String::new(),
                    fields: vec![vec!["value".to_string(), "u64".to_string()]],
                },
                MessageVariant {
                    name: "Ack".to_string(),
                    doc: String::new(),
                    fields: vec![vec!["seq".to_string(), "u64".to_string()]],
                },
            ],
            actions: vec![
                SchedulerActionConfig {
                    spec_name: "LHeadRecvWrite".to_string(),
                    exec_name: "CHeadRecvWrite".to_string(),
                    kind: "message_driven".to_string(),
                    message_variant: Some("ClientWrite".to_string()),
                    existential_params: vec![],
                    flag_injections: vec![],
                    guard_checks: vec![],
                },
                SchedulerActionConfig {
                    spec_name: "LHeadForward".to_string(),
                    exec_name: "CHeadForward".to_string(),
                    kind: "timer_driven".to_string(),
                    message_variant: None,
                    existential_params: vec![],
                    flag_injections: vec![],
                    guard_checks: vec![],
                },
                SchedulerActionConfig {
                    spec_name: "LMiddleRecvFwd".to_string(),
                    exec_name: "CMiddleRecvFwd".to_string(),
                    kind: "message_driven".to_string(),
                    message_variant: Some("Forward".to_string()),
                    existential_params: vec![],
                    flag_injections: vec![],
                    guard_checks: vec![],
                },
                SchedulerActionConfig {
                    spec_name: "LMiddleRecvAck".to_string(),
                    exec_name: "CMiddleRecvAck".to_string(),
                    kind: "message_driven".to_string(),
                    message_variant: Some("Ack".to_string()),
                    existential_params: vec![],
                    flag_injections: vec![],
                    guard_checks: vec![],
                },
                SchedulerActionConfig {
                    spec_name: "LTailRecvFwd".to_string(),
                    exec_name: "CTailRecvFwd".to_string(),
                    kind: "message_driven".to_string(),
                    message_variant: Some("Forward".to_string()),
                    existential_params: vec![],
                    flag_injections: vec![],
                    guard_checks: vec![],
                },
                SchedulerActionConfig {
                    spec_name: "LTailCommit".to_string(),
                    exec_name: "CTailCommit".to_string(),
                    kind: "timer_driven".to_string(),
                    message_variant: None,
                    existential_params: vec![],
                    flag_injections: vec![],
                    guard_checks: vec![],
                },
            ],
            role_dispatch: Some(RoleDispatchConfig {
                dispatch_style: "state_field".to_string(),
                dispatch_field: "self.state.role".to_string(),
                roles: vec![
                    RoleConfig {
                        name: "head".to_string(),
                        condition: "CNodeRole::Head".to_string(),
                        actions: vec!["CHeadRecvWrite".to_string(), "CHeadForward".to_string()],
                    },
                    RoleConfig {
                        name: "middle".to_string(),
                        condition: "CNodeRole::Middle".to_string(),
                        actions: vec!["CMiddleRecvFwd".to_string(), "CMiddleRecvAck".to_string()],
                    },
                    RoleConfig {
                        name: "tail".to_string(),
                        condition: "CNodeRole::Tail".to_string(),
                        actions: vec!["CTailRecvFwd".to_string(), "CTailCommit".to_string()],
                    },
                ],
            }),
        }
    }

    #[test]
    fn test_role_dispatch_config_index_generates_step_methods() {
        let params = make_twophase_role_params();
        let code = generate_host_scaffold(&params);
        // Both role step methods should be generated
        assert!(code.contains("fn tm_step("), "Missing tm_step method");
        assert!(code.contains("fn rm_step("), "Missing rm_step method");
    }

    #[test]
    fn test_role_dispatch_config_index_next_uses_if_else() {
        let params = make_twophase_role_params();
        let code = generate_host_scaffold(&params);
        // next() should dispatch via if-else on config.my_index
        assert!(
            code.contains("if config.my_index == 0 {"),
            "Missing config_index condition"
        );
        assert!(
            code.contains("self.tm_step(config, packet)"),
            "Missing tm_step call in next()"
        );
        assert!(
            code.contains("self.rm_step(config, packet)"),
            "Missing rm_step call in next()"
        );
        // The else branch (last role with empty condition)
        assert!(code.contains("} else {"), "Missing else branch");
    }

    #[test]
    fn test_role_dispatch_config_index_tm_timers() {
        let params = make_twophase_role_params();
        let code = generate_host_scaffold(&params);
        // TM has 3 timer-driven actions → round-robin % 3
        assert!(
            code.contains("self.action_index % 3"),
            "TM should have 3 timer actions"
        );
        // to_snake_case("CTMSendPrepare") = "ctmsend_prepare" (consecutive uppercase collapsed)
        assert!(code.contains("self.try_ctmsend_prepare(config)"));
        assert!(code.contains("self.try_ctmsend_commit(config)"));
        assert!(code.contains("self.try_ctmsend_abort(config)"));
    }

    #[test]
    fn test_role_dispatch_config_index_tm_messages() {
        let params = make_twophase_role_params();
        let code = generate_host_scaffold(&params);
        // TM step handles PreparedVote, not Prepare/Commit/Abort
        // to_snake_case("CTMRecvPrepared") = "ctmrecv_prepared"
        assert!(code.contains("self.handle_ctmrecv_prepared(config, &pkt.src, sender_id, sender)"));
    }

    #[test]
    fn test_role_dispatch_config_index_rm_messages() {
        let params = make_twophase_role_params();
        let code = generate_host_scaffold(&params);
        // RM step handles Prepare, Commit, Abort, not PreparedVote
        // to_snake_case("CRMRecvPrepare") = "crmrecv_prepare"
        assert!(code.contains("self.handle_crmrecv_prepare(config, &pkt.src, sender_id)"));
        assert!(code.contains("self.handle_crmrecv_commit(config, &pkt.src, sender_id)"));
        assert!(code.contains("self.handle_crmrecv_abort(config, &pkt.src, sender_id)"));
    }

    #[test]
    fn test_role_dispatch_state_field_generates_step_methods() {
        let params = make_chain_role_params();
        let code = generate_host_scaffold(&params);
        assert!(code.contains("fn head_step("), "Missing head_step method");
        assert!(
            code.contains("fn middle_step("),
            "Missing middle_step method"
        );
        assert!(code.contains("fn tail_step("), "Missing tail_step method");
    }

    #[test]
    fn test_role_dispatch_state_field_next_uses_match() {
        let params = make_chain_role_params();
        let code = generate_host_scaffold(&params);
        // next() should dispatch via match on self.state.role
        assert!(
            code.contains("match self.state.role {"),
            "Missing match on dispatch_field"
        );
        assert!(code.contains("CNodeRole::Head => self.head_step(config, packet)"));
        assert!(code.contains("CNodeRole::Middle => self.middle_step(config, packet)"));
        // Last role uses wildcard
        assert!(code.contains("_ => self.tail_step(config, packet)"));
    }

    #[test]
    fn test_role_dispatch_state_field_per_role_message_filtering() {
        let params = make_chain_role_params();
        let code = generate_host_scaffold(&params);

        // Head should handle ClientWrite, not Forward or Ack
        // Middle should handle Forward and Ack, not ClientWrite
        // Tail should handle Forward, not Ack or ClientWrite

        // Count occurrences of handler calls — each role's step method
        // calls different handlers for the same message variant
        let head_write =
            code.contains("self.handle_chead_recv_write(config, &pkt.src, sender_id, value)");
        assert!(head_write, "Head should handle ClientWrite");
    }

    #[test]
    fn test_role_dispatch_state_field_per_role_timers() {
        let params = make_chain_role_params();
        let code = generate_host_scaffold(&params);
        // Head has 1 timer (CHeadForward) → no modulo needed (just _ =>)
        // Tail has 1 timer (CTailCommit) → no modulo needed
        assert!(code.contains("self.try_chead_forward(config)"));
        assert!(code.contains("self.try_ctail_commit(config)"));
    }

    #[test]
    fn test_role_dispatch_none_falls_back_to_flat() {
        // When role_dispatch is None, should produce flat dispatch (backwards compat)
        let params = make_paxos_params();
        let code = generate_host_scaffold(&params);
        // Should NOT have any role step methods
        assert!(
            !code.contains("_step("),
            "Flat dispatch should not have role step methods"
        );
        // Should have flat ProtocolHost impl
        assert!(code.contains("impl ProtocolHost for PaxosHost {"));
        assert!(code.contains("return match pkt.msg {"));
    }

    #[test]
    fn test_role_dispatch_handler_stubs_still_generated() {
        // Even with role dispatch, the flat handler stubs are generated
        let params = make_twophase_role_params();
        let code = generate_host_scaffold(&params);
        // Message-driven handler stubs (consecutive uppercase collapsed by to_snake_case)
        assert!(code.contains("fn handle_ctmrecv_prepared("));
        assert!(code.contains("fn handle_crmrecv_prepare("));
        assert!(code.contains("fn handle_crmrecv_commit("));
        assert!(code.contains("fn handle_crmrecv_abort("));
        // Timer-driven handler stubs
        assert!(code.contains("fn try_ctmsend_prepare("));
        assert!(code.contains("fn try_ctmsend_commit("));
        assert!(code.contains("fn try_ctmsend_abort("));
    }

    #[test]
    fn test_role_dispatch_config_deserialize() {
        let toml_str = r#"
[scheduler]
next_fn = "LNext"
action_count = 2

[[scheduler.actions]]
spec_name = "LAction1"
exec_name = "CAction1"
kind = "timer_driven"

[[scheduler.actions]]
spec_name = "LAction2"
exec_name = "CAction2"
kind = "message_driven"
message_variant = "Ping"

[scheduler.role_dispatch]
dispatch_style = "config_index"
dispatch_field = "config.my_index"

[[scheduler.role_dispatch.roles]]
name = "leader"
condition = "config.my_index == 0"
actions = ["CAction1"]

[[scheduler.role_dispatch.roles]]
name = "follower"
condition = ""
actions = ["CAction2"]
"#;
        let config: crate::config::SchedulerTomlConfig = toml::from_str::<toml::Value>(toml_str)
            .unwrap()
            .get("scheduler")
            .unwrap()
            .clone()
            .try_into()
            .unwrap();

        let rd = config.role_dispatch.unwrap();
        assert_eq!(rd.dispatch_style, "config_index");
        assert_eq!(rd.dispatch_field, "config.my_index");
        assert_eq!(rd.roles.len(), 2);
        assert_eq!(rd.roles[0].name, "leader");
        assert_eq!(rd.roles[0].condition, "config.my_index == 0");
        assert_eq!(rd.roles[0].actions, vec!["CAction1"]);
        assert_eq!(rd.roles[1].name, "follower");
        assert_eq!(rd.roles[1].condition, "");
        assert_eq!(rd.roles[1].actions, vec!["CAction2"]);
    }

    #[test]
    fn test_role_dispatch_init_same_as_flat() {
        // init() should be the same whether role_dispatch is present or not
        let params = make_twophase_role_params();
        let code = generate_host_scaffold(&params);
        assert!(code.contains("twophase_gen::CInit(&config.constants)"));
        assert!(code.contains("Some(TwoPhaseHost {"));
        assert!(code.contains("action_index: 0"));
    }

    #[test]
    fn test_role_dispatch_no_flat_next_when_roles_present() {
        // When role_dispatch is present, the flat message dispatch in next() should NOT appear
        let params = make_twophase_role_params();
        let code = generate_host_scaffold(&params);
        // The flat "return match pkt.msg" should NOT be in next()
        // (it should only be in per-role step methods)
        // Count occurrences: should not appear outside role step methods
        // The ProtocolHost next() should only have the if-else dispatch
        let next_impl_start = code.find("fn next(").unwrap();
        let next_body = &code[next_impl_start..];
        let next_end = next_body.find("}\n}").unwrap();
        let next_body = &next_body[..next_end];
        // next() body should have if/else dispatch, not direct match pkt.msg
        assert!(next_body.contains("if config.my_index == 0"));
        assert!(!next_body.contains("return match pkt.msg"));
    }

    // ---------------------------------------------------------------
    // Phase 17.4.4b: Flag injection tests
    // ---------------------------------------------------------------

    #[test]
    fn test_flag_injection_basic() {
        let params = HostScaffoldParams {
            protocol_name: "FlagTest".to_string(),
            module_name: "flagtest".to_string(),
            gen_module: "flagtest_gen".to_string(),
            message_enum: "FlagMessage".to_string(),
            message_variants: vec![MessageVariant {
                name: "Election".to_string(),
                doc: String::new(),
                fields: vec![vec!["sender".to_string(), "u64".to_string()]],
            }],
            actions: vec![SchedulerActionConfig {
                spec_name: "LSendAnswer".to_string(),
                exec_name: "CSendAnswer".to_string(),
                kind: "message_driven".to_string(),
                message_variant: Some("Election".to_string()),
                existential_params: vec![],
                flag_injections: vec![
                    vec!["msgs_election".to_string(), "true".to_string()],
                    vec!["msgs_election_sender".to_string(), "sender".to_string()],
                ],
                guard_checks: vec![],
            }],
            role_dispatch: None,
        };
        let code = generate_host_scaffold(&params);
        // Flag injection comment
        assert!(
            code.contains("// Flag injection: simulate receiving the message"),
            "Missing flag injection comment"
        );
        // Literal boolean assignment
        assert!(
            code.contains("self.state.msgs_election = true;"),
            "Missing boolean flag injection"
        );
        // Parameter reference assignment
        assert!(
            code.contains("self.state.msgs_election_sender = sender;"),
            "Missing parameter flag injection"
        );
    }

    #[test]
    fn test_flag_injection_param_prefix_removed() {
        let params = HostScaffoldParams {
            protocol_name: "FlagTest".to_string(),
            module_name: "flagtest".to_string(),
            gen_module: "flagtest_gen".to_string(),
            message_enum: "FlagMessage".to_string(),
            message_variants: vec![MessageVariant {
                name: "Election".to_string(),
                doc: String::new(),
                fields: vec![vec!["sender".to_string(), "u64".to_string()]],
            }],
            actions: vec![SchedulerActionConfig {
                spec_name: "LSendAnswer".to_string(),
                exec_name: "CSendAnswer".to_string(),
                kind: "message_driven".to_string(),
                message_variant: Some("Election".to_string()),
                existential_params: vec![],
                flag_injections: vec![
                    vec!["msgs_election".to_string(), "true".to_string()],
                    vec!["msgs_election_sender".to_string(), "sender".to_string()],
                ],
                guard_checks: vec![],
            }],
            role_dispatch: None,
        };
        let code = generate_host_scaffold(&params);
        // Parameter used in flag injection should NOT have _ prefix
        assert!(
            code.contains("        sender: u64,"),
            "Used param should not have _ prefix"
        );
        assert!(
            !code.contains("        _sender: u64,"),
            "Used param should not have _ prefix"
        );
    }

    #[test]
    fn test_flag_injection_empty_backwards_compat() {
        // When flag_injections is empty, no injection code should appear
        let params = HostScaffoldParams {
            protocol_name: "NoFlag".to_string(),
            module_name: "noflag".to_string(),
            gen_module: "noflag_gen".to_string(),
            message_enum: "NoFlagMessage".to_string(),
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
                flag_injections: vec![],
                guard_checks: vec![],
            }],
            role_dispatch: None,
        };
        let code = generate_host_scaffold(&params);
        // No flag injection comment or self.state assignments
        assert!(
            !code.contains("// Flag injection:"),
            "Empty injections should produce no comment"
        );
        assert!(
            !code.contains("self.state."),
            "Empty injections should produce no state assignments"
        );
        // Unused parameter should still have _ prefix
        assert!(
            code.contains("_id: u64,"),
            "Unused param should have _ prefix"
        );
    }

    #[test]
    fn test_flag_injection_mixed_used_unused_params() {
        // Test with multiple fields: some used in injections, some not
        let params = HostScaffoldParams {
            protocol_name: "MixFlag".to_string(),
            module_name: "mixflag".to_string(),
            gen_module: "mixflag_gen".to_string(),
            message_enum: "MixMessage".to_string(),
            message_variants: vec![MessageVariant {
                name: "Promise".to_string(),
                doc: String::new(),
                fields: vec![
                    vec!["ballot".to_string(), "u64".to_string()],
                    vec!["v_bal".to_string(), "u64".to_string()],
                    vec!["val".to_string(), "u64".to_string()],
                ],
            }],
            actions: vec![SchedulerActionConfig {
                spec_name: "LRecvPromise".to_string(),
                exec_name: "CRecvPromise".to_string(),
                kind: "message_driven".to_string(),
                message_variant: Some("Promise".to_string()),
                existential_params: vec![],
                flag_injections: vec![
                    vec!["msgs_promise".to_string(), "true".to_string()],
                    vec!["msgs_promise_bal".to_string(), "ballot".to_string()],
                    // v_bal and val are NOT used in injections
                ],
                guard_checks: vec![],
            }],
            role_dispatch: None,
        };
        let code = generate_host_scaffold(&params);
        // ballot is used → no _ prefix
        assert!(
            code.contains("        ballot: u64,"),
            "Used ballot should not have _ prefix"
        );
        // v_bal and val are unused → _ prefix
        assert!(
            code.contains("        _v_bal: u64,"),
            "Unused v_bal should have _ prefix"
        );
        assert!(
            code.contains("        _val: u64,"),
            "Unused val should have _ prefix"
        );
        // Injections present
        assert!(code.contains("self.state.msgs_promise = true;"));
        assert!(code.contains("self.state.msgs_promise_bal = ballot;"));
    }

    #[test]
    fn test_flag_injection_false_literal() {
        let params = HostScaffoldParams {
            protocol_name: "FalseFlag".to_string(),
            module_name: "falseflag".to_string(),
            gen_module: "falseflag_gen".to_string(),
            message_enum: "FalseMessage".to_string(),
            message_variants: vec![MessageVariant {
                name: "Reset".to_string(),
                doc: String::new(),
                fields: vec![],
            }],
            actions: vec![SchedulerActionConfig {
                spec_name: "LReset".to_string(),
                exec_name: "CReset".to_string(),
                kind: "message_driven".to_string(),
                message_variant: Some("Reset".to_string()),
                existential_params: vec![],
                flag_injections: vec![vec!["msgs_active".to_string(), "false".to_string()]],
                guard_checks: vec![],
            }],
            role_dispatch: None,
        };
        let code = generate_host_scaffold(&params);
        assert!(
            code.contains("self.state.msgs_active = false;"),
            "False literal should be emitted"
        );
    }

    #[test]
    fn test_flag_injection_toml_deserialization() {
        let toml_str = r#"
[scheduler]
next_fn = "LNext"
action_count = 1

[[scheduler.actions]]
spec_name = "LSendAnswer"
exec_name = "CSendAnswer"
kind = "message_driven"
message_variant = "Election"
flag_injections = [["msgs_election", "true"], ["msgs_election_sender", "sender"]]
"#;
        let config: crate::config::SchedulerTomlConfig = toml::from_str::<toml::Value>(toml_str)
            .unwrap()
            .get("scheduler")
            .unwrap()
            .clone()
            .try_into()
            .unwrap();

        assert_eq!(config.actions.len(), 1);
        let action = &config.actions[0];
        assert!(action.has_flag_injections());
        assert_eq!(action.flag_injections.len(), 2);
        assert_eq!(action.flag_injections[0], vec!["msgs_election", "true"]);
        assert_eq!(
            action.flag_injections[1],
            vec!["msgs_election_sender", "sender"]
        );
    }

    #[test]
    fn test_flag_injection_toml_default_empty() {
        let toml_str = r#"
[scheduler]
next_fn = "LNext"
action_count = 1

[[scheduler.actions]]
spec_name = "LSend1a"
exec_name = "CSend1a"
kind = "timer_driven"
"#;
        let config: crate::config::SchedulerTomlConfig = toml::from_str::<toml::Value>(toml_str)
            .unwrap()
            .get("scheduler")
            .unwrap()
            .clone()
            .try_into()
            .unwrap();

        let action = &config.actions[0];
        assert!(!action.has_flag_injections());
        assert!(action.flag_injections.is_empty());
    }

    #[test]
    fn test_flag_injection_with_role_dispatch() {
        // Flag injections work when combined with role dispatch
        let params = HostScaffoldParams {
            protocol_name: "RoleFlag".to_string(),
            module_name: "roleflag".to_string(),
            gen_module: "roleflag_gen".to_string(),
            message_enum: "RoleFlagMessage".to_string(),
            message_variants: vec![MessageVariant {
                name: "Election".to_string(),
                doc: String::new(),
                fields: vec![vec!["sender".to_string(), "u64".to_string()]],
            }],
            actions: vec![SchedulerActionConfig {
                spec_name: "LSendAnswer".to_string(),
                exec_name: "CSendAnswer".to_string(),
                kind: "message_driven".to_string(),
                message_variant: Some("Election".to_string()),
                existential_params: vec![],
                flag_injections: vec![
                    vec!["msgs_election".to_string(), "true".to_string()],
                    vec!["msgs_election_sender".to_string(), "sender".to_string()],
                ],
                guard_checks: vec![],
            }],
            role_dispatch: Some(RoleDispatchConfig {
                dispatch_style: "config_index".to_string(),
                dispatch_field: "config.my_index".to_string(),
                roles: vec![RoleConfig {
                    name: "node".to_string(),
                    condition: String::new(),
                    actions: vec!["CSendAnswer".to_string()],
                }],
            }),
        };
        let code = generate_host_scaffold(&params);
        // Handler still has flag injections
        assert!(code.contains("self.state.msgs_election = true;"));
        assert!(code.contains("self.state.msgs_election_sender = sender;"));
        // Role step method exists
        assert!(code.contains("fn node_step("));
    }

    // ---------------------------------------------------------------
    // Phase 17.4.4c: Guard check generation tests
    // ---------------------------------------------------------------

    #[test]
    fn test_guard_checks_basic_message_driven() {
        let params = HostScaffoldParams {
            protocol_name: "Guard".to_string(),
            module_name: "guard".to_string(),
            gen_module: "guard_gen".to_string(),
            message_enum: "GuardMessage".to_string(),
            message_variants: vec![MessageVariant {
                name: "Prepare".to_string(),
                doc: String::new(),
                fields: vec![vec!["ballot".to_string(), "u64".to_string()]],
            }],
            actions: vec![SchedulerActionConfig {
                spec_name: "LSend1b".to_string(),
                exec_name: "CSend1b".to_string(),
                kind: "message_driven".to_string(),
                message_variant: Some("Prepare".to_string()),
                existential_params: vec![],
                flag_injections: vec![],
                guard_checks: vec!["ballot >= self.state.promised_bal".to_string()],
            }],
            role_dispatch: None,
        };
        let code = generate_host_scaffold(&params);
        // Guard check should be an if-return block
        assert!(
            code.contains("if !(ballot >= self.state.promised_bal) {"),
            "Missing guard check condition"
        );
        assert!(
            code.contains("return StepResult { ok: true, outbound: GenericOutbound::None };"),
            "Missing guard check early return"
        );
        // The TODO comment should NOT appear when guards are configured
        assert!(
            !code.contains("// TODO: Add guard checks"),
            "TODO comment should be replaced by actual guards"
        );
    }

    #[test]
    fn test_guard_checks_basic_timer_driven() {
        let params = HostScaffoldParams {
            protocol_name: "Guard".to_string(),
            module_name: "guard".to_string(),
            gen_module: "guard_gen".to_string(),
            message_enum: "GuardMessage".to_string(),
            message_variants: vec![],
            actions: vec![SchedulerActionConfig {
                spec_name: "LSend1a".to_string(),
                exec_name: "CSend1a".to_string(),
                kind: "timer_driven".to_string(),
                message_variant: None,
                existential_params: vec![],
                flag_injections: vec![],
                guard_checks: vec!["matches!(self.state.phase, CPhase::Phase1)".to_string()],
            }],
            role_dispatch: None,
        };
        let code = generate_host_scaffold(&params);
        // Guard check in timer handler
        assert!(
            code.contains("if !(matches!(self.state.phase, CPhase::Phase1)) {"),
            "Missing guard check in timer handler"
        );
    }

    #[test]
    fn test_guard_checks_multiple() {
        let params = HostScaffoldParams {
            protocol_name: "MultiGuard".to_string(),
            module_name: "multiguard".to_string(),
            gen_module: "multiguard_gen".to_string(),
            message_enum: "MultiGuardMessage".to_string(),
            message_variants: vec![MessageVariant {
                name: "Promise".to_string(),
                doc: String::new(),
                fields: vec![
                    vec!["ballot".to_string(), "u64".to_string()],
                    vec!["acceptor".to_string(), "u64".to_string()],
                ],
            }],
            actions: vec![SchedulerActionConfig {
                spec_name: "LRecvPromise".to_string(),
                exec_name: "CRecvPromise".to_string(),
                kind: "message_driven".to_string(),
                message_variant: Some("Promise".to_string()),
                existential_params: vec![],
                flag_injections: vec![],
                guard_checks: vec![
                    "matches!(self.state.phase, CPhase::Phase1)".to_string(),
                    "!self.state.promises_rcvd.contains(&acceptor)".to_string(),
                ],
            }],
            role_dispatch: None,
        };
        let code = generate_host_scaffold(&params);
        // Both guard checks emitted
        assert!(code.contains("if !(matches!(self.state.phase, CPhase::Phase1))"));
        assert!(code.contains("if !(!self.state.promises_rcvd.contains(&acceptor))"));
    }

    #[test]
    fn test_guard_checks_empty_backwards_compat() {
        // When guard_checks is empty, TODO comment should appear
        let params = HostScaffoldParams {
            protocol_name: "NoGuard".to_string(),
            module_name: "noguard".to_string(),
            gen_module: "noguard_gen".to_string(),
            message_enum: "NoGuardMessage".to_string(),
            message_variants: vec![MessageVariant {
                name: "Ping".to_string(),
                doc: String::new(),
                fields: vec![],
            }],
            actions: vec![SchedulerActionConfig {
                spec_name: "LHandlePing".to_string(),
                exec_name: "CHandlePing".to_string(),
                kind: "message_driven".to_string(),
                message_variant: Some("Ping".to_string()),
                existential_params: vec![],
                flag_injections: vec![],
                guard_checks: vec![],
            }],
            role_dispatch: None,
        };
        let code = generate_host_scaffold(&params);
        // Should have TODO comment when no guards configured
        assert!(
            code.contains("// TODO: Add guard checks (spec preconditions)"),
            "Empty guards should show TODO comment"
        );
    }

    #[test]
    fn test_guard_checks_with_flag_injections() {
        // Guards should appear after flag injections
        let params = HostScaffoldParams {
            protocol_name: "FlagGuard".to_string(),
            module_name: "flagguard".to_string(),
            gen_module: "flagguard_gen".to_string(),
            message_enum: "FlagGuardMessage".to_string(),
            message_variants: vec![MessageVariant {
                name: "Election".to_string(),
                doc: String::new(),
                fields: vec![vec!["sender".to_string(), "u64".to_string()]],
            }],
            actions: vec![SchedulerActionConfig {
                spec_name: "LSendAnswer".to_string(),
                exec_name: "CSendAnswer".to_string(),
                kind: "message_driven".to_string(),
                message_variant: Some("Election".to_string()),
                existential_params: vec![],
                flag_injections: vec![
                    vec!["msgs_election".to_string(), "true".to_string()],
                    vec!["msgs_election_sender".to_string(), "sender".to_string()],
                ],
                guard_checks: vec!["self.state.my_id > self.state.msgs_election_sender".to_string()],
            }],
            role_dispatch: None,
        };
        let code = generate_host_scaffold(&params);
        // Both flag injections and guard checks present
        assert!(code.contains("self.state.msgs_election = true;"));
        assert!(code.contains("self.state.msgs_election_sender = sender;"));
        assert!(code.contains("if !(self.state.my_id > self.state.msgs_election_sender)"));
        // Flag injection appears before guard check
        let flag_pos = code.find("self.state.msgs_election = true;").unwrap();
        let guard_pos = code
            .find("if !(self.state.my_id > self.state.msgs_election_sender)")
            .unwrap();
        assert!(
            flag_pos < guard_pos,
            "Flag injection should appear before guard check"
        );
    }

    #[test]
    fn test_guard_checks_toml_deserialization() {
        let toml_str = r#"
[scheduler]
next_fn = "LNext"
action_count = 1

[[scheduler.actions]]
spec_name = "LSend1b"
exec_name = "CSend1b"
kind = "message_driven"
message_variant = "Prepare"
guard_checks = [
    "ballot >= self.state.promised_bal",
    "matches!(self.state.phase, CPhase::Phase1)",
]
"#;
        let config: crate::config::SchedulerTomlConfig = toml::from_str::<toml::Value>(toml_str)
            .unwrap()
            .get("scheduler")
            .unwrap()
            .clone()
            .try_into()
            .unwrap();

        let action = &config.actions[0];
        assert!(action.has_guard_checks());
        assert_eq!(action.guard_checks.len(), 2);
        assert_eq!(action.guard_checks[0], "ballot >= self.state.promised_bal");
        assert_eq!(
            action.guard_checks[1],
            "matches!(self.state.phase, CPhase::Phase1)"
        );
    }

    #[test]
    fn test_guard_checks_toml_default_empty() {
        let toml_str = r#"
[scheduler]
next_fn = "LNext"
action_count = 1

[[scheduler.actions]]
spec_name = "LSend1a"
exec_name = "CSend1a"
kind = "timer_driven"
"#;
        let config: crate::config::SchedulerTomlConfig = toml::from_str::<toml::Value>(toml_str)
            .unwrap()
            .get("scheduler")
            .unwrap()
            .clone()
            .try_into()
            .unwrap();

        let action = &config.actions[0];
        assert!(!action.has_guard_checks());
        assert!(action.guard_checks.is_empty());
    }
}
