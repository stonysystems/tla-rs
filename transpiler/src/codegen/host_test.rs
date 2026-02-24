//! Host init test program generation.
//!
//! Generates standalone Rust programs that test ProtocolHost::init() and
//! a single next(None) step for each protocol. The programs are compiled
//! with rustc and executed as part of integration tests.
//!
//! The approach: strip Verus-specific syntax from types_gen.rs and gen.rs,
//! combine with message code and host code into a self-contained program.

use std::path::Path;

/// Parameters for generating a host init test program.
pub struct HostTestParams {
    /// Protocol name in PascalCase (e.g., "Paxos")
    pub protocol_name: String,
    /// Contents of the types_gen.rs file
    pub types_gen_code: String,
    /// Contents of the protocol_gen.rs file (contains CInit + all gen fns)
    pub gen_code: String,
    /// Generated message code (from generate_message_code)
    pub message_code: String,
    /// Contents of the host.rs file
    pub host_code: String,
    /// The gen module name (e.g., "paxos_gen")
    pub gen_module: String,
}

/// Generate a standalone Rust test program for host init + single step.
pub fn generate_host_init_test_program(params: &HostTestParams) -> String {
    let mut out = String::new();

    // Standard imports
    out.push_str("#![allow(unused, dead_code, non_snake_case, non_camel_case_types)]\n");
    out.push_str("use std::collections::{HashSet, HashMap};\n\n");

    // Framework stubs
    out.push_str(&generate_framework_stubs());

    // Stripped types from types_gen.rs
    let types = strip_verus_types(&params.types_gen_code);
    out.push_str("// --- Protocol types ---\n");
    out.push_str(&types);
    out.push('\n');

    // All generated functions stripped from gen.rs
    // Skip functions already defined in types_gen to avoid duplicates
    let types_fns = collect_function_names(&types);
    let gen_fns = strip_verus_gen(&params.gen_code, &types_fns);
    out.push_str("// --- Generated functions ---\n");
    out.push_str(&gen_fns);
    out.push('\n');

    // Message enum (strip crate imports)
    let msg = strip_message_imports(&params.message_code);
    out.push_str("// --- Message enum ---\n");
    out.push_str(&msg);
    out.push('\n');

    // Host code (fix imports)
    let host = fixup_host_imports(&params.host_code, &params.gen_module, &params.protocol_name);
    out.push_str("// --- Host ---\n");
    out.push_str(&host);
    out.push('\n');

    // Test main
    out.push_str(&generate_test_main(&params.protocol_name));

    out
}

/// Generate minimal framework type stubs for standalone compilation.
fn generate_framework_stubs() -> String {
    r#"// --- Framework stubs ---
#[derive(Clone)]
pub struct EndPoint { pub id: Vec<u8> }
impl EndPoint {
    pub fn clone_up_to_view(&self) -> Self { EndPoint { id: self.id.clone() } }
}
type Arg = Vec<u8>;
type Args = Vec<Arg>;

pub struct GenericPacket<M> { pub dst: EndPoint, pub src: EndPoint, pub msg: M }

pub enum GenericOutbound<M> {
    Send { dst: EndPoint, msg: M },
    Broadcast { dsts: Vec<EndPoint>, msg: M },
    Sequence { packets: Vec<GenericPacket<M>> },
    None,
}

pub struct StepResult<M> { pub ok: bool, pub outbound: GenericOutbound<M> }

pub trait ProtocolMessage: Sized {
    fn serialize_to_bytes(&self, buf: &mut Vec<u8>);
    fn deserialize_from_bytes(data: &Vec<u8>) -> Option<Self>;
}

pub trait ProtocolConfig: Sized {
    fn parse_config(me: &EndPoint, args: &Args) -> Option<Self>;
    fn get_peers(&self) -> &Vec<EndPoint>;
}

pub trait ProtocolHost: Sized {
    type Msg: ProtocolMessage;
    type Cfg: ProtocolConfig;
    fn init(config: &Self::Cfg) -> Option<Self>;
    fn next(&mut self, config: &Self::Cfg, packet: Option<GenericPacket<Self::Msg>>) -> StepResult<Self::Msg>;
}

"#
    .to_string()
}

/// Strip Verus-specific syntax from types_gen.rs content.
///
/// Removes: verus!{} wrapper, impl View, spec fn valid, #[verifier] Clone impls,
/// use vstd/crate::protocol imports. Replaces external_body Clone with #[derive(Clone)].
pub fn strip_verus_types(code: &str) -> String {
    let mut result = String::new();
    let lines: Vec<&str> = code.lines().collect();
    let mut i = 0;
    let len = lines.len();

    // First pass: find which structs have external_body Clone impls
    let mut needs_derive_clone: Vec<String> = Vec::new();
    {
        let mut j = 0;
        while j < len {
            let trimmed = lines[j].trim();
            if trimmed.starts_with("impl Clone for ") && trimmed.contains('{') {
                let has_external = (j + 1 < len)
                    && lines[j + 1]
                        .trim()
                        .starts_with("#[verifier(external_body)]");
                if has_external {
                    if let Some(name) = extract_struct_name_from_clone_impl(trimmed) {
                        needs_derive_clone.push(name);
                    }
                }
            }
            j += 1;
        }
    }

    while i < len {
        let line = lines[i];
        let trimmed = line.trim();

        // Skip Verus imports and wrappers
        if trimmed.starts_with("use vstd::")
            || trimmed.starts_with("use crate::protocol::")
            || trimmed.starts_with("use crate::generated::")
            || trimmed.starts_with("use crate::implementation::")
            || trimmed.starts_with("use std::collections::")
            || trimmed == "verus! {"
            || trimmed == "} // verus!"
            || (trimmed.starts_with("//")
                && (trimmed.contains("Auto-generated") || trimmed.contains("DO NOT EDIT")))
        {
            i += 1;
            continue;
        }

        // Skip `impl View for ...` blocks
        if trimmed.starts_with("impl View for ") {
            i = skip_brace_block(&lines, i);
            continue;
        }

        // Skip `pub open spec fn valid(...)` inside impl blocks
        if trimmed.contains("pub open spec fn valid") {
            i = skip_brace_block(&lines, i);
            continue;
        }

        // Skip standalone spec/proof fn blocks
        if trimmed.starts_with("pub open spec fn")
            || trimmed.starts_with("proof fn")
            || trimmed.starts_with("pub proof fn")
        {
            i = skip_brace_block(&lines, i);
            continue;
        }

        // Detect external_body Clone impl and skip it
        if trimmed.starts_with("impl Clone for ") && trimmed.contains('{') {
            let has_external = (i + 1 < len)
                && lines[i + 1]
                    .trim()
                    .starts_with("#[verifier(external_body)]");
            if has_external {
                i = skip_brace_block(&lines, i);
                continue;
            }
        }

        // Skip standalone #[verifier(...)] annotations
        if trimmed.starts_with("#[verifier(") || trimmed.starts_with("#[verifier::") {
            i += 1;
            continue;
        }

        // Skip CState/CConstants impl blocks with only spec fns
        if trimmed.starts_with("impl C")
            && trimmed.contains('{')
            && !trimmed.contains("Clone")
            && impl_block_is_spec_only(&lines, i)
        {
            i = skip_brace_block(&lines, i);
            continue;
        }

        // Handle exec fn in types_gen (manual_code helpers like Cu64_inc)
        if trimmed.starts_with("pub exec fn ") {
            let sig = trimmed.replace("pub exec fn ", "pub fn ");
            let sig = strip_verus_return_type(&sig);
            result.push_str(&sig);
            result.push('\n');
            i += 1;
            // Skip requires/ensures until body {
            i = skip_requires_ensures(&lines, i);
            // Emit body
            i = emit_function_body(&lines, i, &mut result);
            continue;
        }

        // Add #[derive(Clone)] before struct definitions that had external_body Clone
        if trimmed.starts_with("pub struct ") || trimmed.starts_with("pub enum ") {
            let name = extract_type_name(trimmed);
            if let Some(ref n) = name {
                if needs_derive_clone.contains(n) {
                    result.push_str("#[derive(Clone)]\n");
                }
            }
        }

        result.push_str(line);
        result.push('\n');
        i += 1;
    }

    result
}

/// Collect function names from stripped code (e.g., "pub fn Cu64_inc" → "Cu64_inc").
fn collect_function_names(code: &str) -> Vec<String> {
    let mut names = Vec::new();
    for line in code.lines() {
        let trimmed = line.trim();
        if let Some(rest) = trimmed
            .strip_prefix("pub fn ")
            .or_else(|| trimmed.strip_prefix("fn "))
        {
            if let Some(name) = rest.split('(').next() {
                let name = name.split('<').next().unwrap_or(name).trim();
                if !name.is_empty() {
                    names.push(name.to_string());
                }
            }
        }
    }
    names
}

/// Strip Verus-specific syntax from a gen.rs file, keeping all exec functions.
///
/// Removes: verus!{} wrapper, imports, proof fn blocks, requires/ensures clauses,
/// proof {} blocks inside function bodies, #[verifier] annotations.
/// Converts: `pub exec fn` → `pub fn`, fixes return types.
/// Replaces: clone_hashset(&x) → x.clone()
/// Emits a plain clone_hashset stub for standalone compilation.
/// `skip_fns`: names of functions already defined elsewhere (to avoid duplicates).
pub fn strip_verus_gen(code: &str, skip_fns: &[String]) -> String {
    let mut result = String::new();
    let lines: Vec<&str> = code.lines().collect();
    let len = lines.len();

    // Emit a plain clone_hashset helper so generated code compiles
    result.push_str("fn clone_hashset<K: std::hash::Hash + Eq + Clone>(s: &HashSet<K>) -> HashSet<K> { s.clone() }\n");
    // Only emit clone_log if the gen code actually uses it
    if code.contains("clone_log(") || code.contains("fn clone_log") {
        result.push_str("fn clone_log(v: &Vec<CLogEntry>) -> Vec<CLogEntry> where CLogEntry: Clone { v.clone() }\n");
    }
    // Emit u64 helper stubs if the gen code calls them (Raft protocol)
    if code.contains("Cu64_inc(") && !code.contains("fn Cu64_inc") {
        result.push_str("fn Cu64_inc(x: &u64) -> u64 { *x + 1 }\n");
    }
    if code.contains("Cu64_dec(") && !code.contains("fn Cu64_dec") {
        result.push_str("fn Cu64_dec(x: &u64) -> u64 { *x - 1 }\n");
    }
    result.push('\n');

    let mut i = 0;
    while i < len {
        let trimmed = lines[i].trim();

        // Skip imports, verus wrapper, auto-generated comments
        if trimmed.starts_with("use crate::")
            || trimmed.starts_with("use vstd::")
            || trimmed.starts_with("use std::collections::")
            || trimmed == "verus! {"
            || trimmed == "} // verus!"
            || (trimmed.starts_with("//")
                && (trimmed.contains("Auto-generated") || trimmed.contains("DO NOT EDIT")))
        {
            i += 1;
            continue;
        }

        // Skip #[verifier(...)] annotations
        if trimmed.starts_with("#[verifier(") || trimmed.starts_with("#[verifier::") {
            i += 1;
            continue;
        }

        // Skip proof fn blocks entirely (lemma_empty_set_map, etc.)
        if trimmed.starts_with("proof fn ") || trimmed.starts_with("pub proof fn ") {
            i = skip_brace_block(&lines, i);
            continue;
        }

        // Skip #[verifier(external_body)] clone_hashset/clone_log definitions
        // (we emit our own stubs above)
        if is_external_body_helper(&lines, i) {
            i = skip_brace_block_from_fn(&lines, i);
            continue;
        }

        // Handle exec function signatures: strip `exec` keyword, fix return type
        if trimmed.starts_with("pub exec fn ") {
            // Extract function name to check for duplicates
            let fn_name = trimmed
                .strip_prefix("pub exec fn ")
                .and_then(|r| r.split('(').next())
                .unwrap_or("");
            if skip_fns.iter().any(|n| n == fn_name) {
                // Skip this function entirely — already defined in types
                // Skip past signature, requires/ensures, and body
                i += 1;
                i = skip_requires_ensures(&lines, i);
                if i < len {
                    i = skip_brace_block(&lines, i);
                }
                continue;
            }
            let sig = trimmed.replace("pub exec fn ", "pub fn ");
            let sig = strip_verus_return_type(&sig);
            result.push_str(&sig);
            result.push('\n');
            i += 1;
            // Skip requires/ensures until we hit the body opening brace
            i = skip_requires_ensures(&lines, i);
            // Now emit the body
            i = emit_function_body(&lines, i, &mut result);
            continue;
        }

        // Handle helper function signatures (clone_phase, clone_role, etc.)
        // Skip clone_hashset and clone_log — we emit our own stubs above
        if trimmed.starts_with("fn clone_hashset") || trimmed.starts_with("fn clone_log") {
            // Skip to end of function body
            let mut j = i + 1;
            while j < len && !lines[j].trim().starts_with('{') {
                j += 1;
            }
            if j < len {
                i = skip_brace_block(&lines, j);
            } else {
                i += 1;
            }
            continue;
        }

        // These are `fn foo(...)` without `pub exec` or `proof`
        if (trimmed.starts_with("fn ") || trimmed.starts_with("pub fn "))
            && !trimmed.starts_with("fn main")
            && trimmed.contains("->")
        {
            let sig = strip_verus_return_type(trimmed);
            result.push_str(&sig);
            result.push('\n');
            i += 1;
            // Skip requires/ensures
            i = skip_requires_ensures(&lines, i);
            // Emit body
            i = emit_function_body(&lines, i, &mut result);
            continue;
        }

        // Pass through other lines (comments, blank lines)
        result.push_str(lines[i]);
        result.push('\n');
        i += 1;
    }

    result
}

/// Check if line i starts a `#[verifier(external_body)]` helper function definition
/// (clone_hashset, clone_log). Pattern:
///   #[verifier(external_body)]
///   fn clone_hashset<...>(...) -> ...
/// or the annotation is on the preceding line.
fn is_external_body_helper(lines: &[&str], i: usize) -> bool {
    let trimmed = lines[i].trim();
    // Pattern 1: current line is #[verifier(external_body)], next line is fn
    if trimmed.starts_with("#[verifier(external_body)]") && i + 1 < lines.len() {
        let next = lines[i + 1].trim();
        if next.starts_with("fn clone_hashset") || next.starts_with("fn clone_log") {
            return true;
        }
    }
    false
}

/// Skip past requires/ensures clauses to find the opening `{` of a function body.
/// Returns the index of the line containing the opening `{`.
///
/// Strategy: The function body `{` is the first `{` at paren depth 0
/// that starts a line (possibly preceded only by whitespace).
/// Requires/ensures clauses may contain `({...})` blocks but those
/// have the `{` inside parentheses (paren_depth > 0).
fn skip_requires_ensures(lines: &[&str], mut i: usize) -> usize {
    let mut paren_depth: i32 = 0;
    while i < lines.len() {
        let trimmed = lines[i].trim();

        // Check if this line starts the body: a `{` at paren_depth 0
        // The body `{` is typically at the start of a line (possibly after CState)
        if paren_depth == 0 && trimmed.starts_with('{') {
            return i;
        }
        // Also handle: the body starts with the struct name like `CState {`
        if paren_depth == 0
            && !trimmed.starts_with("requires")
            && !trimmed.starts_with("ensures")
            && !trimmed.starts_with("//")
            && !trimmed.is_empty()
        {
            // Check if this looks like the start of a body expression
            // (not a spec continuation)
            if !trimmed.contains("@")
                && !trimmed.contains("=~=")
                && !trimmed.starts_with("*")
                && !trimmed.starts_with("!")
                && !trimmed.starts_with("(")
                && !trimmed.starts_with("||")
                && !trimmed.starts_with("&&")
                && !trimmed.ends_with(',')
                && trimmed.contains('{')
            {
                return i;
            }
        }

        // Track paren depth for spec expressions like `({ ... })`
        for c in trimmed.chars() {
            if c == '(' {
                paren_depth += 1;
            }
            if c == ')' {
                paren_depth -= 1;
            }
        }

        i += 1;
    }
    i
}

/// Emit a function body starting at line `i` (which should contain the opening `{`).
/// Strips `proof { ... }` blocks inside. Returns the index after the closing `}`.
fn emit_function_body(lines: &[&str], start: usize, result: &mut String) -> usize {
    if start >= lines.len() {
        return start;
    }

    let mut depth: i32 = 0;
    let mut i = start;
    let mut in_proof = false;
    let mut proof_depth: i32 = 0;

    while i < lines.len() {
        let trimmed = lines[i].trim();

        // Detect proof block start
        if !in_proof && (trimmed == "proof {" || trimmed.starts_with("proof {")) {
            in_proof = true;
            proof_depth = 0;
            for c in trimmed.chars() {
                if c == '{' {
                    proof_depth += 1;
                }
                if c == '}' {
                    proof_depth -= 1;
                }
            }
            // Still count toward overall depth
            for c in trimmed.chars() {
                if c == '{' {
                    depth += 1;
                }
                if c == '}' {
                    depth -= 1;
                }
            }
            i += 1;
            if proof_depth <= 0 {
                in_proof = false;
            }
            continue;
        }

        if in_proof {
            for c in trimmed.chars() {
                if c == '{' {
                    proof_depth += 1;
                    depth += 1;
                }
                if c == '}' {
                    proof_depth -= 1;
                    depth -= 1;
                }
            }
            i += 1;
            if proof_depth <= 0 {
                in_proof = false;
            }
            continue;
        }

        // Count braces
        for c in trimmed.chars() {
            if c == '{' {
                depth += 1;
            }
            if c == '}' {
                depth -= 1;
            }
        }

        result.push_str(lines[i]);
        result.push('\n');
        i += 1;

        if depth <= 0 {
            return i;
        }
    }
    i
}

/// Skip past an `#[verifier(external_body)]` annotation + the function it annotates.
/// Starts at the annotation line, finds and skips the function body.
fn skip_brace_block_from_fn(lines: &[&str], i: usize) -> usize {
    // Skip the annotation line(s), then find the fn and skip its body
    let mut j = i;
    // Skip annotation
    while j < lines.len() {
        let trimmed = lines[j].trim();
        j += 1;
        if trimmed.starts_with("fn ")
            || trimmed.starts_with("pub fn ")
            || trimmed.starts_with("pub exec fn ")
        {
            // Now skip requires/ensures and body
            while j < lines.len() {
                let t = lines[j].trim();
                if t.contains('{') {
                    // Found body start - skip to matching close
                    return skip_brace_block(lines, j);
                }
                j += 1;
            }
            return j;
        }
    }
    j
}

/// Strip message code imports for standalone compilation.
fn strip_message_imports(code: &str) -> String {
    code.lines()
        .filter(|line| !line.starts_with("use crate::") && !line.starts_with("//!"))
        .collect::<Vec<_>>()
        .join("\n")
}

/// Fix host.rs imports for standalone compilation.
pub fn fixup_host_imports(host_code: &str, gen_module: &str, _protocol: &str) -> String {
    let qualified_prefix = format!("{}::", gen_module);
    host_code
        .lines()
        .filter(|line| {
            let trimmed = line.trim();
            !trimmed.starts_with("use crate::") && !trimmed.starts_with("use std::collections::")
        })
        .map(|line| {
            // Convert inner doc comments to regular comments
            let line = if line.trim_start().starts_with("//!") {
                line.replacen("//!", "//", 1)
            } else {
                line.to_string()
            };
            line.replace(&qualified_prefix, "")
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// Generate protocol-specific test main() function.
fn generate_test_main(protocol: &str) -> String {
    let constants_code = generate_constants_construction(protocol);
    let config_code = generate_config_construction(protocol);
    let assertions = generate_init_assertions(protocol);

    format!(
        r#"
fn main() {{
    // 1. Construct constants
{constants_code}

    // 2. Build config
{config_code}

    // 3. Test host init
    let host = <{host_type} as ProtocolHost>::init(&config);
    assert!(host.is_some(), "{protocol}: init() should return Some");
    let mut host = host.unwrap();
{assertions}

    // 4. Test single step (timeout, no message)
    let result = host.next(&config, None);
    assert!(result.ok, "{protocol}: next(None) should return ok=true");

    println!("All host tests passed for {protocol}");
}}
"#,
        constants_code = constants_code,
        config_code = config_code,
        host_type = host_type_name(protocol),
        protocol = protocol,
        assertions = assertions,
    )
}

fn generate_constants_construction(protocol: &str) -> String {
    match protocol {
        "TwoPhase" => {
            "    let mut rm = HashSet::new();\n    rm.insert(1u64);\n    rm.insert(2u64);\n    let constants = CConstants { rm };".to_string()
        }
        "Paxos" => {
            "    let mut acceptors = HashSet::new();\n    for i in 0..3u64 { acceptors.insert(i); }\n    let constants = CConstants { acceptors, quorum_size: 2, node_id: 0 };".to_string()
        }
        "LeaderElection" => {
            "    let mut nodes = HashSet::new();\n    for i in 0..3u64 { nodes.insert(i); }\n    let constants = CConstants { nodes, num_nodes: 3 };".to_string()
        }
        "Raft" => {
            "    let mut servers = HashSet::new();\n    for i in 0..3u64 { servers.insert(i); }\n    let constants = CConstants { servers, quorum_size: 2, my_id: 0 };".to_string()
        }
        "ChainReplication" => {
            "    let constants = CConstants { node_id: 1, chain_len: 3 };".to_string()
        }
        "PrimaryBackup" => {
            "    let constants = CConstants { max_log_len: 1_000_000 };".to_string()
        }
        "PBFT" => {
            "    let constants = CConstants { f: 1, n: 4, node_id: 0, checkpoint_interval: 10 };".to_string()
        }
        "VerticalPaxos" => {
            "    let constants = CConstants { quorum_size: 2, num_nodes: 3, node_id: 0 };".to_string()
        }
        "EPaxos" => {
            "    let constants = CConstants { num_replicas: 3, fast_quorum_size: 2, quorum_size: 2, my_id: 0 };".to_string()
        }
        _ => "    let constants = CConstants::default();".to_string(),
    }
}

/// Get the host type name for a protocol.
fn host_type_name(protocol: &str) -> String {
    match protocol {
        "ChainReplication" => "ChainHost".to_string(),
        _ => format!("{}Host", protocol),
    }
}

/// Get the config type name for a protocol.
fn config_type_name(protocol: &str) -> String {
    match protocol {
        "ChainReplication" => "ChainConfig".to_string(),
        _ => format!("{}Config", protocol),
    }
}

fn generate_config_construction(protocol: &str) -> String {
    let config_type = config_type_name(protocol);
    let mut out = String::new();
    out.push_str("    let ep0 = EndPoint { id: b\"node0\".to_vec() };\n");
    out.push_str("    let ep1 = EndPoint { id: b\"node1\".to_vec() };\n");
    out.push_str("    let ep2 = EndPoint { id: b\"node2\".to_vec() };\n");
    out.push_str(&format!("    let config = {} {{\n", config_type));
    out.push_str("        peers: vec![ep0, ep1, ep2],\n");
    out.push_str("        my_index: 0,\n");
    out.push_str("        constants,\n");
    out.push_str("    };");
    out
}

fn generate_init_assertions(protocol: &str) -> String {
    match protocol {
        "Paxos" => "    assert!(matches!(host.state.phase, CPhase::Idle), \"Paxos: initial phase should be Idle\");".to_string(),
        "TwoPhase" => "    assert!(matches!(host.state.tm_state, CTMState::Init), \"TwoPhase: initial tm_state should be Init\");".to_string(),
        "LeaderElection" => "    assert!(!host.state.has_leader, \"LeaderElection: should have no leader initially\");".to_string(),
        "Raft" => "    assert!(matches!(host.state.role, CServerRole::Follower), \"Raft: initial role should be Follower\");".to_string(),
        "ChainReplication" => "    assert!(host.state.alive, \"ChainReplication: node should be alive initially\");".to_string(),
        "PrimaryBackup" => "    assert!(matches!(host.state.role, CNodeRole::Primary), \"PrimaryBackup: initial role should be Primary\");".to_string(),
        "PBFT" => "    assert!(matches!(host.state.phase, CPhase::PrePrepare), \"PBFT: initial phase should be PrePrepare\");".to_string(),
        "VerticalPaxos" => "    assert!(host.state.is_active, \"VerticalPaxos: node should be active initially\");".to_string(),
        "EPaxos" => "    assert!(matches!(host.state.phase, CInstancePhase::Empty), \"EPaxos: initial phase should be Empty\");".to_string(),
        _ => String::new(),
    }
}

// --- Helper functions ---

/// Skip a brace-delimited block starting at line `start`.
/// Returns the line index after the closing brace.
/// If the opening brace is not on `start`, scans forward to find it first.
fn skip_brace_block(lines: &[&str], start: usize) -> usize {
    let mut depth: i32 = 0;
    let mut i = start;
    let mut found_brace = false;
    while i < lines.len() {
        let opens = lines[i].matches('{').count() as i32;
        let closes = lines[i].matches('}').count() as i32;
        depth += opens;
        depth -= closes;
        if opens > 0 {
            found_brace = true;
        }
        i += 1;
        if found_brace && depth <= 0 {
            return i;
        }
    }
    i
}

/// Extract struct name from "impl Clone for CState {"
fn extract_struct_name_from_clone_impl(line: &str) -> Option<String> {
    let trimmed = line.trim();
    if let Some(after) = trimmed.strip_prefix("impl Clone for ") {
        let name = after.split_whitespace().next()?;
        Some(name.to_string())
    } else {
        None
    }
}

/// Extract type name from "pub struct CState {" or "pub enum CPhase {"
fn extract_type_name(line: &str) -> Option<String> {
    let trimmed = line.trim();
    let rest = trimmed
        .strip_prefix("pub struct ")
        .or_else(|| trimmed.strip_prefix("pub enum "))?;
    let name = rest.split(['{', ' ']).next()?;
    Some(name.trim().to_string())
}

/// Check if an impl block contains only spec functions.
fn impl_block_is_spec_only(lines: &[&str], start: usize) -> bool {
    let end = skip_brace_block(lines, start);
    for line in &lines[start..end] {
        let trimmed = line.trim();
        if trimmed.contains("pub open spec fn") || trimmed.contains("open spec fn") {
            return true;
        }
        if (trimmed.starts_with("pub fn ") || trimmed.starts_with("fn "))
            && !trimmed.contains("spec fn")
        {
            return false;
        }
    }
    true
}

/// Strip Verus return-type syntax: "(result: CState)" -> "-> CState"
fn strip_verus_return_type(sig: &str) -> String {
    // Pattern: fn CInit(c: &CConstants) -> (result: CState)
    // Want:    fn CInit(c: &CConstants) -> CState
    if let Some(pos) = sig.find("-> (") {
        if let Some(close) = sig[pos..].find(')') {
            let return_part = &sig[pos + 4..pos + close];
            // return_part is "result: CState"
            if let Some(colon) = return_part.find(':') {
                let type_name = return_part[colon + 1..].trim();
                return format!("{}-> {}{}", &sig[..pos], type_name, &sig[pos + close + 1..]);
            }
        }
    }
    sig.to_string()
}

/// Load protocol test parameters from file paths.
pub fn load_host_test_params(
    toml_path: &Path,
    protocol: &str,
    types_gen_path: &Path,
    gen_path: &Path,
    host_path: &Path,
) -> HostTestParams {
    let config = crate::config::TranspilerConfig::from_file(toml_path)
        .unwrap_or_else(|e| panic!("Failed to load {}: {}", toml_path.display(), e));

    let msg_config = config
        .messages
        .as_ref()
        .unwrap_or_else(|| panic!("No [messages] in {}", toml_path.display()));

    let message_code = crate::codegen::generate_message_code(msg_config);

    let types_gen_code = std::fs::read_to_string(types_gen_path)
        .unwrap_or_else(|e| panic!("Failed to read {}: {}", types_gen_path.display(), e));

    let gen_code = std::fs::read_to_string(gen_path)
        .unwrap_or_else(|e| panic!("Failed to read {}: {}", gen_path.display(), e));

    let host_code = std::fs::read_to_string(host_path)
        .unwrap_or_else(|e| panic!("Failed to read {}: {}", host_path.display(), e));

    // Derive gen_module from filename, not protocol name
    let gen_module = gen_path
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("unknown_gen")
        .to_string();

    HostTestParams {
        protocol_name: protocol.to_string(),
        types_gen_code,
        gen_code,
        message_code,
        host_code,
        gen_module,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_strip_verus_return_type() {
        assert_eq!(
            strip_verus_return_type("pub fn CInit(c: &CConstants) -> (result: CState)"),
            "pub fn CInit(c: &CConstants) -> CState"
        );
    }

    #[test]
    fn test_strip_verus_return_type_no_match() {
        let sig = "pub fn foo() -> CState";
        assert_eq!(strip_verus_return_type(sig), sig);
    }

    #[test]
    fn test_strip_verus_return_type_helper() {
        assert_eq!(
            strip_verus_return_type("fn clone_phase(r: &CPhase) -> (res: CPhase)"),
            "fn clone_phase(r: &CPhase) -> CPhase"
        );
    }

    #[test]
    fn test_extract_struct_name_from_clone() {
        assert_eq!(
            extract_struct_name_from_clone_impl("impl Clone for CState {"),
            Some("CState".to_string())
        );
    }

    #[test]
    fn test_extract_type_name() {
        assert_eq!(
            extract_type_name("pub struct CState {"),
            Some("CState".to_string())
        );
        assert_eq!(
            extract_type_name("pub enum CPhase {"),
            Some("CPhase".to_string())
        );
    }

    #[test]
    fn test_strip_verus_types_removes_view_impl() {
        let input = r#"verus! {

pub struct CState {
    pub x: u64,
}

impl View for CState {
    type V = LState;
    open spec fn view(&self) -> LState {
        LState { x: self.x as int }
    }
}

} // verus!
"#;
        let result = strip_verus_types(input);
        assert!(result.contains("pub struct CState"));
        assert!(!result.contains("impl View"));
        assert!(!result.contains("verus!"));
    }

    #[test]
    fn test_strip_verus_types_replaces_clone() {
        let input = r#"verus! {

pub struct CState {
    pub x: u64,
}

impl Clone for CState {
    #[verifier(external_body)]
    fn clone(&self) -> (res: Self)
    ensures
        res@ == self@,
    { unimplemented!() }
}

} // verus!
"#;
        let result = strip_verus_types(input);
        assert!(result.contains("#[derive(Clone)]"));
        assert!(result.contains("pub struct CState"));
        assert!(!result.contains("external_body"));
    }

    #[test]
    fn test_generate_framework_stubs() {
        let stubs = generate_framework_stubs();
        assert!(stubs.contains("pub struct EndPoint"));
        assert!(stubs.contains("pub trait ProtocolHost"));
        assert!(stubs.contains("pub struct StepResult"));
    }

    #[test]
    fn test_strip_verus_gen_basic() {
        let input = r#"// Auto-generated by verus-transpiler
// DO NOT EDIT MANUALLY

use crate::generated::Foo::types_gen::*;
use crate::protocol::Foo::foo::*;
use vstd::prelude::*;

verus! {

/// Helper: clone CPhase preserving view.
fn clone_phase(r: &CPhase) -> (res: CPhase)
ensures
    res@ == r@,
{
    match r {
        CPhase::Idle => CPhase::Idle,
        CPhase::Active => CPhase::Active,
    }
}

pub exec fn CInit(c: &CConstants) -> (result: CState)
requires
    c.valid(),
ensures
    result.valid(),
    LInit(result@, c@),
{
    CState {
        phase: CPhase::Idle,
        value: 0u64,
    }
}

pub exec fn CDoThing(s: &CState, c: &CConstants) -> (result: CState)
requires
    s.valid(),
    c.valid(),
    s.phase is Idle,
ensures
    result.valid(),
    LDoThing(s@, result@, c@),
{
    CState {
        phase: CPhase::Active,
        value: s.value.clone(),
    }
}

} // verus!
"#;
        let result = strip_verus_gen(input, &[]);
        // Should contain both functions
        assert!(
            result.contains("pub fn CInit"),
            "Should have CInit: {}",
            result
        );
        assert!(
            result.contains("pub fn CDoThing"),
            "Should have CDoThing: {}",
            result
        );
        // Should contain helper
        assert!(
            result.contains("fn clone_phase"),
            "Should have clone_phase: {}",
            result
        );
        // Should not contain Verus syntax
        assert!(
            !result.contains("verus!"),
            "Should not have verus!: {}",
            result
        );
        assert!(
            !result.contains("requires"),
            "Should not have requires: {}",
            result
        );
        assert!(
            !result.contains("ensures"),
            "Should not have ensures: {}",
            result
        );
        assert!(
            !result.contains("exec fn"),
            "Should not have exec fn: {}",
            result
        );
        // Should contain the struct body
        assert!(
            result.contains("CPhase::Idle"),
            "Should have CPhase::Idle in body: {}",
            result
        );
    }

    #[test]
    fn test_strip_verus_gen_with_proof_block() {
        let input = r#"verus! {

proof fn lemma_empty_set_map()
ensures
    Set::<u64>::empty().map(|x: u64| x as int) =~= Set::<int>::empty(),
{
    let f = |x: u64| x as int;
}

#[verifier(external_body)]
fn clone_hashset<K: std::hash::Hash + Eq + Clone>(s: &HashSet<K>) -> (res: HashSet<K>)
ensures
    res@ == s@,
{
    s.clone()
}

pub exec fn CInit(c: &CConstants) -> (result: CState)
requires
    c.valid(),
ensures
    result.valid(),
    LInit(result@, c@),
{
    let result = CState { x: HashSet::new() };
    proof {
        lemma_empty_set_map();
    }
    result
}

} // verus!
"#;
        let result = strip_verus_gen(input, &[]);
        assert!(
            result.contains("pub fn CInit"),
            "Should have CInit: {}",
            result
        );
        assert!(
            !result.contains("lemma_empty_set_map"),
            "Should not have proof fn: {}",
            result
        );
        assert!(
            !result.contains("proof {"),
            "Should not have proof block: {}",
            result
        );
        assert!(
            result.contains("HashSet::new()"),
            "Should have body: {}",
            result
        );
        // Should have our clone_hashset stub
        assert!(
            result.contains("fn clone_hashset"),
            "Should have clone_hashset stub: {}",
            result
        );
    }

    // --- skip_requires_ensures tests ---

    #[test]
    fn test_skip_requires_ensures_simple() {
        let lines = vec![
            "requires",
            "    c.valid(),",
            "ensures",
            "    result.valid(),",
            "{",
        ];
        assert_eq!(skip_requires_ensures(&lines, 0), 4);
    }

    #[test]
    fn test_skip_requires_ensures_brace_at_start() {
        let lines = vec!["{", "    x", "}"];
        assert_eq!(skip_requires_ensures(&lines, 0), 0);
    }

    #[test]
    fn test_skip_requires_ensures_struct_body() {
        let lines = vec!["requires", "    s.valid(),", "CState {"];
        assert_eq!(skip_requires_ensures(&lines, 0), 2);
    }

    // --- emit_function_body tests ---

    #[test]
    fn test_emit_function_body_simple() {
        let lines = vec!["{", "    return 42;", "}"];
        let mut result = String::new();
        let end = emit_function_body(&lines, 0, &mut result);
        assert_eq!(end, 3);
        assert!(result.contains("return 42;"));
    }

    #[test]
    fn test_emit_function_body_strips_proof() {
        let lines = vec![
            "{",
            "    let x = 1;",
            "    proof {",
            "        lemma();",
            "    }",
            "    x",
            "}",
        ];
        let mut result = String::new();
        let end = emit_function_body(&lines, 0, &mut result);
        assert_eq!(end, 7);
        assert!(result.contains("let x = 1;"));
        assert!(!result.contains("lemma()"));
    }

    #[test]
    fn test_emit_function_body_nested_braces() {
        let lines = vec!["{", "    if true {", "        42", "    }", "}"];
        let mut result = String::new();
        let end = emit_function_body(&lines, 0, &mut result);
        assert_eq!(end, 5);
        assert!(result.contains("if true {"));
    }

    #[test]
    fn test_emit_function_body_empty() {
        let lines: Vec<&str> = vec![];
        let mut result = String::new();
        let end = emit_function_body(&lines, 0, &mut result);
        assert_eq!(end, 0);
    }

    // --- collect_function_names tests ---

    #[test]
    fn test_collect_function_names_multiple() {
        let code = "pub fn CInit(c: &CConstants) -> CState {\n}\nfn helper(x: u64) -> u64 {\n}";
        let names = collect_function_names(code);
        assert_eq!(names, vec!["CInit", "helper"]);
    }

    #[test]
    fn test_collect_function_names_generic() {
        let code =
            "fn clone_hashset<K: Hash + Eq + Clone>(s: &HashSet<K>) -> HashSet<K> { s.clone() }";
        let names = collect_function_names(code);
        assert_eq!(names, vec!["clone_hashset"]);
    }

    #[test]
    fn test_collect_function_names_no_fns() {
        let code = "let x = 5;\nstruct Foo {}";
        let names = collect_function_names(code);
        assert!(names.is_empty());
    }

    // --- extract_type_name tests ---

    #[test]
    fn test_extract_type_name_with_generics() {
        assert_eq!(
            extract_type_name("pub struct State<T> {"),
            Some("State<T>".to_string())
        );
    }

    #[test]
    fn test_extract_type_name_not_a_type() {
        assert_eq!(extract_type_name("let x = 5;"), None);
    }

    // --- extract_struct_name_from_clone_impl tests ---

    #[test]
    fn test_extract_clone_name_with_generic() {
        assert_eq!(
            extract_struct_name_from_clone_impl("impl Clone for Vec<T> {"),
            Some("Vec<T>".to_string())
        );
    }

    #[test]
    fn test_extract_clone_name_no_match() {
        assert_eq!(
            extract_struct_name_from_clone_impl("impl Display for Foo {"),
            None
        );
    }

    // --- skip_brace_block tests ---

    #[test]
    fn test_skip_brace_block_simple() {
        let lines = vec!["{", "  x", "}"];
        assert_eq!(skip_brace_block(&lines, 0), 3);
    }

    #[test]
    fn test_skip_brace_block_nested() {
        let lines = vec!["{", "  {", "    x", "  }", "}"];
        assert_eq!(skip_brace_block(&lines, 0), 5);
    }

    #[test]
    fn test_skip_brace_block_brace_on_later_line() {
        let lines = vec!["fn foo()", "-> u64", "{", "    42", "}"];
        assert_eq!(skip_brace_block(&lines, 0), 5);
    }

    // --- impl_block_is_spec_only tests ---

    #[test]
    fn test_impl_block_is_spec_only_true() {
        let lines = vec![
            "impl CState {",
            "    pub open spec fn view(&self) -> LState { }",
            "}",
        ];
        assert!(impl_block_is_spec_only(&lines, 0));
    }

    #[test]
    fn test_impl_block_is_spec_only_false() {
        let lines = vec![
            "impl CState {",
            "    pub fn helper(&self) -> u64 { 42 }",
            "}",
        ];
        assert!(!impl_block_is_spec_only(&lines, 0));
    }

    // --- is_external_body_helper tests ---

    #[test]
    fn test_is_external_body_helper_clone_hashset() {
        let lines = vec![
            "#[verifier(external_body)]",
            "fn clone_hashset<K>(s: &HashSet<K>) -> HashSet<K>",
        ];
        assert!(is_external_body_helper(&lines, 0));
    }

    #[test]
    fn test_is_external_body_helper_clone_log() {
        let lines = vec![
            "#[verifier(external_body)]",
            "fn clone_log(v: &Vec<CLogEntry>) -> Vec<CLogEntry>",
        ];
        assert!(is_external_body_helper(&lines, 0));
    }

    #[test]
    fn test_is_external_body_helper_other_fn() {
        let lines = vec!["#[verifier(external_body)]", "fn other_fn() -> u64"];
        assert!(!is_external_body_helper(&lines, 0));
    }

    #[test]
    fn test_is_external_body_helper_not_annotation() {
        let lines = vec!["fn clone_hashset<K>(s: &HashSet<K>) -> HashSet<K>"];
        assert!(!is_external_body_helper(&lines, 0));
    }

    // --- strip_verus_gen with skip_fns ---

    #[test]
    fn test_strip_verus_gen_skips_duplicate_fns() {
        let input = "verus! {\n\npub exec fn Cu64_inc(x: u64) -> (result: u64)\nrequires\n    x < u64::MAX,\nensures\n    result == x + 1,\n{\n    x + 1\n}\n\n} // verus!\n";
        let skip = vec!["Cu64_inc".to_string()];
        let result = strip_verus_gen(input, &skip);
        assert!(
            !result.contains("pub fn Cu64_inc"),
            "Should skip Cu64_inc: {}",
            result
        );
    }

    #[test]
    fn test_strip_verus_gen_keeps_non_skipped() {
        let input = "verus! {\n\npub exec fn CInit(c: &CConstants) -> (result: CState)\n{\n    CState {}\n}\n\npub exec fn CDoThing(s: &CState) -> (result: CState)\n{\n    CState {}\n}\n\n} // verus!\n";
        let skip = vec!["CDoThing".to_string()];
        let result = strip_verus_gen(input, &skip);
        assert!(result.contains("pub fn CInit"), "Should keep CInit");
        assert!(!result.contains("pub fn CDoThing"), "Should skip CDoThing");
    }

    #[test]
    fn test_strip_verus_gen_clone_log_only_when_used() {
        let input = "verus! {\n\npub exec fn CInit(c: &CConstants) -> (result: CState)\n{\n    CState {}\n}\n\n} // verus!\n";
        let result = strip_verus_gen(input, &[]);
        assert!(
            result.contains("fn clone_hashset"),
            "Always has clone_hashset stub"
        );
        assert!(
            !result.contains("fn clone_log"),
            "Should not have clone_log when not used"
        );
    }

    #[test]
    fn test_strip_verus_gen_clone_log_when_used() {
        let input = "verus! {\n\npub exec fn CInit(c: &CConstants) -> (result: CState)\n{\n    let log = clone_log(&old_log);\n    CState { log }\n}\n\n} // verus!\n";
        let result = strip_verus_gen(input, &[]);
        assert!(
            result.contains("fn clone_log"),
            "Should have clone_log when used"
        );
    }

    // --- strip_verus_types additional tests ---

    #[test]
    fn test_strip_verus_types_removes_spec_fn() {
        let input = "verus! {\n\npub struct CState {\n    pub x: u64,\n}\n\npub open spec fn valid_state(s: CState) -> bool {\n    s.x < 100\n}\n\n} // verus!\n";
        let result = strip_verus_types(input);
        assert!(result.contains("pub struct CState"));
        assert!(!result.contains("valid_state"));
    }

    // --- fixup_host_imports tests ---

    #[test]
    fn test_fixup_host_imports_strips_crate_imports() {
        let code = "use crate::generated::Foo::types_gen::*;\nuse std::collections::HashMap;\npub struct FooHost {}";
        let result = fixup_host_imports(code, "foo_gen", "Foo");
        assert!(!result.contains("use crate::"));
        assert!(!result.contains("use std::collections::"));
        assert!(result.contains("pub struct FooHost"));
    }

    #[test]
    fn test_fixup_host_imports_strips_qualified_prefix() {
        let code = "use foo_gen::CInit;\nlet x = foo_gen::CDoThing(&s);";
        let result = fixup_host_imports(code, "foo_gen", "Foo");
        assert!(result.contains("CDoThing(&s)"));
        assert!(!result.contains("foo_gen::CDoThing"));
    }

    #[test]
    fn test_fixup_host_imports_converts_inner_doc() {
        let code = "//! This is a host module.\npub struct Host {}";
        let result = fixup_host_imports(code, "gen", "Proto");
        assert!(result.contains("// This is a host module."));
        assert!(!result.contains("//!"));
    }

    // --- host_type_name / config_type_name tests ---

    #[test]
    fn test_host_type_name_chain_replication() {
        assert_eq!(host_type_name("ChainReplication"), "ChainHost");
    }

    #[test]
    fn test_host_type_name_default() {
        assert_eq!(host_type_name("Paxos"), "PaxosHost");
        assert_eq!(host_type_name("Raft"), "RaftHost");
    }

    #[test]
    fn test_config_type_name_chain_replication() {
        assert_eq!(config_type_name("ChainReplication"), "ChainConfig");
    }

    #[test]
    fn test_config_type_name_default() {
        assert_eq!(config_type_name("Paxos"), "PaxosConfig");
        assert_eq!(config_type_name("Raft"), "RaftConfig");
    }

    // --- strip_message_imports tests ---

    #[test]
    fn test_strip_message_imports_basic() {
        let code = "use crate::common::framework::protocol_trait::ProtocolMessage;\n//! Module doc.\npub enum TestMsg {}";
        let result = strip_message_imports(code);
        assert!(!result.contains("use crate::"));
        assert!(!result.contains("//!"));
        assert!(result.contains("pub enum TestMsg {}"));
    }
}
