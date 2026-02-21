use crate::error::{TranspileError, TranspileResult};
use crate::tla::{parse_module, TlaBinOp, TlaExpr, TlaModule, TlaOperator, TlaQuantBound};
use crate::verus2tla::TlaPrinter;
use std::collections::HashSet;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PacketProjectionMode {
    None,
    AppendSeq,
    ReplaceSeq,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct McWrapperOptions {
    pub init_operator: String,
    pub next_operator: String,
    pub wrapper_suffix: String,
    pub packet_projection: PacketProjectionMode,
    pub packet_var: String,
    pub invariants: Vec<String>,
}

impl Default for McWrapperOptions {
    fn default() -> Self {
        Self {
            init_operator: "Init".to_string(),
            next_operator: "Next".to_string(),
            wrapper_suffix: "_MC".to_string(),
            packet_projection: PacketProjectionMode::None,
            packet_var: "sent_packets".to_string(),
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
    if options.packet_var.trim().is_empty() {
        return Err(TranspileError::Config {
            message: "Packet variable name cannot be empty.".to_string(),
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
        next,
        options.packet_projection,
        &options.packet_var,
    )?;
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
    next_operator: &TlaOperator,
    packet_projection: PacketProjectionMode,
    packet_var: &str,
) -> TranspileResult<String> {
    let uses_packet_projection = packet_projection != PacketProjectionMode::None;
    let has_state_set = module.constants.iter().any(|c| c.name == "State");
    let has_constants_set = module.constants.iter().any(|c| c.name == "Constants");

    let mut out = String::new();
    out.push_str(&format!("---- MODULE {} ----\n", wrapper_module_name));
    out.push_str("\\* Auto-generated model-check wrapper for relational spec pattern.\n");
    out.push_str(&format!("\\* Source module: {}\n\n", module.name));
    out.push_str(&format!("EXTENDS {}\n\n", module.name));

    if uses_packet_projection {
        out.push_str("VARIABLE state, constants, msgs\n\n");
    } else {
        out.push_str("VARIABLE state, constants\n\n");
    }

    out.push_str("StateInit ==\n");
    if has_state_set {
        out.push_str("    /\\ state \\in State\n");
    }
    if has_constants_set {
        out.push_str("    /\\ constants \\in Constants\n");
    }
    out.push_str(&format!("    /\\ {}(state, constants)\n\n", init_operator));
    if uses_packet_projection {
        out.push_str("    /\\ msgs = <<>>\n\n");
    }

    let state_next = if uses_packet_projection {
        render_state_next_with_packet_projection(next_operator, packet_projection, packet_var)?
    } else {
        render_state_next_plain(next_operator.name.as_str(), has_state_set)
    };
    out.push_str(&state_next);
    out.push('\n');

    if uses_packet_projection {
        out.push_str("vars == <<state, constants, msgs>>\n\n");
    } else {
        out.push_str("vars == <<state, constants>>\n\n");
    }
    out.push_str("Spec == StateInit /\\ [][StateNext]_vars\n\n");
    out.push_str("====\n");

    Ok(out)
}

fn render_state_next_plain(next_operator: &str, has_state_set: bool) -> String {
    let state_quantifier = if has_state_set {
        "\\E state_ \\in State :"
    } else {
        "\\E state_ :"
    };
    let mut out = String::new();
    out.push_str("StateNext ==\n");
    out.push_str(&format!("    /\\ {}\n", state_quantifier));
    out.push_str(&format!(
        "        /\\ {}(state, state_, constants)\n",
        next_operator
    ));
    out.push_str("        /\\ state' = state_\n");
    out.push_str("    /\\ UNCHANGED constants\n");
    out
}

fn render_state_next_with_packet_projection(
    next_operator: &TlaOperator,
    packet_projection: PacketProjectionMode,
    packet_var: &str,
) -> TranspileResult<String> {
    let msg_update = match packet_projection {
        PacketProjectionMode::None => unreachable!("only called for packet projection modes"),
        PacketProjectionMode::AppendSeq => format!("msgs \\o {}", packet_var),
        PacketProjectionMode::ReplaceSeq => packet_var.to_string(),
    };

    let mut disjuncts = Vec::new();
    flatten_disjunction(&next_operator.body, &mut disjuncts);
    if disjuncts.is_empty() {
        return Err(TranspileError::Config {
            message: format!(
                "Cannot project packets from `{}`: no disjunctive branches discovered.",
                next_operator.name
            ),
        });
    }

    let printer = TlaPrinter::new();
    let mut out = String::new();
    out.push_str("StateNext ==\n");

    for disjunct in disjuncts {
        let mut vars = Vec::new();
        let body = peel_exists_chain(disjunct, &mut vars);
        if !vars.iter().any(|bound| bound.var == packet_var) {
            return Err(TranspileError::Config {
                message: format!(
                    "Cannot project packets from `{}`: branch does not bind `{}`.",
                    next_operator.name, packet_var
                ),
            });
        }

        let mut quant_vars = vec!["state_".to_string()];
        quant_vars.extend(
            vars.iter()
                .map(|bound| render_quant_bound(bound, &printer))
                .collect::<Vec<_>>(),
        );

        out.push_str("    \\/ \\E ");
        out.push_str(&quant_vars.join(", "));
        out.push_str(" :\n");
        append_conjunct(&mut out, &printer.print_expr(body, 0));
        out.push_str("        /\\ state' = state_\n");
        out.push_str(&format!("        /\\ msgs' = {}\n", msg_update));
        out.push_str("        /\\ UNCHANGED constants\n");
    }

    Ok(out)
}

fn flatten_disjunction<'a>(expr: &'a TlaExpr, out: &mut Vec<&'a TlaExpr>) {
    match expr {
        TlaExpr::BinOp {
            op: TlaBinOp::Or,
            left,
            right,
        } => {
            flatten_disjunction(left, out);
            flatten_disjunction(right, out);
        }
        _ => out.push(expr),
    }
}

fn peel_exists_chain<'a>(expr: &'a TlaExpr, vars: &mut Vec<TlaQuantBound>) -> &'a TlaExpr {
    let mut cursor = expr;
    while let TlaExpr::Exists {
        vars: bound_vars,
        body,
    } = cursor
    {
        vars.extend(bound_vars.iter().cloned());
        cursor = body;
    }
    cursor
}

fn render_quant_bound(bound: &TlaQuantBound, printer: &TlaPrinter) -> String {
    match &bound.set {
        Some(set) => format!("{} \\in {}", bound.var, printer.print_expr(set, 0)),
        None => bound.var.clone(),
    }
}

fn append_conjunct(buffer: &mut String, expr: &str) {
    let mut lines = expr.lines();
    if let Some(first) = lines.next() {
        buffer.push_str("        /\\ ");
        buffer.push_str(first);
        buffer.push('\n');
        for line in lines {
            buffer.push_str("           ");
            buffer.push_str(line);
            buffer.push('\n');
        }
    } else {
        buffer.push_str("        /\\ TRUE\n");
    }
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
        assert!(generated
            .wrapper_tla
            .contains("/\\ constants \\in Constants"));
        assert!(generated.wrapper_tla.contains("Init(state, constants)"));
        assert!(generated.wrapper_tla.contains("\\E state_ \\in State :"));
        assert!(generated
            .wrapper_tla
            .contains("Next(state, state_, constants)"));
        assert!(generated.cfg.contains("SPECIFICATION Spec"));
        assert!(generated.cfg.contains("CHECK_DEADLOCK FALSE"));
    }

    #[test]
    fn test_generate_relational_mc_wrapper_append_seq_packet_projection() {
        let source = r#"
---- MODULE Demo ----
EXTENDS Integers, Sequences

CONSTANTS Constants, State, Msg

Init(s, c) == TRUE
Send(s, s_, c, sent_packets) == sent_packets = <<>>
Recv(s, s_, c, i, sent_packets) == i \in Int /\ sent_packets = <<>>
Next(s, s_, c) ==
    \/ \E sent_packets \in Seq(Msg) : Send(s, s_, c, sent_packets)
    \/ \E i \in Int, sent_packets \in Seq(Msg) : Recv(s, s_, c, i, sent_packets)
====
"#;
        let opts = McWrapperOptions {
            packet_projection: PacketProjectionMode::AppendSeq,
            ..McWrapperOptions::default()
        };
        let generated = generate_relational_mc_wrapper(source, &opts).unwrap();
        assert!(generated
            .wrapper_tla
            .contains("VARIABLE state, constants, msgs"));
        assert!(generated.wrapper_tla.contains("/\\ msgs = <<>>"));
        assert!(generated
            .wrapper_tla
            .contains("\\/ \\E state_, sent_packets \\in Seq(Msg) :"));
        assert!(generated
            .wrapper_tla
            .contains("msgs' = msgs \\o sent_packets"));
        assert!(generated
            .wrapper_tla
            .contains("vars == <<state, constants, msgs>>"));
    }

    #[test]
    fn test_generate_relational_mc_wrapper_replace_seq_packet_projection() {
        let source = r#"
---- MODULE Demo ----
CONSTANTS Constants
Init(s, c) == TRUE
Step(s, s_, c, sent_packets) == sent_packets = <<>>
Next(s, s_, c) ==
    \E sent_packets \in Seq(Int) : Step(s, s_, c, sent_packets)
====
"#;
        let opts = McWrapperOptions {
            packet_projection: PacketProjectionMode::ReplaceSeq,
            ..McWrapperOptions::default()
        };
        let generated = generate_relational_mc_wrapper(source, &opts).unwrap();
        assert!(generated.wrapper_tla.contains("msgs' = sent_packets"));
    }

    #[test]
    fn test_generate_relational_mc_wrapper_packet_projection_rejects_missing_packet_binding() {
        let source = r#"
---- MODULE Demo ----
CONSTANTS Constants
Init(s, c) == TRUE
Step(s, s_, c, i) == i \in Int
Next(s, s_, c) ==
    \E i \in Int : Step(s, s_, c, i)
====
"#;
        let opts = McWrapperOptions {
            packet_projection: PacketProjectionMode::AppendSeq,
            ..McWrapperOptions::default()
        };
        let err = generate_relational_mc_wrapper(source, &opts).unwrap_err();
        assert!(err.to_string().contains("does not bind `sent_packets`"));
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
        let generated =
            generate_relational_mc_wrapper(source, &McWrapperOptions::default()).unwrap();
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
