//! Well-formedness guards over every `.tla` in the corpus.
//!
//! These are not clean-subset rules (C1–C5) — a spec can be perfectly clean and
//! still be one of these. They are the defects that make a spec *quietly
//! smaller than it looks*, which is the category the evidence document calls
//! silent wrongness. Both checks were written after TLC found the defect, and
//! both defects had already passed the linter.
//!
//! **1. A variable both assigned and frozen in the same conjunction.**
//! `UNCHANGED v` means `v' = v`, so a conjunction that also writes
//! `v' = [v EXCEPT ...]` is unsatisfiable and simply never fires. Nothing
//! reports it: the module parses, lints clean, and TLC finds no error — it just
//! explores a fraction of the state space. In `tier4/t4_01_jetpack_full` a
//! single occurrence, in `BecomeToBeLeader`, meant no node could ever become
//! leader, and **24 of the composition's 31 actions never fired**. The state
//! space was 2,591 states; with the contradiction removed it passes 15 million.
//!
//! The check must respect junction structure, and a textual version of it does
//! not. Upstream Raft writes
//!
//! ```text
//! /\ \/ grant  /\ votedFor' = [votedFor EXCEPT ![i] = j]
//!    \/ ~grant /\ UNCHANGED votedFor
//! ```
//!
//! which is correct and which a grep-shaped check reports. So this walks the
//! parsed body: `/\` merges branches, `\/` (and `IF`/`CASE`) forks them, and a
//! finding needs the assignment and the freeze in the *same* branch.
//!
//! **2. A comment left open.** TLA+ comments nest, so a `(*` whose `*)` is lost
//! (usually to a line-length edit) swallows the rest of the file. Our own
//! frontend is more permissive than SANY here and parses it happily, so this
//! surfaces only when someone runs TLC — twice, in one session, on one case.
//!
//! Neither check needs Java, so unlike V2 these run everywhere.

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};

use verus_transpiler::tla::{parse_module, TlaBinOp, TlaExpr, TlaOperator};

fn corpus_tla_files() -> Vec<PathBuf> {
    fn walk(dir: &Path, out: &mut Vec<PathBuf>) {
        let Ok(entries) = fs::read_dir(dir) else {
            return;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                walk(&path, out);
            } else if path.extension().is_some_and(|e| e == "tla") {
                out.push(path);
            }
        }
    }
    let mut out = Vec::new();
    walk(
        &Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/corpus"),
        &mut out,
    );
    out.sort();
    out
}

fn rel(path: &Path) -> String {
    path.strip_prefix(env!("CARGO_MANIFEST_DIR"))
        .unwrap_or(path)
        .display()
        .to_string()
}

/// One way of satisfying an expression: what it writes, and what it freezes.
#[derive(Clone, Default)]
struct Branch {
    assigned: BTreeSet<String>,
    frozen: BTreeSet<String>,
}

/// Past this many branches the cross product is not worth exploring, and the
/// check gives up on that definition rather than reporting something it did
/// not actually establish.
const BRANCH_CAP: usize = 4096;

fn ident_name(e: &TlaExpr) -> Option<&str> {
    match e {
        TlaExpr::Ident(n) => Some(n),
        _ => None,
    }
}

/// The branches of `e`. `/\` merges pairwise, `\/` and the conditionals fork.
fn branches(e: &TlaExpr) -> Vec<Branch> {
    match e {
        TlaExpr::BinOp { op, left, right } => match op {
            TlaBinOp::And => {
                let (ls, rs) = (branches(left), branches(right));
                if ls.len().saturating_mul(rs.len()) > BRANCH_CAP {
                    return vec![Branch::default()];
                }
                let mut out = Vec::with_capacity(ls.len() * rs.len());
                for l in &ls {
                    for r in &rs {
                        let mut merged = l.clone();
                        merged.assigned.extend(r.assigned.iter().cloned());
                        merged.frozen.extend(r.frozen.iter().cloned());
                        out.push(merged);
                    }
                }
                out
            }
            TlaBinOp::Or => {
                let mut out = branches(left);
                out.extend(branches(right));
                out.truncate(BRANCH_CAP);
                out
            }
            TlaBinOp::Eq => {
                // `v' = e` is the assignment shape. Anything else is a guard.
                if let TlaExpr::Prime(inner) = left.as_ref() {
                    if let Some(name) = ident_name(inner) {
                        return vec![Branch {
                            assigned: [name.to_string()].into_iter().collect(),
                            frozen: BTreeSet::new(),
                        }];
                    }
                }
                vec![Branch::default()]
            }
            _ => vec![Branch::default()],
        },
        TlaExpr::Unchanged(vars) => {
            let mut frozen = BTreeSet::new();
            for v in vars {
                collect_idents(v, &mut frozen);
            }
            vec![Branch {
                assigned: BTreeSet::new(),
                frozen,
            }]
        }
        TlaExpr::IfThenElse {
            then_expr,
            else_expr,
            ..
        } => {
            let mut out = branches(then_expr);
            out.extend(branches(else_expr));
            out.truncate(BRANCH_CAP);
            out
        }
        TlaExpr::Case { arms, other } => {
            let mut out = Vec::new();
            for (_, body) in arms {
                out.extend(branches(body));
            }
            if let Some(o) = other {
                out.extend(branches(o));
            }
            out.truncate(BRANCH_CAP);
            if out.is_empty() {
                out.push(Branch::default());
            }
            out
        }
        TlaExpr::LetIn { body, .. } => branches(body),
        TlaExpr::Exists { body, .. } | TlaExpr::Forall { body, .. } => branches(body),
        _ => vec![Branch::default()],
    }
}

/// Names inside an `UNCHANGED` operand — a bare name, or a tuple of them.
fn collect_idents(e: &TlaExpr, out: &mut BTreeSet<String>) {
    match e {
        TlaExpr::Ident(n) => {
            out.insert(n.clone());
        }
        TlaExpr::Tuple(items) => {
            for i in items {
                collect_idents(i, out);
            }
        }
        _ => {}
    }
}

fn contradictions(op: &TlaOperator) -> Vec<String> {
    let mut out = Vec::new();
    for b in branches(&op.body) {
        let both: Vec<_> = b.assigned.intersection(&b.frozen).cloned().collect();
        if !both.is_empty() {
            out.push(format!("{both:?}"));
        }
    }
    out.sort();
    out.dedup();
    out
}

#[test]
fn no_action_both_assigns_and_freezes_a_variable() {
    let files = corpus_tla_files();
    assert!(!files.is_empty(), "no .tla in the corpus -- vacuous guard");

    let mut failures = Vec::new();
    let mut checked = 0usize;
    for path in &files {
        let src = fs::read_to_string(path).expect("corpus file must be readable");
        // A spec our own frontend cannot parse is unchecked, not clean. The
        // corpus has such files by design (`original.tla` at intake), so this
        // reports rather than fails.
        let Ok(module) = parse_module(&src) else {
            eprintln!("unparsed, so unchecked: {}", rel(path));
            continue;
        };
        checked += 1;
        for op in &module.operators {
            for both in contradictions(op) {
                failures.push(format!(
                    "{}: {} assigns and freezes {both} in one conjunction \
                     -- that branch can never fire",
                    rel(path),
                    op.name,
                ));
            }
        }
    }

    assert!(checked > 0, "nothing parsed -- vacuous guard");
    assert!(
        failures.is_empty(),
        "unsatisfiable action branch(es):\n  {}",
        failures.join("\n  ")
    );
}

#[test]
fn every_comment_is_closed() {
    let files = corpus_tla_files();
    assert!(!files.is_empty(), "no .tla in the corpus -- vacuous guard");

    let mut failures = Vec::new();
    for path in &files {
        let src = fs::read_to_string(path).expect("corpus file must be readable");
        let chars: Vec<char> = src.chars().collect();
        let mut depth: i32 = 0;
        let mut opened_at = 0usize;
        let mut line = 1usize;
        let mut i = 0;
        while i + 1 < chars.len() {
            if chars[i] == '\n' {
                line += 1;
            }
            if chars[i] == '(' && chars[i + 1] == '*' {
                if depth == 0 {
                    opened_at = line;
                }
                depth += 1;
                i += 2;
                continue;
            }
            if chars[i] == '*' && chars[i + 1] == ')' {
                depth -= 1;
                i += 2;
                continue;
            }
            i += 1;
        }
        if depth > 0 {
            failures.push(format!(
                "{}: comment opened at line {opened_at} is never closed \
                 (our frontend accepts this; SANY does not)",
                rel(path)
            ));
        } else if depth < 0 {
            failures.push(format!("{}: a `*)` closes nothing", rel(path)));
        }
    }

    assert!(
        failures.is_empty(),
        "malformed comment(s):\n  {}",
        failures.join("\n  ")
    );
}
