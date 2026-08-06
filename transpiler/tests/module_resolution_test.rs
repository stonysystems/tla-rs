//! Phase 55.1.b — `EXTENDS` and `INSTANCE` resolve to one module.
//!
//! Until this landed, a composed spec was linted as the *file* rather than the
//! module it denotes. With `B!RequestVote` unresolvable the node set could not
//! be identified, so C1, C2 and C3 all returned early and the report said "3 of
//! 5 implemented rules did not run". A reader who looked only at the violation
//! count saw a small number and read it as "nearly clean".
//!
//! Jetpack is the case that shows the cost: **2 violations before, 46 after**.

use std::fs;
use std::path::{Path, PathBuf};

use verus_transpiler::tla::{
    lint_module, needs_resolution, parse_module, resolve_module_file, CleanRule,
};

fn scratch(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tla_rs_modres_{name}"));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("temp dir");
    dir
}

fn write(dir: &Path, name: &str, body: &str) -> PathBuf {
    let p = dir.join(name);
    fs::write(&p, body).expect("write");
    p
}

#[test]
fn extends_pulls_in_the_extended_module() {
    let dir = scratch("extends");
    write(
        &dir,
        "Base.tla",
        "---- MODULE Base ----\nVARIABLES st\nBaseStep(i) == st' = [st EXCEPT ![i] = 1]\n====\n",
    );
    let root = write(
        &dir,
        "Comp.tla",
        "---- MODULE Comp ----\n\
         EXTENDS Base\n\
         TypeOK == st \\in [Node -> Nat]\n\
         Next == \\E i \\in Node : BaseStep(i)\n====\n",
    );

    let resolved = resolve_module_file(&root).expect("must resolve");
    assert!(
        resolved.operators.iter().any(|o| o.name == "BaseStep"),
        "BaseStep should have been pulled in"
    );
    assert!(resolved.variables.contains(&"st".to_string()));

    // The point of resolving: the node set becomes identifiable.
    let report = lint_module(&resolved);
    assert_eq!(
        report.node_set.as_deref(),
        Some("Node"),
        "without resolution this is None and C1/C2/C3 never run"
    );
}

#[test]
fn instance_qualifies_operators_and_shares_variables() {
    let dir = scratch("instance");
    write(
        &dir,
        "Lib.tla",
        "---- MODULE Lib ----\n\
         CONSTANT Tag\n\
         VARIABLES st\n\
         Helper(i) == st[i]\n\
         Step(i) == st' = [st EXCEPT ![i] = Helper(i) + 1]\n====\n",
    );
    let root = write(
        &dir,
        "Top.tla",
        "---- MODULE Top ----\n\
         VARIABLES st\n\
         L == INSTANCE Lib WITH Tag <- 1\n\
         TypeOK == st \\in [Node -> Nat]\n\
         Next == \\E i \\in Node : L!Step(i)\n====\n",
    );

    let resolved = resolve_module_file(&root).expect("must resolve");
    let names: Vec<String> = resolved.operators.iter().map(|o| o.name.clone()).collect();
    assert!(names.contains(&"L!Step".to_string()), "{names:?}");
    assert!(names.contains(&"L!Helper".to_string()), "{names:?}");

    // A qualified body must call the qualified name, or the reference dangles.
    let step = resolved
        .operators
        .iter()
        .find(|o| o.name == "L!Step")
        .expect("L!Step");
    let rendered = format!("{:?}", step.body);
    assert!(
        rendered.contains("L!Helper"),
        "L!Step should call L!Helper, not bare Helper"
    );
    assert!(
        !resolved.constants.iter().any(|c| c.name == "Tag"),
        "a substituted constant must not be added to the parent"
    );
    assert_eq!(
        resolved.variables.iter().filter(|v| *v == "st").count(),
        1,
        "an unsubstituted variable is shared, not duplicated"
    );
}

#[test]
fn a_module_cycle_is_reported_rather_than_looping() {
    let dir = scratch("cycle");
    write(&dir, "A.tla", "---- MODULE A ----\nEXTENDS B\n====\n");
    write(&dir, "B.tla", "---- MODULE B ----\nEXTENDS A\n====\n");
    let err = resolve_module_file(&dir.join("A.tla")).expect_err("a cycle must be an error");
    assert!(err.to_string().contains("cycle"), "{err}");
}

#[test]
fn a_missing_module_names_what_referenced_it() {
    let dir = scratch("missing");
    let root = write(
        &dir,
        "Root.tla",
        "---- MODULE Root ----\nEXTENDS NoSuchModule\n====\n",
    );
    let err = resolve_module_file(&root).expect_err("must fail");
    let msg = err.to_string();
    assert!(msg.contains("NoSuchModule"), "{msg}");
    assert!(msg.contains("Root"), "should say who referenced it: {msg}");
}

#[test]
fn standard_modules_are_not_looked_for_on_disk() {
    let dir = scratch("standard");
    let root = write(
        &dir,
        "Solo.tla",
        "---- MODULE Solo ----\n\
         EXTENDS Integers, Sequences, FiniteSets, TLC\n\
         VARIABLES x\n\
         TypeOK == x \\in [Node -> Nat]\n\
         Step(i) == x' = [x EXCEPT ![i] = 1]\n\
         Next == \\E i \\in Node : Step(i)\n====\n",
    );
    // `needs_resolution` must not be fooled by standard modules, or every
    // self-contained spec would start touching the filesystem.
    let module = parse_module(&fs::read_to_string(&root).unwrap()).expect("parse");
    assert!(
        !needs_resolution(&module),
        "a spec extending only standard modules needs no resolution"
    );
    resolve_module_file(&root).expect("resolving must still succeed");
}

#[test]
fn an_identifier_may_begin_with_an_underscore() {
    // `base_raft.tla` defines `_SendNoRestriction`. Scanning `_` as its own
    // token unconditionally -- which is what the action-subscript fix did --
    // made that module unparseable, and with it the whole Jetpack composition.
    let module = parse_module(
        "---- MODULE U ----\nVARIABLES x\n_Send(m) == x' = m\nNext == _Send(1)\n====\n",
    )
    .expect("an identifier may begin with _");
    assert!(module.operators.iter().any(|o| o.name == "_Send"));

    // ...and the action subscript must still scan as two tokens.
    parse_module(
        "---- MODULE S ----\nVARIABLES x\nNext == x' = x\nvars == <<x>>\nSpec == [][Next]_vars\n====\n",
    )
    .expect("[Next]_vars must still parse");
}

#[test]
fn a_composed_spec_is_measured_against_the_module_it_denotes() {
    // The regression this feature exists to prevent. Before resolution the
    // Jetpack composition linted at 2 violations with three rules silently not
    // running; after, the node set is found and every rule runs.
    let corpus = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/corpus/tier3/t3_01_jetpack");
    if !corpus.join("original.tla").exists() {
        eprintln!("skipping: corpus case not present");
        return;
    }

    // The corpus stores the modules under `original_*` names, so stage them
    // under the names the composition actually references.
    let dir = scratch("jetpack");
    for (from, to) in [
        ("original.tla", "jetpack_raft_composition.tla"),
        ("original_base_raft.tla", "base_raft.tla"),
        ("original_jetpack_layer.tla", "jetpack.tla"),
    ] {
        fs::copy(corpus.join(from), dir.join(to)).expect("stage");
    }

    let resolved =
        resolve_module_file(&dir.join("jetpack_raft_composition.tla")).expect("must resolve");
    let report = lint_module(&resolved);

    assert_eq!(
        report.node_set.as_deref(),
        Some("Server"),
        "the node set must be identifiable once the modules resolve"
    );
    let c2 = report
        .findings
        .iter()
        .filter(|f| f.rule == CleanRule::C2)
        .count();
    assert!(
        c2 > 10,
        "C2 should now report the composition's cross-node reads, got {c2}"
    );
    assert!(
        report.violations() > 40,
        "the resolved distance is ~46; got {} -- if this dropped sharply, \
         check whether a rule silently stopped running",
        report.violations()
    );
}
