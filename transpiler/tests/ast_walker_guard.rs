//! Every walk over `TlaExpr` must reach every sub-expression.
//!
//! A walker that silently skips a node kind is the worst-behaved defect this
//! project produces, because the skipped subtree does not fail — it is simply
//! not looked at, and whatever was in it comes out unexamined. Two were live at
//! once:
//!
//! - **`substitute_all` covered 15 of 34 node kinds.** A name inside a
//!   `SetFilter`, `FnConstruct`, `Tuple`, `Unchanged`, `Prime`, `RecordSet`,
//!   `FnSet`, `SetMapMulti`, `Lambda` or `LetIn` reached the catch-all clone and
//!   came back *unchanged*, so it was emitted meaning whatever it happened to
//!   mean at the use site. `inline_call` and `expand_let` both go through it.
//!   Found only because a re-indexed binder failed to rewrite `k` inside
//!   `{j \in Server : matchIndex[i][j] >= k}`.
//! - **`children` missed `SetMapMulti` and `Lambda`**, so `mentions_prime`,
//!   `reads_state` and the helper-parameter shape tests looked past them.
//!
//! Both were closed by hand, and by hand is not a fix: `TlaExpr` will grow, and
//! the next variant added quietly joins the catch-all of every walker that has
//! one. **This test is the fix.** It reads the AST definition and the walkers
//! out of the source, so a new variant carrying an expression fails it until
//! every walker names that variant.
//!
//! Reading source rather than exercising behaviour is deliberate. A behavioural
//! test would have to construct a value of every variant, and the failure mode
//! here is *forgetting a variant exists* — precisely what a hand-written list of
//! constructors would also forget.

use std::collections::BTreeSet;
use std::fs;
use std::path::PathBuf;

fn src(file: &str) -> String {
    let path: PathBuf = [env!("CARGO_MANIFEST_DIR"), "src", "tla", file]
        .iter()
        .collect();
    fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()))
}

/// The body of a `fn <name>(` up to the line that closes it at the function's
/// own indentation.
fn function_body<'a>(source: &'a str, name: &str) -> &'a str {
    let needle = format!("fn {name}(");
    let start = source
        .find(&needle)
        .unwrap_or_else(|| panic!("no `fn {name}(` in the source -- was it renamed?"));
    let indent = source[..start]
        .rfind('\n')
        .map(|nl| source[nl + 1..start].len())
        .unwrap_or(0);
    let closer = format!("\n{}}}\n", " ".repeat(indent));
    let end = source[start..]
        .find(&closer)
        .unwrap_or(source.len() - start);
    &source[start..start + end]
}

fn finish(current: &mut Option<String>, payload: &str, out: &mut BTreeSet<String>) {
    let Some(name) = current.take() else {
        return;
    };
    let carries = ["TlaExpr", "TlaQuantBound", "TlaOperator", "TlaExceptUpdate"]
        .iter()
        .any(|ty| payload.contains(ty));
    if carries {
        out.insert(name);
    }
}

/// `TlaExpr`'s variants that carry a sub-expression.
///
/// "Carries a sub-expression" is read off the payload: a `TlaExpr`, or one of
/// the structs that hold them — `TlaQuantBound`'s binding set, `TlaOperator`'s
/// body, `TlaExceptUpdate`'s path and value.
fn variants_with_sub_expressions() -> BTreeSet<String> {
    let ast = src("ast.rs");
    let start = ast
        .find("pub enum TlaExpr")
        .expect("TlaExpr must be defined in ast.rs");
    let body = &ast[start..];
    let body = &body[..body.find("\n}\n").expect("TlaExpr must be closed")];

    let mut out = BTreeSet::new();
    let mut current: Option<String> = None;
    let mut payload = String::new();
    let mut depth = 0i32;
    for line in body.lines() {
        let trimmed = line.trim_start();
        let starts_variant = depth == 0
            && line.len() - trimmed.len() == 4
            && !trimmed.starts_with("//")
            && !trimmed.starts_with('#')
            && trimmed
                .chars()
                .next()
                .is_some_and(|c| c.is_ascii_uppercase());
        if starts_variant {
            finish(&mut current, &payload, &mut out);
            current = Some(
                trimmed
                    .chars()
                    .take_while(|c| c.is_alphanumeric() || *c == '_')
                    .collect(),
            );
            payload.clear();
        }
        if current.is_some() {
            payload.push_str(line);
            payload.push('\n');
            depth += line.matches(['{', '(']).count() as i32;
            depth -= line.matches(['}', ')']).count() as i32;
            depth = depth.max(0);
        }
    }
    finish(&mut current, &payload, &mut out);
    assert!(
        out.len() > 20,
        "only {} variants parsed out of ast.rs -- the parse above has drifted \
         from the source and this guard is checking almost nothing",
        out.len()
    );
    out
}

/// Which variants a walker's body names.
fn variants_named(body: &str) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    let mut rest = body;
    while let Some(at) = rest.find("TlaExpr::") {
        rest = &rest[at + "TlaExpr::".len()..];
        let name: String = rest
            .chars()
            .take_while(|c| c.is_alphanumeric() || *c == '_')
            .collect();
        if !name.is_empty() {
            out.insert(name);
        }
    }
    out
}

/// Every walk that must be total, and where it lives.
const WALKERS: &[(&str, &str)] = &[
    // Rewrites an expression. A variant it misses is returned *unchanged*, so
    // the failure is silent -- this is the one that bit.
    ("action_projection.rs", "substitute_all"),
    // The generic descent every analysis in the projection is built on.
    ("action_projection.rs", "children"),
    // The clean-subset linter's own descent: C1-C5 see only what it reaches.
    ("clean_subset.rs", "walk_children"),
    // Rewrites an instantiated module's body, qualifying its own names. A
    // variant it misses keeps bare names that then resolve to nothing --
    // `Case` and `LetIn` both sat in its catch-all.
    ("module_resolver.rs", "rewrite"),
];

#[test]
fn walkers_reach_every_sub_expression() {
    let expected = variants_with_sub_expressions();
    let mut failures = Vec::new();

    for (file, walker) in WALKERS {
        let source = src(file);
        let named = variants_named(function_body(&source, walker));
        let missing: Vec<&str> = expected
            .iter()
            .filter(|v| !named.contains(*v))
            .map(String::as_str)
            .collect();
        if !missing.is_empty() {
            failures.push(format!(
                "{file}::{walker} does not name {} of the {} variants that carry \
                 a sub-expression: {}",
                missing.len(),
                expected.len(),
                missing.join(", ")
            ));
        }
    }

    assert!(
        failures.is_empty(),
        "a walk over TlaExpr skips a node kind, so whatever is inside it goes \
         unexamined:\n  {}\n\nIf a variant genuinely needs no descent, name it \
         anyway in an explicit arm -- silence and intent must not look alike.",
        failures.join("\n  ")
    );
}

/// The guard above is worth its runtime only if the variant list it builds is
/// real. This pins some by name: if the parse breaks they vanish, and the guard
/// then passes while checking nothing.
#[test]
fn the_variant_list_is_actually_parsed() {
    let expected = variants_with_sub_expressions();
    for must in [
        "SetMapMulti", // the one `children` missed
        "SetFilter",   // the one whose miss surfaced `substitute_all`'s hole
        "LetIn",
        "FnExcept",
        "Case",
        "Lambda",
    ] {
        assert!(
            expected.contains(must),
            "`{must}` carries a sub-expression but was not parsed out of ast.rs \
             -- the guard is checking less than it claims. Parsed: {expected:?}"
        );
    }
    for leaf in ["Ident", "Number", "String", "Bool"] {
        assert!(
            !expected.contains(leaf),
            "`{leaf}` is a leaf; counting it would force every walker to name \
             nodes that have nothing to descend into"
        );
    }
}

/// The textual guard above checks that a walker *names* a variant. That is not
/// the same as descending into all of it, and the difference was live in the
/// very commit that added the guard: `substitute_all`'s `FnExcept` arm named
/// the variant and rewrote the value, while cloning the update *path* — so an
/// index expression in `[x EXCEPT ![k] = ..]` kept its definition-site name and
/// was emitted meaning whatever that name meant at the use site.
///
/// So this test asks the question behaviourally: put a marker where each
/// sub-expression lives, substitute it, and require it to be gone. A walker
/// that skips a field fails here even with the variant named.
#[test]
fn substitution_reaches_every_sub_expression_position() {
    use verus_transpiler::tla::parse_module;

    // Each entry is a spec whose action mentions `MARKER` in one structural
    // position. `MARKER` is a 0-ary operator, so inlining the action's call
    // must replace it -- and if the walker skips that position, it survives.
    const CASES: &[(&str, &str)] = &[
        ("EXCEPT index", "x' = [x EXCEPT ![MARKER] = 1]"),
        ("EXCEPT value", "x' = [x EXCEPT ![p] = MARKER]"),
        ("nested EXCEPT index", "y' = [y EXCEPT ![p][MARKER] = 1]"),
        (
            "set filter",
            "x' = [x EXCEPT ![p] = Cardinality({q \\in Proc : q = MARKER})]",
        ),
        ("tuple", "z' = [z EXCEPT ![p] = <<MARKER>>]"),
        (
            "function construct",
            "y' = [y EXCEPT ![p] = [q \\in Proc |-> MARKER]]",
        ),
        (
            "if condition",
            "x' = [x EXCEPT ![p] = IF MARKER = 0 THEN 1 ELSE 2]",
        ),
        (
            "case arm",
            "x' = [x EXCEPT ![p] = CASE MARKER = 0 -> 1 [] OTHER -> 2]",
        ),
    ];

    let mut survived = Vec::new();
    for (what, conjunct) in CASES {
        let source = format!(
            "---- MODULE Test ----\n\
             EXTENDS Integers, FiniteSets, Sequences\n\
             VARIABLES x, y, z\n\
             MARKER == 0\n\
             TypeOK == x \\in [Proc -> Nat] /\\ y \\in [Proc -> [Proc -> Nat]] /\\ z \\in [Proc -> Seq(Nat)]\n\
             Step(p) == {conjunct}\n\
             Next == \\E p \\in Proc : Step(p)\n\
             ===="
        );
        let module = parse_module(&source)
            .unwrap_or_else(|e| panic!("{what}: the probe spec must parse: {e:?}"));
        let step = module
            .operators
            .iter()
            .find(|o| o.name == "Step")
            .expect("Step must be defined");
        // Substituting `MARKER` must reach it wherever it sits.
        let after = verus_transpiler::tla::substitute_for_test(
            &step.body,
            "MARKER",
            &verus_transpiler::tla::ast::TlaExpr::Number(
                verus_transpiler::tla::ast::TlaNumber::Decimal("7".to_string()),
            ),
        );
        if format!("{after:?}").contains("MARKER") {
            survived.push(*what);
        }
    }

    assert!(
        survived.is_empty(),
        "substitution did not reach these positions, so a name there survives \
         and is emitted meaning whatever it means at the use site: {survived:?}"
    );
}

/// Each named walker is found, and its body was really extracted -- otherwise
/// `variants_named` returns an empty set and everything looks missing (or, if
/// the extraction over-reaches, everything looks present).
#[test]
fn every_named_walker_is_found() {
    for (file, walker) in WALKERS {
        let source = src(file);
        let body = function_body(&source, walker);
        assert!(
            body.len() > 200,
            "{file}::{walker} extracted as {} bytes -- the name was found but \
             not the body",
            body.len()
        );
        assert!(
            body.len() < source.len(),
            "{file}::{walker} extraction ran to the end of the file, so it is \
             reading other functions' arms as its own"
        );
        assert!(
            !variants_named(body).is_empty(),
            "{file}::{walker} names no TlaExpr variant at all"
        );
    }
}
