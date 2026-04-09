#!/usr/bin/env python3
"""
Detect degenerate / stub translated tla-rs specs in the DPOR checker corpus.

Background: Phase 38 declared "20/20 ALL GREEN" but several protocol cases pass
vacuously because their translated .rs files are structurally degenerate. This
script catches the four known patterns:

  1. stuttering_lnext       — LNext body is only s_.field == s.field frame
                              conditions with no action call. Source TLA+ wrote
                              `Next == msgs' = msgs /\ ...` (literal stutter).
                              Example bug: 17_paxos_small.

  2. tautological_invariant — invariant body is structurally `X == X`, `X => X`,
                              `(X) ==> (X == X)`, etc. The predicate is
                              unfalsifiable so the model checker can never report
                              a violation.
                              Example bug: 17_paxos_small (LTypeOK), 20_raft_small
                              (LAtMostOneLeader).

  3. arbitrary_soup         — operator body has > ARBITRARY_DENSITY_THRESHOLD
                              `arbitrary::<...>()` calls per line. Indicates the
                              Verus→TLA+ field harvesting fell back to nondet
                              for missing fields.
                              Example bug: 14_leader_election_small.

  4. primitive_state_param  — LInit / LNext parameter `s` is typed as a primitive
                              (`int`, `bool`, `Seq<...>`) instead of a struct.
                              Indicates state-type inference failed.
                              Example bug: 14, 15, 16, 19.

  5. incomplete_next        — LNext disjuncts call only a strict subset of the
                              action operators that have `(s: LState, s_: LState, ...)`
                              signatures. The other actions are dead code, often
                              because the source TLA+ Next dropped existentially
                              parameterized actions like `\E r \in RM : Foo(r)`.
                              Example bug: 13_twophase_small (drops LTMRcvPrepared),
                              18_pbft_small (drops LSendPrePrepare/Prepare/Commit),
                              20_raft_small (drops LGrantVote).

Exit codes:
  0 — no degeneracies found
  1 — at least one .rs file flagged
  2 — usage error

Usage:
  ./scripts/detect_stub_specs.py            # scan tests/tla-rs/
  ./scripts/detect_stub_specs.py --json     # machine-readable
"""

import argparse
import json
import re
import sys
from pathlib import Path

ARBITRARY_DENSITY_THRESHOLD = 3  # >= N arbitrary() calls per operator body line

# Operators that we treat as "invariant predicates" worth tautology-checking.
# Anything ending in OK / Safety / Invariant / NoStarvation / MutualExclusion etc.
INVARIANT_NAME_PATTERNS = [
    re.compile(r"^L.*OK$"),
    re.compile(r"^L.*Safety.*$"),
    re.compile(r"^L.*Invariant$"),
    re.compile(r"^L.*Correct$"),
    re.compile(r"^L.*Exclusion$"),
    re.compile(r"^LAtMost.*$"),
    re.compile(r"^LNo.*$"),
]

OP_DECL_RE = re.compile(
    r"pub open spec fn (L\w+)\s*\(([^)]*)\)\s*->\s*\w[^{]*\{",
    re.MULTILINE,
)


def find_operator_bodies(src):
    """Yield (op_name, params, body) for every `pub open spec fn L...` block."""
    for m in OP_DECL_RE.finditer(src):
        name = m.group(1)
        params = m.group(2)
        body_start = m.end()
        # Find matching closing brace.
        depth = 1
        i = body_start
        while i < len(src) and depth > 0:
            c = src[i]
            if c == "{":
                depth += 1
            elif c == "}":
                depth -= 1
            i += 1
        body = src[body_start : i - 1]
        yield name, params, body.strip()


def looks_like_invariant(name):
    return any(p.match(name) for p in INVARIANT_NAME_PATTERNS)


def normalize_for_tautology(s):
    """Strip whitespace and outer parens for syntactic equality check."""
    s = s.strip()
    while s.startswith("(") and s.endswith(")"):
        # Only strip if outer parens balance.
        depth = 0
        ok = True
        for i, c in enumerate(s):
            if c == "(":
                depth += 1
            elif c == ")":
                depth -= 1
                if depth == 0 and i < len(s) - 1:
                    ok = False
                    break
        if ok:
            s = s[1:-1].strip()
        else:
            break
    return re.sub(r"\s+", " ", s)


def find_tautology_clauses(body):
    """
    Detect `X == X` and `X => X`-style clauses anywhere in a predicate body.
    Returns list of offending normalized clause strings.
    """
    findings = []
    # Match (lhs == rhs) and (lhs ==> rhs) where lhs/rhs are simple field-paths.
    # We use a non-greedy regex over balanced-ish atoms to keep this dependency-free.
    # Pattern: identifier with dots/indexing, ==, identifier with dots/indexing.
    atom = r"[A-Za-z_][\w\.\[\]]*(?:\(\))?"
    eq_re = re.compile(rf"\b({atom})\s*==\s*({atom})\b")
    impl_re = re.compile(rf"\(({atom})\)\s*==>\s*\(({atom})\s*==\s*({atom})\)")
    impl2_re = re.compile(rf"({atom})\s*==>\s*({atom})")

    for m in eq_re.finditer(body):
        if m.group(1) == m.group(2) and "arbitrary" not in m.group(1):
            findings.append(f"{m.group(1)} == {m.group(2)}")
    for m in impl_re.finditer(body):
        if m.group(2) == m.group(3):
            findings.append(f"({m.group(1)}) ==> ({m.group(2)} == {m.group(3)})")
    for m in impl2_re.finditer(body):
        if m.group(1) == m.group(2):
            findings.append(f"{m.group(1)} ==> {m.group(2)}")
    return findings


def is_stuttering_lnext(body):
    """
    A stuttering LNext is one whose body contains only s_.X == s.X clauses
    (the frame condition for every state field) with no operator calls and
    no disjunctions binding to action operators.
    """
    # Strip outer parens.
    text = body
    # Reject if it contains any call to LSomething(...) or `||`/`exists`.
    if re.search(r"\bL[A-Z]\w*\s*\(", text):
        return False, ""
    if "exists |" in text:
        return False, ""
    if "||" in text:
        return False, ""
    # Must have at least one s_.X == s.X clause.
    frame_clauses = re.findall(r"s_\.(\w+)\s*==\s*s\.\1\b", text)
    if not frame_clauses:
        return False, ""
    return True, f"only frame clauses: {', '.join(frame_clauses)}"


def arbitrary_density(body):
    n_arbitrary = body.count("arbitrary")
    n_lines = max(1, body.count("\n") + 1)
    return n_arbitrary, n_arbitrary / n_lines


def primitive_state_params(params):
    """
    Return a list of (param_name, type_str) where the param is named s/s_/state
    but typed as a primitive (int, bool, char, Seq<*>) instead of a struct.
    """
    findings = []
    for raw in params.split(","):
        raw = raw.strip()
        if not raw or ":" not in raw:
            continue
        name, ty = raw.split(":", 1)
        name = name.strip()
        ty = ty.strip()
        if name in ("s", "s_", "state", "state_"):
            if ty in ("int", "bool", "char", "nat") or ty.startswith("Seq<"):
                findings.append((name, ty))
    return findings


def is_action_operator(params):
    """An action operator has both `s` and `s_` as parameters."""
    has_s = bool(re.search(r"\bs\s*:", params))
    has_s_ = bool(re.search(r"\bs_\s*:", params))
    return has_s and has_s_


def scan_file(path):
    src = path.read_text()
    findings = {
        "file": str(path),
        "stuttering_lnext": None,
        "tautological_invariants": [],
        "arbitrary_soup_ops": [],
        "primitive_state_params": [],
        "incomplete_next": None,
    }

    action_ops = []  # (name, params)
    lnext_body = None

    for name, params, body in find_operator_bodies(src):
        if name == "LNext":
            lnext_body = body
            ok, reason = is_stuttering_lnext(body)
            if ok:
                findings["stuttering_lnext"] = reason

        if name != "LNext" and is_action_operator(params):
            action_ops.append((name, params))

        if looks_like_invariant(name):
            tauts = find_tautology_clauses(body)
            if tauts:
                findings["tautological_invariants"].append(
                    {"op": name, "clauses": tauts[:3]}
                )

        n_arb, density = arbitrary_density(body)
        if n_arb >= ARBITRARY_DENSITY_THRESHOLD and density >= 1.0:
            findings["arbitrary_soup_ops"].append(
                {"op": name, "arbitrary_calls": n_arb}
            )

        if name in ("LInit", "LNext"):
            prims = primitive_state_params(params)
            if prims:
                findings["primitive_state_params"].extend(
                    [{"op": name, "param": p, "type": t} for p, t in prims]
                )

    # incomplete_next check: every action operator should appear as a call in LNext.
    if lnext_body is not None and action_ops:
        called = set()
        for name, _ in action_ops:
            if re.search(rf"\b{re.escape(name)}\s*\(", lnext_body):
                called.add(name)
        missing = [name for name, _ in action_ops if name not in called]
        if missing and len(called) > 0:
            findings["incomplete_next"] = {
                "called": sorted(called),
                "missing": sorted(missing),
            }

    return findings


def has_any_finding(f):
    return (
        f["stuttering_lnext"] is not None
        or f["tautological_invariants"]
        or f["arbitrary_soup_ops"]
        or f["primitive_state_params"]
        or f["incomplete_next"] is not None
    )


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument(
        "--corpus",
        default=str(Path(__file__).resolve().parent.parent / "tests" / "tla-rs"),
        help="Path to the tla-rs corpus directory",
    )
    ap.add_argument("--json", action="store_true", help="Emit machine-readable JSON")
    args = ap.parse_args()

    corpus = Path(args.corpus)
    if not corpus.is_dir():
        print(f"error: corpus directory not found: {corpus}", file=sys.stderr)
        return 2

    all_findings = []
    flagged_count = 0

    for case_dir in sorted(corpus.iterdir()):
        if not case_dir.is_dir():
            continue
        for rs in sorted(case_dir.glob("*.rs")):
            f = scan_file(rs)
            if has_any_finding(f):
                f["case_id"] = case_dir.name
                all_findings.append(f)
                flagged_count += 1

    if args.json:
        print(json.dumps({"flagged": flagged_count, "findings": all_findings}, indent=2))
        return 1 if flagged_count > 0 else 0

    if flagged_count == 0:
        print("OK: no degenerate stub specs detected in corpus.")
        return 0

    print(f"Flagged {flagged_count} translated spec(s) in corpus:")
    print()
    for f in all_findings:
        print(f"  {f['case_id']}/{Path(f['file']).name}")
        if f["stuttering_lnext"]:
            print(f"    [BUG_A] stuttering LNext — {f['stuttering_lnext']}")
        for t in f["tautological_invariants"]:
            print(f"    [BUG_A] tautological invariant {t['op']}:")
            for c in t["clauses"]:
                print(f"             {c}")
        for s in f["arbitrary_soup_ops"]:
            print(f"    [BUG_B] arbitrary-soup operator {s['op']} ({s['arbitrary_calls']} arbitrary() calls)")
        for p in f["primitive_state_params"]:
            print(f"    [BUG_B] {p['op']}: param `{p['param']}` typed as `{p['type']}` (expected struct)")
        if f["incomplete_next"]:
            inc = f["incomplete_next"]
            print(f"    [BUG_A] incomplete LNext — calls {len(inc['called'])} of "
                  f"{len(inc['called']) + len(inc['missing'])} action operators")
            print(f"             dropped: {', '.join(inc['missing'])}")
        print()

    print("Bug A = degenerate source TLA+ stub (Next drops actions, invariants are X==X)")
    print("Bug B = Verus→TLA+→spec roundtrip degradation (state field harvesting collapsed)")
    return 1


if __name__ == "__main__":
    sys.exit(main())
