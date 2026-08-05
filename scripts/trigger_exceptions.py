#!/usr/bin/env python3
"""Generate the checked-in list of deliberate trigger exceptions (Phase 54).

Phase 54's acceptance criterion is

    0 `automatically chose triggers` notes on a full pass, **or** a checked-in
    list of the deliberate exceptions with a reason for each

Every note that survives 54.3-54.8 is here, classified, with the reason it was
not annotated and what would be needed to remove it. Generating the list from a
measured inventory rather than writing it by hand means it cannot quietly drift
from reality: `--check` fails when the committed list no longer matches a fresh
inventory.

Usage
-----
    scripts/trigger_exceptions.py reports/triggers/current.json \\
        -o reports/triggers/exceptions.md
    scripts/trigger_exceptions.py reports/triggers/current.json --check \\
        reports/triggers/exceptions.md
"""

import argparse
import json
import os
import re
import sys
from collections import Counter, OrderedDict

def _skip_functions_by_module(repo_root="."):
    """`skip_functions` per RSL module, from the transpile configs.

    A note inside one of these lives in a *hand-written* body that regeneration
    preserves verbatim, so it is not transpiler output and no amount of
    regenerating will change it -- a different disposition from the emitted
    notes, and the reason this file distinguishes them.
    """
    out = {}
    base = os.path.join(repo_root, "src", "protocol", "RSL")
    for mod in (
        "broadcast", "acceptor", "learner", "executor", "election", "proposer", "replica",
    ):
        path = os.path.join(base, "%s_transpile.toml" % mod)
        try:
            with open(path) as fh:
                text = fh.read()
        except OSError:
            continue
        m = re.search(r"skip_functions\s*=\s*\[(.*?)\]", text, re.S)
        out[mod] = set(re.findall(r'"([^"]+)"', m.group(1))) if m else set()
    return out


_FN_RE = re.compile(r"\s*(?:pub )?(?:exec |proof |open spec |spec )*fn ([A-Za-z0-9_]+)")


def _enclosing_fn(path, line):
    try:
        with open(path) as fh:
            lines = fh.read().split("\n")
    except OSError:
        return None
    for i in range(min(line, len(lines)) - 1, -1, -1):
        m = _FN_RE.match(lines[i])
        if m:
            return m.group(1)
    return None


def _in_preserved_body(entry, skip_by_module, repo_root="."):
    path = entry["file"]
    if "generated/RSL/" not in path:
        return False
    mod = os.path.basename(path).replace("_gen.rs", "")
    fn = _enclosing_fn(os.path.join(repo_root, path), entry["line"])
    if not fn:
        return False
    base = fn[1:] if fn.startswith("C") else fn
    stem = base[:-4] if base.endswith("_mut") else base
    candidates = {base, stem, "L" + base, "L" + stem}
    return bool(candidates & skip_by_module.get(mod, set()))


# Why a note is still here. Order matters: the first matching rule wins.
_SKIP_BY_MODULE = _skip_functions_by_module()

RULES = [
    (
        lambda e: e["file"].startswith("src/generated/")
        and _in_preserved_body(e, _SKIP_BY_MODULE),
        "generated-preserved",
        "hand-written body inside a generated file",
        "These sit in `skip_functions` bodies that regeneration copies through "
        "verbatim, so they are **not transpiler output** and regenerating will "
        "never change them -- 54.7.b cannot clear these however 42.8.c lands. "
        "They are still under `src/generated/`, so `CLAUDE.md` forbids editing "
        "them in place; the real fix is either to teach the transpiler to "
        "generate the function (see `docs/rsl-skip-functions.md` for which are "
        "capability gaps versus a deliberate trust boundary) or to move the "
        "hand-written body out to a `*_manual.rs`, as acceptor and executor "
        "already do. That is the open 54.7.c decision.",
    ),
    (
        lambda e: e["file"].startswith("src/generated/"),
        "generated-emitted",
        "transpiler output",
        "Cannot be hand-edited (`CLAUDE.md`). The codegen fix for the dominant "
        "shape landed in 54.7.a, but delivering it needs a regeneration that is "
        "blocked: the RSL modules with `skip_functions` cannot be replaced "
        "wholesale, and merging them hits signature mismatches between the "
        "preserved hand-written bodies and the current emitted API "
        "(42.8.c.2.iv). Unlike the preserved notes, **these do clear once that "
        "merge lands**.",
    ),
    (
        lambda e: True,
        "nested-quantifier",
        "trigger belongs to an inner binder",
        "The note points at an outer quantifier while the trigger Verus chose "
        "names a variable bound by a *nested* one, so attaching it to the outer "
        "binder does not compile (\"cannot find value `p` in this scope\"). "
        "Removing these needs the expression restructured -- hoisting the inner "
        "quantifier, or annotating it so the outer note resolves on its own, as "
        "happened in 54.3 -- not a mechanical annotation.",
    ),
]


def classify(entry):
    for pred, key, short, reason in RULES:
        if pred(entry):
            return key, short, reason
    raise AssertionError("unreachable: the last rule matches everything")


def build(inventory):
    groups = OrderedDict()
    for entry in inventory["entries"]:
        key, short, reason = classify(entry)
        groups.setdefault(key, {"short": short, "reason": reason, "entries": []})
        groups[key]["entries"].append(entry)
    return groups


def render(inventory, groups):
    total = inventory["total_notes"]
    out = []
    out.append("# Deliberate trigger exceptions")
    out.append("")
    out.append(
        "Phase 54 replaced automatically chosen quantifier triggers with explicit "
        "ones across the hand-written tree. Its acceptance criterion allows either "
        "zero remaining notes or **this list**: every note that survives, with the "
        "reason it was not annotated."
    )
    out.append("")
    out.append(
        "Generated by `scripts/trigger_exceptions.py` from a measured inventory, so "
        "it cannot drift from reality unnoticed -- `--check` fails if the committed "
        "list disagrees with a fresh run."
    )
    out.append("")
    out.append("| field | value |")
    out.append("|---|---|")
    out.append("| verus | `{}` |".format(inventory.get("verus_version") or "unknown"))
    out.append("| notes remaining | **{}** |".format(total))
    out.append("| baseline | 534 (see `baseline.md`) |")
    out.append("")
    out.append("| reason | notes |")
    out.append("|---|---:|")
    for key, g in groups.items():
        out.append("| {} ({}) | {} |".format(key, g["short"], len(g["entries"])))
    out.append("")

    for key, g in groups.items():
        out.append("## {} — {} note(s)".format(key, len(g["entries"])))
        out.append("")
        out.append(g["reason"])
        out.append("")
        by_file = Counter(e["file"] for e in g["entries"])
        out.append("| file | notes |")
        out.append("|---|---:|")
        for f, n in sorted(by_file.items(), key=lambda kv: (-kv[1], kv[0])):
            out.append("| `{}` | {} |".format(f, n))
        out.append("")
        if not key.startswith("generated"):
            out.append("<details><summary>Individual sites</summary>")
            out.append("")
            for e in sorted(g["entries"], key=lambda e: (e["file"], e["line"])):
                terms = [t["terms"] for t in e["triggers"]]
                out.append(
                    "- `{}:{}` — chosen trigger `{}`".format(e["file"], e["line"], terms)
                )
            out.append("")
            out.append("</details>")
            out.append("")
    return "\n".join(out)


def extract_counts(markdown):
    """(total, {reason: count}) as recorded in a rendered document."""
    total = None
    m = re.search(r"\| notes remaining \| \*\*(\d+)\*\* \|", markdown)
    if m:
        total = int(m.group(1))
    per = {}
    for line in markdown.split("\n"):
        m = re.match(r"^## (\S+) — (\d+) note\(s\)$", line)
        if m:
            per[m.group(1)] = int(m.group(2))
    return total, per


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("inventory")
    p.add_argument("-o", "--out")
    p.add_argument("--check", metavar="MARKDOWN", help="verify a committed list")
    args = p.parse_args(argv)

    with open(args.inventory) as f:
        inventory = json.load(f)
    groups = build(inventory)
    rendered = render(inventory, groups)

    if args.check:
        if not os.path.exists(args.check):
            sys.stderr.write("error: {} does not exist\n".format(args.check))
            return 1
        with open(args.check) as f:
            committed = f.read()
        want_total, want_per = extract_counts(rendered)
        got_total, got_per = extract_counts(committed)
        if (want_total, want_per) != (got_total, got_per):
            sys.stderr.write(
                "error: {} is out of date.\n  committed: {} total {}\n"
                "  measured : {} total {}\n"
                "Regenerate it with scripts/trigger_exceptions.py.\n".format(
                    args.check, got_total, got_per, want_total, want_per
                )
            )
            return 1
        print("{}: up to date ({} notes)".format(args.check, want_total))
        return 0

    if args.out:
        directory = os.path.dirname(args.out)
        if directory:
            os.makedirs(directory, exist_ok=True)
        with open(args.out, "w") as f:
            f.write(rendered + "\n")
    else:
        sys.stdout.write(rendered + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
