#!/usr/bin/env python3
"""Static inventory of quantifier sites and their trigger annotations (Phase 54).

This is the **work-list** tool. Its companion, `trigger_inventory.py`, is the
**measurement** tool: it reports what Verus actually chose, and it needs a
verification log from the pinned verifier. This one needs only the source, so
the annotation batches (Phase 54.3 onwards) can be planned, split per file and
tracked without waiting for a CI run.

    what it counts        every `forall|...|` / `exists|...|` in the source, and
                          whether a `#[trigger]` / `#![trigger(...)]` / `#![auto]`
                          annotation governs it
    what it does NOT      predict the number of `automatically chose triggers`
                          notes

Those two numbers are different on purpose. Verus in its default `selective`
mode only reports the choices it considers ambiguous, so an unannotated
quantifier need not produce a note. Treat this output as "sites that Phase 54
may have to touch", an upper bound on the work, and `trigger_inventory.py`
output as "what Verus is actually guessing at".

Classification per site:

    annotated    a trigger annotation governs it
    auto         `#![auto]` — automatic selection was requested deliberately
    ambiguous    an annotation appears in scope, but only after a nested
                 quantifier, so it may belong to the inner one
    unannotated  no annotation anywhere in scope

Usage
-----
    scripts/trigger_sites.py src/protocol/RSL src/implementation/RSL
    scripts/trigger_sites.py src --json -o reports/triggers/sites.json
    scripts/trigger_sites.py src --markdown
"""

import argparse
import json
import os
import re
import sys
from collections import Counter, OrderedDict

SCHEMA = "trigger-sites/v1"

QUANT_RE = re.compile(r"\b(forall|exists)\s*\|")
TRIGGER_RE = re.compile(r"#!?\[\s*(trigger|auto)\b")
OPENERS = "([{"
CLOSERS = ")]}"

# A quantifier body longer than this is almost certainly a runaway scan.
MAX_SCAN_CHARS = 20000


def strip_comments(text):
    """Blank out // and /* */ comments, keeping offsets stable."""
    out = list(text)
    i = 0
    n = len(text)
    in_line = in_block = in_str = False
    while i < n:
        c = text[i]
        nxt = text[i + 1] if i + 1 < n else ""
        if in_line:
            if c == "\n":
                in_line = False
            else:
                out[i] = " "
        elif in_block:
            if c == "*" and nxt == "/":
                out[i] = out[i + 1] = " "
                i += 2
                continue
            if c != "\n":
                out[i] = " "
        elif in_str:
            if c == "\\":
                out[i] = " "
                if i + 1 < n and text[i + 1] != "\n":
                    out[i + 1] = " "
                i += 2
                continue
            if c == '"':
                in_str = False
            out[i] = " " if c != "\n" else c
        elif c == "/" and nxt == "/":
            in_line = True
            out[i] = " "
        elif c == "/" and nxt == "*":
            in_block = True
            out[i] = out[i + 1] = " "
            i += 2
            continue
        elif c == '"':
            in_str = True
            out[i] = " "
        i += 1
    return "".join(out)


def binder_end(text, start):
    """Offset just past the closing `|` of a quantifier binder list.

    `start` is the offset just after the opening `|`. Commas separate binders
    (`forall |x1: X, x2: X|`), so the body scan must not begin until the list
    is closed — otherwise the first binder comma looks like the end of the
    quantifier and any `#![trigger ...]` that follows is missed entirely.
    """
    depth = 0
    i = start
    limit = min(len(text), start + 2000)
    while i < limit:
        c = text[i]
        if c in OPENERS:
            depth += 1
        elif c in CLOSERS:
            if depth == 0:
                return i
            depth -= 1
        elif c == "|" and depth == 0:
            # `||` cannot occur inside a binder list, so a doubled bar means we
            # already left it; treat the first bar as the terminator either way.
            return i + 1
        i += 1
    return start


def scope_end(text, start):
    """End offset of the quantifier expression beginning at `start`.

    Walks forward until the bracket that encloses the quantifier closes, or a
    `;` / `,` is reached at the starting depth — the point past which anything
    written can no longer be part of this quantifier.
    """
    depth = 0
    i = start
    limit = min(len(text), start + MAX_SCAN_CHARS)
    while i < limit:
        c = text[i]
        if c in OPENERS:
            depth += 1
        elif c in CLOSERS:
            if depth == 0:
                return i
            depth -= 1
        elif depth == 0 and c in ";,":
            return i
        i += 1
    return limit


def classify(scope):
    """Classify a quantifier scope by the annotation that governs it."""
    ann = TRIGGER_RE.search(scope)
    if ann is None:
        return "unannotated"
    nested = QUANT_RE.search(scope)
    if ann.group(1) == "auto" and (nested is None or ann.start() < nested.start()):
        return "auto"
    if nested is not None and nested.start() < ann.start():
        # The annotation could belong to the inner quantifier; say so rather
        # than guess. These are the sites a human must eyeball.
        return "ambiguous"
    return "annotated"


def scan_text(text):
    """Yield (line, kind, classification) for every quantifier in a file."""
    clean = strip_comments(text)
    results = []
    for m in QUANT_RE.finditer(clean):
        body_start = binder_end(clean, m.end())
        end = scope_end(clean, body_start)
        scope = clean[body_start:end]
        results.append(
            OrderedDict(
                [
                    ("line", clean.count("\n", 0, m.start()) + 1),
                    ("kind", m.group(1)),
                    ("classification", classify(scope)),
                ]
            )
        )
    return results


def iter_rust_files(roots):
    for root in roots:
        if os.path.isfile(root):
            yield root
            continue
        for dirpath, dirnames, filenames in os.walk(root):
            dirnames[:] = sorted(d for d in dirnames if d not in ("target", ".git"))
            for name in sorted(filenames):
                if name.endswith(".rs"):
                    yield os.path.join(dirpath, name)


def build_inventory(roots, repo_root=None):
    files = OrderedDict()
    totals = Counter()
    by_dir = OrderedDict()

    for path in iter_rust_files(roots):
        with open(path, errors="replace") as f:
            text = f.read()
        sites = scan_text(text)
        if not sites:
            continue
        rel = os.path.relpath(path, repo_root) if repo_root else path
        counts = Counter(s["classification"] for s in sites)
        files[rel] = OrderedDict(
            [
                ("total", len(sites)),
                ("unannotated", counts["unannotated"]),
                ("ambiguous", counts["ambiguous"]),
                ("annotated", counts["annotated"]),
                ("auto", counts["auto"]),
                ("sites", sites),
            ]
        )
        totals.update(counts)
        totals["total"] += len(sites)
        d = os.path.dirname(rel) or "."
        agg = by_dir.setdefault(d, Counter())
        agg.update(counts)
        agg["total"] += len(sites)

    return OrderedDict(
        [
            ("schema", SCHEMA),
            ("roots", list(roots)),
            ("file_count", len(files)),
            ("totals", OrderedDict(sorted(totals.items()))),
            (
                "by_dir",
                OrderedDict(
                    (d, OrderedDict(sorted(c.items()))) for d, c in sorted(by_dir.items())
                ),
            ),
            ("files", files),
        ]
    )


def render(inv, top=30):
    t = inv["totals"]
    out = []
    out.append("# Quantifier sites and trigger annotations")
    out.append("")
    out.append(
        "Static source scan. **Not** a prediction of `automatically chose triggers` "
        "note counts — Verus's default `selective` mode only reports the choices it "
        "finds ambiguous. This is the upper bound on sites Phase 54 may touch."
    )
    out.append("")
    out.append("| classification | sites |")
    out.append("|---|---:|")
    for key in ("total", "unannotated", "ambiguous", "annotated", "auto"):
        out.append("| {} | {} |".format(key, t.get(key, 0)))
    out.append("")
    out.append("## By directory")
    out.append("")
    out.append("| directory | total | unannotated | ambiguous | annotated | auto |")
    out.append("|---|---:|---:|---:|---:|---:|")
    for d, c in sorted(
        inv["by_dir"].items(), key=lambda kv: (-kv[1].get("unannotated", 0), kv[0])
    ):
        out.append(
            "| `{}` | {} | {} | {} | {} | {} |".format(
                d,
                c.get("total", 0),
                c.get("unannotated", 0),
                c.get("ambiguous", 0),
                c.get("annotated", 0),
                c.get("auto", 0),
            )
        )
    out.append("")
    out.append("## Files with the most unannotated sites")
    out.append("")
    out.append("| file | unannotated | total |")
    out.append("|---|---:|---:|")
    ranked = sorted(
        inv["files"].items(), key=lambda kv: (-kv[1]["unannotated"], kv[0])
    )
    for path, c in ranked[:top]:
        if c["unannotated"] == 0:
            break
        out.append("| `{}` | {} | {} |".format(path, c["unannotated"], c["total"]))
    out.append("")
    return "\n".join(out)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("roots", nargs="+", help="files or directories to scan")
    parser.add_argument("-o", "--out")
    parser.add_argument("--json", action="store_true", help="emit JSON")
    parser.add_argument(
        "--repo-root", default=".", help="make paths relative to this directory"
    )
    parser.add_argument("--top", type=int, default=30)
    args = parser.parse_args(argv)

    inv = build_inventory(args.roots, repo_root=args.repo_root)
    text = json.dumps(inv, indent=2) if args.json else render(inv, top=args.top)
    if args.out:
        directory = os.path.dirname(args.out)
        if directory:
            os.makedirs(directory, exist_ok=True)
        with open(args.out, "w") as f:
            f.write(text if text.endswith("\n") else text + "\n")
    else:
        sys.stdout.write(text if text.endswith("\n") else text + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
