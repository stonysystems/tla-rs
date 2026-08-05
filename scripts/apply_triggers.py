#!/usr/bin/env python3
"""Insert explicit `#![trigger ...]` annotations from a trigger inventory (Phase 54.5+).

Phase 54 replaces automatically chosen quantifier triggers with explicit ones.
The safe way to do that is to write down **exactly what Verus already chose**:
behaviour is then preserved by construction, and `trigger_inventory.py diff`
should report the notes as `removed` with `changed = 0`. That is mechanical
enough to script, and there are hundreds of sites left (54.5-54.8), so scripting
it is also the only way the batches stay reviewable.

The inventory records, per note, the source location of the quantifier and the
terms Verus picked. This tool finds the binder at that location and inserts
`#![trigger t1, t2]` immediately after it.

It is deliberately conservative — it skips rather than guesses:

  * a site that already carries a trigger annotation
  * a trigger term containing a closure (`|`), which Verus rejects with
    "triggers cannot contain let/forall/exists/lambda/choose" even though it
    chose that term itself
  * a location where no `forall`/`exists`/`choose` binder can be found

Every skip is reported with a reason, so nothing disappears quietly.

Usage
-----
    scripts/apply_triggers.py reports/triggers/baseline.json --dry-run \\
        --filter src/protocol/RSL/proposer.rs
    scripts/apply_triggers.py reports/triggers/baseline.json \\
        --filter src/protocol/RSL/

Then re-verify and diff; never trust the edit without a verification pass.
"""

import argparse
import json
import os
import re
import sys
from collections import OrderedDict

QUANT_RE = re.compile(r"\b(forall|exists|choose)\s*\|")
HAS_TRIGGER_RE = re.compile(r"#!?\[\s*(trigger|auto)\b")
OPENERS = "([{"
CLOSERS = ")]}"


def binder_end(text, start):
    """Offset just past the closing `|` of a binder list starting at `start`."""
    depth = 0
    i = start
    limit = min(len(text), start + 2000)
    while i < limit:
        c = text[i]
        if c in OPENERS:
            depth += 1
        elif c in CLOSERS:
            if depth == 0:
                return None
            depth -= 1
        elif c == "|" and depth == 0:
            return i + 1
        i += 1
    return None


def line_offsets(text):
    offsets, pos = [0], 0
    for line in text.split("\n")[:-1]:
        pos += len(line) + 1
        offsets.append(pos)
    return offsets


def binder_vars(text, start, end):
    """Names bound by the binder list occupying [start, end).

    `|opn: OperationNumber, p: RslPacket|` binds `opn` and `p`. Splitting on
    commas and taking the identifier *before* the colon matters: a regex that
    scans for `name:` or `name|` also picks up the type after the colon, which
    made this check reject every typed binder as "nested".
    """
    inner = text[start:end].rstrip("|")
    names, depth, current = [], 0, ""
    for ch in inner:
        if ch in OPENERS:
            depth += 1
        elif ch in CLOSERS:
            depth -= 1
        if ch == "," and depth == 0:
            names.append(current)
            current = ""
        else:
            current += ch
    names.append(current)
    out = []
    for entry in names:
        name = entry.split(":", 1)[0].strip()
        if re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", name):
            out.append(name)
    return out


def find_binder(text, line):
    """(binder_end_offset, kind) for the quantifier at or after `line`."""
    offsets = line_offsets(text)
    if line - 1 >= len(offsets):
        return None
    start = offsets[line - 1]
    # The note points at the start of the quantifier expression, but the binder
    # may be a line or two later when the expression is wrapped.
    window = text[start : start + 4000]
    m = QUANT_RE.search(window)
    if not m:
        return None
    binder_start = start + m.end()
    end = binder_end(text, binder_start)
    if end is None:
        return None
    return end, m.group(1), binder_vars(text, binder_start, end)


def annotation(groups):
    """`#![trigger a, b]` for one group; repeated attributes for alternatives."""
    return " ".join("#![trigger " + ", ".join(g) + "]" for g in groups)


def plan_edits(inventory, filter_prefix=None):
    """Ordered edit plan; later offsets first so earlier ones stay valid."""
    by_file = OrderedDict()
    for entry in inventory["entries"]:
        path = entry["file"]
        if filter_prefix and not path.startswith(filter_prefix):
            continue
        by_file.setdefault(path, []).append(entry)

    plans = []
    for path, entries in by_file.items():
        if not os.path.exists(path):
            plans.append((path, [], [("<file>", "file not found")]))
            continue
        text = open(path).read()
        edits, skips = [], []
        for entry in entries:
            site = "{}:{}".format(path, entry["line"])
            # One annotation per trigger GROUP. Verus records alternatives as
            # separate triggers (`#![trigger a] #![trigger b]`, either may
            # fire) and conjunctions as several terms in one trigger
            # (`#![trigger a, b]`, both needed to bind the variables).
            # Flattening the groups into a single multi-term trigger is
            # strictly more restrictive and breaks proofs -- it did, on
            # state_machine.rs, which records [[replies[i]], [batch[i]]].
            groups = [tr["terms"] for tr in entry["triggers"] if tr["terms"]]
            terms = [t for g in groups for t in g]
            if not terms:
                skips.append((site, "no trigger terms recorded"))
                continue
            if any("|" in t for t in terms):
                skips.append(
                    (site, "trigger term contains a closure; Verus forbids it")
                )
                continue
            found = find_binder(text, entry["line"])
            if found is None:
                skips.append((site, "no forall/exists/choose binder found"))
                continue
            end, _kind, bound = found
            # The trigger must bind the quantifier's own variables. When it
            # mentions none of them, the note's location points at an outer
            # expression while the chosen trigger belongs to a *nested*
            # quantifier -- attaching it here is a compile error
            # ("cannot find value `p` in this scope"), which is how this was
            # found on refinement_proof/state_machine.rs.
            mentioned = {
                w
                for t in terms
                for w in re.findall(r"[A-Za-z_][A-Za-z_0-9]*", t)
            }
            missing = [v for v in bound if v not in mentioned]
            if bound and missing:
                skips.append(
                    (
                        site,
                        "trigger does not mention bound variable(s) {}; "
                        "it belongs to a nested quantifier".format(
                            ", ".join(missing)
                        ),
                    )
                )
                continue
            following = text[end : end + 200]
            if HAS_TRIGGER_RE.search(following.split("\n")[0]) or HAS_TRIGGER_RE.match(
                following.lstrip()
            ):
                skips.append((site, "already annotated"))
                continue
            edits.append((end, annotation(groups), site))
        # De-duplicate: two notes can share one binder (nested spans).
        seen, unique = set(), []
        for off, ann, site in sorted(edits, key=lambda e: -e[0]):
            if off in seen:
                skips.append((site, "shares a binder with another note"))
                continue
            seen.add(off)
            unique.append((off, ann, site))
        plans.append((path, unique, skips))
    return plans


def apply_plan(plans, dry_run=False):
    applied = skipped = 0
    for path, edits, skips in plans:
        for site, reason in skips:
            print("  skip {}: {}".format(site, reason))
            skipped += 1
        if not edits:
            continue
        text = open(path).read()
        for off, ann, site in edits:  # already sorted descending
            text = text[:off] + " " + ann + text[off:]
            applied += 1
        if not dry_run:
            open(path, "w").write(text)
        print(
            "  {} {}: {} annotation(s)".format(
                "would edit" if dry_run else "edited", path, len(edits)
            )
        )
    return applied, skipped


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("inventory", help="trigger inventory JSON")
    p.add_argument("--filter", help="only touch paths with this prefix")
    p.add_argument("--dry-run", action="store_true")
    args = p.parse_args(argv)

    with open(args.inventory) as f:
        inventory = json.load(f)
    plans = plan_edits(inventory, args.filter)
    applied, skipped = apply_plan(plans, dry_run=args.dry_run)
    print("\n{} annotation(s), {} skipped".format(applied, skipped))
    return 0


if __name__ == "__main__":
    sys.exit(main())
