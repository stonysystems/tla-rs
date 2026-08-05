#!/usr/bin/env python3
"""Structural drift guard for the checked-in model-check artifacts (Phase 37.2.1.j).

The CI evidence job regenerates `reports/model_check/` and checks that every
path referenced by the status doc exists. It deliberately does **not** diff the
result against git, because `elapsed_ms` and friends are wall-clock and differ
per runner — a raw diff would be permanently red.

The consequence, found in 37.2.1.i, is that everything *else* rots silently.
The committed artifacts had been missing telemetry fields for months, carried
`../src/...` paths from a run in the wrong directory, and shipped an
`OPTIMIZATION_DELTAS.md` row that contradicted a state-count fix landed in May.

This script is the missing middle: regenerate, then diff **normalized**
artifacts — volatile keys removed, everything else compared exactly. Timing
noise passes; a changed state count, a new telemetry field, or a wrong-cwd path
fails, which is precisely the set of changes that should be reviewed and
committed rather than discovered a quarter later.

Usage
-----
    ./scripts/run_model_check_matrix.sh          # regenerate in place
    scripts/check_model_check_drift.py           # compare against HEAD

    scripts/check_model_check_drift.py --ref origin/main --json
    scripts/check_model_check_drift.py --list-volatile
"""

import argparse
import json
import os
import re
import subprocess
import sys
from collections import OrderedDict

# Wall-clock / host-dependent keys. Dropped before comparison.
#
# NOTE the explicit list rather than a `_ms$` rule: `timeout_ms` also ends in
# `_ms` but is a *configuration input*, so a change to it is exactly the kind
# of drift this guard must catch. A suffix heuristic would silence it.
VOLATILE_KEYS = frozenset(
    [
        "elapsed_ms",
        "cumulative_solve_elapsed_ms",
        "candidate_generation_evaluation_ms",
        "dedup_hashing_normalization_ms",
        "initial_state_construction_ms",
        "invariant_evaluation_ms",
        "model_config_resolution_ms",
        "report_serialization_output_ms",
        "source_ingestion_parsing_ms",
        "successor_solving_ms",
        # The whole per-phase timing subtree.
        "timing",
    ]
)

# Keys that end in `_ms` but must NOT be treated as volatile.
DELIBERATE_MS_KEEPS = frozenset(["timeout_ms"])

# Volatile lines in the non-JSON artifacts.
VOLATILE_LINE_RES = [re.compile(r"^\s*git_rev:")]


def strip_volatile(obj):
    """Recursively drop volatile keys, preserving order elsewhere."""
    if isinstance(obj, dict):
        out = OrderedDict()
        for k, v in obj.items():
            if k in VOLATILE_KEYS:
                continue
            out[k] = strip_volatile(v)
        return out
    if isinstance(obj, list):
        return [strip_volatile(v) for v in obj]
    return obj


def normalize(path, text):
    """Canonical, comparable form of one artifact."""
    if path.endswith(".json"):
        try:
            data = json.loads(text)
        except json.JSONDecodeError as e:
            raise ValueError("{}: invalid JSON: {}".format(path, e))
        return json.dumps(strip_volatile(data), indent=2, sort_keys=True)
    if path.endswith(".jsonl"):
        lines = []
        for line in text.splitlines():
            if not line.strip():
                continue
            lines.append(
                json.dumps(strip_volatile(json.loads(line)), sort_keys=True)
            )
        return "\n".join(lines)
    return "\n".join(
        line
        for line in text.splitlines()
        if not any(r.search(line) for r in VOLATILE_LINE_RES)
    )


def flatten(obj, prefix=""):
    """Leaf paths of a JSON value, for pinpointing what changed."""
    if isinstance(obj, dict):
        for k, v in obj.items():
            yield from flatten(v, "{}/{}".format(prefix, k))
    elif isinstance(obj, list):
        for i, v in enumerate(obj):
            yield from flatten(v, "{}[{}]".format(prefix, i))
    else:
        yield prefix, obj


def describe_json_diff(old_text, new_text, limit=12):
    """Key paths that differ between two normalized JSON documents."""
    try:
        old = dict(flatten(json.loads(old_text)))
        new = dict(flatten(json.loads(new_text)))
    except json.JSONDecodeError:
        return ["(unparseable JSON; raw text differs)"]
    notes = []
    for key in sorted(set(old) | set(new)):
        if key not in old:
            notes.append("+ {} = {!r}".format(key, new[key]))
        elif key not in new:
            notes.append("- {} (was {!r})".format(key, old[key]))
        elif old[key] != new[key]:
            notes.append("~ {}: {!r} -> {!r}".format(key, old[key], new[key]))
    if len(notes) > limit:
        extra = len(notes) - limit
        notes = notes[:limit] + ["... {} more".format(extra)]
    return notes


def describe_text_diff(old_text, new_text, limit=12):
    old_lines = old_text.splitlines()
    new_lines = new_text.splitlines()
    notes = []
    for i in range(max(len(old_lines), len(new_lines))):
        o = old_lines[i] if i < len(old_lines) else None
        n = new_lines[i] if i < len(new_lines) else None
        if o != n:
            if o is None:
                notes.append("+ {}".format(n))
            elif n is None:
                notes.append("- {}".format(o))
            else:
                notes.append("~ {!r} -> {!r}".format(o, n))
    if len(notes) > limit:
        notes = notes[:limit] + ["... {} more".format(len(notes) - limit)]
    return notes


def git_show(ref, path):
    """Committed content of `path` at `ref`, or None if it is not tracked."""
    r = subprocess.run(
        ["git", "show", "{}:{}".format(ref, path)],
        capture_output=True,
        text=True,
    )
    return r.stdout if r.returncode == 0 else None


MANIFEST_NAME = "MANIFEST.txt"


def manifest_scope(directory, manifest_text):
    """Files the matrix script generates, per the manifest it writes.

    Scoping to the manifest matters: `reports/model_check/` also holds
    hand-written documentation (README.md) and exports produced by other
    scripts (parity/**). Diffing those against HEAD would fail on any ordinary
    doc edit, which is noise that gets a guard switched off. Reading the
    manifest also means a newly generated artifact is guarded automatically,
    because the script that produces it lists it.
    """
    paths = [os.path.join(directory, MANIFEST_NAME)]
    in_list = False
    for line in manifest_text.splitlines():
        if re.match(r"^\s*artifacts:\s*$", line):
            in_list = True
            continue
        if in_list:
            m = re.match(r"^\s*-\s+(\S+)\s*$", line)
            if m:
                paths.append(os.path.join(directory, m.group(1)))
            elif line.strip():
                in_list = False
    return paths


def tracked_files(directory, ref, all_files=False):
    if not all_files:
        manifest = git_show(ref, os.path.join(directory, MANIFEST_NAME))
        if manifest is not None:
            return manifest_scope(directory, manifest)
    r = subprocess.run(
        ["git", "ls-tree", "-r", "--name-only", ref, "--", directory],
        capture_output=True,
        text=True,
        check=True,
    )
    return [p for p in r.stdout.splitlines() if p.strip()]


def check(directory="reports/model_check", ref="HEAD", all_files=False):
    results = []
    for path in tracked_files(directory, ref, all_files=all_files):
        committed = git_show(ref, path)
        if committed is None:
            continue
        if not os.path.exists(path):
            results.append(
                OrderedDict(
                    [("file", path), ("status", "missing"), ("detail", ["file was deleted"])]
                )
            )
            continue
        with open(path, errors="replace") as f:
            current = f.read()
        try:
            old = normalize(path, committed)
            new = normalize(path, current)
        except ValueError as e:
            results.append(
                OrderedDict(
                    [("file", path), ("status", "unparseable"), ("detail", [str(e)])]
                )
            )
            continue
        if old == new:
            continue
        detail = (
            describe_json_diff(old, new)
            if path.endswith(".json")
            else describe_text_diff(old, new)
        )
        results.append(
            OrderedDict([("file", path), ("status", "drifted"), ("detail", detail)])
        )
    return results


def render(results, directory, ref):
    if not results:
        return (
            "model-check artifacts match {} after normalization "
            "(timing-only differences ignored).\n".format(ref)
        )
    out = [
        "Structural drift between the regenerated artifacts and {}.".format(ref),
        "",
        "Volatile keys were ignored, so these are real changes: state counts,",
        "telemetry fields, paths or stop reasons. Review them, then commit the",
        "regenerated artifacts so the checked-in evidence matches the code.",
        "",
    ]
    for r in results:
        out.append("{}  [{}]".format(r["file"], r["status"]))
        for line in r["detail"]:
            out.append("    {}".format(line))
        out.append("")
    return "\n".join(out)


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--dir", default="reports/model_check")
    p.add_argument("--ref", default="HEAD", help="git ref to compare against")
    p.add_argument("--json", action="store_true", help="emit findings as JSON")
    p.add_argument(
        "--list-volatile",
        action="store_true",
        help="print the ignored keys and exit",
    )
    p.add_argument(
        "--warn-only",
        action="store_true",
        help="report drift but exit 0",
    )
    p.add_argument(
        "--all-files",
        action="store_true",
        help="compare every tracked file in the directory, not just the "
        "artifacts named in MANIFEST.txt (includes hand-written docs)",
    )
    args = p.parse_args(argv)

    if args.list_volatile:
        print("volatile keys (ignored):")
        for k in sorted(VOLATILE_KEYS):
            print("  {}".format(k))
        print("deliberately NOT volatile despite the _ms suffix:")
        for k in sorted(DELIBERATE_MS_KEEPS):
            print("  {}".format(k))
        print("volatile line patterns:")
        for r in VOLATILE_LINE_RES:
            print("  {}".format(r.pattern))
        return 0

    results = check(args.dir, args.ref, all_files=args.all_files)
    if args.json:
        print(json.dumps({"ref": args.ref, "dir": args.dir, "findings": results}, indent=2))
    else:
        sys.stdout.write(render(results, args.dir, args.ref))
    return 1 if results and not args.warn_only else 0


if __name__ == "__main__":
    sys.exit(main())
