#!/usr/bin/env python3
"""Verus per-module verification timing inventory and regression diff (Phase 54.2.c).

Phase 54 replaces automatically chosen quantifier triggers with explicit
`#[trigger]` annotations. A batch of those edits can pass verification and
still be a regression: an over-permissive trigger makes the solver instantiate
more terms, and the module that used to verify in 8 s now takes 20 s. Nothing
in a pass/fail check sees that; the acceptance criterion for the phase is
therefore stated in wall-clock terms —

    no module's verification wall-clock regresses more than 20% against the
    54.2 baseline

— and this tool is what makes that criterion checkable.

Input is the text output of `verus --time-expanded` (this repo passes it via
`scons --verus-extra-args="--time-expanded"`), which ends with:

    total-time:             368 ms
        rust-time:                  94 ms
        verification-time:         264 ms
        ...
    verify-crate-time-breakdown
        total verify-time:            157 ms   (3 threads)
          1. alpha                                            54 ms
          2.                                                  53 ms
          3. beta                                             48 ms
            total air-time:                98 ms   (3 threads)
          ...

The unnamed row is the crate root module; it is recorded as `<root>`.

Modes:

    parse   verification log         -> JSON timing inventory
    report  JSON inventory           -> Markdown summary
    diff    two JSON inventories     -> per-module regression report

Usage
-----
    scons --verus-path=... --skip-dotnet --verus-extra-args="--time-expanded" \\
        2>&1 | tee verus-verify.log

    scripts/verus_timing.py parse verus-verify.log \\
        --label "0.2026.08.02 baseline" -o reports/triggers/timing-baseline.json

    scripts/verus_timing.py diff reports/triggers/timing-baseline.json new.json \\
        --max-regression-pct 20 --min-ms 500
"""

import argparse
import json
import os
import re
import sys
from collections import OrderedDict

SCHEMA = "verus-timing/v1"
ROOT_MODULE = "<root>"

VERSION_RE = re.compile(r"^\s*Version:\s*(\S+)\s*$")
# `total-time:   368 ms    (estimated total cpu time 467 ms)` / `  rust-time:  94 ms`
TOTAL_RE = re.compile(
    r"^(\s*)([a-z][a-z0-9-]*):\s+(\d+)\s*ms\s*(?:\([^)]*\))?\s*$"
)
BREAKDOWN_HEADER = "verify-crate-time-breakdown"
# `        total verify-time:            157 ms   (3 threads)`
SECTION_RE = re.compile(
    r"^\s*total\s+(?P<name>[a-z-]+):\s+(?P<ms>\d+)\s*ms"
    r"(?:,\s*(?P<rlimit>\d+)\s*rlimit)?\s*(?:\((?P<threads>\d+)\s*threads?\))?\s*$"
)
# `      1. alpha                                            54 ms`
# `      2.                                                  53 ms`
# `                3. beta                                 0 ms,    1568 rlimit`
ROW_RE = re.compile(
    r"^\s*\d+\.\s*(?P<module>\S*)\s+(?P<ms>\d+)\s*ms(?:,\s*(?P<rlimit>\d+)\s*rlimit)?\s*$"
)

# Section name in the log -> field name in the inventory.
SECTIONS = OrderedDict(
    [
        ("verify-time", "verify_ms"),
        ("air-time", "air_ms"),
        ("smt-init", "smt_init_ms"),
        ("smt-run", "smt_run_ms"),
    ]
)

# Noise floor for the 20% gate, chosen by measurement rather than taste.
# Across three runs of *identical* code on this crate (127-thread parallel
# verification), per-module spread was:
#
#     >= 500 ms   40 modules, max spread 22.6%  <- one module exceeds the gate
#     >= 1000 ms  28 modules, max spread 16.8%  <- gate is noise-free
#     >= 5000 ms  13 modules, max spread 16.8%
#
# So 1000 ms is the smallest floor at which a 20% threshold cannot fire on
# noise alone, and it still covers every module where a real regression would
# matter. Below it, report but never fail.
DEFAULT_MIN_MS = 1000



# ---------------------------------------------------------------------------
# parse
# ---------------------------------------------------------------------------


def parse_log(text):
    """Return (totals, modules) from a `--time-expanded` log."""
    lines = text.splitlines()
    totals = OrderedDict()
    modules = OrderedDict()

    in_breakdown = False
    section = None
    for raw in lines:
        line = raw.rstrip()
        if line.strip() == BREAKDOWN_HEADER:
            in_breakdown = True
            section = None
            continue

        if not in_breakdown:
            m = TOTAL_RE.match(line)
            if m:
                totals[m.group(2)] = int(m.group(3))
            continue

        sec = SECTION_RE.match(line)
        if sec:
            name = sec.group("name")
            section = SECTIONS.get(name)
            totals.setdefault("breakdown-" + name, int(sec.group("ms")))
            if sec.group("threads"):
                totals.setdefault("threads", int(sec.group("threads")))
            continue

        row = ROW_RE.match(line)
        if row and section:
            module = row.group("module") or ROOT_MODULE
            entry = modules.setdefault(
                module,
                OrderedDict(
                    [("module", module)] + [(f, None) for f in SECTIONS.values()]
                ),
            )
            entry[section] = int(row.group("ms"))
            if row.group("rlimit") is not None:
                entry["rlimit"] = int(row.group("rlimit"))
            continue

        # A non-matching, non-indented line ends the breakdown block.
        if line and not line.startswith(" "):
            in_breakdown = False
            section = None

    return totals, modules


def extract_json_payload(text):
    """The `--output-json` object embedded in a log, or None.

    Verus writes diagnostics to stderr and the JSON report to stdout; a merged
    log therefore has the object starting at the first line that is exactly
    `{` and running to the end.
    """
    lines = text.split("\n")
    for i, line in enumerate(lines):
        if line == "{":
            try:
                return json.loads("\n".join(lines[i:]))
            except json.JSONDecodeError:
                return None
    return None


def parse_json_times(payload):
    """(totals, modules) from a `--output-json` payload.

    Strongly preferred over the text breakdown: `--time-expanded` prints only
    the top 3 modules per section, while the JSON carries every module. A
    per-module regression gate over 3 of 148 modules would be mostly decorative.
    """
    tm = payload.get("times-ms")
    if not tm:
        return None
    totals = OrderedDict()
    for key in ("total", "estimated-cpu-time", "total-verify", "num-threads"):
        if key in tm:
            totals[key] = tm[key]
    if isinstance(tm.get("verification"), dict):
        totals["verification-time"] = tm["verification"].get("total")
    if isinstance(tm.get("rust"), dict):
        totals["rust-time"] = tm["rust"].get("total")
    totals["total-time"] = tm.get("total")

    modules = OrderedDict()

    def absorb(entries, field, with_rlimit=False):
        # Verus emits one entry per verification chunk, so a module can appear
        # several times (148 entries / 142 modules on this crate). The module's
        # cost is their sum -- summing every entry reproduces the reported
        # `total-verify`, whereas keeping one entry silently under-reports the
        # very modules that were split because they are expensive.
        for e in entries or []:
            name = e.get("module") or ROOT_MODULE
            entry = modules.setdefault(
                name,
                OrderedDict(
                    [("module", name)] + [(f, None) for f in SECTIONS.values()]
                ),
            )
            entry[field] = (entry.get(field) or 0) + (e.get("time") or 0)
            if with_rlimit and e.get("rlimit") is not None:
                entry["rlimit"] = (entry.get("rlimit") or 0) + e["rlimit"]

    absorb(tm.get("total-verify-module-times"), "verify_ms")
    absorb((tm.get("air") or {}).get("module-times"), "air_ms")
    smt = tm.get("smt") or {}
    absorb(smt.get("smt-init-module-times"), "smt_init_ms")
    absorb(smt.get("smt-run-module-times"), "smt_run_ms", with_rlimit=True)
    return totals, modules


def detect_version(text):
    for line in text.splitlines():
        m = VERSION_RE.match(line)
        if m:
            return m.group(1)
    return None


def build_inventory(text, label=None, verus_version=None, source=None):
    parsed = None
    payload = extract_json_payload(text)
    if payload is not None:
        parsed = parse_json_times(payload)
        if verus_version is None:
            verus_version = (payload.get("verus") or {}).get("version")
    totals, modules = parsed if parsed else parse_log(text)
    ordered = OrderedDict(
        sorted(
            modules.items(),
            key=lambda kv: (-(kv[1].get("verify_ms") or 0), kv[0]),
        )
    )
    return OrderedDict(
        [
            ("schema", SCHEMA),
            ("label", label or ""),
            ("verus_version", verus_version or detect_version(text) or ""),
            ("source_log", source or ""),
            ("parsed_from", "output-json" if parsed else "time-expanded-text"),
            ("module_count", len(ordered)),
            ("total_verify_ms", sum((m.get("verify_ms") or 0) for m in ordered.values())),
            ("totals", totals),
            ("modules", ordered),
        ]
    )


# ---------------------------------------------------------------------------
# report
# ---------------------------------------------------------------------------


def render_report(inv, top=40):
    out = []
    out.append("# Verus verification timing")
    out.append("")
    out.append("| field | value |")
    out.append("|---|---|")
    out.append("| label | {} |".format(inv.get("label") or "(none)"))
    out.append("| verus version | {} |".format(inv.get("verus_version") or "(unknown)"))
    out.append("| source log | {} |".format(inv.get("source_log") or "(stdin)"))
    out.append("| modules | {} |".format(inv["module_count"]))
    out.append("| total verify time | {} ms |".format(inv["total_verify_ms"]))
    for key in ("total-time", "verification-time", "total-verify"):
        if key in inv["totals"]:
            out.append("| {} | {} ms |".format(key, inv["totals"][key]))
    out.append("")
    out.append("## Per module")
    out.append("")
    out.append("| module | verify ms | air ms | smt-init ms | smt-run ms | rlimit |")
    out.append("|---|---:|---:|---:|---:|---:|")
    items = list(inv["modules"].values())
    for m in items[:top]:
        out.append(
            "| `{}` | {} | {} | {} | {} | {} |".format(
                m["module"],
                fmt(m.get("verify_ms")),
                fmt(m.get("air_ms")),
                fmt(m.get("smt_init_ms")),
                fmt(m.get("smt_run_ms")),
                fmt(m.get("rlimit")),
            )
        )
    if len(items) > top:
        out.append("")
        out.append("_{} further modules omitted._".format(len(items) - top))
    out.append("")
    return "\n".join(out)


def fmt(v):
    return "-" if v is None else str(v)


# ---------------------------------------------------------------------------
# diff
# ---------------------------------------------------------------------------


def merge_min(inventories, label=None):
    """Element-wise minimum across runs of the same code.

    A single run is not a usable baseline. Verus verifies modules in parallel,
    so one module's wall-clock depends on what else was scheduled beside it:
    measured here, an untouched module read 1967 ms in the original baseline
    run but 2372-2490 ms across three later runs of that *same commit*. Taking
    the minimum gives the least-contended estimate of each module's real cost,
    which is the standard choice for timing benchmarks and the only one that
    makes a 20% per-module gate meaningful.
    """
    if not inventories:
        raise ValueError("no inventories to merge")
    merged = OrderedDict()
    for inv in inventories:
        for name, m in inv["modules"].items():
            cur = merged.setdefault(
                name,
                OrderedDict(
                    [("module", name)] + [(f, None) for f in SECTIONS.values()]
                ),
            )
            for field in list(SECTIONS.values()) + ["rlimit"]:
                v = m.get(field)
                if v is None:
                    continue
                cur[field] = v if cur.get(field) is None else min(cur[field], v)
    ordered = OrderedDict(
        sorted(merged.items(), key=lambda kv: (-(kv[1].get("verify_ms") or 0), kv[0]))
    )
    first = inventories[0]
    return OrderedDict(
        [
            ("schema", SCHEMA),
            ("label", label or first.get("label", "")),
            ("verus_version", first.get("verus_version", "")),
            ("source_log", "min of {} runs".format(len(inventories))),
            ("parsed_from", first.get("parsed_from", "")),
            ("runs_merged", len(inventories)),
            ("module_count", len(ordered)),
            (
                "total_verify_ms",
                sum((m.get("verify_ms") or 0) for m in ordered.values()),
            ),
            ("totals", first.get("totals", {})),
            ("modules", ordered),
        ]
    )


def confirm_regressions(delta, confirm, max_regression_pct=20.0,
                        min_ms=DEFAULT_MIN_MS,
                        field="verify_ms"):
    """Demote regressions that a second run of the same code does not reproduce.

    Verus verifies modules in parallel (127 threads on this box), so a module's
    wall-clock moves with contention: measured here, an *untouched* module read
    1967 / 2448 / 2241 ms across three runs of two code states. A single-sample
    20% threshold therefore flags modules nobody edited. Requiring the
    regression to appear against a second, independent run of the *new* code
    keeps the criterion meaningful without lowering it.
    """
    confirmed, unconfirmed = [], []
    for r in delta["regressions"]:
        entry = confirm["modules"].get(r["module"])
        c_ms = (entry or {}).get(field)
        if c_ms is None:
            unconfirmed.append(dict(r, confirm_ms=None))
            continue
        base_ms = r["base_ms"]
        pct = ((c_ms - base_ms) * 100.0 / base_ms) if base_ms else 0.0
        record = dict(r, confirm_ms=c_ms, confirm_pct=round(pct, 1))
        if pct > max_regression_pct and max(base_ms, c_ms) >= min_ms:
            confirmed.append(record)
        else:
            unconfirmed.append(record)
    delta["regressions"] = confirmed
    delta["unconfirmed_regressions"] = unconfirmed
    delta["confirmed_against"] = confirm.get("label", "")
    return delta



def diff_inventories(base, new, max_regression_pct=20.0, min_ms=DEFAULT_MIN_MS,
                     field="verify_ms"):
    """Compare per-module times.

    `min_ms` is the noise floor described above: modules smaller than it are
    measured and reported but never counted as regressions.
    """
    base_mods = base["modules"]
    new_mods = new["modules"]

    regressions = []
    improvements = []
    below_floor = []
    added = []
    removed = []

    for name in sorted(set(base_mods) | set(new_mods)):
        b = base_mods.get(name)
        n = new_mods.get(name)
        if b is None:
            added.append(name)
            continue
        if n is None:
            removed.append(name)
            continue
        b_ms = b.get(field) or 0
        n_ms = n.get(field) or 0
        if b_ms == 0:
            pct = 0.0 if n_ms == 0 else float("inf")
        else:
            pct = (n_ms - b_ms) * 100.0 / b_ms
        record = OrderedDict(
            [
                ("module", name),
                ("base_ms", b_ms),
                ("new_ms", n_ms),
                ("delta_ms", n_ms - b_ms),
                ("delta_pct", round(pct, 1) if pct != float("inf") else None),
            ]
        )
        if pct > max_regression_pct:
            # Floor on the BASE value, because the percentage is computed
            # relative to it: if the baseline measurement sits in the regime
            # where identical-code runs already vary by more than the
            # threshold, the ratio says nothing. Measured case: a module with
            # base 953 ms (same-code spread 953-1168) read 1213 ms after an
            # unrelated change -- "+27%" that a third sample dissolved to +12%.
            # A large absolute jump from a small base is not lost: it is listed
            # under "below the noise floor", which is sorted by absolute delta.
            if b_ms < min_ms:
                below_floor.append(record)
            else:
                regressions.append(record)
        elif pct < -max_regression_pct:
            improvements.append(record)

    regressions.sort(key=lambda r: -(r["delta_ms"]))
    below_floor.sort(key=lambda r: -(r["delta_ms"]))
    improvements.sort(key=lambda r: r["delta_ms"])

    base_total = base["total_verify_ms"]
    new_total = new["total_verify_ms"]
    total_pct = (
        round((new_total - base_total) * 100.0 / base_total, 1) if base_total else None
    )

    return OrderedDict(
        [
            ("schema", "verus-timing-diff/v1"),
            ("base_label", base.get("label", "")),
            ("new_label", new.get("label", "")),
            ("max_regression_pct", max_regression_pct),
            ("min_ms", min_ms),
            ("field", field),
            ("base_total_verify_ms", base_total),
            ("new_total_verify_ms", new_total),
            ("total_delta_pct", total_pct),
            ("regressions", regressions),
            ("improvements", improvements),
            ("below_noise_floor", below_floor),
            ("added_modules", added),
            ("removed_modules", removed),
        ]
    )


def render_diff(d):
    out = []
    out.append("# Verus timing diff")
    out.append("")
    out.append("`{}` -> `{}`".format(d["base_label"] or "base", d["new_label"] or "new"))
    out.append("")
    out.append("| metric | value |")
    out.append("|---|---:|")
    out.append("| total verify, base | {} ms |".format(d["base_total_verify_ms"]))
    out.append("| total verify, new | {} ms |".format(d["new_total_verify_ms"]))
    out.append(
        "| total delta | {} |".format(
            "n/a" if d["total_delta_pct"] is None else "{:+.1f}%".format(d["total_delta_pct"])
        )
    )
    out.append("| threshold | {:.0f}% |".format(d["max_regression_pct"]))
    out.append("| noise floor | {} ms |".format(d["min_ms"]))
    out.append("| regressions | {} |".format(len(d["regressions"])))
    out.append("")

    def table(title, rows, note=None):
        if not rows:
            return
        out.append("## {}".format(title))
        out.append("")
        if note:
            out.append(note)
            out.append("")
        out.append("| module | base ms | new ms | delta | delta % |")
        out.append("|---|---:|---:|---:|---:|")
        for r in rows:
            out.append(
                "| `{}` | {} | {} | {:+d} | {} |".format(
                    r["module"],
                    r["base_ms"],
                    r["new_ms"],
                    r["delta_ms"],
                    "n/a" if r["delta_pct"] is None else "{:+.1f}%".format(r["delta_pct"]),
                )
            )
        out.append("")

    table("Regressions", d["regressions"])
    if d.get("unconfirmed_regressions"):
        out.append("## Not reproduced by the confirmation run")
        out.append("")
        out.append(
            "Over threshold against the first run but not against `{}`, which "
            "verified the same code. Parallel verification makes per-module "
            "wall-clock contention-sensitive, so these are noise, not proof "
            "regressions.".format(d.get("confirmed_against") or "the second run")
        )
        out.append("")
        out.append("| module | base ms | new ms | confirm ms |")
        out.append("|---|---:|---:|---:|")
        for r in d["unconfirmed_regressions"]:
            out.append(
                "| `{}` | {} | {} | {} |".format(
                    r["module"], r["base_ms"], r["new_ms"],
                    "n/a" if r.get("confirm_ms") is None else r["confirm_ms"],
                )
            )
        out.append("")
    table(
        "Below the noise floor",
        d["below_noise_floor"],
        "Over threshold in percentage terms but too small to be a real signal; "
        "reported, never failed on.",
    )
    table("Improvements", d["improvements"])

    if d["added_modules"]:
        out.append("## New modules")
        out.append("")
        for m in d["added_modules"]:
            out.append("- `{}`".format(m))
        out.append("")
    if d["removed_modules"]:
        out.append("## Modules gone")
        out.append("")
        for m in d["removed_modules"]:
            out.append("- `{}`".format(m))
        out.append("")

    return "\n".join(out)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def _write(path, text):
    if path:
        directory = os.path.dirname(path)
        if directory:
            os.makedirs(directory, exist_ok=True)
        with open(path, "w") as f:
            f.write(text if text.endswith("\n") else text + "\n")
    else:
        sys.stdout.write(text if text.endswith("\n") else text + "\n")


def _load(path):
    with open(path) as f:
        inv = json.load(f)
    if inv.get("schema") != SCHEMA:
        raise SystemExit(
            "{}: expected schema {}, found {!r}".format(path, SCHEMA, inv.get("schema"))
        )
    return inv


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = parser.add_subparsers(dest="mode", required=True)

    p = sub.add_parser("parse", help="verification log -> JSON timing inventory")
    p.add_argument("log", help="Verus --time-expanded log ('-' for stdin)")
    p.add_argument("-o", "--out")
    p.add_argument("--label")
    p.add_argument("--verus-version")
    p.add_argument(
        "--allow-empty",
        action="store_true",
        help="do not fail when the log has no timing breakdown",
    )

    m = sub.add_parser(
        "merge", help="combine runs of the same code by per-module minimum"
    )
    m.add_argument("inventories", nargs="+")
    m.add_argument("-o", "--out")
    m.add_argument("--label")

    r = sub.add_parser("report", help="JSON inventory -> Markdown")
    r.add_argument("inventory")
    r.add_argument("-o", "--out")
    r.add_argument("--top", type=int, default=40)

    d = sub.add_parser("diff", help="two inventories -> regression report")
    d.add_argument("base")
    d.add_argument("new")
    d.add_argument("-o", "--out")
    d.add_argument("--json", action="store_true")
    d.add_argument(
        "--max-regression-pct",
        type=float,
        default=20.0,
        help="per-module regression threshold (Phase 54 acceptance: 20)",
    )
    d.add_argument(
        "--min-ms",
        type=int,
        default=DEFAULT_MIN_MS,
        help="noise floor; modules smaller than this never count as "
        "regressions (default measured: below 1000 ms, identical-code runs "
        "already swing more than 20%%)",
    )
    d.add_argument(
        "--confirm-with",
        help="a second timing inventory of the SAME new code; a regression is "
        "only reported if it reproduces there (parallel verification makes "
        "per-module wall-clock noisy)",
    )
    d.add_argument(
        "--fail-on-regression",
        action="store_true",
        help="exit 1 if any module regressed past the threshold",
    )

    args = parser.parse_args(argv)

    if args.mode == "parse":
        if args.log == "-":
            text = sys.stdin.read()
            source = ""
        else:
            with open(args.log, errors="replace") as f:
                text = f.read()
            source = args.log
        inv = build_inventory(
            text, label=args.label, verus_version=args.verus_version, source=source
        )
        _write(args.out, json.dumps(inv, indent=2))
        if inv["module_count"] == 0 and not args.allow_empty:
            sys.stderr.write(
                "error: no per-module timing found in {}. Verus only prints the "
                "breakdown with --time-expanded; this repo passes it via "
                "`scons --verus-extra-args=\"--time-expanded\"`. Use --allow-empty "
                "if the log really has no timings.\n".format(args.log)
            )
            return 1
        return 0

    if args.mode == "merge":
        merged = merge_min([_load(p) for p in args.inventories], label=args.label)
        _write(args.out, json.dumps(merged, indent=2))
        return 0

    if args.mode == "report":
        _write(args.out, render_report(_load(args.inventory), top=args.top))
        return 0

    delta = diff_inventories(
        _load(args.base),
        _load(args.new),
        max_regression_pct=args.max_regression_pct,
        min_ms=args.min_ms,
    )
    if args.confirm_with:
        delta = confirm_regressions(
            delta,
            _load(args.confirm_with),
            max_regression_pct=args.max_regression_pct,
            min_ms=args.min_ms,
        )
    _write(args.out, json.dumps(delta, indent=2) if args.json else render_diff(delta))
    if args.fail_on_regression and delta["regressions"]:
        sys.stderr.write(
            "error: {} module(s) regressed more than {:.0f}%: {}\n".format(
                len(delta["regressions"]),
                delta["max_regression_pct"],
                ", ".join(r["module"] for r in delta["regressions"]),
            )
        )
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
