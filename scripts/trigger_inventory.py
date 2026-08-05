#!/usr/bin/env python3
"""Verus trigger-note inventory and diff tool (Phase 54.1).

Verus emits

    note: automatically chose triggers for this expression:
      --> src/protocol/RSL/replica.rs:412:9
       |
    412 |     forall|i: int| 0 <= i < n ==> f(i) == g(i)
       |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

    note:   trigger 1 of 2:
      --> src/protocol/RSL/replica.rs:412:35
       |
    412 |     forall|i: int| 0 <= i < n ==> f(i) == g(i)
       |                                   ^^^^

whenever it picks quantifier triggers itself.  The choice is an implementation
detail of the release: it can change silently between Verus versions, and when
it does, a proof that verifies today fails tomorrow as an uninformative
`rlimit exceeded`.  Phase 54 replaces those choices with explicit
`#[trigger]` annotations; this tool is what makes that work measurable.

Three modes:

    parse   verification log        -> JSON inventory
    report  JSON inventory          -> Markdown summary (checked in under reports/)
    diff    two JSON inventories    -> Markdown/JSON delta, optionally failing on
                                       a regression

The diff distinguishes three things, only one of which is visible from a raw
note count:

    removed   a note that is gone   -> an explicit trigger was added (progress)
    added     a new note            -> a regression
    changed   the same expression, but Verus now picks *different* trigger
              terms                 -> the silent-instability case this whole
                                       phase exists to catch

Usage
-----
    # capture a log (any --triggers-mode; record which one in --label)
    verus --crate-type=lib src/lib.rs --triggers 2>&1 | tee run.log

    scripts/trigger_inventory.py parse run.log \\
        --label "0.2026.08.02 full --triggers" \\
        --verus-version 0.2026.08.02.b677dd5 \\
        --root . -o reports/triggers/baseline.json

    scripts/trigger_inventory.py report reports/triggers/baseline.json \\
        -o reports/triggers/baseline.md

    scripts/trigger_inventory.py diff reports/triggers/baseline.json new.json \\
        --fail-on-regression
"""

import argparse
import json
import os
import re
import sys
from collections import Counter, OrderedDict

SCHEMA = "trigger-inventory/v1"

NOTE_HEADER = "note: automatically chose triggers for this expression:"
TRIGGER_HEADER_RE = re.compile(r"^note:\s+trigger (\d+) of (\d+):\s*$")
LOCATION_RE = re.compile(r"^\s*-->\s*(?P<file>[^\s:]+):(?P<line>\d+):(?P<col>\d+)\s*$")
# `412 |     forall|i: int| ...`  and, for multi-line spans, `412 | |   ...`
SOURCE_LINE_RE = re.compile(r"^\s*(?P<lineno>\d+)\s\|(?P<rest>.*)$")
# `    |            ^^^^` / `    | |____^` / `    |  __^`
MARKER_LINE_RE = re.compile(r"^\s*\|(?P<rest>[\s|^_/\\]*)$")
VERUS_VERSION_RE = re.compile(r"^\s*Version:\s*(\S+)\s*$")
# `verification results:: N verified, M errors` -- the evidence that a capture
# with zero notes is a *clean* run rather than one that died before Verus
# printed any. Phase 54.7.f drove the count to 0, at which point "empty" stopped
# meaning "broken" and the guard could no longer tell the two apart.
VERIFICATION_RESULT_RE = re.compile(
    r"verification results::\s*(?P<verified>\d+)\s+verified,\s*(?P<errors>\d+)\s+error"
)


# ---------------------------------------------------------------------------
# parse
# ---------------------------------------------------------------------------


def _content_offset(line):
    """Character offset of the text that follows the diagnostic gutter `|`."""
    bar = line.find("|")
    if bar < 0:
        return None
    return bar + 1


def _strip_span_marker(raw):
    """Drop the gutter and rustc's multi-line span marker (`/`, `|`, `\\`).

    Exactly one marker character is removed, so a source line that genuinely
    starts with a Rust closure (`|i: int| ...`) keeps its leading bar.
    """
    off = _content_offset(raw)
    text = raw[off:] if off is not None else raw
    if text.startswith(" "):
        text = text[1:]
    if text[:1] in ("/", "|", "\\"):
        text = text[1:]
    return text.strip()


def _carets(marker_line, source_line):
    """Text spans of `^` runs in `marker_line`, sliced out of `source_line`.

    Both lines share the same gutter, so the columns line up character for
    character once the gutter is stripped.
    """
    m_off = _content_offset(marker_line)
    s_off = _content_offset(source_line)
    if m_off is None or s_off is None:
        return []
    marker = marker_line[m_off:]
    source = source_line[s_off:]
    spans = []
    for match in re.finditer(r"\^+", marker):
        start, end = match.start(), match.end()
        text = source[start:end].strip()
        if text:
            spans.append(text)
    return spans


def _line_index(block_lines, raw):
    for i, line in enumerate(block_lines):
        if line is raw or line == raw:
            return i
    return -1


def _following_marker(block_lines, idx):
    """The caret line immediately after `idx`, if there is one."""
    if idx < 0 or idx + 1 >= len(block_lines):
        return None
    nxt = block_lines[idx + 1]
    return nxt if MARKER_LINE_RE.match(nxt) and "^" in nxt else None


def _parse_block(lines):
    """Parse one diagnostic block into (location, snippet, spans, multiline)."""
    lines_of_block = list(lines)
    location = None
    source_lines = []  # (lineno, raw line)
    marker_lines = []
    for line in lines:
        loc = LOCATION_RE.match(line)
        if loc and location is None:
            location = (
                loc.group("file"),
                int(loc.group("line")),
                int(loc.group("col")),
            )
            continue
        src = SOURCE_LINE_RE.match(line)
        if src:
            source_lines.append((int(src.group("lineno")), line))
            continue
        mark = MARKER_LINE_RE.match(line)
        if mark and "^" in line:
            marker_lines.append(line)

    multiline = len(source_lines) > 1
    spans = []
    if source_lines and marker_lines:
        if not multiline:
            spans = _carets(marker_lines[0], source_lines[0][1])
        else:
            # A trigger's terms can straddle several source lines, each with
            # its own caret run:
            #
            #   91 |     s.received_1b_packets.contains(p1)
            #      |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
            #   92 |     && s.received_1b_packets.contains(p2)
            #      |        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
            #
            # Treating "more than one quoted line" as "no terms" silently
            # dropped 29 of the crate's trigger groups, and made a diff report
            # a spurious `changed` when the empty term list met a non-empty
            # one. Pair each source line with the marker line that follows it.
            for lineno, raw in source_lines:
                idx = _line_index(lines_of_block, raw)
                marker = _following_marker(lines_of_block, idx)
                if marker is not None:
                    spans.extend(_carets(marker, raw))

    if multiline:
        # A multi-line span: the whole quoted region is the snippet.
        parts = []
        for _, raw in source_lines:
            parts.append(_strip_span_marker(raw))
        snippet = " ".join(p for p in parts if p)
    elif spans:
        snippet = spans[0] if len(spans) == 1 else " ... ".join(spans)
    elif source_lines:
        off = _content_offset(source_lines[0][1])
        snippet = source_lines[0][1][off:].strip() if off is not None else ""
    else:
        snippet = ""

    # The whole quoted region, not just the underlined span. `expr` is the span,
    # and for an `assert forall ..` the caret run covers only the keyword -- so
    # every assert in a file shares the identity "assert" and the entries are
    # told apart by ordinal alone. Annotating one then shifts every later
    # ordinal and the diff reports the rest as `changed` (Phase 54.10.a; seen
    # twice, 3 sites in proposer_gen.rs and 4 in learner_gen.rs, both times a
    # pure rename with an identical trigger multiset).
    source_parts = []
    for _, raw in source_lines:
        stripped = _strip_span_marker(raw)
        if stripped:
            source_parts.append(stripped)
    source_text = normalize(" ".join(source_parts))

    return location, normalize(snippet), spans, multiline, source_text


def normalize(text):
    """Collapse whitespace so that reformatting does not look like a change."""
    return re.sub(r"\s+", " ", (text or "")).strip()


def _split_blocks(log_lines):
    """Yield (kind, header, block_lines) for every trigger-related note."""
    i = 0
    n = len(log_lines)
    while i < n:
        line = log_lines[i].rstrip("\n")
        kind = None
        header = line.strip()
        if line.strip() == NOTE_HEADER:
            kind = "expression"
        else:
            m = TRIGGER_HEADER_RE.match(line.strip())
            if m:
                kind = "trigger"
        if kind is None:
            i += 1
            continue
        block = []
        j = i + 1
        while j < n:
            nxt = log_lines[j].rstrip("\n")
            if not nxt.strip():
                break
            if nxt.strip() == NOTE_HEADER or TRIGGER_HEADER_RE.match(nxt.strip()):
                break
            block.append(nxt)
            j += 1
        yield kind, header, block
        i = j


def relativize(path, root):
    if not root:
        return path
    try:
        rel = os.path.relpath(os.path.abspath(path), os.path.abspath(root))
    except ValueError:
        return path
    return path if rel.startswith("..") else rel


def parse_log(text, root=None):
    """Parse a Verus log into a list of inventory entries."""
    lines = text.splitlines()
    entries = []
    current = None
    orphans = 0
    for kind, header, block in _split_blocks(lines):
        location, snippet, spans, multiline, source_text = _parse_block(block)
        if location is None:
            continue
        path, line_no, col = location
        if root:
            path = relativize(path, root)
        if kind == "expression":
            current = OrderedDict(
                [
                    ("file", path),
                    ("line", line_no),
                    ("col", col),
                    ("expr", snippet),
                    ("source_text", source_text),
                    ("multiline", multiline),
                    ("triggers", []),
                ]
            )
            entries.append(current)
        else:
            m = TRIGGER_HEADER_RE.match(header)
            index, total = (int(m.group(1)), int(m.group(2))) if m else (0, 0)
            trigger = OrderedDict(
                [
                    ("index", index),
                    ("total", total),
                    ("file", path),
                    ("line", line_no),
                    ("col", col),
                    ("terms", [normalize(s) for s in spans]),
                    ("snippet", snippet),
                    ("multiline", multiline),
                ]
            )
            if current is None:
                orphans += 1
                continue
            current["triggers"].append(trigger)
    for e in entries:
        e["trigger_count"] = len(e["triggers"])
        e["key"] = entry_key(e)
    return entries, orphans


def entry_key(entry, use_source_text=True):
    """Location-independent identity of an expression.

    Line numbers move whenever anything above them is edited, so the diff keys
    on (file, expression text, position among identical expressions in the
    file) instead.  The caller assigns the ordinal.

    The expression text is the whole quoted source region, not the underlined
    span: Verus underlines only the `assert` keyword on an `assert forall`, so
    keying on the span gives every assert in a file the same identity and leaves
    the ordinal doing all the work (Phase 54.10.a).
    """
    text = entry.get("source_text") if use_source_text else None
    return "{}::{}".format(entry["file"], text or entry["expr"])


def detect_verus_version(text):
    for line in text.splitlines():
        m = VERUS_VERSION_RE.match(line)
        if m:
            return m.group(1)
    return None


def build_inventory(text, label=None, verus_version=None, source=None, root=None):
    entries, orphans = parse_log(text, root=root)

    # Disambiguate repeated identical expressions within one file.
    seen = Counter()
    for e in entries:
        base = e["key"]
        seen[base] += 1
        if seen[base] > 1:
            e["key"] = "{}#{}".format(base, seen[base])

    verified = errors = None
    for line in text.splitlines():
        m = VERIFICATION_RESULT_RE.search(line)
        if m:
            verified = int(m.group("verified"))
            errors = int(m.group("errors"))

    by_file = Counter(e["file"] for e in entries)
    by_dir = Counter(os.path.dirname(e["file"]) or "." for e in entries)
    by_trigger_count = Counter(str(e["trigger_count"]) for e in entries)
    return OrderedDict(
        [
            ("schema", SCHEMA),
            ("label", label or ""),
            ("verus_version", verus_version or detect_verus_version(text) or ""),
            ("source_log", source or ""),
            ("total_notes", len(entries)),
            ("verified", verified),
            ("errors", errors),
            ("total_triggers", sum(e["trigger_count"] for e in entries)),
            ("orphan_trigger_notes", orphans),
            ("multiline_notes", sum(1 for e in entries if e["multiline"])),
            ("by_file", OrderedDict(sorted(by_file.items()))),
            ("by_dir", OrderedDict(sorted(by_dir.items()))),
            ("by_trigger_count", OrderedDict(sorted(by_trigger_count.items()))),
            ("entries", entries),
        ]
    )


# ---------------------------------------------------------------------------
# report
# ---------------------------------------------------------------------------


def render_report(inv, top=25):
    out = []
    out.append("# Verus trigger-note inventory")
    out.append("")
    out.append("| field | value |")
    out.append("|---|---|")
    out.append("| label | {} |".format(inv.get("label") or "(none)"))
    out.append("| verus version | {} |".format(inv.get("verus_version") or "(unknown)"))
    out.append("| source log | {} |".format(inv.get("source_log") or "(stdin)"))
    out.append("| notes | {} |".format(inv["total_notes"]))
    out.append("| trigger choices | {} |".format(inv["total_triggers"]))
    out.append("| multi-line expressions | {} |".format(inv.get("multiline_notes", 0)))
    out.append("")
    out.append("## By directory")
    out.append("")
    out.append("| directory | notes |")
    out.append("|---|---:|")
    for d, n in sorted(inv["by_dir"].items(), key=lambda kv: (-kv[1], kv[0])):
        out.append("| `{}` | {} |".format(d, n))
    out.append("")
    out.append("## Triggers per expression")
    out.append("")
    out.append("| triggers chosen | expressions |")
    out.append("|---:|---:|")
    for k, n in sorted(inv["by_trigger_count"].items(), key=lambda kv: int(kv[0])):
        out.append("| {} | {} |".format(k, n))
    out.append("")
    out.append("## Top files")
    out.append("")
    out.append("| file | notes |")
    out.append("|---|---:|")
    ranked = sorted(inv["by_file"].items(), key=lambda kv: (-kv[1], kv[0]))
    for f, n in ranked[:top]:
        out.append("| `{}` | {} |".format(f, n))
    if len(ranked) > top:
        out.append("")
        out.append("_{} further files omitted._".format(len(ranked) - top))
    out.append("")
    return "\n".join(out)


# ---------------------------------------------------------------------------
# diff
# ---------------------------------------------------------------------------


def trigger_signature(entry):
    """The chosen triggers, as a comparable, position-independent value."""
    return [tuple(t["terms"]) for t in entry["triggers"]]


def _rekey(entries, use_source_text):
    """Recompute keys, re-assigning the duplicate ordinals to match."""
    seen = Counter()
    out = OrderedDict()
    for e in entries:
        k = entry_key(e, use_source_text)
        seen[k] += 1
        if seen[k] > 1:
            k = "{}#{}".format(k, seen[k])
        out[k] = e
    return out


def diff_inventories(base, new):
    # An inventory captured before Phase 54.10.a has no `source_text`. Comparing
    # a rich key against a coarse one would make every entry look
    # removed-and-added, so fall back to the coarse key for *both* sides. The
    # diff is then exactly as good as the older run allowed, and no worse.
    both_rich = all(
        e.get("source_text") for inv in (base, new) for e in inv["entries"]
    )
    base_map = _rekey(base["entries"], both_rich)
    new_map = _rekey(new["entries"], both_rich)

    removed = [e for k, e in base_map.items() if k not in new_map]
    added = [e for k, e in new_map.items() if k not in base_map]
    changed = []
    for k, e in new_map.items():
        if k not in base_map:
            continue
        old = base_map[k]
        if trigger_signature(old) != trigger_signature(e):
            changed.append(
                OrderedDict(
                    [
                        ("key", k),
                        ("file", e["file"]),
                        ("line", e["line"]),
                        ("expr", e["expr"]),
                        ("base_triggers", [t["terms"] for t in old["triggers"]]),
                        ("new_triggers", [t["terms"] for t in e["triggers"]]),
                    ]
                )
            )

    per_dir = OrderedDict()
    for d in sorted(set(base["by_dir"]) | set(new["by_dir"])):
        b = base["by_dir"].get(d, 0)
        n = new["by_dir"].get(d, 0)
        if b != n:
            per_dir[d] = OrderedDict([("base", b), ("new", n), ("delta", n - b)])

    return OrderedDict(
        [
            ("schema", "trigger-inventory-diff/v1"),
            ("base_label", base.get("label", "")),
            ("new_label", new.get("label", "")),
            ("base_notes", base["total_notes"]),
            ("new_notes", new["total_notes"]),
            ("delta_notes", new["total_notes"] - base["total_notes"]),
            ("removed_count", len(removed)),
            ("added_count", len(added)),
            ("changed_count", len(changed)),
            (
                "removed",
                [
                    OrderedDict(
                        [("key", e["key"]), ("file", e["file"]), ("expr", e["expr"])]
                    )
                    for e in removed
                ],
            ),
            (
                "added",
                [
                    OrderedDict(
                        [
                            ("key", e["key"]),
                            ("file", e["file"]),
                            ("line", e["line"]),
                            ("expr", e["expr"]),
                        ]
                    )
                    for e in added
                ],
            ),
            ("changed", changed),
            ("by_dir_delta", per_dir),
        ]
    )


def render_diff(d, limit=40):
    out = []
    out.append("# Trigger-note diff")
    out.append("")
    out.append("`{}` -> `{}`".format(d["base_label"] or "base", d["new_label"] or "new"))
    out.append("")
    out.append("| metric | value |")
    out.append("|---|---:|")
    out.append("| notes, base | {} |".format(d["base_notes"]))
    out.append("| notes, new | {} |".format(d["new_notes"]))
    out.append("| delta | {:+d} |".format(d["delta_notes"]))
    out.append("| removed (progress) | {} |".format(d["removed_count"]))
    out.append("| added (regression) | {} |".format(d["added_count"]))
    out.append("| changed triggers (instability) | {} |".format(d["changed_count"]))
    out.append("")

    if d["changed"]:
        out.append("## Changed trigger choices")
        out.append("")
        out.append("Same expression, different automatically chosen triggers. This is the")
        out.append("failure mode Phase 54 exists to prevent: nothing in the note count")
        out.append("moves, but the solver now instantiates different terms.")
        out.append("")
        for c in d["changed"][:limit]:
            out.append("- `{}:{}`".format(c["file"], c["line"]))
            out.append("  - expr: `{}`".format(c["expr"]))
            out.append("  - base: `{}`".format(c["base_triggers"]))
            out.append("  - new:  `{}`".format(c["new_triggers"]))
        if len(d["changed"]) > limit:
            out.append("")
            out.append("_{} more omitted._".format(len(d["changed"]) - limit))
        out.append("")

    if d["added"]:
        out.append("## Added notes (regression)")
        out.append("")
        for a in d["added"][:limit]:
            out.append("- `{}:{}` `{}`".format(a["file"], a["line"], a["expr"]))
        if len(d["added"]) > limit:
            out.append("")
            out.append("_{} more omitted._".format(len(d["added"]) - limit))
        out.append("")

    if d["by_dir_delta"]:
        out.append("## By directory")
        out.append("")
        out.append("| directory | base | new | delta |")
        out.append("|---|---:|---:|---:|")
        for dir_name, v in d["by_dir_delta"].items():
            out.append(
                "| `{}` | {} | {} | {:+d} |".format(
                    dir_name, v["base"], v["new"], v["delta"]
                )
            )
        out.append("")

    return "\n".join(out)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


CEILING_SCHEMA = "trigger-ceiling/v1"


def load_ceiling(path):
    with open(path) as f:
        ceiling = json.load(f)
    if ceiling.get("schema") != CEILING_SCHEMA:
        raise SystemExit(
            "{}: expected schema {}, found {!r}".format(
                path, CEILING_SCHEMA, ceiling.get("schema")
            )
        )
    return ceiling


def guard(inventory, ceiling, mode=None, baseline=None, out=None):
    """Check an inventory against the agreed ceiling. Returns (status, text).

    status 0 = pass, 1 = over the ceiling / regressed, 2 = the comparison
    itself is invalid (e.g. the inventory was captured in a different
    `--triggers-mode` than the ceiling was agreed in, which makes the numbers
    incomparable).
    """
    lines = []
    total = inventory["total_notes"]
    lines.append("trigger notes measured: {}".format(total))

    declared_mode = ceiling.get("mode")
    if mode and declared_mode and mode != declared_mode:
        lines.append(
            "ERROR: this inventory was captured in `{}` mode but the ceiling was "
            "agreed in `{}` mode. Counts from different --triggers-mode settings "
            "are not comparable.".format(mode, declared_mode)
        )
        return 2, "\n".join(lines)

    # Zero notes is ambiguous on its face: it is either a clean run or one that
    # died before Verus printed anything. The capture says which -- a recorded
    # `N verified, 0 errors` with N > 0 is a run that finished. Treating every
    # empty capture as suspect was right until Phase 54.7.f reached 0, and would
    # now make a ceiling of 0 unenforceable: the success state would be the one
    # state never checked.
    finished = (
        inventory.get("verified") is not None
        and inventory["verified"] > 0
        and inventory.get("errors") == 0
    )
    if total == 0 and not finished:
        lines.append(
            "no trigger notes in this capture, and the log does not record a "
            "successful `N verified, 0 errors` — Verus only prints notes for "
            "verified modules, so the run probably failed early. Not judging a "
            "ceiling on an empty capture."
        )
        return 0, "\n".join(lines)

    status = 0

    if not ceiling.get("enforce") or ceiling.get("max_notes") is None:
        lines.append(
            "ceiling not enforced yet (Phase 54.2.b): commit a measured baseline, "
            "then set max_notes and enforce=true in the ceiling file."
        )
    else:
        limit = ceiling["max_notes"]
        lines.append("ceiling: {}".format(limit))
        if total > limit:
            lines.append(
                "ERROR: {} trigger notes exceeds the agreed ceiling of {} by {}. "
                "Either add #[trigger] to the new quantifiers, or raise the ceiling "
                "deliberately in {} with a reason.".format(
                    total, limit, total - limit, out or "the ceiling file"
                )
            )
            status = 1
        else:
            lines.append("under the ceiling by {}".format(limit - total))

    if baseline is not None:
        delta = diff_inventories(baseline, inventory)
        lines.append(
            "vs baseline `{}`: {} removed, {} added, {} changed".format(
                baseline.get("label") or "base",
                delta["removed_count"],
                delta["added_count"],
                delta["changed_count"],
            )
        )
        for c in delta["changed"][:10]:
            lines.append(
                "  changed: {}:{} {} -> {}".format(
                    c["file"], c["line"], c["base_triggers"], c["new_triggers"]
                )
            )
        if ceiling.get("enforce") and (delta["added_count"] or delta["changed_count"]):
            lines.append(
                "ERROR: {} note(s) added and {} expression(s) had their chosen "
                "triggers change. A changed choice is the dangerous one: the count "
                "can stay identical while the solver instantiates different "
                "terms.".format(delta["added_count"], delta["changed_count"])
            )
            status = 1

    return status, "\n".join(lines)


def _write(path, text):
    if path:
        directory = os.path.dirname(path)
        if directory:
            os.makedirs(directory, exist_ok=True)
        with open(path, "w") as f:
            f.write(text)
            if not text.endswith("\n"):
                f.write("\n")
    else:
        sys.stdout.write(text)
        if not text.endswith("\n"):
            sys.stdout.write("\n")


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

    p = sub.add_parser("parse", help="verification log -> JSON inventory")
    p.add_argument("log", help="Verus verification log ('-' for stdin)")
    p.add_argument("-o", "--out", help="output JSON path (default: stdout)")
    p.add_argument("--label", help="human label for this run")
    p.add_argument("--verus-version", help="override the detected Verus version")
    p.add_argument("--root", help="make source paths relative to this directory")
    p.add_argument(
        "--allow-empty",
        action="store_true",
        help="do not fail when the log contains no trigger notes",
    )

    r = sub.add_parser("report", help="JSON inventory -> Markdown summary")
    r.add_argument("inventory")
    r.add_argument("-o", "--out")
    r.add_argument("--top", type=int, default=25, help="files listed in the table")

    d = sub.add_parser("diff", help="two JSON inventories -> delta")
    d.add_argument("base")
    d.add_argument("new")
    d.add_argument("-o", "--out")
    d.add_argument("--json", action="store_true", help="emit JSON instead of Markdown")
    d.add_argument(
        "--fail-on-regression",
        action="store_true",
        help="exit 1 if notes were added or trigger choices changed",
    )
    d.add_argument(
        "--max-notes",
        type=int,
        help="exit 1 if the new inventory exceeds this note count (54.9 CI guard)",
    )

    g = sub.add_parser("guard", help="check an inventory against the agreed ceiling")
    g.add_argument("inventory")
    g.add_argument(
        "--ceiling",
        default=os.path.join("reports", "triggers", "ceiling.json"),
        help="ceiling file (default: reports/triggers/ceiling.json)",
    )
    g.add_argument(
        "--baseline",
        help="optional committed baseline inventory; also checks added/changed",
    )
    g.add_argument(
        "--capture-mode",
        help="--triggers-mode this inventory was captured with; must match the "
        "ceiling's mode",
    )

    args = parser.parse_args(argv)

    if args.mode == "guard":
        inventory = _load(args.inventory)
        ceiling = load_ceiling(args.ceiling)
        baseline = _load(args.baseline) if args.baseline else None
        status, text = guard(
            inventory,
            ceiling,
            mode=args.capture_mode,
            baseline=baseline,
            out=args.ceiling,
        )
        sys.stdout.write(text + "\n")
        if status:
            sys.stderr.write("trigger guard failed\n")
        return status

    if args.mode == "parse":
        if args.log == "-":
            text = sys.stdin.read()
            source = ""
        else:
            with open(args.log, errors="replace") as f:
                text = f.read()
            source = relativize(args.log, args.root) if args.root else args.log
        inv = build_inventory(
            text,
            label=args.label,
            verus_version=args.verus_version,
            source=source,
            root=args.root,
        )
        _write(args.out, json.dumps(inv, indent=2))
        if inv["total_notes"] == 0 and not args.allow_empty:
            sys.stderr.write(
                "error: no trigger notes found in {}. Verus only prints them for "
                "verified modules; re-run with --triggers (or --triggers-mode "
                "all-modules), or pass --allow-empty if the log really is "
                "trigger-free.\n".format(args.log)
            )
            return 1
        if inv["orphan_trigger_notes"]:
            sys.stderr.write(
                "warning: {} 'trigger N of M' notes had no preceding expression "
                "note; the log may be truncated or interleaved.\n".format(
                    inv["orphan_trigger_notes"]
                )
            )
        return 0

    if args.mode == "report":
        _write(args.out, render_report(_load(args.inventory), top=args.top))
        return 0

    base = _load(args.base)
    new = _load(args.new)
    delta = diff_inventories(base, new)
    _write(args.out, json.dumps(delta, indent=2) if args.json else render_diff(delta))

    status = 0
    if args.fail_on_regression and (delta["added_count"] or delta["changed_count"]):
        sys.stderr.write(
            "error: {} note(s) added, {} expression(s) changed triggers\n".format(
                delta["added_count"], delta["changed_count"]
            )
        )
        status = 1
    if args.max_notes is not None and new["total_notes"] > args.max_notes:
        sys.stderr.write(
            "error: {} trigger notes exceeds the ceiling of {}\n".format(
                new["total_notes"], args.max_notes
            )
        )
        status = 1
    return status


if __name__ == "__main__":
    sys.exit(main())
