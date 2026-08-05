#!/usr/bin/env python3
"""Attribute each auto-chosen-trigger note to its containing function and say
whether a regeneration could ever deliver it (Phase 54.7.c).

Phase 54 has estimated the "deliverable by regeneration" count four times -- 80,
50, 3, 40 -- and every estimate was wrong, most recently because attribution was
done by substring search, which put 40 notes on one function. Three merges then
delivered **0**. This does the attribution by *line range* and classifies the
containing function by how it is produced, which is the property that actually
decides deliverability:

    skip      the module's `skip_functions` -- the transpiler emits nothing, so
              the checked-in body is hand-written and regeneration never
              rewrites it. A codegen fix cannot reach these.
    preserve  listed in `rsl_merge_preserve.txt` -- fresh output *does* contain
              this function, but the merge deliberately keeps the existing body.
              A codegen fix reaches these only if the preserve entry is dropped.
    generated  neither -- the transpiler produces this body, so a codegen fix
              plus regeneration delivers the note. These are actionable now.

Usage:
    classify_trigger_notes.py <verification.log> [--root .] [--json]

`generated` being non-empty is the interesting outcome: it means notes are
sitting in transpiler output and the codegen gap is real and fixable today.
"""

import argparse
import collections
import json
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import merge_generated as mg  # noqa: E402

NOTE_RE = re.compile(r"^note: automatically chose triggers for this expression:")
LOC_RE = re.compile(r"^\s*--> (?P<file>[^:]+):(?P<line>\d+):\d+")


SRC_RE = re.compile(r"^\s*\d+\s*\|\s?(?P<src>.*)$")

# The one shape 54.7.a taught codegen to annotate: an ensures clause bounding a
# vector's elements. Notes of this shape in transpiler-emitted code clear
# themselves on regeneration; the same shape in a hand-written body never will.
VEC_ELEMENT_RE = re.compile(
    r"forall\s*\|\s*\w+\s*:\s*int\s*\|.*0\s*<=\s*(?P<i>\w+)\s*<\s*\S+\.len\(\)"
    r".*==>.*\[\s*(?P=i)\s*\]\s*\.\s*(valid|abstractable)"
)


def parse_note_locations(log_text):
    """[(file, line, source)] for each auto-chosen-trigger note, in log order.

    Only the note's own location is taken -- each note is followed by one
    `trigger N of M` block per chosen trigger, each with its own `-->` line, and
    counting those would multiply-count a single note. `source` is the quoted
    source line, used to tell the shapes apart.
    """
    out = []
    lines = log_text.split("\n")
    for i, line in enumerate(lines):
        if not NOTE_RE.match(line):
            continue
        loc = None
        for j in range(i + 1, min(i + 6, len(lines))):
            if loc is None:
                m = LOC_RE.match(lines[j])
                if m:
                    loc = (m.group("file"), int(m.group("line")))
                continue
            m_src = SRC_RE.match(lines[j])
            if m_src:
                out.append((loc[0], loc[1], m_src.group("src")))
                break
        else:
            if loc:
                out.append((loc[0], loc[1], ""))
    return out


def shape_of(src):
    """`vec-element` for the shape codegen already annotates, else `other`."""
    return "vec-element" if VEC_ELEMENT_RE.search(src) else "other"


def function_spans(text):
    """[(qualified_name, start_line, end_line)] 1-indexed, innermost last.

    Reuses `merge_generated._block_end`, which already knows that the body brace
    is the one outside every paren -- a signature whose `requires` holds a struct
    literal otherwise closes the span at the signature and every note in the body
    lands outside any function.
    """
    lines = text.split("\n")
    spans = []
    impl_stack = []  # (name, end_index)
    for i, line in enumerate(lines):
        while impl_stack and i > impl_stack[-1][1]:
            impl_stack.pop()
        m_impl = mg.IMPL_RE.match(line)
        if m_impl and "{" in line:
            impl_stack.append((m_impl.group("name"), mg._block_end(lines, i)))
            continue
        m_fn = mg.FN_RE.match(line)
        if not m_fn:
            continue
        end = mg._block_end(lines, i)
        name = m_fn.group("name")
        if impl_stack:
            name = f"{impl_stack[-1][0]}::{name}"
        spans.append((name, i + 1, end + 1))
    return spans


def containing_function(spans, line):
    """Innermost span covering `line`, or None.

    Smallest span wins so a method inside an impl beats the impl-level match.
    """
    best = None
    for name, start, end in spans:
        if start <= line <= end:
            if best is None or (end - start) < (best[2] - best[1]):
                best = (name, start, end)
    return best[0] if best else None


def load_skip_functions(toml_path):
    """Names in the config's `skip_functions`, without needing a TOML library."""
    if not os.path.exists(toml_path):
        return set()
    with open(toml_path) as fh:
        text = fh.read()
    m = re.search(r"^skip_functions\s*=\s*\[(.*?)\]", text, re.S | re.M)
    if not m:
        return set()
    body = re.sub(r"#.*$", "", m.group(1), flags=re.M)
    return set(re.findall(r'"([^"]+)"', body))


def spec_names_of(exec_name):
    """Spec names a `skip_functions` entry could use for this exec function.

    `skip_functions` lists the *spec* name and the generated file carries the
    *exec* name: `LExecutorExecute` is skipped, `CExecutorExecute` is what
    appears in `executor_gen.rs`; `BoundRequestSequence` is skipped and
    `CBoundRequestSequence` appears. Matching exec names against the list
    directly finds nothing, which reported every skipped function as ordinary
    transpiler output -- 0 skips out of 103 notes, which is how the bug showed.
    """
    names = {exec_name}
    if exec_name.startswith("C"):
        base = exec_name[1:]
        names |= {base, f"L{base}"}
    return names


def module_of(path):
    """`src/generated/RSL/executor_gen.rs` -> `executor`."""
    base = os.path.basename(path)
    return base[: -len("_gen.rs")] if base.endswith("_gen.rs") else None


def classify(log_text, root="."):
    """{category: [(file, line, function)]} plus notes outside src/generated."""
    out = collections.defaultdict(list)
    spans_cache = {}
    skips_cache = {}
    preserve_path = os.path.join(root, "scripts", "rsl_merge_preserve.txt")

    for path, line, src in parse_note_locations(log_text):
        shape = shape_of(src)
        if not path.startswith("src/generated/"):
            out["not-generated"].append((path, line, None, shape))
            continue
        full = os.path.join(root, path)
        if full not in spans_cache:
            with open(full) as fh:
                spans_cache[full] = function_spans(fh.read())
        fn = containing_function(spans_cache[full], line)
        module = module_of(path)
        if module is None or fn is None:
            out["unattributed"].append((path, line, fn, shape))
            continue
        if module not in skips_cache:
            toml = os.path.join(
                root, "src", "protocol", "RSL", f"{module}_transpile.toml"
            )
            preserved, _ = _load_preserve(preserve_path, module)
            skips_cache[module] = (load_skip_functions(toml), preserved)
        skips, preserved = skips_cache[module]
        short = fn.split("::")[-1]
        if spec_names_of(short) & skips:
            out["skip"].append((path, line, fn, shape))
        elif short in preserved or fn in preserved:
            out["preserve"].append((path, line, fn, shape))
        else:
            out["generated"].append((path, line, fn, shape))
    return out


def _load_preserve(path, module):
    import check_merge_body_drift as cd

    return cd.load_preserve(path, module)


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("log")
    p.add_argument("--root", default=".")
    p.add_argument("--json", action="store_true")
    args = p.parse_args(argv)

    with open(args.log) as fh:
        result = classify(fh.read(), args.root)

    if args.json:
        print(json.dumps({k: v for k, v in sorted(result.items())}, indent=2))
        return 0

    total = sum(len(v) for v in result.values())
    print(f"{total} auto-chosen-trigger notes")
    for category in ("generated", "preserve", "skip", "not-generated", "unattributed"):
        items = result.get(category, [])
        if not items:
            continue
        by_fn = collections.Counter(fn for _, _, fn, _ in items)
        shapes = collections.Counter(sh for _, _, _, sh in items)
        detail = ", ".join(f"{sh} {n}" for sh, n in sorted(shapes.items()))
        print(f"\n  {category}: {len(items)}  ({detail})")
        for fn, n in by_fn.most_common():
            print(f"      {n:>3}  {fn}")

    # The decision-relevant cell: transpiler-emitted code carrying the one shape
    # codegen already annotates. Those clear themselves on regeneration; nothing
    # else in the table does, whatever its origin.
    gen = result.get("generated", [])
    ready = [x for x in gen if x[3] == "vec-element"]
    print(
        f"\n  deliverable by regeneration alone: {len(ready)}"
        f"  (transpiler-emitted AND a shape codegen annotates)"
    )
    by_mod = collections.Counter(module_of(f) for f, _, _, _ in ready)
    for mod, n in by_mod.most_common():
        print(f"      {n:>3}  {mod}")
    print(
        f"  needs new codegen work: {len(gen) - len(ready)} emitted but an "
        f"unhandled shape\n"
        f"  not reachable by regeneration: "
        f"{len(result.get('skip', [])) + len(result.get('preserve', []))} "
        f"(hand-written or preserved bodies)"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
