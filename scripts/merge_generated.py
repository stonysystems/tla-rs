#!/usr/bin/env python3
"""Merge fresh transpiler output with preserved hand-written bodies (Phase 42.8.c).

`scripts/regenerate_rsl.sh` can only *replace* a generated file wholesale. Five
of the eight RSL modules carry `skip_functions` — functions the transpiler
deliberately does not emit, whose hand-written bodies live in the checked-in
file — so the script keeps those files untouched and merely reports. The
consequence is that **no codegen improvement can reach them**: the Phase 54.7.a
trigger fix, the Phase 42.8.b import fix, and anything after them stop at the
three modules that happen to have no hand-written content.

This tool closes that gap. It takes the fresh output as the source of truth for
everything the transpiler emits, and splices back exactly the items the
transpiler did not emit:

    fresh output              +  items only in the existing file
    (all codegen improvements)   (skip_functions bodies, helpers, their imports)

Placement matters: a preserved item may be a free function or a method inside
an `impl` block, and putting a method at top level produces `&mut self` outside
an impl, which does not compile. Items are therefore matched to the impl they
came from, and free functions are emitted before the impls.

Usage
-----
    scripts/merge_generated.py fresh.rs existing.rs -o merged.rs
    scripts/merge_generated.py fresh.rs existing.rs --report
"""

import argparse
import os
import re
import sys
from collections import OrderedDict

FN_RE = re.compile(
    r"^(?P<indent>\s*)(?:pub\s+)?(?:open\s+|closed\s+)?"
    r"(?:exec\s+|proof\s+|spec\s+)?fn\s+(?P<name>[A-Za-z_][A-Za-z_0-9]*)"
)
IMPL_RE = re.compile(r"^\s*impl(?:\s*<[^>]*>)?\s+(?P<name>[A-Za-z_][A-Za-z_0-9]*)")
ATTR_RE = re.compile(r"^\s*(#\[|#!\[|///|//!)")
IMPORT_RE = re.compile(r"^\s*(pub\s+)?use\s+")


def _block_end(lines, start):
    """Index of the line closing the brace-delimited block opened at `start`.

    Parens and brackets are tracked too, not just braces. A spec body can have
    its braces balance while a parenthesised expression is still open --

        RemoveAllSatisfiedRequestsInSequence(s.push(x), r) =~= (
            ...
        )

    -- and closing the block there truncates the body mid-expression, so the
    merged file does not parse.
    """
    depth = {"{": 0, "(": 0, "[": 0}
    close = {"}": "{", ")": "(", "]": "["}
    seen = False
    for i in range(start, len(lines)):
        line = lines[i]
        # Strip line comments so a bracket in a comment does not shift the depth.
        code = re.sub(r"//.*$", "", line)
        for ch in code:
            if ch in depth:
                depth[ch] += 1
            elif ch in close:
                depth[close[ch]] -= 1
        # The body-opening brace is the one still open at end of line. A struct
        # literal inside a contract -- `UpperBound::UpperBoundFinite{n: ..}` in a
        # `requires` clause -- opens and closes on one line, and treating it as
        # the body truncates the function to its signature.
        if depth["{"] > 0:
            seen = True
        if seen and all(d <= 0 for d in depth.values()):
            return i
    return len(lines) - 1


def _leading_attrs(lines, idx):
    """Start index of the doc comments / attributes attached above `idx`."""
    start = idx
    while start > 0 and ATTR_RE.match(lines[start - 1]):
        start -= 1
    return start


def parse_items(text):
    """Top-level functions and impl-block methods, with their source text.

    Returns (free_fns, impls, imports) where `impls` maps an impl name to an
    OrderedDict of method name -> source text.
    """
    lines = text.split("\n")
    free_fns = OrderedDict()
    impls = OrderedDict()
    imports = []

    i = 0
    while i < len(lines):
        line = lines[i]
        if IMPORT_RE.match(line):
            # A rustfmt-wrapped import spans several lines:
            #     use crate::x::{
            #         a, b,
            #     };
            # Capturing only the first line yields `use crate::x::{` on its own,
            # which is an unclosed delimiter -- the merged file then does not
            # parse at all, so rustc and rustfmt fail before any real
            # signature mismatch is even reached.
            stmt = [line.rstrip()]
            j = i
            while not stmt[-1].rstrip().endswith(";") and j + 1 < len(lines):
                j += 1
                stmt.append(lines[j].rstrip())
            imports.append("\n".join(stmt).strip())
            i = j + 1
            continue

        impl_m = IMPL_RE.match(line)
        if impl_m and "{" in line:
            end = _block_end(lines, i)
            methods = OrderedDict()
            j = i + 1
            while j < end:
                fn_m = FN_RE.match(lines[j])
                if fn_m:
                    fn_start = _leading_attrs(lines, j)
                    fn_end = _block_end(lines, j)
                    methods[fn_m.group("name")] = "\n".join(lines[fn_start : fn_end + 1])
                    j = fn_end + 1
                    continue
                j += 1
            impls.setdefault(impl_m.group("name"), OrderedDict()).update(methods)
            i = end + 1
            continue

        fn_m = FN_RE.match(line)
        if fn_m and not line.startswith(" "):
            fn_start = _leading_attrs(lines, i)
            fn_end = _block_end(lines, i)
            free_fns[fn_m.group("name")] = "\n".join(lines[fn_start : fn_end + 1])
            i = fn_end + 1
            continue
        i += 1

    return free_fns, impls, imports


def plan_merge(fresh_text, existing_text, preserve=()):
    """What would be carried over from `existing` into `fresh`."""
    f_free, f_impls, f_imports = parse_items(fresh_text)
    e_free, e_impls, e_imports = parse_items(existing_text)

    carried_free = [n for n in e_free if n not in f_free]
    carried_methods = OrderedDict()
    for impl_name, methods in e_impls.items():
        missing = [m for m in methods if m not in f_impls.get(impl_name, {})]
        if missing:
            carried_methods[impl_name] = missing
    # Phase 42.8.c: named free functions the *existing* file wins on, even though
    # fresh emits them. The transpiler synthesises helpers such as
    # `filter_clearnerstate` naively (a `for` loop over `m.iter()`), while the
    # checked-in file holds a hand-verified `while` loop with invariants.
    # Without this, merging silently replaces verified code with code that does
    # not verify -- which is most of learner's 183-line merge diff.
    overridden = [name for name in preserve if name in e_free]
    missing = sorted(set(preserve) - set(e_free))
    if missing:
        raise ValueError(
            "--preserve names not found as free functions in the existing file: "
            + ", ".join(missing)
        )

    # An import whose module path fresh already imports must not be emitted again:
    # `use X::{a, b}` from fresh plus `use X::{b, a, c}` carried over is a
    # duplicate-name error, not two imports. Merge the member sets instead.
    def _module_path(imp):
        flat = re.sub(r"\s+", "", imp).rstrip(";")
        return flat.split("{", 1)[0] if "{" in flat else None

    def _members(imp):
        flat = re.sub(r"\s+", "", imp).rstrip(";")
        m = re.match(r"^.*?\{(.*)\}$", flat)
        return [x for x in m.group(1).split(",") if x] if m else []

    fresh_by_path = {}
    for imp in f_imports:
        path = _module_path(imp)
        if path:
            fresh_by_path.setdefault(path, set()).update(_members(imp))
    merged_imports = {}
    for imp in e_imports:
        path = _module_path(imp)
        if path and path in fresh_by_path:
            extra = set(_members(imp)) - fresh_by_path[path]
            if extra:
                merged_imports[path] = fresh_by_path[path] | set(_members(imp))

    carried_imports = [
        imp
        for imp in e_imports
        if imp not in f_imports
        and _import_path(imp) not in map(_import_path, f_imports)
        and _module_path(imp) not in fresh_by_path
    ]
    dropped_impls = [n for n in carried_methods if n not in f_impls]
    return OrderedDict(
        [
            ("carried_free_fns", carried_free),
            ("carried_methods", carried_methods),
            ("carried_imports", carried_imports),
            ("overridden_free_fns", overridden),
            ("merged_imports", merged_imports),
            ("impls_absent_from_fresh", dropped_impls),
        ]
    )


def _import_path(imp):
    """Normalise an import for identity comparison.

    A wrapped import and its single-line form denote the same thing, so
    whitespace is stripped and the brace-list is sorted -- otherwise a fresh
    `use x::{a, b};` and a preserved `use x::{\n b, a,\n};` look distinct and
    both get emitted.
    """
    flat = re.sub(r"\s+", "", imp).rstrip(";")
    m = re.match(r"^(.*?\{)(.*)\}$", flat)
    if m:
        items = sorted(x for x in m.group(2).split(",") if x)
        return m.group(1) + ",".join(items) + "}"
    return flat


def merge(fresh_text, existing_text, preserve=()):
    """Fresh output with the existing file's unemitted items spliced back."""
    plan = plan_merge(fresh_text, existing_text, preserve)
    if plan["impls_absent_from_fresh"]:
        raise ValueError(
            "cannot place preserved methods: fresh output has no impl block for "
            + ", ".join(plan["impls_absent_from_fresh"])
        )

    e_free, e_impls, _ = parse_items(existing_text)

    # Swap fresh's version of each overridden free function for the existing one.
    for name in plan["overridden_free_fns"]:
        f_free, _, _ = parse_items(fresh_text)
        if name in f_free:
            fresh_text = fresh_text.replace(f_free[name], e_free[name], 1)

    # Widen fresh's import to cover members only the existing file had, rather
    # than emitting a second `use` for the same module path (a duplicate-name
    # error). Phase 42.8.c.2.iv.D.
    for path, members in plan.get("merged_imports", {}).items():
        # `path` comes from the whitespace-stripped form, so it already begins
        # with "use"; re-insert the space rather than prefixing a second one.
        widened = "{}{{{}}};".format(
            path.replace("use", "use ", 1), ", ".join(sorted(members))
        )
        for line in fresh_text.split("\n"):
            flat = re.sub(r"\s+", "", line).rstrip(";")
            if flat.startswith(path + "{") or flat == "use" + path.lstrip("use"):
                fresh_text = fresh_text.replace(line, widened, 1)
                break

    lines = fresh_text.split("\n")

    # Methods go at the end of the impl block they came from, innermost-last so
    # earlier insertions do not shift later line numbers.
    insertions = []
    for impl_name, method_names in plan["carried_methods"].items():
        for i, line in enumerate(lines):
            m = IMPL_RE.match(line)
            if m and m.group("name") == impl_name and "{" in line:
                end = _block_end(lines, i)
                body = "\n".join(
                    "\n" + e_impls[impl_name][name] for name in method_names
                )
                insertions.append((end, body))
                break
    for at, body in sorted(insertions, key=lambda x: -x[0]):
        lines.insert(at, body)

    text = "\n".join(lines)

    # Free functions go before the first impl, or at the end of the verus block.
    if plan["carried_free_fns"]:
        block = "\n".join("\n" + e_free[name] for name in plan["carried_free_fns"])
        m = re.search(r"^impl\b", text, re.M)
        if m:
            text = text[: m.start()] + block.strip("\n") + "\n\n" + text[m.start() :]
        else:
            text = text.rstrip() + "\n" + block + "\n"

    # Imports the preserved code needs.
    if plan["carried_imports"]:
        last = None
        out_lines = text.split("\n")
        for i, line in enumerate(out_lines):
            if IMPORT_RE.match(line):
                last = i
        if last is not None:
            for imp in reversed(plan["carried_imports"]):
                out_lines.insert(last + 1, imp)
            text = "\n".join(out_lines)

    return text


def render_report(plan, fresh, existing):
    out = ["merge plan: {} -> {}".format(os.path.basename(fresh), os.path.basename(existing))]
    out.append(
        "  free functions carried over : {}".format(
            ", ".join(plan["carried_free_fns"]) or "(none)"
        )
    )
    for impl_name, methods in plan["carried_methods"].items():
        out.append("  methods carried into impl {}: {}".format(impl_name, ", ".join(methods)))
    out.append(
        "  imports carried over        : {}".format(len(plan["carried_imports"]))
    )
    if plan["impls_absent_from_fresh"]:
        out.append(
            "  ERROR: fresh output has no impl for: "
            + ", ".join(plan["impls_absent_from_fresh"])
        )
    return "\n".join(out)


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("fresh")
    p.add_argument("existing")
    p.add_argument("-o", "--out")
    p.add_argument("--report", action="store_true", help="describe the merge only")
    p.add_argument(
        "--preserve",
        action="append",
        default=[],
        metavar="FN",
        help="keep the EXISTING file's version of this free function even though "
        "fresh emits one (repeatable). For helpers the transpiler synthesises "
        "naively but which were hand-verified in place.",
    )
    args = p.parse_args(argv)

    fresh_text = open(args.fresh).read()
    existing_text = open(args.existing).read()

    if args.report:
        print(
            render_report(
                plan_merge(fresh_text, existing_text, args.preserve),
                args.fresh,
                args.existing,
            )
        )
        return 0

    try:
        merged = merge(fresh_text, existing_text, args.preserve)
    except ValueError as e:
        sys.stderr.write("error: {}\n".format(e))
        return 1
    if args.out:
        with open(args.out, "w") as f:
            f.write(merged)
    else:
        sys.stdout.write(merged)
    return 0


if __name__ == "__main__":
    sys.exit(main())
