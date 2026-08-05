#!/usr/bin/env python3
"""Report functions a merge would silently rewrite (Phase 42.8.c.2.iv.A).

`regenerate_rsl.sh` compares fresh output against the checked-in file by
`pub exec fn` *name*. That misses the failure that actually happened: the
transpiler synthesises `filter_clearnerstate` as a naive `for` loop over
`m.iter()`, the checked-in file holds a hand-verified `while` loop with
invariants, both are named the same, and the merge replaces the verified one.
Name parity cannot see a body change, and `filter_clearnerstate` is a private
`fn` so it was not even in the comparison.

This looks at bodies. For every free function present in *both* files it
reports the ones whose text differs -- those are what a merge would rewrite.
Names listed in the preserve file are reported separately as already handled.

    check_merge_body_drift.py fresh.rs existing.rs [--preserve-list FILE] [--module NAME]

Exit status is 1 when an unprotected body would be rewritten, so it can gate a
regeneration. `--quiet` reports nothing on success.
"""

import argparse
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import merge_generated as mg  # noqa: E402


def load_preserve(path, module=None):
    """Names to treat as intentionally preserved, optionally for one module."""
    if not path or not os.path.exists(path):
        return set()
    out = set()
    with open(path) as fh:
        for line in fh:
            line = line.split("#", 1)[0].strip()
            if not line:
                continue
            parts = line.split()
            if len(parts) != 2:
                raise ValueError(f"expected '<module> <fn>', got {line!r}")
            mod, fn = parts
            if module is None or mod == module:
                out.add(fn)
    return out


def _normalise(text):
    """Ignore pure whitespace/indentation differences.

    rustfmt reflows the merged file, so a body that only re-wraps is not drift.
    Comparing token streams keeps the check on real changes.
    """
    return " ".join(text.split())


def body_drift(fresh_text, existing_text, preserve=frozenset()):
    """(unprotected, protected) function names whose bodies differ."""
    f_free, _, _ = mg.parse_items(fresh_text)
    e_free, _, _ = mg.parse_items(existing_text)

    unprotected, protected = [], []
    for name, e_body in e_free.items():
        if name not in f_free:
            continue  # not emitted fresh; the merge carries the existing one
        if _normalise(f_free[name]) == _normalise(e_body):
            continue
        (protected if name in preserve else unprotected).append(name)
    return sorted(unprotected), sorted(protected)


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("fresh")
    p.add_argument("existing")
    p.add_argument("--preserve-list")
    p.add_argument("--module", help="only apply preserve entries for this module")
    p.add_argument("--quiet", action="store_true")
    args = p.parse_args(argv)

    with open(args.fresh) as fh:
        fresh = fh.read()
    with open(args.existing) as fh:
        existing = fh.read()

    preserve = load_preserve(args.preserve_list, args.module)
    unprotected, protected = body_drift(fresh, existing, preserve)

    if protected and not args.quiet:
        print(
            "  preserved ({}): {}".format(len(protected), ", ".join(protected))
        )
    if unprotected:
        print(
            "  WOULD BE REWRITTEN ({}): {}".format(
                len(unprotected), ", ".join(unprotected)
            )
        )
        print(
            "  If any of these is hand-written, add it to the preserve list;\n"
            "  merging as-is replaces its body with transpiler output."
        )
        return 1
    if not args.quiet:
        print("  no unprotected body drift")
    return 0


if __name__ == "__main__":
    sys.exit(main())
