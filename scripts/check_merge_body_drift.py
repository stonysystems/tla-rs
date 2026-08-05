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
    """(preserved, accepted) function names, optionally for one module.

    A line is `<module> <fn>` to keep the existing body, or
    `<module> <fn> accept-fresh` to record that the drift was reviewed and the
    transpiler's version is the one to take. The second kind matters as much as
    the first: without it the check reports the same reviewed items on every run,
    and a report that is always noisy stops being read -- which is how the
    original body swap slipped through in the first place.
    """
    if not path or not os.path.exists(path):
        return set(), set()
    preserved, accepted = set(), set()
    with open(path) as fh:
        for line in fh:
            line = line.split("#", 1)[0].strip()
            if not line:
                continue
            parts = line.split()
            if len(parts) == 2:
                mod, fn, kind = parts[0], parts[1], "preserve"
            elif len(parts) == 3:
                mod, fn, kind = parts
                if kind != "accept-fresh":
                    raise ValueError(
                        f"third field must be 'accept-fresh', got {kind!r} in {line!r}"
                    )
            else:
                raise ValueError(
                    f"expected '<module> <fn>' or '<module> <fn> accept-fresh', got {line!r}"
                )
            if module is None or mod == module:
                (preserved if kind == "preserve" else accepted).add(fn)
    return preserved, accepted


def _normalise(text):
    """Ignore pure whitespace/indentation differences.

    rustfmt reflows the merged file, so a body that only re-wraps is not drift.
    Comparing token streams keeps the check on real changes.
    """
    return " ".join(text.split())


def _all_bodies(text):
    """Every function body in the file, free functions *and* impl methods.

    Comparing only free functions was a real hole: the protocol actions are
    `&mut self` methods, so an entire module's implementations went unchecked.
    executor's `CExecutorProcessAppStateRequest` is a 52-line implementation in
    the checked-in file and a 59-line `assume(false)` stub in fresh output, and
    the report still read clean.
    """
    free, impls, _ = mg.parse_items(text)
    out = dict(free)
    for impl_name, methods in impls.items():
        for method, body in methods.items():
            out[f"{impl_name}::{method}"] = body
    return out


def body_drift(fresh_text, existing_text, preserve=frozenset(), accept=frozenset()):
    """(unreviewed, preserved, accepted) function names whose bodies differ."""
    fresh = _all_bodies(fresh_text)
    existing = _all_bodies(existing_text)

    def listed(name, names):
        # accept either `method` or `Impl::method` in the preserve list
        return name in names or name.split("::")[-1] in names

    unreviewed, preserved, accepted = [], [], []
    for name, e_body in existing.items():
        if name not in fresh:
            continue  # not emitted fresh; the merge carries the existing one
        if _normalise(fresh[name]) == _normalise(e_body):
            continue
        if listed(name, preserve):
            preserved.append(name)
        elif listed(name, accept):
            accepted.append(name)
        else:
            unreviewed.append(name)
    return sorted(unreviewed), sorted(preserved), sorted(accepted)


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

    preserve, accept = load_preserve(args.preserve_list, args.module)
    unreviewed, preserved, accepted = body_drift(fresh, existing, preserve, accept)

    if not args.quiet:
        if preserved:
            print("  preserved ({}): {}".format(len(preserved), ", ".join(preserved)))
        if accepted:
            print(
                "  reviewed, taking fresh ({}): {}".format(
                    len(accepted), ", ".join(accepted)
                )
            )
    if unreviewed:
        print(
            "  UNREVIEWED DRIFT ({}): {}".format(
                len(unreviewed), ", ".join(unreviewed)
            )
        )
        print(
            "  Decide each: add `<module> <fn>` to keep the existing body, or\n"
            "  `<module> <fn> accept-fresh` to record that fresh output is correct."
        )
        return 1
    if not args.quiet:
        print("  no unreviewed body drift")
    return 0


if __name__ == "__main__":
    sys.exit(main())
