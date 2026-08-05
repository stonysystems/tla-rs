#!/usr/bin/env python3
"""Tests for merge_generated.py (Phase 42.8.c).

The tool exists because five RSL modules carry hand-written `skip_functions`
bodies, so `regenerate_rsl.sh` keeps those files untouched and no codegen
improvement can reach them. Merging is the way out: fresh output as the source
of truth, plus exactly the items the transpiler did not emit.

Placement is the part that can silently produce garbage -- a method spliced in
at top level becomes `&mut self` outside an impl -- so it is pinned here.
"""

import os
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import merge_generated as mg  # noqa: E402

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


FRESH = """use vstd::prelude::*;
use crate::a::B;

verus! {

pub exec fn emitted_free() -> u64 {
    1
}

impl CThing {
    pub exec fn emitted_method(&mut self) {
    }
}

} // verus!
"""

EXISTING = """use vstd::prelude::*;
use crate::a::B;
use crate::hand::Written;

verus! {

pub exec fn emitted_free() -> u64 {
    1
}

/// A hand-written helper the transpiler never emits.
pub exec fn preserved_free(x: u64) -> u64 {
    x + 1
}

impl CThing {
    pub exec fn emitted_method(&mut self) {
    }

    pub exec fn preserved_method(&mut self, y: u64) {
        let _ = y;
    }
}

} // verus!
"""


class TestParsing(unittest.TestCase):
    def test_free_functions_and_methods_are_separated(self):
        free, impls, imports = mg.parse_items(EXISTING)
        self.assertIn("emitted_free", free)
        self.assertIn("preserved_free", free)
        self.assertNotIn("preserved_method", free, "a method must not parse as free")
        self.assertEqual(set(impls["CThing"]), {"emitted_method", "preserved_method"})
        self.assertIn("use crate::hand::Written;", imports)

    def test_doc_comments_travel_with_the_item(self):
        free, _, _ = mg.parse_items(EXISTING)
        self.assertIn("A hand-written helper", free["preserved_free"])


class TestPlan(unittest.TestCase):
    def test_plan_lists_only_what_is_missing(self):
        plan = mg.plan_merge(FRESH, EXISTING)
        self.assertEqual(plan["carried_free_fns"], ["preserved_free"])
        self.assertEqual(plan["carried_methods"], {"CThing": ["preserved_method"]})
        self.assertIn("use crate::hand::Written;", plan["carried_imports"])

    def test_nothing_to_carry_when_files_agree(self):
        plan = mg.plan_merge(EXISTING, EXISTING)
        self.assertEqual(plan["carried_free_fns"], [])
        self.assertEqual(plan["carried_methods"], {})
        self.assertEqual(plan["carried_imports"], [])


class TestMerge(unittest.TestCase):
    def test_method_lands_inside_its_impl(self):
        merged = mg.merge(FRESH, EXISTING)
        _, impls, _ = mg.parse_items(merged)
        self.assertIn("preserved_method", impls["CThing"])
        free, _, _ = mg.parse_items(merged)
        self.assertNotIn(
            "preserved_method", free, "method must not be emitted at top level"
        )

    def test_free_function_is_carried_over(self):
        merged = mg.merge(FRESH, EXISTING)
        free, _, _ = mg.parse_items(merged)
        self.assertIn("preserved_free", free)

    def test_imports_needed_by_preserved_code_are_carried(self):
        merged = mg.merge(FRESH, EXISTING)
        self.assertIn("use crate::hand::Written;", merged)

    def test_merge_is_idempotent(self):
        once = mg.merge(FRESH, EXISTING)
        twice = mg.merge(once, EXISTING)
        self.assertEqual(mg.parse_items(once)[0].keys(), mg.parse_items(twice)[0].keys())
        self.assertEqual(
            mg.parse_items(once)[1]["CThing"].keys(),
            mg.parse_items(twice)[1]["CThing"].keys(),
        )

    def test_missing_impl_in_fresh_is_an_error_not_a_silent_drop(self):
        fresh_without_impl = FRESH.replace(
            "impl CThing {\n    pub exec fn emitted_method(&mut self) {\n    }\n}\n", ""
        )
        with self.assertRaises(ValueError):
            mg.merge(fresh_without_impl, EXISTING)

    def test_emitted_bodies_come_from_fresh(self):
        # The whole point: codegen improvements must survive the merge.
        fresh_improved = FRESH.replace("    1\n", "    #![trigger x] 2\n")
        merged = mg.merge(fresh_improved, EXISTING)
        self.assertIn("#![trigger x]", merged)




class MultiLineConstructs(unittest.TestCase):
    """Phase 42.8.c: two parser bugs that made merged output fail to *parse*,
    upstream of the signature mismatches 42.8.c.2.iv records. Both were found by
    running the merge over all seven RSL modules and feeding the result to
    rustfmt, not by any existing test."""

    def test_rustfmt_wrapped_import_is_captured_whole(self):
        # rustfmt wraps long imports. Capturing only the first line leaves
        # `use crate::x::{` dangling -- an unclosed delimiter.
        existing = (
            "use crate::x::{\n"
            "    alpha, beta,\n"
            "};\n"
            "use crate::solo::Thing;\n"
        )
        _, _, imports = mg.parse_items(existing)
        self.assertEqual(len(imports), 2, f"expected 2 imports, got {imports!r}")
        self.assertTrue(
            any(i.count("{") == i.count("}") for i in imports if "{" in i),
            f"wrapped import was not captured whole: {imports!r}",
        )

    def test_wrapped_and_flat_imports_compare_equal(self):
        flat = "use crate::x::{alpha, beta};"
        wrapped = "use crate::x::{\n    beta, alpha,\n};"
        self.assertEqual(
            mg._import_path(flat),
            mg._import_path(wrapped),
            "a wrapped import must not be carried over as a duplicate of its flat form",
        )

    def test_block_end_does_not_stop_inside_an_open_paren(self):
        # Braces balance on the `=~= (` line while the paren is still open;
        # stopping there truncates the body mid-expression.
        lines = [
            "pub proof fn f() {",
            "    assert(g(s.push(x), r) =~= (",
            "        h(a) + h(b)",
            "    ));",
            "}",
            "pub proof fn next() {}",
        ]
        end = mg._block_end(lines, 0)
        self.assertEqual(
            end, 4, f"block ended at line {end} ({lines[end]!r}), truncating the body"
        )

    def test_block_end_still_handles_a_plain_body(self):
        lines = ["fn f() {", "    let x = 1;", "}", "fn g() {}"]
        self.assertEqual(mg._block_end(lines, 0), 2)




class PreserveOverride(unittest.TestCase):
    """Phase 42.8.c: the transpiler synthesises some helpers naively -- a `for`
    loop over `m.iter()` where the checked-in file holds a hand-verified `while`
    loop with invariants. Merging without this replaces verified code with code
    that does not verify, silently. `--preserve` names those helpers."""

    FRESH = (
        "verus! {\n"
        "pub fn helper(m: &Map) -> Map {\n"
        "    naive_body()\n"
        "}\n"
        "pub fn other() {}\n"
        "} // verus!\n"
    )
    EXISTING = (
        "verus! {\n"
        "pub fn helper(m: &Map) -> Map {\n"
        "    verified_body_with_invariants()\n"
        "}\n"
        "pub fn other() {}\n"
        "} // verus!\n"
    )

    def test_without_preserve_fresh_wins(self):
        out = mg.merge(self.FRESH, self.EXISTING)
        self.assertIn("naive_body", out)
        self.assertNotIn("verified_body_with_invariants", out)

    def test_with_preserve_existing_wins(self):
        out = mg.merge(self.FRESH, self.EXISTING, ["helper"])
        self.assertIn("verified_body_with_invariants", out)
        self.assertNotIn("naive_body", out)

    def test_preserve_leaves_other_functions_on_fresh(self):
        out = mg.merge(self.FRESH, self.EXISTING, ["helper"])
        self.assertIn("pub fn other", out)

    def test_unknown_preserve_name_is_an_error_not_a_silent_no_op(self):
        # Typing the name wrong must not quietly produce the un-preserved merge.
        with self.assertRaises(ValueError):
            mg.merge(self.FRESH, self.EXISTING, ["helpr"])




class PreserveListIsWiredUp(unittest.TestCase):
    """Phase 42.8.c.2.iv.A: `--preserve` only helps if something passes it. The
    list lives in scripts/rsl_merge_preserve.txt and regenerate_rsl.sh turns it
    into flags; these check the list is real and that every name in it actually
    exists in the file it claims to protect -- a stale entry would make
    merge_generated.py raise mid-regeneration."""

    LIST = os.path.join(REPO_ROOT, "scripts", "rsl_merge_preserve.txt")

    def _entries(self):
        out = []
        with open(self.LIST) as fh:
            for line in fh:
                line = line.split("#", 1)[0].strip()
                if line:
                    parts = line.split()
                    self.assertEqual(
                        len(parts), 2, f"expected '<module> <fn>', got {line!r}"
                    )
                    out.append(tuple(parts))
        return out

    def test_list_exists_and_covers_the_known_collision(self):
        self.assertIn(
            ("learner", "filter_clearnerstate"),
            self._entries(),
            "filter_clearnerstate must stay protected: the transpiler synthesises a "
            "naive version that would replace the hand-verified one",
        )

    def test_every_named_function_exists_in_its_generated_file(self):
        for module, fn in self._entries():
            path = os.path.join(REPO_ROOT, "src", "generated", "RSL", f"{module}_gen.rs")
            self.assertTrue(os.path.exists(path), f"no generated file for {module}")
            with open(path) as fh:
                src = fh.read()
            _, _, _ = mg.parse_items(src)
            free, _, _ = mg.parse_items(src)
            self.assertIn(
                fn,
                free,
                f"{fn} is listed for {module} but is not a free function in "
                f"{module}_gen.rs -- merge_generated.py would raise on it",
            )

    def test_regenerate_script_reads_the_list(self):
        with open(os.path.join(REPO_ROOT, "scripts", "regenerate_rsl.sh")) as fh:
            script = fh.read()
        self.assertIn("rsl_merge_preserve.txt", script)
        self.assertIn("--preserve", script)


if __name__ == "__main__":
    unittest.main()
