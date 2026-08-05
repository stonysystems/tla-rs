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


if __name__ == "__main__":
    unittest.main()
