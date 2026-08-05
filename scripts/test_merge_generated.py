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
        """(module, fn) pairs, using the real parser rather than a second one.

        `check_merge_body_drift.load_preserve` is the parser the tooling uses; a
        copy here would drift from it -- and it already grew a third
        `accept-fresh` field that a private copy would have rejected.
        """
        import check_merge_body_drift as cd  # noqa: PLC0415

        out = []
        with open(self.LIST) as fh:
            for line in fh:
                line = line.split("#", 1)[0].strip()
                if not line:
                    continue
                parts = line.split()
                self.assertIn(
                    len(parts), (2, 3), f"unparseable preserve line: {line!r}"
                )
                out.append((parts[0], parts[1], parts[2] if len(parts) == 3 else "preserve"))
        # the real parser must accept the whole file
        cd.load_preserve(self.LIST)
        return out

    def test_list_exists_and_covers_the_known_collision(self):
        self.assertIn(
            ("learner", "filter_clearnerstate", "preserve"),
            self._entries(),
            "filter_clearnerstate must stay protected: the transpiler synthesises a "
            "naive version that would replace the hand-verified one",
        )

    def test_every_named_function_exists_in_its_generated_file(self):
        for module, fn, _kind in self._entries():
            path = os.path.join(REPO_ROOT, "src", "generated", "RSL", f"{module}_gen.rs")
            self.assertTrue(os.path.exists(path), f"no generated file for {module}")
            import check_merge_body_drift as cd  # noqa: PLC0415

            with open(path) as fh:
                src = fh.read()
            # Free functions *and* impl methods -- the RSL protocol actions are
            # `&mut self` methods, and requiring free functions here would reject
            # the 17 of them the preserve list now covers.
            bodies = cd._all_bodies(src)
            names = set(bodies) | {n.split("::")[-1] for n in bodies}
            self.assertIn(
                fn,
                names,
                f"{fn} is listed for {module} but is not a function in "
                f"{module}_gen.rs -- a stale entry the tooling would trip on",
            )

    def test_regenerate_script_reads_the_list(self):
        with open(os.path.join(REPO_ROOT, "scripts", "regenerate_rsl.sh")) as fh:
            script = fh.read()
        self.assertIn("rsl_merge_preserve.txt", script)
        self.assertIn("--preserve", script)




class OverlappingBraceImports(unittest.TestCase):
    """Phase 42.8.c.2.iv.D. Fresh `use X::{a, b}` plus a carried
    `use X::{b, a, c}` is a duplicate-name error, not two imports -- the earlier
    `_import_path` normalisation compared whole member sets, so the two looked
    distinct. The fix widens fresh's import instead of emitting a second one."""

    FRESH = "verus! {\nuse crate::x::{a, b};\npub fn f() {}\n} // verus!\n"
    EXISTING = (
        "verus! {\nuse crate::x::{b, a, c};\npub fn f() {}\npub fn g() {}\n} // verus!\n"
    )

    def test_module_path_is_imported_once(self):
        out = mg.merge(self.FRESH, self.EXISTING)
        uses = [l for l in out.split("\n") if l.strip().startswith("use crate::x")]
        self.assertEqual(len(uses), 1, f"expected one import, got {uses!r}")

    def test_the_extra_member_survives(self):
        out = mg.merge(self.FRESH, self.EXISTING)
        use_line = next(l for l in out.split("\n") if "crate::x" in l)
        for member in ("a", "b", "c"):
            self.assertIn(member, use_line, f"{member} missing from {use_line!r}")

    def test_no_double_use_keyword(self):
        out = mg.merge(self.FRESH, self.EXISTING)
        self.assertNotIn("use use", out.replace("\n", " "))




class ContractStructLiteral(unittest.TestCase):
    """Phase 42.8.c.2.iv.D. A struct literal inside a `requires` clause --
    `UpperBound::UpperBoundFinite{n: ..}` -- opens and closes braces on one line.
    Treating that as the body-opening brace truncated CExecutorExecute from 99
    lines to 5, and the merge then carried the fragment. The body-opening brace
    is the one still open at end of line."""

    def test_struct_literal_in_requires_does_not_end_the_block(self):
        lines = [
            "pub exec fn f(s: &S) -> (r: R)",
            "requires",
            "    Lt(s.x as int, UpperBound::UpperBoundFinite{n: s.max as int}),",
            "ensures",
            "    r.valid(),",
            "{",
            "    body();",
            "}",
            "pub exec fn next() {}",
        ]
        end = mg._block_end(lines, 0)
        self.assertEqual(
            end, 7, f"block ended at line {end} ({lines[end]!r}), truncating the body"
        )

    def test_parsed_body_is_brace_balanced(self):
        src = (
            "verus! {\n"
            "pub exec fn f(s: &S) -> (r: R)\n"
            "requires\n"
            "    Lt(s.x, Bound::Finite{n: s.max}),\n"
            "{\n"
            "    body();\n"
            "}\n"
            "} // verus!\n"
        )
        free, _, _ = mg.parse_items(src)
        body = free["f"]
        self.assertEqual(body.count("{"), body.count("}"), body)




class SingleNameImportOverlap(unittest.TestCase):
    """Phase 42.8.c.2.iv.H. `use X::a;` and `use X::{a, b, c};` are the same
    module path. Treating a single-name import as having none meant both were
    emitted (E0252) and, once that was patched, that fresh's single-name form was
    never widened -- so `b` and `c` went missing and the file stopped compiling
    for the opposite reason."""

    FRESH = "verus! {\nuse crate::x::a;\npub fn f() {}\n} // verus!\n"
    EXISTING = "verus! {\nuse crate::x::{a, b, c};\npub fn f() {}\npub fn g() {}\n} // verus!\n"

    def test_module_path_of_a_single_name_import(self):
        self.assertEqual(mg._module_path("use crate::x::a;"), "usecrate::x::")
        self.assertEqual(mg._module_path("use crate::x::{a, b};"), "usecrate::x::")

    def test_members_of_a_single_name_import(self):
        self.assertEqual(mg._members("use crate::x::a;"), ["a"])

    def test_imported_once_and_all_members_kept(self):
        out = mg.merge(self.FRESH, self.EXISTING)
        uses = [l for l in out.split("\n") if l.strip().startswith("use crate::x")]
        self.assertEqual(len(uses), 1, f"expected one import, got {uses!r}")
        for member in ("a", "b", "c"):
            self.assertIn(member, uses[0], f"{member} missing from {uses[0]!r}")


class BodyBraceIsTopLevel(unittest.TestCase):
    """Phase 42.8.c.2.iv.H. A contract can contain braces that stay open across a
    line -- `=~= ( if cond { .. } else { .. } )` -- so "still open at end of line"
    is not enough. The body-opening brace is the one outside every paren."""

    def test_if_else_inside_parens_in_a_contract(self):
        lines = [
            "proof fn f(s: Seq<T>, x: T)",
            "    ensures",
            "        G(s.push(x)) =~= (",
            "            if P(x) {",
            "                G(s)",
            "            } else {",
            "                G(s).push(x)",
            "            }",
            "        ),",
            "{",
            "    body();",
            "}",
            "proof fn next() {}",
        ]
        self.assertEqual(mg._block_end(lines, 0), 11)


if __name__ == "__main__":
    unittest.main()
