#!/usr/bin/env python3
"""Tests for apply_triggers.py (Phase 54.5+).

The applier writes what Verus already chose, so its failure modes are silent:
a wrong annotation still compiles often enough to be missed, and an
over-restrictive one breaks a proof somewhere else entirely. Both real bugs
found while rolling it out over protocol/RSL are pinned here.
"""

import json
import os
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import apply_triggers as ap  # noqa: E402


def entry(path, line, groups):
    return {
        "file": path,
        "line": line,
        "expr": "e",
        "multiline": False,
        "triggers": [{"terms": g} for g in groups],
        "trigger_count": len(groups),
    }


class TestAnnotationRendering(unittest.TestCase):
    def test_single_group_single_term(self):
        self.assertEqual(ap.annotation([["s.contains(p)"]]), "#![trigger s.contains(p)]")

    def test_conjunction_stays_one_trigger(self):
        # Both terms needed to bind the variables.
        self.assertEqual(ap.annotation([["p1@", "p2@"]]), "#![trigger p1@, p2@]")

    def test_alternatives_become_separate_attributes(self):
        # Real bug: flattening these into `#![trigger replies[i], batch[i]]` is
        # strictly more restrictive and broke state_machine.rs's postcondition.
        self.assertEqual(
            ap.annotation([["replies[i]"], ["batch[i]"]]),
            "#![trigger replies[i]] #![trigger batch[i]]",
        )


class TestBinderVars(unittest.TestCase):
    def test_typed_binders_yield_only_the_names(self):
        b = "|opn: OperationNumber, p: RslPacket|"
        self.assertEqual(ap.binder_vars(b, 1, len(b)), ["opn", "p"])

    def test_generic_type_is_not_split_on_its_comma(self):
        b = "|m: Map<int, bool>|"
        self.assertEqual(ap.binder_vars(b, 1, len(b)), ["m"])

    def test_untyped_binder(self):
        b = "|s|"
        self.assertEqual(ap.binder_vars(b, 1, len(b)), ["s"])


class TestPlanning(unittest.TestCase):
    def plan(self, source, entries):
        tmp = tempfile.mkdtemp()
        path = os.path.join(tmp, "a.rs")
        with open(path, "w") as f:
            f.write(source)
        inv = {"entries": [entry(path, ln, gs) for ln, gs in entries]}
        return path, ap.plan_edits(inv)

    def test_annotation_is_inserted_after_the_binder(self):
        path, plans = self.plan(
            "ensures forall |i: int| 0 <= i < n ==> f(i),\n",
            [(1, [["f(i)"]])],
        )
        ap.apply_plan(plans)
        self.assertIn("forall |i: int| #![trigger f(i)] 0 <= i", open(path).read())

    def test_already_annotated_site_is_skipped(self):
        path, plans = self.plan(
            "ensures forall |i: int| #![trigger f(i)] 0 <= i < n ==> f(i),\n",
            [(1, [["f(i)"]])],
        )
        applied, skipped = ap.apply_plan(plans)
        self.assertEqual(applied, 0)
        self.assertEqual(skipped, 1)

    def test_closure_terms_are_skipped(self):
        # Verus chooses `s.map(|p| p@).contains(op)` and then refuses to let
        # anyone write it: "triggers cannot contain let/forall/exists/lambda".
        _, plans = self.plan(
            "ensures forall |op: P| s.map(|p: C| p@).contains(op) ==> q,\n",
            [(1, [["s.map(|p: C| p@).contains(op)"]])],
        )
        applied, skipped = ap.apply_plan(plans, dry_run=True)
        self.assertEqual((applied, skipped), (0, 1))

    def test_trigger_for_a_nested_quantifier_is_skipped(self):
        # The note points at the outer expression while the chosen trigger
        # belongs to an inner binder; attaching it here fails to compile with
        # "cannot find value `p` in this scope".
        _, plans = self.plan(
            "ensures forall |req: Request| r.contains(req) ==> exists |p: Pkt| s.contains(p),\n",
            [(1, [["s.contains(p)"]])],
        )
        applied, skipped = ap.apply_plan(plans, dry_run=True)
        self.assertEqual((applied, skipped), (0, 1))

    def test_two_notes_sharing_one_binder_annotate_once(self):
        _, plans = self.plan(
            "ensures forall |i: int| 0 <= i < n ==> f(i),\n",
            [(1, [["f(i)"]]), (1, [["f(i)"]])],
        )
        applied, skipped = ap.apply_plan(plans, dry_run=True)
        self.assertEqual(applied, 1)
        self.assertEqual(skipped, 1)

    def test_multiple_sites_in_one_file_all_apply(self):
        path, plans = self.plan(
            "a: forall |i: int| f(i),\nb: forall |j: int| g(j),\n",
            [(1, [["f(i)"]]), (2, [["g(j)"]])],
        )
        ap.apply_plan(plans)
        text = open(path).read()
        self.assertIn("#![trigger f(i)]", text)
        self.assertIn("#![trigger g(j)]", text)

    def test_applying_twice_is_idempotent(self):
        path, plans = self.plan(
            "ensures forall |i: int| 0 <= i < n ==> f(i),\n", [(1, [["f(i)"]])]
        )
        ap.apply_plan(plans)
        first = open(path).read()
        inv = {"entries": [entry(path, 1, [["f(i)"]])]}
        ap.apply_plan(ap.plan_edits(inv))
        self.assertEqual(open(path).read(), first)

    def test_missing_file_is_reported_not_crashed(self):
        inv = {"entries": [entry("/nonexistent/x.rs", 1, [["f(i)"]])]}
        applied, skipped = ap.apply_plan(ap.plan_edits(inv), dry_run=True)
        self.assertEqual(applied, 0)
        self.assertEqual(skipped, 1)

    def test_filter_limits_the_scope(self):
        inv = {"entries": [entry("src/a.rs", 1, [["f"]]), entry("other/b.rs", 1, [["g"]])]}
        plans = ap.plan_edits(inv, filter_prefix="src/")
        self.assertEqual([p[0] for p in plans], ["src/a.rs"])


if __name__ == "__main__":
    unittest.main()
