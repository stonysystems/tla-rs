#!/usr/bin/env python3
"""Tests for trigger_exceptions.py (Phase 54 acceptance criterion).

The phase allows "zero notes, or a checked-in list of the deliberate
exceptions with a reason for each". A list that silently falls out of date
satisfies the letter of that and none of its intent, so `--check` is the part
that matters most here.
"""

import json
import os
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
SCRIPT = os.path.join(HERE, "trigger_exceptions.py")

sys.path.insert(0, HERE)
import trigger_exceptions as te  # noqa: E402


def entry(path, line=1, terms=None):
    return {
        "file": path,
        "line": line,
        "col": 1,
        "expr": "forall |i: int| f(i)",
        "multiline": False,
        "triggers": [{"terms": terms or ["f(i)"]}],
        "trigger_count": 1,
        "key": "{}::{}".format(path, line),
    }


def inventory(entries):
    return {
        "schema": "trigger-inventory/v1",
        "verus_version": "0.2026.08.02.b677dd5",
        "total_notes": len(entries),
        "entries": entries,
    }


class TestClassification(unittest.TestCase):
    def test_generated_files_are_their_own_reason(self):
        key, _, _ = te.classify(entry("src/generated/RSL/replica_gen.rs"))
        self.assertEqual(key, "generated")

    def test_everything_else_is_the_nested_quantifier_case(self):
        key, _, _ = te.classify(entry("src/protocol/Raft/refinement_proof/invariants.rs"))
        self.assertEqual(key, "nested-quantifier")

    def test_every_note_gets_a_reason(self):
        inv = inventory(
            [entry("src/generated/RSL/a_gen.rs"), entry("src/protocol/RSL/b.rs")]
        )
        groups = te.build(inv)
        self.assertEqual(sum(len(g["entries"]) for g in groups.values()), 2)
        for g in groups.values():
            self.assertGreater(len(g["reason"]), 40, "a reason must actually explain")


class TestRendering(unittest.TestCase):
    def test_totals_and_groups_are_stated(self):
        inv = inventory(
            [entry("src/generated/RSL/a_gen.rs"), entry("src/protocol/RSL/b.rs", 2)]
        )
        text = te.render(inv, te.build(inv))
        total, per = te.extract_counts(text)
        self.assertEqual(total, 2)
        self.assertEqual(per, {"generated": 1, "nested-quantifier": 1})

    def test_individual_sites_are_listed_for_actionable_groups(self):
        inv = inventory([entry("src/protocol/RSL/b.rs", 42, ["s.contains(p)"])])
        text = te.render(inv, te.build(inv))
        self.assertIn("src/protocol/RSL/b.rs:42", text)
        self.assertIn("s.contains(p)", text)


class TestCheck(unittest.TestCase):
    def run_cli(self, args, expect=None):
        r = subprocess.run(
            [sys.executable, SCRIPT] + args, capture_output=True, text=True
        )
        if expect is not None:
            assert r.returncode == expect, (r.returncode, r.stdout, r.stderr)
        return r

    def setUp(self):
        self.tmp = tempfile.mkdtemp()
        self.inv_path = os.path.join(self.tmp, "inv.json")
        with open(self.inv_path, "w") as f:
            json.dump(
                inventory(
                    [entry("src/generated/RSL/a_gen.rs"), entry("src/protocol/RSL/b.rs", 2)]
                ),
                f,
            )
        self.md = os.path.join(self.tmp, "exceptions.md")
        self.run_cli([self.inv_path, "-o", self.md], expect=0)

    def test_freshly_generated_list_passes_its_own_check(self):
        r = self.run_cli([self.inv_path, "--check", self.md], expect=0)
        self.assertIn("up to date", r.stdout)

    def test_a_stale_list_fails(self):
        # One more note appears and nobody regenerated the document.
        with open(self.inv_path, "w") as f:
            json.dump(
                inventory(
                    [
                        entry("src/generated/RSL/a_gen.rs"),
                        entry("src/protocol/RSL/b.rs", 2),
                        entry("src/protocol/RSL/c.rs", 3),
                    ]
                ),
                f,
            )
        r = self.run_cli([self.inv_path, "--check", self.md], expect=1)
        self.assertIn("out of date", r.stderr)

    def test_a_shifted_classification_fails_even_at_equal_totals(self):
        # Same count, different reasons -- the list still misdescribes reality.
        with open(self.inv_path, "w") as f:
            json.dump(
                inventory(
                    [entry("src/protocol/RSL/b.rs", 2), entry("src/protocol/RSL/c.rs", 3)]
                ),
                f,
            )
        self.run_cli([self.inv_path, "--check", self.md], expect=1)

    def test_missing_document_fails(self):
        self.run_cli(
            [self.inv_path, "--check", os.path.join(self.tmp, "nope.md")], expect=1
        )


class TestCiWiring(unittest.TestCase):
    def test_ci_checks_the_list_against_a_fresh_inventory(self):
        path = os.path.join(
            os.path.dirname(HERE), ".github", "workflows", "ci.yml"
        )
        with open(path) as f:
            ci = f.read()
        self.assertIn("scripts/trigger_exceptions.py trigger-inventory.json", ci)
        self.assertIn("--check reports/triggers/exceptions.md", ci)


class TestCommittedList(unittest.TestCase):
    def test_the_repo_list_states_a_total_and_reasons(self):
        path = os.path.join(
            os.path.dirname(HERE), "reports", "triggers", "exceptions.md"
        )
        with open(path) as f:
            total, per = te.extract_counts(f.read())
        self.assertIsNotNone(total, "the committed list must state a total")
        self.assertTrue(per, "the committed list must group notes by reason")
        self.assertEqual(total, sum(per.values()))


if __name__ == "__main__":
    unittest.main()
