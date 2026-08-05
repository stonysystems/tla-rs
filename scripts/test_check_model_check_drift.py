#!/usr/bin/env python3
"""Tests for check_model_check_drift.py (Phase 37.2.1.j).

The guard has exactly one job: ignore wall-clock noise, catch everything else.
Both halves are load-bearing — a guard that flags timing gets disabled, and a
guard that ignores state counts is the status quo that let the artifacts rot
for months (37.2.1.i). So both are tested here, including against a real git
repository rather than only the pure functions.
"""

import json
import os
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
SCRIPT = os.path.join(HERE, "check_model_check_drift.py")

sys.path.insert(0, HERE)
import check_model_check_drift as drift  # noqa: E402


def artifact(states=1, elapsed=4, protocol="src/protocol/Paxos/paxos.rs", extra=None):
    doc = {
        "protocol": protocol,
        "result": "ok",
        "stop_reason": "exhausted",
        "search": {"mode": "bfs", "timeout_ms": 30000},
        "summary": {
            "states": states,
            "transitions": 2,
            "depth": 0,
            "elapsed_ms": elapsed,
            "timing": {"successor_solving_ms": elapsed * 2},
            "pruned_by_por": 0,
        },
    }
    if extra:
        doc["summary"].update(extra)
    return json.dumps(doc, indent=2)


class TestNormalization(unittest.TestCase):
    def test_timing_fields_are_dropped(self):
        a = drift.normalize("x.json", artifact(elapsed=4))
        b = drift.normalize("x.json", artifact(elapsed=9999))
        self.assertEqual(a, b)

    def test_timing_subtree_is_dropped(self):
        norm = drift.normalize("x.json", artifact())
        self.assertNotIn("successor_solving_ms", norm)
        self.assertNotIn('"timing"', norm)

    def test_timeout_ms_is_kept_despite_the_suffix(self):
        # A config input, not wall-clock: changing it must be visible.
        norm = drift.normalize("x.json", artifact())
        self.assertIn("timeout_ms", norm)
        self.assertIn("30000", norm)

    def test_state_count_survives_normalization(self):
        a = drift.normalize("x.json", artifact(states=1))
        b = drift.normalize("x.json", artifact(states=2))
        self.assertNotEqual(a, b)

    def test_key_order_does_not_matter(self):
        one = json.dumps({"b": 1, "a": {"d": 2, "c": 3}})
        two = json.dumps({"a": {"c": 3, "d": 2}, "b": 1})
        self.assertEqual(drift.normalize("x.json", one), drift.normalize("x.json", two))

    def test_git_rev_line_is_dropped_from_text_artifacts(self):
        a = drift.normalize("MANIFEST.txt", "artifacts:\n  git_rev: aaaa\n  n: 3\n")
        b = drift.normalize("MANIFEST.txt", "artifacts:\n  git_rev: bbbb\n  n: 3\n")
        self.assertEqual(a, b)

    def test_other_text_changes_are_kept(self):
        a = drift.normalize("MANIFEST.txt", "  git_rev: aaaa\n  n: 3\n")
        b = drift.normalize("MANIFEST.txt", "  git_rev: aaaa\n  n: 4\n")
        self.assertNotEqual(a, b)

    def test_jsonl_is_normalized_per_line(self):
        a = drift.normalize("s.jsonl", '{"a":1,"elapsed_ms":5}\n{"b":2}\n')
        b = drift.normalize("s.jsonl", '{"elapsed_ms":900,"a":1}\n{"b":2}\n')
        self.assertEqual(a, b)

    def test_invalid_json_is_reported_not_swallowed(self):
        with self.assertRaises(ValueError):
            drift.normalize("x.json", "{not json")


class TestDiffDescription(unittest.TestCase):
    def test_changed_value_is_pinpointed(self):
        old = drift.normalize("x.json", artifact(states=1))
        new = drift.normalize("x.json", artifact(states=2))
        notes = drift.describe_json_diff(old, new)
        self.assertTrue(any("/summary/states" in n and "1 -> 2" in n for n in notes))

    def test_added_field_is_pinpointed(self):
        old = drift.normalize("x.json", artifact())
        new = drift.normalize("x.json", artifact(extra={"eq_constraints": 10}))
        notes = drift.describe_json_diff(old, new)
        self.assertTrue(any(n.startswith("+ ") and "eq_constraints" in n for n in notes))

    def test_removed_field_is_pinpointed(self):
        old = drift.normalize("x.json", artifact(extra={"eq_constraints": 10}))
        new = drift.normalize("x.json", artifact())
        notes = drift.describe_json_diff(old, new)
        self.assertTrue(any(n.startswith("- ") and "eq_constraints" in n for n in notes))

    def test_long_diffs_are_truncated_with_a_count(self):
        old = drift.normalize("x.json", artifact())
        new = drift.normalize(
            "x.json", artifact(extra={"f{}".format(i): i for i in range(40)})
        )
        notes = drift.describe_json_diff(old, new, limit=5)
        self.assertEqual(len(notes), 6)
        self.assertIn("more", notes[-1])


class TestAgainstGit(unittest.TestCase):
    """End-to-end against a real repository, since the guard shells out to git."""

    def setUp(self):
        self.tmp = tempfile.mkdtemp()
        self.dir = os.path.join(self.tmp, "reports", "model_check")
        os.makedirs(self.dir)
        self.path = os.path.join("reports", "model_check", "paxos_small.json")
        self.write(artifact())
        for cmd in (
            ["git", "init", "-q"],
            ["git", "config", "user.email", "t@example.com"],
            ["git", "config", "user.name", "t"],
            ["git", "add", "-A"],
            ["git", "commit", "-qm", "seed"],
        ):
            subprocess.run(cmd, cwd=self.tmp, check=True, capture_output=True)
        self.cwd = os.getcwd()
        os.chdir(self.tmp)

    def tearDown(self):
        os.chdir(self.cwd)

    def write(self, text):
        with open(os.path.join(self.tmp, self.path), "w") as f:
            f.write(text)

    def run_cli(self, *args):
        return subprocess.run(
            [sys.executable, SCRIPT] + list(args), capture_output=True, text=True
        )

    def test_clean_tree_passes(self):
        r = self.run_cli()
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertIn("match HEAD", r.stdout)

    def test_timing_only_change_passes(self):
        self.write(artifact(elapsed=12345))
        r = self.run_cli()
        self.assertEqual(r.returncode, 0, r.stdout)
        self.assertIn("match HEAD", r.stdout)

    def test_state_count_change_fails(self):
        self.write(artifact(states=99))
        r = self.run_cli()
        self.assertEqual(r.returncode, 1)
        self.assertIn("/summary/states", r.stdout)
        self.assertIn("drifted", r.stdout)

    def test_wrong_cwd_path_change_fails(self):
        # The exact drift found in 37.2.1.i.
        self.write(artifact(protocol="../src/protocol/Paxos/paxos.rs"))
        r = self.run_cli()
        self.assertEqual(r.returncode, 1)
        self.assertIn("/protocol", r.stdout)

    def test_new_telemetry_field_fails(self):
        self.write(artifact(extra={"eq_constraints": 10}))
        r = self.run_cli()
        self.assertEqual(r.returncode, 1)
        self.assertIn("eq_constraints", r.stdout)

    def test_deleted_artifact_is_reported(self):
        os.remove(os.path.join(self.tmp, self.path))
        r = self.run_cli()
        self.assertEqual(r.returncode, 1)
        self.assertIn("missing", r.stdout)

    def test_warn_only_reports_but_exits_zero(self):
        self.write(artifact(states=99))
        r = self.run_cli("--warn-only")
        self.assertEqual(r.returncode, 0)
        self.assertIn("drifted", r.stdout)

    def test_json_output(self):
        self.write(artifact(states=99))
        r = self.run_cli("--json")
        self.assertEqual(r.returncode, 1)
        payload = json.loads(r.stdout)
        self.assertEqual(payload["findings"][0]["status"], "drifted")

    def test_readme_edit_does_not_trip_the_scoped_guard(self):
        with open(os.path.join(self.tmp, "reports", "model_check", "MANIFEST.txt"), "w") as f:
            f.write("artifacts:\n    - paxos_small.json\n")
        with open(os.path.join(self.tmp, "reports", "model_check", "README.md"), "w") as f:
            f.write("hand-written notes\n")
        subprocess.run(["git", "add", "-A"], cwd=self.tmp, check=True, capture_output=True)
        subprocess.run(
            ["git", "commit", "-qm", "manifest+readme"], cwd=self.tmp, check=True, capture_output=True
        )
        with open(os.path.join(self.tmp, "reports", "model_check", "README.md"), "w") as f:
            f.write("hand-written notes, edited\n")
        self.assertEqual(self.run_cli().returncode, 0)
        self.assertEqual(self.run_cli("--all-files").returncode, 1)

    def test_list_volatile_exits_zero_and_names_the_exception(self):
        r = self.run_cli("--list-volatile")
        self.assertEqual(r.returncode, 0)
        self.assertIn("elapsed_ms", r.stdout)
        self.assertIn("timeout_ms", r.stdout)


class TestManifestScope(unittest.TestCase):
    """The guard must cover generated artifacts and nothing else.

    `reports/model_check/` also holds a hand-written README and parity exports
    from other scripts. Diffing those would fail on any ordinary doc edit, and
    a guard that cries wolf on documentation is a guard someone deletes.
    """

    MANIFEST = """source_first_matrix_artifacts:
  generated_by: scripts/run_model_check_matrix.sh
  git_rev: abc123
  output_dir: reports/model_check
  artifacts:
    - twophase_small.json
    - OPTIMIZATION_DELTAS.md
"""

    def test_manifest_listed_artifacts_are_in_scope(self):
        scope = drift.manifest_scope("reports/model_check", self.MANIFEST)
        self.assertIn("reports/model_check/twophase_small.json", scope)
        self.assertIn("reports/model_check/OPTIMIZATION_DELTAS.md", scope)

    def test_the_manifest_itself_is_in_scope(self):
        scope = drift.manifest_scope("reports/model_check", self.MANIFEST)
        self.assertIn("reports/model_check/MANIFEST.txt", scope)

    def test_unlisted_files_are_out_of_scope(self):
        scope = drift.manifest_scope("reports/model_check", self.MANIFEST)
        self.assertNotIn("reports/model_check/README.md", scope)
        self.assertNotIn("reports/model_check/parity/tlc/twophase/states.jsonl", scope)

    def test_header_keys_are_not_mistaken_for_artifacts(self):
        scope = drift.manifest_scope("reports/model_check", self.MANIFEST)
        for path in scope:
            self.assertNotIn("generated_by", path)
            self.assertNotIn("git_rev", path)


class TestCiWiring(unittest.TestCase):
    def setUp(self):
        with open(
            os.path.join(os.path.dirname(HERE), ".github", "workflows", "ci.yml")
        ) as f:
            self.ci = f.read()

    def test_guard_runs_after_regeneration(self):
        self.assertIn("scripts/check_model_check_drift.py", self.ci)
        regen = self.ci.index("run_model_check_matrix.sh")
        guard = self.ci.index("check_model_check_drift.py")
        self.assertLess(regen, guard, "the guard must run after regeneration")

    def test_guard_is_not_warn_only_in_ci(self):
        block = self.ci.split("check_model_check_drift.py", 1)[1][:200]
        self.assertNotIn("--warn-only", block)


if __name__ == "__main__":
    unittest.main()
