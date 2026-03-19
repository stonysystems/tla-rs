#!/usr/bin/env python3
"""Tests for diff_parity_by_depth.py (Phase 36.1.9)."""

import json
import os
import subprocess
import sys
import tempfile
import unittest

SCRIPT = os.path.join(os.path.dirname(__file__), 'diff_parity_by_depth.py')


def write_jsonl(path, entries):
    """Write a list of dicts as JSONL."""
    with open(path, 'w') as f:
        for entry in entries:
            f.write(json.dumps(entry) + '\n')


class TestDiffParityByDepth(unittest.TestCase):

    def run_script(self, left_entries, right_entries, extra_args=None):
        """Run the diff script on two JSONL inputs, return (stdout, stderr, exitcode)."""
        with tempfile.TemporaryDirectory() as d:
            left_path = os.path.join(d, 'left.jsonl')
            right_path = os.path.join(d, 'right.jsonl')
            write_jsonl(left_path, left_entries)
            write_jsonl(right_path, right_entries)
            cmd = [sys.executable, SCRIPT, left_path, right_path]
            if extra_args:
                cmd.extend(extra_args)
            result = subprocess.run(cmd, capture_output=True, text=True)
            return result.stdout, result.stderr, result.returncode

    def run_json(self, left_entries, right_entries, extra_args=None):
        """Run script with --json and return parsed report."""
        args = ['--json']
        if extra_args:
            args.extend(extra_args)
        stdout, stderr, code = self.run_script(left_entries, right_entries, args)
        return json.loads(stdout), code

    def test_identical_exports_parity(self):
        entries = [
            {"state": {"x": 0}, "depth": 0, "initial": True},
            {"state": {"x": 1}, "depth": 1, "initial": False},
        ]
        report, code = self.run_json(entries, entries)
        self.assertEqual(code, 0)
        self.assertTrue(report['parity'])
        self.assertEqual(report['shared_total'], 2)
        self.assertIsNone(report['first_divergent_depth'])

    def test_mismatch_at_depth_1(self):
        left = [
            {"state": {"x": 0}, "depth": 0, "initial": True},
            {"state": {"x": 1}, "depth": 1, "initial": False},
        ]
        right = [
            {"state": {"x": 0}, "depth": 0, "initial": True},
            {"state": {"x": 2}, "depth": 1, "initial": False},
        ]
        report, code = self.run_json(left, right)
        self.assertEqual(code, 1)
        self.assertFalse(report['parity'])
        self.assertEqual(report['first_divergent_depth'], 1)
        self.assertEqual(report['left_only_at_divergence'], 1)
        self.assertEqual(report['right_only_at_divergence'], 1)
        # Witness states present
        self.assertEqual(len(report['left_witnesses']), 1)
        self.assertEqual(report['left_witnesses'][0]['state'], {"x": 1})
        self.assertEqual(len(report['right_witnesses']), 1)
        self.assertEqual(report['right_witnesses'][0]['state'], {"x": 2})

    def test_mismatch_at_depth_0_initial(self):
        left = [{"state": {"x": 0}, "depth": 0, "initial": True}]
        right = [{"state": {"x": 1}, "depth": 0, "initial": True}]
        report, code = self.run_json(left, right)
        self.assertFalse(report['parity'])
        self.assertEqual(report['first_divergent_depth'], 0)

    def test_left_strict_subset_of_right(self):
        left = [
            {"state": {"x": 0}, "depth": 0, "initial": True},
        ]
        right = [
            {"state": {"x": 0}, "depth": 0, "initial": True},
            {"state": {"x": 1}, "depth": 1, "initial": False},
        ]
        report, code = self.run_json(left, right)
        self.assertFalse(report['parity'])
        self.assertEqual(report['first_divergent_depth'], 1)
        self.assertEqual(report['left_only_at_divergence'], 0)
        self.assertEqual(report['right_only_at_divergence'], 1)

    def test_no_depth_in_right_export(self):
        """TLC-style export with depth=-1 (no depth info)."""
        left = [
            {"state": {"x": 0}, "depth": 0, "initial": True},
            {"state": {"x": 1}, "depth": 1, "initial": False},
        ]
        right = [
            {"state": {"x": 0}, "depth": -1, "initial": True},
            {"state": {"x": 1}, "depth": -1, "initial": False},
        ]
        report, code = self.run_json(left, right)
        # States match, but depths differ
        self.assertTrue(report['left_has_depth'])
        self.assertFalse(report['right_has_depth'])

    def test_provenance_in_witnesses(self):
        """Debug export with branch_label and predecessor_state_id."""
        left = [
            {"state": {"x": 0}, "depth": 0, "initial": True,
             "state_id": "k0", "branch_label": None, "predecessor_state_id": None},
            {"state": {"x": 1}, "depth": 1, "initial": False,
             "state_id": "k1", "branch_label": "LStep", "predecessor_state_id": "k0"},
        ]
        right = [
            {"state": {"x": 0}, "depth": 0, "initial": True},
        ]
        report, code = self.run_json(left, right)
        self.assertFalse(report['parity'])
        self.assertEqual(report['first_divergent_depth'], 1)
        self.assertEqual(len(report['left_witnesses']), 1)
        w = report['left_witnesses'][0]
        self.assertEqual(w['branch_label'], 'LStep')
        self.assertEqual(w['predecessor_state_id'], 'k0')

    def test_max_witnesses_limit(self):
        left = [{"state": {"x": i}, "depth": 0, "initial": True} for i in range(10)]
        right = []
        report, code = self.run_json(left, right, ['--max-witnesses', '3'])
        self.assertEqual(len(report['left_witnesses']), 3)

    def test_human_readable_output(self):
        left = [
            {"state": {"x": 0}, "depth": 0, "initial": True},
            {"state": {"x": 1}, "depth": 1, "initial": False},
        ]
        right = [
            {"state": {"x": 0}, "depth": 0, "initial": True},
        ]
        stdout, stderr, code = self.run_script(left, right,
                                               ['--left-label', 'SF', '--right-label', 'TLC'])
        self.assertIn('Witness-First Depth Diff Report', stdout)
        self.assertIn('FIRST DIVERGENCE', stdout)
        self.assertIn('VERDICT: MISMATCH', stdout)
        self.assertEqual(code, 1)

    def test_parity_human_readable(self):
        entries = [{"state": {"x": 0}, "depth": 0, "initial": True}]
        stdout, stderr, code = self.run_script(entries, entries)
        self.assertIn('VERDICT: PARITY', stdout)
        self.assertEqual(code, 0)

    def test_missing_file_exits_2(self):
        with tempfile.TemporaryDirectory() as d:
            left_path = os.path.join(d, 'left.jsonl')
            write_jsonl(left_path, [{"state": {"x": 0}, "depth": 0, "initial": True}])
            result = subprocess.run(
                [sys.executable, SCRIPT, left_path, '/nonexistent/right.jsonl'],
                capture_output=True, text=True)
            self.assertEqual(result.returncode, 2)

    def test_empty_exports_parity(self):
        report, code = self.run_json([], [])
        self.assertTrue(report['parity'])
        self.assertEqual(report['shared_total'], 0)

    def test_depth_table_structure(self):
        left = [
            {"state": {"x": 0}, "depth": 0, "initial": True},
            {"state": {"x": 1}, "depth": 1, "initial": False},
            {"state": {"x": 2}, "depth": 2, "initial": False},
        ]
        right = [
            {"state": {"x": 0}, "depth": 0, "initial": True},
            {"state": {"x": 1}, "depth": 1, "initial": False},
        ]
        report, code = self.run_json(left, right)
        # Depth table should have 3 rows (depths 0, 1, 2)
        self.assertEqual(len(report['depth_table']), 3)
        self.assertEqual(report['depth_table'][0]['depth'], 0)
        self.assertEqual(report['depth_table'][0]['shared'], 1)
        self.assertEqual(report['depth_table'][2]['left_only'], 1)
        self.assertEqual(report['depth_table'][2]['right_only'], 0)

    def test_on_real_twophase_exports(self):
        """Smoke test on checked-in TwoPhase parity exports."""
        repo_root = os.path.join(os.path.dirname(__file__), '..')
        sf_path = os.path.join(repo_root, 'reports/model_check/parity/source_first/twophase/states.jsonl')
        tlc_path = os.path.join(repo_root, 'reports/model_check/parity/tlc/twophase/states.jsonl')
        if not os.path.exists(sf_path) or not os.path.exists(tlc_path):
            self.skipTest("TwoPhase parity exports not present")
        result = subprocess.run(
            [sys.executable, SCRIPT, sf_path, tlc_path, '--json'],
            capture_output=True, text=True)
        report = json.loads(result.stdout)
        self.assertEqual(report['left_total'], 37)
        self.assertEqual(report['right_total'], 56)
        self.assertEqual(report['shared_total'], 23)
        self.assertFalse(report['parity'])


if __name__ == '__main__':
    unittest.main()
