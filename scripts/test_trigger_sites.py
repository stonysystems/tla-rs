#!/usr/bin/env python3
"""Tests for trigger_sites.py (Phase 54 work-list scanner)."""

import json
import os
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
SCRIPT = os.path.join(HERE, "trigger_sites.py")

sys.path.insert(0, HERE)
import trigger_sites as ts  # noqa: E402


def classify_one(src):
    sites = ts.scan_text(src)
    assert len(sites) >= 1, "expected at least one quantifier in: {!r}".format(src)
    return sites[0]["classification"]


class TestClassification(unittest.TestCase):
    def test_plain_quantifier_is_unannotated(self):
        self.assertEqual(
            classify_one("ensures forall |i: int| 0 <= i < n ==> f(i) == g(i),"),
            "unannotated",
        )

    def test_inline_trigger_attribute(self):
        self.assertEqual(
            classify_one("ensures forall |i: int| #[trigger] f(i) == g(i),"),
            "annotated",
        )

    def test_bang_trigger_attribute(self):
        self.assertEqual(
            classify_one("ensures forall |i: int| #![trigger f(i)] f(i) == g(i),"),
            "annotated",
        )

    def test_multi_binder_trigger_is_found(self):
        # Regression: the comma between binders used to end the scope scan, so
        # the annotation that follows the binder list was missed entirely and
        # the site was misreported as unannotated.
        self.assertEqual(
            classify_one(
                "forall |x1:X, x2:X| #![trigger f(x1), f(x2)] f(x1) == f(x2) ==> x1 == x2"
            ),
            "annotated",
        )

    def test_three_binders(self):
        self.assertEqual(
            classify_one("forall |a: int, b: int, c: int| #[trigger] p(a, b, c)"),
            "annotated",
        )

    def test_auto_attribute(self):
        self.assertEqual(
            classify_one("ensures forall |i: int| #![auto] f(i) == g(i),"),
            "auto",
        )

    def test_trigger_after_a_nested_quantifier_is_ambiguous(self):
        # The annotation may belong to the inner quantifier; say so rather than
        # credit the outer one with an annotation it may not have.
        self.assertEqual(
            classify_one(
                "if exists |x: int| p(x) { assert forall |y: int| #[trigger] q(y) by { } }"
            ),
            "ambiguous",
        )

    def test_exists_is_recognised(self):
        sites = ts.scan_text("ensures exists |k: int| f(k) == 0,")
        self.assertEqual(sites[0]["kind"], "exists")

    def test_line_numbers_are_reported(self):
        sites = ts.scan_text("\n\nensures forall |i: int| f(i),\n")
        self.assertEqual(sites[0]["line"], 3)


class TestCommentAndStringHandling(unittest.TestCase):
    def test_line_comment_is_not_a_site(self):
        self.assertEqual(ts.scan_text("// forall |i: int| f(i)\n"), [])

    def test_block_comment_is_not_a_site(self):
        self.assertEqual(ts.scan_text("/* forall |i: int| f(i) */\n"), [])

    def test_string_literal_is_not_a_site(self):
        self.assertEqual(ts.scan_text('let s = "forall |i: int| f(i)";\n'), [])

    def test_code_after_a_comment_is_still_scanned(self):
        sites = ts.scan_text("// forall |i: int| nope\nensures forall |j: int| f(j),\n")
        self.assertEqual(len(sites), 1)
        self.assertEqual(sites[0]["line"], 2)

    def test_a_commented_out_trigger_does_not_count_as_annotation(self):
        self.assertEqual(
            classify_one("ensures forall |i: int| /* #[trigger] */ f(i) == g(i),"),
            "unannotated",
        )


class TestInventory(unittest.TestCase):
    def write(self, tmp, rel, text):
        path = os.path.join(tmp, rel)
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "w") as f:
            f.write(text)
        return path

    def test_directory_aggregation(self):
        with tempfile.TemporaryDirectory() as tmp:
            self.write(tmp, "a/one.rs", "ensures forall |i: int| f(i),\n")
            self.write(tmp, "a/two.rs", "ensures forall |i: int| #[trigger] f(i),\n")
            self.write(tmp, "b/three.rs", "ensures exists |i: int| #![auto] f(i),\n")
            inv = ts.build_inventory([tmp], repo_root=tmp)
            self.assertEqual(inv["schema"], ts.SCHEMA)
            self.assertEqual(inv["file_count"], 3)
            self.assertEqual(inv["totals"]["total"], 3)
            self.assertEqual(inv["totals"]["unannotated"], 1)
            self.assertEqual(inv["by_dir"]["a"]["total"], 2)
            self.assertEqual(inv["by_dir"]["a"]["unannotated"], 1)
            self.assertEqual(inv["by_dir"]["b"]["auto"], 1)

    def test_files_without_quantifiers_are_skipped(self):
        with tempfile.TemporaryDirectory() as tmp:
            self.write(tmp, "empty.rs", "fn main() {}\n")
            inv = ts.build_inventory([tmp], repo_root=tmp)
            self.assertEqual(inv["file_count"], 0)

    def test_non_rust_files_are_ignored(self):
        with tempfile.TemporaryDirectory() as tmp:
            self.write(tmp, "notes.md", "forall |i: int| f(i)\n")
            inv = ts.build_inventory([tmp], repo_root=tmp)
            self.assertEqual(inv["file_count"], 0)

    def test_a_single_file_root_works(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = self.write(tmp, "one.rs", "ensures forall |i: int| f(i),\n")
            inv = ts.build_inventory([path], repo_root=tmp)
            self.assertEqual(inv["file_count"], 1)


class TestRepoScan(unittest.TestCase):
    """Sanity checks against the real tree, so the tool cannot rot silently."""

    @classmethod
    def setUpClass(cls):
        cls.repo = os.path.dirname(HERE)
        cls.inv = ts.build_inventory(
            [os.path.join(cls.repo, "src")], repo_root=cls.repo
        )

    def test_the_scan_finds_a_substantial_number_of_sites(self):
        self.assertGreater(self.inv["totals"]["total"], 500)

    def test_known_annotated_file_is_classified_correctly(self):
        # choose_v.rs annotates both of its quantifiers with #![trigger(p(i))].
        entry = self.inv["files"]["src/verus_extra/choose_v.rs"]
        self.assertEqual(entry["total"], 2)
        self.assertEqual(entry["annotated"], 2)
        self.assertEqual(entry["unannotated"], 0)

    def test_ambiguous_sites_stay_a_small_minority(self):
        # If this grows, the scope heuristic needs revisiting rather than the
        # number being quietly accepted.
        total = self.inv["totals"]["total"]
        self.assertLess(self.inv["totals"].get("ambiguous", 0), total * 0.1)


class TestCli(unittest.TestCase):
    def test_markdown_output(self):
        result = subprocess.run(
            [sys.executable, SCRIPT, os.path.join(os.path.dirname(HERE), "src")],
            capture_output=True,
            text=True,
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("# Quantifier sites and trigger annotations", result.stdout)
        self.assertIn("**Not** a prediction", result.stdout)
        self.assertIn("## By directory", result.stdout)

    def test_json_output_is_valid(self):
        with tempfile.TemporaryDirectory() as tmp:
            src = os.path.join(tmp, "a.rs")
            with open(src, "w") as f:
                f.write("ensures forall |i: int| f(i),\n")
            out = os.path.join(tmp, "sites.json")
            result = subprocess.run(
                [sys.executable, SCRIPT, src, "--json", "-o", out],
                capture_output=True,
                text=True,
            )
            self.assertEqual(result.returncode, 0, result.stderr)
            with open(out) as f:
                inv = json.load(f)
            self.assertEqual(inv["schema"], ts.SCHEMA)


if __name__ == "__main__":
    unittest.main()
