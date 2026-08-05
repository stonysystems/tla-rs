#!/usr/bin/env python3
"""Tests for check_merge_body_drift (Phase 42.8.c.2.iv.A)."""

import os
import sys
import tempfile
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import check_merge_body_drift as cd  # noqa: E402


def wrap(*fns):
    return "verus! {\n" + "\n".join(fns) + "\n} // verus!\n"


NAIVE = "pub fn helper(m: &Map) -> Map {\n    naive_for_loop()\n}"
VERIFIED = "pub fn helper(m: &Map) -> Map {\n    verified_while_with_invariants()\n}"
OTHER = "pub fn other() {\n    same()\n}"


class BodyDrift(unittest.TestCase):
    def test_detects_a_rewritten_body(self):
        unprotected, protected = cd.body_drift(wrap(NAIVE, OTHER), wrap(VERIFIED, OTHER))
        self.assertEqual(unprotected, ["helper"])
        self.assertEqual(protected, [])

    def test_preserved_names_are_reported_separately(self):
        unprotected, protected = cd.body_drift(
            wrap(NAIVE, OTHER), wrap(VERIFIED, OTHER), preserve={"helper"}
        )
        self.assertEqual(unprotected, [])
        self.assertEqual(protected, ["helper"])

    def test_identical_bodies_are_not_drift(self):
        unprotected, protected = cd.body_drift(wrap(NAIVE, OTHER), wrap(NAIVE, OTHER))
        self.assertEqual((unprotected, protected), ([], []))

    def test_reflowed_whitespace_is_not_drift(self):
        # rustfmt reflows the merged file; that must not read as a rewrite or the
        # check cries wolf on every regeneration and stops being read.
        reflowed = "pub fn helper(m: &Map) -> Map {\n        naive_for_loop()\n\n}"
        unprotected, protected = cd.body_drift(wrap(reflowed), wrap(NAIVE))
        self.assertEqual((unprotected, protected), ([], []))

    def test_functions_absent_from_fresh_are_not_drift(self):
        # The merge carries these over untouched, so they are not at risk.
        unprotected, protected = cd.body_drift(wrap(OTHER), wrap(VERIFIED, OTHER))
        self.assertEqual((unprotected, protected), ([], []))


class PreserveList(unittest.TestCase):
    def _write(self, text):
        fh = tempfile.NamedTemporaryFile("w", suffix=".txt", delete=False)
        fh.write(text)
        fh.close()
        self.addCleanup(os.unlink, fh.name)
        return fh.name

    def test_filters_by_module(self):
        path = self._write("learner filter_clearnerstate\nexecutor something_else\n")
        self.assertEqual(cd.load_preserve(path, "learner"), {"filter_clearnerstate"})
        self.assertEqual(cd.load_preserve(path, "executor"), {"something_else"})

    def test_all_modules_when_unspecified(self):
        path = self._write("learner a\nexecutor b\n")
        self.assertEqual(cd.load_preserve(path), {"a", "b"})

    def test_comments_and_blank_lines_ignored(self):
        path = self._write("# a comment\n\nlearner a  # trailing\n")
        self.assertEqual(cd.load_preserve(path, "learner"), {"a"})

    def test_malformed_line_raises_rather_than_being_skipped(self):
        # A silently ignored bad line would mean a helper thought protected is not.
        path = self._write("learner\n")
        with self.assertRaises(ValueError):
            cd.load_preserve(path)

    def test_missing_file_is_empty_not_an_error(self):
        self.assertEqual(cd.load_preserve("/nonexistent/preserve.txt"), set())


class ExitStatus(unittest.TestCase):
    def _file(self, text):
        fh = tempfile.NamedTemporaryFile("w", suffix=".rs", delete=False)
        fh.write(text)
        fh.close()
        self.addCleanup(os.unlink, fh.name)
        return fh.name

    def test_nonzero_when_an_unprotected_body_would_be_rewritten(self):
        fresh, existing = self._file(wrap(NAIVE)), self._file(wrap(VERIFIED))
        self.assertEqual(cd.main([fresh, existing, "--quiet"]), 1)

    def test_zero_when_clean(self):
        fresh, existing = self._file(wrap(NAIVE)), self._file(wrap(NAIVE))
        self.assertEqual(cd.main([fresh, existing, "--quiet"]), 0)


if __name__ == "__main__":
    unittest.main()
