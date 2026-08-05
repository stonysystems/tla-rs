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
        unreviewed, preserved, accepted = cd.body_drift(wrap(NAIVE, OTHER), wrap(VERIFIED, OTHER))
        self.assertEqual(unreviewed, ["helper"])
        self.assertEqual((preserved, accepted), ([], []))

    def test_preserved_names_are_reported_separately(self):
        unreviewed, preserved, accepted = cd.body_drift(
            wrap(NAIVE, OTHER), wrap(VERIFIED, OTHER), preserve={"helper"}
        )
        self.assertEqual(unreviewed, [])
        self.assertEqual(preserved, ["helper"])
        self.assertEqual(accepted, [])

    def test_accept_fresh_names_are_reported_but_do_not_fail(self):
        unreviewed, preserved, accepted = cd.body_drift(
            wrap(NAIVE, OTHER), wrap(VERIFIED, OTHER), accept={"helper"}
        )
        self.assertEqual(unreviewed, [])
        self.assertEqual(accepted, ["helper"])

    def test_identical_bodies_are_not_drift(self):
        self.assertEqual(cd.body_drift(wrap(NAIVE, OTHER), wrap(NAIVE, OTHER)), ([], [], []))

    def test_reflowed_whitespace_is_not_drift(self):
        # rustfmt reflows the merged file; that must not read as a rewrite or the
        # check cries wolf on every regeneration and stops being read.
        reflowed = "pub fn helper(m: &Map) -> Map {\n        naive_for_loop()\n\n}"
        self.assertEqual(cd.body_drift(wrap(reflowed), wrap(NAIVE)), ([], [], []))

    def test_functions_absent_from_fresh_are_not_drift(self):
        # The merge carries these over untouched, so they are not at risk.
        self.assertEqual(cd.body_drift(wrap(OTHER), wrap(VERIFIED, OTHER)), ([], [], []))


class PreserveList(unittest.TestCase):
    def _write(self, text):
        fh = tempfile.NamedTemporaryFile("w", suffix=".txt", delete=False)
        fh.write(text)
        fh.close()
        self.addCleanup(os.unlink, fh.name)
        return fh.name

    def test_filters_by_module(self):
        path = self._write("learner filter_clearnerstate\nexecutor something_else\n")
        self.assertEqual(cd.load_preserve(path, "learner")[0], {"filter_clearnerstate"})
        self.assertEqual(cd.load_preserve(path, "executor")[0], {"something_else"})

    def test_all_modules_when_unspecified(self):
        path = self._write("learner a\nexecutor b\n")
        self.assertEqual(cd.load_preserve(path)[0], {"a", "b"})

    def test_comments_and_blank_lines_ignored(self):
        path = self._write("# a comment\n\nlearner a  # trailing\n")
        self.assertEqual(cd.load_preserve(path, "learner")[0], {"a"})

    def test_malformed_line_raises_rather_than_being_skipped(self):
        # A silently ignored bad line would mean a helper thought protected is not.
        path = self._write("learner\n")
        with self.assertRaises(ValueError):
            cd.load_preserve(path)

    def test_accept_fresh_is_parsed_into_its_own_set(self):
        path = self._write("learner a\nlearner b accept-fresh\n")
        preserved, accepted = cd.load_preserve(path, "learner")
        self.assertEqual((preserved, accepted), ({"a"}, {"b"}))

    def test_unknown_third_field_raises(self):
        path = self._write("learner a whatever\n")
        with self.assertRaises(ValueError):
            cd.load_preserve(path)

    def test_missing_file_is_empty_not_an_error(self):
        self.assertEqual(cd.load_preserve("/nonexistent/preserve.txt"), (set(), set()))


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




class ImplMethodsAreCompared(unittest.TestCase):
    """Phase 42.8.c.2.iv.F. The check originally compared only free functions.
    The RSL protocol actions are all `&mut self` methods, so entire modules went
    unchecked -- 17 real implementations would have been replaced by
    `assume(false)` stubs with the report reading clean."""

    FRESH = (
        "verus! {\nimpl CExec {\n"
        "pub exec fn act(&mut self) {\n    assume(false);\n}\n"
        "}\n} // verus!\n"
    )
    EXISTING = (
        "verus! {\nimpl CExec {\n"
        "pub exec fn act(&mut self) {\n    real_implementation();\n}\n"
        "}\n} // verus!\n"
    )

    def test_a_method_body_swap_is_detected(self):
        unreviewed, _, _ = cd.body_drift(self.FRESH, self.EXISTING)
        self.assertEqual(unreviewed, ["CExec::act"])

    def test_preserve_accepts_the_bare_method_name(self):
        # The list is written `<module> <fn>`; requiring `Impl::fn` there would
        # be a second naming convention to get wrong.
        unreviewed, preserved, _ = cd.body_drift(
            self.FRESH, self.EXISTING, preserve={"act"}
        )
        self.assertEqual(unreviewed, [])
        self.assertEqual(preserved, ["CExec::act"])

    def test_qualified_name_also_works(self):
        _, preserved, _ = cd.body_drift(
            self.FRESH, self.EXISTING, preserve={"CExec::act"}
        )
        self.assertEqual(preserved, ["CExec::act"])


if __name__ == "__main__":
    unittest.main()
