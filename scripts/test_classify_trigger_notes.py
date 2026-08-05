#!/usr/bin/env python3
"""Tests for classify_trigger_notes (Phase 54.7.c)."""

import os
import sys
import tempfile
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import classify_trigger_notes as ct  # noqa: E402


def note(path, line, src):
    """One note as verus prints it: header, location, gutter, source."""
    return (
        "note: automatically chose triggers for this expression:\n"
        f"   --> {path}:{line}:5\n"
        "    |\n"
        f"{line} |     {src}\n"
        "    |     ^^^^^^\n"
        "\n"
        "note:   trigger 1 of 2:\n"
        f"   --> {path}:{line}:59\n"
        "    |\n"
        f"{line} |     {src}\n"
    )


VEC_SRC = "ensures forall |i: int| 0 <= i < r@.len() ==> r@[i].valid()"
OTHER_SRC = "assert forall |ak: int| abs2.contains_key(ak) implies abs2[ak] == e[ak] by {"


class NoteParsing(unittest.TestCase):
    def test_one_entry_per_note_not_per_trigger(self):
        # Each note is followed by a `trigger N of M` block carrying its own
        # `-->`; counting those inflates every multi-trigger note.
        got = ct.parse_note_locations(note("src/generated/RSL/a_gen.rs", 12, VEC_SRC))
        self.assertEqual(len(got), 1)
        self.assertEqual(got[0][0], "src/generated/RSL/a_gen.rs")
        self.assertEqual(got[0][1], 12)

    def test_captures_the_source_line(self):
        got = ct.parse_note_locations(note("a.rs", 3, VEC_SRC))
        self.assertIn("r@[i].valid()", got[0][2])

    def test_multiple_notes(self):
        text = note("a.rs", 1, VEC_SRC) + note("b.rs", 2, OTHER_SRC)
        got = ct.parse_note_locations(text)
        self.assertEqual([(f, ln) for f, ln, _ in got], [("a.rs", 1), ("b.rs", 2)])

    def test_unrelated_log_lines_are_ignored(self):
        self.assertEqual(ct.parse_note_locations("warning: unused\nverified: 12\n"), [])


class Shape(unittest.TestCase):
    def test_vec_element_shape(self):
        self.assertEqual(ct.shape_of(VEC_SRC), "vec-element")
        self.assertEqual(
            ct.shape_of("forall |i: int| 0 <= i < s@.len() ==> s@[i].abstractable()"),
            "vec-element",
        )

    def test_other_shapes(self):
        self.assertEqual(ct.shape_of(OTHER_SRC), "other")

    def test_index_variable_must_match(self):
        # `0 <= i < len ==> x@[j].valid()` is a different (and rarer) shape; the
        # codegen pattern indexes by the bound variable.
        self.assertEqual(
            ct.shape_of("forall |i: int| 0 <= i < s@.len() ==> s@[j].valid()"), "other"
        )


class FunctionSpans(unittest.TestCase):
    def test_free_function_span(self):
        text = "pub exec fn foo() {\n    body();\n}\n"
        self.assertEqual(ct.function_spans(text), [("foo", 1, 3)])

    def test_impl_methods_are_qualified(self):
        text = "impl CExec {\npub exec fn act(&mut self) {\n    body();\n}\n}\n"
        self.assertEqual(ct.function_spans(text), [("CExec::act", 2, 4)])

    def test_struct_literal_in_requires_does_not_close_the_span(self):
        # The body brace is the one outside every paren. Closing at the
        # signature would put every note in the body outside any function.
        text = (
            "pub exec fn foo() -> (r: u64)\n"
            "    requires bound(UpperBound::UpperBoundFinite{n: 3}),\n"
            "{\n"
            "    body();\n"
            "}\n"
        )
        spans = ct.function_spans(text)
        self.assertEqual(spans, [("foo", 1, 5)])

    def test_containing_function_picks_the_innermost(self):
        spans = [("Outer", 1, 100), ("Outer::inner", 10, 20)]
        self.assertEqual(ct.containing_function(spans, 15), "Outer::inner")

    def test_line_outside_any_function(self):
        self.assertEqual(ct.containing_function([("foo", 5, 9)], 2), None)


class SpecNames(unittest.TestCase):
    def test_maps_exec_name_back_to_skip_list_spellings(self):
        # This mapping is the whole reason the first run reported 0 skips out of
        # 103: the list holds `LExecutorExecute`, the file holds
        # `CExecutorExecute`, and a direct comparison never matches.
        self.assertIn("LExecutorExecute", ct.spec_names_of("CExecutorExecute"))
        self.assertIn("BoundRequestSequence", ct.spec_names_of("CBoundRequestSequence"))
        self.assertIn("CFoo", ct.spec_names_of("CFoo"))

    def test_name_without_c_prefix_is_left_alone(self):
        self.assertEqual(ct.spec_names_of("lemma_foo"), {"lemma_foo"})


class SkipFunctions(unittest.TestCase):
    def _toml(self, text):
        fh = tempfile.NamedTemporaryFile("w", suffix=".toml", delete=False)
        fh.write(text)
        fh.close()
        self.addCleanup(os.unlink, fh.name)
        return fh.name

    def test_parses_a_list_with_comments(self):
        path = self._toml(
            'skip_functions = [\n    # a comment with "quotes"\n    "Foo",\n    "Bar",\n]\n'
        )
        self.assertEqual(ct.load_skip_functions(path), {"Foo", "Bar"})

    def test_absent_key_is_empty(self):
        self.assertEqual(ct.load_skip_functions(self._toml("other = 1\n")), set())

    def test_missing_file_is_empty(self):
        self.assertEqual(ct.load_skip_functions("/nonexistent.toml"), set())


class EndToEnd(unittest.TestCase):
    """A note in each of the three origins, on a real directory layout."""

    def setUp(self):
        self.root = tempfile.mkdtemp()
        self.addCleanup(__import__("shutil").rmtree, self.root)
        gen = os.path.join(self.root, "src", "generated", "RSL")
        proto = os.path.join(self.root, "src", "protocol", "RSL")
        scripts = os.path.join(self.root, "scripts")
        for d in (gen, proto, scripts):
            os.makedirs(d)

        # line 1 fn CSkipped, note on line 2; line 4 fn CKept, note on 5;
        # line 7 fn CPlain, note on 8.
        with open(os.path.join(gen, "m_gen.rs"), "w") as fh:
            fh.write(
                "pub exec fn CSkipped() {\n    a();\n}\n"
                "pub exec fn CKept() {\n    b();\n}\n"
                "pub exec fn CPlain() {\n    c();\n}\n"
            )
        with open(os.path.join(proto, "m_transpile.toml"), "w") as fh:
            fh.write('skip_functions = [\n    "LSkipped",\n]\n')
        with open(os.path.join(scripts, "rsl_merge_preserve.txt"), "w") as fh:
            fh.write("m CKept\n")

        self.log = (
            note("src/generated/RSL/m_gen.rs", 2, VEC_SRC)
            + note("src/generated/RSL/m_gen.rs", 5, VEC_SRC)
            + note("src/generated/RSL/m_gen.rs", 8, VEC_SRC)
            + note("src/generated/RSL/m_gen.rs", 8, OTHER_SRC)
            + note("src/protocol/RSL/handwritten.rs", 3, OTHER_SRC)
        )

    def test_each_note_lands_in_its_origin(self):
        r = ct.classify(self.log, self.root)
        self.assertEqual([x[2] for x in r["skip"]], ["CSkipped"])
        self.assertEqual([x[2] for x in r["preserve"]], ["CKept"])
        self.assertEqual([x[2] for x in r["generated"]], ["CPlain", "CPlain"])
        self.assertEqual(len(r["not-generated"]), 1)

    def test_nothing_is_unattributed(self):
        self.assertEqual(ct.classify(self.log, self.root)["unattributed"], [])

    def test_shape_is_recorded_alongside_origin(self):
        # The decision needs both: emitted-and-known-shape is the only cell a
        # regeneration clears. `CPlain` has one of each.
        gen = ct.classify(self.log, self.root)["generated"]
        self.assertEqual(sorted(x[3] for x in gen), ["other", "vec-element"])

    def test_totals_account_for_every_note(self):
        r = ct.classify(self.log, self.root)
        self.assertEqual(sum(len(v) for v in r.values()), 5)


if __name__ == "__main__":
    unittest.main()
