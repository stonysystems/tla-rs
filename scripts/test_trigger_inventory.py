#!/usr/bin/env python3
"""Tests for trigger_inventory.py (Phase 54.1).

The two `.log` fixtures under `fixtures/trigger_inventory/` are real Verus
output (`verus --crate-type=lib --triggers`, release 0.2026.01.02.6f52890),
with the probe paths rewritten to `src/probe.rs`. They pin the diagnostic
shape the parser depends on: if a future Verus release changes it, these tests
fail rather than the inventory silently going empty.
"""

import json
import os
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
SCRIPT = os.path.join(HERE, "trigger_inventory.py")
FIXTURES = os.path.join(HERE, "fixtures", "trigger_inventory")

sys.path.insert(0, HERE)
import trigger_inventory as ti  # noqa: E402


def fixture(name):
    with open(os.path.join(FIXTURES, name)) as f:
        return f.read()


def run(args, expect=None):
    result = subprocess.run(
        [sys.executable, SCRIPT] + args, capture_output=True, text=True
    )
    if expect is not None:
        assert result.returncode == expect, (
            "expected exit {}, got {}\nstdout: {}\nstderr: {}".format(
                expect, result.returncode, result.stdout, result.stderr
            )
        )
    return result


class TestParse(unittest.TestCase):
    def test_single_line_notes(self):
        inv = ti.build_inventory(fixture("single_line_notes.log"), label="probe")
        self.assertEqual(inv["schema"], ti.SCHEMA)
        self.assertEqual(inv["total_notes"], 3)
        self.assertEqual(inv["total_triggers"], 5)
        self.assertEqual(inv["orphan_trigger_notes"], 0)
        self.assertEqual(inv["multiline_notes"], 0)
        self.assertEqual(inv["by_file"], {"src/probe.rs": 3})
        self.assertEqual(inv["by_trigger_count"], {"1": 1, "2": 2})

    def test_expression_and_location(self):
        inv = ti.build_inventory(fixture("single_line_notes.log"))
        first = inv["entries"][0]
        self.assertEqual(first["file"], "src/probe.rs")
        self.assertEqual(first["line"], 9)
        self.assertEqual(first["col"], 5)
        self.assertEqual(first["expr"], "forall|i: int| 0 <= i < n ==> f(i) == g(i)")
        self.assertFalse(first["multiline"])

    def test_trigger_terms_are_extracted_from_carets(self):
        inv = ti.build_inventory(fixture("single_line_notes.log"))
        first = inv["entries"][0]
        self.assertEqual([t["terms"] for t in first["triggers"]], [["f(i)"], ["g(i)"]])
        self.assertEqual([t["index"] for t in first["triggers"]], [1, 2])
        self.assertEqual([t["total"] for t in first["triggers"]], [2, 2])

    def test_multi_term_trigger_keeps_all_terms(self):
        # `trigger 1 of 1: f(i)  g(j)` — one trigger made of two terms.
        inv = ti.build_inventory(fixture("single_line_notes.log"))
        second = inv["entries"][1]
        self.assertEqual(second["trigger_count"], 1)
        self.assertEqual(second["triggers"][0]["terms"], ["f(i)", "g(j)"])

    def test_multiline_expression_is_flagged_and_joined(self):
        inv = ti.build_inventory(fixture("multiline_notes.log"))
        entry = inv["entries"][0]
        self.assertTrue(entry["multiline"])
        self.assertEqual(
            entry["expr"], "forall|i: int| 0 <= i < n ==> f(i) == g(i) && h(i, n)"
        )
        # Its triggers are single-line and still extracted exactly.
        self.assertEqual([t["terms"] for t in entry["triggers"]], [["f(i)"], ["g(i)"]])

    def test_nested_quantifier_note(self):
        inv = ti.build_inventory(fixture("multiline_notes.log"))
        entry = inv["entries"][1]
        self.assertEqual(entry["expr"], "exists|j: int| h(i, j)")
        self.assertEqual(entry["triggers"][0]["terms"], ["h(i, j)"])

    def test_verus_version_is_detected(self):
        log = "Verus\n  Version: 0.2026.08.02.b677dd5\n" + fixture(
            "single_line_notes.log"
        )
        inv = ti.build_inventory(log)
        self.assertEqual(inv["verus_version"], "0.2026.08.02.b677dd5")

    def test_explicit_version_overrides_detection(self):
        inv = ti.build_inventory(
            "Verus\n  Version: 0.1\n" + fixture("single_line_notes.log"),
            verus_version="9.9",
        )
        self.assertEqual(inv["verus_version"], "9.9")

    def test_unrelated_diagnostics_are_ignored(self):
        noisy = (
            "error: something else\n"
            "  --> src/other.rs:1:1\n"
            "   |\n"
            " 1 | fn x() {}\n"
            "   | ^^^^^^^^^\n"
            "\n" + fixture("single_line_notes.log")
        )
        inv = ti.build_inventory(noisy)
        self.assertEqual(inv["total_notes"], 3)
        self.assertEqual(list(inv["by_file"]), ["src/probe.rs"])

    def test_orphan_trigger_note_is_counted_not_crashed(self):
        truncated = "\n".join(fixture("single_line_notes.log").splitlines()[6:])
        inv = ti.build_inventory(truncated)
        self.assertGreaterEqual(inv["orphan_trigger_notes"], 1)

    def test_paths_are_relativized(self):
        log = fixture("single_line_notes.log").replace("src/probe.rs", "/repo/src/a.rs")
        inv = ti.build_inventory(log, root="/repo")
        self.assertEqual(list(inv["by_file"]), ["src/a.rs"])

    def test_repeated_identical_expressions_get_distinct_keys(self):
        doubled = fixture("single_line_notes.log") + "\n" + fixture(
            "single_line_notes.log"
        )
        inv = ti.build_inventory(doubled)
        keys = [e["key"] for e in inv["entries"]]
        self.assertEqual(len(keys), len(set(keys)), "keys must be unique")
        self.assertEqual(inv["total_notes"], 6)


class TestMultiLineTriggerTerms(unittest.TestCase):
    """A trigger's terms can straddle several source lines.

    Treating "more than one quoted line" as "no terms" dropped 29 of this
    crate's trigger groups, and an empty term list meeting a non-empty one made
    the diff report a spurious `changed` -- the one category that is supposed
    to mean real instability.
    """

    LOG = """note: automatically chose triggers for this expression:
  --> src/a.rs:90:13
   |
90 |             assert forall |p1: RslPacket, p2: RslPacket|
   |             ^^^^^^

note:   trigger 1 of 1:
  --> src/a.rs:91:17
   |
91 |                 s.received_1b_packets.contains(p1)
   |                 ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
92 |                 && s.received_1b_packets.contains(p2)
   |                    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
"""

    def test_terms_from_every_quoted_line_are_captured(self):
        inv = ti.build_inventory(self.LOG)
        terms = inv["entries"][0]["triggers"][0]["terms"]
        self.assertEqual(
            terms,
            [
                "s.received_1b_packets.contains(p1)",
                "s.received_1b_packets.contains(p2)",
            ],
        )

    def test_no_trigger_group_is_left_termless(self):
        inv = ti.build_inventory(self.LOG)
        for entry in inv["entries"]:
            for tr in entry["triggers"]:
                self.assertTrue(tr["terms"], "trigger group lost its terms")

    def test_empty_versus_nonempty_terms_would_read_as_changed(self):
        # Guards the failure this fixed: same expression, one side parsed with
        # terms and the other without, reported as instability.
        good = ti.build_inventory(self.LOG)
        blank = ti.build_inventory(self.LOG)
        blank["entries"][0]["triggers"][0]["terms"] = []
        d = ti.diff_inventories(good, blank)
        self.assertEqual(d["changed_count"], 1)
        d_same = ti.diff_inventories(good, good)
        self.assertEqual(d_same["changed_count"], 0)


class TestSconsWrappedLog(unittest.TestCase):
    """CI captures the notes out of a full `scons` run, not a bare verus call."""

    def test_notes_are_found_inside_scons_output(self):
        inv = ti.build_inventory(fixture("scons_wrapped_notes.log"))
        self.assertEqual(inv["total_notes"], 3)
        self.assertEqual(inv["total_triggers"], 5)

    def test_runner_paths_are_relativized_to_the_repo(self):
        inv = ti.build_inventory(
            fixture("scons_wrapped_notes.log"),
            root="/home/runner/work/tla-rs/tla-rs",
        )
        self.assertEqual(list(inv["by_file"]), ["src/protocol/RSL/replica.rs"])
        self.assertEqual(list(inv["by_dir"]), ["src/protocol/RSL"])

    def test_scons_chatter_is_not_mistaken_for_a_note(self):
        inv = ti.build_inventory(fixture("scons_wrapped_notes.log"))
        for entry in inv["entries"]:
            self.assertNotIn("scons", entry["expr"])
            self.assertTrue(entry["file"].endswith(".rs"))


class TestCiWiring(unittest.TestCase):
    """Guard the Phase 54.2.a capture wiring in .github/workflows/ci.yml.

    The capture is only useful if it actually runs on every Verus job, and a
    silently dropped step would look exactly like "no triggers left".
    """

    def setUp(self):
        path = os.path.join(os.path.dirname(HERE), ".github", "workflows", "ci.yml")
        with open(path) as f:
            self.ci = f.read()

    def test_verification_output_is_teed_with_pipefail(self):
        self.assertIn("set -o pipefail", self.ci)
        self.assertIn("tee verus-verify.log", self.ci)

    def test_capture_step_runs_the_parser_and_reporter(self):
        self.assertIn("scripts/trigger_inventory.py parse verus-verify.log", self.ci)
        self.assertIn("scripts/trigger_inventory.py report trigger-inventory.json", self.ci)

    def test_capture_cannot_change_the_job_verdict(self):
        # --allow-empty keeps a note-free log from failing the capture step, and
        # a missing log (an earlier step failed) is skipped rather than raising.
        self.assertIn("--allow-empty", self.ci)
        self.assertIn("if [ ! -f verus-verify.log ]", self.ci)

    def test_inventory_is_uploaded_as_an_artifact(self):
        self.assertIn("trigger-inventory-${{ env.VERUS_VERSION }}", self.ci)
        self.assertIn("trigger-inventory.json", self.ci)

    def test_guard_step_exists_and_reads_the_committed_ceiling(self):
        self.assertIn(
            "scripts/trigger_inventory.py guard trigger-inventory.json", self.ci
        )
        self.assertIn("--ceiling reports/triggers/ceiling.json", self.ci)
        self.assertIn("--capture-mode selective", self.ci)

    def test_guard_step_sets_pipefail(self):
        # The guards pipe into tee; without pipefail a failing guard exits 0 and
        # silently stops guarding.
        block = self.ci.split("Guard trigger inventory", 1)[1][:600]
        self.assertIn("set -o pipefail", block)


class TestCeilingFile(unittest.TestCase):
    """reports/triggers/ceiling.json is the agreed limit, as reviewable data."""

    def setUp(self):
        self.path = os.path.join(
            os.path.dirname(HERE), "reports", "triggers", "ceiling.json"
        )
        with open(self.path) as f:
            self.ceiling = json.load(f)

    def test_schema_and_required_fields(self):
        self.assertEqual(self.ceiling["schema"], ti.CEILING_SCHEMA)
        for field in ("enforce", "max_notes", "mode", "rationale"):
            self.assertIn(field, self.ceiling)

    def test_loader_accepts_it(self):
        self.assertEqual(ti.load_ceiling(self.path)["schema"], ti.CEILING_SCHEMA)

    def test_an_enforcing_ceiling_must_carry_a_number(self):
        # Guards against a half-edit that turns enforcement on but leaves the
        # limit unset, which would make the guard silently vacuous.
        if self.ceiling["enforce"]:
            self.assertIsNotNone(self.ceiling["max_notes"])
            self.assertTrue(self.ceiling.get("set_on"), "record when it was agreed")

    def test_rationale_is_present(self):
        self.assertGreater(len(self.ceiling["rationale"]), 40)


class TestGuard(unittest.TestCase):
    def inventory(self):
        return ti.build_inventory(fixture("single_line_notes.log"), label="run")

    def ceiling(self, **kw):
        base = {
            "schema": ti.CEILING_SCHEMA,
            "enforce": False,
            "max_notes": None,
            "mode": "selective",
            "rationale": "test",
        }
        base.update(kw)
        return base

    def test_unset_ceiling_reports_and_passes(self):
        status, text = ti.guard(self.inventory(), self.ceiling())
        self.assertEqual(status, 0)
        self.assertIn("trigger notes measured: 3", text)
        self.assertIn("not enforced yet", text)

    def test_under_the_ceiling_passes(self):
        status, text = ti.guard(
            self.inventory(), self.ceiling(enforce=True, max_notes=10)
        )
        self.assertEqual(status, 0)
        self.assertIn("under the ceiling by 7", text)

    def test_over_the_ceiling_fails(self):
        status, text = ti.guard(
            self.inventory(), self.ceiling(enforce=True, max_notes=2)
        )
        self.assertEqual(status, 1)
        self.assertIn("exceeds the agreed ceiling", text)

    def test_mode_mismatch_is_an_invalid_comparison(self):
        status, text = ti.guard(
            self.inventory(),
            self.ceiling(enforce=True, max_notes=2, mode="selective"),
            mode="all-modules",
        )
        self.assertEqual(status, 2)
        self.assertIn("not comparable", text)

    def test_empty_capture_is_not_judged(self):
        empty = ti.build_inventory("verification results:: 0 verified, 1 errors\n")
        status, text = ti.guard(empty, self.ceiling(enforce=True, max_notes=0))
        self.assertEqual(status, 0)
        self.assertIn("failed early", text)

    def test_changed_trigger_choice_fails_when_enforcing(self):
        base = self.inventory()
        new = self.inventory()
        new["entries"][0]["triggers"][0]["terms"] = ["h(i)"]
        status, text = ti.guard(
            new, self.ceiling(enforce=True, max_notes=10), baseline=base
        )
        self.assertEqual(status, 1)
        self.assertIn("1 expression(s) had their chosen triggers change", text)
        self.assertIn("0 added", text)
        # The count is unchanged; only the choice moved.
        self.assertIn("under the ceiling", text)

    def test_changed_trigger_choice_only_reports_when_not_enforcing(self):
        base = self.inventory()
        new = self.inventory()
        new["entries"][0]["triggers"][0]["terms"] = ["h(i)"]
        status, text = ti.guard(new, self.ceiling(), baseline=base)
        self.assertEqual(status, 0)
        self.assertIn("1 changed", text)

    def test_cli_guard_exit_codes(self):
        with tempfile.TemporaryDirectory() as tmp:
            inv = os.path.join(tmp, "inv.json")
            run(
                [
                    "parse",
                    os.path.join(FIXTURES, "single_line_notes.log"),
                    "-o",
                    inv,
                ],
                expect=0,
            )
            ceil_path = os.path.join(tmp, "ceiling.json")
            with open(ceil_path, "w") as f:
                json.dump(self.ceiling(enforce=True, max_notes=2), f)
            result = run(["guard", inv, "--ceiling", ceil_path], expect=1)
            self.assertIn("exceeds the agreed ceiling", result.stdout)
            with open(ceil_path, "w") as f:
                json.dump(self.ceiling(enforce=True, max_notes=3), f)
            run(["guard", inv, "--ceiling", ceil_path], expect=0)

    def test_cli_rejects_a_bad_ceiling_schema(self):
        with tempfile.TemporaryDirectory() as tmp:
            inv = os.path.join(tmp, "inv.json")
            run(
                ["parse", os.path.join(FIXTURES, "single_line_notes.log"), "-o", inv],
                expect=0,
            )
            bad = os.path.join(tmp, "bad.json")
            with open(bad, "w") as f:
                json.dump({"schema": "nope"}, f)
            result = run(["guard", inv, "--ceiling", bad])
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("expected schema", result.stderr)


class TestDiff(unittest.TestCase):
    def base(self):
        return ti.build_inventory(fixture("single_line_notes.log"), label="base")

    def test_identical_inventories_have_no_delta(self):
        d = ti.diff_inventories(self.base(), self.base())
        self.assertEqual(d["delta_notes"], 0)
        self.assertEqual(d["added_count"], 0)
        self.assertEqual(d["removed_count"], 0)
        self.assertEqual(d["changed_count"], 0)

    def test_removed_note_is_progress(self):
        base = self.base()
        new = self.base()
        new["entries"] = new["entries"][1:]
        new["total_notes"] = len(new["entries"])
        d = ti.diff_inventories(base, new)
        self.assertEqual(d["removed_count"], 1)
        self.assertEqual(d["added_count"], 0)
        self.assertEqual(d["delta_notes"], -1)

    def test_added_note_is_regression(self):
        base = self.base()
        new = self.base()
        base["entries"] = base["entries"][1:]
        base["total_notes"] = len(base["entries"])
        d = ti.diff_inventories(base, new)
        self.assertEqual(d["added_count"], 1)
        self.assertEqual(d["removed_count"], 0)

    def test_changed_trigger_choice_is_detected(self):
        """The silent-instability case: same note count, different triggers."""
        base = self.base()
        new = self.base()
        new["entries"][0]["triggers"][0]["terms"] = ["h(i)"]
        d = ti.diff_inventories(base, new)
        self.assertEqual(d["delta_notes"], 0)
        self.assertEqual(d["added_count"], 0)
        self.assertEqual(d["removed_count"], 0)
        self.assertEqual(d["changed_count"], 1)
        self.assertEqual(d["changed"][0]["base_triggers"], [["f(i)"], ["g(i)"]])
        self.assertEqual(d["changed"][0]["new_triggers"], [["h(i)"], ["g(i)"]])

    def test_line_drift_alone_is_not_a_change(self):
        base = self.base()
        new = self.base()
        for e in new["entries"]:
            e["line"] += 100
            for t in e["triggers"]:
                t["line"] += 100
        d = ti.diff_inventories(base, new)
        self.assertEqual(d["added_count"], 0)
        self.assertEqual(d["removed_count"], 0)
        self.assertEqual(d["changed_count"], 0)

    def test_by_dir_delta(self):
        base = self.base()
        new = self.base()
        new["by_dir"] = {"src": 1}
        d = ti.diff_inventories(base, new)
        self.assertIn("src", d["by_dir_delta"])


class TestCli(unittest.TestCase):
    def parse_to(self, tmp, name, log_name, extra=None):
        out = os.path.join(tmp, name)
        args = [
            "parse",
            os.path.join(FIXTURES, log_name),
            "-o",
            out,
            "--label",
            name,
        ]
        run(args + (extra or []), expect=0)
        return out

    def test_parse_writes_valid_json(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = self.parse_to(tmp, "inv.json", "single_line_notes.log")
            with open(path) as f:
                inv = json.load(f)
            self.assertEqual(inv["total_notes"], 3)
            self.assertEqual(inv["label"], "inv.json")

    def test_parse_fails_on_a_log_with_no_notes(self):
        with tempfile.TemporaryDirectory() as tmp:
            empty = os.path.join(tmp, "empty.log")
            with open(empty, "w") as f:
                f.write("verification results:: 10 verified, 0 errors\n")
            result = run(["parse", empty, "-o", os.path.join(tmp, "o.json")], expect=1)
            self.assertIn("no trigger notes found", result.stderr)

    def test_parse_allow_empty(self):
        with tempfile.TemporaryDirectory() as tmp:
            empty = os.path.join(tmp, "empty.log")
            with open(empty, "w") as f:
                f.write("verification results:: 10 verified, 0 errors\n")
            run(
                ["parse", empty, "-o", os.path.join(tmp, "o.json"), "--allow-empty"],
                expect=0,
            )

    def test_report_renders_markdown(self):
        with tempfile.TemporaryDirectory() as tmp:
            inv = self.parse_to(tmp, "inv.json", "single_line_notes.log")
            result = run(["report", inv], expect=0)
            self.assertIn("# Verus trigger-note inventory", result.stdout)
            self.assertIn("| notes | 3 |", result.stdout)
            self.assertIn("`src`", result.stdout)

    def test_diff_clean_exits_zero_with_fail_flag(self):
        with tempfile.TemporaryDirectory() as tmp:
            a = self.parse_to(tmp, "a.json", "single_line_notes.log")
            b = self.parse_to(tmp, "b.json", "single_line_notes.log")
            result = run(["diff", a, b, "--fail-on-regression"], expect=0)
            self.assertIn("| delta | +0 |", result.stdout)

    def test_diff_regression_exits_one(self):
        with tempfile.TemporaryDirectory() as tmp:
            a = self.parse_to(tmp, "a.json", "single_line_notes.log")
            b = self.parse_to(tmp, "b.json", "single_line_notes.log")
            with open(a) as f:
                inv = json.load(f)
            inv["entries"] = inv["entries"][1:]
            inv["total_notes"] = len(inv["entries"])
            with open(a, "w") as f:
                json.dump(inv, f)
            result = run(["diff", a, b, "--fail-on-regression"], expect=1)
            self.assertIn("Added notes (regression)", result.stdout)
            self.assertIn("note(s) added", result.stderr)

    def test_diff_max_notes_ceiling(self):
        with tempfile.TemporaryDirectory() as tmp:
            a = self.parse_to(tmp, "a.json", "single_line_notes.log")
            b = self.parse_to(tmp, "b.json", "single_line_notes.log")
            run(["diff", a, b, "--max-notes", "3"], expect=0)
            result = run(["diff", a, b, "--max-notes", "2"], expect=1)
            self.assertIn("exceeds the ceiling", result.stderr)

    def test_diff_json_mode(self):
        with tempfile.TemporaryDirectory() as tmp:
            a = self.parse_to(tmp, "a.json", "single_line_notes.log")
            b = self.parse_to(tmp, "b.json", "multiline_notes.log")
            out = os.path.join(tmp, "d.json")
            run(["diff", a, b, "--json", "-o", out], expect=0)
            with open(out) as f:
                d = json.load(f)
            self.assertEqual(d["schema"], "trigger-inventory-diff/v1")
            self.assertEqual(d["added_count"], 2)
            self.assertEqual(d["removed_count"], 3)

    def test_bad_schema_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            bad = os.path.join(tmp, "bad.json")
            with open(bad, "w") as f:
                json.dump({"schema": "nope"}, f)
            result = run(["report", bad])
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("expected schema", result.stderr)


if __name__ == "__main__":
    unittest.main()
