#!/usr/bin/env python3
"""Tests for verus_timing.py (Phase 54.2.c).

`fixtures/trigger_inventory/time_expanded_modules.log` is real Verus output
(`verus --crate-type=lib --time-expanded`, release 0.2026.01.02.6f52890) over a
two-module probe crate. It pins the text shape the parser depends on, including
the unnamed crate-root row and the `, N rlimit` suffix on the smt rows.
"""

import json
import os
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
SCRIPT = os.path.join(HERE, "verus_timing.py")
FIXTURES = os.path.join(HERE, "fixtures", "trigger_inventory")

sys.path.insert(0, HERE)
import verus_timing as vt  # noqa: E402


def fixture(name):
    with open(os.path.join(FIXTURES, name)) as f:
        return f.read()


def synthetic_log(modules, total_ms=1000):
    """Build a `--time-expanded`-shaped log from {module: verify_ms}."""
    lines = [
        "verus-build-info",
        "Verus",
        "  Version: 0.2026.08.02.b677dd5",
        "",
        "total-time:             {} ms    (estimated total cpu time {} ms)".format(
            total_ms, total_ms
        ),
        "    verification-time:         {} ms".format(total_ms // 2),
        "",
        "verify-crate-time-breakdown",
        "    total verify-time:            {} ms   (4 threads)".format(
            sum(modules.values())
        ),
    ]
    for i, (name, ms) in enumerate(modules.items(), start=1):
        label = "" if name == vt.ROOT_MODULE else name
        lines.append("      {}. {:<40s} {} ms".format(i, label, ms))
    return "\n".join(lines) + "\n"


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
    def setUp(self):
        self.inv = vt.build_inventory(fixture("time_expanded_modules.log"))

    def test_schema_and_version(self):
        self.assertEqual(self.inv["schema"], vt.SCHEMA)
        self.assertEqual(self.inv["verus_version"], "0.2026.01.02.6f52890")

    def test_modules_are_found(self):
        self.assertEqual(self.inv["module_count"], 3)
        self.assertEqual(set(self.inv["modules"]), {"alpha", "beta", vt.ROOT_MODULE})

    def test_unnamed_row_becomes_the_root_module(self):
        # Verus prints the crate root with an empty name; an empty string key
        # would silently collide with "module missing".
        self.assertIn(vt.ROOT_MODULE, self.inv["modules"])
        self.assertNotIn("", self.inv["modules"])

    def test_every_section_is_captured_per_module(self):
        alpha = self.inv["modules"]["alpha"]
        for field in ("verify_ms", "air_ms", "smt_init_ms", "smt_run_ms"):
            self.assertIsNotNone(alpha[field], "{} missing".format(field))
        self.assertIn("rlimit", alpha)
        self.assertGreater(alpha["rlimit"], 0)

    def test_totals_include_the_parenthesised_total_time_line(self):
        # `total-time: 370 ms    (estimated total cpu time 467 ms)`
        self.assertIn("total-time", self.inv["totals"])
        self.assertGreater(self.inv["totals"]["total-time"], 0)
        self.assertIn("verification-time", self.inv["totals"])
        self.assertEqual(self.inv["totals"]["threads"], 3)

    def test_total_verify_ms_is_the_sum_of_modules(self):
        expected = sum(m["verify_ms"] for m in self.inv["modules"].values())
        self.assertEqual(self.inv["total_verify_ms"], expected)

    def test_modules_are_sorted_slowest_first(self):
        times = [m["verify_ms"] for m in self.inv["modules"].values()]
        self.assertEqual(times, sorted(times, reverse=True))

    def test_log_without_timings_yields_no_modules(self):
        inv = vt.build_inventory("verification results:: 10 verified, 0 errors\n")
        self.assertEqual(inv["module_count"], 0)

    def test_trigger_notes_in_the_same_log_are_ignored(self):
        mixed = fixture("single_line_notes.log") + fixture(
            "time_expanded_modules.log"
        )
        inv = vt.build_inventory(mixed)
        self.assertEqual(set(inv["modules"]), {"alpha", "beta", vt.ROOT_MODULE})


class TestJsonPayload(unittest.TestCase):
    """`--output-json` is the preferred source: the text breakdown prints only
    the top 3 modules per section, so a per-module gate built on it would cover
    3 of 142 modules."""

    def payload(self, entries, air=None):
        return "some diagnostic line\n" + json.dumps(
            {
                "times-ms": {
                    "total": 1000,
                    "total-verify": sum(e["time"] for e in entries),
                    "verification": {"total": 900},
                    "rust": {"total": 100},
                    "total-verify-module-times": entries,
                    "air": {"module-times": air or []},
                    "smt": {"smt-run-module-times": []},
                },
                "verus": {"version": "0.2026.08.02.b677dd5"},
            },
            indent=2,
        )

    def test_json_is_preferred_and_recorded(self):
        inv = vt.build_inventory(self.payload([{"module": "a", "time": 10}]))
        self.assertEqual(inv["parsed_from"], "output-json")
        self.assertEqual(inv["module_count"], 1)

    def test_version_comes_from_the_payload(self):
        inv = vt.build_inventory(self.payload([{"module": "a", "time": 10}]))
        self.assertEqual(inv["verus_version"], "0.2026.08.02.b677dd5")

    def test_repeated_module_entries_are_summed(self):
        # Verus emits one entry per verification chunk; the module's cost is
        # their sum, and summing reproduces the reported total-verify.
        inv = vt.build_inventory(
            self.payload(
                [
                    {"module": "a", "time": 10},
                    {"module": "a", "time": 5},
                    {"module": "b", "time": 3},
                ]
            )
        )
        self.assertEqual(inv["modules"]["a"]["verify_ms"], 15)
        self.assertEqual(inv["modules"]["b"]["verify_ms"], 3)
        self.assertEqual(inv["total_verify_ms"], 18)

    def test_unnamed_module_becomes_root(self):
        inv = vt.build_inventory(self.payload([{"module": "", "time": 4}]))
        self.assertIn(vt.ROOT_MODULE, inv["modules"])

    def test_text_log_still_parses_when_no_json_present(self):
        inv = vt.build_inventory(fixture("time_expanded_modules.log"))
        self.assertEqual(inv["parsed_from"], "time-expanded-text")
        self.assertEqual(inv["module_count"], 3)

    def test_malformed_json_falls_back_to_text(self):
        inv = vt.build_inventory(fixture("time_expanded_modules.log") + "\n{\nnot json\n")
        self.assertEqual(inv["parsed_from"], "time-expanded-text")


class TestDiff(unittest.TestCase):
    def inv(self, modules, label="x"):
        return vt.build_inventory(synthetic_log(modules), label=label)

    def test_identical_runs_have_no_regressions(self):
        a = self.inv({"slow": 10000, "fast": 900})
        d = vt.diff_inventories(a, a)
        self.assertEqual(d["regressions"], [])
        self.assertEqual(d["improvements"], [])
        self.assertEqual(d["total_delta_pct"], 0.0)

    def test_regression_past_the_threshold_is_reported(self):
        base = self.inv({"slow": 10000})
        new = self.inv({"slow": 13000})
        d = vt.diff_inventories(base, new)
        self.assertEqual(len(d["regressions"]), 1)
        r = d["regressions"][0]
        self.assertEqual(r["module"], "slow")
        self.assertEqual(r["delta_ms"], 3000)
        self.assertEqual(r["delta_pct"], 30.0)

    def test_regression_within_the_threshold_is_not_reported(self):
        d = vt.diff_inventories(self.inv({"slow": 10000}), self.inv({"slow": 11500}))
        self.assertEqual(d["regressions"], [])

    def test_small_module_swing_is_below_the_noise_floor(self):
        # 40ms -> 80ms is +100%, but it is scheduler jitter, not a proof
        # regression; it must be reported and must not fail the build.
        d = vt.diff_inventories(self.inv({"tiny": 40}), self.inv({"tiny": 80}))
        self.assertEqual(d["regressions"], [])
        self.assertEqual(len(d["below_noise_floor"]), 1)
        self.assertEqual(d["below_noise_floor"][0]["module"], "tiny")

    def test_noise_floor_is_configurable(self):
        d = vt.diff_inventories(
            self.inv({"tiny": 40}), self.inv({"tiny": 80}), min_ms=10
        )
        self.assertEqual(len(d["regressions"]), 1)

    def test_threshold_is_configurable(self):
        d = vt.diff_inventories(
            self.inv({"slow": 10000}),
            self.inv({"slow": 11000}),
            max_regression_pct=5,
        )
        self.assertEqual(len(d["regressions"]), 1)

    def test_improvement_is_reported_separately(self):
        d = vt.diff_inventories(self.inv({"slow": 10000}), self.inv({"slow": 5000}))
        self.assertEqual(d["regressions"], [])
        self.assertEqual(len(d["improvements"]), 1)
        self.assertEqual(d["improvements"][0]["delta_pct"], -50.0)

    def test_added_and_removed_modules(self):
        d = vt.diff_inventories(self.inv({"a": 1000}), self.inv({"b": 1000}))
        self.assertEqual(d["added_modules"], ["b"])
        self.assertEqual(d["removed_modules"], ["a"])
        self.assertEqual(d["regressions"], [])

    def test_regressions_are_ordered_by_absolute_cost(self):
        base = self.inv({"a": 10000, "b": 2000})
        new = self.inv({"a": 20000, "b": 6000})
        d = vt.diff_inventories(base, new)
        self.assertEqual([r["module"] for r in d["regressions"]], ["a", "b"])


class TestMergeMin(unittest.TestCase):
    """A single run is not a usable baseline.

    Measured: the module `implementation::RSL::replicaimpl_no_receive_clock`
    read 1967 ms in the original single-run baseline but 2372/2438/2490 ms
    across three runs of that *same commit*. Comparing a later run against the
    lucky 1967 produced a 30% "regression" in code that never touched it.
    Min-of-N on both sides is the fix.
    """

    def inv(self, modules, label="r"):
        return vt.build_inventory(synthetic_log(modules), label=label)

    def test_minimum_is_taken_per_module(self):
        m = vt.merge_min(
            [self.inv({"a": 2490, "b": 100}), self.inv({"a": 2372, "b": 150})]
        )
        self.assertEqual(m["modules"]["a"]["verify_ms"], 2372)
        self.assertEqual(m["modules"]["b"]["verify_ms"], 100)

    def test_run_count_is_recorded(self):
        m = vt.merge_min([self.inv({"a": 10})] * 3)
        self.assertEqual(m["runs_merged"], 3)
        self.assertIn("min of 3 runs", m["source_log"])

    def test_modules_absent_from_one_run_are_kept(self):
        m = vt.merge_min([self.inv({"a": 10}), self.inv({"b": 20})])
        self.assertEqual(set(m["modules"]), {"a", "b"})

    def test_merged_inventory_diffs_like_any_other(self):
        base = vt.merge_min([self.inv({"a": 2372}), self.inv({"a": 2490})])
        new = vt.merge_min([self.inv({"a": 2400}), self.inv({"a": 2571})])
        d = vt.diff_inventories(base, new)
        self.assertEqual(d["regressions"], [])

    def test_empty_input_is_rejected(self):
        with self.assertRaises(ValueError):
            vt.merge_min([])

    def test_schema_is_preserved(self):
        m = vt.merge_min([self.inv({"a": 10})])
        self.assertEqual(m["schema"], vt.SCHEMA)


class TestNoiseFloor(unittest.TestCase):
    def test_default_floor_is_the_measured_one(self):
        # Below 1000 ms, identical-code runs on this crate already swing >20%.
        self.assertEqual(vt.DEFAULT_MIN_MS, 1000)

    def test_a_small_baseline_never_fails(self):
        # The real case: base 953 ms (same-code spread 953-1168) vs 1213 ms
        # after an unrelated change. "+27%" that a third sample dissolved to
        # +12%. The percentage is relative to the base, so a base inside the
        # noisy regime cannot support the claim.
        base = vt.build_inventory(synthetic_log({"m": 953}))
        new = vt.build_inventory(synthetic_log({"m": 1213}))
        d = vt.diff_inventories(base, new)
        self.assertEqual(d["regressions"], [])
        self.assertEqual(len(d["below_noise_floor"]), 1)

    def test_a_large_baseline_still_fails(self):
        base = vt.build_inventory(synthetic_log({"m": 10000}))
        new = vt.build_inventory(synthetic_log({"m": 13000}))
        self.assertEqual(len(vt.diff_inventories(base, new)["regressions"]), 1)

    def test_below_floor_rows_are_sorted_by_absolute_delta(self):
        base = vt.build_inventory(synthetic_log({"small": 100, "mid": 900}))
        new = vt.build_inventory(synthetic_log({"small": 5000, "mid": 1200}))
        d = vt.diff_inventories(base, new)
        # A 100ms -> 5000ms jump must not hide behind a smaller one.
        self.assertEqual(d["below_noise_floor"][0]["module"], "small")


class TestConfirmation(unittest.TestCase):
    """A regression must reproduce against a second run of the same new code.

    Measured during the 54.3 pilot: an *untouched* module read 1967 / 2448 /
    2241 ms across three runs, because Verus verifies modules in parallel and
    wall-clock moves with contention. Without confirmation the 20% gate flags
    modules nobody edited, and a gate that cries wolf gets ignored.
    """

    def inv(self, modules, label="x"):
        return vt.build_inventory(synthetic_log(modules), label=label)

    def test_reproduced_regression_stays(self):
        d = vt.diff_inventories(self.inv({"m": 1000}), self.inv({"m": 2000}))
        d = vt.confirm_regressions(d, self.inv({"m": 1900}, label="confirm"))
        self.assertEqual(len(d["regressions"]), 1)
        self.assertEqual(d["regressions"][0]["confirm_ms"], 1900)

    def test_unreproduced_regression_is_demoted(self):
        d = vt.diff_inventories(self.inv({"m": 1000}), self.inv({"m": 2000}))
        d = vt.confirm_regressions(d, self.inv({"m": 1050}, label="confirm"))
        self.assertEqual(d["regressions"], [])
        self.assertEqual(len(d["unconfirmed_regressions"]), 1)
        self.assertEqual(d["unconfirmed_regressions"][0]["confirm_ms"], 1050)

    def test_module_absent_from_the_confirmation_run_is_demoted(self):
        d = vt.diff_inventories(self.inv({"m": 1000}), self.inv({"m": 2000}))
        d = vt.confirm_regressions(d, self.inv({"other": 10}, label="confirm"))
        self.assertEqual(d["regressions"], [])
        self.assertIsNone(d["unconfirmed_regressions"][0]["confirm_ms"])

    def test_confirmation_respects_the_noise_floor(self):
        # Base is above the floor, so the diff flags it; the confirmation run
        # lands below the floor, which cannot support the claim either.
        d = vt.diff_inventories(
            self.inv({"m": 600}), self.inv({"m": 2000}), min_ms=500
        )
        self.assertEqual(len(d["regressions"]), 1)
        d = vt.confirm_regressions(d, self.inv({"m": 400}, label="c"), min_ms=500)
        self.assertEqual(d["regressions"], [])

    def test_confirmation_source_is_recorded(self):
        d = vt.diff_inventories(self.inv({"m": 1000}), self.inv({"m": 2000}))
        d = vt.confirm_regressions(d, self.inv({"m": 1900}, label="run-2"))
        self.assertEqual(d["confirmed_against"], "run-2")


class TestCli(unittest.TestCase):
    def parse_to(self, tmp, name, log_text):
        log = os.path.join(tmp, name + ".log")
        with open(log, "w") as f:
            f.write(log_text)
        out = os.path.join(tmp, name + ".json")
        run(["parse", log, "-o", out, "--label", name], expect=0)
        return out

    def test_parse_writes_json(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = self.parse_to(tmp, "base", fixture("time_expanded_modules.log"))
            with open(path) as f:
                inv = json.load(f)
            self.assertEqual(inv["module_count"], 3)

    def test_parse_fails_without_a_timing_breakdown(self):
        with tempfile.TemporaryDirectory() as tmp:
            log = os.path.join(tmp, "plain.log")
            with open(log, "w") as f:
                f.write("verification results:: 10 verified, 0 errors\n")
            result = run(["parse", log, "-o", os.path.join(tmp, "o.json")], expect=1)
            self.assertIn("--time-expanded", result.stderr)

    def test_parse_allow_empty(self):
        with tempfile.TemporaryDirectory() as tmp:
            log = os.path.join(tmp, "plain.log")
            with open(log, "w") as f:
                f.write("verification results:: 10 verified, 0 errors\n")
            run(
                ["parse", log, "-o", os.path.join(tmp, "o.json"), "--allow-empty"],
                expect=0,
            )

    def test_report_renders_markdown(self):
        with tempfile.TemporaryDirectory() as tmp:
            inv = self.parse_to(tmp, "base", fixture("time_expanded_modules.log"))
            result = run(["report", inv], expect=0)
            self.assertIn("# Verus verification timing", result.stdout)
            self.assertIn("| `alpha` |", result.stdout)

    def test_diff_fails_only_on_a_real_regression(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = self.parse_to(tmp, "base", synthetic_log({"slow": 10000}))
            same = self.parse_to(tmp, "same", synthetic_log({"slow": 10000}))
            worse = self.parse_to(tmp, "worse", synthetic_log({"slow": 14000}))
            run(["diff", base, same, "--fail-on-regression"], expect=0)
            result = run(["diff", base, worse, "--fail-on-regression"], expect=1)
            self.assertIn("regressed more than 20%", result.stderr)
            self.assertIn("Regressions", result.stdout)

    def test_diff_json_mode(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = self.parse_to(tmp, "base", synthetic_log({"slow": 10000}))
            worse = self.parse_to(tmp, "worse", synthetic_log({"slow": 14000}))
            out = os.path.join(tmp, "d.json")
            run(["diff", base, worse, "--json", "-o", out], expect=0)
            with open(out) as f:
                d = json.load(f)
            self.assertEqual(d["schema"], "verus-timing-diff/v1")
            self.assertEqual(d["regressions"][0]["delta_pct"], 40.0)

    def test_bad_schema_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            bad = os.path.join(tmp, "bad.json")
            with open(bad, "w") as f:
                json.dump({"schema": "trigger-inventory/v1"}, f)
            result = run(["report", bad])
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("expected schema", result.stderr)


class TestCiWiring(unittest.TestCase):
    """The timing capture is only useful if CI actually asks for --time-expanded."""

    def setUp(self):
        path = os.path.join(os.path.dirname(HERE), ".github", "workflows", "ci.yml")
        with open(path) as f:
            self.ci = f.read()

    def test_scons_passes_the_timing_flag(self):
        self.assertIn('--verus-extra-args="--time-expanded"', self.ci)

    def test_timing_is_parsed_and_uploaded(self):
        self.assertIn("scripts/verus_timing.py parse verus-verify.log", self.ci)
        self.assertIn("verus-timing.json", self.ci)

    def test_timing_capture_cannot_change_the_job_verdict(self):
        # Same contract as the trigger capture: report, never assert.
        block = self.ci.split("Capture verification timing", 1)[1][:800]
        self.assertIn("--allow-empty", block)
        self.assertNotIn("--fail-on-regression", block)


class TestSconsWiring(unittest.TestCase):
    """SConstruct must actually forward --verus-extra-args to the verifier."""

    def setUp(self):
        with open(os.path.join(os.path.dirname(HERE), "SConstruct")) as f:
            self.scons = f.read()

    def test_option_is_declared(self):
        self.assertIn("'--verus-extra-args'", self.scons)
        self.assertIn("dest='verus_extra_args'", self.scons)

    def test_option_is_appended_to_the_verus_command_line(self):
        self.assertIn('GetOption("verus_extra_args")', self.scons)
        self.assertIn("cmd_line += shlex.split(extra)", self.scons)
        self.assertIn("import shlex", self.scons)


if __name__ == "__main__":
    unittest.main()
