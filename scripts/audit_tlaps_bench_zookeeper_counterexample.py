#!/usr/bin/env python3
"""Replay the fixed schedule in pinned TLA+ source and compare every trace value."""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
REPORT = ROOT / "reports/tlaps_bench_manual/zookeeper_counterexample"
PIN = "ffa3e31da28f960b70d8c5d44f2735e75d6edcac"
GOALS = {"PrimaryIntegrity": 132, "PrefixConsistency": 135, "Agreement": 163, "TotalOrder": 167}
TOKEN = re.compile(r'\s*(<<|>>|\|->|:>|@@|[\[\]{}(),]|"(?:[^"\\]|\\.)*"|-?\d+|[A-Za-z_][A-Za-z_0-9]*)')


class ValueParser:
    """Parse only TLC's printed finite values; no specification expressions."""

    def __init__(self, source):
        self.tokens = []
        pos = 0
        while source[pos:].strip():
            match = TOKEN.match(source, pos)
            if not match:
                raise ValueError(f"Unparsed TLC value: {source[pos:pos+80]}")
            self.tokens.append(match[1])
            pos = match.end()
        self.pos = 0

    def pop(self, expected=None):
        token = self.tokens[self.pos]
        self.pos += 1
        if expected is not None:
            assert token == expected, (expected, token)
        return token

    def peek(self):
        return self.tokens[self.pos] if self.pos < len(self.tokens) else None

    def expression(self):
        value = self.atom()
        if self.peek() == ":>":
            self.pop()
            value = {str(value): self.atom()}
        while self.peek() == "@@":
            self.pop()
            key = self.atom()
            self.pop(":>")
            value[str(key)] = self.atom()
        return value

    def atom(self):
        token = self.pop()
        if token == "(":
            value = self.expression()
            self.pop(")")
            return value
        if token in {"<<", "{"}:
            end = ">>" if token == "<<" else "}"
            values = []
            while self.peek() != end:
                values.append(self.expression())
                if self.peek() == ",":
                    self.pop()
                else:
                    break
            self.pop(end)
            return values if token == "<<" else {"set": values}
        if token == "[":
            values = {}
            while self.peek() != "]":
                key = self.pop()
                self.pop("|->")
                values[key] = self.expression()
                if self.peek() == ",":
                    self.pop()
                else:
                    break
            self.pop("]")
            return values
        if token.startswith('"'):
            return json.loads(token)
        if re.fullmatch(r"-?\d+", token):
            return int(token)
        if token in {"TRUE", "FALSE"}:
            return token == "TRUE"
        return token


def parse_trace(log):
    states = []
    for chunk in re.split(r"^State \d+:.*\n", log, flags=re.M)[1:]:
        chunk = re.split(r"\n(?:The number|Simulation|Progress|Finished|[0-9]+ states generated)", chunk)[0]
        variables = list(re.finditer(r"^/\\ (\w+) = ", chunk, re.M))
        state = {}
        for index, match in enumerate(variables):
            end = variables[index+1].start() if index+1 < len(variables) else len(chunk)
            parser = ValueParser(chunk[match.end():end].strip())
            state[match[1]] = parser.expression()
            assert parser.pos == len(parser.tokens), (len(states), match[1])
        states.append(state)
    return states


def canonical(value):
    if isinstance(value, list):
        return [canonical(v) for v in value]
    if isinstance(value, dict):
        if set(value) == {"set"}:
            return {"set": sorted((canonical(v) for v in value["set"]), key=lambda v: json.dumps(v, sort_keys=True))}
        return {k: canonical(v) for k, v in value.items()}
    return value


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    global REPORT, GOALS
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--bench", type=Path, default=Path("/var/tmp/TLAPS-Bench"))
    ap.add_argument("--jar", type=Path, default=Path("/var/tmp/tlaps-bench-tools/tla2tools.jar"))
    ap.add_argument("--index-failure", action="store_true", help="Audit the reachable invalid committed index and original goal evaluation errors.")
    args = ap.parse_args()
    if args.index_failure:
        REPORT = ROOT / "reports/tlaps_bench_manual/zookeeper_bad_index"
        GOALS = {"FollowingBound": 197, "Integrity": 197, "GlobalPrimaryOrder": 191, "LocalPrimaryOrder": 191}
    assert subprocess.check_output(["git", "-C", str(args.bench), "rev-parse", "HEAD"], text=True).strip() == PIN
    rel = Path("benchmark/proof-from-scratch-module/ZooKeeper_LowLevel")
    subprocess.run(["git", "-C", str(args.bench), "diff", "--exit-code", "HEAD", "--", str(rel)], check=True)
    sources = [rel / f for f in ["ZkV3_7_0Model.tla", "ZkV3_7_0Defs.tla", "ZkV3_7_0/FastLeaderElection.tla"]]
    model = (args.bench / sources[0]).read_text()
    assert len(re.findall(r"\bValue\b", model)) == 2
    assert "Value == Nat" in model and "CHOOSE v \\in Value : TRUE" in model
    raw = json.loads(gzip.decompress((REPORT / "trace.json.gz").read_bytes()))
    indices = json.loads((REPORT / "actions.json").read_text())["source_trace_indices"]
    expected = [canonical({k: v for k, v in raw[i].items() if k not in {"pc", "edge"}}) for i in indices]
    results = {}
    with tempfile.TemporaryDirectory(prefix="tlaps-zookeeper-replay-") as tmp:
        work = Path(tmp)
        for source in sources:
            shutil.copyfile(args.bench / source, work / source.name)
            assert (args.bench / source).read_bytes() == (work / source.name).read_bytes()
        for source in [REPORT / "Replay.tla", REPORT / "TLAPS.tla", *REPORT.glob("Replay*.cfg")]:
            shutil.copyfile(source, work / source.name)
        for goal, final in GOALS.items():
            command = ["java", "-XX:+UseParallelGC", "-Xmx512m", "-cp", str(args.jar.resolve()), "tlc2.TLC", "-workers", "1", "-metadir", str(work / ("states-" + goal)), "-deadlock", "-config", "Replay" + goal, "Replay"]
            run = subprocess.run(command, cwd=work, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=60)
            evaluation_error = args.index_failure and goal != "FollowingBound"
            expected_error = f"Error: Evaluating invariant {goal} failed." if evaluation_error else f"Error: Invariant {goal} is violated."
            assert run.returncode != 0 and expected_error in run.stdout, run.stdout
            if evaluation_error:
                assert "to integer 4 which is out of domain." in run.stdout
            actual = parse_trace(run.stdout)
            assert len(actual) == final+1
            for index, state in enumerate(actual):
                assert state["replayStep"] == index
                assert canonical({k: v for k, v in state.items() if k != "replayStep"}) == expected[index], (goal, index)
            log_name = f"replay-{goal}.log.gz"
            (REPORT / log_name).write_bytes(gzip.compress(run.stdout.encode(), mtime=0))
            results[goal] = {"failure_at_state": final, "states_compared": len(actual), "invariant_violation_confirmed": not evaluation_error,
                             "evaluation_error_confirmed": evaluation_error, "log": log_name, "exit_code": run.returncode}
            if not evaluation_error:
                results[goal]["violation_at_state"] = final
            print(f"{goal}: {len(actual)} complete source states matched; {'out-of-domain evaluation error' if evaluation_error else 'invariant violation'} confirmed.", flush=True)
    result = {"benchmark_commit": PIN, "source_sha256": {str(p): sha(args.bench / p) for p in sources}, "source_files_byte_identical": True,
              "method": "Exact source replay and complete finite-state comparison; this script asserts no Verus result.",
              "request_choice": 0, "request_choice_note": "Value is used only by the fixed natural-number choice; instantiated to {0} for TLC. Actions and goal definitions are unchanged.",
              "servers": 3, "max_epoch": 4, "transitions": len(indices)-1, "tlc_jar_sha256": sha(args.jar), "audit_script_sha256": sha(Path(__file__)), "replays": results,
              "sha256": {p.name: sha(p) for p in REPORT.iterdir() if p.is_file() and p.name not in {"source_replay_results.json", "results.json"}}}
    (REPORT / "source_replay_results.json").write_text(json.dumps(result, indent=2) + "\n")


if __name__ == "__main__":
    main()
