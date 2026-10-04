#!/usr/bin/env python3
"""Reject unilateral learning of commands and recovery that discards votes."""
import os
import shutil
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MODEL = ROOT / "models/non_bft/mencius"


def main():
    jar = Path(os.environ["TLA2TOOLS"]).resolve()
    source = (MODEL / "CoordinatedPaxos.tla").read_text()
    cases = [
        ("unilateral-command-learning", "(v = NoOp /\\ proposals[0] = NoOp)",
         "(proposals[0] = v)"),
        ("discard-accepted-value", "IF lastBallot[a] = -1 THEN NoOp ELSE lastValue[a]",
         "NoOp"),
    ]
    for name, old, new in cases:
        assert source.count(old) == 1, f"mutation location changed: {name}"
        with tempfile.TemporaryDirectory(prefix="consensus-mencius-") as directory:
            work = Path(directory)
            (work / "CoordinatedPaxos.tla").write_text(source.replace(old, new))
            shutil.copyfile(MODEL / "CoordinatedPaxos.cfg", work / "CoordinatedPaxos.cfg")
            result = subprocess.run(
                ["java", "-XX:+UseParallelGC", "-cp", str(jar), "tlc2.TLC",
                 "-workers", "1", "-seed", "1", "-noGenerateSpecTE",
                 "-metadir", str(work / "states"), "-config", "CoordinatedPaxos.cfg",
                 "CoordinatedPaxos.tla"],
                cwd=work, capture_output=True, text=True, timeout=60,
            )
            output = result.stdout + result.stderr
            if result.returncode != 12 or "Invariant Agreement is violated." not in output:
                raise SystemExit(f"{name}: expected agreement violation\n{output}")
            print(f"{name}: rejected by Agreement")


if __name__ == "__main__":
    main()
