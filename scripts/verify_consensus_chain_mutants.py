#!/usr/bin/env python3
"""Check that Chain Replication's invariants reject three protocol defects."""
import os
import shutil
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MODEL = ROOT / "models/non_bft/chain_replication"


def main():
    jar = Path(os.environ["TLA2TOOLS"]).resolve()
    source = (MODEL / "ChainReplication.tla").read_text()
    cases = [
        ("empty-new-tail", "Append(history, Committed)",
         "Append(history, <<>>)", "CompletedPrefix"),
        ("repeated-request", "r \\notin submitted", "TRUE", "Unique"),
        ("out-of-order-forward", "history[i-1][Len(history[i])+1]",
         "history[i-1][Len(history[i-1])]", "Propagation"),
    ]
    for name, old, new, invariant in cases:
        assert source.count(old) == 1, f"mutation location changed: {name}"
        with tempfile.TemporaryDirectory(prefix="consensus-chain-") as directory:
            work = Path(directory)
            (work / "ChainReplication.tla").write_text(source.replace(old, new))
            shutil.copyfile(MODEL / "ChainReplication.cfg", work / "ChainReplication.cfg")
            result = subprocess.run(
                ["java", "-XX:+UseParallelGC", "-cp", str(jar), "tlc2.TLC",
                 "-workers", "1", "-seed", "1", "-noGenerateSpecTE",
                 "-metadir", str(work / "states"), "-config", "ChainReplication.cfg",
                 "ChainReplication.tla"],
                cwd=work, capture_output=True, text=True, timeout=60,
            )
            output = result.stdout + result.stderr
            if result.returncode != 12 or f"Invariant {invariant} is violated." not in output:
                raise SystemExit(f"{name}: expected violation of {invariant}\n{output}")
            print(f"{name}: rejected by {invariant}")


if __name__ == "__main__":
    main()
