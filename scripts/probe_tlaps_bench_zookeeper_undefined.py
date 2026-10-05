#!/usr/bin/env python3
"""Check conditional consequences of the three undefined ZooKeeper goals.

These checks do not prove or refute any benchmark invariant. The imported
reachability certificate and identifier lemmas must match a passing full run.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
REPORT = ROOT / "reports/tlaps_bench_manual"
OUT = REPORT / "zookeeper_index_probe"
MODULES = [
    "zab", "zab_collections", "zab_connections", "zab_log_math",
    "zk_election", "zk_election_types", "zookeeper", "zookeeper_channels",
    "zookeeper_connections", "zookeeper_bad_index", "zookeeper_quorum_receipts",
    "zookeeper_receipt_sets", "zookeeper_receipts", "zookeeper_support",
    "zookeeper_trace_ids",
]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verus", default=os.environ.get("VERUS_PATH", "verus"))
    args = parser.parse_args()
    baseline_path = REPORT / "results.json"
    baseline = json.loads(baseline_path.read_text())
    if not baseline["verification_passed"]:
        raise RuntimeError("A successful full proof-suite run is required")
    for name, digest in baseline["proof_sha256"].items():
        if sha(ROOT / name) != digest:
            raise RuntimeError(f"Input differs from the successful full run: {name}")
    paths = {name: ROOT / f"src/protocol/TLAPSBench/{name}.rs" for name in MODULES}
    paths["temporal"] = ROOT / "src/common/logic/temporal_s.rs"
    paths["undefined_dependencies"] = OUT / "undefined_dependencies.rs"
    hashes = {str(p.relative_to(ROOT)): sha(p) for p in paths.values()}
    baseline_hash = sha(baseline_path)
    harness = '#![allow(non_snake_case)]\npub mod TLAPSBench {\n'
    harness += "".join(f"#[path = {json.dumps(str(p))}] pub mod {name};\n" for name, p in paths.items())
    harness += "}\n"
    with tempfile.TemporaryDirectory(prefix="zk-undefined-") as directory:
        entry = Path(directory) / "harness.rs"
        entry.write_text(harness)
        command = [args.verus, "--crate-type=lib", "--no-cheating", "--triggers-mode", "silent",
                   "--verify-only-module", "TLAPSBench::undefined_dependencies", "--rlimit", "30",
                   "--multiple-errors", "3", "--num-threads", "4", "-V", "spinoff-all", str(entry)]
        run = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if sha(baseline_path) != baseline_hash or hashes != {str(p.relative_to(ROOT)): sha(p) for p in paths.values()}:
        raise RuntimeError("Inputs changed during verification")
    log = OUT / "undefined-dependencies.log"
    log.write_text(run.stdout)
    match = re.search(r"verification results:: (\d+) verified, (\d+) errors", run.stdout)
    passed = run.returncode == 0 and match is not None and match.groups() == ("3", "0")
    record = {
        "recorded_utc": datetime.now(timezone.utc).isoformat(),
        "status": "conditional_diagnostics_verified" if passed else "diagnostic_check_failed",
        "scope": "Conditional consequences at certified reachable states; neither proofs nor refutations of the three benchmark goals.",
        "counts_toward_benchmark": False,
        "verification_passed": passed,
        "verified_functions": int(match.group(1)) if match else None,
        "errors": int(match.group(2)) if match else None,
        "verus": subprocess.check_output([args.verus, "--version"], text=True).strip(),
        "command": command,
        "reproduce": "python3 scripts/probe_tlaps_bench_zookeeper_undefined.py --verus /path/to/verus",
        "harness": harness,
        "input_sha256": hashes,
        "script_sha256": sha(Path(__file__)),
        "log_sha256": sha(log),
        "baseline_results_sha256": baseline_hash,
        "baseline_verified_functions": baseline["verified_functions"],
    }
    (OUT / "undefined-dependencies-results.json").write_text(json.dumps(record, indent=2) + "\n")
    print(run.stdout, end="")
    raise SystemExit(0 if passed else 1)


if __name__ == "__main__":
    main()
