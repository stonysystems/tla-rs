#!/usr/bin/env python3
"""Verify the handwritten ports and record coverage of the pinned current suite."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
PIN = "ffa3e31da28f960b70d8c5d44f2735e75d6edcac"
REFUTED = {
    "ZooKeeper_LowLevel": {
        name: {
            "counterexample_theorem": "zookeeper_counterexample::counterexample",
            "evidence": "zookeeper_counterexample/results.json",
        } for name in ["PrimaryIntegrity", "PrefixConsistency", "Agreement", "TotalOrder"]
    },
    "etcd_raft": {
        "LeaderCompleteness": {
            "counterexample_theorem": "etcd_counterexample::counterexample",
            "evidence": "etcd_counterexample/results.json",
        },
        "MoreUpToDate": {
            "counterexample_theorem": "etcd_uptodate_counterexample::counterexample",
            "evidence": "etcd_uptodate_counterexample/results.json",
        },
    },
}
SOURCE_EVALUATION_ERRORS = {
    "ZooKeeper_LowLevel": {
        name: {
            "evidence": "zookeeper_bad_index/results.json",
            "reason": "The unchanged source reaches a committed index of 4 in a three-entry history; TLC cannot evaluate the original goal's out-of-domain access.",
        } for name in ["Integrity", "GlobalPrimaryOrder", "LocalPrimaryOrder"]
    },
}
PORTS = {
    "OpenAddressing": ("open_addressing", {
        "CompleteAsSafety": "open_addressing_proof::benchmark_safety",
        "Sorted": "open_addressing_proof::benchmark_safety",
        "Contains": "open_addressing_safety::benchmark_safety",
        "Consistent": "open_addressing_safety::benchmark_safety",
        "Duplicates": "open_addressing_safety::benchmark_safety",
    }),
    "tlaplus_examples_FlashProtocol": ("flash", {
        "TypeCorrect": "flash_proof::type_correct_always",
        "CacheDataCorrect": "flash_shared::cache_data_correct",
        "InvProgressCorrect": "flash_invalidation::inv_progress_correct",
        "ReqProgressCorrect": "flash_requests::request_progress_correct",
        "UniProgressCorrect": "flash_requests::request_progress_correct",
        "DirProgressCorrect": "flash_directory::dir_progress_correct",
        "MemDataCorrect": "flash_coherence::benchmark_coherence",
        "Lemma_1_Correct": "flash_coherence::benchmark_coherence",
        **{f"Lemma_{i}_Correct": "flash_control::benchmark_control" for i in [2, 3, 4]},
        **{name + "ProgressCorrect": "flash_liveness::benchmark_progress" for name in ["Rp", "Wb", "ShWb", "Nakc"]},
    }),
    "ivy_examples_tlb": ("tlb", {"Safety": "tlb_proof::safety", "Liveness": "tlb_progress::liveness"}),
    "etcd_raft": ("etcd", {
        "MoreThanOneLeader": "etcd_election::more_than_one_leader_correct",
        "ElectionSafety": "etcd_origins::election_safety_correct",
        "LogMatching": "etcd_logs::log_matching_correct",
        "CommittedIsDurable": "etcd_durability::committed_is_durable_correct",
        "LogInv": "etcd_safety::benchmark_safety",
        "QuorumLog": "etcd_safety::benchmark_safety",
    }),
    "HashicorpRaft": ("hashicorp", {
        "ConfigurationSafetyCorrect": "hashicorp_config::configuration_safety_correct",
        **{name + "Correct": "hashicorp_safety::benchmark_safety" for name in [
            "LeaderCompleteness", "StateMachineSafety", "CommittedEntriesPreserved",
            "LogMatching", "ElectionSafety",
        ]},
    }),
    "ZooKeeper": ("zab", {
        "Leadership1": "zab_elections::benchmark_leadership",
        "Leadership2": "zab_elections::benchmark_leadership",
        **{name: "zab_commit_safety::benchmark_safety" for name in [
            "PrefixConsistency", "Agreement", "TotalOrder", "GlobalPrimaryOrder",
        ]},
        "PrimaryIntegrity": "zab_primary_barrier::benchmark_primary_integrity",
        "Integrity": "zab_integrity::benchmark_integrity",
        "LocalPrimaryOrder": "zab_proposal_order::benchmark_local_order",
    }),
    "CahillSSI": ("cahill", {"CahillSerializableCorrect": "cahill_cycle_search::benchmark_serializable"}),
    "MongoDB": ("mongodb", {"SnapshotIsolationCorrect": "mongodb_snapshot_isolation::benchmark_snapshot_isolation"}),
    "ZooKeeper_LowLevel": ("zookeeper", {
        "Leadership1": "zookeeper_leadership::benchmark_leadership1",
        "Leadership2": "zookeeper_leadership::benchmark_leadership2",
    }),
}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def record_certificates(report, output):
    """Tie replay manifests to this successful complete proof-suite run."""
    verification_hash = sha(output / "verification.log")
    for case in ["etcd_counterexample", "etcd_uptodate_counterexample"]:
        path = output / case / "results.json"
        record = json.loads(path.read_text())
        cert = record["verus_certificate"]
        assert cert["proof_sha256"] == report["proof_sha256"][f"src/protocol/TLAPSBench/{case}.rs"]
        assert cert["generator_sha256"] == sha(ROOT / f"scripts/build_tlaps_bench_{case}.py")
        cert.update(full_harness_verified_functions=report["verified_functions"], verification_log_sha256=verification_hash, command=report["command"])
        path.write_text(json.dumps(record, indent=2) + "\n")
    for case in ["zookeeper_counterexample", "zookeeper_bad_index"]:
        folder = output / case
        audit = json.loads((folder / "source_replay_results.json").read_text())
        for name, digest in audit["sha256"].items():
            assert sha(folder / name) == digest, (case, name)
        assert audit["audit_script_sha256"] == sha(ROOT / "scripts/audit_tlaps_bench_zookeeper_counterexample.py")
        proof_path = f"src/protocol/TLAPSBench/{case}.rs"
        assert f"pub mod {case};" in (ROOT / "src/protocol/TLAPSBench/mod.rs").read_text()
        cert = {
            "theorem": f"{case}::counterexample", "infinite_behavior": True,
            "stutter_after_index": audit["transitions"], "no_cheating": True,
            "full_harness_verified_functions": report["verified_functions"], "full_harness_errors": 0,
            "verus": report["verus"], "command": report["command"],
            "verification_log": "../verification.log", "verification_log_sha256": verification_hash,
            "proof_sha256": report["proof_sha256"][proof_path],
            "identifier_proof_sha256": report["proof_sha256"]["src/protocol/TLAPSBench/zookeeper_trace_ids.rs"],
            "generator_sha256": sha(ROOT / "scripts/build_tlaps_bench_zookeeper_counterexample.py"),
        }
        index_failure = case == "zookeeper_bad_index"
        record = {
            "benchmark_commit": PIN,
            "status": "reachable_invalid_index_certified_and_source_goal_evaluation_errors_audited" if index_failure else "refuted_in_verus_and_pinned_tla_source",
            "goals": ["Integrity", "GlobalPrimaryOrder", "LocalPrimaryOrder"] if index_failure else ["PrimaryIntegrity", "PrefixConsistency", "Agreement", "TotalOrder"],
            "transitions": audit["transitions"], "source_modified": False,
            "source_audit": "source_replay_results.json", "source_audit_sha256": sha(folder / "source_replay_results.json"),
            "verus_certificate": cert,
        }
        if index_failure:
            record["scope"] = "Verus certifies the reachable invalid committed range. The three original source goals fail to evaluate; their negations are not claimed as Verus theorems."
        (folder / "results.json").write_text(json.dumps(record, indent=2) + "\n")


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--bench", type=Path, default=Path("/var/tmp/TLAPS-Bench"))
    ap.add_argument("--verus", default=os.environ.get("VERUS_PATH", "verus"))
    ap.add_argument("--output", type=Path, default=ROOT / "reports/tlaps_bench_manual")
    ap.add_argument("--threads", type=int, default=4)
    args = ap.parse_args()
    bench = args.bench.resolve()
    head = subprocess.check_output(["git", "-C", str(bench), "rev-parse", "HEAD"], text=True).strip()
    if head != PIN:
        raise SystemExit(f"Expected benchmark {PIN}, got {head}")
    subprocess.run(["git", "-C", str(bench), "diff", "--exit-code", "HEAD", "--", "benchmark/problem-sets.json", "benchmark/proof-from-scratch-module"], check=True, stdout=subprocess.DEVNULL)
    args.output.mkdir(parents=True, exist_ok=True)
    def proof_files():
        return sorted((ROOT / "src/protocol/TLAPSBench").glob("*.rs")) + [ROOT / "src/protocol/tlaps_bench_harness.rs", ROOT / "src/common/logic/temporal_s.rs"]
    before_proof_hashes = {str(p.relative_to(ROOT)): sha(p) for p in proof_files()}
    command = [args.verus, "--crate-type=lib", "--no-cheating", "--triggers-mode", "silent", "--rlimit", "30",
               "--num-threads", str(args.threads), "-V", "spinoff-all", "src/protocol/tlaps_bench_harness.rs"]
    run = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    after_proof_hashes = {str(p.relative_to(ROOT)): sha(p) for p in proof_files()}
    if after_proof_hashes != before_proof_hashes:
        raise RuntimeError("Proof inputs changed during verification; refusing to publish mismatched results and hashes.")
    (args.output / "verification.log").write_text(run.stdout)
    match = re.search(r"verification results:: (\d+) verified, 0 errors", run.stdout)
    passed = run.returncode == 0 and match is not None
    print(run.stdout, end="", flush=True)
    probes_path = args.output / "probes/results.json"
    probes = json.loads(probes_path.read_text()) if probes_path.exists() else []
    probe_status = {(x["module"], x["goal"]): x["status"] for x in probes}
    cases = json.loads((bench / "benchmark/problem-sets.json").read_text())["current"]["tasks"]
    results = []
    for case in cases:
        family, filename = case.split("/")
        module, proved = PORTS.get(family, (None, {}))
        refuted = REFUTED.get(family, {})
        evaluation_errors = SOURCE_EVALUATION_ERRORS.get(family, {})
        path = bench / "benchmark/proof-from-scratch-module" / case
        prefix = Path(filename).stem + "_"
        tasks = re.findall(r"BEGIN AGENT PROOF ([^\s]+)\.tla", path.read_text())
        goals = []
        for task in tasks:
            name = task.split("/")[-1].removeprefix(prefix)
            liveness = name.endswith("ProgressCorrect") or name == "Liveness"
            status = (("proved" if passed else "verification_failed") if name in proved else
                      ("refuted" if passed else "verification_failed") if name in refuted else
                      "source_evaluation_error" if name in evaluation_errors else (
                probe_status.get((module, name), "open") if module else "not_ported"))
            goals.append({"name": name, "kind": "liveness" if liveness else "invariant", "status": status,
                          **({"theorem": proved[name]} if name in proved else {}),
                          **refuted.get(name, {}), **evaluation_errors.get(name, {})})
        if set(proved) - {g["name"] for g in goals}:
            raise RuntimeError(f"Unknown source goal for {family}")
        tracked = subprocess.check_output(["git", "-C", str(bench), "ls-files", "-z", "--", f"benchmark/proof-from-scratch-module/{family}"], text=True).split("\0")
        sources = {rel: sha(bench / rel) for rel in tracked if rel.endswith(".tla")}
        results.append({"source": case, "port": module, "goals": goals, "source_sha256": sources})
    all_goals = [g for result in results for g in result["goals"]]
    counts = {
        "models": len(results), "ported_models": sum(r["port"] is not None for r in results),
        "models_with_proved_goals": sum(any(g["status"] == "proved" for g in r["goals"]) for r in results),
        "models_with_all_goals_proved": sum(all(g["status"] == "proved" for g in r["goals"]) for r in results),
        "models_with_all_goals_resolved": sum(all(g["status"] in {"proved", "refuted"} for g in r["goals"]) for r in results),
        "models_with_all_invariants_proved": sum(all(g["status"] == "proved" for g in r["goals"] if g["kind"] == "invariant") for r in results),
        "goals": len(all_goals), "proved_goals": sum(g["status"] == "proved" for g in all_goals),
        "invariants": sum(g["kind"] == "invariant" for g in all_goals),
        "proved_invariants": sum(g["kind"] == "invariant" and g["status"] == "proved" for g in all_goals),
        "liveness": sum(g["kind"] == "liveness" for g in all_goals),
        "proved_liveness": sum(g["kind"] == "liveness" and g["status"] == "proved" for g in all_goals),
        "refuted_goals": sum(g["status"] == "refuted" for g in all_goals),
        "source_evaluation_errors": sum(g["status"] == "source_evaluation_error" for g in all_goals),
        "unresolved_goals": sum(g["status"] not in {"proved", "refuted"} for g in all_goals),
    }
    report = {"benchmark_commit": PIN, "recorded_utc": datetime.now(timezone.utc).isoformat(),
              "method": "handwritten tla-rs spec/proof modules; manual source correspondence; no TLA+ transpilation",
              "verus": subprocess.check_output([args.verus, "--version"], text=True).strip(),
              "command": command, "verification_passed": passed, "verified_functions": int(match[1]) if match else None,
              "counts": counts, "proof_sha256": after_proof_hashes, "models": results}
    (args.output / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    rows = ["# Current TLAPS-Bench manual ports", "", f"Pinned benchmark `{PIN}`. {counts['proved_invariants']}/{counts['invariants']} invariants and {counts['proved_liveness']}/{counts['liveness']} liveness goals proved.", "",
            f"{counts['ported_models']}/9 models have handwritten specifications. {counts['models_with_proved_goals']}/9 have at least one proved goal; {counts['models_with_all_goals_proved']}/9 have every benchmark goal proved.", "",
            f"{counts['models_with_all_goals_resolved']}/9 models have every goal either proved or refuted by a checked source counterexample.", "",
            f"Baseline: {report['verified_functions']} verified functions, {'0 errors' if passed else 'verification failed'}, with `--no-cheating`.", "",
            f"{counts['refuted_goals']} goals have checked counterexamples; {counts['unresolved_goals']} remain unresolved. Refuted goals do not count as proved.", "",
            "| Model | Port | Proved invariants | Proved liveness | Refuted |", "|---|---|---:|---:|---:|"]
    for result in results:
        vals = []
        for kind in ["invariant", "liveness"]:
            goals = [g for g in result["goals"] if g["kind"] == kind]
            vals.append(f"{sum(g['status'] == 'proved' for g in goals)}/{len(goals)}")
        vals.append(str(sum(g["status"] == "refuted" for g in result["goals"])))
        rows.append(f"| {result['source'].split('/')[0]} | {result['port'] or 'not ported'} | {' | '.join(vals)} |")
    rows += ["", "[Verification log](verification.log), [per-goal results and source hashes](results.json), [proof scope and correspondence](../../docs/tlaps-bench-manual.md).", "",
             "The etcd `LeaderCompleteness` and `MoreUpToDate` counterexamples are checked in Verus and replayed against the unchanged pinned TLA+ source. [Leader completeness evidence](etcd_counterexample/results.json), [up-to-date log evidence](etcd_uptodate_counterexample/results.json).", "",
             "Four low-level ZooKeeper invariants have [checked counterexamples](zookeeper_counterexample/results.json). Its three remaining goals hit [out-of-domain accesses in the original source](zookeeper_bad_index/results.json). Evaluation errors count as neither proofs nor Boolean invariant violations.", "",
             "Direct-induction probe failures and solver limits leave a goal open. They do not establish a protocol counterexample. Initialization alone does not count as a proved benchmark goal.", "",
             "The baseline checks all imported handwritten proofs with `--no-cheating`. Failed probes are separate files and are excluded from that baseline.", ""]
    (args.output / "README.md").write_text("\n".join(rows))
    if passed:
        record_certificates(report, args.output)
    print(json.dumps(counts, indent=2))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
