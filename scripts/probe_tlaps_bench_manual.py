#!/usr/bin/env python3
"""Try direct induction for the open safety goals in the handwritten ports.

Passing a probe is a proof candidate, not automatically a benchmark certificate.
The checked infinite-behavior theorems live in src/protocol/TLAPSBench.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import json
import os
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
CASES = {
    "mongodb": {
        "proof": "mongodb_proof", "base": "model::single_write_per_key(s,c)",
        "init_args": ",catalog:IMap<int,int>", "init_req": ",model::valid_catalog(c,catalog)", "initial": "model::initial(c,catalog)",
        "reveal": "reveal(model::enabled); reveal(model::apply);", "preserve": "",
        "step_req": ",model::single_write_per_key(model::apply(s,c,a),c)",
        "init_body": "proofs::initial_snapshot_isolation(c,catalog);",
        "goals": {"SnapshotIsolationCorrect": "model::snapshot_isolation(S,c)"},
    },
    "cahill": {
        "proof": "cahill_proof", "base": "true", "init_args": "", "init_req": "", "initial": "model::initial(c)",
        "reveal": "reveal(model::enabled); reveal(model::apply); reveal(model::commit); reveal(model::read); reveal(model::acquire);", "preserve": "",
        "goals": {"CahillSerializableCorrect": "model::serializable(S,c)"},
        "init_body": "proofs::initial_serializable(c);",
    },
    "zab": {
        "proof": "zab_proof", "base": "true", "init_args": "", "init_req": "", "initial": "model::initial(c)",
        "init_body": "proofs::initial_goals(c);",
        "reveal": "reveal(model::enabled); reveal(model::apply);", "preserve": "",
        "goals": {"Leadership1": "model::leadership1(S,c)", "Leadership2": "model::leadership2(S,c)",
                  "PrefixConsistency": "model::prefix_consistency(S,c)", "Integrity": "model::integrity(S,c)",
                  "Agreement": "model::agreement(S,c)", "TotalOrder": "model::total_order(S,c)",
                  "LocalPrimaryOrder": "model::local_primary_order(S,c)", "GlobalPrimaryOrder": "model::global_primary_order(S,c)",
                  "PrimaryIntegrity": "model::primary_integrity(S,c)"},
    },
    "open_addressing": {
        "proof": "open_addressing_proof", "base": "proofs::completion_inv(s,c) && model::sorted(s)",
        "init_args": "", "init_req": "", "initial": "model::initial(c)",
        "reveal": "reveal(model::enabled); reveal(model::apply); reveal(model::thread_step);",
        "preserve": "proofs::preserve_completion(s,c,a); proofs::preserve_sorted(s,c,a);",
        "goals": {"Consistent": "model::consistent(S,c)", "Contains": "model::contains_goal(S,c)", "Duplicates": "model::duplicates(S,c)"},
    },
    "flash": {
        "proof": "flash_proof", "base": "proofs::typed(s,c)",
        "init_args": ",home:int,data:int", "init_req": ", c.nodes.contains(home), c.data.contains(data)", "initial": "model::initial(c,home,data)",
        "reveal": "reveal(model::enabled); reveal(model::apply);", "preserve": "proofs::preserve_typed(s,c,a);",
        "goals": {"CacheDataCorrect": "model::cache_data(S,c)", "MemDataCorrect": "model::mem_data(S)",
                  "Lemma_1_Correct": "model::lemma_1(S,c)", "Lemma_2_Correct": "model::lemma_2_3(S,c,false)",
                  "Lemma_3_Correct": "model::lemma_2_3(S,c,true)", "Lemma_4_Correct": "model::lemma_4(S,c)"},
    },
    "etcd": {
        "proof": "etcd_election", "base": "proofs::inductive(s,c)", "init_args": "", "init_req": "", "initial": "model::initial(c)",
        "reveal": "reveal(model::enabled); reveal(model::apply); reveal(model::receive_enabled); reveal(model::receive);",
        "preserve": "proofs::preserve_inductive(s,c,a);",
        "goals": {"LogInv": "model::log_inv(S,c)", "CommittedIsDurable": "model::committed_is_durable(S,c)",
                  "ElectionSafety": "model::election_safety(S,c)", "LeaderCompleteness": "model::leader_completeness(S,c)",
                  "LogMatching": "model::log_matching(S,c)", "MoreUpToDate": "model::more_up_to_date(S,c)", "QuorumLog": "model::quorum_log(S,c)"},
    },
    "hashicorp": {
        "proof": "hashicorp_config", "base": "proofs::inductive(s,c)", "init_args": "", "init_req": "", "initial": "model::initial(c)",
        "reveal": "reveal(model::enabled); reveal(model::protocol_apply); reveal(model::receive_enabled); reveal(model::receive);",
        "preserve": "proofs::preserve_inductive(s,c,a);",
        "goals": {"LeaderCompletenessCorrect": "model::leader_completeness(S)", "StateMachineSafetyCorrect": "model::state_machine_safety(S)",
                  "CommittedEntriesPreservedCorrect": "model::committed_preserved(S)", "LogMatchingCorrect": "model::log_matching(S,c)",
                  "ElectionSafetyCorrect": "model::election_safety(S)"},
    },
}
CASES["zookeeper"] = {
    **CASES["zab"], "proof": "zookeeper_proof",
    "reveal": "reveal(model::enabled); reveal(model::apply); reveal(TLAPSBench::zk_election::apply);",
}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--verus", default=os.environ.get("VERUS_PATH", "verus"))
    ap.add_argument("--output", type=Path, default=ROOT / "reports/tlaps_bench_manual/probes")
    ap.add_argument("--timeout", type=int, default=60)
    args = ap.parse_args()
    args.output = args.output.resolve()
    args.output.mkdir(parents=True, exist_ok=True)

    def check(item):
        module, goal, predicate, case = item
        name = module + "_" + goal
        path = args.output / (name + ".rs")
        target = lambda state: predicate.replace("S", state)
        include = os.path.relpath(ROOT / "src/protocol/TLAPSBench/mod.rs", args.output)
        path.write_text(f'''// Generated induction probe. Not part of the successful proof harness.
#![allow(non_snake_case)]
#[path={json.dumps(include)}] pub mod TLAPSBench;
use vstd::prelude::*;
use TLAPSBench::{module} as model;
use TLAPSBench::{case['proof']} as proofs;
verus! {{
proof fn init(c:model::Constants{case['init_args']})
    requires model::valid_constants(c){case['init_req']}
    ensures {target(case['initial'])}
{{ {case.get('init_body', '')} }}
proof fn preserve(s:model::LState,c:model::Constants,a:model::Action)
    requires model::valid_constants(c), {case['base']}, {target('s')}, model::enabled(s,c,a){case.get('step_req', '')}
    ensures {target('model::apply(s,c,a)')}
{{ {case['reveal']} {case['preserve']} }}
}}
''')
        command = [args.verus, "--crate-type=lib", "--no-cheating", "--verify-root", "--triggers-mode", "silent",
                   "--rlimit", "3", "--multiple-errors", "0", "--num-threads", "1", "-V", "spinoff-all", str(path)]
        try:
            run = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=args.timeout)
            output = run.stdout
            if run.returncode == 0 and re.search(r"verification results:: \d+ verified, 0 errors", output):
                status = "candidate_closed"
            elif re.search(r"error: (postcondition not satisfied|assertion failed|precondition not satisfied)", output):
                status = "induction_not_closed"
            elif "Resource limit" in output:
                status = "solver_limit"
            else:
                status = "probe_error"
            result = {"module": module, "goal": goal, "status": status, "exit_code": run.returncode}
        except subprocess.TimeoutExpired as exc:
            output = exc.stdout.decode() if isinstance(exc.stdout, bytes) else exc.stdout or ""
            result = {"module": module, "goal": goal, "status": "timeout"}
        (args.output / (name + ".log")).write_text(output)
        print(json.dumps(result), flush=True)
        return result

    items = [(module, goal, predicate, case) for module, case in CASES.items() for goal, predicate in case["goals"].items()]
    with ThreadPoolExecutor(max_workers=4) as pool:
        results = list(pool.map(check, items))
    (args.output / "results.json").write_text(json.dumps(results, indent=2) + "\n")
    return int(any(r["status"] == "probe_error" for r in results))


if __name__ == "__main__":
    raise SystemExit(main())
