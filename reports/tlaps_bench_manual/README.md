# Current TLAPS-Bench manual ports

Pinned benchmark `ffa3e31da28f960b70d8c5d44f2735e75d6edcac`. 38/47 invariants and 9/9 liveness goals proved.

9/9 models have handwritten specifications. 9/9 have at least one proved goal; 7/9 have every benchmark goal proved.

8/9 models have every goal either proved or refuted by a checked source counterexample.

Baseline: 2180 verified functions, 0 errors, with `--no-cheating`.

6 goals have checked counterexamples; 3 remain unresolved. Refuted goals do not count as proved.

| Model | Port | Proved invariants | Proved liveness | Refuted |
|---|---|---:|---:|---:|
| tlaplus_examples_FlashProtocol | flash | 7/7 | 8/8 | 0 |
| ZooKeeper | zab | 9/9 | 0/0 | 0 |
| CahillSSI | cahill | 1/1 | 0/0 | 0 |
| ivy_examples_tlb | tlb | 1/1 | 1/1 | 0 |
| OpenAddressing | open_addressing | 5/5 | 0/0 | 0 |
| etcd_raft | etcd | 6/8 | 0/0 | 2 |
| HashicorpRaft | hashicorp | 6/6 | 0/0 | 0 |
| ZooKeeper_LowLevel | zookeeper | 2/9 | 0/0 | 4 |
| MongoDB | mongodb | 1/1 | 0/0 | 0 |

[Verification log](verification.log), [per-goal results and source hashes](results.json), [proof scope and correspondence](../../docs/tlaps-bench-manual.md).

The etcd `LeaderCompleteness` and `MoreUpToDate` counterexamples are checked in Verus and replayed against the unchanged pinned TLA+ source. [Leader completeness evidence](etcd_counterexample/results.json), [up-to-date log evidence](etcd_uptodate_counterexample/results.json).

Four low-level ZooKeeper invariants have [checked counterexamples](zookeeper_counterexample/results.json). Its three remaining goals hit [out-of-domain accesses in the original source](zookeeper_bad_index/results.json). Evaluation errors count as neither proofs nor Boolean invariant violations.

Direct-induction probe failures and solver limits leave a goal open. They do not establish a protocol counterexample. Initialization alone does not count as a proved benchmark goal.

The baseline checks all imported handwritten proofs with `--no-cheating`. Failed probes are separate files and are excluded from that baseline.
