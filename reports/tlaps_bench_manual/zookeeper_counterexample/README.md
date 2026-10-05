# ZooKeeper low-level source counterexample

The pinned benchmark source has a reachable trace violating four stated safety
goals. Exact TLC replays confirm every state in the extracted trace.
Every transition has a checked Verus proof. The certificate also checks
initialization, all four negated goals, and an infinite stuttering continuation.
Complete-suite results and hashes are recorded in `results.json`.

| Goal | First violating state | Exact source states compared |
|---|---:|---:|
| PrimaryIntegrity | 132 | 133 |
| PrefixConsistency | 135 | 136 |
| Agreement | 163 | 164 |
| TotalOrder | 167 | 168 |

Indices are zero-based. The trace contains 167 protocol transitions after
removing seven stutters used by the search wrapper. All FastLeaderElection
steps remain in the trace.

The source files are byte-identical to commit
`ffa3e31da28f960b70d8c5d44f2735e75d6edcac`. The configuration uses three servers,
`MAXEPOCH = 4`, and request value 0. TLC cannot enumerate the source's fixed
`CHOOSE v \in Nat: TRUE`; the replay config overrides `Value` with `{0}`.
The source uses `Value` only for that choice. Zero is a permitted natural
value. No transition or goal definition is replaced.

The servers are named A, B, and C in descending election-ID order. The Verus
certificate derives those names from the model's own choice-based ranking;
it does not assume a particular outcome of `CHOOSE`.

1. A leads epoch 1 and synchronizes B and C. A appends transaction X, then
   crashes before either follower receives it.
2. B completes discovery for epoch 2, then crashes before synchronizing C.
   B's current epoch has advanced, while its log still contains only bootstrap.
3. A restarts and completes discovery for epoch 3. C receives a snapshot
   containing X and marks it committed. A crashes before C processes NEWLEADER,
   so C's current epoch has not advanced.
4. B restarts and wins the next election using its higher current epoch.
   B's epoch-4 synchronization tells C to truncate to bootstrap. C rejects
   that truncation because it is below C's committed index, retains X, and
   subsequently enters broadcast. B has no X: `PrimaryIntegrity` fails.
5. B proposes Y. C appends it after X, and B commits Y at position 2 while
   C's position 2 remains X: `PrefixConsistency` fails.
6. A rejoins and receives B's snapshot containing Y. A and C now have distinct
   committed transactions at position 2, neither present in the other's
   committed prefix: `Agreement` fails.
7. C processes the commit for Y. Its committed sequence contains X before Y,
   while B's committed sequence contains Y without X: `TotalOrder` fails.

X has transaction ID `(1, 1)` and Y has ID `(4, 1)`. Their values are both 0.
The discrepancy is in transaction identity and history order.

`Replay.tla` invokes the original source actions in the fixed schedule and
also checks the original `Next` relation on every edge. The four
`Replay<Goal>.cfg` files check the original goal definitions independently.
The compressed replay logs preserve each complete source trace.
`source_replay_results.json` records hashes and the state-comparison audit.

`trace.json.gz` is untrusted input to
`scripts/build_tlaps_bench_zookeeper_counterexample.py`. The script emits
ground states and proof obligations against the handwritten tla-rs models.
The certificate verifies every enabled action, every resulting state,
initialization, and an infinite continuation by stuttering. These four goals
count as refuted, not proved, in the main report.
