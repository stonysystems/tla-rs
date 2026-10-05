# Reachable invalid committed index

The unchanged low-level ZooKeeper source reaches a follower with a three-entry
history and committed index 4. The exact source replay checks all 197
transitions and compares all 198 states to the certificate input.

Every transition has a checked Verus proof. The certificate constructs an
infinite behavior reaching the invalid index. This does not add a proved or
refuted benchmark predicate to the score. Complete-suite results and hashes
are recorded in `results.json`.

| Check | State | Original source result |
|---|---:|---|
| Follower committed index within history | 197 | Invariant violation |
| Integrity | 197 | Evaluation error, history entry 4 is outside a three-entry sequence |
| GlobalPrimaryOrder | 191 | Same evaluation error |
| LocalPrimaryOrder | 191 | Same evaluation error |

An evaluation error is distinct from a Boolean invariant violation. These
three benchmark goals remain unproved. The source expressions access a value
outside the history's domain on an actual execution. Assigning a convenient
value to that access or adding a missing transition guard would change the
verification problem.

The trace extends the four-invariant counterexample. A proposes three orphaned
transactions in epoch 1. C later retains them after rejecting B's truncation,
and records snapshot index 4. B's shorter history contains transactions from
epoch 4. After C reconnects, B sends a three-entry snapshot. C replaces its
history and committed index but retains saved snapshot index 4. C crashes and
restarts before NEWLEADER. Restart restores committed index 4 without restoring
a fourth history entry. C then follows B again.

`Replay.tla` fixes the action schedule and checks the unchanged source `Next`
relation on every edge. `FollowingBound` is a diagnostic range predicate;
the three benchmark goal definitions come directly from the pinned source.
The configuration uses three servers, MAXEPOCH 4, and the permitted fixed
request value 0. No action or benchmark goal is replaced.

Reproduce the source audit with:

```bash
python3 scripts/audit_tlaps_bench_zookeeper_counterexample.py --index-failure
```

Generate the untrusted ground states and proof obligations with:

```bash
python3 scripts/build_tlaps_bench_zookeeper_counterexample.py --index-failure
```

The generated certificate proves reachability of the invalid index. It does
not claim that a TLC evaluation error is a Verus proof of a negated benchmark
predicate. Source hashes, replay results, and state comparisons are recorded in
`source_replay_results.json`.
