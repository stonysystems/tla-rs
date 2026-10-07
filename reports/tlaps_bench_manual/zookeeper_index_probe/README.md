# ZooKeeper index diagnostics

These candidate proof modules are excluded from the verified protocol modules.
They try to establish committed and snapshot indices within each retained
history, then derive Integrity and GlobalPrimaryOrder from existing provenance
and ordering lemmas. The combined attempt reported 16 successful function
checks and one failed preservation obligation in `mode_node`. It does not
establish either benchmark goal.

The snapshot-receive preservation claim is false. The subsequent exact source
replay in [zookeeper_bad_index](../zookeeper_bad_index/README.md) reaches saved
snapshot index 4 after installing a three-entry history. These files preserve
the attempted strengthening and the verifier diagnostic. They are not imported
by the passing proof suite and are not counted in coverage.

A second diagnostic unfolds each original goal at the specific extracted bad
state. All three fail their postconditions without a solver-resource failure.
`concrete_goals.rs` and `concrete-goals.log` preserve that check. These failed
proof attempts are not treated as Verus theorems of negated goals; the source
evaluation errors and the separate reachable-index certificate are the evidence.

`undefined_dependencies.rs` checks what the original goals require of the
missing fourth entry. Its three conditional lemmas pass Verus with
`--no-cheating`, 3 verified and 0 errors. They use the states from the separately
verified 197-transition reachability certificate.

| Original goal | Checked conditional consequence |
|---|---|
| `Integrity` at state 197 | If the goal holds, the missing entry has value 0, the only value in the recorded proposals. |
| `GlobalPrimaryOrder` at state 191 | If the goal holds, the missing entry has an epoch of at least 4. The second stored entry already has epoch 4. |
| `LocalPrimaryOrder` at state 191 | If the missing entry has transaction identifier `(1, 2)` and value 0, the goal fails. The same leader proposed `(1, 1)` first, but no earlier position in this history contains it. |

States are numbered from zero. In all three checks the history has length 3,
and the original predicate quantifies through committed index 4. The checked
implications constrain Verus's unspecified value for that out-of-range access.
They do not establish that it has any particular value. None proves or refutes
an original benchmark goal, and none contributes to the benchmark score.
TLC reports an evaluation error for the corresponding original source access.

Reproduce the conditional checks after a successful complete proof-suite run:

```bash
python3 scripts/probe_tlaps_bench_zookeeper_undefined.py --verus /path/to/verus
```

The script checks that the imported proof files match the complete run before
checking the three lemmas. It records the inputs, command, and results in
`undefined-dependencies-results.json`, with output in
`undefined-dependencies.log`. The complete proof suite remains at 2074 verified
functions and 0 errors. This separate diagnostic run does not change that total.
