# Raft model recovery proof

The Raft behavior model permits arbitrary reboots between protocol steps.
`LReboot` preserves `current_term`, `has_voted`, `voted_for`, and the complete
log. It resets the role to follower, the commit index to zero, collected votes
and replication maps to empty, and the election membership phase to `None`.
`RaftDistributedReboot` preserves every other node, the network, and ghost
history. Packets sent before a reboot can still be delivered afterward.

`RaftDistributedNext` is the disjunction of `RaftDistributedNormalNext` and a
reboot of any node. `IsValidRaftBehavior` uses this extended relation, so the
existing `lemma_refinement_correct` theorem now quantifies over executions
containing reboots. `LNext` remains the executable protocol relation;
`LNextWithReboot` is its model-level extension. Both reboot-related functions
are excluded from executable generation in `raft_transpile.toml`.

This proves safety of the existing Raft model under ideal persistence. Durable
fields are assumed to survive unchanged. The result does not establish disk
write ordering, storage recovery, application execution, or eventual progress.
For safety, an unscheduled node represents downtime; a separate down/up state
is unnecessary. Existing normal-action and certificate constraints are retained.

The old refinement map used the maximum current `commit_index`. Rebooting every
node would make that map return an empty log, even though previously committed
entries remain in durable logs. The new ghost `committed_history` records the
longest prefix ever observed committed. A normal step deterministically records
its stepping node's committed prefix when that prefix is longer; otherwise it
retains the history. Reboot always preserves it. No prefix-agreement condition
is added as a transition guard: agreement is proved using the existing immutable
commit certificates.

`CommitHistoryValid` connects the history to those certificates and bounds each
node's current commit index. `GetCommittedLog` projects values from the history.
`GetApplicationCommittedLog` filters configuration entries from the same history.
The previous views remain available as `GetKnownCommittedLog` and
`GetKnownApplicationCommittedLog`; these describe current volatile knowledge and
can shrink on reboot.

The packet invariant `AppendEntriesCommitHistoryBound` also uses historical
commitment. An old packet's advertised commit index need not be bounded by the
sender's current commit index after the sender reboots.

The proof includes these checks:

- `lemma_reboot_enabled` constructs a reboot for every well-formed node, with
  no invariant or role restriction as an enabling guard.
- `lemma_reboot_preserves_invariant` preserves the existing safety invariant
  and the new history invariant.
- `lemma_reboot_is_abstract_stutter` preserves the abstract committed log.
- `lemma_whole_cluster_reboot_preserves_commitment` resets every local commit
  index while retaining the historical committed log and safety invariant.
- `lemma_committed_entry_survives_reboots` and
  `lemma_commits_at_different_times_agree` connect actual node commitments at
  different points in an execution, including executions with reboots.
- `lemma_reboot_is_idempotent` checks repeated reset of the same node.

The proof helpers are in `src/protocol/Raft/refinement_proof/recovery.rs`.
Normal-step lemmas still require `RaftDistributedNormalNext`; behavior induction
handles both normal steps and reboots. The quantified leader-completeness helper
uses an explicit trigger matching its invariant to avoid excessive solver
instantiation; its requirements and conclusion are unchanged.

To verify all Raft modules with the repository's pinned Verus version,
`0.2026.08.02.b677dd5`, run from the repository root:

```bash
VERUS_PATH=/path/to/verus
raft_modules=(membership raft raft_refinement types)
for part in committed induction invariants message_invariants reconfiguration recovery refinement state_machine; do
    raft_modules+=("refinement_proof::$part")
done
raft_args=()
for module in "${raft_modules[@]}"; do
    raft_args+=(--verify-only-module "protocol::Raft::$module")
done
"$VERUS_PATH" --crate-type=lib src/lib.rs "${raft_args[@]}" \
    --rlimit 220 --num-threads 8 --triggers-mode silent
```

This command passes with **354 verified, 0 errors**. The recovery proof adds no
`assume`, `admit`, or trusted proof bodies. Building the transpiler and generating
Raft actions from the original and updated specifications produces identical
executable output.
