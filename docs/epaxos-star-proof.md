# EPaxos* model safety and recovery proof

The model in [`src/protocol/EPaxos/star/`](../src/protocol/EPaxos/star/)
proves distributed safety for a baseline EPaxos* variant with durable records
and a volatile-state reboot action. It covers arbitrary finite protocol traces,
including interleaved fast and slow decisions, recovery, message replay, and
reboots. All model and proof modules pass together with **139 verified, 0 errors**.

This is a separate model. The existing simplified EPaxos specification,
generated actions, and executable host are unchanged. The
[audit](epaxos-safety-audit.md) retains checked counterexamples for that model.
Connecting executable code to the corrected specification remains future work.

## Proven properties

The public entry points are in [`safety.rs`](../src/protocol/EPaxos/star/safety.rs)
and [`refinement.rs`](../src/protocol/EPaxos/star/refinement.rs).

| Property | Statement and entry point |
| --- | --- |
| Agreement | Every Commit for one instance has the same payload and dependency set, across all ballots. `lemma_behavior_agreement` |
| Conflict coverage | For two distinct committed commands that conflict, at least one depends on the other. `lemma_behavior_visibility` |
| Compatible execution prefixes | If one replica executes A before conflicting B, including a prefix where B is absent, any replica that executes B must have executed A first. Independent commands can execute in different orders. `lemma_behavior_execution_safety` |
| Validity | A committed command's payload comes from the original submission for its instance. Recovery may instead choose Nop. `lemma_behavior_validity` |
| At-most-once execution | A replica never appends the same instance identity to its execution history twice, including after reboot. `lemma_behavior_at_most_once` |
| Stability | The global committed graph only grows and preserves every existing payload and dependency set. `lemma_behavior_committed_stability` |
| Refinement | The complete protocol trace maps to an abstract committed graph and per-replica execution histories. `theorem_epaxos_star_refinement` |
| Combined safety | Agreement, conflict coverage, execution safety, validity, at-most-once execution, and the abstract history invariant hold at every state of every valid finite trace. `theorem_epaxos_star_safety` |

These results quantify over any number of instances, ballots, messages, and
reboots. They are inductive proofs, not bounded exploration. Agreement also
covers local committed records because each record has a corresponding sent
Commit packet. The network retains sent packets throughout the trace.

The abstract history invariant requires dependency closure. It also requires
deterministic instance ordering inside a strongly connected component. The
execution action appends one ready component atomically. This proof does not
model an application state transition function or prove a concrete client API
linearizable. Command identity is the persistent coordinator/slot pair, so
at-most-once execution does not deduplicate separate client submissions with
identical payloads.

## Recovery and persistence

[`model.rs`](../src/protocol/EPaxos/star/model.rs) defines `reboot` by clearing
the rebooting replica's `attempts` map. The following state survives.

| State | Purpose |
| --- | --- |
| `log[id].promise` | Reject older ballots after restart |
| `log[id].accepted_ballot` | Report the ballot of the accepted attributes during recovery |
| `log[id].phase` and `log[id].attrs` | Retain accepted or committed payloads and dependency sets |
| `log[id].original` and `log[id].initial_deps` | Retain original pre-accept information used by recovery validation |
| `next_slot` | Prevent reuse of an instance identity |
| `executed` | Preserve model-level application execution history and prevent re-execution |

All fields of an attempt are volatile: ballot, stage, candidate, recovery quorum,
and invalidation set. Incoming reply batches represent packets selected for
delivery at that step. Every packet must have been sent, and replies are bound
to sender, destination, instance, ballot, and message kind. A map keyed by sender
prevents counting a duplicate twice. Batches can contain old snapshots.

The reboot action preserves network packets, so pre-reboot requests and replies
remain deliverable. It also preserves `submitted`, a ghost observation of client
submissions that protocol guards never consult. A new recovery attempt must use
an owned ballot strictly above the durable promise. A cleared attempt cannot
resume an old coordinator round.

Persistence is ideal and atomic at each model action. A crash can occur between
any two actions; an arbitrarily long pause models time spent down. Torn writes,
disk corruption, partial execution of a component, and atomicity between a real
application and its execution record are outside this model. The `executed`
history includes Nop identities for dependency bookkeeping; those identities
represent no application command.

## Algorithm reference and model choices

The reference is the baseline algorithm in section 3 and the safety arguments
in appendix D of [EPaxos*](https://arxiv.org/html/2511.02743v2), also published
as [OPODIS 2025 paper 22](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.OPODIS.2025.22).
The model excludes the highlighted optimized recovery branches and the thrifty
variant. It uses the baseline parameter constraints:

```text
n >= 3
0 <= e <= f
n >= 2*f + 1
n >= 2*e + f + 1
majority quorum size >= n - f
fast quorum size >= n - e
```

Membership and the symmetric command conflict relation are fixed. Processes
follow the protocol, and packets cannot be forged. No fairness or eventual
delivery assumption is needed for safety. The proof places no bound on how
often a replica reboots with its durable state intact.

The model makes these choices explicit:

- Self-delivery of submission, proposal publication, and recovery start is
  atomic. Starting validation also handles the coordinator's own request when
  it belongs to the validation quorum.
- Recovery can start only for an instance in the local log or named by a local
  dependency. It cannot invent an unallocated future client identity. This is
  narrower than the paper. Figure 8 lines 88-94 let `Ω[id]` recover an instance
  on TryRecover, possibly with no local record. The theorem does not cover such
  recoveries. `submit` has no line 12 guard, and the proof relies on this
  restriction to keep it safe; removing it breaks the submission-freshness
  invariant in `identities.rs`. A line 12 guard in `submit`, or an allocation
  guard on recovery, would widen the scope. The allocation guard would make
  `submitted` a protocol input instead of a ghost.
- The coordinator must still hold promise `b` when it finishes validation or
  resolves waiting. It accepts its own proposal atomically. The paper checks the
  ballot only on RecoverOK (line 51), so a preempted coordinator may still send
  Accept at lines 64-75. The theorem does not cover those executions.
- Validate requires both a matching promise and a record that is neither
  accepted nor committed. The additional phase guard prevents a delayed
  duplicate Validate from overwriting an accepted Nop. This is an explicit
  extension for the model's message duplication and reboot semantics.
- ValidateOK is sent to its coordinator. The baseline consumes those replies
  only there, so the model omits the paper's unused broadcast copies.
- Execution uses an atomic ready strongly connected component, ordered by
  instance identity. It does not implement a graph traversal algorithm.

The safety theorem is about these encoded transitions. No machine-checked
translation from the paper or refinement from the executable host is claimed.
Liveness, retry completion, failure detection, quorum latency, and performance
are outside the proof.

## Verification

Use Verus `0.2026.08.02.b677dd5` with its matching Rust toolchain:

```bash
VERUS_PATH=/path/to/verus scripts/verify_epaxos_star.sh
VERUS_PATH=/path/to/verus scripts/verify_epaxos_safety_audit.sh
```

The first script selects every Rust module under `star/`, including every helper
lemma used by the public theorems. Both scripts use four verifier threads and
Verus's default resource limit. The coordinator induction lemma carries a local
resource limit of 40. The audit script checks the original EPaxos modules and counterexamples.
Neither script verifies the whole repository.
Both scripts retain Verus's selective trigger diagnostics. The final runs emit
zero automatic-trigger notes, satisfying the repository's trigger ceiling.

Verified on 2026-09-25 with Verus `0.2026.08.02.b677dd5`:

| Suite | Result |
| --- | --- |
| EPaxos* model, safety, recovery, refinement, and concrete trace | 139 verified, 0 errors |
| Original EPaxos source/generated contracts and safety audit | 27 verified, 0 errors |

A final combined run of both selections also passes, **166 verified, 0 errors**,
with the default command-line resource limit and zero automatic-trigger notes.

No new `assume`, `admit`, axiom, trusted module, or `external_body` is used in
these proofs. They rely on Verus, its SMT solver, and its standard mathematical
library. No generated file was edited.

[`scenarios.rs`](../src/protocol/EPaxos/star/scenarios.rs) also constructs a
ten-state witness with no preconditions. Three replicas fast-commit a command,
the coordinator executes it, reboots, collects recovery responses, and commits
the same attributes at ballot 3. Its durable execution history remains intact.
This checks reachability of a useful path; it is not a liveness theorem.
