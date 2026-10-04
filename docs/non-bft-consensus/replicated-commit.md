# Replicated Commit decision safety

Verus proves atomic-commit agreement and preparation validity for one
transaction. Higher-ballot recovery preserves decisions in an explicitly
completed recovery variant. The source is
[Low-Latency Multi-Datacenter Databases using Replicated Commit, VLDB 2013](https://www.vldb.org/pvldb/vol6/p661-mahmoud.pdf),
Section 3.2 and Algorithm 1.

[commit.rs](../../src/protocol/ReplicatedCommit/commit.rs) models the unique
initial client, one Paxos instance, datacenter coordinators, durable prepared
cohorts, learned decisions and cohort application events.

| Source rule | Model action |
|---|---|
| Unique client proposes commit, omitting initial Phase 1 | `InitialCommit`, sole owner of ballot zero |
| Each local cohort durably prepares | `Prepare` |
| Datacenter accepts after all its cohorts prepare | `Accept` with `prepared_dc` |
| Learn a quorum decision | `Learn` |
| Apply the learned decision locally | `Apply`; commit requires that cohort's preparation |

`atomic_commit_agreement` proves that outcomes applied at any datacenters or
cohorts, at any two positions in a finite execution, agree on commit or abort.
`commit_requires_prepared_quorum` proves commit requires a quorum of
datacenters to prepare every local cohort. `decision_persists` proves stability
through recovery. `atomic_decision_refinement` maps the state to an initially
empty, single-assignment commit/abort decision and proves learned replies
match it.

The initial proposal path maps to Algorithm 1. The paper invokes Paxos but
does not give detailed coordinator-recovery pseudocode. This model's `Recover`
action is a classic-Paxos completion: promise a fresh higher ballot, adopt the
highest accepted decision, and choose abort after an empty prepare quorum.
It is identified as that variant, not a verified implementation of recovery
pseudocode from the paper. Phase 1 collection is atomic; accept delivery and
local preparation are individual actions.

The decision object has a linearization point at the first quorum choice.
This is atomic-decision refinement, not multi-transaction data linearizability
or the paper's one-copy serializability claim. Lock conflicts, read-set
validation, read versions, concurrent transactions and database updates are
outside this model. Preparation is durable; transaction and ballot ownership
are unique; faults are crashes. Liveness is excluded.

`replicated_commit_recovers_chosen_commit` in
[the execution witnesses](../../src/protocol/next_five_witnesses.rs) constructs
a prepared, chosen and applied commit followed by higher-ballot recovery and
another acceptance of that decision. See
[verification metadata](next-five-verification.json) for digests and commands.
