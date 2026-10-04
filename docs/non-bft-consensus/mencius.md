# Mencius: one Coordinated Paxos instance

Mao, Junqueira and Marzullo's [Mencius, OSDI 2008](https://www.usenix.org/legacy/event/osdi08/tech/full_papers/mao/mao.pdf)
describes Coordinated Paxos in Section 4.2. A designated coordinator may propose
a command or skip its turn. Other proposers recover an existing value or
originate a no-op. The coordinator's skip can be learned directly. The
formalization here addresses that instance core, before the paper's
multi-instance scheduling and skip optimizations.

## Model boundary

An acceptor stores a promise, its last accepted ballot and its last accepted
value. The model also records immutable proposal and vote histories for the
safety proof. Ballot 0 belongs to the designated coordinator. A coordinator
proposes at most once in that ballot. Each later ballot has a unique proposal,
corresponding to the unique ownership of Paxos ballot numbers. Integer 0 denotes
no-op; other integers denote commands.

`Config` supplies nonempty acceptors and a nonempty family of nonempty quorums
within that set. Every pair of quorums must intersect. The proof is parametric
in this condition; it does not derive a majority-cardinality theorem. The TLA+
instance uses the three two-element quorums over three acceptors.

| Action | Rule |
|---|---|
| Suggest | Create the coordinator's single ballot-0 proposal |
| Revoke | Obtain a quorum's promises for a higher unused ballot; choose its highest accepted value, or no-op if none exists |
| Accept | Vote for an existing proposal whose ballot is at least the local promise |
| Stutter | Leave persistent state unchanged |

Revoke makes quorum collection and value selection atomic. No explicit prepare
messages or delayed promise replies exist in this model. A message-level
refinement remains necessary to cover all paper executions. Stable acceptor
state survives inactivity; crashes do not erase it. No failure detector accuracy
or eventual delivery assumption is needed for these safety theorems, and no
liveness claim is made.

`learned(s, v)` denotes available decision evidence. Either a quorum has voted
for `v` at one ballot, or the coordinator has proposed no-op and `v` is no-op.
Learner message delivery can be delayed arbitrarily. It cannot create evidence
that does not exist in the histories. There is no action guarded by the desired
agreement theorem.

## Proof structure

For a value `v` and a lower ballot `k`, a blocking quorum consists of acceptors
that either voted for `v` at `k`, or promised above `k` without voting there.
`safe_at(s, b, v)` requires such a quorum for every `0 <= k < b`.

The inductive invariant connects votes to unique proposals, bounds vote ballots
by the acceptor's last ballot and promise, records the last acceptance in the
vote history, and establishes `safe_at` for each proposal. It also establishes
that every non-no-op proposal originates from ballot 0.

Recovery preserves this invariant by selecting the highest accepted ballot in
its quorum. Lower ballots inherit that proposal's blocking quorums. At or above
the selected ballot, the new promises block conflicting lower-ballot votes.
An acceptance cannot invalidate a blocking quorum: if its promise already
excluded a ballot, its acceptance guard prevents voting there later.

For two quorum decisions, intersect the earlier decision's quorum with the
later proposal's blocking quorum. The shared acceptor either demonstrates the
same value or contradicts the purported earlier vote. Direct skip learning is
safe because when ballot 0 contains no-op, the origin invariant rules out every
non-no-op proposal at every ballot.

The checked Verus theorems in
[instance.rs](../../src/protocol/Mencius/instance.rs) include:

- `reachable_inv`: invariant preservation for arbitrary finite behaviors.
- `learned_agreement`: any two decisions justified in the same state agree.
- `learned_persists`: decision evidence persists across arbitrary later steps.
- `behavior_agreement`: decisions at arbitrary positions of one finite behavior agree.
- `learned_coordinator_origin`: a learned command other than no-op came from the coordinator's proposal.

These are proofs about the transition system. They use no `assume`, `admit`, or
trusted external proof bodies. The verifier, its library and solver remain in
the trust boundary. The TLA+ and Verus models are independently written; their
correspondence is not machine-checked.

## Verification

Verus `0.2026.08.02.b677dd5` reports **14 verified, 0 errors**. TLC 2.19 reports
**28,903 generated states, 6,917 distinct states, depth 13**, with no violation
of type correctness, agreement or coordinator origin. Its finite configuration
has three acceptors, ballots 0 through 2, two commands and no-op.

```bash
VERUS_PATH=/path/to/verus TLA2TOOLS=/path/to/tla2tools.jar \
  scripts/verify_consensus_mencius.sh
TLA2TOOLS=/path/to/tla2tools.jar python3 scripts/verify_consensus_mencius_mutants.py
```

The mutation controls require agreement counterexamples when any coordinator
command can be learned unilaterally, or when recovery discards accepted values
and always proposes no-op. Logs and model digests are in
[verification.json](verification.json).

The full-paper proof still needs concurrent instance assignment, ordered or
commutativity-based execution, client deduplication, skip aggregation over FIFO
channels, batched revocation, and liveness under the stated failure-detector
assumptions. This package is not a proof of those mechanisms.
