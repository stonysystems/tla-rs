# Om safety audit

Om has a conditional consensus proof and two formally checked gaps in the
published description. There is no positive linearizability claim for Om here.
The source is [Consistent and Automatic Replica Regeneration, NSDI 2004](https://www.usenix.org/legacy/events/nsdi04/tech/full_papers/yu/yu.pdf),
Sections 3 and 5 and Figures 4 and 5. The author's
[extended paper](https://www.comp.nus.edu.sg/~yuhf/p3-yu.pdf) was also checked.
Section 2.2 explicitly uses linearizability as the consistency definition.
Pinned PDF digests appear in [the verification ledger](next-five-verification.json).

[consensus.rs](../../src/protocol/Om/consensus.rs) records each proposal or
check access, its processing time at each witness, and the quorum of returned
responses. A process sees a proposal only if a returned witness processed
that proposal before producing its response. There is no atomic-snapshot
assumption. Random choices become nondeterministic choices among allowed
observed proposals.

| Source rule | Model |
|---|---|
| Figure 4, write own entry and union returned witness views | `processed`, `quorums`, `sees` |
| Figure 5, proposal snapshot and agree/disagree check | `uniform`, `agrees`, `defined_execution` |
| Decide if no disagree flag appears | `decision` |
| Mixed result, select an agreeing process and read its proposal | Next-round clause in `defined_execution`, with a separate defined-lookup condition |

`agreement` proves that any two decisions, including decisions in different
rounds, have the same value. `decision_validity` proves this value is a process
input. The proof derives one-way visibility from quorum intersection, derives
equal proposals for agreeing processes, and inducts over later rounds.

Both theorems require intersecting returned witness quorums and a defined
lookup whenever the mixed branch advances. Om deliberately uses probabilistic
quorums, so unconditional intersection is not a source guarantee. No probability
bound is proved. Intersection alone also does not ensure the lookup is defined.

## Missing proposal lookup

[`mixed_lookup_can_be_missing`](../../src/protocol/Om/lookup.rs) constructs a
legal history prefix with processes `p`, `u`, `q`, inputs `1`, `2`, `1`, and
intersecting witness quorums `{0,1}` and `{0,2}`.

| Time | Witness event |
|---|---|
| 1 | Witness 1 records `u=2`; `u` has not finished its proposal access. |
| 3, 4 | Witnesses 0 and 1 process `p=1`. Its union includes `u=2`, so `p` disagrees. |
| 7 | Witness 1 processes `p`'s disagree flag. Processing at witness 0 is delayed. |
| 9, 10 | Witnesses 0 and 2 process `q=1`. Its snapshot sees `p=1` and `q=1`, so `q` agrees. |
| 13, 14 | Witnesses 0 and 2 process `q`'s agree flag. `q` sees no disagree and decides `1`. |
| 16 | Witness 0 finally processes `p`'s disagree flag, returning both flags. |

Now `p` has a mixed check result whose agreeing process is `q`. Its earlier
proposal snapshot has no entry for `q`. Figure 5's `prop_view[q]` therefore has
no proposal value. The proof does not assign invented semantics to the missing
entry and does not claim two conflicting decisions occurred. It establishes
that the published pseudocode needs a rule or argument for this case. The
positive agreement theorem covers executions where subsequent lookups are
defined; it does not discharge this obligation.

## Read returns new, then another read returns old

[`reachable_new_old_inversion`](../../src/protocol/Om/read_write.rs) proves an
eleven-transition execution of Section 3's normal-case rules, with two replicas
and initially `x=0`.

1. Invoke `write(1)`, prepare both replicas, then send commits.
2. Deliver commit to A, which applies `1`. Delay delivery to B.
3. A read at A completes with `1`.
4. A later read at B completes with `0`.
5. Deliver commit to B and acknowledge the write.

All operations finish. Both replicas stay in the same configuration with valid
leases. `new_old_inversion_has_no_linearization` proves there is no legal
sequential order. The values require `write < read1` and `read2 < write`, while
real time requires `read1 < read2`.

The source applies a write on receipt of commit and describes reads from a
replica with valid leases. The modeled rules do not block reads on pending
writes. An implementation could add synchronization that excludes this
schedule; that implementation has not been audited. This is a counterexample
to the literal published-rule model, not a confirmed implementation bug.
Lease expiration, regeneration, concurrent reconfiguration and liveness remain
open.
