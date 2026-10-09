# Raft joint-consensus safety: proof structure

Branch: `raft/honest-model`. Status: proved. `lemma_refinement_correct` and
`lemma_committed_histories_are_safe` hold for every `RaftDistributedNext`
behavior, including membership changes. `lift.rs` defines the raw protocol
(`IsValidRawBehavior`, no proof-only state) and proves that each of its
behaviors is a proof-model behavior with the same protocol state
(`lemma_lift_behavior`). The end-to-end theorems over raw behaviors are
`lemma_raw_behaviors_are_safe` and `lemma_raw_refinement_correct`. The
fixed-membership proof in `static_safety.rs` remains as a simpler special
case.

| File | Content |
|------|---------|
| `dynamic_safety.rs` | commit side (section 1) |
| `dynamic_logs.rs` | appended-entry sources, history held, I4, legal configurations |
| `dynamic_winners.rs` | candidate logs, winner records, entry provenance, log matching |
| `dynamic_completeness.rs` | phase progression, winner completeness by term induction |
| `dynamic_election.rs` | history cut, two winners of a term coincide |
| `dynamic_invariant.rs` | `DynamicInvariant`, init, preservation, election safety |
| `lift.rs` | raw protocol, lift theorem, safety and refinement over raw behaviors |

Notation. `H` is `committed_history`. `phase_at(log, k)` is
`active_membership_phase_from_raft_log(log, k, Stable{servers})`, the phase
that governs index `k`. The configuration entries of `H` form the committed
chain `P0 -> P1 -> ...`, where `P(i+1)` sits at history index `c(i+1)`.

## 1. Commit side

The fixed-membership argument carries over almost unchanged.

* Every index `k` is governed by `phase_at(H, k)`. A leader commits the
  interval `[commit, n)` under `phase_at(log, commit)`, and the interval has
  no configuration entry before `n - 1`. So each index in it is governed by
  the leader's active phase.
* By induction over the interval, the leader's log agrees with `H` below `k`,
  so the leader's phase for `k` equals the phase recorded in an existing
  certificate for `k`.
* Two quorums of one phase intersect (`lemma_phase_quorums_intersect`). The
  common server holds the certificate's entry (certificate quorum invariant)
  and the leader's entry (`MatchIndexImpliesLogAgreement`), so they are equal.
* Follower commits follow certified `AppendEntries` advertisements, exactly
  as in the static proof.

Invariants: certificates held by a quorum of their governing phase,
`governing_phase == phase_at(H, k)`, AppendEntries commit advertisements
certified, `MatchIndexImpliesLogAgreement` (needs `LogMatching`).

## 2. Log structure

`LogMatching` needs one winner per term, and that needs the election phases
of two candidates for one term to intersect. All invariants below were
checked on reachable states by the model checker (`raftmc2.py`, guided runs
that commit non-initial configurations).

### Inductive invariants

* **Legal configuration entries.** Every Configuration entry is a legal
  progression from the phase of the log prefix before it.
* **I4.** A Configuration entry followed by another one in the same log is
  committed: it equals `H` at its index. So a log has at most one
  configuration beyond the prefix it shares with `H`. (Leaders propose only
  with no uncommitted configuration; followers copy leader prefixes; `H`
  only grows.)
* **History held.** Some server's log has `H` as a prefix.
* **Winner records.** `election_log_len[(d, t)]` marks `d` as the winner of
  `t`. The winner's log below that length has terms `< t`. Its voters,
  including itself, form a quorum of `phase_at(d.log, len)`, and every other
  voter sent `d` a granted VoteResponse for `t`. The winner never grants
  another server its vote in `t`.
* **Unique winners.** At most one winner per term.
* **Entry provenance.** Every entry of term `t` is held, at the same index,
  by the winner of `t`.
* `LogMatching`, plus the commit-side invariants of section 1.

### Derived in any state (no preservation proof)

* **Strong log matching** follows from entry provenance, unique winners and
  `LogMatching`.
* **Winner completeness**, by induction on terms. The winner of `t` holds
  every `H[k]` with `H[k].term < t`, below its election length.
  - Let `Z` be the history phase at the end of the prefix the election log
    shares with `H`. By I4 and legality, the election phase is `Z` or a
    legal successor of `Z`, so the winner's voters meet any quorum of `Z`.
  - Take the first committed index at or past that shared prefix, either
    `k` itself or an earlier configuration of `H`. Its governing phase is
    `Z`.
  - A voter in the certificate quorum held the entry when it voted, since
    later entries have term `>= t`. The candidate's RequestVote summary is
    at least as up to date.
  - Entry-level completeness for the summary's last entry (a smaller term:
    the induction hypothesis), or strong log matching for an equal term,
    places the entry in the winner's log. This contradicts the choice of
    the shared prefix.
* **Entry-level completeness** for an entry of term `u` follows from winner
  completeness of the winner of `u` and log matching.
* **Election safety** follows from unique winners.

### Preserving unique winners

A candidate that completes a quorum in term `t`, and an existing winner of
`t`, would both satisfy winner completeness. So their shared prefixes with
`H` end in the same history phase, and their election phases intersect.
A common voter would have voted twice in `t`, or a winner would have voted
for another server.

Known liveness issue (not a safety problem): a leader change while a
configuration entry is uncommitted can stall commitment.
