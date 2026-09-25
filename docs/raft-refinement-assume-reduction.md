# Raft refinement assume-elimination experiment

Date: 2026-08-12

Branch: `codex/raft-refinement-remove-assumes`

## Result

The experiment eliminates all 12 executable `assume` sites from
`src/protocol/Raft/refinement_proof/invariants.rs` without adding
`external_body`, `admit`, or replacement assumptions. There are now no such
trust shortcuts in `src/protocol/Raft/refinement_proof/`.

The first six sites were removed by:

- extracting nested `EntryTermHasVoteQuorum` witnesses in
  `lemma_entry_term_vote_quorum_witness`;
- deriving the common vote destination in the same-term bridge with
  `lemma_ethvq_vote_dest_unique`;
- proving the legacy `StateMachineSafety` induction case from maintained log
  certificates and unique certificate coverage.

The remaining six sites all represented the same strict-term case: a voter
contains committed entry `e` at index `k`, while the candidate's RequestVote
summary has a strictly newer last-log term whose index may be at or before
`k`. Equal-term vote-destination uniqueness and a local LogMatching step alone
cannot provide an anchor at or above `k`.

`lemma_election_quorum_contains_committed_entry` now supplies the missing
term-indexed induction. It intersects the concrete election quorum with the
commit quorum, follows the `EntryTermHasVoteQuorum` certificate for the newer
last-log entry, and recursively proves that the earlier election destination
already contains `e`. Since that destination contains both entries, log-term
monotonicity forces the newer-term anchor to occur at or after `k`, and
LogMatching transfers `e` to the current destination.

`lemma_strict_term_anchor_contains_committed_entry` adapts this result to the
existing anchor-based helpers. Together these lemmas discharge all six former
strict-term assumptions.

## Fixed-majority compatibility boundary

The retired/static LeaderCompleteness chain reasons about
`EntryCommittedAt`, whose quorum is a fixed majority of all servers. A
dynamic-membership certificate is instead authorized by its recorded phase;
such a phase quorum need not be a fixed majority of every server in
`0..num_servers`.

The compatibility predicate
`LegacyCertificatesAreFixedMajorityCommitted` now states this relationship
explicitly for callers of the retired chain. It is required by the legacy
certificate-to-LeaderCompleteness discharge lemmas before they invoke the new
term induction. This is a real semantic precondition, not a replacement proof
assumption: the active dynamic-membership committed-history refinement remains
certificate-based and does not rely on it.

## Verification

Using Verus `0.2026.08.02.b677dd5` with `--rlimit 220` and
`--triggers-mode silent`:

- full `invariants.rs`: `215 verified, 0 errors`;
- full `induction.rs`: `3 verified, 0 errors`;
- full `refinement.rs`: `3 verified, 0 errors`;
- all runs produced no automatic-trigger notes.

Repository searches confirm zero executable `assume` calls under
`src/protocol/Raft/`, and zero `external_body` or `admit` markers under
`src/protocol/Raft/refinement_proof/`.
