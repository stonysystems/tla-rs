# Raft refinement assume-reduction experiment

Date: 2026-08-12

Branch: `codex/raft-refinement-remove-assumes`

## Result

The experiment reduces executable `assume` sites in
`src/protocol/Raft/refinement_proof/invariants.rs` from 12 to 6 without adding
`external_body`, `admit`, or replacement assumptions.

The removed sites were:

- four direct extractions of nested `EntryTermHasVoteQuorum` witnesses;
- one same-term bridge that previously assumed a common vote destination;
- the legacy `StateMachineSafety` induction's newly committed-entry equality.

`lemma_entry_term_vote_quorum_witness` now performs the nested existential
extraction. Callers explicitly require `EntryTermHasVoteQuorum`; previously
several helpers only claimed in comments that the caller had this invariant,
while their signatures did not require it. The same-term bridge now extracts
both vote-quorum certificates and applies `lemma_ethvq_vote_dest_unique`.

The state-machine-safety case now follows the maintained proof architecture:
`CommittedEntriesHaveLogCertificates` is preserved into the post-state, and
unique certificate coverage implies `StateMachineSafety` directly.

## Remaining six sites

All six remaining `assume(false)` sites are instances of the same strict-term
case. A voter contains committed entry `e` at index `k`, but the candidate's
RequestVote summary has a strictly newer last-log term and an index at or before
`k`. Equal-term vote-destination uniqueness and ordinary LogMatching do not
provide an anchor at or above `k`.

Closing this case requires the Raft paper's induction over leader/election term:
the leader that created the newer-term entry must already contain `e`; append-only
log construction then places that newer-term entry after `k`. The existing
helpers recurse over a concrete higher-term log anchor and cannot express this
historical leader fact when that anchor is at or before `k`.

A sound next step is therefore a term-indexed ghost invariant or history
certificate recording the elected leader/log snapshot for every term. Merely
adding another local log lemma, hiding the case behind a stronger `requires`, or
deleting the retired legacy chain would make the source look assumption-free
without completing the missing argument, so this experiment does none of those.

## Verification

Using Verus `0.2026.08.02.b677dd5`:

- full `invariants.rs`: `213 verified, 0 errors`;
- full `induction.rs`: `3 verified, 0 errors`;
- full `refinement.rs`: `3 verified, 0 errors`;
- all runs used `--triggers-mode silent` and produced no automatic-trigger notes.

The maintained certificate-based committed-history refinement remains separate
from the six residual legacy LeaderCompleteness assumptions.
