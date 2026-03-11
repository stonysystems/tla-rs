# Phase 31.9.4.7.b.1 — Find2a truncate-log retention helper

## Context
`lemma_Find2aThatCausedVote` still has `#[verifier(external_body)]` and is blocked by rlimit pressure when verified directly at `--rlimit 40`.
One recurring branch obligation is the contradiction shape:
- pre-state does **not** contain vote key `opn`,
- post-state **does** contain vote key `opn`,
- transition path is via truncation (`LAcceptorTruncateLog`) or 1b-processing path that can include truncation.

The key semantic fact needed is that truncation does not introduce new vote keys; retained keys preserve value.

## Design rationale
Added helper:
- `lemma_find2a_truncate_log_preserves_vote_if_retained(s, s_, truncate_opn, opn)`

Contract:
- requires `LAcceptorTruncateLog(s, s_, truncate_opn)` and `s_.votes.contains_key(opn)`
- ensures `s.votes.contains_key(opn)` and `s_.votes[opn] == s.votes[opn]`

This keeps quantified map reasoning out of the main recursive proof and provides a reusable local fact for both truncate-related branches.

## Solver note
Directly asserting the postcondition from `RemoveVotesBeforeLogTruncationPoint` failed initially due trigger selection on map-index terms.
A stable proof shape was to introduce explicit map-index terms (`s_.votes[opn]`, `s.votes[opn]`) before the final assertion, which gives the solver matching terms for quantifier instantiation.

## Focused verification evidence
Command:

```bash
timeout 240s /home/shuai/tools/verus-x86-linux/verus --crate-type=lib src/lib.rs \
  --verify-only-module protocol::RSL::common_proof::message2a \
  --verify-function '*lemma_find2a_truncate_log_preserves_vote_if_retained*' \
  --rlimit 40
```

Result:
- `1 verified, 0 errors` (warnings only).
