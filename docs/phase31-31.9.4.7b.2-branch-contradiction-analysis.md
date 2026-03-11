# Phase 31.9.4.7.b.2 — Find2a branch contradiction replacement

## Context
`lemma_Find2aThatCausedVote` still has `#[verifier(external_body)]` until leaf `31.9.4.7.b.3`, but two local branch placeholders used `assert(false)` and needed to be replaced by explicit proof structure:

- `nextActionIndex == 4` (spontaneous truncate-log path)
- `nextActionIndex == 0 && p.msg is RslMessage1b` (process-1b path)

Both branches are in the case where `!s.votes.contains_key(opn)` but `s_.votes.contains_key(opn)`.

## Design rationale
The replacement keeps branch reasoning local and aligned with the model semantics.

1. Spontaneous truncate path (`nextActionIndex == 4`):
- derive `LReplicaNoReceiveNext` and `LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints`
- extract witness for truncate opn and split:
  - `LAcceptorTruncateLog(s, s_, truncate_opn)`
  - or `s_ == s`
- in truncate branch, apply `lemma_find2a_truncate_log_preserves_vote_if_retained`
- in either split, derive `s.votes.contains_key(opn)`, contradicting the enclosing `!s.votes.contains_key(opn)` branch assumption

2. Process-1b path (`nextActionIndex == 0 && p.msg is RslMessage1b`):
- derive scheduler/process facts to reach `LReplicaNextProcess1b`
- obtain `LAcceptorTruncateLog(s, s_, p.msg->log_truncation_point)`
- apply `lemma_find2a_truncate_log_preserves_vote_if_retained`
- derive `s.votes.contains_key(opn)` contradiction with enclosing branch assumption

This removes trust-heavy placeholders and prepares the function body for `31.9.4.7.b.3` external-body removal.

## Focused check
The target lemma remains external in this leaf, so this run is a structural parse/type check for the edited body:

```bash
timeout 240s /home/shuai/tools/verus-x86-linux/verus --crate-type=lib src/lib.rs \
  --verify-only-module protocol::RSL::common_proof::message2a \
  --verify-function '*lemma_Find2aThatCausedVote*' \
  --rlimit 40
```

Result:
- `0 verified, 0 errors` (warnings only), expected while `#[verifier(external_body)]` remains.
