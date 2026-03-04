# Phase 34.6.2: Raft Log Truncation Model Audit

Date: 2026-03-04

## Scope

This note records the result of TODO item **34.6.2**:
check whether the current Raft spec models follower log truncation/overwrite,
or only append-only follower updates.

## Result

The current spec is **append-only** for follower log updates.
It does **not** currently model overwrite/truncation semantics.

## Evidence

1. In `src/protocol/Raft/raft.rs`, `LHandleAppendEntriesMsg` has an explicit guard:
   - reject when `ae_has_entry && ae_prev_index != s_mid.log.len()`.
   - This permits only appending at the current log end.

2. In `src/protocol/Raft/raft.rs`, `LFollowerAppendEntries` updates log as:
   - `s_.log == (if ae_has_entry { s.log.push(...) } else { s.log })`.
   - No branch performs overwrite, truncate, splice, or replacement.

3. In `src/protocol/Raft/refinement_proof/message_invariants.rs`,
   `LogAppendOnly` and `lemma_log_append_only` encode and prove that logs
   preserve all old entries and only grow by appending.

## Verification run used

Focused proof check executed for append-only step property:

```bash
/home/shuai/tools/verus-x86-linux/verus \
  --crate-type=lib src/lib.rs \
  --verify-only-module protocol::Raft::refinement_proof::message_invariants \
  --verify-function '*log_append_only*' \
  --rlimit 40
```

Outcome: `1 verified, 0 errors` (partial verification mode).

## Implication for Phase 34 proofs

Because overwrite/truncation is not modeled in the current spec,
`LogMatching` for this model does not need the extra
"post-overwrite follower log is prefix of leader log" case split.

If truncation is added later (to match full Raft §5.3 overwrite behavior),
re-open TODO 34.6.2 and add:

- an explicit overwrite transition model,
- a prefix-after-overwrite lemma,
- and corresponding updates to `LogMatching` induction.
