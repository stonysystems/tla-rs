# Phase 31.9.4.7.b.3: `lemma_Find2aThatCausedVote` External-Body Removal

Date: 2026-03-12

## Scope Check

- Target leaf: `31.9.4.7.b.3`
- Expected edit size: well under 500 LOC
- Actual implementation change: remove `#[verifier(external_body)]` from `lemma_Find2aThatCausedVote` in `src/protocol/RSL/common_proof/message2a.rs`

## Design Rationale

The prior leaves already reduced solver coupling and closed the previously open branch obligations:

- `31.9.4.7.a` extracted receive-provenance proof obligations into `lemma_find2a_receive_packet_was_sent` and made packet monotonicity explicit.
- `31.9.4.7.b.1` introduced `lemma_find2a_truncate_log_preserves_vote_if_retained`.
- `31.9.4.7.b.2` replaced `assert(false)` placeholders in truncate-log and process-1b branches.

Given that structure, the least-risk and most honest completion for `.b.3` is to remove only the trust boundary and verify the same body directly, rather than adding new proof layers.

## Focused Verification

Command:

`timeout 300s /home/shuai/tools/verus-x86-linux/verus --crate-type=lib src/lib.rs --verify-only-module protocol::RSL::common_proof::message2a --verify-function '*lemma_Find2aThatCausedVote*' --rlimit 40`

Result:

`1 verified, 0 errors`
