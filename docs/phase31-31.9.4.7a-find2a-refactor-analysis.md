# Phase 31.9.4.7.a Analysis: `lemma_Find2aThatCausedVote` Refactor

## Scope
- Target file: `src/protocol/RSL/common_proof/message2a.rs`
- Parent task: `31.9.4.7` (remove two remaining `external_body` lemmas in `message2a.rs`)
- This leaf (`31.9.4.7.a`) focuses on solver-load reduction for `lemma_Find2aThatCausedVote` without claiming final external-body removal yet.

## Design Rationale
- The original lemma body coupled recursion, environment receive-provenance, and acceptor state-shape obligations in one VC and repeatedly hit solver pressure.
- Splitting receive-provenance into a dedicated helper (`lemma_find2a_receive_packet_was_sent`) keeps the core recursion branch focused on vote-shape reasoning.
- Using `lemma_PacketStaysInSentPackets` explicitly in the recursive branch makes packet monotonicity proof-local and avoids implicit search.

## Result
- Added helper:
  - `lemma_find2a_receive_packet_was_sent`
- Refactored `lemma_Find2aThatCausedVote` body to call the helper and explicit packet-stays lemma.
- Kept `#[verifier(external_body)]` on `lemma_Find2aThatCausedVote` for now; remaining obligations are tracked in `31.9.4.7.b`.

Focused command (helper):
- `timeout 180s /home/shuai/tools/verus-x86-linux/verus --crate-type=lib src/lib.rs --verify-only-module protocol::RSL::common_proof::message2a --verify-function '*lemma_find2a_receive_packet_was_sent*' --rlimit 40`

Focused result:
- `1 verified, 0 errors`.

Diagnostic command (main lemma with external removed temporarily during analysis):
- `timeout 300s /home/shuai/tools/verus-x86-linux/verus --crate-type=lib src/lib.rs --verify-only-module protocol::RSL::common_proof::message2a --verify-function '*lemma_Find2aThatCausedVote*' --rlimit 40`

Diagnostic outcome:
- `Resource limit (rlimit) exceeded` on `lemma_Find2aThatCausedVote`, motivating the 31.9.4.7 sub-leaf split.
