# Phase 31.9.4.2 Analysis: `lemma_GetSent2bMessageFromLearnerState`

## Scope
- Target lemma: `src/protocol/RSL/common_proof/learner_state.rs::lemma_GetSent2bMessageFromLearnerState`
- Goal: remove `#[verifier(external_body)]` and keep focused verification stable at `--rlimit 40`.
- Expected edit size remains small (<500 LOC), but direct one-shot proof is currently solver-fragile.

## Reference
- Dafny counterpart:
  - `/tmp/ironclad.WGce4j/ironfleet/src/Dafny/Distributed/Protocol/RSL/CommonProof/LearnerState.i.dfy`
  - lines around `lemma_GetSent2bMessageFromLearnerState` (106-177).

## Reproduction Commands
- Focused command used in all attempts:
  - `timeout 300s /home/shuai/tools/verus-x86-linux/verus --crate-type=lib src/lib.rs --verify-only-module protocol::RSL::common_proof::learner_state --verify-function '*lemma_GetSent2bMessageFromLearnerState*' --rlimit 40`

## Attempt Outcomes
1. Remove `external_body` only:
- Verus fails final-return postcondition in `learner_state.rs`.

2. Add target assertions to isolate first missing obligation:
- Concrete failure:
  - `assert(b[i].environment.sentPackets.contains(p))` fails (final branch).

3. Add stronger local provenance/index proof scaffolding:
- `--rlimit 40` becomes `function body check: Resource limit (rlimit) exceeded`.
- `--rlimit 80` did not complete within bounded run (`timeout 360s`).

All temporary code edits were reverted; repository state remains on the prior verified baseline.

## 31.9.4.2.a Completion (2026-03-12)
- Added helper proof in `src/protocol/RSL/common_proof/learner_state.rs`:
  - `lemma_getsent2b_receive_packet_was_sent`
- The helper proves final-branch receive provenance with local:
  - `LEnvironment_PerformIos`
  - `match_ios_recv`
  - `lemma_PacketStaysInSentPackets`
- Wired helper call into `lemma_GetSent2bMessageFromLearnerState` final branch.
- Focused verification passed:
  - `timeout 300s /home/shuai/tools/verus-x86-linux/verus --crate-type=lib src/lib.rs --verify-only-module protocol::RSL::common_proof::learner_state --verify-function '*lemma_getsent2b_receive_packet_was_sent*' --rlimit 40`
  - Result: `1 verified, 0 errors`.

## 31.9.4.2.b Completion (2026-03-12)
- Added helper proof in `src/protocol/RSL/common_proof/learner_state.rs`:
  - `lemma_getsent2b_sender_index_witness`
- The helper discharges sender-index obligations with local facts:
  - `lemma_Received2bMessageSendersAlwaysValidReplicas`
  - `lemma_FindIndexInSeq`
  - direct transfer from `p.src == sender`
- Wired helper call into `lemma_GetSent2bMessageFromLearnerState` final branch before `GetReplicaIndex`.
- Focused verification passed:
  - `timeout 300s /home/shuai/tools/verus-x86-linux/verus --crate-type=lib src/lib.rs --verify-only-module protocol::RSL::common_proof::learner_state --verify-function '*lemma_getsent2b_sender_index_witness*' --rlimit 40`
  - Result: `1 verified, 0 errors`.

## 31.9.4.2.c Completion (2026-03-12)
- Added helper proofs in `src/protocol/RSL/common_proof/learner_state.rs`:
  - `lemma_getsent2b_message_shape_from_learner_process2b`
  - `lemma_getsent2b_message_shape_from_receive`
- Approach:
  - first derive `LLearnerProcess2b` for the final-branch receive packet from local scheduler/replica transition facts;
  - then perform explicit `LLearnerProcess2b` branch analysis and rule out stutter branches by contradiction with final-branch negated recursion guards.
- Resulting obligations discharged in the final branch:
  - `p.msg->opn_2b == opn`
  - `p.msg->bal_2b == s_prime.max_ballot_seen`
- Focused verification passed:
  - `timeout 300s /home/shuai/tools/verus-x86-linux/verus --crate-type=lib src/lib.rs --verify-only-module protocol::RSL::common_proof::learner_state --verify-function '*lemma_getsent2b_message_shape_from_learner_process2b*' --rlimit 40`
  - Result: `1 verified, 0 errors`.

## 31.9.4.2.d Completion (2026-03-12)
- Plan:
  - integrate 2.a/2.b/2.c helper obligations directly in the final branch;
  - keep recursion stable by using lexicographic decreases for the main/helper proof cycle;
  - isolate the expensive value-mismatch contradiction into a dedicated helper.
- Implementation in `src/protocol/RSL/common_proof/learner_state.rs`:
  - removed `#[verifier(external_body)]` from `lemma_GetSent2bMessageFromLearnerState`;
  - added `lemma_getsent2b_value_matches_candidate` and called it from the final branch;
  - added decreases pair to break recursion-cycle ambiguity:
    - `lemma_GetSent2bMessageFromLearnerState`: `decreases i, 1int`
    - `lemma_getsent2b_value_matches_candidate`: `decreases i, 0int`
  - strengthened `lemma_getsent2b_message_shape_from_receive` ensures to return the needed `LLearnerProcess2b(...)` fact and reuse it in the final-branch value proof.
- Focused verification passed:
  - `timeout 300s /home/shuai/tools/verus-x86-linux/verus --crate-type=lib src/lib.rs --verify-only-module protocol::RSL::common_proof::learner_state --verify-function '*lemma_GetSent2bMessageFromLearnerState*' --rlimit 40`
  - Result: `1 verified, 0 errors`.

## Decomposition Rationale
To avoid broad proof context blow-up, split the work into small proof obligations:
- 31.9.4.2.a: final-branch receive provenance + sentPackets transfer.
- 31.9.4.2.b: sender index witness obligations.
- 31.9.4.2.c: opn/bal equalities via explicit `LLearnerProcess2b` branch split.
- 31.9.4.2.d: integrate and re-run focused check at `--rlimit 40` (completed 2026-03-12).
