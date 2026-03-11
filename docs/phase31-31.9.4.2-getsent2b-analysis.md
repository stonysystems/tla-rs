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

## Decomposition Rationale
To avoid broad proof context blow-up, split the work into small proof obligations:
- 31.9.4.2.a: final-branch receive provenance + sentPackets transfer.
- 31.9.4.2.b: sender index witness obligations.
- 31.9.4.2.c: opn/bal equalities via explicit `LLearnerProcess2b` branch split.
- 31.9.4.2.d: integrate and re-run focused check at `--rlimit 40`.
