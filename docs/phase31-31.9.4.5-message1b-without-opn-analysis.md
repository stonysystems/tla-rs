# Phase 31.9.4.5 Analysis: `lemma_1bMessageWithoutOpnImplicationsFor2b`

## Scope
- Target lemma: `src/protocol/RSL/common_proof/message1b.rs::lemma_1bMessageWithoutOpnImplicationsFor2b`
- Goal: remove `#[verifier(external_body)]` and keep focused verification stable at `--rlimit 40`.
- Size assessment: small (<500 LOC touched), so no additional TODO decomposition required.

## Plan
1. Remove `#[verifier(external_body)]` from the lemma.
2. Run focused verification at `--rlimit 40`.
3. If blocked, reduce solver load by replacing local environment-heavy derivations with existing action helper lemmas from `packet_sending.rs`.

## Result
- A direct removal attempt hit `rlimit` at 40 and timed out at higher limits.
- Final proof keeps the same lemma-level structure but uses the existing action lemmas (`lemma_ActionThatSends1bIsProcess1a`, `lemma_ActionThatSends2bIsProcess2a`) for branch reasoning instead of repeating low-level IO/environment reconstruction.
- The contradictory branch where both packets are newly sent in one step is discharged by equating the two `RslNextOneReplica` host-IO witnesses (same source implies same replica index and same `nextStep` host IO sequence).

Focused command:
- `timeout 300s /home/shuai/tools/verus-x86-linux/verus --crate-type=lib src/lib.rs --verify-only-module protocol::RSL::common_proof::message1b --verify-function '*lemma_1bMessageWithoutOpnImplicationsFor2b*' --rlimit 40`

Focused result:
- `1 verified, 0 errors`.
