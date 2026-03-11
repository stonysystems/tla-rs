# Phase 31.9.4.6 Analysis: `lemma_1bMessageWithOpnImplicationsFor2b`

## Scope
- Target lemma: `src/protocol/RSL/common_proof/message1b.rs::lemma_1bMessageWithOpnImplicationsFor2b`
- Goal: remove `#[verifier(external_body)]` and keep focused verification stable at `--rlimit 40`.
- Size assessment: small (<500 LOC touched), no further TODO decomposition required.

## Plan
1. Remove `#[verifier(external_body)]` from the lemma.
2. Run focused verification at `--rlimit 40`.
3. If proof obligations fail, rework old/new packet branches to reuse existing `packet_sending` and message implications lemmas instead of duplicating environment-level derivations.

## Result
- Initial direct run after annotation removal exposed an unproven contradiction branch and an uncovered ensures disjunct.
- Final proof uses action-origin lemmas for the new-packet branches and explicitly discharges the ensures disjunction:
  - old-1b/new-2b branch: proves `BalLeq(p_1b.bal_1b, p_2b.bal_2b)`.
  - old-2b/new-1b branch: from `lemma_2bMessageImplicationsForCAcceptor`, proves either exact vote match (equal ballot/value) or strict less-than ballot.
  - both-new branch: contradiction by equating `RslNextOneReplica` host-IO witnesses for same source and deriving impossible receive-message tag clash (`1a` vs `2a`).

Focused command:
- `timeout 300s /home/shuai/tools/verus-x86-linux/verus --crate-type=lib src/lib.rs --verify-only-module protocol::RSL::common_proof::message1b --verify-function '*lemma_1bMessageWithOpnImplicationsFor2b*' --rlimit 40`

Focused result:
- `1 verified, 0 errors`.
