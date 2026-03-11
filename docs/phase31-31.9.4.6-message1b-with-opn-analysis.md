# Phase 31.9.4.6 Analysis: `lemma_1bMessageWithOpnImplicationsFor2b`

## Scope
- Target lemma: `src/protocol/RSL/common_proof/message1b.rs::lemma_1bMessageWithOpnImplicationsFor2b`
- Goal: remove `#[verifier(external_body)]` and keep focused verification stable at `--rlimit 40`.
- Size assessment: small (<500 LOC touched), no further TODO decomposition required.

## Design Rationale
- Reuse existing action-origin lemmas (`lemma_ActionThatSends1bIsProcess1a`, `lemma_ActionThatSends2bIsProcess2a`) to keep proof obligations local to this lemma and avoid duplicating environment-level derivations.
- Make each old/new packet combination explicit so the postcondition disjunction is discharged directly in-branch.
- Keep the proof change small and scoped (<500 LOC) to preserve maintainability and make focused verification reproducible.

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
