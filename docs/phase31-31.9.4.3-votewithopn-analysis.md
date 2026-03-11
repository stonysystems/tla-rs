# Phase 31.9.4.3 Analysis: `lemma_VoteWithOpnImplies2aSent`

## Scope
- Target lemma: `src/protocol/RSL/common_proof/message2b.rs::lemma_VoteWithOpnImplies2aSent`
- Goal: remove `#[verifier(external_body)]` and pass focused verification at `--rlimit 40`.
- Edit size: small (<500 LOC touched), no additional TODO decomposition required.

## Focused Command
- `timeout 300s /home/shuai/tools/verus-x86-linux/verus --crate-type=lib src/lib.rs --verify-only-module protocol::RSL::common_proof::message2b --verify-function '*lemma_VoteWithOpnImplies2aSent*' --rlimit 40`

## Attempt Log
1. Removed `external_body` and kept the original duplicated inductive/case-split body.
- Result: `function body check: Resource limit (rlimit) exceeded` at `--rlimit 40`.

2. Replaced the duplicated body with a direct call to the canonical vote-causality proof:
- `lemma_Find2aThatCausedVote(b, c, i, idx, opn)`
- This keeps the same postconditions while avoiding a second copy of heavy solver obligations in `message2b.rs`.
- Result: focused verification passed (`1 verified, 0 errors`) at `--rlimit 40`.

## Rationale
- `lemma_VoteWithOpnImplies2aSent` and `lemma_Find2aThatCausedVote` share the same operational claim shape.
- Using the canonical lemma as the message2b-side wrapper removes one `external_body` immediately and avoids repeated solver-heavy proof structure.
- The deeper branch-heavy proof internals remain tracked under later message2a leaves (`31.9.4.7`).
