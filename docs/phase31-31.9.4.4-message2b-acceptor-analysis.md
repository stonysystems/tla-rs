# Phase 31.9.4.4 Analysis: `lemma_2bMessageImplicationsForCAcceptor`

## Scope
- Target lemma: `src/protocol/RSL/common_proof/message2b.rs::lemma_2bMessageImplicationsForCAcceptor`
- Goal: remove `#[verifier(external_body)]` and keep focused verification stable at `--rlimit 40`.
- Expected size: small (<500 LOC touched), no nested decomposition required.

## Plan
1. Remove `#[verifier(external_body)]` from the lemma.
2. Run focused verification at `--rlimit 40`.
3. If needed, only refactor branch-local assertions for the old-packet and new-packet paths.

## Result
- Existing proof body already discharges both required branches (`old packet` recursive path and `new packet` Process2a path) once the stub annotation is removed.
- No further proof refactor was required.

Focused command:
- `timeout 300s /home/shuai/tools/verus-x86-linux/verus --crate-type=lib src/lib.rs --verify-only-module protocol::RSL::common_proof::message2b --verify-function '*lemma_2bMessageImplicationsForCAcceptor*' --rlimit 40`

Focused result:
- `1 verified, 0 errors`.
