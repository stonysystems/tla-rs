# Phase 31.9.4.7.c Decomposition and 31.9.4.7.c.1-c.2 Completion

Date: 2026-03-12

## Context

Target task `31.9.4.7.c` is to remove `#[verifier(external_body)]` from:

- `lemma_2aMessagesFromSameBallotAndOperationMatchWithoutLossOfGenerality`

in `src/protocol/RSL/common_proof/message2a.rs`.

## Scope / Feasibility Check

- Code-edit scope remains under 500 LOC.
- Direct focused verification of the full lemma body at `--rlimit 40` is currently solver-bounded:

`timeout 300s /home/shuai/tools/verus-x86-linux/verus --crate-type=lib src/lib.rs --verify-only-module protocol::RSL::common_proof::message2a --verify-function '*lemma_2aMessagesFromSameBallotAndOperationMatchWithoutLossOfGenerality*' --rlimit 40`

Result: `0 verified, 1 errors` with `function body check: Resource limit (rlimit) exceeded`.

## Decomposition

To keep progress auditable and verifier-local, `31.9.4.7.c` was split into:

1. `31.9.4.7.c.1` helper extraction and integration (completed)
2. `31.9.4.7.c.2` further branch-local solver-load reduction for index/disjunction contradiction
3. `31.9.4.7.c.3` final external-body removal + focused checks for both message2a lemmas
   1. `31.9.4.7.c.3.a` old/new contradiction branch helperization (completed)
   2. `31.9.4.7.c.3.b` both-new branch helperization if needed
   3. `31.9.4.7.c.3.c` final no-external focused checks

## Completed in 31.9.4.7.c.1

Added:

- `lemma_2a_packet_sent_by_maybe_nominate_has_state_ballot_and_opn`

This helper proves that if a packet `p` is in non-empty `sent_packets` produced by `LProposerMaybeNominateValueAndSend2a`, then:

- `p.msg is RslMessage2a`
- `p.msg->bal_2a == s.max_ballot_i_sent_1a`
- `p.msg->opn_2a == s.next_operation_number_to_propose`

The helper was then used in the old-packet/new-packet branch of
`lemma_2aMessagesFromSameBallotAndOperationMatchWithoutLossOfGenerality` to remove duplicated
branch-local broadcast witness construction from the main lemma body.

Focused proof check for c.1:

`timeout 240s /home/shuai/tools/verus-x86-linux/verus --crate-type=lib src/lib.rs --verify-only-module protocol::RSL::common_proof::message2a --verify-function '*lemma_2a_packet_sent_by_maybe_nominate_has_state_ballot_and_opn*' --rlimit 40`

Result:

`1 verified, 0 errors`

## Completed in 31.9.4.7.c.2

Added:

- `lemma_2a_ballot_proposer_id_alignment`
- `lemma_2a_disjunction_from_implications_contradicts_prestate`

These helpers split the old-packet/new-packet contradiction branch into two smaller obligations:

1. Proposer-index alignment from ballot proposer-id equality.
2. Final contradiction from the `lemma_2aMessageImplicationsForProposerState` disjunction once
   the new packet has established pre-state ballot/opn equality.

The main lemma branch now calls these helpers instead of carrying all alignment/contradiction
reasoning inline.

Focused proof checks for c.2:

`timeout 240s /home/shuai/tools/verus-x86-linux/verus --crate-type=lib src/lib.rs --verify-only-module protocol::RSL::common_proof::message2a --verify-function '*lemma_2a_ballot_proposer_id_alignment*' --rlimit 40 --triggers-mode silent`

Result:

`1 verified, 0 errors`

`timeout 240s /home/shuai/tools/verus-x86-linux/verus --crate-type=lib src/lib.rs --verify-only-module protocol::RSL::common_proof::message2a --verify-function '*lemma_2a_disjunction_from_implications_contradicts_prestate*' --rlimit 40 --triggers-mode silent`

Result:

`1 verified, 0 errors`

`timeout 240s /home/shuai/tools/verus-x86-linux/verus --crate-type=lib src/lib.rs --verify-only-module protocol::RSL::common_proof::message2a --verify-function '*lemma_2aMessagesFromSameBallotAndOperationMatchWithoutLossOfGenerality*' --rlimit 40 --triggers-mode silent`

Result:

`0 verified, 0 errors` (expected while `31.9.4.7.c.3` keeps the lemma `external_body`)

## Completed in 31.9.4.7.c.3.a

Added:

- `lemma_2a_old_packet_new_packet_same_ballot_opn_is_impossible`

This helper moves the full old-packet/new-packet contradiction path out of
`lemma_2aMessagesFromSameBallotAndOperationMatchWithoutLossOfGenerality`, so the
main lemma now dispatches by branch shape and calls a dedicated contradiction helper for
the impossible old/new case.

Focused proof check for c.3.a:

`timeout 300s /home/shuai/tools/verus-x86-linux/verus --crate-type=lib src/lib.rs --verify-only-module protocol::RSL::common_proof::message2a --verify-function '*lemma_2a_old_packet_new_packet_same_ballot_opn_is_impossible*' --rlimit 40 --triggers-mode silent`

Result:

`1 verified, 0 errors`

## Current c.3 status after c.3.a

Direct no-external attempt for the target lemma at `--rlimit 40` is still solver-bounded:

`timeout 300s /home/shuai/tools/verus-x86-linux/verus --crate-type=lib src/lib.rs --verify-only-module protocol::RSL::common_proof::message2a --verify-function '*lemma_2aMessagesFromSameBallotAndOperationMatchWithoutLossOfGenerality*' --rlimit 40 --triggers-mode silent`

Result:

`0 verified, 1 errors` (`function body check: Resource limit (rlimit) exceeded`)

Because of this, `#[verifier(external_body)]` stays in place for now and the next leaf is
`31.9.4.7.c.3.b`.
