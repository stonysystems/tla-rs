# Phase 31.9.4.8.b decomposition analysis (chosen lemma)

Date: 2026-03-12

## Scope probe result

Target leaf `31.9.4.8.b` was originally: remove `#[verifier(external_body)]` from
`lemma_DecidedOperationWasChosen` and pass focused checks at `--rlimit 40`.

Direct probe command:

```bash
timeout 300s /home/shuai/tools/verus-x86-linux/verus \
  --crate-type=lib src/lib.rs \
  --verify-only-module protocol::RSL::common_proof::chosen \
  --verify-function '*lemma_DecidedOperationWasChosen*' \
  --rlimit 40 --triggers-mode silent
```

Observed result: `function body check: Resource limit (rlimit) exceeded` on
`lemma_DecidedOperationWasChosen`.

A follow-up attempt that extracted a non-recursive `change_step` helper still
hit rlimit at `--rlimit 40`.

## Why decomposition is needed

The failure mode is solver budget, not a single concrete failed assertion.
That means we need a staged proof-shaping approach (smaller proof obligations,
stronger helper contracts) rather than one large remove-external-body edit.

## Completed preparatory step (`31.9.4.8.b.1`)

`collect_2b_messages` was strengthened to provide structured facts that the
chosen-proof step needs:

- packet sequence length relation to recursion cursor,
- index range facts for returned quorum indices,
- per-index packet shape/value/ballot/sent-membership facts,
- witness extraction aligned to pre-state learner facts (`i - 1`) plus
  `lemma_PacketStaysInSentPackets` to transfer sent-membership to step `i`.

Focused validation:

```bash
timeout 300s /home/shuai/tools/verus-x86-linux/verus \
  --crate-type=lib src/lib.rs \
  --verify-only-module protocol::RSL::common_proof::chosen \
  --verify-function '*collect_2b_messages*' \
  --rlimit 40 --triggers-mode silent
# => 1 verified, 0 errors
```

And module baseline stability:

```bash
timeout 300s /home/shuai/tools/verus-x86-linux/verus \
  --crate-type=lib src/lib.rs \
  --verify-only-module protocol::RSL::common_proof::chosen \
  --rlimit 40 --triggers-mode silent
# => 4 verified, 0 errors
```

`lemma_DecidedOperationWasChosen` remains external in this step to avoid a
regression while staging the remaining proof work.

## Remaining substeps

- `31.9.4.8.b.2`: prove non-recursive change-step helper at `--rlimit 40`.
- `31.9.4.8.b.3`: remove external-body from recursive
  `lemma_DecidedOperationWasChosen` and close focused checks.
