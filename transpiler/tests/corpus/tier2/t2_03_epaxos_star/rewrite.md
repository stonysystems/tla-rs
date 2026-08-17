# t2_03_epaxos_star — rewrite notes

**Source**: `arxiv:2511.02743v2` `docs/epaxos_reference/EPaxosCommitWithRecovery.tla`
**Pinned commit**: `md5:c96914a9d585e44bffcec9db305fed4f`
**Clean-distance at intake**: 2 — **measured, and checked for the usual failure mode**
**Status**: `intake`. `clean.tla` not yet written; the TODO sections below are live.

> Fill this in while writing `clean.tla`. It is the record of what a human decided,
> and it is what makes the rewrite reviewable. Do not leave TODOs in a case that is
> marked `clean` in the manifest.

## Why this case exists

`t2_02_epaxos` pins `efficient/epaxos@ab4dbea`, and **that specification is
unsafe** — Sutra, *On the correctness of Egalitarian Paxos* (IPL 156:105901,
2020; arXiv `1906.10917`). This case is the corrected protocol, **EPaxos\***
(Ryabinin, Gotsman, Sutra, OPODIS 2025). See `docs/epaxos_reference/README.md`
for the defect, the fix, and the vendoring; `reports/epaxos_spec_gap.md` for the
item-by-item difference from `src/protocol/EPaxos/`.

Upstream is an arXiv ancillary bundle rather than a git checkout, so
reproducibility is pinned by arXiv id + version + MD5. `intake_case.sh` grew a
`--local` source path for this (Phase 56.2.a); the reproduction command is:

```bash
transpiler/tests/corpus/scripts/intake_case.sh \
  --tier 2 --id t2_03_epaxos_star \
  --local     docs/epaxos_reference/EPaxosCommitWithRecovery.tla \
  --aux-local docs/epaxos_reference/ExtraConfiguration.tla \
  --cfg-local docs/epaxos_reference/EPaxosCommitWithRecovery.cfg \
  --source-repo "arxiv:2511.02743v2" \
  --source-commit "md5:c96914a9d585e44bffcec9db305fed4f" \
  --append-manifest
```

## The clean-distance of 2 is a real 2

This corpus has mismeasured this number four times (Jetpack 2→46→15→22, EPaxos
1→3→5→6), every time in the same direction: a linter that cannot identify the
node set returns early, reports a small number, and the small number reads as
"nearly clean". So the measurement was checked before it was believed:

| linter output | |
|---|---|
| `rules_executed` | C1, C2, C3, C4, C5 |
| `rules_skipped` | **`[]`** |
| `node_set` | `Proc` |
| `network_variable` | `msgs` |
| per-node variables | 15 |
| global variables | `submitted`, `initCoord` |
| findings | 2 × C1, both on those globals |

Nothing returned early. **EPaxos\* is the cleanest complex spec in this
corpus**: C2 and C4 pass untouched because it is natively message-passing with
one message set, and 15 of its 17 variables are already `[Proc -> [Id -> _]]`.

## Both C1 findings dissolve; neither needs a redesign

Every occurrence was read before this was claimed.

- **`submitted`** — written only in `Submit` (`original.tla:240`), read only as
  the guard `id \notin submitted` (`:239`).
- **`initCoord`** — written only in `Submit` (`:241`); read at `:394`
  (`initCoord[id] \in Q`), `:478` (`initCoord[x[1]] \notin Q`) and `:531`
  (`m2.from = initCoord[id]`). Every read is *"who owns this id"*.

So make the identifier carry its owner: `Id == [owner: Proc, num: 1..MaxNum]` —
which is how upstream writes an instance (`<<cleader, crtInst[cleader]>>`) and
what `t2_02_epaxos/clean.tla` already does. Then `initCoord[id]` is `id.owner`,
a pure function of the id rather than state, and `submitted` becomes a per-node
counter (upstream's `crtInst[cleader]`). The case is C1-clean by construction,
which is why it is tier 2 despite being the largest spec in the corpus.

## Reference TLC status: does not close

Run under the vendored `original.cfg` (`Proc={1,2,3}`, `F=E=1`,
`Cmd=Id={1,2,3}`, `NumberOfRecoveryAttempts=1`), TLC 2.16, 8 workers, 7.2 GB
heap: **38,059,515 states generated / 13,251,622 distinct at depth 13**, queue
10,116,132 and growing, **no invariant violation**, killed by disk exhaustion.
The bundled `.cfg` ships with no `CONSTRAINT` and no `VIEW`. Any V2 comparison
needs a bound of our own — in a separate `.cfg`, never by editing
`original.tla`. Tracked as Phase 56.0.e.

## Which variable is the network (C4)

TODO — name the message variable, and the operators used to send/receive it.

## History variables removed (C3)

TODO — list each removed ghost/history variable and why it was safe to drop.

## Instantaneous cross-node reads message-ified (C2)

TODO — for each `x[other]` read: what message now carries that value, who sends it,
and what the receiving action does with it.

## Out-of-subset constructs stripped

TODO — reconfiguration (view/epoch) per Q2, and anything else dropped.

## Semantic-fidelity claim (V2)

TODO — how `clean.tla` was checked against `original.tla` with TLC: config, bounds,
observables compared, result.

## Golden review (before freezing golden.rs)

TODO — what was diffed against `reference.rs` (if any) and what differences were
accepted, with reasons.
