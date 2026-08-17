# EPaxos* reference specification (vendored)

These three files are the **ancillary files** attached to the arXiv version of:

> Fedor Ryabinin, Alexey Gotsman, Pierre Sutra.
> *Making Democracy Work: Fixing and Simplifying Egalitarian Paxos.*
> OPODIS 2025, LIPIcs vol. 360, pp. 22:1–22:19. DOI `10.4230/LIPIcs.OPODIS.2025.22`
> Extended version: arXiv `2511.02743`.

TLA+ author (per the module header): Alexandre SIRET. The module covers the
**commit and recovery protocols — Figures 3 and 5 of the paper**.

| file | lines | what |
|---|---|---|
| `EPaxosCommitWithRecovery.tla` | 616 | the EPaxos\* spec |
| `EPaxosCommitWithRecovery.cfg` | 30 | TLC config: `Proc={1,2,3}`, `F=1`, `E=1`, `Cmd=Id={1,2,3}`, `NumberOfRecoveryAttempts=1`; checks `Agreement`, `Visibility`, `TypeInv` |
| `ExtraConfiguration.tla` | 10 | the conflict relation as a model constant: `ConflictPairs == {<<1,3>>, <<2,3>>}` |

## Provenance

Fetched 2026-08-17 from the arXiv e-print bundle:

```bash
curl -sSL -o eprint.tar.gz https://arxiv.org/e-print/2511.02743
tar xzf eprint.tar.gz anc/
```

(The per-file endpoint `https://arxiv.org/src/2511.02743/anc/<name>` serves the
two `.tla` files but returns HTTP 406 for the `.cfg`; the tarball has all three.
The `.tla` obtained either way is byte-identical.)

MD5, as vendored:

```
99813c86de8c41250595b67dc59ee949  EPaxosCommitWithRecovery.cfg
c96914a9d585e44bffcec9db305fed4f  EPaxosCommitWithRecovery.tla
1a884c5f39b6e491395718eac840b22b  ExtraConfiguration.tla
```

Unmodified copies, kept for reference only — nothing in the build reads them.
LIPIcs papers are published under CC-BY 4.0.

## Why these are here and not `efficient/epaxos`

The corpus case `transpiler/tests/corpus/tier2/t2_02_epaxos` pins upstream
`efficient/epaxos` at `ab4dbeae58a7eabcb514865e9ccf1ab0386abfc3`. **That
specification is known to be unsafe.**

Pierre Sutra, *On the correctness of Egalitarian Paxos* (Information Processing
Letters 156:105901, 2020; arXiv `1906.10917`) exhibits an admissible execution in
which replicas disagree on a command's dependencies. The counterexample is a
TLA+ module extending `EgalitarianPaxos`, published at
<https://github.com/otrack/on-epaxos-correctness>.

The defect is visible directly in the pinned file. `ReplyPrepare`
(`original.tla:418-424`) writes the *promise* ballot over the record's single
`ballot` field:

```tla
cmdLog' = [cmdLog EXCEPT ![replica] = (@ \ {rec}) \cup
     {[inst |-> rec.inst, status |-> rec.status,
       ballot |-> msg.ballot,          \* the accept-ballot is lost here
       cmd |-> rec.cmd, deps |-> rec.deps, seq |-> rec.seq]}]
```

so a later `prepare-reply` reports `prev_ballot` = an earlier *promise* rather
than the ballot at which `(cmd, deps, seq)` was *accepted* — and
`PrepareFinalize` (`original.tla:475-477`) selects the accepted record by
maximum `prev_ballot[1]`. Sutra's fix, in the artifact's own words: *"Each
process needs to maintain the last ballot at which it voted. This requires an
additional ballot variable in the algorithm."*

EPaxos\* is that fix, carried through: `bal[p][id]` (current/promised) and
`abal[p][id]` (last ballot at which a slow-path value was accepted). The whole
discipline is three lines of this spec:

| `EPaxosCommitWithRecovery.tla` | writes `bal` | writes `abal` |
|---|---|---|
| `ApplyAccept` (:188-189) | yes | yes |
| `ApplyCommit` (:199) | no (requires `bal = b`) | yes |
| `ApplyRecover` (:209) | yes (requires `bal < b`) | no |

## Running it here — parses, does not close

**SANY 2.1** parses and semantically processes `EPaxosCommitWithRecovery.tla`
cleanly, with `ExtraConfiguration.tla` beside it. No changes needed.

**TLC does not close under the bundled `.cfg`** on this box. Attempted
2026-08-17 with TLC 2.16 (`~/janus/tla/tla2tools.jar` — note the repo's
environment table in `TODO.md` says 2.19; the jar actually present is 2.16),
8 workers, 7.2 GB heap:

| | |
|---|---|
| states generated | 38,059,515 |
| distinct states | 13,251,622 |
| depth reached | 13 |
| queue at failure | 10,116,132, growing |
| outcome | crashed, `No space left on device` |

No invariant violation was found before it died. The proximate cause was that
`/tmp` here is a 48 GB **tmpfs**, so TLC's disk state queue was consuming RAM;
the underlying reason is that the bundled `.cfg` has **no `CONSTRAINT` and no
`VIEW`**, and the space is genuinely large — `t2_02_epaxos/clean.tla` closes at
3.2M distinct states and tier4 Jetpack at 17.6M, while this had passed 13M at
depth 13 and was still accelerating.

If you re-run it: put the state queue on real disk (`-metadir`), and consider a
constraint in a **separate** `.cfg` of your own rather than editing the vendored
file. See `TODO.md` Phase 56.0.e.

## Scope, stated plainly

- **No `seq`.** EPaxos\* orders on `(cmd, dep)` alone. Every `seq`-looking
  identifier in the file is a substring of `phaseq` / `abalq` / `Sequences`.
- **No execution layer.** The module is commit + recovery. Dependency-graph
  execution ordering is out of scope here, exactly as it is in upstream's spec
  (where `executed'` never appears).
- **The correctness proof is by hand** (paper Appendix D). The TLA+ model is
  checked by TLC in bounded configurations only. As of this writing EPaxos has
  no mechanized safety proof in any system — see
  `docs/consensus_verification_survey.md`.

## Related reading in this repo

- `reports/epaxos_spec_gap.md` — the change list from `src/protocol/EPaxos/` to this spec
- `transpiler/tests/corpus/tier2/t2_02_epaxos/` — the corpus case built on the *unsafe* upstream
- `docs/consensus_verification_survey.md` — entries `w285` (Sutra) and `w116` (EPaxos\*)
