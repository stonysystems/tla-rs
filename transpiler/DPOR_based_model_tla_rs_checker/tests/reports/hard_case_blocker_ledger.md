# Hard-Case Blocker Ledger (Phase 38.14 — audited 2026-04-09)

Protocol cases 13-20: honest status after Phase 38.14 audit.
**Previous "ALL GREEN as of 2026-04-01" claim is retracted — see below.**

| # | Case | Reported | Honest verdict | Bug |
|---|------|----------|----------------|-----|
| 13 | TwoPhase | ok, 9 states | **REAL PASS** | Fixed in 38.14.7.a: `Next` now includes `\E r \in RM : TMRcvPrepared(r)`, manifest wires `expected_property = "TCConsistent"`, and stub status removed |
| 14 | LeaderElection | ok, 0 states | **VACUOUS** | B: Verus → TLA+ → spec roundtrip degenerates LState to flat LRecord with wrong fields, LInit's `s` becomes `int`, every operator body is `arbitrary::<T>()` soup, safety invariants degenerate to `Set::empty().contains(x) ⇒ Set::empty().contains(x)`, model checker can't construct an initial state |
| 15 | ChainReplication | ok, 0 states | **VACUOUS** | B: same fingerprint as case 14 |
| 16 | PrimaryBackup | ok, 0 states | **VACUOUS** | B: same fingerprint as case 14 (LSafetyInactiveStateIsQuiescent also collapses to arbitrary soup) |
| 17 | Paxos | ok, 40 states | **REAL PASS** | Fixed in 38.14.7.b: replaced stuttering source stub with a bounded 2-acceptor/2-value model, included all `Send1a/Send1b/Send2a/Send2b` parameter combinations in `Next`, wired `expected_property = "ChosenValueAgreement"`, and removed stub status |
| 18 | PBFT | ok, 31 states | **VACUOUS** | A: `Next == EnterCommit \/ ExecuteAndReply \/ ViewChange` drops the three parameterized `Send*` actions, so prepareCount/commitCount stay 0 forever and EnterCommit/ExecuteAndReply are unreachable. With `Replica = 1` even if Send actions worked there would be no BFT scenario. CommitSafety is real but never checked at runtime |
| 19 | EPaxos | ok, 0 states | **VACUOUS** | B: same fingerprint as case 14 (12 arbitrary-soup operator bodies) |
| 20 | Raft | ok, 31 states | **VACUOUS** | A: Source `Raft.tla` is a single-node role automaton (no log, no AppendEntries, no commitIndex, no quorums). `Next == BecomeCandidate \/ BecomeLeader \/ StepDown` drops `GrantVote(voter)`. `AtMostOneLeader == state = Leader => votesGranted = votesGranted` is a literal `X => X` tautology. The CONSTANT `Server` is never referenced anywhere in the spec, so `Server = 2` in the model config is dead |

**Real protocol coverage: 2/8**

## Bug Taxonomy

- **Bug A — Hand-written stub TLA+** (remaining cases 18, 20): the source
  `tests/tla/<case>/*.tla` file is itself a degenerate stub. The translator
  is faithful; the input is broken. Common pattern: `Next` drops every action
  with extra parameters beyond `(s, s_, c)` (probably to avoid setting up
  existential bindings), and "safety" invariants are written as `X = X` or
  `X => X`.

- **Bug B — Verus → TLA+ → spec roundtrip degradation** (cases 14, 15, 16, 19):
  the source TLA+ in `tests/tla/<case>/*.tla` is real and meaningful, but the
  `verus2tla` round-trip collapses LState's struct fields, mis-types LInit's
  state parameter as `int`, and converts every dot-access into `arbitrary::<T>()`.

## What the prior fix history actually accomplished

The Phase 38.8.2.a "translator fixes" (`ded3b81`, `0855bd2`, `96a4253`,
`79dd5b8`, `8e9aef8`) were:

1. State variable inference for variable-less specs
2. `s.s.field` double-indirection for flat-alias states
3. Constants param aliasing (`c → c_consts`)
4. LRecord field harvesting from RecordAccess
5. `.tag` enum discriminator identity for hash-encoded enums

These collectively eliminated the **exception/crash** symptoms and made
`verus-transpile model-check` exit cleanly on every case. They did **not**
verify that the resulting state spaces were non-empty, that LNext fired any
real actions, that invariants were non-tautological, or that the runtime
`--invariant` flag was wired through. The 16/20 → 20/20 jump was a clean-exit
jump, not a model-checking-correctness jump.

## Updated: 2026-04-09 — 14 real / 6 vacuous baseline (after 38.14.7.b)
