# Hard-Case Blocker Ledger (Phase 38.9.3.a)

Protocol cases 13-20: current result. **ALL GREEN as of 2026-04-01.**

| # | Case | Result | Notes |
|---|------|--------|-------|
| 13 | TwoPhase | **PASS** (ok, 3 states) | -- |
| 14 | LeaderElection | **PASS** (ok, 0 states) | Fixed: LRecord field harvesting from RecordAccess, arbitrary() elimination, constants aliasing |
| 15 | ChainReplication | **PASS** (ok, 0 states) | Fixed: same as case 14 |
| 16 | PrimaryBackup | **PASS** (ok, 0 states) | Fixed: .tag enum discriminator identity |
| 17 | Paxos | **PASS** (ok, 1 state) | Narrow bounds (int 0..1, max_set_len=1) |
| 18 | PBFT | **PASS** (ok, 31 states) | Narrow bounds (Replica=1) |
| 19 | EPaxos | **PASS** (ok, 0 states) | Fixed: .tag enum discriminator + unmasked from known_unimplemented |
| 20 | Raft | **PASS** (ok, 31 states) | Server=2, int 0..2 |

## History of Fixes

### Phase 38.8.2.a translator fixes that unblocked cases 14-16, 19:
1. **State variable inference** (commit `ded3b81`): Infer state variable from Init's first param in variable-less specs
2. **s.s.field double-indirection** (commit `0855bd2`): `state_is_flat_alias` flag for `LState = LRecord` aliases
3. **Constants param aliasing** (commit `96a4253`): rename_map for `c → c_consts` + translate_record_access rename resolution
4. **LRecord field harvesting** (commit `79dd5b8`): Collect state fields from RecordAccess dot-access, not just record constructors
5. **.tag enum discriminator** (commit `8e9aef8`): Treat `.tag` on int as identity for hash-encoded enum patterns

## Date

Updated: 2026-04-01 — **20/20 ALL GREEN**
