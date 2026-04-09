# DPOR Checker Suite Scoreboard

## Phase 38.14 Follow-Up (2026-04-09): 14/20 honest, 6/20 vacuous

The previous "Milestone M9: 20/20 ALL GREEN" claim from 2026-04-01 has been
audited and rejected. After `38.14.7.a` (real TwoPhase case 13) and
`38.14.7.b` (real Paxos case 17), the honest baseline-checker score is
**14 real passes + 6 vacuous passes**. See `design.md`
§"Phase 38.14 Honest Postmortem" for the full root-cause analysis
(Bug A: hand-written stub TLA+; Bug B: Verus → TLA+ → spec roundtrip
degradation).

| Metric | Count |
|--------|-------|
| Total cases | 20 |
| **Real passes** | **14** |
| **Vacuous passes** | **6** |
| Translation failed | 0 |
| Checker error | 0 |

A "real" pass means: an invariant or deadlock check was actually configured
and run, AND the explorer reached at least one distinct state, AND the verdict
matched the manifest expectation. A "vacuous" pass means: `result = ok` was
returned but no property was checked, OR the explorer never reached any state.

### Per-Case Honest Status

| # | Case ID | Reported | Honest | States | Stub status |
|---|---------|----------|--------|--------|-------------|
| 01 | `01_aplusb` | ok | **REAL PASS** | 51 | — |
| 02 | `02_counter_incdec` | ok | **REAL PASS** | 5 | — |
| 03 | `03_counter_race_bug` | inv_viol | **REAL PASS** (bug found) | -- | — |
| 04 | `04_lock_basic` | ok | **REAL PASS** | 3 | — |
| 05 | `05_broken_lock_bug` | inv_viol | **REAL PASS** (bug found) | -- | — |
| 06 | `06_ticket_lock` | ok | **REAL PASS** | 7 | — |
| 07 | `07_producer_consumer` | ok | **REAL PASS** | 51 | — |
| 08 | `08_bounded_buffer` | ok | **REAL PASS** | 6 | — |
| 09 | `09_peterson_mutex` | ok | **REAL PASS** | 10 | — |
| 10 | `10_bakery_mutex` | ok | **REAL PASS** | 24 | — |
| 11 | `11_readers_writers` | inv_viol | **REAL PASS** (bug found) | -- | — |
| 12 | `12_dining_phil` | deadlock | **REAL PASS** (deadlock found) | -- | — |
| 13 | `13_twophase` | ok | **REAL PASS** | 9 | — |
| 14 | `14_leader_election` | ok | **VACUOUS** (0 states) | 0 | bug_b_roundtrip_degraded |
| 15 | `15_chain_repl` | ok | **VACUOUS** (0 states) | 0 | bug_b_roundtrip_degraded |
| 16 | `16_primarybackup` | ok | **VACUOUS** (0 states) | 0 | bug_b_roundtrip_degraded |
| 17 | `17_paxos` | ok | **REAL PASS** | 40 | — |
| 18 | `18_pbft` | ok | **VACUOUS** (Replica=1, drops 3 Send actions, no inv) | 31 | bug_a_incomplete_next |
| 19 | `19_epaxos` | ok | **VACUOUS** (0 states) | 0 | bug_b_roundtrip_degraded |
| 20 | `20_raft` | ok | **VACUOUS** (single-node toy, AtMostOneLeader is `X⇒X`) | 31 | bug_a_stub_source |

### Honest Score by Category

| Category | Real / Total | Notes |
|----------|--------------|-------|
| Micro-models (01–05) | 5/5 | Real invariants, real verdicts |
| Concurrency primitives (06–12) | 7/7 | Real invariants, including ticket lock, Peterson, bakery, R/W, dining phil |
| **Protocols (13–20)** | **2/8** | Cases 13 and 17 are real; 14/15/16/18/19/20 remain vacuous or blocked |

### Reproducing the Audit

```bash
# Re-run the suite (same timeout used for this report)
./scripts/run_full_suite.sh --timeout 600

# Static stub detection on the translated .rs files
./scripts/detect_stub_specs.py
```

### Milestone Trail (with retroactive correction)

- M0 → M1(2) → M1.5(3) → M2(5) → M3(9) → M4(10) → M6(11) → M7(12) → M8(13) → M8.5(16) → M8.6(18) → M9(claimed 20)
- **Phase 38.14 (2026-04-09): retracted M9 → 12 real / 8 vacuous**
- **Phase 38.14.7.a (2026-04-09): case 13 fixed → 13 real / 7 vacuous**
- **Phase 38.14.7.b (2026-04-09): case 17 fixed → 14 real / 6 vacuous**

The growth from M8 (13 real) to the claimed M9 (20) consisted of vacuous
passes. Post-audit protocol gains are now cases 13 and 17 moving to real
passes under 38.14.7.a/38.14.7.b.

### What's actually next

To honestly raise the protocol score above 2/8:

1. **Bug A track** — replace the remaining hand-written stub TLA+ files for
   cases 18 and 20 with real specifications that include all actions in `Next`,
   non-tautological invariants, and meaningful constants. Keep
   `expected_property` wired in the manifest so `--invariant` is actually
   passed.
2. **Bug B track** — fix the Verus → TLA+ field harvesting and Init
   parameter type inference so that auto-generated cases 14, 15, 16, 19
   produce specs whose `LState` reflects the real VARIABLE declarations
   and whose Init parameter is typed as the state struct, not `int`.
3. Then re-run `./scripts/run_full_suite.sh --timeout 600` and
   `./scripts/detect_stub_specs.py` together; both must come back clean
   before any pass count above 14 is trustworthy.
