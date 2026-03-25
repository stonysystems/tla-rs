# DPOR-Based Model Checker — Design Notes

## Workfolder Organization Decision (Phase 38.1.2)

**Decision**: This workfolder is a **separate Cargo crate** (`dpor-checker`)
under `transpiler/DPOR_based_model_tla_rs_checker/`.

**Rationale**:
- **Isolation**: A separate crate prevents accidental coupling with the
  existing `transpiler/src/modelcheck/` code during early prototyping.
- **Independent testing**: The crate can have its own `cargo test` without
  polluting the transpiler's test suite.
- **Clear integration boundary**: When the prototype matures, integration
  means adding a dependency edge, not untangling interleaved code.
- **Shared types later**: The crate can depend on `verus-transpiler` as a
  library for shared types (`RuntimeValue`, `canonical_key`, etc.) when
  needed, without the reverse dependency.

The Cargo crate will be initialized when implementation begins (Phase 38.5+).
Until then, the workfolder contains design docs, test corpus, and scripts.

---

## Upstream References

### GenMC (`https://github.com/MPI-SWS/genmc`)

- **Inspected**: _(to be filled in Phase 38.2.1)_
- **Commit/date**: _(to be pinned)_
- **Architecture summary**: _(pending)_
- **What to borrow**: _(pending)_
- **What to reject**: _(pending)_
- **How it maps to tla-rs**: _(pending)_

### Nidhugg (`https://github.com/nidhugg/nidhugg`)

- **Inspected**: _(to be filled in Phase 38.2.1)_
- **Commit/date**: _(to be pinned)_
- **Architecture summary**: _(pending)_
- **What to borrow**: _(pending)_
- **What to reject**: _(pending)_
- **How it maps to tla-rs**: _(pending)_

### CDSChecker (`https://github.com/computersforpeace/model-checker`)

- **Inspected**: _(to be filled in Phase 38.2.1)_
- **Commit/date**: _(to be pinned)_
- **Architecture summary**: _(pending)_
- **What to borrow**: _(pending)_
- **What to reject**: _(pending)_
- **How it maps to tla-rs**: _(pending)_

---

## DPOR Concept Selection Table (Phase 38.2.3)

| Concept | Source | Borrow / Adapt / Reject | tla-rs Mapping | Notes |
|---------|--------|------------------------|----------------|-------|
| _(to be filled in Phase 38.2)_ | | | | |

---

## tla-rs-Specific Questions (Phase 38.2.4)

1. **What is a "thread" in tla-rs?** _(pending)_
2. **What is the independence relation for tla-rs transitions?** _(pending)_
3. **How do set/map operations affect commutativity?** _(pending)_
4. **Can we reuse `RuntimeValue` + `canonical_key` from the existing checker?** _(pending)_

---

## Prototype-to-Mainline Integration Gate (Phase 38.2.5)

**No rewrite of `transpiler/src/modelcheck` is allowed** until ALL of the
following conditions are met:

1. The DPOR prototype has its own green 20-case regression suite.
2. Baseline exhaustive exploration and DPOR agree on verdict AND normalized
   reachable-state set (or first violation witness) on all small cases.
3. The prototype has been reviewed against the existing checker's telemetry
   and parity infrastructure (Phase 36).
4. A migration plan exists that preserves the existing checker as a fallback.
5. The prototype's performance on at least 3 protocol-scale cases (e.g.,
   TwoPhase, LeaderElection, PrimaryBackup) is documented with before/after
   numbers.

Until these gates are passed, this workfolder is an incubator only.
