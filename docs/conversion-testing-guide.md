# Testing TLA+ / Verus Conversions

## Overview

The tla-rs transpiler supports three conversion directions:

1. **TLA+ → Verus spec** (`translate-tla`): Parses TLA+ specs and generates Verus `spec fn` declarations with `.automan` mode annotations.
2. **Verus spec → Verus exec** (default mode): Transpiles `L`-prefixed spec functions into `C`-prefixed exec functions with proof linkage.
3. **Verus spec → TLA+** (`verus2-tla`): Converts Verus spec functions back to TLA+ specifications.

There is also a **full pipeline** (`pipeline`) that chains directions 1 and 2: TLA+ → Verus spec → Verus exec.

This guide covers how to verify each direction works correctly, how to run the automated test suites, and how to debug failures.

## Prerequisites

- Rust toolchain (1.80.1+)
- Build the transpiler: `cd transpiler && cargo build --release`
- For Verus verification: Verus verifier (see `CLAUDE.md` for tested version)
- .NET 6.0 SDK (only needed for building the full project with `scons`)

No TLA+ tooling is required — the TLA+ parser is built into the transpiler. Optionally, [SANY](https://github.com/tlaplus/tlaplus) can independently validate generated `.tla` files.

## Quick Validation Checklist

Three commands to verify all conversions are working:

```bash
# Run all transpiler tests (681 lib + 226 integration = 907 total)
cd transpiler && cargo test

# Run only round-trip consistency tests
cd transpiler && cargo test --test roundtrip

# Full Verus verification of all generated protocols (optional, requires Verus)
scons --verus-path=/path/to/verus
```

If all tests pass, all conversions are working correctly.

---

## Direction 1: TLA+ → Verus Spec (`translate-tla`)

### Running the translation

```bash
cd transpiler

# Basic translation
cargo run -- translate-tla \
    --input tests/tla_examples/SimpleCounter.tla \
    --output /tmp/counter.rs

# With mode annotations (generates .automan file alongside output)
cargo run -- translate-tla \
    --input tests/tla_examples/SimpleCounter.tla \
    --output /tmp/counter.rs \
    --gen-modes

# With explicit type annotations
cargo run -- translate-tla \
    --input tests/tla_examples/Raft.tla \
    --output /tmp/raft.rs \
    --types tests/tla_examples/Raft.tla-types
```

### Checking the output

Verify the generated Verus spec file:

1. Contains a `verus! {}` block with `use vstd::prelude::*;`
2. `pub struct LState` has one field per TLA+ `VARIABLE`
3. `pub struct LConstants` has one field per TLA+ `CONSTANT` (if any)
4. Each TLA+ operator becomes `pub open spec fn L<Name>(...) -> bool`
5. Action operators (those with primed variables) have `s: LState, s_: LState` parameters
6. Non-action predicates have `s: LState` only
7. `LInit` sets initial values matching the TLA+ `Init` operator
8. `LNext` is a disjunction of all action operators

### Automated tests

```bash
# Parse and translate all 7 TLA+ examples
cargo test --test tla_examples_test

# End-to-end pipeline tests
cargo test --test pipeline_e2e_test

# Semantic preservation (variables, constants, init, actions, expressions)
cargo test --test roundtrip_test
```

The 7 example files in `transpiler/tests/tla_examples/` are: SimpleCounter, DieHard, EWD840, TwoPhase, Raft, Paxos, PBFT.

---

## Direction 2: Verus Spec → Verus Exec (default mode)

### Running the transpilation

```bash
cd transpiler

# Single file — requires spec file, annotations, and config
cargo run -- \
    --input ../src/protocol/TwoPhase/twophase.rs \
    --annotations ../src/protocol/TwoPhase/twophase.automan \
    --config ../src/protocol/TwoPhase/twophase_transpile.toml \
    --output /tmp/twophase_gen.rs

# Generate type definitions
cargo run -- generate-types \
    --input ../src/protocol/TwoPhase/types.rs \
    --config ../src/protocol/TwoPhase/types_transpile.toml \
    --output /tmp/types_gen.rs

# Dry run (show output without writing)
cargo run -- \
    --input ../src/protocol/TwoPhase/twophase.rs \
    --annotations ../src/protocol/TwoPhase/twophase.automan \
    --config ../src/protocol/TwoPhase/twophase_transpile.toml \
    --dry-run --stdout
```

### Checking the output

Verify the generated exec file:

1. Every annotated function (from `.automan`) that is not in `skip_functions` (from config) produces a `pub exec fn C<Name>`
2. Each exec function has:
   - `requires` clause including validity predicates (e.g., `s.valid()`)
   - `ensures` clause referencing the original spec function: `ensures L<Name>(old(s)@, ...)`
3. The function body constructs `C`-prefixed types from `L`-prefixed spec types
4. Functions listed in `skip_functions` are absent from the output
5. `custom_imports` from the config appear at the top of the generated file

### Automated tests

```bash
# Integration tests for Raft, ChainReplication, and core transpilation
cargo test --test integration

# Specific protocol tests
cargo test test_raft_function_transpilation
cargo test test_chain_replication_function_transpilation

# All library unit tests (parser, code generation, mode analysis, etc.)
cargo test --lib
```

---

## Direction 3: Verus Spec → TLA+ (`verus2tla`)

### Running the conversion

```bash
cd transpiler

# Single file
cargo run -- verus2-tla \
    --input ../src/protocol/Raft/raft.rs \
    --output /tmp/Raft.tla

# Batch mode (all .rs files in a directory)
cargo run -- verus2-tla \
    --input ../src/protocol/Raft/ \
    --output /tmp/Raft_tla/ \
    --batch

# Include recommends as ASSUME statements
cargo run -- verus2-tla \
    --input ../src/protocol/Raft/raft.rs \
    --output /tmp/Raft.tla \
    --include-recommends
```

### Checking the output

Verify the generated TLA+ file:

1. Follows TLA+ module structure: `---- MODULE Name ----` ... `====`
2. `L` prefix is stripped from operator and type names
3. Each `spec fn` becomes a TLA+ operator with matching parameter count
4. Type definitions become TLA+ record constructors
5. Verus expressions map correctly (conjunction `&&&` → `/\`, disjunction `|||` → `\/`, etc.)

The project maintains 33 generated TLA+ spec files across 9 protocols in `src/tla+/`.

### Automated tests

```bash
# Round-trip consistency tests (Verus → TLA+ → Verus comparison)
cargo test --test roundtrip

# Specific round-trip tests
cargo test --test roundtrip test_twophase_roundtrip
cargo test --test roundtrip test_paxos_roundtrip
```

---

## Full Pipeline: TLA+ → Verus Exec

The `pipeline` command chains direction 1 and direction 2 in a single invocation:

```bash
cd transpiler

cargo run -- pipeline \
    --tla-input tests/tla_examples/SimpleCounter.tla \
    --exec-output /tmp/counter_exec.rs \
    --keep-intermediate

# With a transpiler config for the exec stage
cargo run -- pipeline \
    --tla-input tests/tla_examples/TwoPhase.tla \
    --exec-output /tmp/twophase_exec.rs \
    --config ../src/protocol/TwoPhase/twophase_transpile.toml \
    --keep-intermediate
```

The `--keep-intermediate` flag preserves the intermediate spec `.rs` and `.automan` files so you can inspect the midpoint between TLA+ and exec code.

```bash
# Pipeline end-to-end tests
cargo test --test pipeline_e2e_test
```

---

## Round-trip Consistency Testing

### How it works

The round-trip testing framework (`transpiler/src/roundtrip/`) verifies semantic preservation by:

1. Converting in one direction (e.g., TLA+ → Verus)
2. Converting back (Verus → TLA+)
3. Comparing canonical AST representations

Canonicalization normalizes: `L`-prefix stripping, record field sorting, operator equivalences (e.g., `!=` → `¬(=)`), and whitespace/formatting. Comparison is structural at the AST level, not textual.

### Running round-trip tests

```bash
cd transpiler

# All round-trip tests
cargo test --test roundtrip

# Semantic preservation tests (variables, constants, init, actions, expressions)
cargo test --test roundtrip_test

# All round-trip-related tests together
cargo test roundtrip
```

### What failures mean

A round-trip failure means the canonical ASTs differ after a convert-and-convert-back cycle. Common causes:

- **Unsupported TLA+ construct**: The parser doesn't handle a particular syntax pattern. Check `docs/tla-transpiler-limitations.md` for the full list.
- **Expression translation losing structure**: An intermediate conversion step simplifies or restructures an expression.
- **Type information mismatch**: Type inference produces different types on the second pass.

---

## Running the Complete Test Suite

```bash
cd transpiler

# Everything (recommended)
cargo test

# Library tests only (681 tests: parser, code generation, mode analysis, proofs)
cargo test --lib

# Integration tests only (226 tests across 7 test files + main binary tests)
cargo test --test integration
cargo test --test roundtrip
cargo test --test roundtrip_test
cargo test --test pipeline_e2e_test
cargo test --test tla_examples_test
cargo test --test regression_test
cargo test --test negative_tests

# With output visible
cargo test -- --nocapture

# Verus verification of all generated protocols (optional)
scons --verus-path=/path/to/verus
```

---

## Adding a New Protocol

1. **Create spec files**: Write `src/protocol/MyProto/myproto.rs` with `spec fn L<Name>` functions inside `verus! {}`, and `src/protocol/MyProto/types.rs` for type definitions.

2. **Create mode annotations**: Write `src/protocol/MyProto/myproto.automan` with function mode annotations. Format:
   ```
   module MyProto::myproto
   LInit(+s_, +c)
   LAction(+s, -s_, +c, +param)
   ```
   Use `+` for input parameters and `-` for output parameters.

3. **Create transpile config**: Write `src/protocol/MyProto/myproto_transpile.toml`. Use an existing config (e.g., `src/protocol/TwoPhase/twophase_transpile.toml`) as a template. See `docs/transpiler-config-reference.md` for all options.

4. **Generate exec code**:
   ```bash
   cd transpiler
   cargo run -- --input ../src/protocol/MyProto/myproto.rs \
                --annotations ../src/protocol/MyProto/myproto.automan \
                --config ../src/protocol/MyProto/myproto_transpile.toml \
                --output ../src/generated/MyProto/myproto_gen.rs
   ```

5. **Generate types** (if types.rs exists):
   ```bash
   cargo run -- generate-types \
                --input ../src/protocol/MyProto/types.rs \
                --config ../src/protocol/MyProto/types_transpile.toml \
                --output ../src/generated/MyProto/types_gen.rs
   ```

6. **Generate TLA+ specs**:
   ```bash
   cargo run -- verus2-tla \
                --input ../src/protocol/MyProto/ \
                --output ../src/tla+/MyProto/ \
                --batch
   ```

7. **Add integration tests**: Add tests to `transpiler/tests/integration.rs` following the pattern of `test_raft_function_transpilation` or `test_chain_replication_function_transpilation`.

8. **Verify**: Run `cargo test` and optionally `scons --verus-path=/path/to/verus`.

---

## Debugging Conversion Failures

### TLA+ parse errors

The TLA+ parser supports a subset of TLA+. Use `--verbose` on the CLI for diagnostics. Common issues:
- Vertical conjunction/disjunction lists (bullet `/\` and `\/`) — supported
- `LET ... IN` expressions — supported for simple cases
- Recursive operator definitions — may need manual intervention
- See `docs/tla-transpiler-limitations.md` for the full list of unsupported features

### Type inference failures

If generated Verus code uses `int` where you expect a specific type, provide a `.tla-types` annotation file:
```bash
cargo run -- translate-tla --input spec.tla --output spec.rs --types spec.tla-types
```
See `docs/tla-to-verus-guide.md` for the type annotation format.

### Transpiler parse errors on Verus spec files

The Verus spec parser has known limitations:
- `as u64` casts — use typed parameters (`u64`) instead of `int` with casts
- Typed integer suffixes like `0u64` — use plain `0` when the type is inferrable
- Complex match expressions — add the function to `skip_functions` in the config

### Missing or wrong operator output

Compare operator counts between input and output. For TLA+ → Verus, count `pub open spec fn L` in the output vs operators in the TLA+ source. For Verus → exec, count `pub exec fn C` in the output vs annotated functions minus `skip_functions`.

### Verus verification failures after transpilation

If Verus rejects the generated code:
1. Check that `valid()` predicates in `types_gen.rs` are correct
2. Check that `requires` clauses are sufficient — use `extra_requires` in the config to add more
3. Consider adding the function to `skip_functions` if the pattern is too complex
4. Ensure `generate_proofs = true` in the config for inline proof hints
5. Use `--verbose` on the transpiler to see translation decisions

---

## Compile & Run Status Matrix

**Last updated**: 2026-02-13 (Phase 16 complete — all 4 directions × all examples pass)

### Summary

| Direction | Description | Examples | Status |
|-----------|-------------|----------|--------|
| D1: TLA+ → Verus Spec | `translate-tla` | 7/7 | ✅ All compile & verify |
| D2: Verus Spec → Verus Exec | default mode (TLA-generated) | 7/7 | ✅ All compile & verify |
| D2: Verus Spec → Verus Exec | default mode (hand-written) | 10/10 | ✅ 581+ verified, 0 errors |
| D3: Verus Spec → TLA+ | `verus2-tla` | 33/33 | ✅ All SANY validated |
| D4: TLA+ → Verus Exec | `pipeline` (D1+D2) | 7/7 | ✅ 69 total verified, 0 errors |

### TLA+ Examples (`transpiler/tests/tla_examples/`)

#### Direction 1: TLA+ → Verus Spec (`translate-tla`)

| Example | Transpile | Verus Compile | Notes |
|---------|-----------|---------------|-------|
| SimpleCounter | ✅ | ✅ | Generates spec + automan |
| DieHard | ✅ | ✅ | Generates spec + automan |
| EWD840 | ✅ | ✅ | Fixed: Set type inference, empty set annotation |
| TwoPhase | ✅ | ✅ | Fixed: Set type inference, empty set annotation |
| Raft | ✅ | ✅ | Fixed: string literal `@` suffix, Set type inference |
| Paxos | ✅ | ✅ | Fixed: record struct field types, keyword escaping |
| PBFT | ✅ | ✅ | Fixed: record struct field types, keyword escaping |

**Command**:
```bash
cd transpiler
cargo run --release -- translate-tla \
    --input tests/tla_examples/<NAME>.tla \
    --output /tmp/<name>.rs --gen-modes
```

#### Direction 2: Verus Spec → Verus Exec (from TLA-generated specs)

| Example | Transpile | Verus Compile | Notes |
|---------|-----------|---------------|-------|
| SimpleCounter | ✅ | ✅ | Verified via D4 pipeline |
| DieHard | ✅ | ✅ | Verified via D4 pipeline; overflow guards for conditional arithmetic |
| EWD840 | ✅ | ✅ | Fixed: annotation match, HashSet clone via `clone_hashset` helper |
| TwoPhase | ✅ | ✅ | Fixed: string literal parsing, set field View mapping |
| Raft | ✅ | ✅ | Fixed: string literal parsing, set field cloning + union/difference ops |
| Paxos | ✅ | ✅ | Fixed: record literal parsing, record struct handling |
| PBFT | ✅ | ✅ | Fixed: record literal parsing, record struct + set ops |

**Command** (two steps):
```bash
cd transpiler
# Step 1: TLA+ → Verus Spec
cargo run --release -- translate-tla \
    --input tests/tla_examples/<NAME>.tla \
    --output /tmp/<name>.rs --gen-modes
# Step 2: Verus Spec → Verus Exec
cargo run --release -- \
    --input /tmp/<name>.rs \
    --annotations /tmp/<name>.automan \
    --output /tmp/<name>_exec.rs
```

#### Direction 3: Verus Spec → TLA+ (`verus2-tla`)

| Example (from TLA-generated specs) | Transpile | SANY Valid | Notes |
|-------------------------------------|-----------|------------|-------|
| SimpleCounter | ✅ | N/A | Intermediate spec; not persisted to src/tla+ |
| DieHard | ✅ | N/A | Intermediate spec; not persisted to src/tla+ |
| EWD840 | ✅ | N/A | Intermediate spec; not persisted to src/tla+ |
| TwoPhase | ✅ | N/A | Intermediate spec; not persisted to src/tla+ |
| Raft | ✅ | N/A | Intermediate spec; not persisted to src/tla+ |
| Paxos | ✅ | N/A | Intermediate spec; not persisted to src/tla+ |
| PBFT | ✅ | N/A | Intermediate spec; not persisted to src/tla+ |

| Example (from hand-written Verus specs) | Transpile | SANY Valid | Notes |
|-----------------------------------------|-----------|------------|-------|
| RSL/election.rs | ✅ | ✅ | |
| RSL/acceptor.rs | ✅ | ✅ | |

| Protocol (all `src/tla+/` specs) | Files | SANY Valid | Notes |
|----------------------------------|-------|------------|-------|
| TwoPhase | 2 | ✅ | |
| Paxos | 2 | ✅ | |
| LeaderElection | 2 | ✅ | |
| Raft | 2 | ✅ | |
| ChainReplication | 2 | ✅ | |
| PrimaryBackup | 2 | ✅ | |
| PBFT | 2 | ✅ | |
| VerticalPaxos | 2 | ✅ | |
| EPaxos | 2 | ✅ | |
| RSL | 15 | ✅ | All 15 component specs pass |
| **Total** | **33** | **33/33** | `scripts/validate_tla_specs.sh` validates all |

**Command**:
```bash
cd transpiler
cargo run --release -- verus2-tla \
    --input /tmp/<name>.rs \
    --output /tmp/<name>.tla
```

#### D3 Per-File Results: `transpiler_generated_tla/` (from real protocol specs)

Generated from `src/protocol/<Protocol>/` inputs via `scripts/generate_tla_workspace.sh`.

| Protocol | File | SANY | Notes |
|----------|------|------|-------|
| TwoPhase | Types.tla | ✅ | |
| TwoPhase | Twophase.tla | ✅ | |
| Paxos | Types.tla | ✅ | |
| Paxos | Paxos.tla | ✅ | |
| LeaderElection | Types.tla | ✅ | |
| LeaderElection | Election.tla | ✅ | |
| Raft | Types.tla | ✅ | |
| Raft | Raft.tla | ✅ | |
| ChainReplication | Types.tla | ✅ | |
| ChainReplication | Chain.tla | ✅ | Fixed: comparison precedence parens (`=` vs `>`) |
| PrimaryBackup | Types.tla | ✅ | |
| PrimaryBackup | Primarybackup.tla | ✅ | |
| PBFT | Types.tla | ✅ | |
| PBFT | Pbft.tla | ✅ | |
| VerticalPaxos | Types.tla | ✅ | |
| VerticalPaxos | Vpaxos.tla | ✅ | |
| EPaxos | Types.tla | ✅ | |
| EPaxos | Epaxos.tla | ✅ | |
| RSL | Acceptor.tla | ✅ | |
| RSL | Broadcast.tla | ✅ | |
| RSL | Configuration.tla | ✅ | |
| RSL | Constants.tla | ✅ | |
| RSL | Distributed_system.tla | ✅ | |
| RSL | Election.tla | ✅ | |
| RSL | Environment.tla | ✅ | |
| RSL | Executor.tla | ✅ | |
| RSL | Learner.tla | ✅ | |
| RSL | Message.tla | ✅ | |
| RSL | Parameters.tla | ✅ | |
| RSL | Proposer.tla | ✅ | |
| RSL | Replica.tla | ✅ | |
| RSL | State_machine.tla | ✅ | |
| RSL | Types.tla | ✅ | |
| **Total** | **33** | **33/33** | |

#### D1 Round-trip: `transpiler_generated_tla/` → Verus Spec (Phase 16.8.3)

Feeds D3 output back through `translate-tla` to verify the TLA+ parser handles all generated patterns.
Output written to `transpiler/tla_test_workspace/transpiler_generated_verus_spec/`.

| Protocol | Files | Parse | Translate | Notes |
|----------|-------|-------|-----------|-------|
| TwoPhase | 2 | ✅ | ✅ | Fixed: `::` enum path stripping |
| Paxos | 2 | ✅ | ✅ | |
| LeaderElection | 2 | ✅ | ✅ | |
| Raft | 2 | ✅ | ✅ | Fixed: `[D -> R]` fn set type, EXCEPT base parsing |
| ChainReplication | 2 | ✅ | ✅ | |
| PrimaryBackup | 2 | ✅ | ✅ | Fixed: `::` enum path stripping |
| PBFT | 2 | ✅ | ✅ | |
| VerticalPaxos | 2 | ✅ | ✅ | |
| EPaxos | 2 | ✅ | ✅ | |
| RSL | 15 | ✅ | ✅ | Fixed: EXCEPT with dotted/call base, `[D -> R]` fn set type |
| **Total** | **33** | **33/33** | **33/33** | |

**Fixes applied to unblock round-trip:**
1. **D3 emitter** (`verus2tla/converter.rs`): Strip Rust `::` enum type prefix from `Ident` and `Call` expressions
2. **D1 parser** (`tla/parser.rs`): Support dotted expressions (`s.field`) and function calls (`f(x)`) as `EXCEPT` base
3. **D1 parser** (`tla/parser.rs`): Support `[Domain -> Range]` function set type notation (new `FnSet` AST variant)

#### D1 Verus Compile Baseline on Generated Specs (Phase 16.8.3d-3d-5)

Measured with Verus on each generated D1 `.rs` file (`verus --crate-type=lib <file>`), captured by
`test_d1_generated_verus_spec_compile_baseline`.

| Metric | Count |
|--------|-------|
| Total generated D1 spec files | 33 |
| Compile pass | 31 |
| Compile fail | 2 |
| `E0425` unresolved symbol | 0 |
| `E0423` value/type constructor misuse | 0 |
| `E0609` unknown field on scalar | 0 |
| `E0599` missing method on scalar | 1 |
| `E0308` mismatched types | 1 |
| `E0600` unary operator type mismatch | 0 |
| `E0618` call on non-function | 0 |
| `E0277` trait-bound failure | 0 |
| `E0061` wrong argument count | 0 |
| `E0282` type annotations needed | 0 |
| `REC_DECREASES` missing decreases on recursive fn | 0 |
| Other categories | 0 |

Residual first-error files after `16.8.3d-3d-5`:
- `RSL/Executor.rs` (`E0308`)
- `RSL/Replica.rs` (`E0599`)

Update after `16.8.3d-3d-4` + `16.8.3d-3d-5`:
- Generated-D1 recursive helpers now emit conservative `decreases <seq>.len()` when all recursive self-calls provably shrink the same sequence argument (`skip`/`drop_first`/`Tail`), eliminating the `REC_DECREASES` first-error class.
- D1 baseline assertions were tightened to pin the two residual failing files explicitly, so regressions in blocker location/category fail fast.
- Promotion decision for `16.8.3d-3`: **not ready yet** (`31/33`, target remains `33/33`).

This compile gate is currently blocked by codegen quality in D1 output (symbol/value emission shape),
not by D1 parsing coverage (which is already 33/33).

#### D2 on D1 Output: `transpiler_generated_verus_spec/` → Verus Exec (Phase 16.8.4)

Attempts D2 (Verus Spec → Verus Exec) transpilation on D1-generated Verus spec files.
Output directory: `transpiler/tla_test_workspace/transpiler_generated_verus_exec/`.

| Protocol | Files | D2 Parse | D2 Transpile | Failure Category |
|----------|-------|----------|-------------|------------------|
| TwoPhase | 2 | 2 ✅ / 0 ❌ | 2 ✅ | all pass |
| Paxos | 2 | 2 ✅ / 0 ❌ | 2 ✅ | all pass |
| LeaderElection | 2 | 2 ✅ / 0 ❌ | 2 ✅ | all pass |
| Raft | 2 | 2 ✅ / 0 ❌ | 2 ✅ | all pass |
| ChainReplication | 2 | 2 ✅ / 0 ❌ | 2 ✅ | all pass |
| PrimaryBackup | 2 | 2 ✅ / 0 ❌ | 2 ✅ | all pass |
| PBFT | 2 | 2 ✅ / 0 ❌ | 2 ✅ | all pass |
| VerticalPaxos | 2 | 2 ✅ / 0 ❌ | 2 ✅ | all pass |
| EPaxos | 2 | 2 ✅ / 0 ❌ | 2 ✅ | all pass |
| RSL | 15 | 10 ✅ / 5 ❌ | 10 ✅ | 5 recursive codegen unsupported (Broadcast/Election/Executor/Replica/State_machine) |
| **Total** | **33** | **28/33** | **28/33** | |

Revalidated after `16.8.4d-3c` annotation-arity fix + full D1 workspace regeneration (2026-02-21) via:
`cargo test --test integration test_d2_spec_to_exec_on_generated_workspace -- --nocapture`
with totals: `28/33` pass, `0` Cat-A, `0` Cat-B, `0` Cat-C, `5` other.

**Gate status (16.8.4d-4): REQUIRED**
- Enforced by `test_d2_spec_to_exec_on_generated_workspace`.
- Required baseline: `>=27/33` pass, `0` Cat-A, `0` Cat-B, `0` Cat-C, `<=6` other.
- Remaining "other" failures are the tracked recursive-codegen backlog (not parser/annotation blockers).

**Failure Categories:**
- **Cat-A (0 files)**: residual anonymous-record parser failures eliminated by `16.8.4d-3b`.
- **Cat-B (0 files)**: call-shape parse failures ("Expected ')', found '('") were eliminated by `16.8.4d-1` (`translate_op_apply` fix).
- **Cat-C (0 files)**: annotation parameter mismatch class eliminated by `16.8.4d-3c`.
- **Other (5 files)**: recursive helper lowering gaps (`LBuildLBroadcast`, `LRemoveAllSatisfiedRequestsInSequence`, `LGetPacketsFromReplies`, `LExtractSentPacketsFromIos`, `LHandleRequestBatchHidden`).

**Root cause**: D1 (TLA+ → Verus) parsing/signature/annotation compatibility is now largely aligned with D2 after the nested-record and arity fixes. Remaining blockers are concentrated in recursive codegen pattern coverage for D2.

#### Runtime Validation: D2-Generated Exec Code (Phase 16.8.4, completed 2026-03-08)

Production D2-generated code validated via `scripts/integration_test_cluster.sh` (Phase 17.6 infrastructure).
All 10 protocols tested with 3-node clusters for 30s:

| Protocol | Runtime Result | Duration | Nodes | Observed Behavior |
|----------|---------------|----------|-------|-------------------|
| RSL | PASS (end-to-end) | 30s | 3 | Servers stable, client throughput verified |
| TwoPhase | PASS | 30s | 3 | Stable, normal message exchange |
| LeaderElection | PASS | 30s | 3 | Stable, normal message exchange |
| PrimaryBackup | PASS | 30s | 3 | Stable, normal message exchange |
| ChainReplication | PASS | 30s | 3 | Stable, normal message exchange |
| Paxos | PASS | 30s | 3 | Stable, normal message exchange |
| VerticalPaxos | PASS | 30s | 3 | Stable, normal message exchange |
| Raft | PASS (benchmark) | 30s | 3 | Stable, benchmark client verified |
| PBFT | PASS | 30s | 3 | Stable, moderate activity (24 log lines) |
| EPaxos | PASS | 30s | 3 | Most active: 134K log lines (extensive message exchange) |

**Replay command:**
```bash
./scripts/integration_test_cluster.sh
```

#### D3 TLC Model Checking: `transpiler_generated_tla_with_properties/` (Phase 16.8.2)

TLC model checking of D3-generated TLA+ specs with manually written MC wrappers.
MC wrappers add finite domains, explicit message channels, and safety invariants.

| Protocol | TLC Result | States | Distinct | Depth | Invariants | Time | Notes |
|----------|-----------|--------|----------|-------|------------|------|-------|
| TwoPhase | ✅ PASS | 926 | 304 | 9 | 5 | 2s | Consistency, TMCommit/Abort implications |
| Paxos | ⚠️ PARTIAL | 1.37B+ | 198M+ | 30 | 4 | 20min+ | No violation in 1.37B states; exhaustive check infeasible |
| LeaderElection | ✅ PASS | 100,636 | 9,337 | 13 | 5 | 2s | TypeOK, LeaderValid, ElectingSubsetAlive |
| PrimaryBackup | ✅ PASS | 786 | 438 | 20 | 6 | 1s | LogConsistency, NoSplitBrain, ViewBounded |
| Raft | — | — | — | — | — | — | State space too large (Seq-based logs) |
| ChainReplication | — | — | — | — | — | — | State space too large (Seq-based logs) |
| PBFT | — | — | — | — | — | — | State space too large (9 actions + per-node) |
| VerticalPaxos | — | — | — | — | — | — | State space too large (multi-ballot + views) |
| EPaxos | — | — | — | — | — | — | State space too large (11 actions + deps) |

**Model sizes used:** TwoPhase: 3 RMs. Paxos: 3 nodes, ballot=node-ID, 2 values, quorum=2 (exhaustive check infeasible; 1.37B states explored with 0 violations). LeaderElection: 3 nodes. PrimaryBackup: 3 values, max log 3, max view 2.

**Key findings:**
- Relational specs (s, s_, c) require MC wrappers with explicit VARIABLE state, finite domains, and message channels
- Paxos uses ballot=node-ID ownership to prevent multiple proposers on same ballot; 3-node model creates very large state space (~200M+ distinct states)
- Protocols with sequence-based state (Raft, ChainReplication) have state spaces too large for exhaustive model checking even with minimal finite domains
- 3 protocols (TwoPhase, LeaderElection, PrimaryBackup) exhaustively checked with all invariants verified; Paxos partially checked (1.37B states, 0 violations found)

**Phase 33.4.3 TLC vs source-first benchmark comparison (2026-03-08)**:

Matched TLC and source-first model checking on the same finite models with the same safety invariants. Full comparison: `reports/benchmarks/TLC_VS_SOURCE_FIRST_BENCHMARK_COMPARISON.md`. Replay: `scripts/run_tlc_benchmarks.sh`, `scripts/run_model_check_benchmarks.sh`, `scripts/compare_tlc_vs_source_first.sh`.

| Protocol | Source-first | TLC (distinct states / wall) | Model |
|----------|-------------|------------------------------|-------|
| TwoPhase | 8 states, 79s (exhausted) | 64 / 1s (exhausted) | 2 RMs |
| PrimaryBackup | 60 states, 190s (exhausted) | 54 / 1s (exhausted) | max_log=1, values={0,1} |
| LeaderElection | BLOCKED (enumeration) | 9,337 / 2s (exhausted) | 3 nodes |
| Paxos | BLOCKED (enumeration) | 3,005,604 / 375s (exhausted) | 3 nodes, quorum=2 |

Benchmark configs: `transpiler/tests/model_check_fixtures/benchmarks_1h/`. TLC wrappers: `transpiler/tla_test_workspace/transpiler_generated_tla_with_properties/benchmarks_1h/`.

#### D1 on External TLA+ Corpora (Phase 16.8.5)

Tests D1 parser robustness against TLA+ specs NOT produced by our D3 emitter.

**LLM-Authored Specs** (`tla_test_workspace/generated_tla_by_llm/`):

| Spec | D1 Parse | Blocking Construct |
|------|----------|-------------------|
| SimpleConsensus.tla | ✅ | — |
| SimpleLeader.tla | ✅ | — |
| SimplePrimary.tla | ✅ | — |
| TwoPhaseCommit.tla | ❌ | `1..NumRM` range operator |
| SimplePaxos.tla | ❌ | `ASSUME Name ==` named assume |
| SimpleRaft.tla | ❌ | `[][Next]_<<vars>>` temporal subscript |
| BullyElection.tla | ❌ | `[][Next]_<<vars>>` temporal subscript |
| PrimaryBackup.tla | ❌ | `\E v \in 1..MaxVal` range in quantifier |
| ChainRep.tla | ❌ | `1..ChainLen` range operator |
| SimplePBFT.tla | ❌ | `[][Next]_<<vars>>` temporal subscript |
| SimpleEPaxos.tla | ❌ | Range in multi-var quantifier |
| VerticalPaxos.tla | ❌ | Range in multi-var quantifier |
| **Total** | **3/12** | |

**Community Canonical Specs** (`tla_test_workspace/tla_by_community/`):

| Spec | License | D1 Parse | Output Quality | Blocking Construct |
|------|---------|----------|---------------|-------------------|
| EPaxos_community.tla | Apache 2.0 | ✅ | Minimal (empty) | — |
| Paxos_community.tla | MIT | ✅ | Minimal (empty) | — |
| Raft_community.tla | CC BY 4.0 | ✅ | Minimal (constants only) | — |
| TwoPhase_community.tla | MIT | ❌ | — | `[type : {"Prepared"}, rm : RM]` record set |
| **Total** | | **3/4** | | |

Note: Community specs that pass D1 produce minimal output because complex TLA+ constructs (CHOOSE, function mapping, LET...IN) parse but don't generate Verus code. See `docs/tla-input-compatibility-report.md` for the full analysis.

#### Direction 4: TLA+ → Verus Exec (pipeline)

| Example | Pipeline | Verus Compile | Notes |
|---------|----------|---------------|-------|
| SimpleCounter | ✅ | ✅ 7 verified, 0 errors | |
| DieHard | ✅ | ✅ 9 verified, 0 errors | Fixed overflow guards for conditional arithmetic |
| EWD840 | ✅ | ✅ 8 verified, 0 errors | Fixed HashSet clone via `clone_hashset` helper |
| TwoPhase | ✅ | ✅ 6 verified, 0 errors | Fixed set field View mapping |
| Raft | ✅ | ✅ 11 verified, 0 errors | Fixed set field cloning + union/difference ops |
| Paxos | ✅ | ✅ 13 verified, 0 errors | Fixed record struct handling |
| PBFT | ✅ | ✅ 15 verified, 0 errors | Fixed record struct + set ops |

**Command**:
```bash
cd transpiler
cargo run --release -- pipeline \
    --tla-input tests/tla_examples/<NAME>.tla \
    --exec-output /tmp/<name>_exec.rs \
    --keep-intermediate
```

### Verus Spec → Verus Exec (Existing Protocol Specs)

Generated code in `src/generated/` compiles and verifies with Verus: **581+ verified, 0 errors** (10 uniform packet-identity assumes remain in replica_gen.rs — irreducible IO trust boundary).

| Module | Status | Notes |
|--------|--------|-------|
| RSL/replica_gen.rs | ✅ 0 errors | 7 irreducible IO trust boundary assumes remain |
| RSL/proposer_gen.rs | ✅ 0 errors | |
| RSL/types_gen.rs | ✅ 0 errors | |
| RSL/acceptor_gen.rs | ✅ 0 errors | |
| RSL/election_gen.rs | ✅ 0 errors | |
| RSL/executor_gen.rs | ✅ 0 errors | |
| RSL/learner_gen.rs | ✅ 0 errors | |
| RSL/broadcast_gen.rs | ✅ 0 errors | |
| TwoPhase/*_gen.rs | ✅ 0 errors | |
| Paxos/*_gen.rs | ✅ 0 errors | |
| LeaderElection/*_gen.rs | ✅ 0 errors | |
| Raft/*_gen.rs | ✅ 0 errors | |
| ChainReplication/*_gen.rs | ✅ 0 errors | |
| PrimaryBackup/*_gen.rs | ✅ 0 errors | |
| PBFT/*_gen.rs | ✅ 0 errors | |
| VerticalPaxos/*_gen.rs | ✅ 0 errors | |
| EPaxos/*_gen.rs | ✅ 0 errors | |

**Command**:
```bash
scons --verus-path=/home/shuai/tools/verus-x86-linux
```

---

## See Also

- `docs/tla-to-verus-guide.md` — Full TLA+ to Verus operator mapping and type annotations
- `docs/tla_features.md` — TLA+ feature support matrix
- `docs/tla-transpiler-limitations.md` — Known limitations and workarounds
- `docs/transpiler-config-reference.md` — Complete TOML config options reference
- `docs/dev/verus2tla-design.md` — Internal design of the verus2tla module
- `docs/dev/phase2_roundtrip_design.md` — Round-trip testing framework design
- `CLAUDE.md` — Project overview and build commands
