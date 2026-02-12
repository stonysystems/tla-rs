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
# Run all transpiler tests (656 lib + 33 integration)
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

# Library tests only (656 tests: parser, code generation, mode analysis, proofs)
cargo test --lib

# Integration tests only (33 tests across 7 test files)
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

## See Also

- `docs/tla-to-verus-guide.md` — Full TLA+ to Verus operator mapping and type annotations
- `docs/tla_features.md` — TLA+ feature support matrix
- `docs/tla-transpiler-limitations.md` — Known limitations and workarounds
- `docs/transpiler-config-reference.md` — Complete TOML config options reference
- `docs/dev/verus2tla-design.md` — Internal design of the verus2tla module
- `docs/dev/phase2_roundtrip_design.md` — Round-trip testing framework design
- `CLAUDE.md` — Project overview and build commands
