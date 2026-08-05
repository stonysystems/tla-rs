# CLAUDE.md - tla-rs Project Guide

## Important: Generated Code Policy

The rule is about **provenance, not path**. `src/generated/` holds two kinds of code, and
they carry different rules.

**Transpiler-emitted code — do NOT hand-edit.** Anything the transpiler actually produces must
keep coming from the transpiler. To add proofs or fix assumes there, improve the proof
generation in `transpiler/src/` and regenerate. Do NOT delegate to manual implementation code
or use "clone-delegate-extract" patterns. An edit here is silently lost on the next
regeneration, which is the whole reason for the rule. Read `TODO.md` Phase 12 for the full plan.

**Hand-written bodies preserved inside generated files — edit them directly.** Functions listed
in `skip_functions`, and the helpers that live in a generated file without appearing in any
config, are never emitted: regeneration copies them through verbatim. The divergence risk the
rule guards against does not exist for them, so treating them as untouchable only blocks work
(it stalled 53 Phase 54 trigger annotations) without protecting anything.

Do not decide which kind you are looking at by reading the config, and do not infer it from a
function *not* being listed somewhere — that inference was made once and was wrong for all 74
functions it covered. Measure it:

```bash
python3 scripts/classify_trigger_notes.py --fresh-dir <dir>   # diffs against fresh transpiler output
```

If a function does not appear in fresh transpiler output, it is hand-maintained and you may
edit it in place. If it does, change the transpiler instead.

## Project Overview

tla-rs is a Rust implementation of the IronFleet verified distributed systems framework, focused on Replicated State Machine (RSM) protocols. It provides formally verified implementations of Byzantine fault-tolerant consensus protocols using Verus (a deductive program verifier for Rust).

## Build Commands

```bash
# Build and verify all Rust code with Verus
scons --verus-path=/path/to/verus

# Build only C# projects
scons --skip-verus

# Build specific target
scons bin/IronRSLServerUDP.dll
```

**Requirements:**
- Verus verifier (tested: release/0.2026.08.02.b677dd5; rolling is the same commit)
- rustc 1.97.1
- .NET 6.0 SDK
- scons (`pip install scons`)

## Running Services

```bash
# Generate certificates
dotnet bin/CreateIronServiceCerts.dll outputdir=certs name=MyService ...

# Run RSL server (UDP — default)
export LD_LIBRARY_PATH="$PWD"
dotnet bin/IronRSLServerUDP.dll <service.txt> <private_key.txt>

# Run RSL client (UDP)
dotnet bin/IronRSLClientUDP.dll ip1=... port1=... nthreads=4 duration=10

# Legacy TCP+SSL variant (slower, kept for backward compat)
# dotnet bin/IronRSLServer.dll <service.txt> <private_key.txt>
```

## Architecture

```
┌─────────────────────────────────────────────┐
│  C# .NET Layer (I/O & Networking)           │
│  - csharp/Common/IoFramework.cs             │
│  - Trusted runtime for network operations   │
└──────────────────┬──────────────────────────┘
                   │ (FFI)
┌──────────────────▼──────────────────────────┐
│  Rust/Verus Layer (Verified Protocol)       │
├─────────────────────────────────────────────┤
│ src/services/     - Entry points            │
│ src/implementation/ - Concrete impls        │
│ src/protocol/     - Specs & proofs          │
│ src/common/       - Utilities & I/O         │
└─────────────────────────────────────────────┘
```

## Code Organization

### Naming Conventions
- `*_s.rs` - Spec/abstract modules (protocol layer)
- `*_i.rs` - Implementation/concrete modules
- `L*` prefix - Logical/protocol types (e.g., `LReplica`, `LProposer`)
- `C*` prefix - Concrete types (e.g., `CConstants`, `CMessage`)

### Key Directories
- `src/protocol/RSL/` - Abstract protocol specs and proofs (~6K LOC)
- `src/implementation/RSL/` - Verified concrete implementation (~6K LOC)
- `src/common/native/io_s.rs` - Network client with marshalling
- `csharp/` - C# runtime and deployable services

## Verus Patterns

### Function Types
```rust
verus! {
    spec fn abstract_spec() -> bool;           // Pure mathematical (ghost)
    proof fn lemma_about_spec() { ... }        // Proof-only
    exec fn concrete_impl() { ... }            // Executable code
}
```

### Annotations
- `#[verifier(external)]` - Trusted FFI, not verified
- `#[verifier(external_body)]` - Implementation trusted, interface verified
- `#[verus::trusted]` - Mark entire module as trusted

### View Trait
Maps concrete types to ghost types for verification:
```rust
// struct@ syntax calls the view function
let ghost_replica = replica@;
```

### Triggers Workaround
For arithmetic in triggers, use extra variables:
```rust
// Instead of: forall|i: int| 0 <= i < len ==> f(i + 1)
// Use: forall|i: int, j: int| j == i + 1 && 0 <= i < len ==> f(j)
```

## Key Files

| File | Purpose |
|------|---------|
| `src/protocol/RSL/replica.rs` | Abstract replica state machine |
| `src/protocol/RSL/proposer.rs` | Ballot/proposal logic (~22K LOC) |
| `src/implementation/RSL/ReplicaImpl.rs` | Concrete replica impl |
| `src/implementation/RSL/marshalling.rs` | Message serialization |
| `src/common/native/io_s.rs` | Network client (~17K LOC) |
| `csharp/Common/IoFramework.cs` | C# I/O framework (~45K LOC) |

## Protocol Components

The RSL protocol implements Multi-Paxos with:
- **Proposer** - Generates ballots and proposals
- **Acceptor** - Stores votes and accepts ballots
- **Learner** - Learns committed values from quorum
- **Executor** - Applies committed operations to state machine
- **Election** - Leader election via ballot numbers

## Known Issues

See `hacks.md` for Verus workarounds and `notes.md` for development notes.

**Key limitations:**
- Verus spec functions cannot use mutable variables or iteration (use recursion)
- Verus maps/sets are infinite by default (need `.dom().finite()` bounds)
- Cannot add conditions on trait implementations (copy clauses as workaround)
