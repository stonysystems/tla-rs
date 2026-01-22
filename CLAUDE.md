# CLAUDE.md - tla-rs Project Guide

## Project Overview

tla-rs is a Rust implementation of the IronFleet verified distributed systems framework, focused on Replicated State Machine (RSM) protocols. It provides formally verified implementations of Byzantine fault-tolerant consensus protocols using Verus (a deductive program verifier for Rust).

## Build Commands

```bash
# Build and verify all Rust code with Verus
scons --verus-path=/path/to/verus

# Build only C# projects
scons --skip-verus

# Build specific target
scons bin/IronRSLServer.dll
```

**Requirements:**
- Verus verifier (tested: release/rolling/0.2024.09.05.29e4da0)
- rustc 1.80.1
- .NET 6.0 SDK
- scons (`pip install scons`)

## Running Services

```bash
# Generate certificates
dotnet bin/CreateIronServiceCerts.dll outputdir=certs name=MyService ...

# Run RSL server
dotnet bin/IronRSLServer.dll <service.txt> <private_key.txt>

# Run RSL client
dotnet bin/IronRSLClient.dll
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
