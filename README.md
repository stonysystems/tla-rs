# tla-rs (IronFleet Verus)

A Rust implementation of the IronFleet verified distributed systems framework, featuring formally verified Byzantine fault-tolerant consensus protocols using [Verus](https://github.com/verus-lang/verus).

## Features

- **Formally Verified Protocols**: Paxos-based RSL (Replicated State Machine) and distributed Lock service
- **669 Verified Functions**: Main codebase fully verified with Verus (0 errors)
- **Spec-to-Exec Transpiler**: Automatic transformation of TLA-style specifications to verified implementations (~10K LOC)
- **C# FFI Integration**: Production-ready networking layer via .NET runtime

## Architecture

```
┌─────────────────────────────────────────────┐
│  C# .NET Layer (I/O & Networking)           │
│  Trusted runtime for network operations     │
└──────────────────┬──────────────────────────┘
                   │ FFI
┌──────────────────▼──────────────────────────┐
│  Rust/Verus Layer (Verified Protocol)       │
├─────────────────────────────────────────────┤
│ src/services/       - Entry points          │
│ src/implementation/ - Concrete impls        │
│ src/protocol/       - Specs & proofs        │
│ src/common/         - Utilities & I/O       │
└─────────────────────────────────────────────┘
```

## Requirements

- **Verus**: v0.2026.01.14 or compatible (tested with 0.2026.01.14.88f7396)
- **Rust**: 1.80.1+ (tested with 1.92.0)
- **.NET 6.0 SDK**: https://dotnet.microsoft.com/download
- **scons**: `pip install scons`
- **Python 3**: For running scons

## Building

```bash
# Build and verify all Rust code with Verus
scons --verus-path="$VERUS_PATH"

# Build only C# projects (skip Verus verification)
scons --skip-verus

# Build specific target
scons bin/IronRSLServer.dll
```

## Running

### IronRSL (Paxos-based Replicated State Machine)

#### Generate Certificates

Each IronRSL host has a unique public key as an identifier:

```bash
dotnet bin/CreateIronServiceCerts.dll \
    outputdir=certs name=MyCounter type=IronRSL \
    addr1=127.0.0.1 port1=4001 \
    addr2=127.0.0.1 port2=4002 \
    addr3=127.0.0.1 port3=4003
```

#### Run Servers

Run each in a separate terminal:

```bash
dotnet bin/IronRSLServer.dll certs/MyCounter.IronRSL.service.txt certs/MyCounter.IronRSL.server1.private.txt
dotnet bin/IronRSLServer.dll certs/MyCounter.IronRSL.service.txt certs/MyCounter.IronRSL.server2.private.txt
dotnet bin/IronRSLServer.dll certs/MyCounter.IronRSL.service.txt certs/MyCounter.IronRSL.server3.private.txt
```

### IronLock (Distributed Lock Service)

#### Generate Certificates

```bash
dotnet bin/CreateIronServiceCerts.dll \
    outputdir=certs name=MyLock type=IronLock \
    addr1=127.0.0.1 port1=4001 \
    addr2=127.0.0.1 port2=4002 \
    addr3=127.0.0.1 port3=4003
```

#### Run Servers

Note: The protocol starts once server1 is online.

```bash
dotnet bin/IronLockServer.dll certs/MyLock.IronLock.service.txt certs/MyLock.IronLock.server2.private.txt
dotnet bin/IronLockServer.dll certs/MyLock.IronLock.service.txt certs/MyLock.IronLock.server3.private.txt
dotnet bin/IronLockServer.dll certs/MyLock.IronLock.service.txt certs/MyLock.IronLock.server1.private.txt
```

## Transpiler

The project includes a spec-to-implementation transpiler that converts Verus `spec fn` predicates (TLA-style specifications) into verified `exec fn` implementations.

### Usage

```bash
cd transpiler

# Run transpiler tests
cargo test

# Transpile a spec file
cargo run -- --input spec.rs --annotations spec.automan --output impl.rs

# Verify generated code
verus impl.rs
```

### Transformation Example

**Input (spec):**
```rust
spec fn LAcceptorProcess1a(s: LAcceptor, s_: LAcceptor, inp: RslPacket, sent: Seq<RslPacket>) -> bool {
    if BalLt(s.max_bal, inp.msg->bal_1a) {
        &&& s_.max_bal == inp.msg->bal_1a
        &&& s_.votes == s.votes
        &&& sent == seq![make_1b_reply(s, inp)]
    } else {
        &&& s_ == s
        &&& sent == Seq::empty()
    }
}
```

**Output (exec):**
```rust
exec fn CAcceptorProcess1a(s: &CAcceptor, inp: &CRslPacket) -> (CAcceptor, Vec<CRslPacket>)
    requires s.well_formed(), inp.well_formed()
    ensures LAcceptorProcess1a(s@, result.0@, inp@, result.1@)
{
    if ballot_lt(&s.max_bal, &inp.msg.get_bal_1a()) {
        (CAcceptor { max_bal: inp.msg.get_bal_1a().clone(), votes: s.votes.clone() },
         vec![make_1b_reply_impl(s, inp)])
    } else {
        (s.clone(), vec![])
    }
}
```

### Verified Examples

The transpiler includes 25+ verified examples in `transpiler/verus_examples/` covering:
- Init predicates (struct construction, collection initialization)
- Process predicates (conditionals, state updates)
- Quantifier patterns (forall over sequences/maps)
- Collection mutations (seq.update, map.insert, set addition)
- Cross-component dispatch (multi-component state transitions)
- I/O operations (packet construction, broadcast patterns)

### Documentation

- `transpiler/docs/ANNOTATION_FORMAT.md` - Mode annotation syntax
- `transpiler/docs/PATTERNS.md` - Supported transformation patterns
- `transpiler/docs/LIMITATIONS.md` - Known limitations and workarounds
- `transpiler/docs/MIGRATION_GUIDE.md` - Migration from manual implementations

## Code Organization

### Naming Conventions

- `*_s.rs` - Spec/abstract modules (protocol layer)
- `*_i.rs` - Implementation/concrete modules
- `L*` prefix - Logical/protocol types (e.g., `LReplica`, `LProposer`)
- `C*` prefix - Concrete types (e.g., `CConstants`, `CMessage`)

### Key Directories

| Directory | Purpose |
|-----------|---------|
| `src/protocol/RSL/` | Abstract Paxos protocol specs and proofs (~6K LOC) |
| `src/protocol/lock/` | Abstract Lock protocol specs |
| `src/implementation/RSL/` | Verified concrete RSL implementation (~6K LOC) |
| `src/implementation/lock/` | Verified concrete Lock implementation |
| `src/generated/RSL/` | Auto-generated RSL types and functions |
| `src/common/native/io_s.rs` | Network client with marshalling (~17K LOC) |
| `csharp/` | C# runtime and deployable services (~45K LOC) |
| `transpiler/` | Spec-to-exec transpiler (~10K LOC) |
| `scripts/` | Utility scripts (e.g., regeneration) |

## Verus Patterns

### Function Types

```rust
verus! {
    spec fn abstract_spec() -> bool;           // Pure mathematical (ghost)
    proof fn lemma_about_spec() { ... }        // Proof-only
    exec fn concrete_impl() { ... }            // Executable code
}
```

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

## Known Limitations

- Verus spec functions cannot use mutable variables or iteration (use recursion)
- Verus maps/sets are infinite by default (need `.dom().finite()` bounds)
- Cannot add conditions on trait implementations (copy clauses as workaround)
- Marshalling lacks spec function for non-deserializable check

## Code Attribution

Some code borrowed from [IronKV](https://github.com/verus-lang/verified-ironkv):
- NetClient code (`src/common/framework/native/io_s.rs`)
- Verus extra utilities (`src/verus_extra/...`)
- C# I/O framework (modified)
- Binding to C# (`src/lib.rs`)
- Common marshalling library (`src/implementation/common/marshalling.rs`)

The transpiler is inspired by [AutoMan](https://github.com/stonysystems/automan) (for Dafny), reimplemented in Rust for Verus.

## License

MIT License - see [LICENSE](LICENSE)
