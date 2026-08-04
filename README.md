# tla-rs (IronFleet Verus)

A Rust implementation of the IronFleet verified distributed systems framework, featuring formally verified Byzantine fault-tolerant consensus protocols using [Verus](https://github.com/verus-lang/verus).

## Features

- **10 Formally Verified Protocols**: RSL (Multi-Paxos RSM), Single-Decree Paxos, Raft,
  EPaxos, PBFT, Chain Replication, Primary-Backup, Vertical Paxos, Two-Phase Commit, and
  Bully Leader Election — plus a distributed Lock service
- **~1000 Verified Functions**: Verified with Verus. Every protocol verifies with 0 errors
  except Raft, whose refinement proof still carries 13 deprecated "Phase 34" `assume`s (a
  known, isolated research gap)
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

- **Verus**: 0.2026.08.02.b677dd5 (latest stable tested; rolling is the same commit)
- **Rust**: 1.97.1 for Verus; a recent stable toolchain for the transpiler
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
scons bin/IronRSLServerUDP.dll
```

> A complete, reproducible spec → generate → verify → compile → run walkthrough for a fresh
> checkout (with toolchain pins and exact commands) lives in
> [`docs/REPRODUCE_WORKFLOW.md`](docs/REPRODUCE_WORKFLOW.md).

## Running

### IronRSL (Multi-Paxos Replicated State Machine)

#### Generate Certificates

Each IronRSL host has a unique public key as an identifier:

```bash
dotnet bin/CreateIronServiceCerts.dll \
    outputdir=certs name=MyCounter type=IronRSL \
    addr1=127.0.0.1 port1=4001 \
    addr2=127.0.0.1 port2=4002 \
    addr3=127.0.0.1 port3=4003
```

#### Run Servers (UDP — recommended)

Run each in a separate terminal:

```bash
export LD_LIBRARY_PATH="$PWD"
dotnet bin/IronRSLServerUDP.dll certs/MyCounter.IronRSL.service.txt certs/MyCounter.IronRSL.server1.private.txt
dotnet bin/IronRSLServerUDP.dll certs/MyCounter.IronRSL.service.txt certs/MyCounter.IronRSL.server2.private.txt
dotnet bin/IronRSLServerUDP.dll certs/MyCounter.IronRSL.service.txt certs/MyCounter.IronRSL.server3.private.txt
```

#### Run Client (UDP)

```bash
dotnet bin/IronRSLClientUDP.dll ip1=127.0.0.1 port1=4001 ip2=127.0.0.1 port2=4002 ip3=127.0.0.1 port3=4003 nthreads=4 duration=10
```

> **Note:** A legacy TCP+SSL variant (`IronRSLServer.dll` / `IronRSLClient.dll`) is
> still available for backward compatibility but delivers ~17x lower throughput.

### Other Protocols (Raft, EPaxos, PBFT, …)

The 8 non-RSL protocols share a unified C# runtime: one server binary
(`IronProtocolServer.dll`) dispatched by a `protocol=<name>` argument, and one client
(`IronGenericClient.dll`). Supported `protocol=` values include `raft`, `epaxos`, `pbft`,
and `primarybackup`.

```bash
# Certificates (name=MyRaft / type=IronProtocol for all generic protocols).
# 3-node cluster (raft, epaxos):
dotnet bin/CreateIronServiceCerts.dll outputdir=bench/certs name=MyRaft type=IronProtocol \
  addr1=127.0.0.1 port1=4001 addr2=127.0.0.1 port2=4002 addr3=127.0.0.1 port3=4003
```

The easiest way to start a cluster, run the client, and print throughput is the helper
script:

```bash
# usage: scripts/bench_generic.sh <protocol> [duration_s] [trials] [nthreads]
scripts/bench_generic.sh raft   8 1 4
scripts/bench_generic.sh epaxos 8 1 4
scripts/bench_generic.sh pbft   8 1 4   # 4-node; see the script for cert setup
```

See [`docs/REPRODUCE_WORKFLOW.md`](docs/REPRODUCE_WORKFLOW.md) for the full run recipe,
including PBFT's 4-node certificate generation.

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

By default the transpiler emits an **in-place `&mut self`** calling convention (enabled per
protocol via `mut_self_types` in the `_transpile.toml`): the post-state is `self` and the
function returns only the sent messages.

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

**Output (exec, `&mut self`):**
```rust
impl CAcceptor {
    exec fn CAcceptorProcess1a(&mut self, inp: &CPacket) -> (sent: Vec<CPacket>)
        requires old(self).well_formed(), inp.well_formed()
        ensures LAcceptorProcess1a(old(self)@, self@, inp@, sent@)
    {
        if ballot_lt(&self.max_bal, &inp.msg.get_bal_1a()) {
            self.max_bal = inp.msg.get_bal_1a().clone();   // in-place mutation, no rebuild
            vec![make_1b_reply_impl(self, inp)]
        } else {
            vec![]
        }
    }
}
```

Protocols whose specs are not amenable to `&mut self` (e.g. **Raft**, whose handlers compute
an intermediate whole-state via a helper) instead use the **functional** convention —
`fn CFoo(s: &CState, ...) -> (CState, Vec<CMsg>)` — selected simply by leaving
`mut_self_types` unset. The choice is pure configuration; there is no protocol-specific logic
in the transpiler.

### Verified Examples

The transpiler includes 25+ verified examples in `transpiler/verus_examples/` covering:
- Init predicates (struct construction, collection initialization)
- Process predicates (conditionals, state updates)
- Quantifier patterns (forall over sequences/maps)
- Collection mutations (seq.update, map.insert, set addition)
- Cross-component dispatch (multi-component state transitions)
- I/O operations (packet construction, broadcast patterns)

### Performance

The transpiler's default `&mut self` calling convention mutates state in place — eliminating
the per-request "rebuild the whole struct + clone every field" cost of the earlier functional
style. On RSL this closes most of the gap to a fully hand-tuned implementation.

RSL over UDP (localhost, 3 nodes, 32 client threads, `max_batch_size=32`):

| Configuration | Throughput | Notes |
|--------------|-----------|-------|
| Pre-optimization (functional rebuild) | ~16K ops/s | Phase 46 baseline |
| **Transpiler + `&mut self`** | **~46–54K ops/s** | current codegen (~0.85 ms latency) |
| Hand-tuned reference (Sushant) | ~60K ops/s | `&mut self` end-to-end, hand-written |

So the auto-generated code reaches roughly **80–90% of a full hand-tune** — a ~3× improvement
over the pre-optimization baseline. (Earlier READMEs credited "field-level `Arc<T>` wrapping";
that approach was superseded by `&mut self` in Phases 47–49 and the Arc wrapping was removed
from the RSL hot fields. `arc_wrap_fields` still exists for functional-convention protocols
but conflicts with — and is auto-cleared under — `mut_self_types`.)

Other protocols run end-to-end but are not perf-tuned; sample localhost smoke numbers
(hardware- and duration-dependent — yours will differ):

| Protocol | Nodes | Throughput (localhost smoke) |
|----------|-------|------------------------------|
| RSL | 3 | ~46K ops/s (32 clients) |
| EPaxos | 3 | ~15K ops/s (4 clients, 8 s) |
| Raft | 3 | ~11K ops/s (4 clients, 8 s) |
| PBFT | 4 | ~2.5K ops/s (4 clients, 8 s; BFT 3-phase) |

To select the calling convention, set `mut_self_types` in the protocol's `_transpile.toml`:

```toml
mut_self_types = ["CProposer"]   # emit &mut self methods on CProposer
```

See `transpiler/docs/EFFICIENT_EMIT.md` for the `&mut self`-vs-functional decision matrix and
`docs/REPRODUCE_WORKFLOW.md` for how to reproduce these measurements.

### Documentation

- `transpiler/docs/ANNOTATION_FORMAT.md` - Mode annotation syntax
- `transpiler/docs/PATTERNS.md` - Supported transformation patterns
- `transpiler/docs/EFFICIENT_EMIT.md` - `&mut self` vs functional convention, perf history
- `transpiler/docs/LIMITATIONS.md` - Known limitations, workarounds, and performance analysis
- `transpiler/docs/MIGRATION_GUIDE.md` - Migration from manual implementations
- `docs/REPRODUCE_WORKFLOW.md` - End-to-end spec → generate → verify → compile → run guide

## Code Organization

### Naming Conventions

- `*_s.rs` - Spec/abstract modules (protocol layer)
- `*_i.rs` - Implementation/concrete modules
- `L*` prefix - Logical/protocol types (e.g., `LReplica`, `LProposer`)
- `C*` prefix - Concrete types (e.g., `CConstants`, `CMessage`)

### Key Directories

| Directory | Purpose |
|-----------|---------|
| `src/protocol/<P>/` | Abstract protocol specs and proofs (RSL, Raft, EPaxos, PBFT, …) |
| `src/implementation/<P>/` | Verified concrete implementation + hand-written I/O host |
| `src/generated/<P>/` | Transpiler-generated types and functions (do not hand-edit) |
| `src/services/<P>/` | Service entry points |
| `src/common/native/io_s.rs` | Network client with marshalling (~17K LOC) |
| `csharp/` | C# runtime and deployable services (~45K LOC) |
| `transpiler/` | Spec-to-exec transpiler (~10K LOC) |
| `scripts/` | Utility scripts (regeneration, benchmarks) |

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
- `&mut self` codegen cannot yet lift an intermediate whole-state (`s_mid = helper(s, …)`)
  into `*self = s_mid`; protocols using that pattern (Raft) stay on the functional convention
- RSL is not fully auto-generated: 10 functions have hand-written bodies (`skip_functions`);
  see `transpiler/docs/REGEN_WORKFLOW.md`

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
