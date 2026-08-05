# tla-rs: IronFleet and AutoMan in Verus

`tla-rs` lets you write TLA-style distributed-system specifications in
Rust/[Verus](https://github.com/verus-lang/verus), then automatically derive executable Rust
implementations and the proof obligations connecting them to their specifications. It is
primarily a reimplementation of the systems and methodology described in two papers:

- [**IronFleet: Proving Practical Distributed Systems Correct**](https://doi.org/10.1145/2815400.2815428)
  ([code](https://github.com/microsoft/Ironclad/tree/main/ironfleet)) — the verified
  distributed-systems framework, refinement methodology, and Multi-Paxos replicated state
  machine on which this project is based.
- [**AutoMan: Facilitating Verified Distributed Systems Development Through Automatic Code
  Generation and Manual Optimizations**](https://doi.org/10.1145/3731569.3764822)
  ([code](https://github.com/stonysystems/automan)) — the workflow for generating executable
  implementations and their verification obligations from protocol specifications.

Both original systems use Dafny. This project re-expresses their core ideas in verified Rust:
IronFleet's specifications, proofs, and runtime structure are ported to Verus, while AutoMan's
specification-to-implementation workflow is reimplemented as a Rust/Verus transpiler.

The repository also extends that foundation with additional distributed protocols, bidirectional
TLA+/Verus translation, source-first and DPOR-based model checking, mutation-oriented code
generation, and deployable C# networking/runtime integration.

## Quick Start: From a Spec to a Program

Here is a complete counter transition written as a TLA-style relation in Verus:

```rust
verus! {
    pub open spec fn LInit(value: int) -> bool {
        value == 0
    }

    pub open spec fn LIncrement(value: int, value_: int) -> bool {
        value_ == value + 1
    }
}
```

The accompanying AutoMan annotation marks supplied inputs with `+` and outputs for the
transpiler to synthesize with `-`:

```text
LInit(-);
LIncrement(+, -);
```

From the repository root, generate the executable functions, verify them, compile them, and
run the result:

```bash
cargo run --manifest-path transpiler/Cargo.toml -- \
  -i examples/quickstart/counter_spec.rs \
  -a examples/quickstart/counter_spec.automan \
  -c examples/quickstart/counter_transpile.toml \
  -o examples/quickstart/counter_gen.rs

"$VERUS_PATH" --compile examples/quickstart/main.rs -o /tmp/tla-rs-counter
/tmp/tla-rs-counter
```

The generated `CInit` and `CIncrement` functions have `ensures` clauses tying their concrete
`i64` results back to `LInit` and `LIncrement`. The final output is:

```text
verification results:: 2 verified, 0 errors
Counter: 0 -> 1
```

All source, annotation, configuration, generated code, and runner files are in
[`examples/quickstart/`](examples/quickstart/). CI regenerates the code, rejects proof shortcuts,
and verifies, compiles, and runs this example.

## Features

- **10 Formally Verified Protocols**: RSL (Multi-Paxos RSM), Single-Decree Paxos, Raft,
  EPaxos, PBFT, Chain Replication, Primary-Backup, Vertical Paxos, Two-Phase Commit, and
  Bully Leader Election
- **Spec-to-Exec Transpiler**: Automatic transformation of TLA-style specifications to verified implementations
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
│ src/generated/      - Transpiler output     │
│ src/protocol/       - Specs & proofs        │
│ src/common/         - Utilities & I/O       │
└─────────────────────────────────────────────┘
```

## Requirements

- **Verus**: 0.2026.08.02.b677dd5 (latest stable tested; rolling is the same commit).
  The release binaries link against glibc 2.39, so verification needs Ubuntu 24.04 or newer.
- **Rust**: 1.97.1 for Verus; a recent stable toolchain for the transpiler
- **.NET 6.0 SDK**: https://dotnet.microsoft.com/download
- **scons**: `pip install scons`
- **Python 3**: For running scons

## Verification

To check the correctness claims yourself, run Verus over the whole crate.

```bash
scons --verus-path="$VERUS_PATH" --skip-dotnet
```

All 10 protocols live in one crate rooted at `src/lib.rs`, so a single pass covers every
protocol's spec, refinement proof, transpiler-generated implementation, and service entry
point. Expect:

```
verification results:: 1044 verified, 0 errors
```

This takes about 2 minutes on CI hardware.
The same pass runs on every push (`CI / Verus Verification`).

## Building

```bash
# Verify with Verus and build the C# services
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

The 9 non-RSL protocols share a unified C# runtime: one server binary
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
- `transpiler/docs/PATTERNS.md` - Supported transformation patterns, with runnable examples
  in `transpiler/verus_examples/`
- `transpiler/docs/EFFICIENT_EMIT.md` - `&mut self` vs functional convention, perf history
- `transpiler/docs/LIMITATIONS.md` - Known limitations, workarounds, and performance analysis
- `transpiler/docs/MIGRATION_GUIDE.md` - Migration from manual implementations
- `docs/REPRODUCE_WORKFLOW.md` - End-to-end spec → generate → verify → compile → run guide

## Code Organization

Types are prefixed by layer: `L*` for logical/protocol types (`LReplica`, `LProposer`) and
`C*` for their concrete counterparts (`CConstants`, `CMessage`).

| Directory | Purpose |
|-----------|---------|
| `src/protocol/<P>/` | Abstract protocol specs and proofs (RSL, Raft, EPaxos, PBFT, …) |
| `src/implementation/<P>/` | Verified concrete implementation + hand-written I/O host |
| `src/generated/<P>/` | Transpiler-generated types and functions (do not hand-edit) |
| `src/services/<P>/` | Service entry points |
| `src/common/native/io_s.rs` | Network client with marshalling |
| `csharp/` | C# runtime and deployable services (~6.6K LOC) |
| `transpiler/` | Spec-to-exec transpiler (~135K LOC) |
| `scripts/` | Utility scripts (regeneration, benchmarks) |

## Known Limitations

- Raft's refinement proof still carries a few `assume`s, mostly around leader completeness;
  every other protocol's proof is assumption-free
- RSL is not fully auto-generated. Of the 30 entries in its `skip_functions` lists:
  **10 are a deliberate trust boundary** — the host event loop and its packet/clock
  dispatch, which IronFleet also leaves trusted; **15 have proven hand-written
  implementations** in `acceptor_manual.rs` / `executor_manual.rs`; and **8 are a genuine
  transpiler gap** — quantifier-defined map constructions, recursive sequence walks, and
  composite send-actions. Full RSL regeneration is not a goal. See
  `docs/rsl-skip-functions.md` for the per-function classification and
  `transpiler/docs/REGEN_WORKFLOW.md` for the workflow
- `&mut self` codegen cannot handle intermediate whole-state assignments; protocols using
  that pattern (Raft) stay on the slower functional convention
- Marshalling lacks a spec function for the non-deserializable check

## Code Attribution

Some code borrowed from [IronKV](https://github.com/verus-lang/verified-ironkv):
- NetClient code (`src/common/native/io_s.rs`)
- Verus extra utilities (`src/verus_extra/...`)
- C# I/O framework (modified)
- Binding to C# (`src/lib.rs`)
- Common marshalling library (`src/implementation/common/marshalling.rs`)

The transpiler reimplements the [AutoMan](https://github.com/stonysystems/automan) workflow
for Rust and Verus. The additional protocols, translation/model-checking tools, and Rust-specific
code-generation optimizations are extensions developed in this repository.

## License

MIT License - see [LICENSE](LICENSE)
