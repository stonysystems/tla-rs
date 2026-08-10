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
TLA+/Verus translation, source-first model checking, mutation-oriented code generation, and
deployable C# networking/runtime integration.

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

The Rust functions above are relations: their signatures do not say which parameters
are known before execution. That dataflow is declared separately in
`examples/quickstart/counter_spec.automan`:

```text
module counter_spec {
    LInit(-);
    LIncrement(+, -);
}
```

Each marker corresponds positionally to a parameter in the Rust relation. `+` marks an
input supplied to the generated function, while `-` marks an output that function must
compute. Thus `LInit(value)` with `LInit(-)` generates a zero-argument `CInit` returning
the initial value, and `LIncrement(value, value_)` with `LIncrement(+, -)` generates
`CIncrement(value)` returning the new value represented by `value_`.

The modes can also live inline in the spec itself, as a named `// @automan` comment
directly above each function — `// @automan predicate(value: in, value_: out)` — in which
case no sidecar file is needed and a parameter rename or reorder fails loudly instead of
silently rebinding the modes. The maintained protocols under `src/protocol/` use the
inline form; this example keeps the sidecar to demonstrate that path, and
`migrate-inline` converts one form to the other.

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

## What is included

- Ten distributed protocols: RSL (Multi-Paxos), Single-Decree Paxos, Raft, EPaxos,
  PBFT, Chain Replication, Primary-Backup, Vertical Paxos, Two-Phase Commit, and
  Bully leader election.
- A spec-to-executable transpiler that generates Rust implementations and Verus
  refinement contracts.
- TLA+/Verus translation, bounded model checking, and a deployable C#/.NET networking runtime.

## Requirements

Ubuntu 24.04 or newer — the Verus release binaries link against glibc 2.39. On an older
distribution, build Verus from source instead.

```bash
# rustup — must be rustup, not just a matching rustc: the verus launcher shells out to it
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
rustup toolchain install 1.97.1

# Verus 0.2026.08.02.b677dd5 — the zip drops the executable bit, hence chmod
V=0.2026.08.02.b677dd5
wget https://github.com/verus-lang/verus/releases/download/release/$V/verus-$V-x86-linux.zip
unzip -q verus-$V-x86-linux.zip -d ~/ && mv ~/verus-x86-linux ~/verus
chmod +x ~/verus/verus && export VERUS_PATH=~/verus/verus

sudo apt install scons          # `pip install scons` is blocked by PEP 668 on 24.04
```

.NET 6.0 SDK is needed only to build and run the services, not to verify.
See [*The tla-rs Book*](docs/tla-rs-book.md), Chapters 2 and 16, for complete
installation and development-environment guidance.

## Verify and build

```bash
# Verify the Rust/Verus crate
scons --verus-path="$VERUS_PATH" --skip-dotnet

# Verify Rust and build the C# services
scons --verus-path="$VERUS_PATH"

# Build C# only, reusing an existing native library
scons --skip-verus
```

The Verus invocation covers all ten protocol modules in the crate. The current full-crate
gate reports `1048 verified, 0 errors`, with no warnings or automatically chosen trigger
notes, and runs on every push. Verification remains relative to the declared trusted and
externally implemented boundaries; Appendix F of the book records those boundaries and
the remaining proof escapes.

## Running a service

After building, generate a three-node RSL configuration:

```bash
dotnet bin/CreateIronServiceCerts.dll \
  outputdir=certs name=MyCounter type=IronRSL \
  addr1=127.0.0.1 port1=4001 \
  addr2=127.0.0.1 port2=4002 \
  addr3=127.0.0.1 port3=4003
```

Set `LD_LIBRARY_PATH="$PWD"`, then start one UDP server per node using the generated
service file and corresponding private-key file:

```bash
dotnet bin/IronRSLServerUDP.dll \
  certs/MyCounter.IronRSL.service.txt \
  certs/MyCounter.IronRSL.server1.private.txt
```

Run a client from another terminal:

```bash
dotnet bin/IronRSLClientUDP.dll \
  ip1=127.0.0.1 port1=4001 \
  ip2=127.0.0.1 port2=4002 \
  ip3=127.0.0.1 port3=4003 \
  nthreads=4 duration=10
```

The other protocols use the shared `IronProtocolServer.dll`; Raft, Primary-Backup,
PBFT, and EPaxos also have workload support through `scripts/bench_generic.sh`.
Chapter 10 of the book contains the complete service recipes.

## Performance

Generated transitions support functional state updates with selective `Arc` sharing
and opt-in mutable-receiver lowering for eligible hot paths. RSL uses mutable lowering
for selected actions, avoiding unnecessary whole-state reconstruction while preserving
the same Verus postconditions.

This repository does not currently publish an RSL-versus-IronFleet or
generated-versus-hand-tuned speedup: the available historical measurements are not a
controlled, reproducible comparison. The benchmark requirements and runtime profiling
workflow are documented in [Chapter 25 of the book](docs/tla-rs-book.md) and the
[generated-code performance record](transpiler/docs/EFFICIENT_EMIT.md).

## Documentation

[*The tla-rs Book*](docs/tla-rs-book.md) is the primary documentation:

- Part I is the user guide: specifications, generation, verification, model checking,
  TLA+ interchange, and running services.
- Part II is the developer guide: architecture, trust boundaries, transpiler internals,
  generated-code maintenance, testing, and releases.
- The appendices contain the CLI, annotation, configuration, support, evidence, and
  proof-pattern references.

Capability claims tied directly to tests remain in
[`docs/model_checker_status.md`](docs/model_checker_status.md), while
[`docs/clean_tla_subset.md`](docs/clean_tla_subset.md) defines the normative clean-TLA
projection contract. RSL's trusted, proved hand-written, and unsupported generated paths
are classified in [`docs/rsl-skip-functions.md`](docs/rsl-skip-functions.md).

## Contributing

Do not hand-edit transpiler-emitted code: change the protocol source, its
`// @automan` annotations, the configuration, or the transpiler, and
regenerate. Files under `src/generated/` can also carry hand-written bodies
that regeneration deliberately preserves (RSL's `skip_functions`, classified
in [`docs/rsl-skip-functions.md`](docs/rsl-skip-functions.md)) — those are
edited in place. When unsure which kind a function is, diff against fresh
transpiler output rather than guessing. See
[`AGENTS.md`](AGENTS.md) for project rules, the book's developer guide for the normal
workflow, and [`TODO.md`](TODO.md) for current work and known gaps.

## Attribution and license

Parts of the native I/O, Verus utilities, marshalling, FFI, and C# runtime were adapted
from [IronKV](https://github.com/verus-lang/verified-ironkv). The transpiler reimplements
the [AutoMan](https://github.com/stonysystems/automan) workflow for Rust and Verus.

Licensed under the [MIT License](LICENSE).
