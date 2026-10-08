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

## Verified refinement theorems

The two flagship protocols carry machine-checked refinement proofs, verified end to end by Verus:

- **RSL (Multi-Paxos)** —
  [`lemma_GetBehaviorRefinement`](src/protocol/RSL/refinement_proof/refinement.rs):
  every behavior of the distributed protocol refines an abstract replicated
  state machine — the IronFleet theorem, mechanized in Verus.
- **Raft** —
  [`lemma_refinement_correct`](src/protocol/Raft/refinement_proof/refinement.rs):
  every valid distributed behavior refines a sequential state machine over the
  committed log (no two reachable servers commit different entries at the same
  index), including dynamic membership changes via joint consensus — a
  property IronFleet's original development did not cover.

The repository also extends that foundation with additional distributed protocols, bidirectional
TLA+/Verus translation, source-first model checking, mutation-oriented code generation, and
deployable services with a native Rust+Lion runtime, configuration tool, and workload client.

## Quick Start: From a Spec to a Program

Here is a complete counter transition written as a TLA-style relation in Verus
([`examples/quickstart/counter_spec.rs`](examples/quickstart/counter_spec.rs)):

```rust
verus! {
    // @automan predicate(value: out)
    pub open spec fn LInit(value: int) -> bool {
        value == 0
    }

    // @automan predicate(value: in, value_: out)
    pub open spec fn LIncrement(value: int, value_: int) -> bool {
        value_ == value + 1
    }
}
```

The functions are relations: their signatures do not say which parameters are
known before execution. The `// @automan` directive above each function
declares that dataflow — `in` parameters are supplied to the generated
function, `out` parameters are what it must compute. Thus `LInit` generates a
zero-argument `CInit` returning the initial value, and `LIncrement` generates
`CIncrement(value)` returning the new value represented by `value_`. Bindings
are matched by parameter name, so renaming or reordering a parameter without
updating the directive is an error rather than a silent meaning change.

From the repository root, generate the executable functions, verify them, compile them, and
run the result:

```bash
cargo run --manifest-path transpiler/Cargo.toml -- \
  -i examples/quickstart/counter_spec.rs \
  -c examples/quickstart/counter_transpile.toml \
  -o examples/quickstart/counter_gen.rs

"$VERUS_PATH" --compile examples/quickstart/main.rs -o /tmp/tla-rs-counter
/tmp/tla-rs-counter
```

Inline directives are the default. As an alternative, the same modes can live
in a separate `.automan` sidecar file passed with `-a`, using positional
`+`/`-` markers — `LInit(-); LIncrement(+, -);` inside a `module counter_spec
{ ... }` block. The sidecar form predates the inline form and remains fully
supported; `migrate-inline` converts a sidecar into inline directives, and a
function annotated in both places must agree.

The generated `CInit` and `CIncrement` functions have `ensures` clauses tying their concrete
`i64` results back to `LInit` and `LIncrement`. The final output is:

```text
verification results:: 2 verified, 0 errors
Counter: 0 -> 1
```

All source (with its inline annotations), configuration, generated code, and runner files are in
[`examples/quickstart/`](examples/quickstart/). CI regenerates the code, rejects proof shortcuts,
and verifies, compiles, and runs this example.

## What is included

- Ten distributed protocols: RSL (Multi-Paxos), Single-Decree Paxos, Raft, EPaxos,
  PBFT, Chain Replication, Primary-Backup, Vertical Paxos, Two-Phase Commit, and
  Bully leader election.
- A spec-to-executable transpiler that generates Rust implementations and Verus
  refinement contracts.
- A native Rust+Lion server for all ten protocols, native configuration/identity
  generation, and native workload clients. No C# or .NET is required on this path.

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

sudo apt install scons pkg-config libssl-dev
```

The native runtime uses Linux batched UDP syscalls and OpenSSL for identity generation
and TLS. Lion is pinned in the runtime Cargo manifests; lockfiles are checked in.
See [*The tla-rs Book*](docs/tla-rs-book.md), Chapters 2 and 16, for complete
installation and development-environment guidance.

## Verify and build

```bash
# Verify the protocol library and build all three native executables
scons --verus-path="$VERUS_PATH"

# Equivalent native-only build without SCons
scripts/build_lion_runtime.sh

# Explicitly skip proof checking during runtime iteration
scripts/build_lion_runtime.sh --no-verify
```

The Verus invocation covers all ten protocol modules in the crate. The current full-crate
gate reports `4101 verified, 0 errors`, with no warnings or automatically chosen trigger
notes. It includes the TLAPS-Bench ports, whose published results
([reports/tlaps_bench_manual](reports/tlaps_bench_manual/README.md)) come from verifying
them as their own crate with `scripts/report_tlaps_bench_manual.py`.
Verification remains relative to the declared trusted boundaries:
the native scheduler, marshalling, Lion's OS-facing glue, configuration, and TLS
integration are runtime-tested, not covered by an end-to-end service theorem.

For service configuration, deployment, client workloads, and transport options,
see [Chapter 10 of *The tla-rs Book*](docs/tla-rs-book.md#run-a-three-node-rsl-service).

## Performance

Generated transitions support functional state updates with selective `Arc` sharing
and opt-in mutable-receiver lowering for eligible hot paths. RSL uses mutable lowering
for selected actions, avoiding unnecessary whole-state reconstruction while preserving
the same Verus postconditions.

Native measurements and methodology are recorded in the
[Lion runtime report](reports/benchmarks/LION_RUNTIME_BENCHMARK_COMPARISON.md).
`scripts/bench_rsl_runtime.sh` defaults to Lion's unbatched RSL methodology:
plaintext TCP with `TCP_NODELAY`, two clients connected to every replica, a
1-second request timeout, three seconds of initial idle time, five seconds of
active warmup, three 30-second measured trials, and unpinned versus
one-physical-core-per-replica configurations.
RSL defaults are one request per batch, a 1,000-entry log bound, 1,000 ms baseline
view timeout, 100 ms heartbeat, and 10 ms partial-batch timer. The timer no longer
delays a lone request. UDP and TLS remain supported.

The default benchmark is native-only. An explicit, isolated reference can be built
with `scripts/build_lion_reference.sh --install-prerequisites`, then selected with
`RUNTIMES='native csharp' REFERENCE_SERVER=/path/printed/by/the/builder`.
This uses Lion's pinned original Dafny/C# server, not a production dependency.
The same native load generator measures both arms, using their respective wire
codecs. Results are **local end-to-end service comparisons**, not an identical-core
I/O-only experiment or reproduction of Lion's remote-client hardware results.
CSV and JSON evidence record actual post-warmup timing, latency/error counters,
server CPU intervals, threads/RSS, affinity, compiled parameters, and binary hashes.
Unverified external `BASELINE_SERVICE` comparisons are no longer accepted.

An October 2026 sweep of the **pre-fix** batch-1 binary measured 1,273 ops/s
at two workers, versus 2,868 ops/s for the original C# service at four
workers. The transpiler was deep-cloning unchanged protocol fields on each
mutable action; after fixing its lowering and regenerating the affected
modules, the Verus-verified native batch-1 server reached a **4,482 ops/s**
median at 64 workers (three 30-second trials). At the same four workers and
batch size, the corrected native server reached **4,274 ops/s** versus
**2,854 ops/s** for the original C# server. The 64-worker configuration favors
throughput over latency (14.2 ms mean versus 0.94 ms at four workers).
An isolated **pre-fix** native batch-32 variant reached 3,891 ops/s at 32
workers; it uses a different batch limit and predates the generator fix, so
it is not a matched comparison with the corrected server. The
[runtime report](reports/benchmarks/LION_RUNTIME_BENCHMARK_COMPARISON.md)
records the profiling evidence, concurrency curve, per-trial errors, source
provenance, and comparisons. `NATIVE_BATCH_SIZE=32` is only a driver check
for an explicitly built native variant; the production default remains 1.

The benchmark requirements and runtime profiling workflow remain documented in
[Chapter 25 of the book](docs/tla-rs-book.md) and the
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
