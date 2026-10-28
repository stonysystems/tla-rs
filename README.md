# tla-rs: TLA-Style Specifications for Verified Rust

**Stop looking for bugs. Start proving your code.**

`tla-rs` lets you write **TLA-style specifications in Rust with
[Verus](https://github.com/verus-lang/verus)** and prove that your Rust code implements
the behavior you specified.
Describe your system's state, initial conditions, and allowed transitions as logical
relations—not just a collection of test cases.

Tests find executions that go wrong. Proofs establish stated properties for every
execution covered by the theorem's assumptions. The goal is not just to check a model
beside your code, but to connect the specification to the Rust that runs.

## Specify and prove

1. **Specify the behavior.** Write TLA-style state machines and invariants directly in
   Verus's Rust syntax. You do not need to start with a separate TLA+ file.
2. **Prove your code.** State the contracts your Rust implementation must satisfy
   and use Verus to check them. Supply invariants and lemmas to establish
   system-level safety and refinement properties.

Verification covers the stated properties under explicit preconditions and trusted
boundaries. Testing and model checking still help find specification mistakes and
exercise runtime code outside those boundaries.

For specification and proof techniques, see Chapters 4 and 20 of
[*The tla-rs Book*](docs/tla-rs-book.md).

## Verified refinement theorems

The two flagship protocols carry machine-checked refinement proofs, verified end to end by Verus:

- **RSL (Multi-Paxos)** —
  [`lemma_GetBehaviorRefinement`](src/protocol/RSL/refinement_proof/refinement.rs):
  every behavior of the distributed protocol refines an abstract replicated
  state machine — the IronFleet theorem, mechanized in Verus.
- **Raft** —
  [`lemma_raw_refinement_correct`](src/protocol/Raft/refinement_proof/lift.rs):
  every behavior of the raw protocol, with message loss, reordering,
  crash-reboot, and joint-consensus membership changes, refines a sequential
  state machine over the committed log (no two reachable servers commit
  different entries at the same index, and each term has at most one leader)
  — a property IronFleet's original development did not cover. The theorem is
  stated over protocol state alone; proof-only history is shown never to
  restrict the protocol.

The repository also includes bidirectional TLA+/Verus translation and source-first
model checking.

## What is included

- Ten distributed protocols: RSL (Multi-Paxos), Single-Decree Paxos, Raft, EPaxos,
  PBFT, Chain Replication, Primary-Backup, Vertical Paxos, Two-Phase Commit, and
  Bully leader election.
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
gate reports `1921 verified, 0 errors`, with no warnings or automatically chosen trigger
notes. The TLAPS-Bench ports are a separate crate, verified by
`scripts/verify_tlaps_bench_manual.sh` in their own CI job to the same standard; see
[their published results](reports/tlaps_bench_manual/README.md).
Verification remains relative to the declared trusted boundaries:
the native scheduler, marshalling, Lion's OS-facing glue, configuration, and TLS
integration are runtime-tested, not covered by an end-to-end service theorem.

For service configuration, deployment, client workloads, and transport options,
see [Chapter 10 of *The tla-rs Book*](docs/tla-rs-book.md#run-a-three-node-rsl-service).

## Code generation

The repository also includes an AutoMan-style transpiler that generates executable
Rust and refinement contracts from supported, annotated Verus specifications.
The generated code must still be checked by Verus.
See the [counter example](examples/quickstart/) and Chapters 5–7 of
[*The tla-rs Book*](docs/tla-rs-book.md) for annotations, configuration, and usage.

## Performance

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

## Foundations

`tla-rs` brings the methodology of two verified-systems projects to Rust and Verus:

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

## Attribution and license

Parts of the native I/O, Verus utilities, marshalling, FFI, and C# runtime were adapted
from [IronKV](https://github.com/verus-lang/verified-ironkv). The transpiler reimplements
the [AutoMan](https://github.com/stonysystems/automan) workflow for Rust and Verus.

Licensed under the [MIT License](LICENSE).
