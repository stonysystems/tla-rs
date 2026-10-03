# Lion-Aligned RSL: Native versus Original C# Reference

Measured **2026-09-29, 18:00:33–18:08:38 UTC**, in `/var/tmp/tla-rs-lion`.

The 2026-09-29 and 2026-10-02 results below describe the **pre-fix** native
binary. [The 2026-10-03 investigation](#native-throughput-investigation-2026-10-03)
measures the corrected, production batch-1 binary.

## Result

**Native wins with one core per replica, but is slower unpinned.** The native
production path remains C#-free; C# is an explicitly selected, isolated benchmark
reference only.

Each cell below reports the median of three fresh-cluster trials, with two clients
and a 30-second measured interval. Ratios are **ratios of median throughputs**.

| Affinity | Native (ops/s) | Original C# (ops/s) | Native / C# | Interpretation |
|---|---:|---:|---:|---|
| Unpinned | 1,264.92 | 2,113.89 | **0.598×** | Native throughput is 40.2% lower |
| One physical core per replica | 1,268.75 | 78.46 | **16.170×** | Native is substantially faster under the same core restriction |

This does **not** reproduce a greater-than-2× unpinned speedup. Nor is it an
I/O-only comparison: the native service uses the Rust/Verus protocol core, whereas
the reference uses Lion's original Dafny-generated C# core.

| Affinity | Runtime | Throughput range (ops/s) | Mean latency (ms) | p99 (ms) | Server CPU (%) | Peak RSS (MiB) | Peak OS threads |
|---|---|---:|---:|---:|---:|---:|---:|
| Unpinned | Native Lion | 1,137.73–1,275.03 | 1.581 | 3.031 | 256.14 | 36.90 | 3 |
| Unpinned | Original C# | 2,098.37–2,127.91 | 0.946 | 2.097 | 1,249.48 | 179.31 | 140 |
| One core | Native Lion | 1,171.18–1,283.00 | 1.576 | 3.015 | 253.87 | 48.79 | 3 |
| One core | Original C# | 78.09–78.63 | 25.467 | 51.905 | 299.71 | 188.59 | 84 |

Latency/CPU columns are medians of per-run values; RSS/thread columns are medians
of sampled per-run peaks. CPU, RSS, and thread counts are **totals across three
server processes**. CPU 100% means one fully occupied core. RSS sums include
shared pages; they are not physical-memory/PSS measurements. The CPU figures are
interval averages, not Lion's published peak/lifetime-`ps` statistic.

### Individual throughput trials

| Trial | Native unpinned | C# unpinned | Native one-core | C# one-core |
|---:|---:|---:|---:|---:|
| 1 | 1,275.03 | 2,113.89 | 1,283.00 | 78.63 |
| 2 | 1,137.73 | 2,098.37 | 1,171.18 | 78.09 |
| 3 | 1,264.92 | 2,127.91 | 1,268.75 | 78.46 |

Across all 12 cells:

- **419,286 matching measured completions**; both workers progressed in every cell.
- **Zero measured transport errors, invalid replies, or worker failures.**
- **Four measured request timeouts**, all in native unpinned trial 2. That trial is
  retained in the table and medians, not rerun or excluded.
- Native warmup recorded 30 timeouts across its six cells; C# warmup recorded none.
  Warmup transport errors and invalid replies were zero in both arms.
- There were 24 unfinished requests at measurement boundaries, excluded from
  completed-operation counts. Actual measured durations were 30.000030–30.004884 s.

Evidence:

- [All 12 raw CSV rows](lion-runtime/lion-aligned-final/results.csv)
- [Compact aggregate evidence](lion-runtime/lion-aligned-final/evidence.json)
- [Configuration, source/binary hashes, toolchains, topology, schedule, and per-cell evidence links](lion-runtime/lion-aligned-final/metadata.json)

## Throughput under increasing concurrency (2026-10-02)

The two-client result above is a latency comparison, **not a throughput
capacity measurement**. A separate unpinned, loopback RSL/TCP sweep varies
client workers (one outstanding request per worker). Both matched services
retain Lion's **batch size 1**. To answer whether batching matters, a separate
**native-only batch-size-32 experiment** changes exactly one protocol source
constant; the production server and pinned C# reference remain batch size 1.

Observed best medians among tested concurrencies, each from **three 30-second
trials**:

| Server | Batch limit | Workers at observed peak | Median ops/s (trial range) | Mean latency (ms) | Aggregate server CPU (%) |
|---|---:|---:|---:|---:|---:|
| Native, production settings | 1 | 2 | **1,272.71** (1,191.32–1,281.74) | 1.571 | 255.5 |
| Original Dafny/C# | 1 | 4 | **2,867.59** (2,825.42–2,876.71) | 1.395 | 1,476.7 |
| Native, isolated batching variant | 32 | 32 | **3,890.55** (3,886.50–3,905.45) | 8.221 | 151.7 |

At each service's observed optimum, the matched batch-1 native service reaches
**0.444×** the original C# service's throughput. With batch size 32, native
reaches **1.357×** C#'s observed batch-1 peak, but **that is a differently
configured comparison** (batch size and client count differ), not a Lion-style
same-protocol I/O speedup. Relative to native batch 1 at its own best client
count, native batch 32 delivers **3.057×** the throughput at its own best client
count. At the **same 32 workers**, the single 10-second reconnaissance runs
measured **946.02 ops/s** native batch 1 and **3,695.25 ops/s** native batch 32;
these single trials are not substituted for the 30-second peak medians.

The throughput curve makes the latency/throughput tradeoff explicit. A cell
marked `3×30s` is a median of three fresh-cluster runs; `1×10s` is a
reconnaissance observation, **not a repeated estimate**. A dash is untested.

| Workers | Native batch 1 | C# batch 1 | Native batch 32 |
|---:|---:|---:|---:|
| 1 | 1,171 (3×30s) | 1,063 (3×30s) | 95 (1×10s) |
| 2 | 1,273 (3×30s) | 2,110 (3×30s) | 190 (1×10s) |
| 4 | 1,260 (3×30s) | 2,868 (3×30s) | 281 (1×10s) |
| 8 | 1,207 (3×30s) | 2,769 (3×30s) | 732 (1×10s) |
| 16 | 1,112 (1×10s) | 2,464 (1×10s) | 1,337 (3×30s) |
| 24 | — | — | 2,005 (3×30s) |
| 32 | 946 (1×10s) | 2,095 (1×10s) | 3,891 (3×30s) |
| 48 | — | — | 3,490 (3×30s) |
| 64 | 794 (1×10s) | 1,718 (1×10s) | 3,130 (3×30s) |
| 128 | 376 (1×10s) | 1,154 (1×10s) | 2,189 (1×10s) |

For batch 32, a lone request waits for the 10 ms partial-batch timer:
one worker completed **95 ops/s**, versus **1,171 ops/s** with batch 1.
Thirty-two concurrent workers can fill a batch; the observed mean latency
at that peak was **8.221 ms**, not the batch-1 native peak's 1.571 ms.
The measured throughput decreases again above the observed peaks. Only
the listed concurrency and batch-size settings were tested; these are
**observed bests, not universal maxima or hardware capacity bounds**.

Across the **59 reported sweep/confirmation cells**, all workers progressed,
all measurement-start TCP connection sets had exactly three connections per
worker, and there were **2,776,438 matching measured completions**.
There were **zero measured transport errors, invalid replies, or rejections**;
**124 measured request timeouts** are retained: four in the matched batch-1
confirmation, nine in the batch-32 10-second sweep, and 111 in batch-32
30-second trials at 16/24 workers. The native batch-1 two-worker peak group
includes the four timeouts; C#'s four-worker and native batch-32's
32-worker peak groups have none. A separate two-second default-driver smoke
completed no measured requests after only two warmup completions; it failed
explicitly and was not used for throughput estimates. A subsequent
[15-second four-worker default-driver smoke](lion-runtime/max-throughput-default-driver-smoke/results.csv)
passed; both observations are preserved in the aggregate evidence.

The variant was built outside the production source tree: a copy of 391 source
files differed in **only** `src/implementation/RSL/cparameters.rs`
(`max_batch_size: 1` → `32`); `max_batch_delay` stayed **10 ms**.
Verus reported **1,496 verified, 0 errors** before compiling its isolated
rlib and server. The benchmark checked each server's actual `[[CONFIG]]`
batch size; the unchanged client and certificate tool binaries were reused.
`NATIVE_BATCH_SIZE=32` is an explicit driver expectation and rejects a C#
arm, whose pinned source has batch size 1. The production default still
expects and verifies batch size 1.

Evidence and reproduction:

- [Checked aggregate, per-count medians, and run counters](lion-runtime/max-throughput-summary/evidence.json)
- [Matched batch-1, three 30-second trials at 1/2/4/8 workers](lion-runtime/max-throughput-confirm/results.csv)
  and [single 10-second 4/8/16/32/64/128-worker sweep](lion-runtime/max-throughput-sweep/results.csv)
- [Native batch-32, three 30-second trials at 16/24/32/48/64 workers](lion-runtime/max-throughput-batch32-confirm/results.csv)
  and [single 10-second 1/2/4/8/16/32/64/128-worker sweep](lion-runtime/max-throughput-batch32-sweep/results.csv)
- [Exact isolated source change, binary hashes, build, and verification provenance](lion-runtime/max-throughput-batch32-variant/evidence.json)

Each CSV row links per-cell metrics and sampled CPU/RSS/threads; its count's
`metadata.json` records source hashes, identity/configuration, topology,
runtime order, and the full command. For a matched batch-1 sweep, run
`PROTOCOLS=rsl CLIENT_COUNTS='1 2 4 8' CONFIGS=unpin RUNTIMES='native csharp'`
with `REFERENCE_SERVER` set as below, `DURATION=30 TRIALS=3
WARMUP_SECONDS=5 SETTLE_SECONDS=3 REQUEST_TIMEOUT_MS=1000` and a fresh
`OUTPUT_DIR` through `scripts/bench_vary_clients.sh`. For the batch-32
variant, copy `src/` to a separate directory, change only the stated constant,
compile its rlib with the `--compile -C opt-level=3` Verus command from
`scripts/build_lion_runtime.sh`, and build only `tla-rs-server` with
`CARGO_ENCODED_RUSTFLAGS` pointing `--extern tla_protocol` to that rlib and
an isolated `CARGO_TARGET_DIR`. Reuse the production `tla-rs-client` and
`tla-rs-config` in the variant `BIN_DIR`; run the same sweep with
`RUNTIMES=native NATIVE_BATCH_SIZE=32` and a fresh output directory.
This experiment does **not** turn batching on in the production binary.

## Native throughput investigation (2026-10-03)

The previous native batch-1 peak of 1,273 ops/s was limited by a
code-generation defect, not an idle busy loop; the fix did not change transport.
Over six idle seconds, three native replicas used 0.67% aggregate CPU
(versus 0.50% for the isolated batch-32 build). An
isolated native server with per-action `Instant` counters reproduced the old
two-worker rate at 1,271 ops/s. In a steady five-second leader interval, each
of ten actions ran 38,352 times. Actions 1, 2, 7, and 8 sent **zero packets**
but spent respectively 0.698, 0.713, 0.674, and 0.671 seconds executing:
**2.756 seconds of the leader's five seconds** on those four actions alone.
`perf` hardware counters were unavailable (`perf_event_paranoid=4`), so this
is per-action wall time inside the single-threaded protocol loop, not a
hardware-cycle profile.
Slots 1 and 2 enter a view/phase two; slots 7 and 8 check view timeout and
quorum suspicion, respectively. The
[six steady pre-fix leader samples](lion-runtime/native-identity-clone-confirm/profile-steady-leader.log)
retain the raw calls, nanoseconds, and packets-sent counters.

In `src/generated/RSL/replica_gen.rs`, these mutable actions previously assigned
five unchanged fields back to themselves using deep `.clone()` calls each turn,
including the learner and executor. `transpiler/src/printer/mod.rs` now omits
exact self-field identity assignments even when the expression is a cloned
field; changed-field assignments remain. The RSL replica and affected
TwoPhase, EPaxos, and PBFT modules were **regenerated by the transpiler**,
not hand-edited. Whole-crate Verus: **1,496 verified, 0 errors**; native
runtime/I/O: **21 passing tests**; transpiler: **2,731 passing tests**.

Three fresh-cluster, **30-second** trials per row; unpinned, three replicas,
plaintext loopback TCP, batch size **1**, 5-second warmup, one outstanding
request per worker, 1,000 ms timeout. The four-worker comparison alternated
the native and original C# arms under the same driver.

| Server | Workers | Median ops/s (trial range) | Mean latency (ms) | Aggregate server CPU (%) | Measured timeouts |
|---|---:|---:|---:|---:|---:|
| Native, corrected | 2 | **3,862.86** (3,812.55–4,131.66) | 0.518 | 231.8 | 7 |
| Native, corrected | 4 | **4,274.29** (4,262.46–4,280.02) | 0.936 | 247.1 | 0 |
| Original Dafny/C# | 4 | **2,853.87** (2,833.57–2,894.50) | 1.401 | 1,477.4 | 0 |
| Native, corrected | 64 | **4,482.28** (4,482.28–4,559.43) | 14.197 | 291.6 | 0 |

The corrected native service delivers **1.498×** the C# throughput at the
**same four workers and batch size**, versus **3.393×** its own pre-fix
four-worker median (1,259.60 ops/s). Its highest confirmed native median
among tested worker counts is **4,482.28 ops/s at 64 workers**, **3.522×**
the pre-fix native peak of 1,272.71 ops/s. This is an observed peak, not a
hardware maximum: single 10-second probes measured 3,057/4,136/4,187/4,161/
4,070/3,919/4,534 ops/s at 1/2/4/8/16/32/64 workers and
2,401/2,295/2,170 ops/s at 96/128/192 workers. The 64-worker gain costs
14.2 ms mean latency versus 0.94 ms at four workers. All confirmed workers
progressed; across the 12 confirmed native/C# runs, there were **seven
measured timeouts** (native two-worker trials 2 and 3), and no measured
transport errors, invalid replies, or rejections. Timeout-affected trials
remain in the medians.

Reproduction and per-cell timing, binary/source hashes, errors, and CPU:

- [Matched four-worker native/C# trials](lion-runtime/native-identity-clone-matched/results.csv)
- [Native two- and 64-worker confirmations](lion-runtime/native-identity-clone-confirm/results.csv)
- [Initial one-to-64-worker survey](lion-runtime/native-identity-clone-sweep/results.csv)
  and [96-to-192-worker probe](lion-runtime/native-identity-clone-highcount/results.csv)

Run `scripts/build_lion_runtime.sh --test` with `VERUS_PATH` set, then
`PROTOCOLS=rsl CLIENT_COUNTS='2 64' CONFIGS=unpin RUNTIMES=native
DURATION=30 TRIALS=3 WARMUP_SECONDS=5 SETTLE_SECONDS=3
REQUEST_TIMEOUT_MS=1000 OUTPUT_DIR=/fresh/output scripts/bench_vary_clients.sh`.
For the matched four-worker row, set `CLIENT_COUNTS=4`,
`RUNTIMES='native csharp'`, and `REFERENCE_SERVER` to the pinned Lion
launcher described below. Neither the batch-32 historical variant nor the
reference binary was rebuilt as part of the generator fix.

## What changed

`src/implementation/RSL/cparameters.rs::StaticParams` now matches the pinned Lion
IronFleet configuration:

| Parameter | Previous native value | Revised value |
|---|---:|---:|
| Maximum request batch | 32 | **1** |
| Maximum log length | 1,000 | **1,000** |
| Baseline view timeout (ms) | 400 | **1,000** |
| Heartbeat period (ms) | 30 | **100** |
| Partial-batch delay (ms) | 30 | **10** |

A lone request fills its batch immediately rather than waiting for a partial-batch
flush. A protocol regression holds the clock fixed after initialization and checks
that individual requests commit and duplicates do not reexecute. No generated Rust
files were hand-edited. The native server emits its instantiated RSL parameters in
`[[CONFIG]]`; the benchmark rejects stale or mismatched binaries.

The native server still directly links `bin/libtla_protocol.rlib`, with one Lion
executor thread per replica. UDP batching and TLS remain available. Plain TCP
already set `TCP_NODELAY` in both connection directions; that behavior is retained.
The benchmark, rather than the deployment transport default, now selects TCP.
Disabling protocol batching favors low-concurrency latency; this is not a claim
about maximum throughput at 32 or more clients.

## Matched methodology

- Three replicas on IPv4 loopback. A fresh identity set is generated for each
  affinity/trial pair and reused between its native and C# arms. Only the reference
  launcher normalizes `ServiceType` from `IronRSL` to `IronRSLCounter`.
- Plain TCP, no TLS, and `TCP_NODELAY` on accepted and outgoing connections in
  both implementations. The reference includes Lion's existing C# NoDelay fixes.
- Two client workers, one outstanding request each. Like Lion's original client,
  the load generator starts connections to every replica and idles for three
  seconds before issuing requests. The driver verifies **six established client
  TCP connections**, two to each replica, at every measurement start.
- A 1,000 ms request timeout, then five seconds of active warmup and 30 seconds of
  measurement. Both initial idle and warmup are excluded from the denominator.
  Throughput is completions divided by actual monotonic elapsed time.
- The same native client binary runs both arms. `wire=native` uses the Rust
  protocol's encoding; `wire=ironfleet` uses the original u64-big-endian message
  discriminants, sequence numbers, payload lengths, and counter values. The wire
  encodings and payload sizes are therefore **not identical**.
- Replies must match the outstanding sequence and have increasing counter values.
  Stale duplicate replies are counted separately, not as new work or leader hints.
  Histogram percentiles are upper bounds with less than 0.8% bucket-width error.
- Runtime order and affinity order alternate by trial. Unpinned processes inherit
  the allowed 64-CPU mask. Pinned replicas use distinct physical cores, CPUs
  **0, 1, and 2**. The client stays unpinned in both configurations.
- Flushed client measurement markers delimit `/proc/PID/stat` CPU tick sampling.
  Sampler duration and client elapsed duration are recorded separately. Server
  startup, client CPU, and warmup are outside the reported server CPU interval.
- No concurrent builds or other assistant-launched workloads ran during the final
  matrix. There is no general host-load isolation, NUMA tuning, remote network,
  confidence-interval claim, or automatic performance-regression threshold.

The reference builder exports unmodified original source from Lion commit
`aa5bebe74369003b16193d73d43727e95dcf4ea0`, compiles its counter server in a private
cache, and runs `lion=false safeguard=false`: the **original C# IoScheduler**, not
Lion's queued FFI adapter. Source, generated C#, executable/dependency hashes, and
build commands are retained. Dafny compilation explicitly skips verification;
this reference build is not new proof evidence. Default native builds and
benchmarks never invoke the reference builder or .NET.

## Relation to Lion's published result

Lion's [pinned methodology](https://github.com/stonysystems/lion/blob/aa5bebe74369003b16193d73d43727e95dcf4ea0/lion-benchmark/ironfleet/README.md)
and [reference table](https://github.com/stonysystems/lion/blob/aa5bebe74369003b16193d73d43727e95dcf4ea0/lion-benchmark/ironfleet/ref-2/table.md)
report 3,330 versus 1,635 ops/s unpinned (**2.04×**) and 2,005 versus 329 with one
core (**6.09×**). Those arms share the same Dafny/C# protocol core and change the
I/O runtime. They use a remote client and an AMD EPYC server, not this loopback
Threadripper setup.

Our native core, scheduler organization, wire encoding, and client differ. The
new results establish a substantial constrained-core service advantage, **not** a
transport-only speedup or reproduction of the published unpinned result. These
measurements do not attribute the native unpinned deficit to a particular function.

## Correctness and diagnostic evidence

- Full Verus build: **1,496 verified, 0 errors**, with the existing automatic-trigger
  note in Raft recovery. This covers the protocol/proof crate, not an end-to-end
  theorem for the trusted runtime, OS I/O, configuration, or TLS integration.
- **21 tests pass**: eight batched-UDP, seven identity/stream, five protocol-boundary,
  and one original-IronFleet reply-codec regression. The latter rejects malformed
  lengths and wrong request sequences and checks big-endian counter interpretation.
- Live all-ten-selector smoke passes. RSL, Raft, Primary-Backup, PBFT, and EPaxos
  execute real workloads; the other five selectors have startup-only evidence.
- RSL UDP, plaintext TCP, and TLS workloads pass. UDP and TLS retain quorum progress
  after killing one replica and after restarting it; this does not prove durable
  recovery. Generic wrapper and concurrency-sweep entrypoints were exercised.
- The final eager-connection path passes native/C# and native TLS smoke, including
  the actual six-connection check. [Correctness evidence](lion-runtime/aligned-correctness/evidence.json)
  retains counters, including Primary-Backup/EPaxos UDP retries.
- An exploratory PBFT/TCP check completed 233 warmup operations but no operations
  in its subsequent one-second measured window. Its cause is not diagnosed; this
  is not a PBFT/TCP correctness claim. Generic benchmark defaults remain UDP, and
  that failed observation is retained in the correctness evidence.

An earlier matrix [stopped after a counted send error](lion-runtime/lion-aligned-2/metadata.json).
Investigation found a real timer-precision defect: Lion floored a requested 900 µs
pending-future timeout to an observed **3 µs**. With two milliseconds of padding,
the probe expired after **2,083 µs**. The client now prevents early send deadlines
and classifies cancellation by the deadline that bounded the operation; genuine
send errors are still counted and logged. [Probe evidence](lion-runtime/deadline-precision/evidence.json)
is retained. The old send-error detail was discarded by the former client, so the
probe does not establish that the old matrix's sole error was a false positive.
A second [partial matrix](lion-runtime/lion-aligned-2-corrected/metadata.json) was
explicitly cancelled to align eager connections, initial idle, and request timeout.
Neither partial run contributes to the final comparison.

## Environment and reproduction

- AMD Ryzen Threadripper 2990WX; 32 physical cores, 64 allowed logical CPUs.
- Linux `7.0.14-19-pve`, x86-64, glibc 2.41; `MemTotal` 65,791,560 KiB.
- Rust `1.97.1`; Verus `0.2026.08.02.b677dd5`; pinned Lion revision above.
- Reference: .NET SDK `6.0.428`, Dafny `3.4.0.40208`, SCons `4.8.1`.
- Benchmark driver: Python `3.14.6` on this host; requires Python 3.11 or newer.

```bash
export VERUS_PATH=/path/to/verus/verus
scripts/build_lion_runtime.sh --test
scripts/integration_test_cluster.sh

# Native only: no managed dependency.
scripts/bench_rsl_runtime.sh

# Explicit isolated historical reference; never part of a default native build.
scripts/build_lion_reference.sh --install-prerequisites
export REFERENCE_SERVER=/absolute/path/printed/by/builder/tla-rs-csharp-reference
RUNTIMES='native csharp' DURATION=30 TRIALS=3 CLIENT_THREADS=2 \
  SETTLE_SECONDS=3 WARMUP_SECONDS=5 REQUEST_TIMEOUT_MS=1000 \
  OUTPUT_DIR=/fresh/output/directory scripts/bench_rsl_runtime.sh
```

On this host, Python's Homebrew OpenSSL had no default CA bundle. The explicit
reference download succeeded with `SSL_CERT_FILE=/etc/ssl/certs/ca-certificates.crt`;
certificate verification was not disabled. Generated private identities and raw logs
remain local/ignored; CSV, metadata, and per-cell JSON evidence are retained.

## Historical results, not matched baselines

The previous 32-request-batch UDP configuration measured medians of 131.53 ops/s
with four clients and 7,073.91 ops/s with 32 clients. The former waited for the
30 ms partial-batch timer; the latter could fill a protocol batch. Their different
batching, transport, concurrency, duration, and kernel make them unsuitable as a
matched baseline for this retest. Their [four-client CSV](lion-runtime/native-direct-4/results.csv),
[32-client CSV](lion-runtime/native-direct-32/results.csv), and
[UDP syscall/profile evidence](lion-runtime/native-profile/evidence.json) remain
available. The older callback-ABI adapter comparison is also superseded; that
adapter is no longer the native deployment path.
