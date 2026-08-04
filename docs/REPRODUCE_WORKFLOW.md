# Reproducing the End-to-End Workflow (spec → generate → verify → compile → run)

This guide lets a fresh checkout on a clean Linux/x64 machine reproduce the full
pipeline for the transpiler-generated protocols (**Raft, EPaxos, PBFT**, and the other
non-RSL protocols), and collect throughput numbers.

> **Two honest caveats up front.** (1) You must install the pinned toolchain yourself —
> this doc tells you exactly what, but installing it is on you. (2) The throughput numbers
> you get are **your machine's** — they will not match ours (perf depends on CPU, load, and
> run duration). Everything up to and including *compile* is deterministic; *run* produces
> data but the absolute values are hardware-dependent.

---

## 0. Prerequisites (install these first)

| Tool | Version we used | Notes |
|------|-----------------|-------|
| **Verus** | `0.2026.08.02.b677dd5` | From <https://github.com/verus-lang/verus/releases>. This is the latest stable release tested by the project; rolling currently points at the same commit. Set `export VERUS=/path/to/verus/verus`. |
| **Rust** | 1.97.1 | This is the toolchain required by the pinned Verus binary. A system Rust (any recent stable) is also sufficient to build the transpiler. |
| **.NET SDK** | 6.0.x | For the C# runtime + client. `dotnet` must be on `PATH`. |
| **SCons** | any recent | `pip install scons` — builds the C# projects. |
| **Platform** | Linux x86-64 | The C# native interop loads `liblib.so`. |

Clone and enter the repo. Throughout, `$REPO` is the repo root and `$VERUS` is your Verus
binary.

```bash
export REPO=$(pwd)                 # from the repo root
export VERUS=/path/to/verus/verus  # adjust to your install
export LD_LIBRARY_PATH="$REPO"     # so dotnet can load liblib.so
```

---

## Pipeline inputs and outputs

For each protocol `<P>` with module `<m>` (e.g. `Raft`/`raft`, `EPaxos`/`epaxos`,
`PBFT`/`pbft`):

- **Inputs** (hand-written, checked in):
  - `src/protocol/<P>/<m>.rs` — the TLA-style **spec** (`spec fn` predicates)
  - `src/protocol/<P>/types.rs` — spec type definitions
  - `src/protocol/<P>/<m>.automan` — mode annotations (which params are in/out, helper vs predicate)
  - `src/protocol/<P>/<m>_transpile.toml` — codegen config (calling convention, imports, messages)
- **Outputs** (transpiler-generated, checked in — regenerating reproduces them byte-for-byte):
  - `src/generated/<P>/types_gen.rs`
  - `src/generated/<P>/<m>_gen.rs`

The `host.rs` under `src/implementation/<P>/` is the hand-written I/O shell (wires the
generated pure functions to the network framework); it is **not** generated.

---

## 1. Build the transpiler

```bash
cd "$REPO/transpiler"
cargo build --release          # produces target/release/verus-transpile
cd "$REPO"
export T="$REPO/transpiler/target/release/verus-transpile"
```

---

## 2. Generate from spec (byte-reproducible)

Easiest: use the script (regenerates a single protocol into `src/generated/<P>/`):

```bash
./scripts/regenerate_all.sh Raft
./scripts/regenerate_all.sh EPaxos
./scripts/regenerate_all.sh PBFT
```

Or run the two transpiler commands explicitly (shown for Raft; substitute
`epaxos`/`EPaxos`, `pbft`/`PBFT`):

```bash
$T generate-types \
   -i src/protocol/Raft/types.rs \
   -c src/protocol/Raft/raft_transpile.toml \
   -o src/generated/Raft/types_gen.rs

$T --input       src/protocol/Raft/raft.rs \
   --annotations src/protocol/Raft/raft.automan \
   --config      src/protocol/Raft/raft_transpile.toml \
   --output      src/generated/Raft/raft_gen.rs
```

**Check reproducibility** — regenerating should leave the checked-in files unchanged:

```bash
git diff --stat src/generated/Raft src/generated/EPaxos src/generated/PBFT
# expect: no changes (byte-identical to what is checked in)
```

There is also a guardrail test: `cd transpiler && cargo test --release regen_matches_checked_in -- --test-threads=1`
(run single-threaded — these tests spawn `cargo run` and race on the build lock in parallel).

---

## 3. Verify (Verus)

Verify each generated module (expect `0 errors`):

```bash
for pm in Raft:raft EPaxos:epaxos PBFT:pbft; do
  P=${pm%%:*}; m=${pm##*:}
  $VERUS --crate-type=lib src/lib.rs \
    --verify-only-module generated::$P::${m}_gen \
    --verify-only-module generated::$P::types_gen
done
# expected: Raft 30 verified/0 err, EPaxos 19/0, PBFT 17/0
```

> Note: **Raft's refinement proof** (`protocol::Raft::refinement_proof`) still carries 13
> pre-existing "Phase 34" deprecated `assume`s — that is a separate, long-standing research
> gap and is **not** part of this workflow. The generated `raft_gen` module itself verifies
> clean.

---

## 4. Compile the whole crate → `liblib.so`

```bash
$VERUS --crate-type=dylib -C opt-level=3 --compile src/lib.rs --no-verify
# expected: 0 errors; produces ./liblib.so
ls -l liblib.so
```

> `liblib.so` is **not** checked in (gitignored) and is often stale on disk — always rebuild
> it before running or benchmarking.

---

## 5. Build the C# runtime + client

```bash
scons --skip-verus         # builds bin/*.dll (IronProtocolServer, IronGenericClient, CreateIronServiceCerts, ...)
```

(`bin/` is gitignored, so you must build it. Use `scons --verus-path=$(dirname $VERUS)` to
build C# *and* re-verify Rust in one shot.)

---

## 6. Run + collect throughput

### 6a. Generate certificates (one-time per node count)

Generic protocols share the service name `MyRaft` / type `IronProtocol`:

```bash
# 3-node cluster (Raft, EPaxos):
dotnet bin/CreateIronServiceCerts.dll outputdir=bench/certs name=MyRaft type=IronProtocol \
  addr1=127.0.0.1 port1=4001 addr2=127.0.0.1 port2=4002 addr3=127.0.0.1 port3=4003

# 4-node cluster (PBFT):
dotnet bin/CreateIronServiceCerts.dll outputdir=bench/certs_4node name=MyRaft type=IronProtocol \
  addr1=127.0.0.1 port1=4001 addr2=127.0.0.1 port2=4002 addr3=127.0.0.1 port3=4003 addr4=127.0.0.1 port4=4004
```

### 6b. Run a cluster and read throughput

The helper script starts the servers, runs `IronGenericClient`, and prints throughput:

```bash
# usage: scripts/bench_generic.sh <protocol> [duration_s] [trials] [nthreads]
scripts/bench_generic.sh raft   8 1 4
scripts/bench_generic.sh epaxos 8 1 4
scripts/bench_generic.sh pbft   8 1 4
```

Look for the line `throughput <N> ops/sec | avg latency ms <L>` in the client output, plus
`[METRICS]` lines from each server showing `committed=`/`seq_num=` advancing together (proof
of consensus).

**Reference numbers (localhost, 4 client threads, 8 s, single trial — yours will differ):**

| Protocol | Nodes | Throughput | Latency |
|----------|:-----:|-----------:|--------:|
| Raft     | 3     | ~11,000 ops/s | ~0.45 ms |
| EPaxos   | 3     | ~15,000 ops/s | ~0.34 ms |
| PBFT     | 4     | ~2,500 ops/s  | ~2.0 ms  |

For a longer/fairer number use e.g. `scripts/bench_generic.sh epaxos 30 2 16`. Throughput
scales with client threads and decays over longer runs (the decay is in the C# I/O layer,
not the Rust protocol code).

### RSL (the flagship, separate binaries)

```bash
dotnet bin/CreateIronServiceCerts.dll outputdir=bench/certs_rsl name=MyRSL type=IronRSL \
  addr1=127.0.0.1 port1=4001 addr2=127.0.0.1 port2=4002 addr3=127.0.0.1 port3=4003
SVC=bench/certs_rsl/MyRSL.IronRSL.service.txt
for n in 1 2 3; do
  dotnet bin/IronRSLServerUDP.dll "$SVC" bench/certs_rsl/MyRSL.IronRSL.server$n.private.txt &
done
sleep 8
dotnet bin/IronRSLClientUDP.dll ip1=127.0.0.1 port1=4001 ip2=127.0.0.1 port2=4002 \
  ip3=127.0.0.1 port3=4003 nthreads=32 duration=28
# reference: ~46,000 ops/s @ 32 clients, ~0.85 ms (max_batch_size=32)
pkill -f IronRSLServerUDP
```

---

## Calling convention per protocol (why the generated code looks different)

- **`&mut self` (in-place mutation, faster)**: RSL, TwoPhase, EPaxos, PBFT. Their specs
  express the post-state as per-field diffs (`s_.f == s.f <op>`), which map directly to
  `self.f = ...`.
- **Functional (`fn CFoo(s: &CState, ...) -> (CState, Vec<Msg>)`)**: Raft, Paxos,
  LeaderElection, ChainReplication, PrimaryBackup, VerticalPaxos. Set by leaving
  `mut_self_types` unset in the TOML. Raft *must* be functional because its handlers compute
  an intermediate whole-state (`s_mid = step_down_if_needed(s, term)`) that the `&mut self`
  body transform cannot lift into `*self = s_mid`; the other five verify-fail under
  `&mut self` due to proof-generation gaps and have no perf need. This is pure config — there
  is no protocol-specific logic in the transpiler.

## Note on RSL regeneration

RSL is **not** fully auto-generated: 10 functions are in `skip_functions` with hand-written
bodies (see `transpiler/docs/REGEN_WORKFLOW.md`) plus Arc patches. Regenerating RSL from
scratch requires re-applying those manual patches. RSL's *compile* and *run* work out of the
box from the checked-in tree; only lossless *regeneration* is a manual process (tracked as
Phase 42).

---

## Troubleshooting

- **`liblib.so not found` / immediately exits**: `export LD_LIBRARY_PATH="$REPO"` and make
  sure you rebuilt `liblib.so` (step 4) after any source change.
- **Client throughput 0**: fewer than a quorum of servers came up. Check all N servers print
  `[[READY]]`; make sure ports 4001–400N are free (`pkill -f IronProtocolServer`).
- **Verification `rlimit exceeded`**: pass `--rlimit 60` (or higher) — proof search time
  varies by machine.
- **`generate-types` prints nothing**: it writes to stdout when `-o/--output` is omitted;
  always pass `--output` (or redirect) when regenerating in place.
