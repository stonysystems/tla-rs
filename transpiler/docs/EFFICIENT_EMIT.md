# Efficient Emit Strategies for Generated Code

> **Status:** Current design guidance plus a historical performance record. Audited on
> 2026-08-05 at commit `189b227a`. The source and tests define actual behavior; see
> [*The tla-rs Book*](../../docs/tla-rs-book.md), Chapters 18, 19, and 25, for configuration,
> generated-artifact, and benchmarking guidance.

The transpiler supports two ownership and calling-convention strategies. Neither is a
universal performance switch: the correct choice depends on whether the action can be lowered
soundly, whether its proof closes, and whether a controlled benchmark shows a real benefit.

## Current calling conventions

| Convention | Selection | Generated shape | Appropriate use |
|---|---|---|---|
| Functional | Default; `mut_self_types` is empty for the type | Takes `&CState` and returns a new state | General fallback, including actions that compute an intermediate whole state |
| Mutable receiver | Add an eligible concrete type to `mut_self_types` | Emits an `impl` method taking `&mut self`; the receiver-typed output becomes `self` | Hot action paths whose generated body and proof both support the mutable rewrite |

For example:

```toml
mut_self_types = ["CProposer"]
```

This setting is opt-in and type-specific. It applies only to functionalizable predicate/action
functions whose first input has the selected receiver type. Initializers, value-returning
helpers, skipped functions, and functions that do not match that shape remain free or
functional functions.

The mutable path rewrites a tail-position state construction into assignments and changes the
contract from a relation over `s@` and `result@` to one over `old(self)@` and `self@`. It is not
general mutation analysis. In particular, it does not currently support every intermediate
whole-state pattern; Raft's `s_mid = step_down_if_needed(...)` flow is a concrete reason Raft
uses the functional convention.

Review mutable lowering carefully when one assigned field's expression reads another field
that was assigned earlier. The emitted assignments are sequential, while a functional struct
construction conceptually evaluates from one pre-state. Current structural tests do not prove
that every such cross-field dependency is safe.

## Arc wrapping in functional mode

Functional transitions may rebuild a state and clone unchanged collections. The transpiler can
wrap selected generated fields in `Arc<T>` so unchanged paths use a shallow clone:

```toml
arc_wrap_types = ["CState"]
arc_wrap_fields = { CState = ["log", "votes_granted"] }
```

`arc_wrap_types` enables generated type changes. A matching `arc_wrap_fields` entry narrows the
wrapping to named fields; without a field list, the type generator wraps recognized non-copy
fields. A field list alone does not change an ordinary generated struct into an Arc-backed one;
it is useful only when the matching type is already Arc-backed elsewhere.

Arc wrapping is not proof-neutral. Generated Arc-backed structs use specialized helpers and a
trusted `#[verifier::external_body]` clone implementation. Mutation lowering is also limited to
recognized collection operations such as `insert`, `remove`, and `push`; it deep-clones the
inner collection before mutation and re-wraps the result.

Any nonempty `mut_self_types` setting currently clears **all** `arc_wrap_types` and
`arc_wrap_fields` entries in that file configuration, even for disjoint types. The CLI warns
when this occurs. Do not combine the two strategies in one configuration and assume both are
active.

## Effective repository configuration

At the audit revision, the checked-in protocols use:

| Effective strategy | Protocols |
|---|---|
| Functional with selected Arc-backed fields | Chain Replication, Leader Election, Paxos, Raft, Vertical Paxos |
| Functional with direct ownership | Primary-Backup |
| Mutable receiver with direct ownership | Two-Phase Commit, EPaxos, PBFT |
| Mixed by function shape | RSL: selected acceptor, election, executor, learner, proposer, and replica actions are mutable; ineligible helpers, initializers, and other functions remain free/functional |

Some mutable-protocol TOML files still contain Arc settings, but configuration resolution clears
them. Treat the generated source and resolved configuration—not the presence of an isolated TOML
key—as the effective behavior.

## Current recommendation

1. Start with functional generation because it has the broadest semantic and proof coverage.
2. Profile a representative, reproducible workload before changing ownership strategy.
3. For a functional hot path dominated by unchanged collection clones, consider narrowly
   targeted Arc fields and account for the additional trusted clone boundary.
4. Use `mut_self_types` only when the action shape is supported, deterministic regeneration
   passes, the full Verus build closes, and a fresh compiled artifact runs correctly.
5. Benchmark the candidate against the functional form under identical conditions before
   calling it an optimization.

Do not hand-edit `src/generated/`. Change the specification, annotation, configuration, or
transpiler; regenerate; then verify and benchmark. This policy is defined in
[`AGENTS.md`](../../AGENTS.md).

Persistent collections such as the `im` crate were considered historically but have no current
implementation or verified adapter in this project. They are not an available emit strategy.

## Historical optimization record

The old version of this document mixed proposals and benchmark claims as though they were
current recommendations. The durable engineering conclusions are narrower:

| Phase | Experiment | Durable conclusion | Evidence status |
|---|---|---|---|
| 40 | Arc-wrap whole subcomponents | Limited runs did not demonstrate a consistent benefit; blanket Arc wrapping is not recommended | Historical measurements lacked a complete reproducibility bundle |
| 41 | Arc-wrap selected RSL collection fields | Targeted sharing can reduce cloning in functional code | Reported throughput is historical and no longer describes current RSL ownership |
| 47 | Manually prototype mutable RSL actions | Removing outer-state rebuilds was promising enough to automate | The reported “1.44× faster than hand-tuned” comparison was later retracted |
| 48 | Add `mut_self_types` to the transpiler | Mutable lowering works for a restricted action shape, not every protocol | The broad rollout had no independent controlled benchmark and was not validated by a whole-crate compile |
| 49 | Remove one hot deep clone and simplify RSL Arc ownership | The deep clone, not Arc itself, was the measured hotspot; Arc removal was primarily simplification | Reported comparisons cannot authenticate the binaries that ran |
| 50 | Rebuild and validate the whole crate | Six simple protocols had to return to functional generation; only TwoPhase, EPaxos, and PBFT retained mutable lowering | Exposed stale build artifacts and invalidated the earlier results as current evidence |

### Retracted and disputed claims

The Phase 47 claim that generated RSL was **1.44× faster** than the hand-tuned reference is
invalid. The reference used a stale shared library with a mismatched batch size.

Phase 49 subsequently recorded generated-RSL trials of 54,000 and 54,849 operations/second and
a hand-tuned summary value of 60,031 operations/second. Do not publish that as a controlled
comparison. Phase 50 found 203 whole-crate compile errors and a stale pre-mutable `liblib.so`
that had never been rebuilt from the relevant source. Raw logs, binary hashes, full hardware
metadata, exact commands, and individual reference trials are also absent.

A later fresh-build RSL run established only that the service starts and processes requests; it
was not a matched benchmark. Consequently, this repository currently has **no controlled,
reproducible generated-versus-hand-tuned RSL performance comparison** and no evidence for a
claim that it is faster than the original IronFleet implementation.

The phase ledger remains in [`TODO.md`](../../TODO.md) for historical investigation. Its numbers
must not be presented as current performance without a fresh experiment.

## Requirements for a new performance claim

Before adding throughput or speedup to the README:

1. Start from a named clean commit and record the Verus, Rust, .NET, and OS versions.
2. Perform a clean full-crate verification and compilation; do not reuse an existing
   `liblib.so`.
3. Record hashes and timestamps for every compared executable/shared library and the exact
   configuration used to build it.
4. Hold host hardware, network topology, node count, client count, batch size, duration,
   warm-up, and trial count constant.
5. Capture every trial rather than only an average, and report variance or a range.
6. Store raw CSV/log artifacts and the exact reproduction command under `reports/benchmarks/`.
7. Re-run deterministic generation and the full Verus gate after any configuration or
   transpiler change.
8. Compare with IronFleet or another external system only when the workload and environment
   are demonstrably equivalent.

The historical [`scripts/bench_vary_clients.sh`](../../scripts/bench_vary_clients.sh) is not
yet a publication-quality harness: it contains host-specific setup and can leave source batch
configuration out of sync with a previously built library. Review and fix the harness before
using it for a new headline result.

## Implementation anchors

- Configuration schema: [`transpiler/src/config.rs`](../src/config.rs)
- Arc/mutable conflict resolution: [`transpiler/src/main.rs`](../src/main.rs)
- Arc type generation: [`transpiler/src/codegen/mod.rs`](../src/codegen/mod.rs)
- Mutable action translation: [`transpiler/src/translator/mod.rs`](../src/translator/mod.rs)
- Mutable body printing: [`transpiler/src/printer/mod.rs`](../src/printer/mod.rs)
- Current configuration reference and performance method:
  [*The tla-rs Book*](../../docs/tla-rs-book.md), Appendix C and Chapter 25
