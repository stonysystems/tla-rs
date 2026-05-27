# Efficient Emit Strategies for Generated Code

## Problem

The transpiler emits pure-functional state transitions: every `ProcessXxx`
takes `&State` and returns a fresh `State`, rebuilding the entire top-level
struct even when only one sub-component changes.

**Concrete example** (RSL `replica_gen.rs:214-221`):
```rust
let r = (CReplica {
    constants: s.constants.clone(),
    proposer: s_proposer,                   // actual delta
    acceptor: s.acceptor.clone_up_to_view(), // unchanged — full clone
    learner: s.learner.clone_up_to_view(),   // unchanged — full clone
    executor: s.executor.clone_up_to_view(), // unchanged — full clone
}, vec![]);
```

**Impact**: gdb sampling on the RSL leader (zoo-002, 32 client threads)
shows ~35% of active CPU in `clone_up_to_view` + `drop` + `malloc`.
Clone cost is O(n) per HashMap/Vec element, producing measurable
throughput decay (16.5K → 10.5K ops/s across two 30-s trials).

**Scale**: 790 `clone`/`clone_up_to_view` call sites across 19 generated
files spanning all 10 protocols.

## Candidate Strategies

### A. `Arc<T>` wrapping for unchanged sub-components

**Approach**: Wrap each sub-component field in the top-level protocol
state struct with `Arc<T>`. Unchanged fields get `Arc::clone()` (refcount
bump, O(1)) instead of deep clone. Fields that change get `Arc::new(new_value)`.

**Type-level change** (transpiler emits):
```rust
pub struct CReplica {
    pub constants: Arc<CConstants>,
    pub proposer: Arc<CProposer>,
    pub acceptor: Arc<CAcceptor>,
    pub learner: Arc<CLearner>,
    pub executor: Arc<CExecutor>,
    pub nextHeartbeatTime: i64,  // scalars stay bare
}
```

**Rebuild site after change**:
```rust
let r = (CReplica {
    constants: s.constants.clone(),  // Arc::clone — O(1)
    proposer: Arc::new(s_proposer),  // wrap new value
    acceptor: s.acceptor.clone(),    // Arc::clone — O(1)
    learner: s.learner.clone(),      // Arc::clone — O(1)
    executor: s.executor.clone(),    // Arc::clone — O(1)
    nextHeartbeatTime: s.nextHeartbeatTime,
}, vec![]);
```

**Verus compatibility**: vstd already provides `impl View for Arc<A>`
where `type V = A::V` (`vstd/view.rs:81-88`). This means `Arc<CProposer>@`
= `LProposer` — all existing spec-level proofs work without change.
Field access works via autoderef (`s.proposer.field` works through Arc).

**Estimated reach**: Kills ~30% CPU on RSL (the entire
`clone_up_to_view` family). Applies uniformly to all 10 protocols.

**Complexity**: Low — single rule in the type generator. No proof template
changes (View delegation is handled by vstd). `clone_up_to_view()` calls
become `Arc::clone()` calls (or just `.clone()` which Rust dispatches to
Arc::clone for `Arc<T>`).

**Risks**:
- Cache miss from Arc indirection (very low — single pointer + 16-byte
  header; prefetcher handles)
- `Arc::make_mut` needed for in-place mutation patterns (see below)

### B. Persistent data structures (`im::HashMap`, `im::Vec`)

**Approach**: Replace `HashMap`/`Vec` with structurally-shared persistent
types from the `im` crate. Clone becomes O(1) (shared tree nodes);
mutation is O(log n).

**Targets**: The hottest HashMap fields per gdb profile:
- `CProposer.highest_seqno_requested_by_client_this_view: HashMap<EndPoint, u64>`
- `CExecutor.reply_cache: HashMap<EndPoint, CReply>`
- `CLearner.unexecuted_ops: HashMap<COperationNumber, …>`
- `CState.log: Vec<CLogEntry>` (Raft — worst-case, append-only)

**Verus compatibility**: Requires a new Verus adapter with
`View == Map<K,V>` (vstd's abstract type). Not currently available.

**Estimated reach**: Eliminates the *remaining* decay after Arc-wrapping
(the sub-component that *does* change still deep-clones its internals).

**Complexity**: Medium — needs adapter crate, Verus verification of
adapter, per-field TOML configuration.

**Risks**:
- O(log n) mutation overhead may partially offset clone savings
- No existing Verus adapter; needs new trusted code

### C. Mutation analysis emitting `&mut self`

**Approach**: Analyze spec transitions to detect `s_.f == s.f` (unchanged)
vs `s_.f == expr(s, …)` (changed), then emit in-place mutation via
`&mut self` instead of functional rebuild.

**Example emitted code**:
```rust
fn CReplicaNextProcess1a(s: &mut CReplica, pkt: &CPacket) -> Vec<CPacket> {
    // only acceptor changes
    let (s_acceptor, sent) = CAcceptorProcess1a(&s.acceptor, pkt);
    s.acceptor = s_acceptor;
    sent
}
```

**Estimated reach**: Highest peak speedup — eliminates both structural
clone AND container clone. Matches hand-written `&mut self` patterns.

**Complexity**: Very high — requires:
1. Field-level mutation analysis in the transpiler
2. A second codegen path (functional vs mutational)
3. New proof templates (the current spec comparison `s@ == expected`
   becomes a pre/post pattern with `old(s)`)
4. Handling of the "returned state" vs "mutated state" semantic gap

**Risks**:
- Most ad-hoc of all approaches
- Doubles codegen complexity
- Proof template changes affect all 10 protocols
- Edge cases in nested mutation (`s_.proposer.queue.push(x)`)

### D. Do nothing — let users hand-optimize hot paths

**Approach**: Accept the current functional-clone overhead. Users who need
peak performance write hand-optimized `&mut self` implementations (the
current wasiq model).

**Estimated reach**: None (baseline).

**Complexity**: None.

**Risks**:
- Permanent 2× gap to hand-tuned implementations
- Per-protocol hand-optimization effort
- Defeats the purpose of auto-generation for performance-sensitive uses

## Recommendation

**Path A (Arc-wrapping) as the primary fix**, with **Path B (persistent
containers) as a conditional follow-up** only if post-Arc benchmarks show
persistent throughput decay from mutated sub-component clones.

**Path C is rejected** as too ad-hoc: it doubles the codegen complexity,
requires new proof templates, and the incremental benefit over A+B is
marginal (A+B already eliminate the structural overhead; C's remaining
benefit is avoiding `Arc::new` allocation for the one changed field).

**Path D is the fallback** if A doesn't pan out, but evidence strongly
suggests it will (Arc::clone is a single atomic increment, well under 1 ns
per call).

## Comparison Matrix

| Strategy | Clone cost | Mutation cost | Verus support | Impl effort | Risk |
|----------|-----------|--------------|---------------|-------------|------|
| A. Arc   | O(1) refcount bump | O(1) Arc::new | Built-in (vstd) | Low | Low |
| B. im    | O(1) structural share | O(log n) | Needs adapter | Medium | Medium |
| C. &mut  | None | In-place | New proof templates | Very high | High |
| D. None  | O(n) deep clone | N/A | N/A | None | None |

## Post-Implementation Results (Phase 40 + Phase 41)

### Phase 40: Struct-level Arc-wrapping (completed, no benefit)
Arc-wrapped sub-component structs (`proposer: Arc<CProposer>`, etc.) for 7 small
protocols + Raft. **No measured benefit** on any benchable protocol.

**Phase 43 comprehensive bench results (HEAD vs c097da0 pre-Arc baseline):**

| Protocol | Nodes | HEAD ops/s | Baseline ops/s | Delta | Notes |
|----------|-------|-----------|---------------|-------|-------|
| RSL | 3 | 32,663 | 16,341 | +100% | Field-level Arc (Phase 41), not struct-level |
| Raft | 3 | 3,613 | 3,612 | +0.03% | Within noise |
| EPaxos | 3 | 4,066 | 4,680 | **-13%** | Arc adds overhead; small state, high mutation |
| PrimaryBackup | 2 | 32,769 | 32,186 | +1.8% | Within noise (±15% variance) |
| PBFT | 4 | <1 | N/A | N/A | Too slow for comparison (3-phase consensus) |

**Conclusion**: Struct-level Arc provides no benefit on any protocol. EPaxos shows
13% regression from Arc refcounting overhead on its small, frequently-mutated state.
RSL's +100% gain comes entirely from field-level Arc (Phase 41), not struct-level.
The original "+24% RSL / +12% Raft" claims were noise. RSL struct-level wrapping
(40.3.g) was deferred and is now **WONTFIX**.

### Phase 41: Field-level Arc-wrapping (complete, measured)

Arc-wrapping individual **collection fields** (HashMap, HashSet, Vec) inside
sub-component structs proved far more effective than struct-level wrapping.

**Five fields Arc-wrapped in RSL (Phase 41.1.b):**

| Struct | Field | Type |
|--------|-------|------|
| `CProposer` | `highest_seqno_requested_by_client_this_view` | `Arc<HashMap<EndPoint, u64>>` |
| `CProposer` | `request_queue` | `Arc<Vec<CRequest>>` |
| `CProposer` | `received_1b_packets` | `Arc<HashSet<CPacket>>` |
| `CExecutor` | `reply_cache` | `Arc<HashMap<EndPoint, CReply>>` |
| `CLearner` | `unexecuted_learner_state` | `Arc<HashMap<COperationNumber, CLearnerTuple>>` |

**Measured result (2026-05-24, 32 threads x 30s x 2 trials):**
- Trial 1: **33,503 ops/s**, 1.12 ms latency
- Trial 2: **31,823 ops/s**, 1.13 ms latency
- Average: **32,663 ops/s** (exceeds 28K target by 16.7%)
- Decay: 5.0% (vs 36% pre-Arc)
- vs pre-Arc baseline (16,341): **+100%** (2x throughput)
- vs wasiq hand-tuned (28,449): **+14.8%**

**Why field-level works but struct-level doesn't:**
Struct-level Arc (`proposer: Arc<CProposer>`) saves the clone of CProposer's
scalars but still deep-clones its internal collections when constructing the
new CProposer value. The hot fields (HashMaps with hundreds of entries,
HashSets with accumulated packets) dominate clone time. Field-level Arc
(`received_1b_packets: Arc<HashSet<CPacket>>`) wraps exactly those hot
collections, making unchanged-path clone O(1) at the granularity that matters.

### Transpiler support (Phase 41.2)

The transpiler fully supports field-level Arc-wrapping via TOML config:

```toml
# In <module>_transpile.toml
arc_wrap_fields = { CProposer = ["highest_seqno_requested_by_client_this_view", "request_queue", "received_1b_packets"] }
```

**What the transpiler handles automatically:**
- Struct field declarations: `pub field: Arc<T>` (codegen/mod.rs)
- Construction sites: new values wrapped with `Arc::new(value)` (translator/mod.rs)
- Unchanged clone sites: `field: field.clone()` dispatches to `Arc::clone` (O(1))
- Proof lemma signatures: `m: &T` instead of `m: T` for auto-deref through `Arc<T>`
- Proof lemma call sites: `&s.field` for auto-deref (translator/mod.rs build_proof_block)
- `use std::sync::Arc;` import injection

**What must be hand-written (in `*Impl.rs` files):**
- Struct definition with `Arc<T>` field type
- `Clone` impl using `Arc::clone` for wrapped fields
- `View` impl using `abstractify_*(&self.field)` (auto-deref through Arc)
- `valid()`/`abstractable()` predicates using `&self.field` (auto-deref)
- `clone_arc_*` helper for proof-compatible Arc cloning

**Pattern for mutation sites:**
The transpiler uses a clone-mutate-wrap pattern rather than `Arc::make_mut`:
```rust
// Generated code for a mutation site:
let mut __field = clone_field(&s.field);  // deep clone the inner T
__field.insert(key, value);               // mutate
CStruct { field: Arc::new(__field), ..s.clone() }  // wrap new value
```
This is simpler than `Arc::make_mut` and works with Verus verification because
the clone function has `ensures res@ == m@`.

### Conclusion

**Strategy A (struct-level Arc) has no measured benefit.** The actual win comes from
**field-level Arc-wrapping of hot collection fields** (a variant of Strategy B's
insight — structural sharing — applied via Arc instead of persistent data structures).
The transpiler automates this via `arc_wrap_fields` TOML config, achieving 2x RSL
throughput improvement over the baseline.

### Phase 47/48: `&mut self` calling convention (supersedes Arc)

Phase 47 manually rewrote ~35 hot-path RSL functions to use `&mut self` instead
of functional rebuild. Phase 48 automated this as a transpiler feature via
`mut_self_types` TOML config.

**Result**: 1.44x speedup over Sushant's hand-tuned implementation. This
eliminates the structural clone problem entirely — the outer struct is never
rebuilt, so there is nothing to Arc-wrap.

**`mut_self_types` config**:
```toml
# In <module>_transpile.toml
mut_self_types = ["CProposer"]
```

When `mut_self_types` is set, the transpiler transforms the first parameter of
each function from `&CProposer` to `&mut self`, emitting in-place field
assignment instead of struct reconstruction.

### Phase 49: Arc removal (post `&mut self`)

With `&mut self` calling convention, Arc-wrapping becomes pure overhead:
- The hot path no longer clones the outer struct, so Arc's O(1) clone is unused
- Arc adds 16 bytes per field + pointer indirection + atomic refcount ops
- Profiling confirmed zero Arc symbols in the hot path

Phase 49 removed Arc from all 5 RSL collection fields. Benchmarks confirmed
zero measurable impact (as predicted — the fields were never cloned on the hot
path after Phase 47).

### Arc vs Direct Ownership Decision Matrix

| Calling convention | Clone pattern | Recommended field wrapping |
|---|---|---|
| Functional (`&State` -> `State`) | Entire struct rebuilt each call | `arc_wrap_fields` for hot collection fields |
| `&mut self` (`mut_self_types`) | No struct rebuild; fields mutated in-place | Direct ownership (no Arc) |

**Transpiler enforcement**: When `mut_self_types` is non-empty, the transpiler
automatically clears `arc_wrap_fields` and `arc_wrap_types` with a warning.
These configurations conflict — Arc adds overhead without benefit under `&mut self`.

**Migration path**: If a protocol transitions from functional to `&mut self`:
1. Add `mut_self_types = ["CState"]` to the TOML
2. Remove or comment out `arc_wrap_fields` (transpiler will clear it anyway)
3. Remove `Arc::new`/`Arc::get_mut` helpers from generated and manual code
4. Replace `Arc<T>` field types with `T` in manual impl files

## Implementation Plan

See TODO.md Phase 40.2 for struct-level Arc steps (dormant), Phase 41 for
field-level Arc steps (complete), Phase 47-48 for `&mut self` calling convention
(active — recommended for all protocols).
