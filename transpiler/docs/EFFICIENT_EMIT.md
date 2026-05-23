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

## Implementation Plan

See TODO.md Phase 40.2 for the detailed Arc-wrapping implementation steps.
