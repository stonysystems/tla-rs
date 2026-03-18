# Model Checker Implementation Lessons (Phase 36.3.5)

Analysis of mature explicit-state model-checker implementations,
focusing on techniques relevant to source-first solver optimization.

## 1. TLC (TLA+ Model Checker)

TLC is the reference model checker for TLA+, developed at Microsoft
Research and maintained by the TLA+ community. Key source:
`tlc2.tool.ModelChecker`, `tlc2.tool.Worker`, `tlc2.tool.TLCState`.

### 1.1 Enabled-Action Generation

**TLC approach**: TLC evaluates each action predicate (`Next` disjunct)
against the current state. For each action, it:
1. Evaluates the action's guard (precondition) first
2. Only if the guard is satisfied, constructs the successor state
3. Uses lazy evaluation — fields not referenced aren't computed

**Lesson for source-first**: Our solver currently constructs full
candidate next-states before checking constraints. TLC's approach is
the opposite: check constraints first, then construct only the fields
needed. The Phase 36.3.4 fix (skip candidate-key filtering) was a step
in this direction, but the predicate-only solver still evaluates all
branch constraints for each existential assignment.

**Actionable improvement**: Split branch constraints into:
- **Guard constraints** (depend only on current state + constants):
  evaluate once per state, skip entire branch if guard fails
- **Assignment constraints** (`s_.field == expr`): evaluate to construct
  the successor
- **Output constraints** (`sent_packets == ...`): evaluate last, only
  to verify consistency

This is the "guard → assign → verify" pipeline that TLC uses
internally. Our solver already partially does this in the enumeration
fallback path (candidate_independent vs candidate_dependent constraints)
but not in the direct-assignment path.

### 1.2 State Fingerprinting / Hashing

**TLC approach**: TLC uses a 64-bit fingerprint (FP64) for state
deduplication. The fingerprint is computed incrementally:
- Each state variable contributes to the fingerprint via `FP64.Extend()`
- The fingerprint is computed as part of state construction (not as a
  separate pass)
- The fingerprint table is a flat array indexed by hash (open addressing)
- Collision handling: TLC accepts small collision probability as a
  trade-off for speed

**Lesson for source-first**: Our dedup uses `canonical_key()` which
produces a full string representation, then inserts into a `BTreeSet`.
This is O(n * key_length) for both computation and comparison.

**Actionable improvements**:
1. **Use hash-based dedup by default**: Replace `BTreeSet<String>` with
   `HashSet<u64>` using a 64-bit fingerprint. Our `hash_compaction64`
   mode already does this but it's not the default.
2. **Incremental fingerprinting**: Compute the hash during state
   construction (in `solve_one_assignment`) rather than after.
3. **Avoid string allocation**: `canonical_key()` allocates a new
   `String` per state. A hash-based approach avoids this entirely.

### 1.3 Worklist Management

**TLC approach**: TLC uses a disk-backed FIFO queue for BFS:
- States are serialized to disk when the queue is large
- Multiple worker threads process states in parallel
- Each worker has a local queue to reduce contention
- State generation is the unit of parallelism (each worker processes
  one state and generates successors independently)

**Lesson for source-first**: Our explorer uses a `VecDeque<FrontierItem>`
in memory. For small state spaces this is fine. For larger spaces
(Paxos 16K+ states), memory pressure from storing full `RuntimeValue`
states in the queue could become significant.

**Actionable improvements**:
1. **Parallel successor generation**: Each state's successors can be
   computed independently. Rayon or a thread pool could parallelize this.
2. **Compact frontier representation**: Store only the state fingerprint
   + parent pointer in the frontier, not the full state. Recompute
   the full state only when needed (for counterexample traces).
3. **DFS with iterative deepening**: For very large state spaces,
   DFS with bounded depth uses O(depth) memory instead of O(frontier).

### 1.4 Avoiding Full-State Materialization

**TLC approach**: TLC's action evaluation is lazy:
- TLA+ expressions are evaluated on-demand
- `UNCHANGED <<x, y, z>>` doesn't copy x, y, z — it just marks them
  as unchanged in the successor state representation
- State representations use field-level copy-on-write

**Lesson for source-first**: Our `solve_one_assignment` starts with
`let mut next_state = current_state.clone()` — a full deep clone of
the entire state. For Paxos with 11 fields × 3 nodes, this is a
significant allocation even though most branches only modify 1-2 fields.

**Actionable improvements**:
1. **Copy-on-write state**: Use `Cow<RuntimeValue>` or a diff-based
   representation. Only clone fields that are actually modified.
2. **Frame-condition optimization**: For `s_.field == s.field` (frame
   conditions), skip the field entirely — it's already correct in the
   cloned state. Our solver currently evaluates these as constraints,
   wasting eval calls.
3. **Lazy field evaluation**: Don't evaluate `s_.field == expr` until
   the field value is needed (e.g., for another constraint or for
   fingerprinting).

## 2. SPIN (Promela Model Checker)

SPIN is the most widely used explicit-state model checker for
concurrent systems.

### Key techniques relevant to source-first:

1. **Partial-order reduction (POR)**: SPIN avoids exploring equivalent
   interleavings by identifying independent transitions. Our solver
   has a `por_heuristic` config option but it's not fully implemented.

2. **State compression**: SPIN can compress states using hash-compaction
   or collapse compression. Our `hash_compaction64` mode is similar.

3. **On-the-fly verification**: SPIN checks properties during
   exploration, not as a post-processing step. We already do this
   for safety invariants.

## 3. Summary of Prioritized Improvements

| Improvement | Impact | Effort | Blocked by |
|------------|--------|--------|------------|
| Guard → assign → verify pipeline | HIGH | MEDIUM | Branch constraint partitioning |
| Frame-condition skip (don't eval `s_.f == s.f`) | HIGH | LOW | Constraint classification |
| Hash-based dedup (default) | MEDIUM | LOW | Already have `hash_compaction64` |
| Copy-on-write state construction | MEDIUM | MEDIUM | RuntimeValue refactoring |
| Parallel successor generation | MEDIUM | HIGH | Thread safety of evaluator |
| Incremental fingerprinting | LOW | MEDIUM | Hash computation during solve |
| Compact frontier (fingerprint only) | LOW | MEDIUM | State reconstruction |

**Recommended next optimization** (based on effort/impact ratio):
Frame-condition skip — when the solver encounters `s_.field == s.field`,
it currently evaluates `s.field`, copies it to `next_state.field`, and
checks equality. Since `next_state` starts as a clone of `current_state`,
these frame conditions are tautological. Detecting and skipping them
would reduce evaluator calls by ~70% for most branches (since most
fields are frame conditions).
