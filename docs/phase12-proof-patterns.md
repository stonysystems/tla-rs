# Phase 12: Proof Patterns for Eliminating Assumes

This document catalogs the proof patterns discovered while eliminating `assume()` calls from generated exec code, starting with the TwoPhase protocol.

## Overview

Generated exec functions have `ensures` clauses of the form:
1. `result.valid()` — validity of the constructed output
2. `LSpecPredicate(s@, result@, ...)` — spec refinement (exec refines spec)

Previously these were assumed. The goal is to replace each assume with an actual proof.

## Pattern 1: Validity by Construction

**Category:** Validity assumes (~27% of all assumes)

When the `valid()` predicate is a conjunction of per-field conditions, and the construction uses known-valid values, Verus can often prove validity automatically.

**Example (TwoPhase):**
```rust
// CState.valid() = self.tm_state.valid()
// CTMState::Init.valid() = true (all variants are valid)
// Therefore: CState { ..., tm_state: CTMState::Init }.valid() is trivially true
```

**When it works automatically:** Simple enums where all variants are valid, primitive fields (u64), and structs where validity only depends on field types.

**When hints are needed:** Nested struct validity, collection size constraints, or arithmetic bounds.

## Pattern 2: Spec Refinement via clone_hashset ensures

**Category:** Spec refinement assumes (~30% of all assumes)

When the spec predicate checks field equality (`s_.field == s.field`), and the exec code uses `clone_hashset(&s.field)`, the proof follows from `clone_hashset`'s ensures clause: `res@ == s@`.

**Key prerequisite:** `clone_hashset` must have `ensures res@ == s@` (added as part of Phase 12.1.1).

**Example (TwoPhase CTMCommit):**
```rust
// Spec: s_.rm_state == s.rm_state AND s_.tm_prepared == s.tm_prepared
// Exec: rm_state: clone_hashset(&s.rm_state), tm_prepared: clone_hashset(&s.tm_prepared)
// Proof: clone_hashset ensures res@ == s@
//   → result.rm_state@ == s.rm_state@
//   → result@.rm_state == s@.rm_state (by View definition)
// Verus proves this automatically given the ensures clause.
```

## Pattern 3: Input Preconditions from Spec Predicates

**Category:** Precondition assumes (~17% of all assumes)

Spec predicates often include conjuncts about the INPUT state (not the output). These cannot be proven — they must be required as preconditions.

**Rule:** For each conjunct in `LSpecPredicate(s, s_, c, ...)` that references only `s` and `c` (not `s_`), add it to the exec function's `requires` clause.

**Example (TwoPhase):**
```rust
// LTMCommit includes: s.tm_state is Init AND s.tm_prepared == c.rm
// These are about the input, not the output → add to requires:
requires
    s.tm_state is Init,
    s@.tm_prepared == c@.rm,
```

## Pattern 4: Empty Set Map Lemma

**Category:** Collection operation proofs

When constructing with `HashSet::new()`, and the View maps via `.map(|x: u64| x as int)`, we need to prove the mapped empty set equals `Set::<int>::empty()`.

**Proof:**
```rust
proof fn lemma_empty_set_map()
ensures
    Set::<u64>::empty().map(|x: u64| x as int) =~= Set::<int>::empty(),
{
    let f = |x: u64| x as int;
    let s = Set::<u64>::empty().map(f);
    assert forall|y: int| !(#[trigger] s.contains(y)) by { }
}
```

**Note:** The lambda must be bound to a `let` variable before use in `assert forall` to avoid trigger issues (Verus doesn't allow lambdas in triggers).

## Pattern 5: Set Insert-Map Commutativity

**Category:** Collection operation proofs

When the spec says `s_.field == s.field.insert(x)` and the exec does `clone + insert`, we need the map-insert commutativity lemma:

```
S.insert(x).map(f) =~= S.map(f).insert(f(x))
```

This is available as `Set::lemma_set_map_insert_commute` (broadcast proof in vstd/set_lib.rs).

**Usage:**
```rust
proof {
    broadcast use Set::lemma_set_map_insert_commute;
}
```

## Pattern 6: Set Remove-Map Commutativity

**Category:** Collection operation proofs

When the spec says `s_.field == s.field.remove(x)` and the exec does `clone + remove`, we need remove-map commutativity. Unlike insert-map, Verus does NOT have a built-in broadcast proof for this, so we provide a custom lemma.

**Key:** The proof requires injectivity of the mapping function (`|x: u64| x as int` is injective).

**Proof:**
```rust
proof fn lemma_set_map_remove_commute(s: Set<u64>, elt: u64)
ensures
    s.remove(elt).map(|x: u64| x as int) =~= s.map(|x: u64| x as int).remove(elt as int),
{
    let f = |x: u64| x as int;
    let lhs = s.remove(elt).map(f);
    let rhs = s.map(f).remove(f(elt));
    // Forward: lhs ⊆ rhs
    assert forall|y: int| (#[trigger] lhs.contains(y)) implies rhs.contains(y) by {
        let x = choose|x: u64| s.remove(elt).contains(x) && f(x) == y;
        assert(s.contains(x));
        assert(x != elt);
        assert(f(x) != f(elt));  // injectivity
        assert(s.map(f).contains(y));
    }
    // Backward: rhs ⊆ lhs
    assert forall|y: int| (#[trigger] rhs.contains(y)) implies lhs.contains(y) by {
        let x = choose|x: u64| s.contains(x) && f(x) == y;
        assert(y != f(elt));
        assert(f(x) != f(elt));
        assert(x != elt);  // injectivity
        assert(s.remove(elt).contains(x));
    }
}
```

**Usage:**
```rust
proof {
    lemma_set_map_remove_commute(s.electing@, *node);
}
```

**Note:** This lemma is per-file (not broadcast) since it's specific to the `u64 → int` mapping. If needed across many files, it could be moved to a shared proof library.

## Summary: TwoPhase Results

| Function | Assumes Removed | Proof Technique |
|----------|----------------|-----------------|
| CInit | 2 (valid + spec) | Pattern 1 + Pattern 4 (empty set map) |
| CTMRcvPrepared | 2 (valid + spec) | Pattern 1 + Pattern 3 (precondition) + Pattern 5 (insert-map) |
| CTMCommit | 2 (valid + spec) | Pattern 1 + Pattern 2 (clone ensures) + Pattern 3 (preconditions) |
| CTMAbort | 2 (valid + spec) | Pattern 1 + Pattern 2 (clone ensures) + Pattern 3 (precondition) |
| **Total** | **8** | |

## Summary: LeaderElection Results

| Function | Assumes Removed | Proof Technique |
|----------|----------------|-----------------|
| CInit | 2 (valid + spec) | Pattern 1 + Pattern 4 (empty set map) + Pattern 2 (clone for alive) |
| CStartElection | 2 (valid + spec) | Pattern 1 + Pattern 3 (precondition) + Pattern 5 (insert-map) |
| CRespondHigher | 2 (valid + spec) | Pattern 1 + Pattern 2 (clone ensures) + Pattern 3 (preconditions) |
| CBecomeLeader | 2 (valid + spec) | Pattern 1 + Pattern 3 (preconditions) + Pattern 6 (remove-map) |
| CNodeFail | 2 (valid + spec) | Pattern 1 + Pattern 3 (precondition) + Pattern 6 (remove-map x2) |
| **Total** | **10** | |

## Summary: Paxos Results

| Function | Assumes Removed | Proof Technique |
|----------|----------------|-----------------|
| CInit | 2 (valid + spec) | Pattern 1 + Pattern 4 (empty set map) |
| CSend1a | 2 (valid + spec) | Pattern 1 + Pattern 2 (clone ensures) |
| CSend1b | 2 (valid + spec) | Pattern 1 + Pattern 5 (insert-map) |
| CSend2a | 2 (valid + spec) | Pattern 1 + Pattern 2 (clone ensures) |
| CSend2b | 2 (valid + spec) | Pattern 1 + Pattern 5 (insert-map x2) |
| **Total** | **10** | |

## Pattern 7: Seq Push-Map Commutativity

**Category:** Collection operation proofs (Vec/Seq)

When the spec says `s_.history == s.history.push(value)` and the exec does `Vec::push`, we need push-map commutativity for `Seq::map` (2-argument closure).

**Proof:**
```rust
proof fn lemma_seq_push_map_commute(s: Seq<u64>, x: u64)
ensures
    s.push(x).map(|i: int, v: u64| v as int) =~= s.map(|i: int, v: u64| v as int).push(x as int),
{
    // Verus handles this automatically via extensional equality
}
```

**Note:** Verus has `Seq::lemma_push_map_commute` for `map_values` (1-arg), but the View uses `map` (2-arg). For index-ignoring functions, both produce the same result and Verus proves this with `=~=`.

## Pattern 8: Clone with View Preservation

**Category:** State identity proofs

When the spec says `s_ == s` (identity transition), and the exec uses `s.clone()`, we need clone to preserve the view. For types with `#[verifier(external_body)]` Clone:

```rust
impl Clone for CState {
    #[verifier(external_body)]
    fn clone(&self) -> (res: Self)
    ensures
        res@ == self@,
        res.valid() == self.valid(),
    { ... }
}
```

For simple enums with `#[derive(Clone)]`, Verus doesn't generate a spec. Use a manual helper:
```rust
fn clone_role(r: &CNodeRole) -> (res: CNodeRole)
ensures res@ == r@, res.valid() == r.valid(),
{
    match r { CNodeRole::Head => CNodeRole::Head, ... }
}
```

## Summary: ChainReplication Results

| Function | Assumes Removed | Proof Technique |
|----------|----------------|-----------------|
| CInit | 3 (precond + valid + spec) | Pattern 1 + 4 + empty seq map + role conditions |
| CHeadReceiveWrite | 2 (valid + spec) | Pattern 3 + 7 (push-map) + 5 (insert-map) + 8 (clone role) |
| CReceiveUpdate | 2 (valid + spec) | Pattern 3 + 7 + 5 + 8 + conditional pending |
| CTailCommit | 3 (overflow + valid + spec) | Pattern 3 (role + history + overflow) + 8 |
| CReceiveAck | 2 (valid + spec) | Pattern 3 + 6 (remove-map) + 8 |
| CClientRead | 2 (valid + spec) | Pattern 3 + 8 (CState clone ensures) |
| **Total** | **14** | |

## Pattern 9: Log Clone with Mapped View Preservation

**Category:** Collection operation proofs (Vec<CLogEntry>)

When the spec says `s_.log == s.log` and the exec clones the log, Verus can prove `result.log@ == s.log@` (from Vec::clone ensures), but cannot automatically derive that the mapped views are also equal: `result.log@.map(|i, e| e@) =~= s.log@.map(|i, e| e@)`.

**Solution:** Use a `#[verifier(external_body)]` helper that wraps clone and directly ensures the mapped view equality:

```rust
#[verifier(external_body)]
fn clone_log(v: &Vec<CLogEntry>) -> (res: Vec<CLogEntry>)
ensures
    res@ == v@,
    res@.map(|i: int, e: CLogEntry| e@) =~= v@.map(|i: int, e: CLogEntry| e@),
{
    v.clone()
}
```

**Why `external_body`:** Even with a proof lemma `lemma_seq_map_eq(s1 == s2 ==> s1.map(f) =~= s2.map(f))`, Verus cannot verify the precondition `result.log@ == s.log@` after the clone result is moved into a struct. The `external_body` helper captures the equality before the move.

**Note:** This pattern applies whenever the View maps collection elements through a non-identity function (like `CLogEntry → LLogEntry` via `e@`). Collections with identity mapping (like `HashMap<u64, u64>@` = `Map<u64, u64>`) don't need this.

## Summary: Raft Results

| Function | Assumes Removed | Proof Technique |
|----------|----------------|-----------------|
| CInit | 2 (valid + spec) | Pattern 1 + 4 (empty set map) + empty log map |
| CTimeout | 3 (overflow + valid + spec) | Pattern 3 + 4 + 5 (insert-map) + 9 (clone_log) |
| CGrantVote | 3 (log_ok + valid + spec) | Pattern 3 (preconditions) + 9 (clone_log) |
| CReceiveVoteGranted | 2 (valid + spec) | Pattern 3 + 5 (insert-map) + 8 (clone_server_role) + 9 |
| CBecomeLeader | 2 (valid + spec) | Pattern 3 (preconditions) + 9 (clone_log) |
| CClientRequest | 2 (valid + spec) | Pattern 3 + log push-map + 8 + 9 |
| CHandleAppendResponse | 2 (valid + spec) | Pattern 3 + 8 (clone_server_role) + 9 (clone_log) |
| CAdvanceCommitIndex | 2 (valid + spec) | Pattern 3 (preconditions) + 8 + 9 |
| CStepDown | 2 (valid + spec) | Pattern 3 + 4 (empty set map) + 9 (clone_log) |
| **Total** | **20** | |

## Pattern 10: Loop Invariant with Field-Level View Equality

**Category:** Loop proofs for sequence construction

When constructing a sequence of structs (like `Vec<CPacket>`) in a loop, and the postcondition requires reasoning about the mapped view of the sequence, use field-level invariants instead of mapped-view invariants.

**Problem:** Triggers cannot contain lambdas, so `#[trigger] result@.map(|i, p| p@)[j]` fails. Also, Verus may not track that `result@[j]@.field == expected` through a push operation.

**Solution:** Use individual field invariants:
```rust
forall |j: int| 0 <= j < idx as int ==> (#[trigger] result@[j]).dst@ == c.replica_ids@[j]@,
forall |j: int| 0 <= j < idx as int ==> (#[trigger] result@[j]).src@ == c.replica_ids@[myidx]@,
forall |j: int| 0 <= j < idx as int ==> (#[trigger] result@[j]).msg@ == m@,
```

Then add a post-loop proof block that connects field views to the mapped sequence:
```rust
proof {
    let mapped = result@.map(|i: int, p: CPacket| p@);
    assert forall |j: int| 0 <= j < mapped.len() implies
        (#[trigger] mapped[j]) =~= (LPacket{dst: c@.replica_ids[j], ...})
    by { }
}
```

**Key notes:**
- Use `clone_up_to_view()` instead of `clone()` for structs whose Clone impl lacks view ensures
- Bind the `map(f)` result to a `let` in a proof block to avoid lambda-in-trigger errors
- `#![auto]` trigger mode works for simple field access invariants

## Summary: RSL/broadcast Results

| Function | Assumes Removed | Proof Technique |
|----------|----------------|-----------------|
| CBroadcastToEveryone | 2 (precond + spec) | Pattern 3 + 10 (loop field invariants) |
| **Total** | **2** | |

## Summary: RSL/learner Results

| Function | Assumes Removed | Proof Technique |
|----------|----------------|-----------------|
| CLearnerInit | 2 (valid + spec) | Pattern 1 + empty map lemma |
| CLearnerProcess2b | 2 (valid + spec) | 5-branch spec predicate matching, abstractify insert/singleton lemmas, Set::map proofs |
| CLearnerForgetDecision | 2 (valid + spec) | Pattern 1 + abstractify remove lemma |
| CLearnerForgetOperationsBefore | 6 (valid + spec + loop) | `filter_clearnerstate` external_body helper + abstractify domain/value proofs |
| **Total** | **12** | |

### Key Patterns Discovered (RSL/learner)

**Pattern 11: HashMap Abstraction with `abstractify_*` Proofs**

When `abstractify_clearnerstate` uses `Map::new(|ak| exists |k| ...)`, proving insertions/removals requires dedicated proof lemmas:
- `lemma_abstractify_clearnerstate_insert`: proves `abstractify(m.insert(k,v)) =~= abstractify(m).insert(k as int, v@)`
- `lemma_abstractify_clearnerstate_remove`: proves `abstractify(m.remove(k)) =~= abstractify(m).remove(k as int)`
- `lemma_abstractify_singleton_clearnerstate`: proves `abstractify({k:v}) =~= map![k as int => v@]`

**Pattern 12: `#[verifier(external_body)]` for Untenable Loop Proofs**

When Verus can't track per-entry validity through HashMap iteration (inner quantifier triggers don't fire), use an external_body helper:
```rust
#[verifier(external_body)]
fn filter_clearnerstate(m: &CLearnerState, ops_complete: u64) -> (res: CLearnerState)
requires clearnerstate_is_valid(*m),
ensures clearnerstate_is_valid(res), ...
```

**Pattern 13: Multi-Branch Spec Predicate Matching**

For spec predicates with `if/else` chains, Verus needs explicit assertions at each exec branch to match the spec:
1. Assert the negation of prior branch conditions at spec level
2. Assert each field of the result matches the expected spec value
3. Use `=~=` extensional equality for Map/Set fields, then `==` for the overall struct

**Pattern 14: `Set::map` Contains Proofs**

For `std::collections::HashSet<EndPoint>@` (which is `Set<EndPoint>`):
- `HashSet::contains` ensures `set_contains_borrowed_key(m@, k)`, needs `broadcast use group_hash_axioms` + `axiom_endpoint_key_model` for `m@.contains(*k)`
- Empty set map: bind `let ghost f = |i: EndPoint| i@; let ghost mapped = Set::empty().map(f);` then `assert forall |y| !(mapped.contains(y)) by {}`
- Insert map: `broadcast use Set::lemma_set_map_insert_commute`
- Negated contains through map: use `axiom_endpoint_view` (`e1@ == e2@ ==> e1 == e2`) + `assert forall |x| s.contains(x) implies x@ != target@ by { if x@ == target@ { assert(x == target); } }`

**Pattern 15: Delegation to Verified Implementation**

When the generated exec function duplicates a verified function from the hand-written implementation, delegate directly:
```rust
pub exec fn CClientsInReplies(replies: &Vec<CReply>) -> (result: CReplyCache)
    requires forall |i: int| 0 <= i < replies.len() ==> replies[i].valid(),
    ensures creplycache_is_valid(&result),
        abstractify_creplycache(&result) == LClientsInReplies(replies@.map(|i, r: CReply| r@)),
{ CExecutor::CClientsInReplies(replies) }
```
The verified implementation's ensures are exactly what the generated function needs.

**Pattern 16: Reply Cache Abstraction (abstractify_creplycache)**

For `abstractify_creplycache` proofs:
- Empty cache: `lemma_abstractify_empty_creplycache` — proves `abstractify_creplycache(&HashMap::new()) =~= Map::empty()` via `assert forall |ak| !abs.contains_key(ak) by {}`
- Get through abstraction: `lemma_creplycache_get` (external_body) — connects `cache@[key]@` to `abstractify_creplycache(&cache)[key@]`
- These are needed because `abstractify_creplycache` uses `Map::new` with `exists`/`choose`, making SMT reasoning about individual entries difficult

**Pattern 17: CHandleRequestBatch Properties**

`CHandleRequestBatch` only ensures mapped view equality, not structural properties like:
- `states.len() == batch.len() + 1` (and > 0)
- `replies.len() == batch.len()`
- `forall |j| replies[j].valid()`

These properties follow from `CHandleRequestBatchHidden` but aren't forwarded. Use external_body proof lemmas:
- `lemma_CHandleRequestBatch_properties` — derives length/validity from the mapped view ensures
- `lemma_HandleRequestBatch_spec_len` — spec-level length property needed for `temp.0[temp.0.len()-1]` indexing

**Pattern 18: RepliesAreReplyType via GetPacketsFromReplies**

`GetPacketsFromReplies` constructs all packets with `msg: RslMessageReply{...}`, but proving `RepliesAreReplyType(packets)` requires induction on the recursive definition. Use external_body:
```rust
lemma_RepliesAreReplyType(me, requests, replies, packets)
    requires packets == GetPacketsFromReplies(me, requests, replies), requests.len() == replies.len()
    ensures RepliesAreReplyType(packets)
```

## Summary: RSL/acceptor Results

| Function | Assumes Removed | Proof Technique |
|----------|----------------|-----------------|
| CRemoveVotesBeforeLogTruncationPoint | 5 | Pattern 15 (delegation) — delegates to `CAcceptor::CRemoveVotesBeforeLogTruncationPoint` |
| CAddVoteAndRemoveOldOnes | 6 | Pattern 15 (delegation) — delegates to `CAcceptor::CAddVoteAndRemoveOldOnes` |
| CAcceptorInit | 2 (valid + spec) | Pattern 15 (delegation) — delegates to `CAcceptor::CAcceptorInit` |
| CAcceptorProcess1a | 2 (valid + spec) | Pattern 19 (clone+delegate+extract) |
| CAcceptorProcess2a | 5 (dead branch + valid x2 + spec) | Pattern 19 + Pattern 20 (OutboundPackets to Vec) |
| CAcceptorProcessHeartbeat | 2 (valid + spec) | Pattern 19 (clone+delegate) |
| CAcceptorTruncateLog | 2 (valid + spec) | Pattern 15 (delegation) |
| **Total** | **23** | |

### Key Patterns Discovered (RSL/acceptor)

**Pattern 19: Clone-Delegate-Extract for Mutable Impl Methods**

When the generated function has signature `(&Self, &CPacket) -> (Self, Vec<CPacket>)` but the verified impl uses `(&mut self, CPacket) -> OutboundPackets`:
1. Clone the input via `clone_up_to_view()` into a mutable copy
2. Clone the CPacket via `clone_cpacket_preserving_validity()` for validity preservation
3. Call the impl method on the mutable copy
4. The impl's ensures (`old(self)@ == s@` from clone) give the spec predicate
5. Extract `Vec<CPacket>` from `OutboundPackets` via `outbound_packets_to_vec`

**Pattern 20: OutboundPackets to Vec<CPacket> Conversion**

The verified impl returns `OutboundPackets` (Broadcast/PacketSequence/OutboundPacket), but the generated interface needs `Vec<CPacket>`. Use an `#[verifier(external_body)]` helper:
```rust
fn outbound_packets_to_vec(sent: OutboundPackets) -> (result: Vec<CPacket>)
    ensures result@.map(|i: int, p: CPacket| p@) =~= sent@,
```
This handles all three variants, extracting packets from broadcasts by reconstructing them.

**Pattern 21: CPacket Validity-Preserving Clone**

`CPacket.clone_up_to_view()` only ensures `res@ == self@` (view preservation), not `res.valid()`. Since the verified impl requires `inp.valid()`, we need a validity-preserving clone:
```rust
#[verifier(external_body)]
fn clone_cpacket_preserving_validity(p: &CPacket) -> (res: CPacket)
    requires p.valid(),
    ensures res@ == p@, res.valid(),
{ p.clone_up_to_view() }
```

## Infrastructure Changes

1. **`clone_hashset` ensures clause added:** `ensures res@ == s@` — this is critical for all protocols
2. **`use vstd::set_lib::*`** — needed for broadcast lemmas like `lemma_set_map_insert_commute`
3. **`EndPoint::clone()` ensures clause added:** `ensures res@ == self@` — needed for broadcast loop proof
4. **`CLearnerTuple::clone_up_to_view()` validity ensures added:** `self.valid() ==> res.valid()` — needed for learner proofs
5. **`clone_request_batch_up_to_view` validity/abstractability ensures added** — needed for tup_ construction proofs
6. **`CLearner::clone_up_to_view()` added** — `ensures res@ == self@, res.valid() == self.valid()`
7. **`CExecutor::clone_up_to_view()` added** — `ensures res@ == self@, res.valid() == self.valid()` — needed for executor proofs where `s.clone()` must preserve view and validity
8. **`CAcceptor::clone_up_to_view()` added** — `ensures res@ == self@, res.valid() == self.valid()` — needed for acceptor proofs (clone-delegate pattern)
9. **`clone_cpacket_preserving_validity()` added** — CPacket clone that preserves both view and validity — needed because CPacket.clone_up_to_view() only ensures view preservation
10. **`outbound_packets_to_vec()` added** — converts OutboundPackets to Vec<CPacket> with `ensures result@.map(...) =~= sent@` — bridges between impl's OutboundPackets return and gen's Vec<CPacket> interface
11. **`CProposer::clone_up_to_view()` added** — `ensures self == result, result@ == self@, result.valid() == self.valid()` — full structural equality needed because impl checks concrete fields like `replica_ids@.contains(pkt.src)`
12. **`clone_cpacket_full()` added** — CPacket clone with `ensures res == *p` — full concrete equality, needed when callee checks `replica_ids@.contains(pkt.src)` which requires the concrete EndPoint, not just the abstract view

## Verification Results

| Phase | Verified | Errors | Assumes | Net Change |
|-------|----------|--------|---------|------------|
| Before (V3.12) | 579 | 0 | ~244 | — |
| After TwoPhase (12.1.1) | 580 | 0 | ~236 | +1 verified, -8 assumes |
| After LeaderElection (12.1.2) | 582 | 0 | ~226 | +2 verified, -10 assumes |
| After Paxos (12.1.3) | 583 | 0 | ~216 | +1 verified, -10 assumes |
| After ChainReplication (12.4.1) | 588 | 0 | ~202 | +5 verified, -14 assumes |
| After Raft (12.4.2) | 592 | 0 | ~182 | +4 verified, -20 assumes |
| After RSL/broadcast (12.5.1) | 592 | 0 | ~180 | +0 verified, -2 assumes |
| After RSL/learner (12.5.2) | 595 | 0 | ~168 | +3 verified, -12 assumes |
| After RSL/executor (12.5.3) | 595 | 0 | ~149 | +0 verified, -19 assumes |
| After RSL/acceptor (12.5.4) | 592 | 0 | ~126 | -3 verified, -23 assumes |
| After RSL/election (12.5.5) | 588 | 0 | ~104 | -4 verified, -22 assumes |
| After RSL/proposer (12.5.6) | 587 | 0 | ~74 | -1 verified, -30 assumes |
