# Recursive Pattern Analysis for RSL Spec Functions

This document analyzes the 6 recursive helper functions in RSL specs that need to be transpiled to loop-based implementations.

## Summary

| Function | File | Pattern | Complexity |
|----------|------|---------|------------|
| `RemoveAllSatisfiedRequestsInSequence` | election.rs | **Filter** | Simple |
| `RemoveExecutedRequestBatch` | election.rs | **Fold** | Nested (calls filter) |
| `GetPacketsFromReplies` | executor.rs | **Map** | Simple (zip-style) |
| `LClientsInReplies` | executor.rs | **Fold to Map** | Simple |
| `ExtractSentPacketsFromIos` | replica.rs | **Filter** | Simple |
| `BuildLBroadcast` | broadcast.rs | **Map** | Simple |

## Detailed Analysis

### 1. RemoveAllSatisfiedRequestsInSequence (Filter Pattern)

**Location**: `src/protocol/RSL/election.rs:51`

**Signature**:
```rust
pub open spec fn RemoveAllSatisfiedRequestsInSequence(s: Seq<Request>, r: Request) -> Seq<Request>
```

**Pattern**: Filter - keeps elements that do NOT satisfy a predicate
```rust
if s.len() == 0 {
    Seq::empty()
} else if RequestSatisfiedBy(s[0], r) {
    // Skip this element (satisfied)
    RemoveAllSatisfiedRequestsInSequence(s.drop_first(), r)
} else {
    // Keep this element (not satisfied)
    seq![s[0]] + RemoveAllSatisfiedRequestsInSequence(s.drop_first(), r)
}
```

**Target Loop Implementation**:
```rust
let mut result = Vec::new();
for i in 0..s.len() {
    if !RequestSatisfiedBy(&s[i], &r) {
        result.push(s[i].clone());
    }
}
result
```

**Loop Invariant**:
```rust
invariant result@ == s@.take(i as int).filter(|x| !RequestSatisfiedBy(x, r@))
```

---

### 2. RemoveExecutedRequestBatch (Fold Pattern)

**Location**: `src/protocol/RSL/election.rs:198`

**Signature**:
```rust
pub open spec fn RemoveExecutedRequestBatch(reqs: Seq<Request>, batch: RequestBatch) -> Seq<Request>
```

**Pattern**: Fold/Reduce - applies filter iteratively over batch
```rust
if batch.len() == 0 {
    reqs  // base case: return accumulated result
} else {
    RemoveExecutedRequestBatch(
        RemoveAllSatisfiedRequestsInSequence(reqs, batch[0]),  // accumulator update
        batch.drop_first()
    )
}
```

**Target Loop Implementation**:
```rust
let mut result = reqs.clone();
for i in 0..batch.len() {
    result = RemoveAllSatisfiedRequestsInSequence(&result, &batch[i]);
}
result
```

**Loop Invariant**:
```rust
invariant result@ == fold(batch@.take(i as int), reqs@, |acc, r| RemoveAllSatisfiedRequestsInSequence(acc, r))
```

---

### 3. GetPacketsFromReplies (Map/Zip Pattern)

**Location**: `src/protocol/RSL/executor.rs:63`

**Signature**:
```rust
pub open spec fn GetPacketsFromReplies(me: AbstractEndPoint, requests: Seq<Request>, replies: Seq<Reply>) -> Seq<RslPacket>
```

**Pattern**: Map with zip - transforms two parallel sequences into one
```rust
if requests.len() == 0 {
    Seq::empty()
} else {
    seq![LPacket{
        dst: requests[0].client,
        src: me,
        msg: RslMessage::RslMessageReply{
            seqno_reply: requests[0].seqno,
            reply: replies[0].reply,
        }
    }] + GetPacketsFromReplies(me, requests.drop_first(), replies.drop_first())
}
```

**Target Loop Implementation**:
```rust
let mut result = Vec::new();
for i in 0..requests.len() {
    result.push(CPacket {
        dst: requests[i].client.clone(),
        src: me.clone(),
        msg: CRslMessage::CRslMessageReply {
            seqno_reply: requests[i].seqno,
            reply: replies[i].reply.clone(),
        }
    });
}
result
```

**Loop Invariant**:
```rust
invariant result.len() == i
invariant forall |j| 0 <= j < i ==> result[j].dst == requests[j].client
invariant forall |j| 0 <= j < i ==> result[j].src == me
```

---

### 4. LClientsInReplies (Fold to Map Pattern)

**Location**: `src/protocol/RSL/executor.rs:99`

**Signature**:
```rust
pub open spec fn LClientsInReplies(replies: Seq<Reply>) -> ReplyCache
```

**Pattern**: Fold to build a Map
```rust
if replies.len() == 0 {
    Map::empty()
} else {
    LClientsInReplies(replies.drop_first())
        .insert(replies[0].client, replies[0])
}
```

**Note**: This processes from end-to-start, so later entries override earlier ones with same client.

**Target Loop Implementation**:
```rust
let mut result = HashMap::new();
// Process in reverse to match spec semantics (last entry wins)
for i in (0..replies.len()).rev() {
    result.insert(replies[i].client.clone(), replies[i].clone());
}
result
```

**Loop Invariant** (with reverse iteration):
```rust
invariant result@ == LClientsInReplies(replies@.skip(i as int))
```

---

### 5. ExtractSentPacketsFromIos (Filter Pattern)

**Location**: `src/protocol/RSL/replica.rs:493`

**Signature**:
```rust
pub open spec fn ExtractSentPacketsFromIos(ios: Seq<RslIo>) -> Seq<RslPacket>
```

**Pattern**: Filter + Map - filters Send operations and extracts packet
```rust
if ios.len() == 0 {
    Seq::empty()
} else if ios[0] is Send {
    seq![ios[0]->s] + ExtractSentPacketsFromIos(ios.drop_first())
} else {
    ExtractSentPacketsFromIos(ios.drop_first())
}
```

**Target Loop Implementation**:
```rust
let mut result = Vec::new();
for i in 0..ios.len() {
    if let CRslIo::CSend { s } = &ios[i] {
        result.push(s.clone());
    }
}
result
```

**Loop Invariant**:
```rust
invariant result@ == ios@.take(i as int).filter(|io| io is Send).map(|io| io->s)
```

---

### 6. BuildLBroadcast (Map Pattern)

**Location**: `src/protocol/RSL/broadcast.rs:20`

**Signature**:
```rust
pub open spec fn BuildLBroadcast(src: AbstractEndPoint, dsts: Seq<AbstractEndPoint>, m: RslMessage) -> Seq<RslPacket>
```

**Pattern**: Simple Map - transforms destinations to packets
```rust
if dsts.len() == 0 {
    Seq::empty()
} else {
    seq![LPacket{dst: dsts[0], src: src, msg: m}] + BuildLBroadcast(src, dsts.skip(1), m)
}
```

**Target Loop Implementation**:
```rust
let mut result = Vec::new();
for i in 0..dsts.len() {
    result.push(CPacket {
        dst: dsts[i].clone(),
        src: src.clone(),
        msg: m.clone(),
    });
}
result
```

**Loop Invariant**:
```rust
invariant result.len() == i
invariant forall |j| 0 <= j < i ==> result[j] == LPacket{dst: dsts[j], src: src, msg: m}
```

---

## Pattern Categories

### Filter Pattern (2 functions)
- `RemoveAllSatisfiedRequestsInSequence` - filter by NOT satisfying predicate
- `ExtractSentPacketsFromIos` - filter by enum variant + extract field

**Template**:
```rust
for i in 0..s.len() {
    if predicate(&s[i]) {
        result.push(transform(&s[i]));
    }
}
```

### Map Pattern (2 functions)
- `GetPacketsFromReplies` - zip-style map of two sequences
- `BuildLBroadcast` - simple map with captured context

**Template**:
```rust
for i in 0..s.len() {
    result.push(transform(&s[i], context));
}
```

### Fold Pattern (2 functions)
- `RemoveExecutedRequestBatch` - iterative accumulator update
- `LClientsInReplies` - build map from sequence

**Template**:
```rust
let mut acc = initial;
for i in 0..s.len() {
    acc = combine(acc, &s[i]);
}
acc
```

---

## Implementation Priority

1. **Filter Pattern** - Most common, simplest to implement
2. **Map Pattern** - Straightforward transformation
3. **Fold Pattern** - Requires more complex invariants

## Manual Implementation References

- `ElectionImpl.rs` - Contains `CRemoveAllSatisfiedRequestsInSequence`, `CRemoveExecutedRequestBatch`
- `ExecutorImpl.rs` - Contains `CGetPacketsFromReplies`, `CClientsInReplies`
- `broadcast_i.rs` - Contains `CBroadcastToEveryone`
- `ReplicaImpl.rs` - Contains I/O extraction logic
