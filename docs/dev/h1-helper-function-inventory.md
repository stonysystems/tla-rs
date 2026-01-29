# H1: Helper Function Inventory

## Status: COMPLETE [26:01:29]

## Goal
Identify all helper functions in RSL spec files that need exec implementations.

## Inventory

### election.rs

| Function | Signature | Complexity |
|----------|-----------|------------|
| `ComputeSuccessorView` | `(Ballot, LConstants) -> Ballot` | Simple |
| `BoundRequestSequence` | `(Seq<Request>, UpperBound) -> Seq<Request>` | Simple |
| `RequestsMatch` | `(Request, Request) -> bool` | Simple |
| `RequestSatisfiedBy` | `(Request, Request) -> bool` | Simple |
| `RemoveAllSatisfiedRequestsInSequence` | `(Seq<Request>, Request) -> Seq<Request>` | **Recursive** |
| `RemoveExecutedRequestBatch` | `(Seq<Request>, RequestBatch) -> Seq<Request>` | **Recursive** |

### types.rs

| Function | Signature | Complexity |
|----------|-----------|------------|
| `BalLt` | `(Ballot, Ballot) -> bool` | Simple |
| `BalLeq` | `(Ballot, Ballot) -> bool` | Simple |

### configuration.rs

| Function | Signature | Complexity |
|----------|-----------|------------|
| `LMinQuorumSize` | `(LConfiguration) -> int` | Simple |
| `ReplicasDistinct` | `(Seq, int, int) -> bool` | Simple |
| `ReplicasIsUnique` | `(Seq) -> bool` | Quantifier |
| `WellFormedLConfiguration` | `(LConfiguration) -> bool` | Quantifier |
| `IsReplicaIndex` | `(int, EndPoint, LConfiguration) -> bool` | Simple |
| `GetReplicaIndex` | `(EndPoint, LConfiguration) -> int` | Calls external |

### upper_bound.rs (common)

| Function | Signature | Complexity |
|----------|-----------|------------|
| `LeqUpperBound` | `(int, UpperBound) -> bool` | Simple |
| `LtUpperBound` | `(int, UpperBound) -> bool` | Simple |
| `UpperBoundedAddition` | `(int, int, UpperBound) -> int` | Simple |

## Dependency Graph

```
election.rs predicates
  └─> ComputeSuccessorView (local)
  └─> BoundRequestSequence (local)
  └─> RequestsMatch (local)
  └─> RequestSatisfiedBy (local)
  └─> RemoveAllSatisfiedRequestsInSequence (local, recursive)
  └─> RemoveExecutedRequestBatch (local, recursive)
  └─> GetReplicaIndex (configuration.rs)
      └─> FindIndexInSeq (common/collections)
  └─> BalLt (types.rs)
  └─> UpperBoundedAddition (upper_bound.rs)
      └─> LtUpperBound (upper_bound.rs)
  └─> LMinQuorumSize (configuration.rs)
  └─> LtUpperBound (upper_bound.rs)
```

## Implementation Priority

1. **Simple helpers first** (no recursion, no quantifiers):
   - `ComputeSuccessorView`
   - `BoundRequestSequence`
   - `RequestsMatch`
   - `RequestSatisfiedBy`
   - `BalLt`, `BalLeq`
   - `LMinQuorumSize`
   - `LeqUpperBound`, `LtUpperBound`, `UpperBoundedAddition`
   - `GetReplicaIndex`

2. **Recursive helpers** (need decreases/loop transformation):
   - `RemoveAllSatisfiedRequestsInSequence`
   - `RemoveExecutedRequestBatch`

3. **Quantifier helpers** (may need special handling):
   - `ReplicasIsUnique`
   - `WellFormedLConfiguration`

## Notes

- Many helper functions already have manual exec implementations in `src/implementation/RSL/`
- Need to compare transpiler output with manual implementations for correctness
- Recursive functions will need `decreases` clauses and loop transformation
- Some functions call external helpers from common modules - these need to be available
