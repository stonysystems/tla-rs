# RSL Init Predicate Transpiler Test Plan

## Objective

Test the transpiler with real RSL protocol Init predicates to validate that it can handle the actual complexity of the RSL specification.

## Target Predicates

### 1. LAcceptorInit (from acceptor.rs)
```rust
pub open spec fn LAcceptorInit(a:LAcceptor, c:LReplicaConstants) -> bool
{
    &&& a.constants =~= c
    &&& a.max_bal =~= Ballot{seqno:0,proposer_id:0}
    &&& a.votes == Map::<OperationNumber, Vote>::empty()
    &&& a.last_checkpointed_operation.len() == c.all.config.replica_ids.len()
    &&& (forall |idx:int| 0 <= idx < a.last_checkpointed_operation.len() ==> a.last_checkpointed_operation[idx] == 0)
    &&& a.log_truncation_point == 0
}
```

**Complexity**: Medium
- Uses `=~=` (deep equality with view)
- Uses struct literal construction (`Ballot{seqno:0,proposer_id:0}`)
- Uses `Map::empty()`
- Has a forall quantifier over sequence indices
- Has nested structs (`LReplicaConstants` contains `LConstants` which contains `LConfiguration`)

### 2. LLearnerInit (from learner.rs)
```rust
pub open spec fn LLearnerInit(l:LLearner, c:LReplicaConstants) -> bool
{
  &&& l.constants == c
  &&& l.max_ballot_seen == Ballot{seqno:0, proposer_id:0}
  &&& l.unexecuted_learner_state == Map::<OperationNumber, LearnerTuple>::empty()
}
```

**Complexity**: Simple
- Basic equality assignments
- Struct literal construction
- Map empty construction
- No quantifiers

### 3. LExecutorInit (from executor.rs)
```rust
pub open spec fn LExecutorInit(s:LExecutor, c:LReplicaConstants) -> bool
{
    &&& s.constants == c
    &&& s.app == AppInitialize()
    &&& s.ops_complete == 0
    &&& s.max_bal_reflected == Ballot{seqno:0, proposer_id:0}
    &&& s.next_op_to_execute == OutstandingOperation::OutstandingOpUnknown{}
    &&& s.reply_cache == Map::<AbstractEndPoint, Reply>::empty()
}
```

**Complexity**: Medium
- Basic field assignments
- Function call in spec (`AppInitialize()`)
- Enum variant construction (`OutstandingOperation::OutstandingOpUnknown{}`)
- Map empty construction

### 4. LProposerInit (from proposer.rs)
```rust
pub open spec fn LProposerInit(s:LProposer, c:LReplicaConstants) -> bool
recommends
        WellFormedLConfiguration(c.all.config)
{
    &&& s.constants == c
    &&& s.current_state == 0
    &&& s.request_queue == Seq::<Request>::empty()
    &&& s.max_ballot_i_sent_1a == Ballot{seqno:0, proposer_id:c.my_index}
    &&& s.next_operation_number_to_propose == 0
    &&& s.received_1b_packets == Set::<RslPacket>::empty()
    &&& s.highest_seqno_requested_by_client_this_view == Map::<AbstractEndPoint, int>::empty()
    &&& ElectionStateInit(s.election_state, c)
    &&& s.incomplete_batch_timer is IncompleteBatchTimerOff
}
```

**Complexity**: High
- Has `recommends` clause
- Uses Seq::empty(), Set::empty(), Map::empty()
- Has a reference to another field (`c.my_index`) in struct construction
- Calls another Init predicate (`ElectionStateInit`)
- Enum variant check (`is IncompleteBatchTimerOff`)
- Many fields to assign

## Test Strategy

### Phase 1: Simplified Isolated Tests

Create standalone examples that test specific features in isolation:

1. **Test: Struct literal in equality** - `a.field == Struct{f1:0, f2:0}`
2. **Test: Collection empty** - `a.field == Map::empty()`
3. **Test: Enum variant** - `a.field is Variant` / `a.field == Enum::Variant{}`
4. **Test: Function call in spec** - `a.field == SomeFunc()`
5. **Test: Forall over sequence** - `forall |i| 0 <= i < seq.len() ==> seq[i] == 0`

### Phase 2: Full Init Predicate Tests

Create complete working examples for each Init predicate:

1. `learner_init_complete.rs` - Simplest, no quantifiers
2. `executor_init_complete.rs` - Tests enum variants and function calls
3. `acceptor_init_full_complete.rs` - Tests quantifiers over sequences
4. `proposer_init_complete.rs` - Tests recommends and cross-predicate calls

### Phase 3: Transpiler Pipeline Tests

Run the transpiler on `.automan` annotated spec files and verify:
1. Generated code compiles with rustc
2. Generated code verifies with Verus
3. Generated ensures clause correctly references original spec

## Expected Challenges

1. **`=~=` operator**: The spec uses deep equality with view (`=~=`). Need to translate to `.clone()` pattern.

2. **Enum variant construction**: `OutstandingOperation::OutstandingOpUnknown{}` needs proper translation.

3. **Forall over sequences**: The `LAcceptorInit` has a quantifier that requires creating a Vec with specific length initialized to zeros.

4. **Cross-predicate calls**: `ElectionStateInit(s.election_state, c)` calls another predicate.

5. **External function calls**: `AppInitialize()` is an external spec function.

## Deliverables

1. Working Verus example files in `transpiler/verus_examples/`
2. Integration tests in `transpiler/tests/`
3. Documentation of any transpiler limitations discovered
4. Updates to TODO.md marking progress

## Success Criteria

- All example files verify with Verus (0 errors)
- At least 3 Init predicates working end-to-end
- Documented list of transpiler enhancements needed for remaining features
