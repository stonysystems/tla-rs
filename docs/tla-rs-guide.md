# tla-rs: Writing TLA-Style Specifications in Rust/Verus

A comprehensive guide to writing formally verified distributed system specifications using tla-rs.

---

## Table of Contents

1. [Introduction](#1-introduction)
   - 1.1 [What is tla-rs?](#11-what-is-tla-rs)
   - 1.2 [TLA+ Background](#12-tla-background)
   - 1.3 [Why Rust/Verus?](#13-why-rustverus)

2. [Core Concepts](#2-core-concepts)
   - 2.1 [State Machines](#21-state-machines)
   - 2.2 [Init and Next Predicates](#22-init-and-next-predicates)
   - 2.3 [Actions and Transitions](#23-actions-and-transitions)
   - 2.4 [Invariants and Safety Properties](#24-invariants-and-safety-properties)

3. [Syntax Translation: TLA+ to Verus](#3-syntax-translation-tla-to-verus)
   - 3.1 [Logical Operators](#31-logical-operators)
   - 3.2 [Quantifiers](#32-quantifiers)
   - 3.3 [Variables and Constants](#33-variables-and-constants)
   - 3.4 [State Updates and UNCHANGED](#34-state-updates-and-unchanged)
   - 3.5 [Quick Reference Table](#35-quick-reference-table)

4. [Verus Function Types](#4-verus-function-types)
   - 4.1 [Spec Functions](#41-spec-functions)
   - 4.2 [Proof Functions](#42-proof-functions)
   - 4.3 [Exec Functions](#43-exec-functions)
   - 4.4 [The `recommends` Clause](#44-the-recommends-clause)

5. [Modeling Distributed Systems](#5-modeling-distributed-systems)
   - 5.1 [Environment Abstraction](#51-environment-abstraction)
   - 5.2 [Message Types](#52-message-types)
   - 5.3 [Packet and I/O Operations](#53-packet-and-io-operations)
   - 5.4 [Broadcasting](#54-broadcasting)

6. [Component Composition](#6-component-composition)
   - 6.1 [Modular State Machines](#61-modular-state-machines)
   - 6.2 [Composing Init Predicates](#62-composing-init-predicates)
   - 6.3 [Composing Next Relations](#63-composing-next-relations)

7. [Refinement and Abstraction](#7-refinement-and-abstraction)
   - 7.1 [Multi-Level Architecture](#71-multi-level-architecture)
   - 7.2 [Abstraction Functions](#72-abstraction-functions)
   - 7.3 [Proving Refinement](#73-proving-refinement)

8. [Complete Example: Lock Service](#8-complete-example-lock-service)

9. [Complete Example: RSL (Paxos)](#9-complete-example-rsl-paxos)

10. [Best Practices](#10-best-practices)

---

## 1. Introduction

### 1.1 What is tla-rs?

tla-rs is a framework for writing TLA-style formal specifications in Rust using the Verus verification tool. It allows you to:

- Define state machines with Init and Next predicates
- Specify safety and liveness properties
- Prove refinement between abstraction layers
- Generate verified executable code

The project demonstrates this approach through implementations of:
- **IronRSL**: A Paxos-based replicated state machine
- **IronLock**: A distributed locking service

### 1.2 TLA+ Background

TLA+ (Temporal Logic of Actions) is a formal specification language for describing and reasoning about concurrent and distributed systems. Key concepts include:

- **State machines**: Systems described by state variables and transitions
- **Init**: Predicate defining valid initial states
- **Next**: Predicate defining valid state transitions
- **Invariants**: Properties that must hold in all reachable states
- **Refinement**: Proving a concrete implementation satisfies an abstract specification

### 1.3 Why Rust/Verus?

Verus is a deductive verification tool for Rust that provides:

- **Proof integration**: Write specifications alongside executable code
- **Type safety**: Leverage Rust's type system for correctness
- **Executable output**: Generate verified binaries, not just checked specifications
- **SMT-backed verification**: Automatic proof discharge via Z3

---

## 2. Core Concepts

### 2.1 State Machines

In tla-rs, state machines are defined using Rust structs. Each struct field represents a state variable:

```rust
verus! {
    pub struct LAcceptor {
        pub constants: LReplicaConstants,  // Configuration (constant)
        pub max_bal: Ballot,               // Highest ballot seen
        pub votes: Votes,                  // Recorded votes
        pub log_truncation_point: OperationNumber,
    }
}
```

### 2.2 Init and Next Predicates

The fundamental building blocks are `Init` and `Next` predicates:

```rust
verus! {
    // Init predicate: defines valid initial states
    pub open spec fn LAcceptorInit(a: LAcceptor, c: LReplicaConstants) -> bool {
        &&& a.constants == c
        &&& a.max_bal == Ballot { seqno: 0, proposer_id: 0 }
        &&& a.votes == Map::empty()
        &&& a.log_truncation_point == 0
    }

    // Next predicate: relates pre-state to post-state
    pub open spec fn LAcceptorNext(
        s: LAcceptor,
        s_: LAcceptor,  // Convention: s_ is the post-state
        ios: Seq<RslIo>
    ) -> bool {
        ||| LAcceptorProcess1a(s, s_, ...)
        ||| LAcceptorProcess2a(s, s_, ...)
        ||| LAcceptorStutter(s, s_)
    }
}
```

### 2.3 Actions and Transitions

Individual actions are spec functions that define specific transitions:

```rust
verus! {
    pub open spec fn LAcceptorProcess1a(
        s: LAcceptor,
        s_: LAcceptor,
        inp: RslPacket,
        sent_packets: Seq<RslPacket>
    ) -> bool
        recommends inp.msg is RslMessage1a
    {
        let bal = inp.msg->bal_1a;

        if BalLt(s.max_bal, bal) {
            // Guard satisfied: perform transition
            &&& s_.max_bal == bal
            &&& s_.votes == s.votes  // UNCHANGED
            &&& sent_packets == seq![make_1b_reply(s, bal, inp.src)]
        } else {
            // Guard not satisfied: stutter
            &&& s_ == s
            &&& sent_packets == Seq::empty()
        }
    }
}
```

### 2.4 Invariants and Safety Properties

Invariants are expressed as spec functions returning bool:

```rust
verus! {
    // Type invariant
    pub open spec fn WellFormedLConfiguration(c: LConfiguration) -> bool {
        &&& c.replica_ids.len() > 0
        &&& forall |i: int, j: int|
            0 <= i < j < c.replica_ids.len()
            ==> c.replica_ids[i] != c.replica_ids[j]
    }

    // Safety property: quorum intersection
    pub open spec fn QuorumIntersection(c: LConfiguration, q1: Set<int>, q2: Set<int>) -> bool {
        q1.len() >= LMinQuorumSize(c) && q2.len() >= LMinQuorumSize(c)
        ==> q1.intersect(q2).len() > 0
    }
}
```

---

## 3. Syntax Translation: TLA+ to Verus

### 3.1 Logical Operators

**Conjunction (AND)**
```
TLA+:  /\ cond1 /\ cond2 /\ cond3
Verus: &&& cond1
       &&& cond2
       &&& cond3
```

The `&&&` operator is Verus's "bulleted conjunction" - each line is implicitly ANDed:

```rust
verus! {
    pub open spec fn Example() -> bool {
        &&& condition_a
        &&& condition_b
        &&& condition_c
    }
}
```

**Disjunction (OR)**
```
TLA+:  \/ action1 \/ action2 \/ action3
Verus: ||| action1
       ||| action2
       ||| action3
```

```rust
verus! {
    pub open spec fn NextAction(s: State, s_: State) -> bool {
        ||| ActionA(s, s_)
        ||| ActionB(s, s_)
        ||| ActionC(s, s_)
    }
}
```

### 3.2 Quantifiers

**Universal Quantification (forall)**
```
TLA+:  \A i \in 0..n-1 : P(i)
Verus: forall |i: int| 0 <= i < n ==> P(i)
```

**Existential Quantification (exists)**
```
TLA+:  \E i \in 0..n-1 : P(i)
Verus: exists |i: int| 0 <= i < n && P(i)
```

Examples:
```rust
verus! {
    // All replicas initialized
    pub open spec fn AllReplicasInit(replicas: Seq<Replica>, c: Constants) -> bool {
        forall |i: int| 0 <= i < replicas.len() ==> ReplicaInit(replicas[i], c)
    }

    // Some replica has the lock
    pub open spec fn SomeoneHoldsLock(nodes: Map<int, Node>) -> bool {
        exists |i: int| nodes.contains_key(i) && nodes[i].held
    }
}
```

### 3.3 Variables and Constants

**TLA+ VARIABLE → Struct Fields**
```
TLA+:  VARIABLE ballot, votes
Verus: pub struct Acceptor {
           pub ballot: Ballot,
           pub votes: Votes,
       }
```

**TLA+ CONSTANT → Constant Structs**
```
TLA+:  CONSTANT Replicas, MaxBallot
Verus: pub struct Constants {
           pub replicas: Seq<EndPoint>,
           pub max_ballot: int,
       }
```

### 3.4 State Updates and UNCHANGED

**Record Update (EXCEPT)**
```
TLA+:  [acceptor EXCEPT !.max_bal = newBal]
Verus: LAcceptor {
           max_bal: newBal,
           votes: s.votes,        // copy unchanged fields
           constants: s.constants,
           ...
       }
```

**UNCHANGED**
```
TLA+:  /\ UNCHANGED <<votes, constants>>
Verus: &&& s_.votes == s.votes
       &&& s_.constants == s.constants
```

Or more concisely when the entire state is unchanged:
```rust
&&& s_ == s
```

### 3.5 Quick Reference Table

| TLA+ | Verus | Description |
|------|-------|-------------|
| `/\` | `&&&` | Conjunction |
| `\/` | `\|\|\|` | Disjunction |
| `\A x \in S : P(x)` | `forall \|x\| S.contains(x) ==> P(x)` | Universal |
| `\E x \in S : P(x)` | `exists \|x\| S.contains(x) && P(x)` | Existential |
| `VARIABLE x` | `pub x: Type` (in struct) | State variable |
| `CONSTANT C` | Constant struct field | Configuration |
| `UNCHANGED x` | `s_.x == s.x` | No change |
| `IF c THEN a ELSE b` | `if c { a } else { b }` | Conditional |
| `[r EXCEPT !.f = v]` | Struct literal with field update | Record update |
| `Init` | `pub open spec fn *Init(...) -> bool` | Initial predicate |
| `Next` | `pub open spec fn *Next(...) -> bool` | Transition relation |

---

## 4. Verus Function Types

### 4.1 Spec Functions

Spec functions are ghost code - they exist only for verification and are erased at runtime:

```rust
verus! {
    // Pure mathematical specification
    pub open spec fn BalLt(a: Ballot, b: Ballot) -> bool {
        ||| a.seqno < b.seqno
        ||| (a.seqno == b.seqno && a.proposer_id < b.proposer_id)
    }

    // Can use recursion (no iteration allowed)
    pub open spec fn SumSeq(s: Seq<int>) -> int
        decreases s.len()
    {
        if s.len() == 0 {
            0
        } else {
            s[0] + SumSeq(s.drop_first())
        }
    }
}
```

Key properties:
- No side effects, no mutation
- Cannot use loops (use recursion with `decreases`)
- `open` means visible to other modules
- `closed` means opaque to other modules

### 4.2 Proof Functions

Proof functions establish lemmas and invariants:

```rust
verus! {
    pub proof fn lemma_ballot_lt_transitive(a: Ballot, b: Ballot, c: Ballot)
        requires
            BalLt(a, b),
            BalLt(b, c),
        ensures
            BalLt(a, c),
    {
        // Proof body - Verus/Z3 often discharges automatically
    }

    pub proof fn lemma_quorum_intersection(config: LConfiguration)
        requires
            WellFormedLConfiguration(config),
        ensures
            forall |q1: Set<int>, q2: Set<int>|
                IsQuorum(config, q1) && IsQuorum(config, q2)
                ==> q1.intersect(q2).len() > 0,
    {
        // Proof of quorum intersection property
    }
}
```

### 4.3 Exec Functions

Exec functions are compiled to executable code:

```rust
verus! {
    pub exec fn process_1a_message(
        acceptor: &mut Acceptor,
        msg: &Message1a
    ) -> (result: Vec<Packet>)
        requires
            old(acceptor).well_formed(),
        ensures
            acceptor.well_formed(),
            // Relates to spec
            LAcceptorProcess1a(old(acceptor)@, acceptor@, msg@, result@),
    {
        if ballot_lt(&acceptor.max_bal, &msg.ballot) {
            acceptor.max_bal = msg.ballot.clone();
            vec![make_1b_packet(acceptor, msg)]
        } else {
            vec![]
        }
    }
}
```

### 4.4 The `recommends` Clause

The `recommends` clause specifies preconditions that should hold for a spec function to be meaningful:

```rust
verus! {
    pub open spec fn LAcceptorProcess1a(
        s: LAcceptor,
        s_: LAcceptor,
        inp: RslPacket,
        sent_packets: Seq<RslPacket>
    ) -> bool
        recommends
            inp.msg is RslMessage1a,  // Message type check
            WellFormedLConfiguration(s.constants.all.config),
    {
        // ... specification body
    }
}
```

Unlike `requires`, `recommends` doesn't generate proof obligations - it documents assumptions.

---

## 5. Modeling Distributed Systems

### 5.1 Environment Abstraction

The environment models the network and external world:

```rust
verus! {
    pub struct LEnvironment<IdType, MessageType> {
        pub sentPackets: Set<LPacket<IdType, MessageType>>,
        pub nextStep: LEnvStep<IdType, MessageType>,
    }

    pub enum LEnvStep<IdType, MessageType> {
        LEnvStepHostIos { actor: IdType, ios: Seq<LIoOp<IdType, MessageType>> },
        LEnvStepDeliverPacket { p: LPacket<IdType, MessageType> },
        LEnvStepAdvanceTime,
        LEnvStepStutter,
    }
}
```

### 5.2 Message Types

Messages are defined as Rust enums:

```rust
verus! {
    pub enum RslMessage {
        RslMessageInvalid {},

        RslMessageRequest {
            seqno_req: int,
            val: AppMessage,
        },

        RslMessage1a {
            bal_1a: Ballot,
        },

        RslMessage1b {
            bal_1b: Ballot,
            log_truncation_point: OperationNumber,
            votes: Votes,
        },

        RslMessage2a {
            bal_2a: Ballot,
            opn_2a: OperationNumber,
            val_2a: RequestBatch,
        },

        RslMessage2b {
            bal_2b: Ballot,
            opn_2b: OperationNumber,
            val_2b: RequestBatch,
        },

        RslMessageReply {
            seqno_reply: int,
            reply: AppMessage,
        },
        // ... more message types
    }
}
```

### 5.3 Packet and I/O Operations

Packets wrap messages with source and destination:

```rust
verus! {
    pub struct LPacket<IdType, MessageType> {
        pub dst: IdType,
        pub src: IdType,
        pub msg: MessageType,
    }

    // I/O operations
    pub enum LIoOp<IdType, MessageType> {
        Send { s: LPacket<IdType, MessageType> },
        Receive { r: LPacket<IdType, MessageType> },
        ReadClock { t: int },
        TimeoutReceive,
    }
}
```

### 5.4 Broadcasting

Broadcast is specified as sending to all replicas:

```rust
verus! {
    pub open spec fn LBroadcastToEveryone(
        config: LConfiguration,
        my_idx: int,
        msg: RslMessage,
        sent_packets: Seq<RslPacket>
    ) -> bool {
        &&& sent_packets.len() == config.replica_ids.len()
        &&& 0 <= my_idx < config.replica_ids.len()
        &&& forall |idx: int| 0 <= idx < sent_packets.len() ==>
            sent_packets[idx] == LPacket {
                dst: config.replica_ids[idx],
                src: config.replica_ids[my_idx],
                msg: msg,
            }
    }
}
```

---

## 6. Component Composition

### 6.1 Modular State Machines

Large state machines are composed from smaller components:

```rust
verus! {
    pub struct LReplica {
        pub constants: LReplicaConstants,
        pub nextHeartbeatTime: int,
        pub proposer: LProposer,    // Sub-component
        pub acceptor: LAcceptor,    // Sub-component
        pub learner: LLearner,      // Sub-component
        pub executor: LExecutor,    // Sub-component
    }
}
```

### 6.2 Composing Init Predicates

The composite Init calls each component's Init:

```rust
verus! {
    pub open spec fn LReplicaInit(r: LReplica, c: LReplicaConstants) -> bool
        recommends WellFormedLConfiguration(c.all.config)
    {
        &&& r.constants == c
        &&& r.nextHeartbeatTime == 0
        &&& LProposerInit(r.proposer, c)
        &&& LAcceptorInit(r.acceptor, c)
        &&& LLearnerInit(r.learner, c)
        &&& LExecutorInit(r.executor, c)
    }
}
```

### 6.3 Composing Next Relations

Actions update specific components while others remain unchanged:

```rust
verus! {
    pub open spec fn LReplicaNextProcess1a(
        s: LReplica,
        s_: LReplica,
        received_packet: RslPacket,
        sent_packets: Seq<RslPacket>
    ) -> bool
        recommends received_packet.msg is RslMessage1a
    {
        // Only acceptor changes
        &&& LAcceptorProcess1a(s.acceptor, s_.acceptor, received_packet, sent_packets)

        // All other components UNCHANGED
        &&& s_.constants == s.constants
        &&& s_.nextHeartbeatTime == s.nextHeartbeatTime
        &&& s_.proposer == s.proposer
        &&& s_.learner == s.learner
        &&& s_.executor == s.executor
    }
}
```

---

## 7. Refinement and Abstraction

### 7.1 Multi-Level Architecture

The project uses a two-level refinement:

```
┌─────────────────────────────────────┐
│  Abstract Service (RSLSystemState)  │  High-level: requests → replies
└──────────────────┬──────────────────┘
                   │ Refinement
┌──────────────────▼──────────────────┐
│  Protocol State (RslState)          │  Low-level: Paxos messages
└─────────────────────────────────────┘
```

### 7.2 Abstraction Functions

The abstraction function maps concrete to abstract states:

```rust
verus! {
    // Abstract service state
    pub struct RSLSystemState {
        pub server_addresses: Set<AbstractEndPoint>,
        pub app: AppState,
        pub requests: Set<Request>,
        pub replies: Set<Reply>,
    }

    // Abstraction function
    pub open spec fn ProduceAbstractState(
        server_addresses: Set<AbstractEndPoint>,
        batches: Seq<RequestBatch>
    ) -> RSLSystemState {
        let requests = Set::new(|req: Request|
            exists |batch_num: int, req_num: int|
                0 <= batch_num < batches.len()
                && 0 <= req_num < batches[batch_num].len()
                && batches[batch_num][req_num] == req
        );

        let replies = Set::new(|rep: Reply|
            exists |batch_num: int, req_num: int|
                0 <= batch_num < batches.len()
                && 0 <= req_num < batches[batch_num].len()
                && GetReplyFromRequestBatches(batches, batch_num, req_num) == rep
        );

        RSLSystemState {
            server_addresses: server_addresses,
            app: GetAppStateFromRequestBatches(batches),
            requests: requests,
            replies: replies,
        }
    }
}
```

### 7.3 Proving Refinement

Refinement proofs show that concrete behaviors correspond to abstract behaviors:

```rust
verus! {
    // Refinement relation
    pub open spec fn SystemRefinementRelation(
        ps: RslState,
        rs: RSLSystemState
    ) -> bool {
        exists |qs: Seq<QuorumOf2bs>|
            IsMaximalQuorumOf2bsSequence(ps, qs)
            && rs == ProduceAbstractState(
                GetServerAddresses(ps),
                GetSequenceOfRequestBatches(qs)
            )
    }

    // Refinement correctness
    pub open spec fn RslSystemBehaviorRefinementCorrect(
        server_addresses: Set<AbstractEndPoint>,
        low_level_behavior: Seq<RslState>,
        high_level_behavior: Seq<RSLSystemState>
    ) -> bool {
        &&& high_level_behavior.len() == low_level_behavior.len()

        // Each state refines
        &&& forall |i: int| 0 <= i < low_level_behavior.len() ==>
            SystemRefinementRelation(low_level_behavior[i], high_level_behavior[i])

        // Abstract behavior is valid
        &&& high_level_behavior.len() > 0
        &&& RslSystemInit(high_level_behavior[0], server_addresses)
        &&& forall |i: int| 0 <= i < high_level_behavior.len() - 1 ==>
            RslSystemNext(high_level_behavior[i], high_level_behavior[i + 1])
    }
}
```

---

## 8. Complete Example: Lock Service

A simpler example to illustrate the patterns:

```rust
verus! {
    // State
    pub struct AbstractNode {
        pub held: bool,
        pub epoch: nat,
        pub my_index: nat,
        pub config: AbstractConfig,
    }

    // Messages
    pub enum LockMessage {
        Transfer { transfer_epoch: nat },
        Locked { locked_epoch: nat },
    }

    // Init
    pub open spec fn NodeInit(
        s: AbstractNode,
        my_index: nat,
        config: AbstractConfig
    ) -> bool {
        &&& s.my_index == my_index
        &&& s.config == config
        &&& s.held == (my_index == 0)  // Node 0 starts with lock
        &&& s.epoch == if my_index == 0 { 1 } else { 0 }
    }

    // Action: Grant lock to next node
    pub open spec fn NodeGrant(
        s: AbstractNode,
        s_: AbstractNode,
        ios: Seq<LockIo>
    ) -> bool {
        if s.held && s.epoch < 0xFFFF_FFFF_FFFF_FFFF {
            &&& !s_.held
            &&& s_.epoch == s.epoch
            &&& ios.len() == 1
            &&& ios[0] is Send
            &&& {
                let packet = ios[0]->s;
                &&& packet.msg is Transfer
                &&& packet.msg->transfer_epoch == s.epoch + 1
                &&& packet.dst == s.config[((s.my_index + 1) % s.config.len()) as int]
            }
        } else {
            &&& s_ == s
            &&& ios.len() == 0
        }
    }

    // Action: Accept lock transfer
    pub open spec fn NodeAccept(
        s: AbstractNode,
        s_: AbstractNode,
        ios: Seq<LockIo>
    ) -> bool
        recommends
            ios.len() > 0,
            ios[0] is Receive,
            ios[0]->r.msg is Transfer,
    {
        let transfer_epoch = ios[0]->r.msg->transfer_epoch;
        if !s.held && transfer_epoch > s.epoch {
            &&& s_.held == true
            &&& s_.epoch == transfer_epoch
        } else {
            &&& s_ == s
        }
    }

    // Next relation
    pub open spec fn NodeNext(
        s: AbstractNode,
        s_: AbstractNode,
        ios: Seq<LockIo>
    ) -> bool {
        ||| NodeGrant(s, s_, ios)
        ||| NodeAccept(s, s_, ios)
    }

    // Safety: At most one node holds the lock
    pub open spec fn LockSafety(nodes: Map<nat, AbstractNode>) -> bool {
        forall |i: nat, j: nat|
            nodes.contains_key(i) && nodes.contains_key(j)
            && nodes[i].held && nodes[j].held
            ==> i == j
    }
}
```

---

## 9. Complete Example: RSL (Paxos)

The RSL protocol demonstrates a full Paxos implementation. Here are the key components:

### System State

```rust
verus! {
    pub struct RslState {
        pub constants: LConstants,
        pub environment: LEnvironment<AbstractEndPoint, RslMessage>,
        pub replicas: Seq<LScheduler>,
        pub clients: Seq<AbstractEndPoint>,
    }
}
```

### System Init

```rust
verus! {
    pub open spec fn RslInit(con: LConstants, ps: RslState) -> bool {
        &&& WellFormedLConfiguration(con.config)
        &&& WFLParameters(con.params)
        &&& ps.constants == con
        &&& LEnvironment_Init(ps.environment)
        &&& RslMapsComplete(ps)
        &&& forall |i: int| 0 <= i < con.config.replica_ids.len() ==>
            LSchedulerInit(
                ps.replicas[i],
                LReplicaConstants { my_index: i, all: con }
            )
    }
}
```

### System Next

```rust
verus! {
    pub open spec fn RslNext(ps: RslState, ps_: RslState) -> bool {
        // One of three things happens:
        ||| exists |idx: int, ios: Seq<RslIo>|
            RslNextOneReplica(ps, ps_, idx, ios)
        ||| exists |eid: AbstractEndPoint, ios: Seq<RslIo>|
            RslNextOneExternal(ps, ps_, eid, ios)
        ||| RslNextEnvironment(ps, ps_)
    }
}
```

### Proposer Actions (Phase 1)

```rust
verus! {
    pub open spec fn LProposerMaybeEnterNewViewAndSend1a(
        s: LProposer,
        s_: LProposer,
        sent_packets: Seq<RslPacket>
    ) -> bool {
        if s.election_state.current_view > s.max_ballot_i_sent_1a
            && s.election_state.current_view.proposer_id == s.constants.my_index
        {
            let new_ballot = s.election_state.current_view;
            &&& s_.max_ballot_i_sent_1a == new_ballot
            &&& s_.current_state == 1  // Entered phase 1
            &&& s_.received_1b_packets == Set::empty()
            &&& LBroadcastToEveryone(
                    s.constants.all.config,
                    s.constants.my_index,
                    RslMessage::RslMessage1a { bal_1a: new_ballot },
                    sent_packets
                )
        } else {
            &&& s_ == s
            &&& sent_packets == Seq::empty()
        }
    }
}
```

---

## 10. Best Practices

### Naming Conventions

| Suffix/Prefix | Meaning | Example |
|---------------|---------|---------|
| `_s` | Spec module | `host_s.rs` |
| `_i` | Implementation module | `host_i.rs` |
| `L*` | Logical/protocol type | `LReplica`, `LProposer` |
| `C*` | Concrete type | `CMessage`, `CConstants` |
| `s_` | Post-state (in transitions) | `LAcceptorNext(s, s_, ...)` |

### Structuring Specifications

1. **Separate concerns**: Define Init and Next for each component separately
2. **Use recommends**: Document preconditions without generating proof obligations
3. **Explicit UNCHANGED**: Make unchanged fields explicit in state updates
4. **Guard-else-stutter pattern**: Always handle the case when guards aren't satisfied

### Common Patterns

**Guard-based transitions:**
```rust
if guard_condition {
    // State change
    &&& s_.field = new_value
    &&& sent_packets == seq![...]
} else {
    // Stutter
    &&& s_ == s
    &&& sent_packets == Seq::empty()
}
```

**Extracting sent packets from I/O:**
```rust
pub open spec fn ExtractSentPacketsFromIos(ios: Seq<RslIo>) -> Seq<RslPacket>
    decreases ios.len()
{
    if ios.len() == 0 {
        Seq::empty()
    } else if ios[0] is Send {
        seq![ios[0]->s] + ExtractSentPacketsFromIos(ios.drop_first())
    } else {
        ExtractSentPacketsFromIos(ios.drop_first())
    }
}
```

### Verus-Specific Tips

1. **Triggers for quantifiers**: Complex arithmetic in triggers may need helper variables
   ```rust
   // Instead of: forall |i| f(i + 1)
   // Use: forall |i, j| j == i + 1 ==> f(j)
   ```

2. **Finite sets**: Verus sets are infinite by default; use `.dom().finite()` for bounds

3. **No iteration in specs**: Use recursion with `decreases` clause

4. **View trait (`@`)**: Use `struct@` to convert concrete to ghost types

---

## Further Resources

- [Verus Documentation](https://verus-lang.github.io/verus/guide/)
- [TLA+ Home Page](https://lamport.azurewebsites.net/tla/tla.html)
- [IronFleet Paper](https://www.microsoft.com/en-us/research/publication/ironfleet-proving-practical-distributed-systems-correct/)
- Project source: `src/protocol/` for specifications, `src/implementation/` for verified code
