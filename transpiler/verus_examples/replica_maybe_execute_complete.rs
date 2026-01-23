// Test for LReplicaNextSpontaneousMaybeExecute predicate
// Tests: Three-component coordination - updates Proposer, Learner, AND Executor atomically
// This is the most complex multi-component orchestration pattern in RSL protocol
//
// Pattern demonstrated:
// - Conditional based on executor state (OutstandingOpKnown)
// - Three separate component predicates called in one step
// - Partial replica struct update (some fields from s_, some from s)
// - No change (identity) when condition not met

use vstd::prelude::*;
use vstd::map::*;
use vstd::seq::*;

verus! {
    // === SPEC TYPES ===

    pub type OperationNumber = int;
    pub type RequestBatch = int;  // Simplified

    // Outstanding operation state - simplified enum
    pub enum OutstandingOperation {
        OutstandingOpKnown { v: RequestBatch, bal: int },
        OutstandingOpUnknown,
    }

    // Simplified packet
    pub struct RslPacket {
        pub dst: int,
        pub msg: int,
    }

    // Simplified election state
    pub struct ElectionState {
        pub timer: int,
    }

    // === COMPONENT TYPES ===

    // Proposer (simplified - focuses on election_state reset)
    pub struct LProposer {
        pub election_state: ElectionState,
        pub current_state: int,
    }

    // Learner (simplified)
    pub struct LLearner {
        pub unexecuted_state: Map<OperationNumber, int>,
    }

    // Executor (simplified)
    pub struct LExecutor {
        pub ops_complete: OperationNumber,
        pub next_op_to_execute: OutstandingOperation,
        pub app_state: int,
    }

    // Replica containing all components
    pub struct LReplica {
        pub proposer: LProposer,
        pub acceptor: int,  // Simplified - not modified in this predicate
        pub learner: LLearner,
        pub executor: LExecutor,
        pub next_heartbeat_time: int,
    }

    // === HELPER PREDICATES ===

    // Proposer reset due to execution (simplified)
    pub open spec fn LProposerResetViewTimerDueToExecution(
        s: LProposer,
        s_: LProposer,
        _val: RequestBatch
    ) -> bool
    {
        // Simplified: just reset the timer
        &&& s_.election_state.timer == 0
        &&& s_.current_state == s.current_state
    }

    // Learner forget decision (simplified)
    pub open spec fn LLearnerForgetDecision(
        s: LLearner,
        s_: LLearner,
        opn: OperationNumber
    ) -> bool
    {
        if s.unexecuted_state.contains_key(opn) {
            s_.unexecuted_state == s.unexecuted_state.remove(opn)
        } else {
            s_.unexecuted_state == s.unexecuted_state
        }
    }

    // Executor execute (simplified)
    pub open spec fn LExecutorExecute(
        s: LExecutor,
        s_: LExecutor,
        sent_packets: Seq<RslPacket>
    ) -> bool
    {
        &&& s_.ops_complete == s.ops_complete + 1
        &&& s_.next_op_to_execute == OutstandingOperation::OutstandingOpUnknown
        &&& s_.app_state == s.app_state + 1  // Simplified state machine transition
        &&& sent_packets.len() >= 0  // Packets sent as replies (simplified)
    }

    // === MAIN PREDICATE ===
    // LReplicaNextSpontaneousMaybeExecute - three-component coordination

    pub open spec fn LReplicaNextSpontaneousMaybeExecute(
        s: LReplica,
        s_: LReplica,
        sent_packets: Seq<RslPacket>,
        should_execute: bool  // Abstracts: s.executor.next_op_to_execute is OutstandingOpKnown && bounds check
    ) -> bool
    {
        if should_execute {
            // Get the value from the known operation (abstracted as parameter)
            let v = 0 as RequestBatch;  // Simplified - would be s.executor.next_op_to_execute->v

            // Dispatch to all THREE components
            &&& LProposerResetViewTimerDueToExecution(s.proposer, s_.proposer, v)
            &&& LLearnerForgetDecision(s.learner, s_.learner, s.executor.ops_complete)
            &&& LExecutorExecute(s.executor, s_.executor, sent_packets)

            // Construct new replica state with updated components
            &&& s_ == LReplica {
                proposer: s_.proposer,
                acceptor: s.acceptor,  // Unchanged
                learner: s_.learner,
                executor: s_.executor,
                next_heartbeat_time: s.next_heartbeat_time,  // Unchanged
            }
        } else {
            // No change
            &&& s_ == s
            &&& sent_packets == Seq::<RslPacket>::empty()
        }
    }

    // === EXEC TYPES ===

    pub struct CElectionState {
        pub timer: i64,
    }

    impl CElectionState {
        pub open spec fn well_formed(&self) -> bool { true }

        pub fn clone_ghost(&self) -> (result: CElectionState)
            ensures result@ == self@
        {
            CElectionState { timer: self.timer }
        }

        pub fn reset_timer(&self) -> (result: CElectionState)
            ensures result@.timer == 0
        {
            CElectionState { timer: 0 }
        }
    }

    impl View for CElectionState {
        type V = ElectionState;
        open spec fn view(&self) -> ElectionState {
            ElectionState { timer: self.timer as int }
        }
    }

    pub struct CProposer {
        pub election_state: CElectionState,
        pub current_state: i64,
    }

    impl CProposer {
        pub open spec fn well_formed(&self) -> bool {
            self.election_state.well_formed()
        }
    }

    impl View for CProposer {
        type V = LProposer;
        open spec fn view(&self) -> LProposer {
            LProposer {
                election_state: self.election_state@,
                current_state: self.current_state as int,
            }
        }
    }

    pub struct CLearnerState {
        pub ghost_state: Ghost<Map<OperationNumber, int>>,
    }

    impl CLearnerState {
        pub open spec fn well_formed(&self) -> bool { true }

        #[verifier::external_body]
        pub fn contains_key(&self, opn: i64) -> (result: bool)
            ensures result == self@.contains_key(opn as int)
        {
            unimplemented!()
        }

        pub fn remove(&self, opn: i64) -> (result: CLearnerState)
            requires self@.contains_key(opn as int)
            ensures result@ == self@.remove(opn as int)
        {
            CLearnerState { ghost_state: Ghost(self.ghost_state@.remove(opn as int)) }
        }

        pub fn clone_ghost(&self) -> (result: CLearnerState)
            ensures result@ == self@
        {
            CLearnerState { ghost_state: Ghost(self.ghost_state@) }
        }
    }

    impl View for CLearnerState {
        type V = Map<OperationNumber, int>;
        open spec fn view(&self) -> Map<OperationNumber, int> {
            self.ghost_state@
        }
    }

    pub struct CLearner {
        pub unexecuted_state: CLearnerState,
    }

    impl CLearner {
        pub open spec fn well_formed(&self) -> bool {
            self.unexecuted_state.well_formed()
        }
    }

    impl View for CLearner {
        type V = LLearner;
        open spec fn view(&self) -> LLearner {
            LLearner { unexecuted_state: self.unexecuted_state@ }
        }
    }

    pub struct CExecutor {
        pub ops_complete: i64,
        pub next_op_to_execute: COutstandingOperation,
        pub app_state: i64,
    }

    impl CExecutor {
        pub open spec fn well_formed(&self) -> bool { true }
    }

    impl View for CExecutor {
        type V = LExecutor;
        open spec fn view(&self) -> LExecutor {
            LExecutor {
                ops_complete: self.ops_complete as int,
                next_op_to_execute: self.next_op_to_execute@,
                app_state: self.app_state as int,
            }
        }
    }

    pub enum COutstandingOperation {
        OutstandingOpKnown { v: i64, bal: i64 },
        OutstandingOpUnknown,
    }

    impl COutstandingOperation {
        pub open spec fn well_formed(&self) -> bool { true }
    }

    impl View for COutstandingOperation {
        type V = OutstandingOperation;
        open spec fn view(&self) -> OutstandingOperation {
            match self {
                COutstandingOperation::OutstandingOpKnown { v, bal } =>
                    OutstandingOperation::OutstandingOpKnown { v: *v as int, bal: *bal as int },
                COutstandingOperation::OutstandingOpUnknown =>
                    OutstandingOperation::OutstandingOpUnknown,
            }
        }
    }

    pub struct CRslPacket {
        pub dst: i64,
        pub msg: i64,
    }

    impl CRslPacket {
        pub open spec fn well_formed(&self) -> bool { true }
    }

    impl View for CRslPacket {
        type V = RslPacket;
        open spec fn view(&self) -> RslPacket {
            RslPacket {
                dst: self.dst as int,
                msg: self.msg as int,
            }
        }
    }

    pub struct CReplica {
        pub proposer: CProposer,
        pub acceptor: i64,
        pub learner: CLearner,
        pub executor: CExecutor,
        pub next_heartbeat_time: i64,
    }

    impl CReplica {
        pub open spec fn well_formed(&self) -> bool {
            &&& self.proposer.well_formed()
            &&& self.learner.well_formed()
            &&& self.executor.well_formed()
        }
    }

    impl View for CReplica {
        type V = LReplica;
        open spec fn view(&self) -> LReplica {
            LReplica {
                proposer: self.proposer@,
                acceptor: self.acceptor as int,
                learner: self.learner@,
                executor: self.executor@,
                next_heartbeat_time: self.next_heartbeat_time as int,
            }
        }
    }

    // === EXEC HELPER FUNCTIONS ===

    fn c_proposer_reset_view_timer(s: &CProposer, _val: i64) -> (result: CProposer)
        requires s.well_formed()
        ensures LProposerResetViewTimerDueToExecution(s@, result@, _val as int)
    {
        CProposer {
            election_state: s.election_state.reset_timer(),
            current_state: s.current_state,
        }
    }

    fn c_learner_forget_decision(s: &CLearner, opn: i64) -> (result: CLearner)
        requires s.well_formed()
        ensures LLearnerForgetDecision(s@, result@, opn as int)
    {
        if s.unexecuted_state.contains_key(opn) {
            CLearner { unexecuted_state: s.unexecuted_state.remove(opn) }
        } else {
            CLearner { unexecuted_state: s.unexecuted_state.clone_ghost() }
        }
    }

    fn c_executor_execute(s: &CExecutor) -> (result: (CExecutor, Vec<CRslPacket>))
        requires
            s.well_formed(),
            s.ops_complete < i64::MAX,  // Overflow guard
            s.app_state < i64::MAX,     // Overflow guard
        ensures
            LExecutorExecute(s@, result.0@, result.1@.map(|i, p: CRslPacket| p@)),
            result.0.well_formed(),
    {
        let new_executor = CExecutor {
            ops_complete: s.ops_complete + 1,
            next_op_to_execute: COutstandingOperation::OutstandingOpUnknown,
            app_state: s.app_state + 1,
        };

        // In real implementation, would generate reply packets
        let packets: Vec<CRslPacket> = Vec::new();

        proof {
            assert(new_executor.ops_complete as int == s.ops_complete as int + 1);
            assert(new_executor.next_op_to_execute@ == OutstandingOperation::OutstandingOpUnknown);
            assert(new_executor.app_state as int == s.app_state as int + 1);
            assert(packets@.map(|i, p: CRslPacket| p@).len() >= 0);
        }

        (new_executor, packets)
    }

    // === MAIN EXEC FUNCTION ===
    // Implements LReplicaNextSpontaneousMaybeExecute with three-component dispatch

    pub fn c_replica_next_spontaneous_maybe_execute(
        s: &CReplica,
        should_execute: bool,
    ) -> (result: (CReplica, Vec<CRslPacket>))
        requires
            s.well_formed(),
            s.executor.ops_complete < i64::MAX,  // Overflow guard
            s.executor.app_state < i64::MAX,     // Overflow guard
        ensures
            result.0.well_formed(),
            LReplicaNextSpontaneousMaybeExecute(s@, result.0@, result.1@.map(|i, p: CRslPacket| p@), should_execute),
    {
        if should_execute {
            // Simplified: v would be extracted from s.executor.next_op_to_execute->v
            let v: i64 = 0;

            // Dispatch to all THREE components
            let new_proposer = c_proposer_reset_view_timer(&s.proposer, v);
            let new_learner = c_learner_forget_decision(&s.learner, s.executor.ops_complete);
            let (new_executor, packets) = c_executor_execute(&s.executor);

            // Construct new replica with updated components
            let new_replica = CReplica {
                proposer: new_proposer,
                acceptor: s.acceptor,  // Unchanged
                learner: new_learner,
                executor: new_executor,
                next_heartbeat_time: s.next_heartbeat_time,  // Unchanged
            };

            proof {
                assert(LProposerResetViewTimerDueToExecution(s.proposer@, new_replica.proposer@, v as int));
                assert(LLearnerForgetDecision(s.learner@, new_replica.learner@, s.executor.ops_complete as int));
                assert(LExecutorExecute(s.executor@, new_replica.executor@, packets@.map(|i, p: CRslPacket| p@)));
            }

            (new_replica, packets)
        } else {
            // No change - clone the replica
            let same_proposer = CProposer {
                election_state: s.proposer.election_state.clone_ghost(),
                current_state: s.proposer.current_state,
            };
            let same_learner = CLearner {
                unexecuted_state: s.learner.unexecuted_state.clone_ghost(),
            };
            let same_executor = CExecutor {
                ops_complete: s.executor.ops_complete,
                next_op_to_execute: match &s.executor.next_op_to_execute {
                    COutstandingOperation::OutstandingOpKnown { v, bal } =>
                        COutstandingOperation::OutstandingOpKnown { v: *v, bal: *bal },
                    COutstandingOperation::OutstandingOpUnknown =>
                        COutstandingOperation::OutstandingOpUnknown,
                },
                app_state: s.executor.app_state,
            };

            proof {
                assert(same_proposer@ == s.proposer@);
                assert(same_learner@ == s.learner@);
                assert(same_executor@ == s.executor@);
            }

            let same_replica = CReplica {
                proposer: same_proposer,
                acceptor: s.acceptor,
                learner: same_learner,
                executor: same_executor,
                next_heartbeat_time: s.next_heartbeat_time,
            };

            let empty_packets: Vec<CRslPacket> = Vec::new();

            proof {
                assert(same_replica@ == s@);
                assert(empty_packets@.map(|i, p: CRslPacket| p@) =~= Seq::<RslPacket>::empty());
            }

            (same_replica, empty_packets)
        }
    }
}

fn main() {}
