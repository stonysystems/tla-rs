// Manual helper code for RSL concrete types generation.
//
// This file is intended to be injected by transpiler generate-types via
// `output.manual_code` in `types_transpile.toml`.
//
// IMPORTANT: Contents here live inside an existing `verus! { ... }` block in
// generated output. Do not add `use` statements or a nested `verus!` block.
//
// Helper functions shared with types_i.rs (COperationNumber helpers, CBalLt/Leq/Eq,
// CRequestBatch helpers, CReplyCache helpers, CVotes helpers, CLearnerTuple,
// CLearnerState helpers) are defined in types_i.rs and bulk re-exported via:
//   pub use crate::implementation::RSL::types_i::*;
// in the re_exports section of types_transpile.toml.
//
// CRslIo is generated via [extra_type_aliases] in types_transpile.toml.

// =============================================================================
// CParameters (manual validity/view + static defaults)
// =============================================================================

impl CParameters{
    pub open spec fn valid(self) -> bool
    {
        &&& self.max_integer_val > self.max_log_length > 0
        &&& self.max_integer_val > self.max_batch_delay
        &&& self.max_integer_val < 0x8000_0000_0000_0000
        &&& self.baseline_view_timeout_period > 0
        &&& self.max_integer_val > self.heartbeat_period > 0
        &&& self.max_batch_size > 0
    }

    pub open spec fn view(self) -> LParameters
    {
        LParameters{
            max_log_length: self.max_log_length as int,
            baseline_view_timeout_period: self.baseline_view_timeout_period as int,
            heartbeat_period: self.heartbeat_period as int,
            max_integer_val: UpperBound::UpperBoundFinite{n: self.max_integer_val as int},
            max_batch_size: self.max_batch_size as int,
            max_batch_delay: self.max_batch_delay as int,
        }
    }
}

impl View for CParameters {
    type V = LParameters;

    open spec fn view(&self) -> LParameters {
        LParameters {
            max_log_length: self.max_log_length as int,
            baseline_view_timeout_period: self.baseline_view_timeout_period as int,
            heartbeat_period: self.heartbeat_period as int,
            max_integer_val: UpperBound::UpperBoundFinite{n: self.max_integer_val as int},
            max_batch_size: self.max_batch_size as int,
            max_batch_delay: self.max_batch_delay as int,
        }
    }
}

// =============================================================================
// CConfiguration (generated + impl methods)
// =============================================================================

#[derive(Clone)]
pub struct CConfiguration {
    pub replica_ids: Vec<EndPoint>,
}

impl CConfiguration {
    #[verifier(external_body)]
    pub fn clone_up_to_view(&self) -> (res:CConfiguration)
    ensures
        self@ == res@,
        self == res,
        res.valid(),
    {
        let mut newVec:Vec<EndPoint> = Vec::new();
        let mut i = 0;
        let len = self.replica_ids.len();
        while i<len
        {
            assert(i >= 0);
            assert(i < self.replica_ids@.len());
            newVec.push(self.replica_ids[i].clone_up_to_view());
            i += 1;
        }
        CConfiguration {
            replica_ids: newVec,
        }
    }

    pub open spec fn abstractable(self) -> bool
    {
        &&& (forall |i:int| 0 <= i < self.replica_ids.len() ==> self.replica_ids[i].abstractable())
        &&& seq_is_unique(self.replica_ids@)
    }

    pub open spec fn valid(self) -> bool
    {
        &&& self.abstractable()
        &&& (forall |i:int| 0 <= i < self.replica_ids.len() ==> self.replica_ids[i].abstractable() && self.replica_ids[i].valid_public_key())
        &&& (0 < self.replica_ids.len() < 0xffff_ffff_ffff_ffff)
    }

    pub open spec fn view(self) -> LConfiguration
    {
        LConfiguration{
            clientIds: Set::<AbstractEndPoint>::empty(),
            replica_ids: self.replica_ids@.map(|i, e:EndPoint| e@)
        }
    }

    pub open spec fn CReplicaDistinct(&self, i:int, j:int) -> bool
    {
        &&& 0 <= i < self.replica_ids.len()
        &&& 0 <= j < self.replica_ids.len()
        &&& self.replica_ids[i] == self.replica_ids[j] ==> i == j
    }

    pub open spec fn CReplicasIsUnique(&self) -> bool
    {
        forall |i:int, j:int| 0 <= i < self.replica_ids.len() && 0 <= j < self.replica_ids.len() && self.replica_ids[i] == self.replica_ids[j] ==> i == j
    }

    pub open spec fn CWellFormedCConfiguration(&self) -> bool
    {
        &&& 0 < self.replica_ids.len()
        &&& (forall |i:int, j:int| self.CReplicaDistinct(i, j))
        &&& self.CReplicasIsUnique()
    }

    pub open spec fn CIsReplicaIndex(&self, idx:usize, id:EndPoint) -> bool
    {
        &&& 0 <= idx < self.replica_ids.len()
        &&& self.replica_ids[idx as int] == id
    }
}

impl View for CConfiguration {
    type V = LConfiguration;

    open spec fn view(&self) -> LConfiguration {
        LConfiguration {
            clientIds: Set::<AbstractEndPoint>::empty(),
            replica_ids: self.replica_ids@.map(|i, e:EndPoint| e@),
        }
    }
}

pub open spec fn ReplicaIndexValid(index:u64, config:CConfiguration) -> bool
{
    0 <= index < config.replica_ids.len()
}

// =============================================================================
// CConstants (generated + impl methods)
// =============================================================================

#[derive(Clone)]
pub struct CConstants {
    pub config: CConfiguration,
    pub params: CParameters,
}

impl CConstants {
    #[verifier(external_body)]
    pub fn clone_up_to_view(&self) -> (result:Self)
    ensures
        self == result,
        self@ == result@,
        result.valid()
    {
        CConstants {
            config: self.config.clone_up_to_view(),
            params: self.params.clone_up_to_view(),
        }
    }

    pub open spec fn abstractable(self) -> bool
    {
        self.config.abstractable()
    }

    pub open spec fn valid(self) -> bool
    {
        &&& self.config.valid()
        &&& self.params.valid()
        &&& self.abstractable()
        &&& (0 <= self.params.heartbeat_period < self.params.max_integer_val)
        &&& (0 < self.params.max_batch_size as int <= RequestBatchSizeLimit())
        &&& (self.params.max_log_length < max_votes_len())
    }

    pub open spec fn view(self) -> LConstants
        recommends self.abstractable()
    {
        LConstants{
            config:self.config@,
            params:self.params@,
        }
    }
}

impl View for CConstants {
    type V = LConstants;

    open spec fn view(&self) -> LConstants {
        LConstants {
            config: self.config@,
            params: self.params@,
        }
    }
}

// =============================================================================
// CReplicaConstants (generated + impl methods)
// =============================================================================

#[derive(Clone)]
pub struct CReplicaConstants {
    pub my_index: u64,
    pub all: CConstants,
}

impl CReplicaConstants {
    #[verifier(external_body)]
    pub fn clone_up_to_view(&self) -> (result:Self)
    ensures
        self == result,
        self@ == result@,
        result.valid()
    {
        CReplicaConstants {
            my_index: self.my_index,
            all: self.all.clone_up_to_view(),
        }
    }

    pub open spec fn abstractable(self) -> bool
    {
        &&& self.all.abstractable()
        &&& ReplicaIndexValid(self.my_index, self.all.config)
    }

    pub open spec fn valid(self) -> bool
    {
        &&& self.abstractable()
        &&& self.all.valid()
    }

    pub open spec fn view(self) -> LReplicaConstants
        recommends self.abstractable()
    {
        LReplicaConstants{
            my_index: self.my_index as int,
            all: self.all@,
        }
    }
}

impl View for CReplicaConstants {
    type V = LReplicaConstants;

    open spec fn view(&self) -> LReplicaConstants {
        LReplicaConstants {
            my_index: self.my_index as int,
            all: self.all@,
        }
    }
}

// =============================================================================
// Component extension section (part 1 extraction)
// =============================================================================

// =============================================================================
// CAcceptor (generated + impl methods)
// =============================================================================

#[derive(Clone)]
pub struct CAcceptor {
    pub constants: CReplicaConstants,
    pub max_bal: CBallot,
    pub votes: CVotes,
    pub last_checkpointed_operation: Vec<COperationNumber>,
    pub log_truncation_point: COperationNumber,
    pub min_vote_opn: COperationNumber,
}

impl CAcceptor{
    pub open spec fn abstractable(self) -> bool
    {
        &&& self.constants.abstractable()
        &&& self.max_bal.abstractable()
        &&& cvotes_is_abstractable(&self.votes)
        &&& (forall |i:int| 0 <= i < self.last_checkpointed_operation.len() ==> COperationNumberIsAbstractable(self.last_checkpointed_operation[i]))
        &&& COperationNumberIsAbstractable(self.log_truncation_point)
    }

    pub open spec fn valid(self) -> bool {
        &&& self.abstractable()
        &&& self.constants.valid()
        &&& self.max_bal.valid()
        &&& cvotes_is_valid(&self.votes)
        &&& (forall |i:int| 0 <= i < self.last_checkpointed_operation.len() ==> COperationNumberIsValid(self.last_checkpointed_operation[i]))
        &&& COperationNumberIsValid(self.log_truncation_point)
        &&& self.last_checkpointed_operation.len() == self.constants.all.config.replica_ids.len()
    }

    pub open spec fn view(self) -> LAcceptor
        recommends self.abstractable()
    {
        LAcceptor {
            constants: self.constants.view(),
            max_bal: self.max_bal.view(),
            votes: abstractify_cvotes(&self.votes),
            last_checkpointed_operation:self.last_checkpointed_operation@.map(|i,c:COperationNumber| AbstractifyCOperationNumberToOperationNumber(c)),
            log_truncation_point: AbstractifyCOperationNumberToOperationNumber(self.log_truncation_point),
        }
    }

    #[verifier(external_body)]
    pub fn clone_up_to_view(&self) -> (result: Self)
        ensures
            result@ == self@,
            result.valid() == self.valid(),
    {
        self.clone()
    }
}

impl View for CAcceptor {
    type V = LAcceptor;

    open spec fn view(&self) -> LAcceptor {
        LAcceptor {
            constants: self.constants.view(),
            max_bal: self.max_bal.view(),
            votes: abstractify_cvotes(&self.votes),
            last_checkpointed_operation: self.last_checkpointed_operation@.map(|i, c: COperationNumber| AbstractifyCOperationNumberToOperationNumber(c)),
            log_truncation_point: AbstractifyCOperationNumberToOperationNumber(self.log_truncation_point),
        }
    }
}

// =============================================================================
// CLearner (generated + impl methods)
// =============================================================================

#[derive(Clone)]
pub struct CLearner {
    pub constants: CReplicaConstants,
    pub max_ballot_seen: CBallot,
    pub unexecuted_learner_state: CLearnerState,
}

impl CLearner {
    pub open spec fn abstractable(self) -> bool {
        &&& self.constants.abstractable()
        &&& self.max_ballot_seen.abstractable()
        &&& clearnerstate_is_abstractable(self.unexecuted_learner_state)
    }

    pub open spec fn valid(&self) -> bool {
        &&& self.abstractable()
        &&& self.constants.valid()
        &&& self.max_ballot_seen.valid()
        &&& clearnerstate_is_valid(self.unexecuted_learner_state)
    }

    #[verifier(external_body)]
    pub fn clone_up_to_view(&self) -> (res: CLearner)
    ensures
        res@ == self@,
        res.valid() == self.valid(),
    {
        self.clone()
    }
}

impl View for CLearner {
    type V = LLearner;

    open spec fn view(&self) -> LLearner {
        LLearner {
            constants: self.constants@,
            max_ballot_seen: self.max_ballot_seen@,
            unexecuted_learner_state: abstractify_clearnerstate(self.unexecuted_learner_state),
        }
    }
}

// =============================================================================
// CElectionState (generated + impl methods)
// =============================================================================

pub struct CElectionState {
    pub constants: CReplicaConstants,
    pub current_view: CBallot,
    pub current_view_suspectors: HashSet<u64>,
    pub epoch_end_time: u64,
    pub epoch_length: u64,
    pub requests_received_this_epoch: Vec<CRequest>,
    pub requests_received_prev_epochs: Vec<CRequest>,
    pub cur_req_set: HashSet<CRequestHeader>,
    pub prev_req_set: HashSet<CRequestHeader>,
}

// Clone impl for CElectionState is in ElectionImpl.rs (needs clone_hashset_u64)

impl CElectionState {
    pub open spec fn abstractable(self) -> bool {
        &&& self.constants.abstractable()
        &&& self.current_view.abstractable()
        &&& (forall |i:int| 0 <= i < self.requests_received_this_epoch@.len() ==> self.requests_received_this_epoch@[i].abstractable())
        &&& (forall |i:int| 0 <= i < self.requests_received_prev_epochs@.len() ==> self.requests_received_prev_epochs@[i].abstractable())
    }

    pub open spec fn valid(self) -> bool {
        &&& self.abstractable()
        &&& self.constants.valid()
        &&& self.current_view.valid()
        &&& (forall |i:int| 0 <= i < self.requests_received_this_epoch@.len() ==> self.requests_received_this_epoch@[i].valid())
        &&& (forall |i:int| 0 <= i < self.requests_received_prev_epochs@.len() ==> self.requests_received_prev_epochs@[i].valid())
    }

    pub open spec fn view(self) -> ElectionState
        recommends self.abstractable()
    {
        ElectionState{
            constants: self.constants@,
            current_view: self.current_view@,
            current_view_suspectors: self.current_view_suspectors@.map(|x:u64| x as int),
            epoch_end_time: self.epoch_end_time as int,
            epoch_length: self.epoch_length as int,
            requests_received_this_epoch: self.requests_received_this_epoch@.map(|i, r:CRequest| r@),
            requests_received_prev_epochs: self.requests_received_prev_epochs@.map(|i, r:CRequest| r@)
        }
    }
}

impl View for CElectionState {
    type V = ElectionState;

    open spec fn view(&self) -> ElectionState {
        ElectionState {
            constants: self.constants@,
            current_view: self.current_view@,
            current_view_suspectors: self.current_view_suspectors@.map(|u:u64| u as int),
            epoch_end_time: self.epoch_end_time as int,
            epoch_length: self.epoch_length as int,
            requests_received_this_epoch: self.requests_received_this_epoch@.map(|i, r:CRequest| r.view()),
            requests_received_prev_epochs: self.requests_received_prev_epochs@.map(|i, r:CRequest| r.view()),
        }
    }
}

// =============================================================================
// COutstandingOperation (generated enum)
// =============================================================================

#[derive(Clone)]
pub enum COutstandingOperation {
    COutstandingOpKnown {
        v: CRequestBatch,
        bal: CBallot,
    },
    COutstandingOpUnknown {
    },
}

impl COutstandingOperation {
    pub open spec fn valid(&self) -> bool {
        match self {
            COutstandingOperation::COutstandingOpKnown{v, bal} => {
                self.abstractable()
                    && crequestbatch_is_valid(v)
                    && bal.valid()
            }
            COutstandingOperation::COutstandingOpUnknown{} => self.abstractable()
        }
    }

    pub open spec fn abstractable(&self) -> bool {
        match self {
            COutstandingOperation::COutstandingOpKnown{v, bal} => {
                crequestbatch_is_abstractable(v) && bal.abstractable()
            }
            COutstandingOperation::COutstandingOpUnknown{} => true
        }
    }

    pub open spec fn view(self) -> OutstandingOperation
        recommends
            self.abstractable()
    {
        match self {
            COutstandingOperation::COutstandingOpKnown{v,bal} => {
                OutstandingOperation::OutstandingOpKnown{
                    v: abstractify_crequestbatch(&v),
                    bal: bal@,
                }
            }
            COutstandingOperation::COutstandingOpUnknown{} => OutstandingOperation::OutstandingOpUnknown{},
        }
    }
}

impl View for COutstandingOperation {
    type V = OutstandingOperation;

    open spec fn view(&self) -> OutstandingOperation {
        match self {
            COutstandingOperation::COutstandingOpKnown{v, bal} => {
                OutstandingOperation::OutstandingOpKnown{
                    v: abstractify_crequestbatch(v),
                    bal: bal@,
                }
            }
            COutstandingOperation::COutstandingOpUnknown{} => OutstandingOperation::OutstandingOpUnknown{},
        }
    }
}

// =============================================================================
// CExecutor (generated + impl methods)
// =============================================================================

#[derive(Clone)]
pub struct CExecutor {
    pub constants: CReplicaConstants,
    pub app: CAppState,
    pub ops_complete: u64,
    pub max_bal_reflected: CBallot,
    pub next_op_to_execute: COutstandingOperation,
    pub reply_cache: CReplyCache,
}

impl CExecutor {
    pub open spec fn valid(&self) -> bool {
        self.abstractable()
            && self.constants.valid()
            && CAppStateIsValid(&self.app)
            && self.max_bal_reflected.valid()
            && self.next_op_to_execute.valid()
            && creplycache_is_valid(&self.reply_cache)
    }

    pub open spec fn abstractable(&self) -> bool {
        self.constants.abstractable()
            && CAppStateIsAbstractable(&self.app)
            && self.max_bal_reflected.abstractable()
            && self.next_op_to_execute.abstractable()
            && creplycache_is_abstractable(&self.reply_cache)
    }

    pub open spec fn view(&self) -> LExecutor
        recommends
            self.abstractable(){
        let res = LExecutor {
            constants: self.constants.view(),
            app: self.app,
            ops_complete: self.ops_complete as int,
            max_bal_reflected: self.max_bal_reflected.view(),
            next_op_to_execute: self.next_op_to_execute.view(),
            reply_cache: abstractify_creplycache(&self.reply_cache),
        };
        res
    }

    #[verifier(external_body)]
    pub fn clone_up_to_view(&self) -> (result: Self)
        ensures
            result@ == self@,
            result.valid() == self.valid(),
    {
        self.clone()
    }
}

impl View for CExecutor {
    type V = LExecutor;

    open spec fn view(&self) -> LExecutor {
        let res = LExecutor {
            constants: self.constants.view(),
            app: self.app,
            ops_complete: self.ops_complete as int,
            max_bal_reflected: self.max_bal_reflected.view(),
            next_op_to_execute: self.next_op_to_execute.view(),
            reply_cache: abstractify_creplycache(&self.reply_cache),
        };
        res
    }
}

// =============================================================================
// CIncompleteBatchTimer (generated enum)
// =============================================================================

#[derive(Clone)]
pub enum CIncompleteBatchTimer {
    CIncompleteBatchTimerOn {
        when: u64,
    },
    CIncompleteBatchTimerOff,
}

impl CIncompleteBatchTimer{
    pub open spec fn abstractable(self) -> bool {
        match self {
            CIncompleteBatchTimer::CIncompleteBatchTimerOn {when} => true,
            CIncompleteBatchTimer::CIncompleteBatchTimerOff => true,
        }
    }

    pub open spec fn valid(self) -> bool {
        match self {
            CIncompleteBatchTimer::CIncompleteBatchTimerOn {when} => self.abstractable(),
            CIncompleteBatchTimer::CIncompleteBatchTimerOff => self.abstractable(),
        }
    }

    pub open spec fn view(self) -> IncompleteBatchTimer
        recommends
        self.abstractable(),
    {
        match self {
            CIncompleteBatchTimer::CIncompleteBatchTimerOn {when} => IncompleteBatchTimer::IncompleteBatchTimerOn {when:when as int},
            CIncompleteBatchTimer::CIncompleteBatchTimerOff => IncompleteBatchTimer::IncompleteBatchTimerOff{},
        }
    }
}

impl View for CIncompleteBatchTimer {
    type V = IncompleteBatchTimer;

    open spec fn view(&self) -> IncompleteBatchTimer {
        match self {
            CIncompleteBatchTimer::CIncompleteBatchTimerOn {when} => IncompleteBatchTimer::IncompleteBatchTimerOn {when:*when as int},
            CIncompleteBatchTimer::CIncompleteBatchTimerOff => IncompleteBatchTimer::IncompleteBatchTimerOff{},
        }
    }
}

// =============================================================================
// CProposer (generated + impl methods)
// =============================================================================

pub struct CProposer {
    pub constants: CReplicaConstants,
    pub current_state: u64,
    pub request_queue: Vec<CRequest>,
    pub max_ballot_i_sent_1a: CBallot,
    pub next_operation_number_to_propose: u64,
    pub received_1b_packets: HashSet<CPacket>,
    pub highest_seqno_requested_by_client_this_view: HashMap<EndPoint, u64>,
    pub incomplete_batch_timer: CIncompleteBatchTimer,
    pub election_state: CElectionState,
    pub max_log_truncation_point: COperationNumber,
    pub max_opn_with_proposal: COperationNumber,
}

// Clone impl for CProposer is in ProposerImpl.rs (needs local helper access)

impl CProposer{
    pub open spec fn abstractable(self) -> bool {
        &&& self.constants.abstractable()
        &&& (forall |i:int| 0 <= i < self.request_queue@.len() ==> self.request_queue@[i].abstractable())
        &&& self.max_ballot_i_sent_1a.abstractable()
        &&& (forall |p:CPacket| self.received_1b_packets@.contains(p) ==> p.abstractable())
        &&& (forall |k:EndPoint| #[trigger] self.highest_seqno_requested_by_client_this_view@.contains_key(k) ==> k.abstractable())
        &&& self.incomplete_batch_timer.abstractable()
        &&& self.election_state.abstractable()
    }

    pub open spec fn valid(self) -> bool {
        &&& self.abstractable()
        &&& self.constants.valid()
        &&& (forall |i:int| 0 <= i < self.request_queue@.len() ==> self.request_queue@[i].valid())
        &&& self.max_ballot_i_sent_1a.valid()
        &&& (forall |p:CPacket| self.received_1b_packets@.contains(p) ==> p.valid())
        &&& (forall |k:EndPoint| #[trigger] self.highest_seqno_requested_by_client_this_view@.contains_key(k) ==> k.valid_public_key())
        &&& self.incomplete_batch_timer.valid()
        &&& self.election_state.valid()
    }

    #[verifier(external_body)]
    pub fn clone_up_to_view(&self) -> (result: Self)
        ensures
            self == result,
            result@ == self@,
            result.valid() == self.valid(),
    {
        self.clone()
    }

    pub open spec fn view(self) -> LProposer
    recommends self.valid(),
    {
        LProposer{
            constants: self.constants.view(),
            current_state: self.current_state as int,
            request_queue: self.request_queue@.map(|i, r:CRequest| r.view()),
            max_ballot_i_sent_1a: self.max_ballot_i_sent_1a.view(),
            next_operation_number_to_propose: self.next_operation_number_to_propose as int,
            received_1b_packets: self.received_1b_packets@.map(|p:CPacket| p.view()),
            highest_seqno_requested_by_client_this_view: Map::new(
                |ak: AbstractEndPoint| exists |k:EndPoint| self.highest_seqno_requested_by_client_this_view@.contains_key(k) && k@ == ak,
                |ak: AbstractEndPoint| {
                    let k = choose |k: EndPoint| self.highest_seqno_requested_by_client_this_view@.contains_key(k) && k@ == ak;
                    self.highest_seqno_requested_by_client_this_view@[k] as int
                }
            ),
            incomplete_batch_timer: self.incomplete_batch_timer.view(),
            election_state: self.election_state.view(),
        }
    }
}

impl View for CProposer {
    type V = LProposer;

    open spec fn view(&self) -> LProposer {
        LProposer{
            constants: self.constants.view(),
            current_state: self.current_state as int,
            request_queue: self.request_queue@.map(|i, r:CRequest| r.view()),
            max_ballot_i_sent_1a: self.max_ballot_i_sent_1a.view(),
            next_operation_number_to_propose: self.next_operation_number_to_propose as int,
            received_1b_packets: self.received_1b_packets@.map(|p:CPacket| p.view()),
            highest_seqno_requested_by_client_this_view: Map::new(
                |ak: AbstractEndPoint| exists |k:EndPoint| self.highest_seqno_requested_by_client_this_view@.contains_key(k) && k@ == ak,
                |ak: AbstractEndPoint| {
                    let k = choose |k: EndPoint| self.highest_seqno_requested_by_client_this_view@.contains_key(k) && k@ == ak;
                    self.highest_seqno_requested_by_client_this_view@[k] as int
                }
            ),
            incomplete_batch_timer: self.incomplete_batch_timer.view(),
            election_state: self.election_state.view(),
        }
    }
}

// =============================================================================
// CReplica (generated)
// =============================================================================

#[derive(Clone)]
pub struct CReplica {
    pub constants: CReplicaConstants,
    pub nextHeartbeatTime: u64,
    pub proposer: CProposer,
    pub acceptor: CAcceptor,
    pub learner: CLearner,
    pub executor: CExecutor,
}

impl CReplica{
    pub open spec fn valid(self) -> bool {
        self.abstractable()
        &&
        self.constants.valid()
        &&
        self.proposer.valid()
        &&
        self.acceptor.valid()
        &&
        self.learner.valid()
        &&
        self.executor.valid()
        &&
        self.constants@ == self.acceptor.constants@
        &&
        self.constants@ == self.proposer.constants@
        &&
        self.constants@ == self.learner.constants@
        &&
        self.constants@ == self.executor.constants@
    }

    pub open spec fn abstractable(self) -> bool{
        self.constants.abstractable()
        &&
        self.proposer.abstractable()
        &&
        self.acceptor.abstractable()
        &&
        self.learner.abstractable()
        &&
        self.executor.abstractable()
    }

    pub open spec fn view(self) -> LReplica
    recommends
        self.abstractable()
    {
        LReplica{
            constants:self.constants@,
            nextHeartbeatTime:self.nextHeartbeatTime as int,
            proposer:self.proposer@,
            acceptor:self.acceptor@,
            learner:self.learner@,
            executor:self.executor@
        }
    }
}

impl CReplica {
    #[verifier(external_body)]
    pub fn clone_up_to_view(&self) -> (result: Self)
        ensures
            self == result,
            result@ == self@,
            result.valid() == self.valid(),
    {
        self.clone()
    }
}

impl View for CReplica {
    type V = LReplica;

    open spec fn view(&self) -> LReplica {
        LReplica{
            constants:self.constants@,
            nextHeartbeatTime:self.nextHeartbeatTime as int,
            proposer:self.proposer@,
            acceptor:self.acceptor@,
            learner:self.learner@,
            executor:self.executor@
        }
    }
}

// =============================================================================
// CScheduler (generated)
// =============================================================================

#[derive(Clone)]
pub struct CScheduler {
    pub replica: CReplica,
    pub nextActionIndex: u64,
}

impl CScheduler {
    pub open spec fn valid(&self) -> bool {
        &&& self.replica.valid()
        &&& 0 <= self.nextActionIndex < 10  // LReplicaNumActions() == 10
    }
}

impl View for CScheduler {
    type V = LScheduler;

    open spec fn view(&self) -> LScheduler {
        LScheduler {
            replica: self.replica@,
            nextActionIndex: self.nextActionIndex as int,
        }
    }
}

// =============================================================================
// Abstractify functions for CRslIo → RslIo conversion
// =============================================================================

/// Convert a concrete LPacket<EndPoint, CMessage> to spec RslPacket
pub open spec fn abstractify_clpacket(p: LPacket<EndPoint, CMessage>) -> RslPacket {
    LPacket {
        dst: p.dst@,
        src: p.src@,
        msg: p.msg.view(),
    }
}

/// Convert a concrete CRslIo to spec RslIo
pub open spec fn abstractify_crslio(io: CRslIo) -> RslIo {
    match io {
        LIoOp::Send{s} => LIoOp::Send{s: abstractify_clpacket(s)},
        LIoOp::Receive{r} => LIoOp::Receive{r: abstractify_clpacket(r)},
        LIoOp::TimeoutReceive => LIoOp::TimeoutReceive,
        LIoOp::ReadClock{t} => LIoOp::ReadClock{t: t},
    }
}

/// Convert a sequence of CRslIo to Seq<RslIo>
pub open spec fn abstractify_crslio_seq(ios: Seq<CRslIo>) -> Seq<RslIo> {
    ios.map(|i, io: CRslIo| abstractify_crslio(io))
}
