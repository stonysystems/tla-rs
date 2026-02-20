// Manual code for all 11 election functions.
// These functions have protocol-specific proofs too complex for auto-generation.
// They are injected into election_gen.rs by the transpiler via manual_code config.
// Uses assume-based proof pattern consistent with other generated RSL modules.

pub exec fn CComputeSuccessorView(b: &CBallot, c: &CConstants) -> (result: CBallot)
requires
    b.valid(),
    c.valid(),
ensures
    result.valid(),
    result@ == ComputeSuccessorView(b@, c@),
{
    if ((b.proposer_id + 1) < (c.config.replica_ids.len() as u64)) {
        let result = CBallot {
            seqno: b.seqno,
            proposer_id: (b.proposer_id + 1),
        };
        assume(result.valid());
        assume(result@ == ComputeSuccessorView(b@, c@));
        result
    } else {
        assume(b.seqno + 1 <= u64::MAX);
        let result = CBallot {
            seqno: (b.seqno + 1),
            proposer_id: 0u64,
        };
        assume(result.valid());
        assume(result@ == ComputeSuccessorView(b@, c@));
        result
    }
}

pub exec fn CRequestsMatch(r1: &CRequest, r2: &CRequest) -> (result: bool)
requires
    r1.valid(),
    r2.valid(),
ensures
    result == RequestsMatch(r1@, r2@),
{
    let result = (r1.client == r2.client) && (r1.seqno == r2.seqno);
    assume(result == RequestsMatch(r1@, r2@));
    result
}

pub exec fn CRequestSatisfiedBy(r1: &CRequest, r2: &CRequest) -> (result: bool)
requires
    r1.valid(),
    r2.valid(),
ensures
    result == RequestSatisfiedBy(r1@, r2@),
{
    let result = (r1.client == r2.client) && (r1.seqno <= r2.seqno);
    assume(result == RequestSatisfiedBy(r1@, r2@));
    result
}

pub exec fn CRemoveAllSatisfiedRequestsInSequence(s: &Vec<CRequest>, r: &CRequest) -> (result: Vec<CRequest>)
requires
    r.valid(),
ensures
    result@.map(|i: int, v: CRequest| v@) == RemoveAllSatisfiedRequestsInSequence(s@.map(|i: int, v: CRequest| v@), r@),
{
    let mut result: Vec<CRequest> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
    invariant
        i <= s.len(),
        r.valid(),
    decreases s.len() - i,
    {
        assume(s[i as int].valid());  // element validity from es.valid()
        if !CRequestSatisfiedBy(&s[i], r) {
            result.push(s[i].clone());
        }
        i = i + 1;
    }
    assume(result@.map(|i: int, v: CRequest| v@) == RemoveAllSatisfiedRequestsInSequence(s@.map(|i: int, v: CRequest| v@), r@));
    result
}

pub exec fn CElectionStateInit(c: &CReplicaConstants) -> (result: CElectionState)
requires
    c.valid(),
    (c.all.config.replica_ids.len() > 0),
ensures
    result.valid(),
    ElectionStateInit(result@, c@),
{
    let result = CElectionState {
        constants: c.clone(),
        current_view: CBallot {
            seqno: 1u64,
            proposer_id: 0u64,
        },
        current_view_suspectors: HashSet::new(),
        epoch_end_time: 0u64,
        epoch_length: c.all.params.baseline_view_timeout_period,
        requests_received_this_epoch: vec![],
        requests_received_prev_epochs: vec![],
        cur_req_set: HashSet::new(),
        prev_req_set: HashSet::new(),
    };
    assume(result.valid());
    assume(ElectionStateInit(result@, c@));
    result
}

pub exec fn CElectionStateProcessHeartbeat(es: &CElectionState, p: &CPacket, clock: &u64) -> (result: CElectionState)
requires
    es.valid(),
    p.valid(),
    p.msg is CMessageHeartbeat,
ensures
    result.valid(),
    ElectionStateProcessHeartbeat(es@, result@, p@, *clock as int),
{
    let result = if !contains(&es.constants.all.config.replica_ids, &p.src) {
        es.clone()
    } else {
        let (_unused0, sender_index) = es.constants.all.config.CGetReplicaIndex(&p.src);
        let sender_index = (sender_index as u64);
        if (CBalEq(&match &p.msg {
            CMessage::CMessageHeartbeat { bal_heartbeat, .. } => bal_heartbeat.clone(),
            _  => unreachable_value(),
        }, &es.current_view) && match &p.msg {
            CMessage::CMessageHeartbeat { suspicious, .. } => suspicious.clone(),
            _  => unreachable_value(),
        }) {
            CElectionState {
                constants: es.constants.clone(),
                current_view: es.current_view.clone(),
                current_view_suspectors: {
                    broadcast use vstd::std_specs::hash::group_hash_axioms;
                    let mut __hs = HashSet::new();
                    __hs.insert(sender_index);
                    union_sets(&es.current_view_suspectors, &__hs)
                },
                epoch_end_time: es.epoch_end_time,
                epoch_length: es.epoch_length,
                requests_received_this_epoch: es.requests_received_this_epoch.clone(),
                requests_received_prev_epochs: es.requests_received_prev_epochs.clone(),
                cur_req_set: HashSet::new(),
                prev_req_set: HashSet::new(),
            }
        } else if CBalLt(&es.current_view, &match &p.msg {
            CMessage::CMessageHeartbeat { bal_heartbeat, .. } => bal_heartbeat.clone(),
            _  => unreachable_value(),
        }) {
            let new_epoch_length = CUpperBoundedAddition(es.epoch_length, es.epoch_length, es.constants.all.params.max_integer_val);
            let new_prevs = concat_vecs(&es.requests_received_prev_epochs, &es.requests_received_this_epoch);
            assume(new_prevs@.len() < 0x1_0000_0000_0000_0000);
            assume(forall |i: int| 0 <= i < new_prevs@.len() ==> new_prevs@[i].valid());
            let bounded_prevs = crate::generated::RSL::types_gen::CElectionState::CBoundRequestSequence(&new_prevs, es.constants.all.params.max_integer_val);
            CElectionState {
                constants: es.constants.clone(),
                current_view: match &p.msg {
                    CMessage::CMessageHeartbeat { bal_heartbeat, .. } => bal_heartbeat.clone(),
                    _  => unreachable_value(),
                },
                current_view_suspectors: if match &p.msg {
                    CMessage::CMessageHeartbeat { suspicious, .. } => suspicious.clone(),
                    _  => unreachable_value(),
                } {
                    broadcast use vstd::std_specs::hash::group_hash_axioms;
                    let mut __hs = HashSet::new();
                    __hs.insert(sender_index);
                    __hs
                } else {
                    HashSet::new()
                },
                epoch_end_time: CUpperBoundedAddition(*clock, new_epoch_length, es.constants.all.params.max_integer_val),
                epoch_length: new_epoch_length,
                requests_received_this_epoch: vec![],
                requests_received_prev_epochs: bounded_prevs,
                cur_req_set: HashSet::new(),
                prev_req_set: HashSet::new(),
            }
        } else {
            es.clone()
        }
    };
    assume(result.valid());
    assume(ElectionStateProcessHeartbeat(es@, result@, p@, *clock as int));
    result
}

pub exec fn CElectionStateCheckForViewTimeout(es: &CElectionState, clock: &u64) -> (result: CElectionState)
requires
    es.valid(),
ensures
    result.valid(),
    ElectionStateCheckForViewTimeout(es@, result@, *clock as int),
{
    let result = if (*clock < es.epoch_end_time) {
        es.clone()
    } else {
        if ((es.requests_received_prev_epochs.len() as u64) == 0) {
            let new_epoch_length = es.constants.all.params.baseline_view_timeout_period;
            CElectionState {
                constants: es.constants.clone(),
                current_view: es.current_view.clone(),
                current_view_suspectors: clone_hashset(&es.current_view_suspectors),
                epoch_end_time: CUpperBoundedAddition(*clock, new_epoch_length, es.constants.all.params.max_integer_val),
                epoch_length: new_epoch_length,
                requests_received_this_epoch: vec![],
                requests_received_prev_epochs: es.requests_received_this_epoch.clone(),
                cur_req_set: HashSet::new(),
                prev_req_set: HashSet::new(),
            }
        } else {
            let new_prevs = concat_vecs(&es.requests_received_prev_epochs, &es.requests_received_this_epoch);
            assume(new_prevs@.len() < 0x1_0000_0000_0000_0000);
            assume(forall |i: int| 0 <= i < new_prevs@.len() ==> new_prevs@[i].valid());
            let bounded_prevs = crate::generated::RSL::types_gen::CElectionState::CBoundRequestSequence(&new_prevs, es.constants.all.params.max_integer_val);
            CElectionState {
                constants: es.constants.clone(),
                current_view: es.current_view.clone(),
                current_view_suspectors: {
                    broadcast use vstd::std_specs::hash::group_hash_axioms;
                    let mut __hs = HashSet::new();
                    __hs.insert(es.constants.my_index);
                    union_sets(&es.current_view_suspectors, &__hs)
                },
                epoch_end_time: CUpperBoundedAddition(*clock, es.epoch_length, es.constants.all.params.max_integer_val),
                epoch_length: es.epoch_length,
                requests_received_this_epoch: vec![],
                requests_received_prev_epochs: bounded_prevs,
                cur_req_set: HashSet::new(),
                prev_req_set: HashSet::new(),
            }
        }
    };
    assume(result.valid());
    assume(ElectionStateCheckForViewTimeout(es@, result@, *clock as int));
    result
}

pub exec fn CElectionStateCheckForQuorumOfViewSuspicions(es: &CElectionState, clock: &u64) -> (result: CElectionState)
requires
    es.valid(),
ensures
    result.valid(),
    ElectionStateCheckForQuorumOfViewSuspicions(es@, result@, *clock as int),
{
    let result = if (((es.current_view_suspectors.len() as u64) < (es.constants.all.config.CMinQuorumSize() as u64)) || !(es.current_view.seqno < es.constants.all.params.max_integer_val)) {
        es.clone()
    } else {
        let new_epoch_length = CUpperBoundedAddition(es.epoch_length, es.epoch_length, es.constants.all.params.max_integer_val);
        let new_prevs = concat_vecs(&es.requests_received_prev_epochs, &es.requests_received_this_epoch);
        assume(new_prevs@.len() < 0x1_0000_0000_0000_0000);
        assume(forall |i: int| 0 <= i < new_prevs@.len() ==> new_prevs@[i].valid());
        let bounded_prevs = crate::generated::RSL::types_gen::CElectionState::CBoundRequestSequence(&new_prevs, es.constants.all.params.max_integer_val);
        CElectionState {
            constants: es.constants.clone(),
            current_view: CComputeSuccessorView(&es.current_view, &es.constants.all),
            current_view_suspectors: HashSet::new(),
            epoch_end_time: CUpperBoundedAddition(*clock, new_epoch_length, es.constants.all.params.max_integer_val),
            epoch_length: new_epoch_length,
            requests_received_this_epoch: vec![],
            requests_received_prev_epochs: bounded_prevs,
            cur_req_set: HashSet::new(),
            prev_req_set: HashSet::new(),
        }
    };
    assume(result.valid());
    assume(ElectionStateCheckForQuorumOfViewSuspicions(es@, result@, *clock as int));
    result
}

pub exec fn CElectionStateReflectReceivedRequest(es: &CElectionState, req: &CRequest) -> (result: CElectionState)
requires
    es.valid(),
    req.valid(),
ensures
    result.valid(),
    ElectionStateReflectReceivedRequest(es@, result@, req@),
{
    let found = {
        let mut found: bool = false;
        let mut i: usize = 0;
        while i < es.requests_received_prev_epochs.len()
        invariant
            i <= es.requests_received_prev_epochs.len(),
            req.valid(),
        decreases es.requests_received_prev_epochs.len() - i,
        {
            assume(es.requests_received_prev_epochs[i as int].valid());  // element validity from es.valid()
            if CRequestsMatch(&es.requests_received_prev_epochs[i], req) {
                found = true;
                break;
            }
            i = i + 1;
        }
        if !found {
            let mut j: usize = 0;
            while j < es.requests_received_this_epoch.len()
            invariant
                j <= es.requests_received_this_epoch.len(),
                req.valid(),
            decreases es.requests_received_this_epoch.len() - j,
            {
                assume(es.requests_received_this_epoch[j as int].valid());  // element validity from es.valid()
                if CRequestsMatch(&es.requests_received_this_epoch[j], req) {
                    found = true;
                    break;
                }
                j = j + 1;
            }
        }
        found
    };
    let result = if found {
        es.clone()
    } else {
        let new_reqs = concat_vecs(&es.requests_received_this_epoch, &vec![req.clone()]);
        assume(new_reqs@.len() < 0x1_0000_0000_0000_0000);
        assume(forall |i: int| 0 <= i < new_reqs@.len() ==> new_reqs@[i].valid());
        let bounded_reqs = crate::generated::RSL::types_gen::CElectionState::CBoundRequestSequence(&new_reqs, es.constants.all.params.max_integer_val);
        CElectionState {
            constants: es.constants.clone(),
            current_view: es.current_view.clone(),
            current_view_suspectors: clone_hashset(&es.current_view_suspectors),
            epoch_end_time: es.epoch_end_time,
            epoch_length: es.epoch_length,
            requests_received_this_epoch: bounded_reqs,
            requests_received_prev_epochs: es.requests_received_prev_epochs.clone(),
            cur_req_set: HashSet::new(),
            prev_req_set: HashSet::new(),
        }
    };
    assume(result.valid());
    assume(ElectionStateReflectReceivedRequest(es@, result@, req@));
    result
}

pub exec fn CRemoveExecutedRequestBatch(reqs: &Vec<CRequest>, batch: &CRequestBatch) -> (result: Vec<CRequest>)
ensures
    result@.map(|i: int, v: CRequest| v@) == RemoveExecutedRequestBatch(reqs@.map(|i: int, v: CRequest| v@), abstractify_crequestbatch(batch)),
{
    let mut acc = reqs.clone();
    let mut i: usize = 0;
    while i < batch.len()
    invariant
        i <= batch.len(),
    decreases batch.len() - i,
    {
        assume(batch[i as int].valid());  // element validity from batch validity
        acc = CRemoveAllSatisfiedRequestsInSequence(&acc, &batch[i]);
        i = i + 1;
    }
    assume(acc@.map(|i: int, v: CRequest| v@) == RemoveExecutedRequestBatch(reqs@.map(|i: int, v: CRequest| v@), abstractify_crequestbatch(batch)));
    acc
}

pub exec fn CElectionStateReflectExecutedRequestBatch(es: &CElectionState, batch: &CRequestBatch) -> (result: CElectionState)
requires
    es.valid(),
ensures
    result.valid(),
    ElectionStateReflectExecutedRequestBatch(es@, result@, abstractify_crequestbatch(batch)),
{
    let result = CElectionState {
        constants: es.constants.clone(),
        current_view: es.current_view.clone(),
        current_view_suspectors: clone_hashset(&es.current_view_suspectors),
        epoch_end_time: es.epoch_end_time,
        epoch_length: es.epoch_length,
        requests_received_this_epoch: CRemoveExecutedRequestBatch(&es.requests_received_this_epoch, batch),
        requests_received_prev_epochs: CRemoveExecutedRequestBatch(&es.requests_received_prev_epochs, batch),
        cur_req_set: HashSet::new(),
        prev_req_set: HashSet::new(),
    };
    assume(result.valid());
    assume(ElectionStateReflectExecutedRequestBatch(es@, result@, abstractify_crequestbatch(batch)));
    result
}
