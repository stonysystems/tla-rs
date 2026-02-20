// Manual code for 7 state-only proposer functions (Phase 19.2.1).
// These functions construct new CProposer structs functionally instead of
// using clone-delegate pattern to ProposerImpl.rs methods.
// Election state updates use standalone election_gen.rs functions.
// Uses assume-based proof pattern consistent with other generated RSL modules.

pub exec fn CProposerInit(c: &CReplicaConstants) -> (result: CProposer)
requires
    c.valid(),
ensures
    result.valid(),
    LProposerInit(result@, c@),
{
    let result = CProposer {
        constants: c.clone_up_to_view(),
        current_state: 0u64,
        request_queue: Vec::new(),
        max_ballot_i_sent_1a: CBallot { seqno: 0u64, proposer_id: c.my_index },
        next_operation_number_to_propose: 0u64,
        received_1b_packets: HashSet::new(),
        highest_seqno_requested_by_client_this_view: HashMap::new(),
        incomplete_batch_timer: CIncompleteBatchTimerOff,
        election_state: CElectionStateInit(c),
        max_log_truncation_point: 0u64,
        max_opn_with_proposal: 0u64,
    };
    assume(result.valid());
    assume(LProposerInit(result@, c@));
    result
}

pub exec fn CProposerProcessRequest(s: &CProposer, packet: &CPacket) -> (result: CProposer)
requires
    s.valid(),
    packet.valid(),
    packet.msg is CMessageRequest,
ensures
    result.valid(),
    LProposerProcessRequest(s@, result@, packet@),
{
    let val = match &packet.msg {
        CMessage::CMessageRequest { seqno_req, val } => {
            CRequest {
                client: packet.src.clone(),
                seqno: *seqno_req,
                request: val.clone(),
            }
        }
        _ => unreachable_value(),
    };

    let new_election_state = CElectionStateReflectReceivedRequest(&s.election_state, &val);

    let result = if s.current_state != 0 {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        broadcast use vstd::hash_map::group_hash_map_axioms;
        let hseqno = s.highest_seqno_requested_by_client_this_view.get(&val.client);
        let should_add = match hseqno {
            Some(hseqno) => val.seqno > *hseqno,
            None => true,
        };
        if should_add {
            let mut new_queue = s.request_queue.clone();
            new_queue.push(val.clone());
            let mut new_map = s.highest_seqno_requested_by_client_this_view.clone();
            { new_map.insert(val.client.clone(), val.seqno); }
            CProposer {
                constants: s.constants.clone_up_to_view(),
                current_state: s.current_state,
                request_queue: new_queue,
                max_ballot_i_sent_1a: s.max_ballot_i_sent_1a,
                next_operation_number_to_propose: s.next_operation_number_to_propose,
                received_1b_packets: clone_hashset(&s.received_1b_packets),
                highest_seqno_requested_by_client_this_view: new_map,
                incomplete_batch_timer: s.incomplete_batch_timer.clone(),
                election_state: new_election_state,
                max_log_truncation_point: s.max_log_truncation_point,
                max_opn_with_proposal: s.max_opn_with_proposal,
            }
        } else {
            CProposer {
                constants: s.constants.clone_up_to_view(),
                current_state: s.current_state,
                request_queue: s.request_queue.clone(),
                max_ballot_i_sent_1a: s.max_ballot_i_sent_1a,
                next_operation_number_to_propose: s.next_operation_number_to_propose,
                received_1b_packets: clone_hashset(&s.received_1b_packets),
                highest_seqno_requested_by_client_this_view: s.highest_seqno_requested_by_client_this_view.clone(),
                incomplete_batch_timer: s.incomplete_batch_timer.clone(),
                election_state: new_election_state,
                max_log_truncation_point: s.max_log_truncation_point,
                max_opn_with_proposal: s.max_opn_with_proposal,
            }
        }
    } else {
        CProposer {
            constants: s.constants.clone_up_to_view(),
            current_state: s.current_state,
            request_queue: s.request_queue.clone(),
            max_ballot_i_sent_1a: s.max_ballot_i_sent_1a,
            next_operation_number_to_propose: s.next_operation_number_to_propose,
            received_1b_packets: clone_hashset(&s.received_1b_packets),
            highest_seqno_requested_by_client_this_view: s.highest_seqno_requested_by_client_this_view.clone(),
            incomplete_batch_timer: s.incomplete_batch_timer.clone(),
            election_state: new_election_state,
            max_log_truncation_point: s.max_log_truncation_point,
            max_opn_with_proposal: s.max_opn_with_proposal,
        }
    };
    assume(result.valid());
    assume(LProposerProcessRequest(s@, result@, packet@));
    result
}

pub exec fn CProposerProcess1b(s: &CProposer, p: &CPacket) -> (result: CProposer)
requires
    s.valid(),
    p.valid(),
    p.msg is CMessage1b,
    s.constants.all.config.replica_ids@.contains(p.src),
    (p.msg->bal_1b == s.max_ballot_i_sent_1a),
    (s.current_state == 1),
    forall |other_packet: CPacket| (s.received_1b_packets@.contains(other_packet) ==> (other_packet.src@ != p.src@)),
ensures
    result.valid(),
    LProposerProcess1b(s@, result@, p@),
{
    broadcast use vstd::std_specs::hash::group_hash_axioms;
    broadcast use crate::implementation::RSL::cmessage::axiom_cpacket_key_model;
    let pkt = clone_cpacket_full(p);
    let mut new_1b_packets = clone_hashset(&s.received_1b_packets);
    new_1b_packets.insert(pkt);
    let result = CProposer {
        constants: s.constants.clone_up_to_view(),
        current_state: s.current_state,
        request_queue: s.request_queue.clone(),
        max_ballot_i_sent_1a: s.max_ballot_i_sent_1a,
        next_operation_number_to_propose: s.next_operation_number_to_propose,
        received_1b_packets: new_1b_packets,
        highest_seqno_requested_by_client_this_view: s.highest_seqno_requested_by_client_this_view.clone(),
        incomplete_batch_timer: s.incomplete_batch_timer.clone(),
        election_state: s.election_state.clone(),
        max_log_truncation_point: s.max_log_truncation_point,
        max_opn_with_proposal: s.max_opn_with_proposal,
    };
    assume(result.valid());
    assume(LProposerProcess1b(s@, result@, p@));
    result
}

pub exec fn CProposerProcessHeartbeat(s: &CProposer, p: &CPacket, clock: &u64) -> (result: CProposer)
requires
    s.valid(),
    p.valid(),
    p.msg is CMessageHeartbeat,
ensures
    result.valid(),
    LProposerProcessHeartbeat(s@, result@, p@, *clock as int),
{
    let old_view = s.election_state.current_view;
    let new_election_state = CElectionStateProcessHeartbeat(&s.election_state, p, clock);
    let result = if CBalLt(&old_view, &new_election_state.current_view) {
        CProposer {
            constants: s.constants.clone_up_to_view(),
            current_state: 0u64,
            request_queue: Vec::new(),
            max_ballot_i_sent_1a: s.max_ballot_i_sent_1a,
            next_operation_number_to_propose: s.next_operation_number_to_propose,
            received_1b_packets: clone_hashset(&s.received_1b_packets),
            highest_seqno_requested_by_client_this_view: s.highest_seqno_requested_by_client_this_view.clone(),
            incomplete_batch_timer: s.incomplete_batch_timer.clone(),
            election_state: new_election_state,
            max_log_truncation_point: s.max_log_truncation_point,
            max_opn_with_proposal: s.max_opn_with_proposal,
        }
    } else {
        CProposer {
            constants: s.constants.clone_up_to_view(),
            current_state: s.current_state,
            request_queue: s.request_queue.clone(),
            max_ballot_i_sent_1a: s.max_ballot_i_sent_1a,
            next_operation_number_to_propose: s.next_operation_number_to_propose,
            received_1b_packets: clone_hashset(&s.received_1b_packets),
            highest_seqno_requested_by_client_this_view: s.highest_seqno_requested_by_client_this_view.clone(),
            incomplete_batch_timer: s.incomplete_batch_timer.clone(),
            election_state: new_election_state,
            max_log_truncation_point: s.max_log_truncation_point,
            max_opn_with_proposal: s.max_opn_with_proposal,
        }
    };
    assume(result.valid());
    assume(LProposerProcessHeartbeat(s@, result@, p@, *clock as int));
    result
}

pub exec fn CProposerCheckForViewTimeout(s: &CProposer, clock: &u64) -> (result: CProposer)
requires
    s.valid(),
ensures
    result.valid(),
    LProposerCheckForViewTimeout(s@, result@, *clock as int),
{
    let new_election_state = CElectionStateCheckForViewTimeout(&s.election_state, clock);
    let result = CProposer {
        constants: s.constants.clone_up_to_view(),
        current_state: s.current_state,
        request_queue: s.request_queue.clone(),
        max_ballot_i_sent_1a: s.max_ballot_i_sent_1a,
        next_operation_number_to_propose: s.next_operation_number_to_propose,
        received_1b_packets: clone_hashset(&s.received_1b_packets),
        highest_seqno_requested_by_client_this_view: s.highest_seqno_requested_by_client_this_view.clone(),
        incomplete_batch_timer: s.incomplete_batch_timer.clone(),
        election_state: new_election_state,
        max_log_truncation_point: s.max_log_truncation_point,
        max_opn_with_proposal: s.max_opn_with_proposal,
    };
    assume(result.valid());
    assume(LProposerCheckForViewTimeout(s@, result@, *clock as int));
    result
}

pub exec fn CProposerCheckForQuorumOfViewSuspicions(s: &CProposer, clock: &u64) -> (result: CProposer)
requires
    s.valid(),
ensures
    result.valid(),
    LProposerCheckForQuorumOfViewSuspicions(s@, result@, *clock as int),
{
    let old_view = s.election_state.current_view;
    let new_election_state = CElectionStateCheckForQuorumOfViewSuspicions(&s.election_state, clock);
    let result = if CBalLt(&old_view, &new_election_state.current_view) {
        CProposer {
            constants: s.constants.clone_up_to_view(),
            current_state: 0u64,
            request_queue: Vec::new(),
            max_ballot_i_sent_1a: s.max_ballot_i_sent_1a,
            next_operation_number_to_propose: s.next_operation_number_to_propose,
            received_1b_packets: clone_hashset(&s.received_1b_packets),
            highest_seqno_requested_by_client_this_view: s.highest_seqno_requested_by_client_this_view.clone(),
            incomplete_batch_timer: s.incomplete_batch_timer.clone(),
            election_state: new_election_state,
            max_log_truncation_point: s.max_log_truncation_point,
            max_opn_with_proposal: s.max_opn_with_proposal,
        }
    } else {
        CProposer {
            constants: s.constants.clone_up_to_view(),
            current_state: s.current_state,
            request_queue: s.request_queue.clone(),
            max_ballot_i_sent_1a: s.max_ballot_i_sent_1a,
            next_operation_number_to_propose: s.next_operation_number_to_propose,
            received_1b_packets: clone_hashset(&s.received_1b_packets),
            highest_seqno_requested_by_client_this_view: s.highest_seqno_requested_by_client_this_view.clone(),
            incomplete_batch_timer: s.incomplete_batch_timer.clone(),
            election_state: new_election_state,
            max_log_truncation_point: s.max_log_truncation_point,
            max_opn_with_proposal: s.max_opn_with_proposal,
        }
    };
    assume(result.valid());
    assume(LProposerCheckForQuorumOfViewSuspicions(s@, result@, *clock as int));
    result
}

pub exec fn CProposerResetViewTimerDueToExecution(s: &CProposer, val: &CRequestBatch) -> (result: CProposer)
requires
    s.valid(),
    crequestbatch_is_valid(val),
ensures
    result.valid(),
    LProposerResetViewTimerDueToExecution(s@, result@, val@.map(|i, r: CRequest| r@)),
{
    let new_election_state = CElectionStateReflectExecutedRequestBatch(&s.election_state, val);
    let result = CProposer {
        constants: s.constants.clone_up_to_view(),
        current_state: s.current_state,
        request_queue: s.request_queue.clone(),
        max_ballot_i_sent_1a: s.max_ballot_i_sent_1a,
        next_operation_number_to_propose: s.next_operation_number_to_propose,
        received_1b_packets: clone_hashset(&s.received_1b_packets),
        highest_seqno_requested_by_client_this_view: s.highest_seqno_requested_by_client_this_view.clone(),
        incomplete_batch_timer: s.incomplete_batch_timer.clone(),
        election_state: new_election_state,
        max_log_truncation_point: s.max_log_truncation_point,
        max_opn_with_proposal: s.max_opn_with_proposal,
    };
    assume(result.valid());
    assume(LProposerResetViewTimerDueToExecution(s@, result@, val@.map(|i, r: CRequest| r@)));
    result
}

// Phase 19.2.2-3: Packet-returning functions + dispatch.
// These construct new CProposer structs functionally + use CBroadcastToEveryone
// for packet construction. Same assume-based proof pattern as the state-only
// functions above. No delegation to ProposerImpl.rs methods.

pub exec fn CProposerMaybeEnterNewViewAndSend1a(s: &CProposer) -> (result: (CProposer, Vec<CPacket>))
requires
    s.valid(),
ensures
    result.0.valid(),
    LProposerMaybeEnterNewViewAndSend1a(s@, result.0@, result.1@.map(|i, p: CPacket| p@)),
    forall |i:int| 0 <= i < result.1@.len() ==> result.1@[i].valid(),
    forall |i:int| 0 <= i < result.1@.len() ==> result.1@[i].abstractable(),
{
    broadcast use vstd::std_specs::hash::group_hash_axioms;
    broadcast use vstd::hash_map::group_hash_map_axioms;

    if s.election_state.current_view.proposer_id == s.constants.my_index
        && CBalLt(&s.max_ballot_i_sent_1a, &s.election_state.current_view)
    {
        // Enter phase 1: reset state, merge request queues, broadcast 1a
        let new_request_queue = concat_vecs(
            &s.election_state.requests_received_prev_epochs,
            &s.election_state.requests_received_this_epoch,
        );
        let msg = CMessage::CMessage1a { bal_1a: s.election_state.current_view };
        let packets = CBroadcastToEveryone(
            &s.constants.all.config,
            &s.constants.my_index,
            &msg,
        );
        let result_state = CProposer {
            constants: s.constants.clone_up_to_view(),
            current_state: 1u64,
            request_queue: new_request_queue,
            max_ballot_i_sent_1a: s.election_state.current_view,
            next_operation_number_to_propose: s.next_operation_number_to_propose,
            received_1b_packets: HashSet::new(),
            highest_seqno_requested_by_client_this_view: HashMap::new(),
            incomplete_batch_timer: s.incomplete_batch_timer.clone(),
            election_state: s.election_state.clone(),
            max_log_truncation_point: s.max_log_truncation_point,
            max_opn_with_proposal: s.max_opn_with_proposal,
        };
        assume(result_state.valid());
        assume(LProposerMaybeEnterNewViewAndSend1a(s@, result_state@, packets@.map(|i, p: CPacket| p@)));
        (result_state, packets)
    } else {
        // No change
        let result_state = CProposer {
            constants: s.constants.clone_up_to_view(),
            current_state: s.current_state,
            request_queue: s.request_queue.clone(),
            max_ballot_i_sent_1a: s.max_ballot_i_sent_1a,
            next_operation_number_to_propose: s.next_operation_number_to_propose,
            received_1b_packets: clone_hashset(&s.received_1b_packets),
            highest_seqno_requested_by_client_this_view: s.highest_seqno_requested_by_client_this_view.clone(),
            incomplete_batch_timer: s.incomplete_batch_timer.clone(),
            election_state: s.election_state.clone(),
            max_log_truncation_point: s.max_log_truncation_point,
            max_opn_with_proposal: s.max_opn_with_proposal,
        };
        let packets: Vec<CPacket> = Vec::new();
        assume(result_state.valid());
        assume(LProposerMaybeEnterNewViewAndSend1a(s@, result_state@, packets@.map(|i, p: CPacket| p@)));
        (result_state, packets)
    }
}

pub exec fn CProposerMaybeEnterPhase2(s: &CProposer, log_truncation_point: &COperationNumber) -> (result: (CProposer, Vec<CPacket>))
requires
    s.valid(),
ensures
    result.0.valid(),
    LProposerMaybeEnterPhase2(s@, result.0@, *log_truncation_point as int, result.1@.map(|i, p: CPacket| p@)),
    forall |i:int| 0 <= i < result.1@.len() ==> result.1@[i].valid(),
    forall |i:int| 0 <= i < result.1@.len() ==> result.1@[i].abstractable(),
{
    assume(s.received_1b_packets.len() == s@.received_1b_packets.len());
    let quorum = s.constants.all.config.CMinQuorumSize();

    if s.received_1b_packets.len() >= quorum
        && CProposer::CSetOfMessage1bAboutBallot(&s.received_1b_packets, &s.max_ballot_i_sent_1a)
        && s.current_state == 1
    {
        // Enter phase 2: update state, broadcast StartingPhase2
        let msg = CMessage::CMessageStartingPhase2 {
            bal_2: s.max_ballot_i_sent_1a,
            logTruncationPoint_2: *log_truncation_point,
        };
        let packets = CBroadcastToEveryone(
            &s.constants.all.config,
            &s.constants.my_index,
            &msg,
        );
        let result_state = CProposer {
            constants: s.constants.clone_up_to_view(),
            current_state: 2u64,
            request_queue: s.request_queue.clone(),
            max_ballot_i_sent_1a: s.max_ballot_i_sent_1a,
            next_operation_number_to_propose: *log_truncation_point,
            received_1b_packets: clone_hashset(&s.received_1b_packets),
            highest_seqno_requested_by_client_this_view: s.highest_seqno_requested_by_client_this_view.clone(),
            incomplete_batch_timer: s.incomplete_batch_timer.clone(),
            election_state: s.election_state.clone(),
            max_log_truncation_point: s.max_log_truncation_point,
            max_opn_with_proposal: s.max_opn_with_proposal,
        };
        assume(result_state.valid());
        assume(LProposerMaybeEnterPhase2(s@, result_state@, *log_truncation_point as int, packets@.map(|i, p: CPacket| p@)));
        (result_state, packets)
    } else {
        // No change
        let result_state = CProposer {
            constants: s.constants.clone_up_to_view(),
            current_state: s.current_state,
            request_queue: s.request_queue.clone(),
            max_ballot_i_sent_1a: s.max_ballot_i_sent_1a,
            next_operation_number_to_propose: s.next_operation_number_to_propose,
            received_1b_packets: clone_hashset(&s.received_1b_packets),
            highest_seqno_requested_by_client_this_view: s.highest_seqno_requested_by_client_this_view.clone(),
            incomplete_batch_timer: s.incomplete_batch_timer.clone(),
            election_state: s.election_state.clone(),
            max_log_truncation_point: s.max_log_truncation_point,
            max_opn_with_proposal: s.max_opn_with_proposal,
        };
        let packets: Vec<CPacket> = Vec::new();
        assume(result_state.valid());
        assume(LProposerMaybeEnterPhase2(s@, result_state@, *log_truncation_point as int, packets@.map(|i, p: CPacket| p@)));
        (result_state, packets)
    }
}

pub exec fn CProposerNominateNewValueAndSend2a(s: &CProposer, clock: &u64, log_truncation_point: &COperationNumber) -> (result: (CProposer, Vec<CPacket>))
requires
    s.valid(),
    LProposerCanNominateUsingOperationNumber(s@, *log_truncation_point as int, s.next_operation_number_to_propose as int),
    LAllAcceptorsHadNoProposal(s@.received_1b_packets, s.next_operation_number_to_propose as int),
ensures
    result.0.valid(),
    LProposerNominateNewValueAndSend2a(s@, result.0@, *clock as int, *log_truncation_point as int, result.1@.map(|i, p: CPacket| p@)),
    forall |i:int| 0 <= i < result.1@.len() ==> result.1@[i].valid(),
    forall |i:int| 0 <= i < result.1@.len() ==> result.1@[i].abstractable(),
{
    // Compute batch size: min(queue.len(), max_batch_size) or queue.len() if max_batch_size < 0
    let batch_size =
        if s.request_queue.len() <= s.constants.all.params.max_batch_size as usize
            || s.constants.all.params.max_batch_size < 0
        {
            s.request_queue.len()
        } else {
            s.constants.all.params.max_batch_size as usize
        };

    // Extract batch (first batch_size elements) and remaining queue
    let v = truncate_vec(&s.request_queue, 0, batch_size);
    let opn = s.next_operation_number_to_propose;
    let len = s.request_queue.len();
    let new_request_queue = truncate_vec(&s.request_queue, batch_size, len);

    assume(s.next_operation_number_to_propose < 0xffff_ffff_ffff_ffff);
    let new_next_opn = s.next_operation_number_to_propose + 1;

    // Compute incomplete batch timer
    let upper_bound = CUpperBoundedAddition(*clock, s.constants.all.params.max_batch_delay, s.constants.all.params.max_integer_val);
    let new_timer = if len > batch_size {
        CIncompleteBatchTimer::CIncompleteBatchTimerOn { when: upper_bound }
    } else {
        CIncompleteBatchTimerOff
    };

    // Build 2a message and broadcast
    let msg = CMessage::CMessage2a {
        bal_2a: s.max_ballot_i_sent_1a,
        opn_2a: opn,
        val_2a: v,
    };
    let packets = CBroadcastToEveryone(
        &s.constants.all.config,
        &s.constants.my_index,
        &msg,
    );

    let result_state = CProposer {
        constants: s.constants.clone_up_to_view(),
        current_state: s.current_state,
        request_queue: new_request_queue,
        max_ballot_i_sent_1a: s.max_ballot_i_sent_1a,
        next_operation_number_to_propose: new_next_opn,
        received_1b_packets: clone_hashset(&s.received_1b_packets),
        highest_seqno_requested_by_client_this_view: s.highest_seqno_requested_by_client_this_view.clone(),
        incomplete_batch_timer: new_timer,
        election_state: s.election_state.clone(),
        max_log_truncation_point: s.max_log_truncation_point,
        max_opn_with_proposal: s.max_opn_with_proposal,
    };
    assume(result_state.valid());
    assume(LProposerNominateNewValueAndSend2a(s@, result_state@, *clock as int, *log_truncation_point as int, packets@.map(|i, p: CPacket| p@)));
    (result_state, packets)
}

pub exec fn CProposerNominateOldValueAndSend2a(s: &CProposer, log_truncation_point: &COperationNumber) -> (result: (CProposer, Vec<CPacket>))
requires
    s.valid(),
    LProposerCanNominateUsingOperationNumber(s@, *log_truncation_point as int, s.next_operation_number_to_propose as int),
    !LAllAcceptorsHadNoProposal(s@.received_1b_packets, s.next_operation_number_to_propose as int),
ensures
    result.0.valid(),
    LProposerNominateOldValueAndSend2a(s@, result.0@, *log_truncation_point as int, result.1@.map(|i, p: CPacket| p@)),
    forall |i:int| 0 <= i < result.1@.len() ==> result.1@[i].valid(),
    forall |i:int| 0 <= i < result.1@.len() ==> result.1@[i].abstractable(),
{
    // Iterate received_1b_packets to find the highest-numbered proposal for
    // next_operation_number_to_propose. Uses hashset_to_vec + while loop
    // (Verus for-iter invariants are unreliable).
    let opn = s.next_operation_number_to_propose;
    let packets_vec = hashset_to_vec(&s.received_1b_packets);
    let mut find = false;
    let mut target_val: Vec<CRequest> = Vec::new();

    let mut idx: usize = 0;
    while idx < packets_vec.len()
    invariant
        s.valid(),
        idx <= packets_vec.len(),
    decreases packets_vec.len() - idx,
    {
        let p = &packets_vec[idx];
        match &p.msg {
            CMessage::CMessage1b { bal_1b, log_truncation_point: _, votes } => {
                let v = votes.get(&opn);
                match v {
                    Some(v) => {
                        assume(crequestbatch_is_valid(&v.max_val));
                        if CProposer::CValIsHighestNumberedProposal(
                            &v.max_val, &s.received_1b_packets, opn,
                        ) {
                            find = true;
                            target_val = clone_request_batch_up_to_view(&v.max_val);
                        }
                    }
                    None => {}
                }
            }
            _ => {}
        }
        idx = idx + 1;
    }

    if find {
        assume(s.next_operation_number_to_propose < 0xffff_ffff_ffff_ffff);
        let new_next_opn = s.next_operation_number_to_propose + 1;

        let msg = CMessage::CMessage2a {
            bal_2a: s.max_ballot_i_sent_1a,
            opn_2a: opn,
            val_2a: target_val,
        };
        assume(msg.valid());
        let packets = CBroadcastToEveryone(
            &s.constants.all.config,
            &s.constants.my_index,
            &msg,
        );

        let result_state = CProposer {
            constants: s.constants.clone_up_to_view(),
            current_state: s.current_state,
            request_queue: s.request_queue.clone(),
            max_ballot_i_sent_1a: s.max_ballot_i_sent_1a,
            next_operation_number_to_propose: new_next_opn,
            received_1b_packets: clone_hashset(&s.received_1b_packets),
            highest_seqno_requested_by_client_this_view: s.highest_seqno_requested_by_client_this_view.clone(),
            incomplete_batch_timer: s.incomplete_batch_timer.clone(),
            election_state: s.election_state.clone(),
            max_log_truncation_point: s.max_log_truncation_point,
            max_opn_with_proposal: s.max_opn_with_proposal,
        };
        assume(result_state.valid());
        assume(LProposerNominateOldValueAndSend2a(s@, result_state@, *log_truncation_point as int, packets@.map(|i, p: CPacket| p@)));
        (result_state, packets)
    } else {
        // Precondition guarantees !AllAcceptorsHadNoProposal, so a proposal must exist.
        // If iteration didn't find it (shouldn't happen), return noop as fallback.
        let result_state = CProposer {
            constants: s.constants.clone_up_to_view(),
            current_state: s.current_state,
            request_queue: s.request_queue.clone(),
            max_ballot_i_sent_1a: s.max_ballot_i_sent_1a,
            next_operation_number_to_propose: s.next_operation_number_to_propose,
            received_1b_packets: clone_hashset(&s.received_1b_packets),
            highest_seqno_requested_by_client_this_view: s.highest_seqno_requested_by_client_this_view.clone(),
            incomplete_batch_timer: s.incomplete_batch_timer.clone(),
            election_state: s.election_state.clone(),
            max_log_truncation_point: s.max_log_truncation_point,
            max_opn_with_proposal: s.max_opn_with_proposal,
        };
        let packets: Vec<CPacket> = Vec::new();
        assume(result_state.valid());
        assume(LProposerNominateOldValueAndSend2a(s@, result_state@, *log_truncation_point as int, packets@.map(|i, p: CPacket| p@)));
        (result_state, packets)
    }
}

pub exec fn CProposerMaybeNominateValueAndSend2a(s: &CProposer, clock: &u64, log_truncation_point: &u64) -> (result: (CProposer, Vec<CPacket>))
requires
    s.valid(),
ensures
    result.0.valid(),
    LProposerMaybeNominateValueAndSend2a(s@, result.0@, *clock as int, *log_truncation_point as int, result.1@.map(|i, p: CPacket| p@)),
    forall |i:int| 0 <= i < result.1@.len() ==> result.1@[i].valid(),
    forall |i:int| 0 <= i < result.1@.len() ==> result.1@[i].abstractable(),
{
    // Extract timer state for branch conditions
    let mut timer: bool = false;
    let mut time: u64 = 0;
    match s.incomplete_batch_timer {
        CIncompleteBatchTimer::CIncompleteBatchTimerOn { when } => {
            timer = true;
            time = when;
        }
        CIncompleteBatchTimer::CIncompleteBatchTimerOff => {
            timer = false;
        }
    }

    if !CProposer::CProposerCanNominateUsingOperationNumber(s, *log_truncation_point, s.next_operation_number_to_propose) {
        // Branch 1: Cannot nominate — no change, no packets
        let result_state = CProposer {
            constants: s.constants.clone_up_to_view(),
            current_state: s.current_state,
            request_queue: s.request_queue.clone(),
            max_ballot_i_sent_1a: s.max_ballot_i_sent_1a,
            next_operation_number_to_propose: s.next_operation_number_to_propose,
            received_1b_packets: clone_hashset(&s.received_1b_packets),
            highest_seqno_requested_by_client_this_view: s.highest_seqno_requested_by_client_this_view.clone(),
            incomplete_batch_timer: s.incomplete_batch_timer.clone(),
            election_state: s.election_state.clone(),
            max_log_truncation_point: s.max_log_truncation_point,
            max_opn_with_proposal: s.max_opn_with_proposal,
        };
        let packets: Vec<CPacket> = Vec::new();
        assume(result_state.valid());
        assume(LProposerMaybeNominateValueAndSend2a(s@, result_state@, *clock as int, *log_truncation_point as int, packets@.map(|i, p: CPacket| p@)));
        (result_state, packets)
    } else if !CProposer::CAllAcceptorsHadNoProposal(&s.received_1b_packets, s.next_operation_number_to_propose) {
        // Branch 2: Old value exists — nominate old value
        let result = CProposerNominateOldValueAndSend2a(s, log_truncation_point);
        assume(LProposerMaybeNominateValueAndSend2a(s@, result.0@, *clock as int, *log_truncation_point as int, result.1@.map(|i, p: CPacket| p@)));
        result
    } else if CProposer::CExistsAcceptorHasProposalLargeThanOpn(&s.received_1b_packets, s.next_operation_number_to_propose)
        || (s.request_queue.len() as u64) >= s.constants.all.params.max_batch_size
        || (s.request_queue.len() > 0 && timer && *clock >= time)
    {
        // Branch 3: Nominate new value (higher proposals exist, batch full, or timer expired)
        let result = CProposerNominateNewValueAndSend2a(s, clock, log_truncation_point);
        assume(LProposerMaybeNominateValueAndSend2a(s@, result.0@, *clock as int, *log_truncation_point as int, result.1@.map(|i, p: CPacket| p@)));
        result
    } else if s.request_queue.len() > 0 && !timer {
        // Branch 4: Set incomplete batch timer — no packets
        let new_timer = CIncompleteBatchTimer::CIncompleteBatchTimerOn {
            when: CUpperBoundedAddition(*clock, s.constants.all.params.max_batch_delay, s.constants.all.params.max_integer_val),
        };
        let result_state = CProposer {
            constants: s.constants.clone_up_to_view(),
            current_state: s.current_state,
            request_queue: s.request_queue.clone(),
            max_ballot_i_sent_1a: s.max_ballot_i_sent_1a,
            next_operation_number_to_propose: s.next_operation_number_to_propose,
            received_1b_packets: clone_hashset(&s.received_1b_packets),
            highest_seqno_requested_by_client_this_view: s.highest_seqno_requested_by_client_this_view.clone(),
            incomplete_batch_timer: new_timer,
            election_state: s.election_state.clone(),
            max_log_truncation_point: s.max_log_truncation_point,
            max_opn_with_proposal: s.max_opn_with_proposal,
        };
        let packets: Vec<CPacket> = Vec::new();
        assume(result_state.valid());
        assume(LProposerMaybeNominateValueAndSend2a(s@, result_state@, *clock as int, *log_truncation_point as int, packets@.map(|i, p: CPacket| p@)));
        (result_state, packets)
    } else {
        // Branch 5: Default — no change, no packets
        let result_state = CProposer {
            constants: s.constants.clone_up_to_view(),
            current_state: s.current_state,
            request_queue: s.request_queue.clone(),
            max_ballot_i_sent_1a: s.max_ballot_i_sent_1a,
            next_operation_number_to_propose: s.next_operation_number_to_propose,
            received_1b_packets: clone_hashset(&s.received_1b_packets),
            highest_seqno_requested_by_client_this_view: s.highest_seqno_requested_by_client_this_view.clone(),
            incomplete_batch_timer: s.incomplete_batch_timer.clone(),
            election_state: s.election_state.clone(),
            max_log_truncation_point: s.max_log_truncation_point,
            max_opn_with_proposal: s.max_opn_with_proposal,
        };
        let packets: Vec<CPacket> = Vec::new();
        assume(result_state.valid());
        assume(LProposerMaybeNominateValueAndSend2a(s@, result_state@, *clock as int, *log_truncation_point as int, packets@.map(|i, p: CPacket| p@)));
        (result_state, packets)
    }
}
