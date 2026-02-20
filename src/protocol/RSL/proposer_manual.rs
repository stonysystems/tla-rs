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

// Phase 19.2.2: Packet-returning functions.
// MaybeEnterNewViewAndSend1a and MaybeEnterPhase2 use clone-delegate pattern
// because auto-generated struct construction lacks validity proofs.

pub exec fn CProposerMaybeEnterNewViewAndSend1a(s: &CProposer) -> (result: (CProposer, Vec<CPacket>))
requires
    s.valid(),
ensures
    result.0.valid(),
    LProposerMaybeEnterNewViewAndSend1a(s@, result.0@, result.1@.map(|i, p: CPacket| p@)),
    forall |i:int| 0 <= i < result.1@.len() ==> result.1@[i].valid(),
    forall |i:int| 0 <= i < result.1@.len() ==> result.1@[i].abstractable(),
{
    let mut state = s.clone_up_to_view();
    let sent = state.CProposerMaybeEnterNewViewAndSend1a();
    let packets = outbound_packets_to_vec(sent);
    (state, packets)
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
    let mut state = s.clone_up_to_view();
    let sent = state.CProposerMaybeEnterPhase2(*log_truncation_point);
    let packets = outbound_packets_to_vec(sent);
    (state, packets)
}

// Phase 19.2.2-3: Remaining packet-returning functions + dispatch.
// These delegate to ProposerImpl methods via clone-delegate pattern because they
// have complex packet construction or require &mut self access to NominateOld/NominateNew.
// They will be made standalone in a future phase.

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
    let mut state = s.clone_up_to_view();
    let sent = state.CProposerNominateNewValueAndSend2a(*clock, *log_truncation_point);
    let packets = outbound_packets_to_vec(sent);
    (state, packets)
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
    let mut state = s.clone_up_to_view();
    let sent = state.CProposerNominateOldValueAndSend2a(*log_truncation_point);
    let packets = outbound_packets_to_vec(sent);
    (state, packets)
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
    let mut state = s.clone_up_to_view();
    let sent = state.CProposerMaybeNominateValueAndSend2a(*clock, *log_truncation_point);
    let packets = outbound_packets_to_vec(sent);
    (state, packets)
}
