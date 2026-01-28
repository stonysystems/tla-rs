use crate::protocol::RSL::broadcast::*;
use crate::protocol::RSL::configuration::*;
use crate::protocol::RSL::constants::*;
use crate::protocol::RSL::election::*;
use crate::protocol::RSL::environment::*;
use crate::protocol::RSL::message::*;
use crate::protocol::RSL::state_machine::*;
use crate::protocol::RSL::types::*;
use vstd::prelude::*;
use vstd::{map::*, modes::*, prelude::*, seq::*, seq_lib::*, *};
use vstd::{set::*, set_lib::*};

use crate::protocol::common::upper_bound::*;

use crate::services::RSL::app_state_machine::*;

use crate::common::framework::environment_s::*;
use crate::common::native::io_s::*;

verus! {
    pub enum IncompleteBatchTimer{
        IncompleteBatchTimerOn{when:int},
        IncompleteBatchTimerOff{},
    }

    pub struct LProposer{
        pub constants:LReplicaConstants,
        // The replica constants, duplicated here for convenience

        pub current_state:int,
        // What state the proposer is in:
        // 0 = not leader
        // 1 = leader in phase 1
        // 2 = leader in phase 2

        // request_queue:RequestBatch,
        pub request_queue:Seq<Request>,
        // Values that clients have requested that I need to eventually
        // propose, in the order I should propose them

        pub max_ballot_i_sent_1a:Ballot,
        // The maximum ballot I've sent a 1a message for

        pub next_operation_number_to_propose:int,
        // The next operation number I should propose

        pub received_1b_packets:Set<RslPacket>,
        // The set of 1b messages I've received concerning max_ballot_i_sent_1a

        pub highest_seqno_requested_by_client_this_view:Map<AbstractEndPoint, int>,
        // For each client, the highest sequence number for a request
        // I proposed in max_ballot_i_sent_1a

        pub incomplete_batch_timer:IncompleteBatchTimer,
        // If the incomplete batch timer is set, it indicates when I should
        // give up on trying to amass a full-size batch and just propose
        // whatever I have.  If it's not set, I shouldn't propose an
        // incomplete batch.

        pub election_state:ElectionState,
        // State for view change election management
    }

    pub open spec fn LIsAfterLogTruncationPoint(opn:OperationNumber, received_1b_packets:Set<RslPacket>) -> bool
    {
        (forall |p:RslPacket| received_1b_packets.contains(p) && p.msg is RslMessage1b ==> p.msg->log_truncation_point <= opn)
    }


    pub open spec fn LSetOfMessage1b(S:Set<RslPacket>) -> bool
    {
        forall |p:RslPacket| S.contains(p) ==> p.msg is RslMessage1b
    }

    pub open spec fn LSetOfMessage1bAboutBallot(S:Set<RslPacket>, b:Ballot) -> bool
    {
        &&& LSetOfMessage1b(S)
        &&& (forall |p:RslPacket| S.contains(p) ==> p.msg->bal_1b == b)
    }

    pub open spec fn LExistVotesHasProposalLargeThanOpn(p:RslPacket, op:OperationNumber) -> bool
        recommends
            p.msg is RslMessage1b
    {
        exists |opn:OperationNumber| p.msg->votes.contains_key(opn) && opn > op
    }

    pub open spec fn LExistsAcceptorHasProposalLargeThanOpn(S:Set<RslPacket>, op:OperationNumber) -> bool
    recommends
            LSetOfMessage1b(S)
    {
        // exists p :: p in S && exists opn :: opn in p.msg.votes && opn > op
        exists |p:RslPacket| S.contains(p) && LExistVotesHasProposalLargeThanOpn(p, op)
    }

    pub open spec fn LAllAcceptorsHadNoProposal(S:Set<RslPacket>, opn:OperationNumber) -> bool
    recommends
            LSetOfMessage1b(S)
    {
        forall |p:RslPacket| S.contains(p) ==> !p.msg->votes.contains_key(opn)
    }

    pub open spec fn Lmax_balInS(c:Ballot, S:Set<RslPacket>, opn:OperationNumber) -> bool
    recommends
            LSetOfMessage1b(S)
    {
        forall |p:RslPacket| S.contains(p) && p.msg->votes.contains_key(opn) ==> BalLeq(p.msg->votes[opn].max_value_bal, c)
    }

    pub open spec fn LExistsBallotInS(v:RequestBatch, c:Ballot, S:Set<RslPacket>, opn:OperationNumber) -> bool
    recommends
            LSetOfMessage1b(S)
    {
        exists |p:RslPacket| S.contains(p)
                    && p.msg->votes.contains_key(opn)
                    && p.msg->votes[opn].max_value_bal==c
                    && p.msg->votes[opn].max_val==v
    }

    pub open spec fn LValIsHighestNumberedProposalAtBallot(v:RequestBatch, c:Ballot, S:Set<RslPacket>, opn:OperationNumber) -> bool
    recommends
            LSetOfMessage1b(S)
    {
        &&& Lmax_balInS(c, S, opn)
        &&& LExistsBallotInS(v, c, S, opn)
    }

    pub open spec fn LValIsHighestNumberedProposal(v:RequestBatch, S:Set<RslPacket>, opn:OperationNumber) -> bool
    recommends
            LSetOfMessage1b(S)
    {
        // exists c :: c in S && opn in c.msg.votes && LValIsHighestNumberedProposalAtBallot(v, c, S, opn)
        exists |c:Ballot| LValIsHighestNumberedProposalAtBallot(v, c, S, opn)
    }

    pub open spec fn LProposerCanNominateUsingOperationNumber(s:LProposer, log_truncation_point:OperationNumber, opn:OperationNumber) -> bool
    {
        &&& s.election_state.current_view == s.max_ballot_i_sent_1a
        &&& s.current_state == 2
        &&& s.received_1b_packets.len() >= LMinQuorumSize(s.constants.all.config)
        &&& LSetOfMessage1bAboutBallot(s.received_1b_packets, s.max_ballot_i_sent_1a)
        // Don't try to nominate for an operation that's already been truncated into history:
        &&& LIsAfterLogTruncationPoint(opn, s.received_1b_packets)
        // Don't try to nominate in an operation that's too far in the future; that would grow the log too much.
        &&& opn < UpperBoundedAddition(log_truncation_point, s.constants.all.params.max_log_length, s.constants.all.params.max_integer_val)
        // Disallow negative operations
        &&& opn >= 0
        // It must be possible to add one and still be representable, so we can compute next_operation_number_to_propose
        &&& LtUpperBound(opn, s.constants.all.params.max_integer_val)
    }

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

    pub open spec fn LProposerProcessRequest(
        s:LProposer,
        s_:LProposer,
        packet:RslPacket
    ) -> bool
    recommends
            packet.msg is RslMessageRequest
    {
        let val = Request{client:packet.src, seqno:packet.msg->seqno_req, request:packet.msg->val};
        &&& ElectionStateReflectReceivedRequest(s.election_state, s_.election_state, val)
        &&& if s.current_state != 0
            && (!s.highest_seqno_requested_by_client_this_view.contains_key(val.client)
                || val.seqno > s.highest_seqno_requested_by_client_this_view[val.client])
            {
                s_ == LProposer{
                    constants:s.constants,
                    current_state:s.current_state,
                    request_queue:s.request_queue + seq![val],
                    max_ballot_i_sent_1a:s.max_ballot_i_sent_1a,
                    next_operation_number_to_propose:s.next_operation_number_to_propose,
                    received_1b_packets:s.received_1b_packets,
                    highest_seqno_requested_by_client_this_view:s.highest_seqno_requested_by_client_this_view.insert(val.client, val.seqno),
                    incomplete_batch_timer:s.incomplete_batch_timer,
                    election_state:s_.election_state
                }
            } else {
                s_ == LProposer{
                    constants:s.constants,
                    current_state:s.current_state,
                    request_queue:s.request_queue,
                    max_ballot_i_sent_1a:s.max_ballot_i_sent_1a,
                    next_operation_number_to_propose:s.next_operation_number_to_propose,
                    received_1b_packets:s.received_1b_packets,
                    highest_seqno_requested_by_client_this_view:s.highest_seqno_requested_by_client_this_view,
                    incomplete_batch_timer:s.incomplete_batch_timer,
                    election_state:s_.election_state
                }
            }
    }

    pub open spec fn LProposerMaybeEnterNewViewAndSend1a(
        s:LProposer,
        s_:LProposer,
        sent_packets:Seq<RslPacket>
    ) -> bool
    {
        if s.election_state.current_view.proposer_id == s.constants.my_index
            && BalLt(s.max_ballot_i_sent_1a, s.election_state.current_view)
        {
            &&& s_ == LProposer{
                constants:s.constants,
                current_state:1,
                request_queue:s.election_state.requests_received_prev_epochs + s.election_state.requests_received_this_epoch,
                max_ballot_i_sent_1a:s.election_state.current_view,
                next_operation_number_to_propose:s.next_operation_number_to_propose,
                received_1b_packets:Set::<RslPacket>::empty(),
                highest_seqno_requested_by_client_this_view:Map::<AbstractEndPoint, int>::empty(),
                incomplete_batch_timer:s.incomplete_batch_timer,
                election_state:s.election_state
            }
            &&& LBroadcastToEveryone(s.constants.all.config, s.constants.my_index,
                                    RslMessage::RslMessage1a{bal_1a:s.election_state.current_view},
                                    sent_packets)
        } else {
            &&& s_ == s
            &&& sent_packets == Seq::<RslPacket>::empty()
        }
    }

    pub open spec fn LProposerProcess1b(
        s:LProposer,
        s_:LProposer,
        p:RslPacket
    ) -> bool
    recommends
            p.msg is RslMessage1b,
            s.constants.all.config.replica_ids.contains(p.src),
            p.msg->bal_1b == s.max_ballot_i_sent_1a,
            s.current_state == 1,
            forall |other_packet:RslPacket| s.received_1b_packets.contains(other_packet) ==> other_packet.src != p.src
    {
        s_ == LProposer{
            constants:s.constants,
            current_state:s.current_state,
            request_queue:s.request_queue,
            max_ballot_i_sent_1a:s.max_ballot_i_sent_1a,
            next_operation_number_to_propose:s.next_operation_number_to_propose,
            received_1b_packets:s.received_1b_packets + set![p],
            highest_seqno_requested_by_client_this_view:s.highest_seqno_requested_by_client_this_view,
            incomplete_batch_timer:s.incomplete_batch_timer,
            election_state:s.election_state
        }
    }

    pub open spec fn LProposerMaybeEnterPhase2(
        s:LProposer,
        s_:LProposer,
        log_truncation_point:OperationNumber,
        sent_packets:Seq<RslPacket>
    ) -> bool
    {
        if s.received_1b_packets.len() >= LMinQuorumSize(s.constants.all.config)
            && LSetOfMessage1bAboutBallot(s.received_1b_packets, s.max_ballot_i_sent_1a)
            && s.current_state == 1
        {
            &&& s_ == LProposer{
                constants:s.constants,
                current_state:2,
                request_queue:s.request_queue,
                max_ballot_i_sent_1a:s.max_ballot_i_sent_1a,
                next_operation_number_to_propose:log_truncation_point,
                received_1b_packets:s.received_1b_packets,
                highest_seqno_requested_by_client_this_view:s.highest_seqno_requested_by_client_this_view,
                incomplete_batch_timer:s.incomplete_batch_timer,
                election_state:s.election_state
            }
            &&& LBroadcastToEveryone(s.constants.all.config, s.constants.my_index,
                                    RslMessage::RslMessageStartingPhase2{
                                        bal_2:s.max_ballot_i_sent_1a, logTruncationPoint_2:log_truncation_point
                                    }, sent_packets)
        } else {
            &&& s_ == s
            &&& sent_packets == Seq::<RslPacket>::empty()
        }
    }

    pub open spec fn LProposerNominateNewValueAndSend2a(
        s:LProposer,
        s_:LProposer,
        clock:int,
        log_truncation_point:OperationNumber,
        sent_packets:Seq<RslPacket>
    ) -> bool
    recommends
            LProposerCanNominateUsingOperationNumber(s, log_truncation_point, s.next_operation_number_to_propose),
            LAllAcceptorsHadNoProposal(s.received_1b_packets, s.next_operation_number_to_propose)
    {
        let batchSize = if s.request_queue.len() <= s.constants.all.params.max_batch_size || s.constants.all.params.max_batch_size < 0 {
                            s.request_queue.len() as int
                        } else {
                            s.constants.all.params.max_batch_size
                        };
        let v = s.request_queue.subrange(0, batchSize);
        let opn = s.next_operation_number_to_propose;
        &&& s_ == LProposer{
            constants:s.constants,
            current_state:s.current_state,
            request_queue:s.request_queue.subrange(batchSize, s.request_queue.len() as int),
            max_ballot_i_sent_1a:s.max_ballot_i_sent_1a,
            next_operation_number_to_propose:s.next_operation_number_to_propose + 1,
            received_1b_packets:s.received_1b_packets,
            highest_seqno_requested_by_client_this_view:s.highest_seqno_requested_by_client_this_view,
            incomplete_batch_timer: if s.request_queue.len() > batchSize
                                    {
                                        IncompleteBatchTimer::IncompleteBatchTimerOn{when:UpperBoundedAddition(clock, s.constants.all.params.max_batch_delay, s.constants.all.params.max_integer_val)}
                                    } else {
                                        IncompleteBatchTimer::IncompleteBatchTimerOff{}
                                    },
            election_state:s.election_state
        }
        &&& LBroadcastToEveryone(s.constants.all.config, s.constants.my_index,
                                RslMessage::RslMessage2a{bal_2a:s.max_ballot_i_sent_1a, opn_2a:opn, val_2a:v},
                                sent_packets)
    }

    pub open spec fn LProposerNominateOldValueAndSend2a(
        s:LProposer,
        s_:LProposer,
        log_truncation_point:OperationNumber,
        sent_packets:Seq<RslPacket>
    ) -> bool
    recommends LProposerCanNominateUsingOperationNumber(s, log_truncation_point, s.next_operation_number_to_propose),
                 !LAllAcceptorsHadNoProposal(s.received_1b_packets, s.next_operation_number_to_propose)
    {
        let opn = s.next_operation_number_to_propose;
        exists |p:RslPacket| s.received_1b_packets.contains(p)
                            && LValIsHighestNumberedProposal(p.msg->votes[opn].max_val, s.received_1b_packets, opn)
                            && s_ == LProposer{
                                constants:s.constants,
                                current_state:s.current_state,
                                request_queue:s.request_queue,
                                max_ballot_i_sent_1a:s.max_ballot_i_sent_1a,
                                next_operation_number_to_propose:s.next_operation_number_to_propose + 1,
                                received_1b_packets:s.received_1b_packets,
                                highest_seqno_requested_by_client_this_view:s.highest_seqno_requested_by_client_this_view,
                                incomplete_batch_timer:s.incomplete_batch_timer,
                                election_state:s.election_state
                            }
                            && LBroadcastToEveryone(s.constants.all.config, s.constants.my_index,
                                RslMessage::RslMessage2a{bal_2a:s.max_ballot_i_sent_1a, opn_2a:opn, val_2a:p.msg->votes[opn].max_val},
                                sent_packets)
    }

    pub open spec fn LProposerMaybeNominateValueAndSend2a(
        s:LProposer,
        s_:LProposer,
        clock:int,
        log_truncation_point:int,
        sent_packets:Seq<RslPacket>
    ) -> bool
    {
        if !LProposerCanNominateUsingOperationNumber(s, log_truncation_point, s.next_operation_number_to_propose) {
            &&& s_ == s
            &&& sent_packets == Seq::<RslPacket>::empty()
        } else if !LAllAcceptorsHadNoProposal(s.received_1b_packets, s.next_operation_number_to_propose) {
            LProposerNominateOldValueAndSend2a(s, s_, log_truncation_point, sent_packets)
        } else if LExistsAcceptorHasProposalLargeThanOpn(s.received_1b_packets, s.next_operation_number_to_propose)
                || s.request_queue.len() >= s.constants.all.params.max_batch_size
                || (s.request_queue.len() > 0 && s.incomplete_batch_timer is IncompleteBatchTimerOn && clock >= s.incomplete_batch_timer->when)
        {
            LProposerNominateNewValueAndSend2a(s, s_, clock, log_truncation_point, sent_packets)
        } else if s.request_queue.len() > 0 && s.incomplete_batch_timer is IncompleteBatchTimerOff {
            &&& s_ == LProposer{
                constants:s.constants,
                current_state:s.current_state,
                request_queue:s.request_queue,
                max_ballot_i_sent_1a:s.max_ballot_i_sent_1a,
                next_operation_number_to_propose:s.next_operation_number_to_propose,
                received_1b_packets:s.received_1b_packets,
                highest_seqno_requested_by_client_this_view:s.highest_seqno_requested_by_client_this_view,
                incomplete_batch_timer:IncompleteBatchTimer::IncompleteBatchTimerOn{when:UpperBoundedAddition(clock, s.constants.all.params.max_batch_delay, s.constants.all.params.max_integer_val)},
                election_state:s.election_state
            }
            &&& sent_packets == Seq::<RslPacket>::empty()
        } else {
            &&& s_ == s
            &&& sent_packets == Seq::<RslPacket>::empty()
        }
    }

    pub open spec fn LProposerProcessHeartbeat(
        s:LProposer,
        s_:LProposer,
        p:RslPacket,
        clock:int
    ) -> bool
    recommends
            p.msg is RslMessageHeartbeat
    {
        &&& ElectionStateProcessHeartbeat(s.election_state, s_.election_state, p, clock)
        &&& (if BalLt(s.election_state.current_view, s_.election_state.current_view) {
                s_.current_state == 0 && s_.request_queue == Seq::<Request>::empty()
            } else {
                s_.current_state == s.current_state && s_.request_queue == s.request_queue
            })
        &&& s_ == LProposer{
            constants:s.constants,
            current_state:s_.current_state,
            request_queue:s_.request_queue,
            max_ballot_i_sent_1a:s.max_ballot_i_sent_1a,
            next_operation_number_to_propose:s.next_operation_number_to_propose,
            received_1b_packets:s.received_1b_packets,
            highest_seqno_requested_by_client_this_view:s.highest_seqno_requested_by_client_this_view,
            incomplete_batch_timer:s.incomplete_batch_timer,
            election_state:s_.election_state
        }
    }

    pub open spec fn LProposerCheckForViewTimeout(
        s:LProposer,
        s_:LProposer,
        clock:int
    ) -> bool
    {
        &&& ElectionStateCheckForViewTimeout(s.election_state, s_.election_state, clock)
        &&& s_ == LProposer{
            constants:s.constants,
            current_state:s.current_state,
            request_queue:s.request_queue,
            max_ballot_i_sent_1a:s.max_ballot_i_sent_1a,
            next_operation_number_to_propose:s.next_operation_number_to_propose,
            received_1b_packets:s.received_1b_packets,
            highest_seqno_requested_by_client_this_view:s.highest_seqno_requested_by_client_this_view,
            incomplete_batch_timer:s.incomplete_batch_timer,
            election_state:s_.election_state
        }
    }

    pub open spec fn LProposerCheckForQuorumOfViewSuspicions(
        s:LProposer,
        s_:LProposer,
        clock:int
    ) -> bool
    {
        &&& ElectionStateCheckForQuorumOfViewSuspicions(s.election_state, s_.election_state, clock)
        &&& (if BalLt(s.election_state.current_view, s_.election_state.current_view) {
                s_.current_state == 0 && s_.request_queue == Seq::<Request>::empty()
            } else {
                s_.current_state == s.current_state && s_.request_queue == s.request_queue
            })
        &&& s_ == LProposer{
            constants:s.constants,
            current_state:s_.current_state,
            request_queue:s_.request_queue,
            max_ballot_i_sent_1a:s.max_ballot_i_sent_1a,
            next_operation_number_to_propose:s.next_operation_number_to_propose,
            received_1b_packets:s.received_1b_packets,
            highest_seqno_requested_by_client_this_view:s.highest_seqno_requested_by_client_this_view,
            incomplete_batch_timer:s.incomplete_batch_timer,
            election_state:s_.election_state
        }
    }

    pub open spec fn LProposerResetViewTimerDueToExecution(
        s:LProposer,
        s_:LProposer,
        val:RequestBatch
    ) -> bool
    {
        &&& ElectionStateReflectExecutedRequestBatch(s.election_state, s_.election_state, val)
        &&& s_ == LProposer{
            constants:s.constants,
            current_state:s.current_state,
            request_queue:s.request_queue,
            max_ballot_i_sent_1a:s.max_ballot_i_sent_1a,
            next_operation_number_to_propose:s.next_operation_number_to_propose,
            received_1b_packets:s.received_1b_packets,
            highest_seqno_requested_by_client_this_view:s.highest_seqno_requested_by_client_this_view,
            incomplete_batch_timer:s.incomplete_batch_timer,
            election_state:s_.election_state
        }
    }


    /*
    s_ == LProposer{
        constants:s.constants,
        current_state:s.current_state,
        request_queue:s.request_queue,
        max_ballot_i_sent_1a:s.max_ballot_i_sent_1a,
        next_operation_number_to_propose:s.next_operation_number_to_propose,
        received_1b_packets:s.received_1b_packets,
        highest_seqno_requested_by_client_this_view:s.highest_seqno_requested_by_client_this_view,
        incomplete_batch_timer:s.incomplete_batch_timer,
        election_state:s.election_state
    }
    */


}
