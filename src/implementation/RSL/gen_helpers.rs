// Shared helper functions for generated RSL modules.
//
// These helpers are used by the hand-written dispatch wrappers in the
// generated *_gen.rs files (acceptor_gen, proposer_gen, replica_gen).
// Centralizing them here eliminates duplication across those modules.

use std::collections::HashMap;
use std::collections::HashSet;
use vstd::prelude::*;

use crate::common::collections::hashsets::hashset_to_vec;
use crate::common::collections::seq_is_unique_v::do_end_points_match;
use crate::common::collections::vecs::*;
use crate::common::framework::environment_s::{LIoOp, LPacket};
use crate::common::native::io_s::EndPoint;
use crate::generated::RSL::types_gen::*;
use crate::implementation::RSL::cmessage::*;
use crate::implementation::RSL::types_i::abstractify_creplycache;
use crate::protocol::RSL::environment::RslPacket;
use crate::protocol::RSL::executor::{GetPacketsFromReplies, LClientsInReplies, UpdateNewCache};
use crate::protocol::RSL::message::RslMessage;
use crate::protocol::RSL::replica::{
    ExtractSentPacketsFromIos, LReplicaNextProcess1b, LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints,
};

verus! {

/// Clone a CPacket preserving both view equality and validity.
/// Verified: CPacket::clone_up_to_view ensures res.valid() == self.valid().
pub fn clone_cpacket_preserving_validity(p: &CPacket) -> (res: CPacket)
    requires p.valid(),
    ensures res@ == p@, res.valid(),
{
    p.clone_up_to_view()
}

/// Clone a CPacket preserving full structural equality (needed when
/// callee checks concrete fields like `replica_ids@.contains(pkt.src)`).
pub fn clone_cpacket_full(p: &CPacket) -> (res: CPacket)
    requires p.valid(),
    ensures res == *p,
{
    let res = p.clone_up_to_view();
    proof {
        broadcast use crate::implementation::RSL::cmessage::axiom_cpacket_view;
        let ghost r = res;
        let ghost q = *p;
        assert(r@ == q@);
        // axiom gives: r@ == q@ ==> r == q
    }
    res
}

/// Clone an LPacket<EndPoint, CMessage> into a CPacket with field equality
/// and validity guarantees. Needed for IO dispatch in replica_gen where packets
/// come from the network layer as LPacket rather than CPacket.
#[verifier(external_body)]
pub fn clone_io_packet(p: &LPacket<EndPoint, CMessage>) -> (res: CPacket)
    ensures
        res.dst == p.dst,
        res.src == p.src,
        res.msg == p.msg,
        res.valid(),
        res.abstractable(),
{
    CPacket { dst: p.dst.clone(), src: p.src.clone(), msg: p.msg.clone() }
}

/// Convert runtime IO events to sent packets with the exact spec projection.
/// Re-homed from replica_manual.rs to shrink manual_code footprint.
#[verifier(external_body)]
pub exec fn CExtractSentPacketsFromIos(ios: &Vec<CRslIo>) -> (result: Vec<CPacket>)
ensures
    result@.map(|i, p: CPacket| p@) == ExtractSentPacketsFromIos(abstractify_crslio_seq(ios@)),
{
    let mut result: Vec<CPacket> = Vec::new();
    let mut i: usize = 0;
    while i < ios.len()
    {
        if let LIoOp::Send{s: pkt_s} = &ios[i] {
            result.push(CPacket {
                dst: pkt_s.dst.clone(),
                src: pkt_s.src.clone(),
                msg: pkt_s.msg.clone(),
            })
        }
        i = i + 1;
    }
    result
}

/// Shared fallback for processing 1b packets.
/// Re-homed from generated proof-fallback ownership so dispatch wrappers can
/// reference a stable helper without relying on manual_code injection.
#[verifier(external_body)]
pub exec fn CReplicaNextProcess1b(s: &CReplica, received_packet: &CPacket) -> (result: (CReplica, Vec<CPacket>))
    requires
        s.valid(),
        received_packet.valid(),
        received_packet.msg is CMessage1b,
    ensures
        result.0.valid(),
        LReplicaNextProcess1b(s@, result.0@, received_packet@, result.1@.map(|i, p: CPacket| p@)),
{
    let mut state = s.clone_up_to_view();
    let pkt = clone_cpacket_full(received_packet);
    let sent = state.CReplicaNextProcess1b(pkt);
    let packets = outbound_packets_to_vec(sent);
    (state, packets)
}

/// Shared fallback for spontaneous truncate-log action.
/// Re-homed from generated ownership so no_receive dispatch can resolve it
/// without relying on manual_code-injected local definitions.
#[verifier(external_body)]
pub exec fn CReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(s: &CReplica) -> (result: (CReplica, Vec<CPacket>))
    requires
        s.valid(),
    ensures
        result.0.valid(),
        LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(
            s@,
            result.0@,
            result.1@.map(|i, p: CPacket| p@),
        ),
{
    let mut state = s.clone_up_to_view();
    let sent = state.CReplicaNextSpontaneousTruncateLogBasedOnCheckpoints();
    let packets = outbound_packets_to_vec(sent);
    (state, packets)
}

/// Check that a 1b packet source is unique among previously received 1b packets.
///
/// Kept as an external-body runtime helper because it is an IO-adjacent
/// HashSet iteration pattern used by replica packet-processing wrappers.
pub exec fn Packet1bHasUniqueSrc(received_1b_packets: &HashSet<CPacket>, pkt: &CPacket) -> (res: bool)
    requires
        pkt.msg is CMessage1b,
    ensures
        res == (forall |op: CPacket| received_1b_packets@.contains(op) ==> op.src@ != pkt.src@),
{
    let vec = hashset_to_vec(received_1b_packets);
    let mut res = true;
    let mut i: usize = 0;
    while i < vec.len()
        invariant
            0 <= i <= vec.len(),
            forall |j: int| 0 <= j < vec@.len() ==> received_1b_packets@.contains(#[trigger] vec@[j]),
            forall |x: CPacket| received_1b_packets@.contains(x) ==> (exists |j: int| 0 <= j < vec@.len() && vec@[j] == x),
            res == (forall |j: int| 0 <= j < i ==> (#[trigger] vec@[j]).src@ != pkt.src@),
        decreases vec.len() - i,
    {
        if do_end_points_match(&vec[i].src, &pkt.src) {
            res = false;
        }
        i += 1;
    }
    proof {
        if res {
            assert forall |op: CPacket| received_1b_packets@.contains(op) implies op.src@ != pkt.src@ by {
                let j = choose |j: int| 0 <= j < vec@.len() && vec@[j] == op;
                assert(vec@[j].src@ != pkt.src@);
            };
        } else {
            let j = choose |j: int| 0 <= j < i && vec@[j].src@ == pkt.src@;
            assert(received_1b_packets@.contains(vec@[j]));
        }
    }
    res
}

/// Build reply cache from a reply list.
/// Kept external-body because HashMap construction/proofs are runtime-backed.
#[verifier(external_body)]
pub exec fn CClientsInReplies(replies: &Vec<CReply>) -> (result: CReplyCache)
    requires
        forall |i: int| 0 <= i < replies.len() ==> replies[i].valid(),
    ensures
        creplycache_is_valid(&result),
        abstractify_creplycache(&result) == LClientsInReplies(replies@.map(|i, r: CReply| r@)),
{
    let mut result: HashMap<EndPoint, CReply> = HashMap::new();
    for reply in replies.iter() {
        result.insert(reply.client.clone(), reply.clone());
    }
    result
}

/// Merge new replies into an existing reply cache.
/// Kept external-body because HashMap iteration/insert is runtime-backed.
#[verifier(external_body)]
pub exec fn CUpdateNewCache(c: &CReplyCache, replies: &Vec<CReply>) -> (c_prime: CReplyCache)
    requires
        creplycache_is_valid(c),
        forall |i: int| 0 <= i < replies.len() ==> replies[i].valid(),
    ensures
        creplycache_is_valid(&c_prime),
        UpdateNewCache(
            abstractify_creplycache(c),
            abstractify_creplycache(&c_prime),
            replies@.map(|i, x: CReply| x@),
        ),
{
    let nc = CClientsInReplies(replies);
    let mut updated_cache = HashMap::<EndPoint, CReply>::new();
    for (k, v) in c.iter() {
        updated_cache.insert(k.clone(), v.clone());
    }
    for (k, v) in nc.iter() {
        updated_cache.insert(k.clone(), v.clone());
    }
    updated_cache
}

/// Build reply packets from paired requests/replies.
/// Kept as a standalone recursive helper to preserve exact decreases/spec relation.
pub exec fn CGetPacketsFromReplies(
    me: &EndPoint,
    requests: &Vec<CRequest>,
    replies: &Vec<CReply>,
) -> (cr: Vec<CPacket>)
    requires
        me.valid_public_key(),
        crequestbatch_is_valid(requests),
        forall |i: int| 0 <= i < requests.len() ==> requests[i].valid(),
        forall |i: int| 0 <= i < replies.len() ==> replies[i].valid(),
        requests.len() == replies.len(),
    ensures
        ({
            let lr = GetPacketsFromReplies(
                me@,
                requests@.map(|i, x: CRequest| x@),
                replies@.map(|i, x: CReply| x@),
            );
            &&& forall |i: int| 0 <= i < cr@.len() ==> cr@[i].valid()
            &&& cr@.map(|i, x: CPacket| x@) == lr
        }),
    decreases requests.len(),
{
    if requests.len() == 0 {
        let res = Vec::new();
        assert(res@.map(|i, p: CPacket| p@) == Seq::<RslPacket>::empty());
        res
    } else {
        let new_req = truncate_vec(&requests, 1, requests.len());
        assert(
            new_req@.map(|i, r: CRequest| r@)
                == requests@.map(|i, r: CRequest| r@).drop_first()
        );
        let new_rep = truncate_vec(&replies, 1, replies.len());
        assert(
            new_rep@.map(|i, r: CReply| r@) == replies@.map(|i, r: CReply| r@).drop_first()
        );
        let rest = CGetPacketsFromReplies(&me, &new_req, &new_rep);
        assert(
            rest@.map(|i, p: CPacket| p@)
                == GetPacketsFromReplies(
                    me@,
                    requests@.map(|i, r: CRequest| r@).drop_first(),
                    replies@.map(|i, r: CReply| r@).drop_first(),
                )
        );
        let pkt = CPacket {
            dst: requests[0].client.clone_up_to_view(),
            src: me.clone_up_to_view(),
            msg: CMessage::CMessageReply {
                seqno_reply: requests[0].seqno,
                reply: replies[0].reply.clone_up_to_view(),
            },
        };
        let ghost spkt = LPacket {
            dst: requests[0].client@,
            src: me@,
            msg: RslMessage::RslMessageReply {
                seqno_reply: requests[0].seqno as int,
                reply: replies[0].reply@,
            },
        };
        assert(pkt@ == spkt);

        let mut first: Vec<CPacket> = Vec::new();
        first.push(pkt);
        assert(first@.map(|i, p: CPacket| p@) == seq![spkt]);

        let res = concat_vecs(&first, &rest);
        assert(
            res@.map(|i, p: CPacket| p@)
                == seq![spkt]
                    + GetPacketsFromReplies(
                        me@,
                        requests@.map(|i, r: CRequest| r@).drop_first(),
                        replies@.map(|i, r: CReply| r@).drop_first(),
                    )
        );

        res
    }
}

/// Convert OutboundPackets (enum with Broadcast/PacketSequence/OutboundPacket variants)
/// to Vec<CPacket> with view-preserving ensures and validity guarantees.
#[verifier(external_body)]
pub fn outbound_packets_to_vec(sent: OutboundPackets) -> (result: Vec<CPacket>)
    ensures
        result@.map(|i: int, p: CPacket| p@) =~= sent@,
        forall |i:int| 0 <= i < result@.len() ==> result@[i].valid(),
        forall |i:int| 0 <= i < result@.len() ==> result@[i].abstractable(),
{
    match sent {
        OutboundPackets::PacketSequence { s } => s,
        OutboundPackets::Broadcast { broadcast } => {
            match broadcast {
                CBroadcast::CBroadcast { src, dsts, msg } => {
                    let mut result = Vec::new();
                    let mut i = 0;
                    while i < dsts.len() {
                        result.push(CPacket {
                            dst: dsts[i].clone(),
                            src: src.clone(),
                            msg: msg.clone(),
                        });
                        i += 1;
                    }
                    result
                },
                CBroadcast::CBroadcastNop {} => Vec::new(),
            }
        },
        OutboundPackets::OutboundPacket { p } => {
            match p {
                Some(pkt) => vec![pkt],
                None => Vec::new(),
            }
        },
    }
}

} // verus!
