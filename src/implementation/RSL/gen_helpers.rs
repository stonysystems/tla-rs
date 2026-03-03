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
use crate::protocol::RSL::environment::{RslIo, RslPacket};
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

/// Snoc lemma: ExtractSentPacketsFromIos distributes over push.
/// Extract(s.push(x)) == Extract(s) ++ [x->s]  if x is Send
/// Extract(s.push(x)) == Extract(s)             otherwise
proof fn lemma_ExtractSentPacketsFromIos_snoc(s: Seq<RslIo>, x: RslIo)
    ensures
        ExtractSentPacketsFromIos(s.push(x)) =~=
            if x is Send { ExtractSentPacketsFromIos(s).push(x->s) }
            else { ExtractSentPacketsFromIos(s) }
    decreases s.len()
{
    let sx = s.push(x);
    let target = if x is Send { ExtractSentPacketsFromIos(s).push(x->s) }
                 else { ExtractSentPacketsFromIos(s) };

    if s.len() == 0 {
        // s.push(x) = seq![x], len 1
        assert(sx.len() == 1);
        assert(sx[0] == x);
        assert(sx.drop_first().len() == 0);
        assert(ExtractSentPacketsFromIos(sx.drop_first()) =~= Seq::<RslPacket>::empty());
        assert(ExtractSentPacketsFromIos(s) =~= Seq::<RslPacket>::empty());
        if x is Send {
            // Extract(seq![x]) = seq![x->s] + Extract(empty) = seq![x->s]
            // target = Extract(empty).push(x->s) = empty.push(x->s) = seq![x->s]
        }
    } else {
        lemma_ExtractSentPacketsFromIos_snoc(s.drop_first(), x);
        // IH: Extract(s.drop_first().push(x)) =~= target_rest
        // where target_rest = if x is Send: Extract(s.drop_first()).push(x->s)
        //                     else: Extract(s.drop_first())

        // Key identity: sx.drop_first() == s.drop_first().push(x)
        assert(sx.drop_first() =~= s.drop_first().push(x));
        assert(sx[0] == s[0]);

        let extract_df_x = ExtractSentPacketsFromIos(s.drop_first().push(x));
        let extract_df = ExtractSentPacketsFromIos(s.drop_first());

        if s[0] is Send {
            // Extract(sx) = seq![s[0]->s] + Extract(sx.drop_first())
            // Extract(s) = seq![s[0]->s] + extract_df
            let head = seq![s[0]->s];
            if x is Send {
                // IH: extract_df_x =~= extract_df.push(x->s)
                //                    = extract_df + seq![x->s]
                assert(extract_df_x =~= extract_df.push(x->s));
                // Assoc: head + (extract_df + seq![x->s])
                //     =~= (head + extract_df) + seq![x->s]
                assert((head + extract_df) + seq![x->s]
                    =~= head + (extract_df + seq![x->s]));
                // Extract(sx) = head + extract_df_x
                //             =~= head + (extract_df + seq![x->s])
                //             =~= (head + extract_df) + seq![x->s]
                //             = Extract(s) + seq![x->s]
                //             = target
                assert(ExtractSentPacketsFromIos(sx) =~= target);
            } else {
                assert(extract_df_x =~= extract_df);
                assert(ExtractSentPacketsFromIos(sx) =~= target);
            }
        } else {
            // Extract(sx) = Extract(sx.drop_first())
            // Extract(s) = extract_df
            if x is Send {
                assert(extract_df_x =~= extract_df.push(x->s));
                assert(ExtractSentPacketsFromIos(sx) =~= target);
            } else {
                assert(extract_df_x =~= extract_df);
                assert(ExtractSentPacketsFromIos(sx) =~= target);
            }
        }
    }
}

/// Convert runtime IO events to sent packets with the exact spec projection.
/// Re-homed from replica_manual.rs to shrink manual_code footprint.
pub exec fn CExtractSentPacketsFromIos(ios: &Vec<CRslIo>) -> (result: Vec<CPacket>)
ensures
    result@.map(|i, p: CPacket| p@) == ExtractSentPacketsFromIos(abstractify_crslio_seq(ios@)),
{
    let mut result: Vec<CPacket> = Vec::new();
    let mut i: usize = 0;
    let ghost abs_ios = abstractify_crslio_seq(ios@);

    while i < ios.len()
        invariant
            0 <= i <= ios.len(),
            abs_ios == abstractify_crslio_seq(ios@),
            result@.map(|j: int, p: CPacket| p@) =~=
                ExtractSentPacketsFromIos(abs_ios.take(i as int)),
        decreases ios.len() - i,
    {
        if let LIoOp::Send{s: pkt_s} = &ios[i] {
            let pkt = CPacket {
                dst: pkt_s.dst.clone_up_to_view(),
                src: pkt_s.src.clone_up_to_view(),
                msg: pkt_s.msg.clone_up_to_view(),
            };
            result.push(pkt);
            proof {
                assert(pkt@ == abstractify_clpacket(*pkt_s));
                assert(abs_ios[i as int] == abstractify_crslio(ios@[i as int]));
                lemma_ExtractSentPacketsFromIos_snoc(
                    abs_ios.take(i as int), abs_ios[i as int]);
                assert(abs_ios.take((i + 1) as int) =~=
                    abs_ios.take(i as int).push(abs_ios[i as int]));
            }
        } else {
            proof {
                assert(abs_ios[i as int] == abstractify_crslio(ios@[i as int]));
                assert(!(abs_ios[i as int] is Send));
                lemma_ExtractSentPacketsFromIos_snoc(
                    abs_ios.take(i as int), abs_ios[i as int]);
                assert(abs_ios.take((i + 1) as int) =~=
                    abs_ios.take(i as int).push(abs_ios[i as int]));
            }
        }
        i = i + 1;
    }

    proof {
        assert(abs_ios.take(ios@.len() as int) =~= abs_ios);
    }

    result
}

/// Shared fallback for processing 1b packets.
/// Re-homed from generated proof-fallback ownership so dispatch wrappers can
/// reference a stable helper without relying on manual_code injection.
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
    // clone_up_to_view: state@ == s@, state.valid() == s.valid()
    let pkt = clone_cpacket_full(received_packet);
    // clone_cpacket_full: pkt == *received_packet, so pkt@ == received_packet@
    let sent = state.CReplicaNextProcess1b(pkt);
    // impl ensures: state.valid(), sent.valid(),
    //   LReplicaNextProcess1b(old(state)@ == s@, state@, pkt@ == received_packet@, sent@)
    let packets = outbound_packets_to_vec(sent);
    // outbound_packets_to_vec: packets@.map(|i, p| p@) =~= sent@
    (state, packets)
}

/// Shared fallback for spontaneous truncate-log action.
/// Re-homed from generated ownership so no_receive dispatch can resolve it
/// without relying on manual_code-injected local definitions.
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
    // clone_up_to_view: state@ == s@, state.valid() == s.valid()
    let sent = state.CReplicaNextSpontaneousTruncateLogBasedOnCheckpoints();
    // impl ensures: state.valid(), sent.valid(),
    //   LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(old(state)@ == s@, state@, sent@)
    let packets = outbound_packets_to_vec(sent);
    // outbound_packets_to_vec: packets@.map(|i, p| p@) =~= sent@
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
pub fn outbound_packets_to_vec(sent: OutboundPackets) -> (result: Vec<CPacket>)
    requires
        sent.valid(),
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
                    let mut result: Vec<CPacket> = Vec::new();
                    let mut i: usize = 0;
                    while i < dsts.len()
                        invariant
                            0 <= i <= dsts.len(),
                            result.len() == i,
                            src.valid_public_key(),
                            src.abstractable(),
                            msg.valid(),
                            msg.abstractable(),
                            forall |j: int| 0 <= j < dsts.len() ==> (#[trigger] dsts@[j]).valid_public_key(),
                            forall |j: int| 0 <= j < dsts.len() ==> (#[trigger] dsts@[j]).abstractable(),
                            forall |j: int| 0 <= j < i ==> (#[trigger] result@[j]).valid(),
                            forall |j: int| 0 <= j < i ==> (#[trigger] result@[j]).abstractable(),
                            forall |j: int| 0 <= j < i ==> (#[trigger] result@[j])@ =~= (LPacket { dst: dsts@[j]@, src: src@, msg: msg@ }),
                        decreases dsts.len() - i,
                    {
                        let pkt = CPacket {
                            dst: dsts[i].clone_up_to_view(),
                            src: src.clone_up_to_view(),
                            msg: msg.clone_up_to_view(),
                        };
                        result.push(pkt);
                        i += 1;
                    }
                    proof {
                        lemma_BuildBroadcast_ensures(src@, dsts@.map(|i: int, e: EndPoint| e@), msg@);
                    }
                    result
                },
                CBroadcast::CBroadcastNop {} => Vec::new(),
            }
        },
        OutboundPackets::OutboundPacket { p } => {
            match p {
                Some(pkt) => {
                    let mut v: Vec<CPacket> = Vec::new();
                    v.push(pkt);
                    v
                },
                None => Vec::new(),
            }
        },
    }
}

} // verus!
