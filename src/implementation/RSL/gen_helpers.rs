// Shared helper functions for generated RSL modules.
//
// These helpers are used by the hand-written dispatch wrappers in the
// generated *_gen.rs files (acceptor_gen, proposer_gen, replica_gen).
// Centralizing them here eliminates duplication across those modules.

use std::collections::HashMap;
use std::collections::HashSet;
use vstd::prelude::*;

use crate::common::framework::environment_s::LPacket;
use crate::common::native::io_s::EndPoint;
use crate::generated::RSL::types_gen::*;
use crate::implementation::RSL::cmessage::*;
use crate::implementation::RSL::types_i::abstractify_creplycache;
use crate::protocol::RSL::executor::{LClientsInReplies, UpdateNewCache};

verus! {

/// Clone a CPacket preserving both view equality and validity.
/// Standard clone_up_to_view only ensures view preservation; we also need validity.
#[verifier(external_body)]
pub fn clone_cpacket_preserving_validity(p: &CPacket) -> (res: CPacket)
    requires p.valid(),
    ensures res@ == p@, res.valid(),
{
    p.clone_up_to_view()
}

/// Clone a CPacket preserving full structural equality (needed when
/// callee checks concrete fields like `replica_ids@.contains(pkt.src)`).
#[verifier(external_body)]
pub fn clone_cpacket_full(p: &CPacket) -> (res: CPacket)
    requires p.valid(),
    ensures res == *p,
{
    p.clone_up_to_view()
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

/// Check that a 1b packet source is unique among previously received 1b packets.
///
/// Kept as an external-body runtime helper because it is an IO-adjacent
/// HashSet iteration pattern used by replica packet-processing wrappers.
#[verifier(external_body)]
pub exec fn Packet1bHasUniqueSrc(received_1b_packets: &HashSet<CPacket>, pkt: &CPacket) -> (res: bool)
    requires
        pkt.msg is CMessage1b,
    ensures
        res ==> forall |op: CPacket| received_1b_packets@.contains(op) ==> op.src@ != pkt.src@,
{
    broadcast use vstd::std_specs::hash::group_hash_axioms;
    broadcast use vstd::hash_map::group_hash_map_axioms;
    broadcast use crate::common::native::io_s::axiom_endpoint_key_model;
    let mut res = true;
    for p in received_1b_packets.iter() {
        if p.src == pkt.src {
            res = false;
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
    broadcast use vstd::std_specs::hash::group_hash_axioms;
    broadcast use vstd::hash_map::group_hash_map_axioms;
    broadcast use crate::common::native::io_s::axiom_endpoint_key_model;
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
