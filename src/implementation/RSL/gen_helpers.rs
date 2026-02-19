// Shared helper functions for generated RSL modules.
//
// These helpers are used by the hand-written dispatch wrappers in the
// generated *_gen.rs files (acceptor_gen, proposer_gen, replica_gen).
// Centralizing them here eliminates duplication across those modules.

use vstd::prelude::*;

use crate::common::framework::environment_s::LPacket;
use crate::common::native::io_s::EndPoint;
use crate::generated::RSL::types_gen::*;
use crate::implementation::RSL::cmessage::*;

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
