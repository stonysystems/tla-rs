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
use crate::common::native::io_s::{AbstractEndPoint, EndPoint};
use crate::generated::RSL::types_gen::*;
use crate::implementation::RSL::cmessage::*;
use crate::implementation::RSL::types_i::abstractify_creplycache;
use crate::protocol::RSL::environment::{RslIo, RslPacket};
use crate::protocol::RSL::executor::{GetPacketsFromReplies, LClientsInReplies, UpdateNewCache};
use crate::protocol::RSL::types::Reply;
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
/// Iterates back-to-front to match spec's recursive first-wins semantics:
/// LClientsInReplies(replies) = LClientsInReplies(replies.drop_first()).insert(replies[0].client, replies[0])
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
    broadcast use crate::common::native::io_s::axiom_endpoint_view;

    let ghost abs_replies = replies@.map(|i: int, r: CReply| r@);
    let ghost len = abs_replies.len() as int;

    let mut result: HashMap<EndPoint, CReply> = HashMap::new();
    let mut i: usize = replies.len();

    while i > 0
        invariant
            0 <= i <= replies.len(),
            // Validity: keys abstractable, values abstractable+valid
            creplycache_is_valid(&result),
            // Abstract equality with spec function on the suffix
            abstractify_creplycache(&result) =~= LClientsInReplies(abs_replies.subrange(i as int, len)),
            // Preserved
            forall |j: int| 0 <= j < replies.len() ==> (#[trigger] replies@[j]).valid(),
            abs_replies == replies@.map(|i: int, r: CReply| r@),
            len == abs_replies.len(),
        decreases i,
    {
        i = i - 1;
        let ghost old_map = result@;
        let ghost old_abstract = abstractify_creplycache(&result);

        let k = replies[i].client.clone_eq();
        let v = replies[i].clone_up_to_view();

        proof {
            // Broadcast axioms must be re-stated inside loop body
            broadcast use vstd::std_specs::hash::group_hash_axioms;
            broadcast use vstd::hash_map::group_hash_map_axioms;
            broadcast use crate::common::native::io_s::axiom_endpoint_key_model;
            broadcast use crate::common::native::io_s::axiom_endpoint_view;
            assert(k == replies@[i as int].client);
            assert(v == replies@[i as int]);
            assert(v@ == replies@[i as int]@);
            // Establish pointwise equality: abs_replies[j] == replies@[j]@ for valid j
            assert forall |j: int| 0 <= j < replies@.len() as int implies
                abs_replies[j] == (#[trigger] replies@[j])@
            by {};
            assert(abs_replies[i as int] == v@);
        }

        let _ = result.insert(k, v);

        proof {
            broadcast use vstd::std_specs::hash::group_hash_axioms;
            broadcast use vstd::hash_map::group_hash_map_axioms;
            broadcast use vstd::map::group_map_axioms;
            broadcast use crate::common::native::io_s::axiom_endpoint_key_model;
            broadcast use crate::common::native::io_s::axiom_endpoint_view;

            // Establish HashMap insert postcondition explicitly
            assert(result@ =~= old_map.insert(k, v));
            assert(result@.contains_key(k));
            assert(result@[k] == v);
            assert(forall |e: EndPoint| e != k ==> (result@.contains_key(e) == old_map.contains_key(e)));
            assert(forall |e: EndPoint| e != k && old_map.contains_key(e) ==> result@[e] == old_map[e]);

            // Step 1: Relate LClientsInReplies recursion
            let sub_i = abs_replies.subrange(i as int, len);
            let sub_i1 = abs_replies.subrange(i as int + 1, len);
            assert(sub_i.len() > 0);
            assert(sub_i.drop_first() =~= sub_i1);
            assert(sub_i[0] == abs_replies[i as int]);

            // Step 2: Show abstractify_creplycache(&result) =~= old_abstract.insert(k@, v@)
            let new_abstract = abstractify_creplycache(&result);
            let target = old_abstract.insert(k@, v@);

            // Domain forward: new_abstract.dom ⊆ target.dom
            assert forall |ak: AbstractEndPoint|
                new_abstract.dom().contains(ak) implies target.dom().contains(ak)
            by {
                broadcast use crate::common::native::io_s::axiom_endpoint_view;
                broadcast use vstd::map::group_map_axioms;
                // Unfold: new_abstract.dom().contains(ak) means exists ep in result@ with ep@ == ak
                assert(exists |ep: EndPoint| result@.contains_key(ep) && ep@ == ak);
                let ep = choose |ep: EndPoint| result@.contains_key(ep) && ep@ == ak;
                if ep == k {
                    // ak == k@ → target contains k@
                } else {
                    // ep in result@ and ep != k → ep in old_map → old_abstract.dom().contains(ak)
                    assert(old_map.contains_key(ep));
                }
            };

            // Domain backward: target.dom ⊆ new_abstract.dom
            assert forall |ak: AbstractEndPoint|
                target.dom().contains(ak) implies new_abstract.dom().contains(ak)
            by {
                broadcast use crate::common::native::io_s::axiom_endpoint_view;
                broadcast use vstd::map::group_map_axioms;
                if ak == k@ {
                    // Witness: k is in result@ and k@ == ak
                    assert(result@.contains_key(k) && k@ == ak);
                } else {
                    // ak in old_abstract.dom() → exists ep in old_map with ep@ == ak
                    assert(old_abstract.dom().contains(ak));
                    assert(exists |ep: EndPoint| old_map.contains_key(ep) && ep@ == ak);
                    let ep = choose |ep: EndPoint| old_map.contains_key(ep) && ep@ == ak;
                    assert(ep != k);
                    assert(result@.contains_key(ep));
                    assert(result@.contains_key(ep) && ep@ == ak);
                }
            };

            // Values match
            assert forall |ak: AbstractEndPoint|
                new_abstract.dom().contains(ak) implies new_abstract[ak] == target[ak]
            by {
                broadcast use crate::common::native::io_s::axiom_endpoint_view;
                broadcast use vstd::map::group_map_axioms;
                assert(exists |ep: EndPoint| result@.contains_key(ep) && ep@ == ak);
                let ep_new = choose |ep: EndPoint| result@.contains_key(ep) && ep@ == ak;
                if ak == k@ {
                    assert(ep_new == k);
                } else {
                    assert(ep_new != k);
                    assert(result@[ep_new] == old_map[ep_new]);
                }
            };

            // Combine: new_abstract =~= target
            assert(new_abstract =~= target);

            // Bridge: sub_i[0] == v@ and v@.client == k@
            // abs_replies[i] == v@ was established in the pre-insert proof block
            assert(sub_i[0] == v@);
            assert(v@.client == k@);
            // By IH: old_abstract =~= LClientsInReplies(sub_i1)
            // target = old_abstract.insert(k@, v@) = LClientsInReplies(sub_i1).insert(sub_i[0].client, sub_i[0])
            // = LClientsInReplies(sub_i)

            // Maintain creplycache_is_valid
            assert(v.valid());
            assert(k.abstractable());
        }
    }

    // Post-loop: i == 0, subrange(0, len) == abs_replies
    proof {
        assert(abs_replies.subrange(0int, len) =~= abs_replies);

        // creplycache_is_valid: abstractable + valid for all entries
        assert forall |e: EndPoint| result@.contains_key(e) implies
            e.abstractable() && (#[trigger] result@[e]).abstractable()
        by {
            // result@[e].valid() from invariant, valid ==> abstractable
        };
    }
    result
}

/// Helper lemma: if LClientsInReplies(replies) contains a client,
/// then some reply has that client and LClientsInReplies maps to it.
proof fn lemma_clients_in_replies_witness(replies: Seq<Reply>, client: AbstractEndPoint)
    requires LClientsInReplies(replies).contains_key(client),
    ensures exists |idx: int| 0 <= idx < replies.len()
        && replies[idx].client == client
        && LClientsInReplies(replies)[client] == replies[idx],
    decreases replies.len(),
{
    if replies.len() == 0 {
        // Map::empty has no keys — contradicts requires
    } else {
        let rest = LClientsInReplies(replies.drop_first());
        let merged = rest.insert(replies[0].client, replies[0]);
        // LClientsInReplies(replies) == merged
        if replies[0].client == client {
            // replies[0] is the witness at index 0
            assert(merged[client] == replies[0]);
        } else {
            // client must be in rest (insert of different key doesn't add client)
            assert(rest.contains_key(client));
            lemma_clients_in_replies_witness(replies.drop_first(), client);
            let idx = choose |idx: int| 0 <= idx < replies.drop_first().len()
                && replies.drop_first()[idx].client == client
                && LClientsInReplies(replies.drop_first())[client] == replies.drop_first()[idx];
            // drop_first()[idx] == replies[idx + 1]
            assert(replies[idx + 1].client == client);
            // merged[client] == rest[client] (insert of different key)
            assert(merged[client] == rest[client]);
            assert(rest[client] == replies.drop_first()[idx]);
            assert(merged[client] == replies[idx + 1]);
        }
    }
}

/// Merge new replies into an existing reply cache.
/// Clones nc (from replies), then inserts c's entries on top (c takes priority per spec).
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
    broadcast use vstd::std_specs::hash::group_hash_axioms;
    broadcast use vstd::hash_map::group_hash_map_axioms;
    broadcast use crate::common::native::io_s::axiom_endpoint_key_model;
    broadcast use crate::common::native::io_s::axiom_endpoint_view;

    // Step 1: Build nc from replies (verified)
    let nc = CClientsInReplies(replies);
    let ghost abs_nc = abstractify_creplycache(&nc);
    let ghost abs_c = abstractify_creplycache(c);
    let ghost abs_replies = replies@.map(|i, x: CReply| x@);

    // Step 2: Clone nc into result
    let mut result = clone_creply_cache_up_to_view(&nc);
    // result@ == nc@

    // Step 3: Insert all entries from c (overwrites nc where both have same key)
    let c_keys = crate::common::collections::hashsets::hashmap_keys_to_vec(c);
    let mut j: usize = 0;
    while j < c_keys.len()
        invariant
            0 <= j <= c_keys.len(),
            // All nc keys are in result (never removed)
            forall |ep: EndPoint| nc@.contains_key(ep) ==> result@.contains_key(ep),
            // Processed c keys are in result with c's values
            forall |idx: int| 0 <= idx < j as int ==>
                result@.contains_key(#[trigger] c_keys@[idx])
                && result@[c_keys@[idx]] == c@[c_keys@[idx]],
            // Domain: result only has nc keys and processed c keys
            forall |ep: EndPoint| result@.contains_key(ep) ==>
                nc@.contains_key(ep)
                || (exists |idx: int| 0 <= idx < j as int && c_keys@[idx] == ep),
            // nc-only keys (not in c) still have nc's values
            forall |ep: EndPoint| nc@.contains_key(ep) && !c@.contains_key(ep)
                ==> result@[ep] == nc@[ep],
            // Validity
            creplycache_is_valid(&result),
            // Preserved postconditions
            forall |k: int| 0 <= k < c_keys@.len() ==> c@.contains_key(#[trigger] c_keys@[k]),
            forall |k: EndPoint| c@.contains_key(k) ==> (exists |idx: int| 0 <= idx < c_keys@.len() && c_keys@[idx] == k),
            creplycache_is_valid(c),
            creplycache_is_valid(&nc),
            abs_nc == abstractify_creplycache(&nc),
            abs_c == abstractify_creplycache(c),
        decreases c_keys.len() - j,
    {
        let ghost old_result = result@;

        proof {
            broadcast use vstd::std_specs::hash::group_hash_axioms;
            broadcast use vstd::hash_map::group_hash_map_axioms;
            broadcast use crate::common::native::io_s::axiom_endpoint_key_model;
            broadcast use crate::common::native::io_s::axiom_endpoint_view;
            assert(c@.contains_key(c_keys@[j as int]));
        }

        let k = c_keys[j].clone_eq();
        let v = c.get(&c_keys[j]).unwrap().clone_up_to_view();
        let _ = result.insert(k, v);

        proof {
            broadcast use vstd::std_specs::hash::group_hash_axioms;
            broadcast use vstd::hash_map::group_hash_map_axioms;
            broadcast use vstd::map::group_map_axioms;
            broadcast use crate::common::native::io_s::axiom_endpoint_key_model;
            broadcast use crate::common::native::io_s::axiom_endpoint_view;

            assert(k == c_keys@[j as int]);
            assert(v == c@[k]);
            assert(result@ =~= old_result.insert(k, v));

            // Processed c keys maintain values (including the new one)
            assert forall |idx: int| 0 <= idx < j as int + 1 implies
                result@.contains_key(#[trigger] c_keys@[idx])
                && result@[c_keys@[idx]] == c@[c_keys@[idx]]
            by {
                if idx == j as int {
                    assert(result@.contains_key(k));
                    assert(result@[k] == v);
                    assert(v == c@[k]);
                } else {
                    // Previous c keys: unchanged unless k == c_keys@[idx]
                    if c_keys@[idx] == k {
                        // Same key, just overwritten with same value
                        assert(result@[k] == v);
                        assert(c@[c_keys@[idx]] == c@[k]);
                    } else {
                        assert(result@[c_keys@[idx]] == old_result[c_keys@[idx]]);
                    }
                }
            };

            // nc-only keys still have nc's values
            assert forall |ep: EndPoint| nc@.contains_key(ep) && !c@.contains_key(ep)
                implies result@[ep] == nc@[ep]
            by {
                // ep is not in c, k IS in c, so ep != k
                assert(c@.contains_key(k));
                assert(!c@.contains_key(ep));
                assert(ep != k);
                assert(result@[ep] == old_result[ep]);
            };

            // Validity: new entry valid because c is valid
            assert forall |ep: EndPoint| result@.contains_key(ep) implies
                ep.abstractable() && (#[trigger] result@[ep]).abstractable() && result@[ep].valid()
            by {
                if ep == k {
                    assert(c@.contains_key(k));
                    // creplycache_is_valid(c) gives c@[k].valid() and k.abstractable()
                } else {
                    assert(old_result.contains_key(ep));
                }
            };
        }
        j = j + 1;
    }

    // Post-loop proof: establish UpdateNewCache
    //
    // Key insight: Verus encodes ghost `let` bindings as separate SMT constants,
    // so proved foralls using ghost variables don't trigger-match the postcondition
    // which uses raw expressions. We use `abs_replies` (defined at exec-level before
    // the loop) consistently. The postcondition unfolds with `replies@.map(...)` —
    // Verus should equate this with `abs_replies` from the exec-level ghost binding.
    proof {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        broadcast use vstd::hash_map::group_hash_map_axioms;
        broadcast use vstd::map::group_map_axioms;
        broadcast use crate::common::native::io_s::axiom_endpoint_key_model;
        broadcast use crate::common::native::io_s::axiom_endpoint_view;

        // First establish: all c keys are in result
        assert forall |ep: EndPoint| c@.contains_key(ep) implies result@.contains_key(ep) by {
            let idx = choose |idx: int| 0 <= idx < c_keys@.len() && c_keys@[idx] == ep;
            assert(result@.contains_key(c_keys@[idx]));
        };

        // Concrete domain: result has exactly nc ∪ c keys
        assert forall |ep: EndPoint| result@.contains_key(ep) <==>
            (nc@.contains_key(ep) || c@.contains_key(ep)) by {};

        // Concrete values: c keys get c's values
        assert forall |ep: EndPoint| result@.contains_key(ep) && c@.contains_key(ep)
            implies result@[ep] == c@[ep] by {
            let idx = choose |idx: int| 0 <= idx < c_keys@.len() && c_keys@[idx] == ep;
        };

        // Bridge between concrete and abstract
        assert(abstractify_creplycache(&nc) == abs_nc);
        assert(abs_nc == LClientsInReplies(abs_replies));

        // Pre-prove: for all clients in nc, a witness reply exists
        assert forall |client: AbstractEndPoint|
            LClientsInReplies(abs_replies).contains_key(client) implies
            (exists |idx: int| 0 <= idx < abs_replies.len()
                && (#[trigger] abs_replies[idx]).client == client
                && LClientsInReplies(abs_replies)[client] == abs_replies[idx])
        by {
            lemma_clients_in_replies_witness(abs_replies, client);
        };

        // Now prove all 4 conjuncts using abs_replies (exec-level ghost variable)
        // Conjunct 1: existential witness
        assert forall |client: AbstractEndPoint|
            abstractify_creplycache(&result).contains_key(client) implies
            (abstractify_creplycache(c).contains_key(client) && abstractify_creplycache(&result)[client] == abstractify_creplycache(c)[client])
            || (exists |req_idx: int| 0 <= req_idx < abs_replies.len()
                && (#[trigger] abs_replies[req_idx]).client == client
                && abstractify_creplycache(&result)[client] == abs_replies[req_idx])
        by {
            assert(exists |ep: EndPoint| result@.contains_key(ep) && ep@ == client);
            let ep_r = choose |ep: EndPoint| result@.contains_key(ep) && ep@ == client;
            if c@.contains_key(ep_r) {
                assert(result@[ep_r] == c@[ep_r]);
                assert(abstractify_creplycache(c).contains_key(client));
            } else {
                assert(nc@.contains_key(ep_r));
                assert(abstractify_creplycache(&nc).contains_key(client));
                assert(LClientsInReplies(abs_replies).contains_key(client));
                // Witness exists from the pre-proved forall above
            }
        };

        // Conjunct 2: domain
        assert forall |client: AbstractEndPoint|
            abstractify_creplycache(&result).contains_key(client) <==>
            (LClientsInReplies(abs_replies).contains_key(client) || abstractify_creplycache(c).contains_key(client))
        by {
            if abstractify_creplycache(&result).contains_key(client) {
                assert(exists |ep: EndPoint| result@.contains_key(ep) && ep@ == client);
                let ep = choose |ep: EndPoint| result@.contains_key(ep) && ep@ == client;
                if nc@.contains_key(ep) {
                    assert(exists |ep2: EndPoint| nc@.contains_key(ep2) && ep2@ == client);
                    assert(abstractify_creplycache(&nc).contains_key(client));
                } else {
                    assert(c@.contains_key(ep));
                    assert(exists |ep2: EndPoint| c@.contains_key(ep2) && ep2@ == client);
                    assert(abstractify_creplycache(c).contains_key(client));
                }
            }
            if LClientsInReplies(abs_replies).contains_key(client) || abstractify_creplycache(c).contains_key(client) {
                if LClientsInReplies(abs_replies).contains_key(client) {
                    assert(abstractify_creplycache(&nc).contains_key(client));
                    assert(exists |ep: EndPoint| nc@.contains_key(ep) && ep@ == client);
                    let ep = choose |ep: EndPoint| nc@.contains_key(ep) && ep@ == client;
                    assert(result@.contains_key(ep));
                    assert(exists |ep2: EndPoint| result@.contains_key(ep2) && ep2@ == client);
                }
                if abstractify_creplycache(c).contains_key(client) {
                    assert(exists |ep: EndPoint| c@.contains_key(ep) && ep@ == client);
                    let ep = choose |ep: EndPoint| c@.contains_key(ep) && ep@ == client;
                    assert(result@.contains_key(ep));
                    assert(exists |ep2: EndPoint| result@.contains_key(ep2) && ep2@ == client);
                }
            }
        };

        // Conjunct 3: values
        assert forall |client: AbstractEndPoint|
            abstractify_creplycache(&result).contains_key(client) implies
            abstractify_creplycache(&result)[client] == if abstractify_creplycache(c).contains_key(client) { abstractify_creplycache(c)[client] } else { LClientsInReplies(abs_replies)[client] }
        by {
            assert(exists |ep: EndPoint| result@.contains_key(ep) && ep@ == client);
            let ep_r = choose |ep: EndPoint| result@.contains_key(ep) && ep@ == client;
            if abstractify_creplycache(c).contains_key(client) {
                assert(exists |ep: EndPoint| c@.contains_key(ep) && ep@ == client);
                let ep_c = choose |ep: EndPoint| c@.contains_key(ep) && ep@ == client;
                assert(ep_c == ep_r);
                assert(c@.contains_key(ep_r));
                assert(result@[ep_r] == c@[ep_r]);
            } else {
                assert(!c@.contains_key(ep_r));
                assert(nc@.contains_key(ep_r));
                assert(result@[ep_r] == nc@[ep_r]);
            }
        };

        // Conjunct 4: reverse direction
        assert forall |client: AbstractEndPoint|
            (LClientsInReplies(abs_replies).contains_key(client) || abstractify_creplycache(c).contains_key(client)) implies
            abstractify_creplycache(&result).contains_key(client)
            && abstractify_creplycache(&result)[client] == if abstractify_creplycache(c).contains_key(client) { abstractify_creplycache(c)[client] } else { LClientsInReplies(abs_replies)[client] }
        by {};
    }
    result
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
