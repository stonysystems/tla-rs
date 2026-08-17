/// Distributed state for EPaxos*: N replicas plus a network.
///
/// `epaxos_star.rs` is a single replica; `Agreement` and `Visibility` both
/// quantify over **two** replicas, so they have nowhere to live without this
/// layer. Structurally this follows `Raft/refinement_proof/state_machine.rs`,
/// which is the only other protocol in the tree that has one.
///
/// # Two deliberate differences from the reference, both stated rather than
/// # discovered later
///
/// **The network is monotone: receipt does not consume.** The reference writes
/// `msgs' = (msgs \ {m}) \cup ...` and so delivers each message once. Here a
/// delivered packet stays in `network`, which admits *more* behaviours —
/// re-delivery — and is therefore a sound over-approximation for safety: an
/// invariant that holds here holds under exactly-once delivery too. Re-delivery
/// is not interesting in practice because the handlers are either idempotent or
/// blocked by their own guards on the second pass (`LHandlePreAccept` requires
/// `phase is Initial`, the `LRecord*` actions require the sender to be absent
/// from their accumulator). Raft's model makes the same choice for the same
/// reason. It is *not* free for liveness, which is out of scope here.
///
/// **`LNext` and `ReplicaAction` are separate.** `LNext` hides each action's
/// received packet inside an existential, which is exactly what this layer must
/// not allow — a replica could then "receive" a packet that was never sent.
/// `ReplicaAction` exposes it so the receive guard can pin it to `network`.
/// This is the whole reason the layer exists, and it is what closes the defect
/// class found in `src/protocol/EPaxos/`, where `pa_sender: int` is a free
/// integer and a leader assembles a quorum from senders that do not exist.
use crate::protocol::EPaxosStar::epaxos_star::*;
use crate::protocol::EPaxosStar::types::*;
use vstd::prelude::*;

verus! {

/// One replica's step, with the packet it consumed made explicit.
///
/// `received` is `Some` for the ten message handlers and the two
/// `PostWaiting` branches that read the network, `None` for the steps a replica
/// takes on its own behalf.
pub open spec fn ReplicaAction(
    s: LState,
    s_: LState,
    c: LConstants,
    received: Option<LPacket>,
    sent: Set<LPacket>,
) -> bool {
    match received {
        Option::Some(pkt) => {
            ||| LHandlePreAccept(s, s_, c, pkt, sent)
            ||| LRecordPreAcceptOK(s, s_, c, pkt, sent)
            ||| LHandleAccept(s, s_, c, pkt, sent)
            ||| LRecordAcceptOK(s, s_, c, pkt, sent)
            ||| LHandleCommit(s, s_, c, pkt, sent)
            ||| LHandleRecover(s, s_, c, pkt, sent)
            ||| LRecordRecoverOK(s, s_, c, pkt, sent)
            ||| LHandleValidate(s, s_, c, pkt, sent)
            ||| LRecordValidateOK(s, s_, c, pkt, sent)
            ||| exists|id: LInstanceId| LPostWaitingOnWaiting(s, s_, c, id, pkt, sent)
            ||| exists|id: LInstanceId| LPostWaitingOnRecoverOK(s, s_, c, id, pkt, sent)
        },
        Option::None => {
            ||| exists|value: int| LSubmit(s, s_, c, value, sent)
            ||| exists|id: LInstanceId| LCommitFast(s, s_, c, id, sent)
            ||| exists|id: LInstanceId| LStartAccept(s, s_, c, id, sent)
            ||| exists|id: LInstanceId| LCommitSlow(s, s_, c, id, sent)
            ||| exists|id: LInstanceId| LStartRecover(s, s_, c, id, sent)
            ||| exists|id: LInstanceId| LRecoverCommitted(s, s_, c, id, sent)
            ||| exists|id: LInstanceId| LRecoverAccepted(s, s_, c, id, sent)
            ||| exists|id: LInstanceId| LRecoverNop(s, s_, c, id, sent)
            ||| exists|id: LInstanceId| LRecoverValidate(s, s_, c, id, sent)
            ||| exists|id: LInstanceId| LValidateAccept(s, s_, c, id, sent)
            ||| exists|id: LInstanceId| LValidateNop(s, s_, c, id, sent)
            ||| exists|id: LInstanceId| LValidateWait(s, s_, c, id, sent)
            ||| exists|id: LInstanceId| LPostWaitingNop(s, s_, c, id, sent)
            ||| exists|id: LInstanceId| LPostWaitingAccept(s, s_, c, id, sent)
        },
    }
}

pub struct EPaxosStarDistributedState {
    pub replica_states: Seq<LState>,
    pub replica_constants: Seq<LConstants>,
    pub network: Set<LPacket>,
    pub num_replicas: int,
}

/// Every replica agrees on the configuration, and its own identity is its index.
///
/// This is where the quorum sizes get pinned to the replica count. Without it
/// `IsQuorumSized` is a comparison against a number nobody constrained — the
/// defect `src/protocol/EPaxos/`'s `LInit` has, where `quorum_size = 1` is a
/// legal initial state.
pub open spec fn WellFormedDistributed(ds: EPaxosStarDistributedState) -> bool {
    &&& ds.num_replicas > 0
    &&& ds.replica_states.len() == ds.num_replicas
    &&& ds.replica_constants.len() == ds.num_replicas
    &&& forall|i: int|
        0 <= i < ds.num_replicas ==> {
            let ci = #[trigger] ds.replica_constants[i];
            &&& WellFormedConstants(ci)
            &&& ci.my_id == i
            &&& ci.procs =~= Set::<int>::range(0, ds.num_replicas)
            &&& ci.f == ds.replica_constants[0].f
            &&& ci.e == ds.replica_constants[0].e
            &&& ci.max_num == ds.replica_constants[0].max_num
            &&& ci.max_recovery_attempts == ds.replica_constants[0].max_recovery_attempts
            &&& ci.conflict_pairs =~= ds.replica_constants[0].conflict_pairs
        }
}

pub open spec fn EPaxosStarDistributedInit(ds: EPaxosStarDistributedState) -> bool {
    &&& WellFormedDistributed(ds)
    &&& forall|i: int|
        0 <= i < ds.num_replicas ==> LInit(
            #[trigger] ds.replica_states[i],
            ds.replica_constants[i],
        )
    &&& ds.network =~= Set::<LPacket>::empty()
}

/// Replica `i` steps: it may consume only a packet addressed to it that is
/// actually in the network, every packet it emits is stamped with its own id,
/// the network grows by exactly what it emitted, and no other replica moves.
pub open spec fn ReplicaStepWithNetwork(
    ds: EPaxosStarDistributedState,
    ds_: EPaxosStarDistributedState,
    i: int,
) -> bool {
    &&& 0 <= i < ds.num_replicas
    &&& ds_.num_replicas == ds.num_replicas
    &&& ds_.replica_constants =~= ds.replica_constants
    &&& ds_.replica_states.len() == ds.replica_states.len()
    &&& forall|j: int|
        0 <= j < ds.num_replicas && j != i ==> (#[trigger] ds_.replica_states[j])
            == ds.replica_states[j]
    &&& exists|received: Option<LPacket>, sent: Set<LPacket>|
        {
            &&& #[trigger] ReplicaAction(
                ds.replica_states[i],
                ds_.replica_states[i],
                ds.replica_constants[i],
                received,
                sent,
            )
            &&& received matches Option::Some(pkt) ==> ds.network.contains(pkt) && pkt.dst == i
            &&& forall|p: LPacket| (#[trigger] sent.contains(p)) ==> p.src == i
            &&& ds_.network =~= ds.network.union(sent)
        }
}

pub open spec fn EPaxosStarDistributedNext(
    ds: EPaxosStarDistributedState,
    ds_: EPaxosStarDistributedState,
) -> bool {
    exists|i: int| #[trigger] ReplicaStepWithNetwork(ds, ds_, i)
}

/// A behaviour: an initial state followed by valid steps.
pub type EPaxosStarBehavior = Seq<EPaxosStarDistributedState>;

pub open spec fn IsValidEPaxosStarBehavior(b: EPaxosStarBehavior) -> bool {
    &&& b.len() > 0
    &&& EPaxosStarDistributedInit(b[0])
    &&& forall|i: int|
        0 <= i < b.len() - 1 ==> EPaxosStarDistributedNext(#[trigger] b[i], b[i + 1])
}

} // verus!
