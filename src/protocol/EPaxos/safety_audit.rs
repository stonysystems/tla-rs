//! Executable-spec audit of the existing simplified EPaxos model.
//!
//! This module constructs counterexamples, not a positive EPaxos safety proof.
//! Its network wrapper calls the existing L* action predicates. Execution
//! histories only observe LExecute; they do not constrain protocol choices.
use crate::protocol::EPaxos::epaxos::*;
use crate::protocol::EPaxos::types::*;
use vstd::prelude::*;

verus! {

pub struct Packet {
    pub src: int,
    pub dst: int,
    pub msg: LEPaxosMessage,
}

pub struct AuditState {
    pub replicas: Seq<LState>,
    /// Append-only sent-packet history permits delay and duplicate delivery.
    pub network: Seq<Packet>,
    /// Actual commands passed through LExecute at each node.
    pub executed: Seq<Seq<int>>,
}

pub enum Action {
    Propose { node: int, command: int },
    Reply { packet: int },
    Collect { packet: int },
    Commit { node: int },
    Execute { node: int },
    NewInstance { node: int },
    Recover { node: int, ballot: int },
}

pub open spec fn constants(node: int) -> LConstants {
    LConstants { num_replicas: 3, quorum_size: 2, fast_quorum_size: 2, my_id: node }
}

pub open spec fn initial_local() -> LState {
    LState {
        ballot: 0, phase: LInstancePhase::Empty, cmd: 0, seq: 0,
        dep_count: 0, is_leader: false, committed_count: 0, executed_count: 0,
        preaccept_senders: Set::empty(), accept_senders: Set::empty(),
        has_conflict: false, max_resp_seq: 0,
    }
}

pub open spec fn initial() -> AuditState {
    AuditState {
        replicas: seq![initial_local(), initial_local(), initial_local()],
        network: Seq::empty(),
        executed: seq![Seq::empty(), Seq::empty(), Seq::empty()],
    }
}

pub open spec fn well_formed(s: AuditState) -> bool {
    s.replicas.len() == 3 && s.executed.len() == 3
}

pub open spec fn actor(s: AuditState, action: Action) -> int {
    match action {
        Action::Propose { node, .. } | Action::Commit { node }
        | Action::Execute { node } | Action::NewInstance { node }
        | Action::Recover { node, .. } => node,
        Action::Reply { packet } | Action::Collect { packet } => s.network[packet].dst,
    }
}

pub open spec fn sent(s: AuditState, action: Action) -> Seq<LEPaxosMessage> {
    let node = actor(s, action);
    let local = s.replicas[node];
    match action {
        Action::Propose { command, .. } => seq![LEPaxosMessage::PreAccept {
            ballot: local.ballot, cmd: command, seq: local.committed_count + 1 }],
        Action::Reply { .. } => seq![LEPaxosMessage::PreAcceptOk {
            sender: node, seq: local.committed_count, conflict: false }],
        Action::Commit { .. } => seq![LEPaxosMessage::Commit { cmd: local.cmd, seq: local.seq }],
        Action::Execute { .. } => seq![LEPaxosMessage::ClientReply { cmd: local.cmd }],
        Action::Recover { ballot, .. } => seq![LEPaxosMessage::PreAccept {
            ballot, cmd: local.cmd, seq: local.seq }],
        _ => Seq::empty(),
    }
}

pub open spec fn broadcast(network: Seq<Packet>, src: int, msg: LEPaxosMessage) -> Seq<Packet> {
    network + Seq::new(2, |i: int| Packet {
        src, dst: if i < src { i } else { i + 1 }, msg,
    })
}

pub open spec fn network_after(s: AuditState, action: Action) -> Seq<Packet> {
    match action {
        Action::Propose { node, .. } | Action::Commit { node }
        | Action::Recover { node, .. } => broadcast(s.network, node, sent(s, action)[0]),
        Action::Reply { packet } => s.network.push(Packet {
            src: s.network[packet].dst, dst: s.network[packet].src, msg: sent(s, action)[0],
        }),
        // Client replies leave the protocol network.
        _ => s.network,
    }
}

pub open spec fn execution_after(s: AuditState, action: Action) -> Seq<Seq<int>> {
    match action {
        Action::Execute { node } => s.executed.update(node,
            s.executed[node].push(s.replicas[node].cmd)),
        _ => s.executed,
    }
}

/// A subset of real source actions suffices for a counterexample. Incoming
/// packets must have been sent, have valid endpoints, and match the handler.
/// Reply uses the host's actual conflict=false and committed_count policy.
pub open spec fn local_action(s: AuditState, s_: AuditState, action: Action) -> bool {
    let node = actor(s, action);
    let local = s.replicas[node];
    let next = s_.replicas[node];
    let c = constants(node);
    let output = sent(s, action);
    match action {
        Action::Propose { command, .. } => LPropose(local, next, c, command, output),
        Action::Reply { packet } => {
            &&& 0 <= packet < s.network.len()
            &&& 0 <= s.network[packet].src < 3
            &&& s.network[packet].msg is PreAccept
            &&& LSendPreAcceptOk(local, next, c, false, local.committed_count, output)
        },
        Action::Collect { packet } => {
            &&& 0 <= packet < s.network.len()
            &&& 0 <= s.network[packet].src < 3
            &&& match s.network[packet].msg {
                LEPaxosMessage::PreAcceptOk { sender, seq, conflict } => {
                    &&& sender == s.network[packet].src
                    &&& LReceivePreAcceptOk(local, next, c, sender, seq, conflict, output)
                },
                _ => false,
            }
        },
        Action::Commit { .. } => LFastCommit(local, next, c, output),
        Action::Execute { .. } => LExecute(local, next, c, output),
        Action::NewInstance { .. } => LNewInstance(local, next, c, output),
        Action::Recover { ballot, .. } => LRecover(local, next, c, ballot, output),
    }
}

#[verifier::opaque]
pub open spec fn step(s: AuditState, s_: AuditState, action: Action) -> bool {
    let node = actor(s, action);
    &&& well_formed(s)
    &&& well_formed(s_)
    &&& 0 <= node < 3
    &&& local_action(s, s_, action)
    &&& s_.replicas == s.replicas.update(node, s_.replicas[node])
    &&& s_.network == network_after(s, action)
    &&& s_.executed == execution_after(s, action)
}

#[verifier::opaque]
pub open spec fn audit_next(s: AuditState, s_: AuditState) -> bool {
    exists |action: Action| #[trigger] step(s, s_, action)
}

#[verifier::opaque]
pub open spec fn valid_behavior(trace: Seq<AuditState>) -> bool {
    &&& trace.len() > 0
    &&& trace[0] == initial()
    &&& forall |i: int| 0 <= i < trace.len() - 1 ==>
        #[trigger] audit_next(trace[i], trace[i + 1])
}

#[verifier::opaque]
pub open spec fn source_next(s: AuditState, s_: AuditState) -> bool {
    exists |node: int| #![trigger s.replicas[node]] {
        &&& 0 <= node < 3
        &&& LNext(s.replicas[node], s_.replicas[node], constants(node))
        &&& (forall |other: int| #![trigger s_.replicas[other]]
            0 <= other < 3 && other != node ==>
                s_.replicas[other] == s.replicas[other])
    }
}

/// The audit wrapper cannot invent a local transition outside the checked-in
/// protocol. Its histories impose no agreement assumption on those actions.
pub proof fn lemma_step_projects_to_source(s: AuditState, s_: AuditState, action: Action)
    requires step(s, s_, action)
    ensures
        0 <= actor(s, action) < 3,
        well_formed(s), well_formed(s_), source_next(s, s_),
        LNext(s.replicas[actor(s, action)], s_.replicas[actor(s, action)],
            constants(actor(s, action))),
        forall |node: int| #![trigger s_.replicas[node]]
            0 <= node < 3 && node != actor(s, action) ==>
                s_.replicas[node] == s.replicas[node],
{
    reveal(step);
    reveal(source_next);
    match action {
        Action::Collect { packet } => {
            match s.network[packet].msg {
                LEPaxosMessage::PreAcceptOk { sender, seq, conflict } => {
                    assert(LReceivePreAcceptOk(s.replicas[actor(s, action)],
                        s_.replicas[actor(s, action)], constants(actor(s, action)),
                        sender, seq, conflict, sent(s, action)));
                },
                _ => {},
            }
        },
        _ => {},
    }
}

pub proof fn lemma_initial_satisfies_source()
    ensures forall |node: int| 0 <= node < 3 ==>
        LInit(initial().replicas[node], #[trigger] constants(node))
{
}

/// Projection into the existing local model, with exactly one replica taking
/// an LNext step and every other replica unchanged at each transition.
#[verifier::opaque]
pub open spec fn source_behavior(trace: Seq<AuditState>) -> bool {
    &&& trace.len() > 0
    &&& (forall |node: int| 0 <= node < 3 ==>
        #[trigger] LInit(trace[0].replicas[node], constants(node)))
    &&& (forall |i: int| 0 <= i < trace.len() - 1 ==>
        #[trigger] source_next(trace[i], trace[i + 1]))
}

pub proof fn lemma_behavior_projects_to_source(trace: Seq<AuditState>)
    requires valid_behavior(trace)
    ensures source_behavior(trace)
{
    reveal(valid_behavior);
    reveal(source_behavior);
    lemma_initial_satisfies_source();
    assert(trace.len() > 0);
    assert(trace[0] == initial());
    assert forall |node: int| 0 <= node < 3 implies
        #[trigger] LInit(trace[0].replicas[node], constants(node))
    by {
        assert(LInit(initial().replicas[node], constants(node)));
    };
    assert forall |i: int| 0 <= i < trace.len() - 1 implies
        #[trigger] source_next(trace[i], trace[i + 1])
    by {
        assert(audit_next(trace[i], trace[i + 1]));
        reveal(audit_next);
        let action = choose |action: Action| #[trigger] step(trace[i], trace[i + 1], action);
        lemma_step_projects_to_source(trace[i], trace[i + 1], action);
    };
}

/// Candidate successors are witnesses only. Every used successor below is
/// checked against step, which calls the original source predicates.
pub open spec fn run(s: AuditState, action: Action) -> AuditState {
    let node = actor(s, action);
    let local = s.replicas[node];
    let next = match action {
        Action::Propose { command, .. } => LState {
            phase: LInstancePhase::PreAccepted, cmd: command,
            seq: local.committed_count + 1, dep_count: 0, is_leader: true,
            preaccept_senders: Set::empty().insert(node), accept_senders: Set::empty(),
            has_conflict: false, max_resp_seq: 0, ..local
        },
        Action::Collect { packet } => match s.network[packet].msg {
            LEPaxosMessage::PreAcceptOk { sender, seq, conflict } => LState {
                preaccept_senders: local.preaccept_senders.insert(sender),
                has_conflict: local.has_conflict || conflict,
                dep_count: if conflict { local.dep_count + 1 } else { local.dep_count },
                max_resp_seq: if seq > local.max_resp_seq { seq } else { local.max_resp_seq },
                seq: if seq > local.seq { seq } else { local.seq }, ..local
            },
            _ => local,
        },
        Action::Commit { .. } => LState {
            phase: LInstancePhase::Committed, committed_count: local.committed_count + 1, ..local
        },
        Action::Execute { .. } => LState {
            phase: LInstancePhase::Executed, executed_count: local.executed_count + 1, ..local
        },
        Action::NewInstance { .. } => LState {
            phase: LInstancePhase::Empty, cmd: 0, seq: 0, dep_count: 0, is_leader: false,
            preaccept_senders: Set::empty(), accept_senders: Set::empty(),
            has_conflict: false, max_resp_seq: 0, ..local
        },
        Action::Recover { ballot, .. } => LState {
            ballot, phase: LInstancePhase::PreAccepted, dep_count: 0, is_leader: true,
            preaccept_senders: Set::empty().insert(node), accept_senders: Set::empty(),
            has_conflict: false, max_resp_seq: 0, ..local
        },
        _ => local,
    };
    AuditState {
        replicas: s.replicas.update(node, next),
        network: network_after(s, action), executed: execution_after(s, action),
    }
}

pub open spec fn prefix(left: Seq<int>, right: Seq<int>) -> bool {
    &&& left.len() <= right.len()
    &&& forall |i: int| #![trigger left[i], right[i]]
        0 <= i < left.len() ==> left[i] == right[i]
}

/// Required specialization of SMR refinement for an application in which
/// every distinct command conflicts. Independent-command reordering is not
/// ruled out by the general EPaxos goal; this particular workload has none.
pub open spec fn execution_prefix_agreement(s: AuditState) -> bool {
    forall |left: int, right: int| #![trigger s.executed[left], s.executed[right]]
        0 <= left < 3 && 0 <= right < 3 ==>
        (prefix(s.executed[left], s.executed[right])
            || prefix(s.executed[right], s.executed[left]))
}

/// All commands conflict in the audited application, so each node's executed
/// sequence must be a prefix of one common sequential history.
pub open spec fn sequential_refinement(s: AuditState, history: Seq<int>) -> bool {
    forall |node: int| #![trigger s.executed[node]] 0 <= node < 3 ==>
        prefix(s.executed[node], history)
}

/// A trace append helper proves actual reachability, not just isolated states.
pub proof fn lemma_extend(trace: Seq<AuditState>, next: AuditState, action: Action)
    requires trace.len() > 0, valid_behavior(trace), step(trace.last(), next, action)
    ensures valid_behavior(trace.push(next))
{
    reveal(valid_behavior);
    assert(trace[0] == initial());
    assert(trace.push(next)[0] == initial());
    assert(audit_next(trace.last(), next)) by { reveal(audit_next); };
    assert forall |i: int|
        0 <= i < trace.push(next).len() - 1 implies
            #[trigger] audit_next(trace.push(next)[i], trace.push(next)[i + 1])
    by {
        if i == trace.len() - 1 {
            assert(trace.push(next)[i] == trace.last());
            assert(audit_next(trace.push(next)[i], trace.push(next)[i + 1]));
        } else {
            assert(trace.push(next)[i] == trace[i]);
            assert(trace.push(next)[i + 1] == trace[i + 1]);
            assert(audit_next(trace[i], trace[i + 1]));
        }
    };
}

/// Complete one proposal using a genuine peer reply. This helper makes no
/// claim that the resulting execution is safe.
pub proof fn lemma_execute_cycle(
    trace: Seq<AuditState>, node: int, peer: int, command: int,
) -> (result: Seq<AuditState>)
    requires
        trace.len() > 0, valid_behavior(trace), well_formed(trace.last()),
        0 <= node < 3, 0 <= peer < 3, node != peer,
        trace.last().replicas[node].phase is Empty,
    ensures
        valid_behavior(result), well_formed(result.last()),
        result.len() == trace.len() + 5,
        result.last().executed == trace.last().executed.update(node,
            trace.last().executed[node].push(command)),
        result.last().replicas[node].phase is Executed,
        result.last().replicas[node].cmd == command,
        result.last().replicas[node].committed_count
            == trace.last().replicas[node].committed_count + 1,
        result.last().network.len() == trace.last().network.len() + 5,
        result.last().network[trace.last().network.len() as int + 2]
            == (Packet { src: peer, dst: node, msg: LEPaxosMessage::PreAcceptOk {
                sender: peer, seq: trace.last().replicas[peer].committed_count, conflict: false } }),
        result[trace.len() as int + 1].network[trace.last().network.len() as int + 2]
            == result.last().network[trace.last().network.len() as int + 2],
        result[trace.len() as int + 1].network[trace.last().network.len() as int
            + if peer < node { peer } else { peer - 1 }].msg
            == (LEPaxosMessage::PreAccept { ballot: trace.last().replicas[node].ballot,
                cmd: command, seq: trace.last().replicas[node].committed_count + 1 }),
        forall |i: int| #![trigger result.last().replicas[i]]
            0 <= i < 3 && i != node ==>
                result.last().replicas[i] == trace.last().replicas[i],
{
    reveal(step);
    let s0 = trace.last();
    let a0 = Action::Propose { node, command };
    let s1 = run(s0, a0);
    assert(step(s0, s1, a0));
    let request = s0.network.len() as int + if peer < node { peer } else { peer - 1 };
    assert(s1.network[request].src == node);
    assert(s1.network[request].dst == peer);
    let a1 = Action::Reply { packet: request };
    let s2 = run(s1, a1);
    assert(step(s1, s2, a1));
    let response = s0.network.len() as int + 2;
    let a2 = Action::Collect { packet: response };
    let s3 = run(s2, a2);
    assert(step(s2, s3, a2));
    let voters = Set::<int>::empty().insert(node);
    assert(voters.len() == 1);
    assert(!voters.contains(peer));
    vstd::set::lemma_set_insert_len(voters, peer);
    assert(s3.replicas[node].preaccept_senders == voters.insert(peer));
    assert(s3.replicas[node].preaccept_senders.len() == 2);
    let a3 = Action::Commit { node };
    let s4 = run(s3, a3);
    assert(step(s3, s4, a3));
    let a4 = Action::Execute { node };
    let s5 = run(s4, a4);
    assert(step(s4, s5, a4));
    lemma_extend(trace, s1, a0);
    let trace = trace.push(s1);
    lemma_extend(trace, s2, a1);
    let trace = trace.push(s2);
    lemma_extend(trace, s3, a2);
    let trace = trace.push(s3);
    lemma_extend(trace, s4, a3);
    let trace = trace.push(s4);
    lemma_extend(trace, s5, a4);
    trace.push(s5)
}

/// Three genuine replicas, actual sent replies, majority and fast quorum both
/// two. Two distinct commands execute first at different nodes. No fabricated
/// reply, invalid sender, crash, recovery, or repeated client proposal is used.
pub proof fn lemma_conflicting_execution_prefixes() -> (trace: Seq<AuditState>)
    ensures
        valid_behavior(trace),
        trace.last().executed[0] == seq![10int],
        trace.last().executed[1] == seq![20int],
        !execution_prefix_agreement(trace.last()),
{
    let start = seq![initial()];
    assert(valid_behavior(start)) by { reveal(valid_behavior); };
    let first = lemma_execute_cycle(start, 0, 2, 10);
    let result = lemma_execute_cycle(first, 1, 2, 20);
    assert(result.last().executed[0] == seq![10int]);
    assert(result.last().executed[1] == seq![20int]);
    assert(result.last().executed[0][0] == 10);
    assert(result.last().executed[1][0] == 20);
    assert(!prefix(result.last().executed[0], result.last().executed[1]));
    assert(!prefix(result.last().executed[1], result.last().executed[0]));
    assert(!execution_prefix_agreement(result.last()));
    result
}

/// A response to command 10 is accepted again for command 20. The peer has
/// processed no request for 20, but the coordinator reaches a fast quorum.
/// This refutes response-to-instance binding, an auxiliary proof obligation;
/// it is distinct from the execution-refinement counterexample above.
pub proof fn lemma_stale_reply_crosses_instances() -> (trace: Seq<AuditState>)
    ensures
        valid_behavior(trace), trace.len() == 10,
        trace[5].executed[0] == seq![10int],
        trace[7].replicas[0].cmd == 20,
        step(trace[7], trace[8], Action::Collect { packet: 2 }),
        step(trace[8], trace[9], Action::Commit { node: 0 }),
        trace[7].network[2] == trace[2].network[2],
        trace[2].network[1].msg == (LEPaxosMessage::PreAccept { ballot: 0, cmd: 10, seq: 1 }),
        trace[9].replicas[0].phase is Committed,
        trace[9].replicas[0].cmd == 20,
        trace[9].replicas[0].committed_count == 2,
        trace[9].replicas[2] == initial_local(),
{
    reveal(step);
    let start = seq![initial()];
    assert(valid_behavior(start)) by { reveal(valid_behavior); };
    let trace = lemma_execute_cycle(start, 0, 2, 10);
    let s5 = trace.last();
    let a5 = Action::NewInstance { node: 0 };
    let s6 = run(s5, a5);
    assert(step(s5, s6, a5));
    let a6 = Action::Propose { node: 0, command: 20 };
    let s7 = run(s6, a6);
    assert(step(s6, s7, a6));
    let a7 = Action::Collect { packet: 2 };
    let s8 = run(s7, a7);
    assert(step(s7, s8, a7));
    assert(s8.replicas[0].preaccept_senders =~= set![0int, 2int]);
    assert(s8.replicas[0].preaccept_senders.len() == 2);
    let a8 = Action::Commit { node: 0 };
    let s9 = run(s8, a8);
    assert(step(s8, s9, a8));
    lemma_extend(trace, s6, a5);
    let trace = trace.push(s6);
    lemma_extend(trace, s7, a6);
    let trace = trace.push(s7);
    lemma_extend(trace, s8, a7);
    let trace = trace.push(s8);
    lemma_extend(trace, s9, a8);
    trace.push(s9)
}

/// The requested all-conflicting application refinement has a counterexample
/// consisting entirely of source LInit/LNext actions and genuine packet sends.
pub proof fn lemma_no_sequential_execution_refinement() -> (trace: Seq<AuditState>)
    ensures
        valid_behavior(trace), source_behavior(trace),
        !(exists |history: Seq<int>| #[trigger] sequential_refinement(trace.last(), history)),
{
    let trace = lemma_conflicting_execution_prefixes();
    lemma_behavior_projects_to_source(trace);
    let s = trace.last();
    assert(s.executed[0][0] == 10);
    assert(s.executed[1][0] == 20);
    assert forall |history: Seq<int>| #[trigger] sequential_refinement(s, history)
        implies false
    by {
        assert(prefix(s.executed[0], history));
        assert(prefix(s.executed[1], history));
        assert(history.len() >= 1);
        assert(history[0] == 10);
        assert(history[0] == 20);
    };
    trace
}

} // verus!
