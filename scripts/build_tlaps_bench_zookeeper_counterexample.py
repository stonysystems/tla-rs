#!/usr/bin/env python3
"""Emit untrusted ground states from a TLC trace; Verus checks every model edge.

This converts finite trace values, not the TLA+ specification. The handwritten
ZooKeeper and FastLeaderElection models remain the definitions being checked.
"""
from pathlib import Path
import argparse
import gzip
import json

ROOT = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--index-failure", action="store_true", help="Emit the separate reachable invalid-index certificate.")
parser.add_argument("--proof-output", type=Path, help="Write a candidate certificate outside the main proof suite while developing it.")
arguments = parser.parse_args()
INDEX_FAILURE = arguments.index_failure
CASE = "zookeeper_bad_index" if INDEX_FAILURE else "zookeeper_counterexample"
REPORT = ROOT / "reports/tlaps_bench_manual" / CASE
RAW = json.loads(gzip.decompress((REPORT / "trace.json.gz").read_bytes()))
IDS = ("a", "b", "c")


def canonical(value):
    if isinstance(value, dict):
        if set(value) == {"set"}:
            return {"set": sorted((canonical(v) for v in value["set"]), key=lambda v: json.dumps(v, sort_keys=True))}
        return {k: canonical(v) for k, v in value.items()}
    if isinstance(value, list):
        return [canonical(v) for v in value]
    return value


def original(s):
    return canonical({k: v for k, v in s.items() if k not in {"pc", "edge"}})


states = [original(RAW[0])]
actions = []
trace_indices = [0]
for trace_index, s in enumerate(RAW[1:], 1):
    if s["edge"][0] == "Stutter":
        assert original(s) == states[-1]
    else:
        actions.append(s["edge"])
        states.append(original(s))
        trace_indices.append(trace_index)


def sid(i):
    assert i in IDS
    return f"ids::{i}()"


def boolean(v):
    assert isinstance(v, bool)
    return str(v).lower()


def seq(values, render):
    return "seq![" + ",".join(map(render, values)) + "]"


def aset(values, render):
    assert set(values) == {"set"}
    return "set![" + ",".join(map(render, values["set"])) + "]"


def amap(values, render):
    return "map![" + ",".join(f"{sid(i)} => {render(values[i])}" for i in IDS) + "]"


def pairmap(values, render):
    return "map![" + ",".join(f"({sid(i)},{sid(j)}) => {render(values[i][j])}" for i in IDS for j in IDS) + "]"


def zxid(z):
    return f"Zxid {{ epoch: {z[0]},counter: {z[1]} }}"


def txn(t):
    return f"Txn {{ zxid: {zxid(t['zxid'])},value: {t['value']},epoch: {t['epoch']},ack: {aset(t['ackSid'],sid)} }}"


def commit(c):
    return f"Commit {{ index: {c['index']},zxid: {zxid(c['zxid'])} }}"


def option(i):
    return "None" if i == "Nil" else f"Some({sid(i)})"


def vote(v):
    return f"fle::Vote {{ leader: {option(v['proposedLeader'])},zxid: {zxid(v['proposedZxid'])},epoch: {v['proposedEpoch']} }}"


def role(v):
    return "Role::" + {"LOOKING": "Looking", "FOLLOWING": "Following", "LEADING": "Leading"}[v]


def received(r):
    return f"fle::Received {{ vote: {vote(r['vote'])},round: {r['round']},role: {role(r['state'])},version: {r['version']} }}"


def notification(m):
    assert m["mtype"] == "NOTIFICATION"
    return f"fle::Notification {{ source: {sid(m['msource'])},role: {role(m['mstate'])},round: {m['mround']},vote: {vote(m['mvote'])} }}"


def queued(m):
    return "None" if m["mtype"] == "NONE" else f"Some({notification(m)})"


def message(m):
    name = {"FOLLOWERINFO": "FollowerInfo", "LEADERINFO": "LeaderInfo", "ACKEPOCH": "AckEpoch", "DIFF": "Diff", "TRUNC": "Trunc", "SNAP": "Snap", "PROPOSAL": "Proposal", "COMMIT": "Commit", "NEWLEADER": "NewLeader", "ACKLD": "AckLd", "UPTODATE": "UpToDate", "ACK": "Ack"}[m["mtype"]]
    if name == "Snap":
        fields = zxid(m["msnapZxid"]) + "," + seq(m["msnapshot"], txn)
    elif name == "Trunc":
        fields = zxid(m["mtruncZxid"])
    else:
        fields = zxid(m["mzxid"])
        if name == "AckEpoch":
            fields += "," + str(m["mepoch"])
        if name == "Proposal":
            fields += "," + str(m["mdata"])
    return f"Message::{name}({fields})"


def al(r):
    return f"AL {{ sid: {sid(r['sid'])},connected: {boolean(r['connected'])} }}"


def electing(r):
    return f"Electing {{ sid: {sid(r['sid'])},zxid: {zxid(r['peerLastZxid'])},quorum: {boolean(r['inQuorum'])} }}"


def proposal(p):
    return f"Proposal {{ source: {sid(p['source'])},epoch: {p['epoch']},zxid: {zxid(p['zxid'])},value: {p['data']} }}"


POOL = {}
DEFS = []


def intern(kind, ty, value):
    key = (kind, value)
    if key not in POOL:
        name = f"{kind}_{len(POOL)}"
        POOL[key] = name
        DEFS.append(f"pub open spec fn {name}() -> {ty} {{ {value} }}\n")
    return POOL[key] + "()"


def history(h):
    return intern("h", "Seq<Txn>", seq(h, txn))


def fnode(s, i):
    fields = {
        "role": role(s["state"][i]), "current": str(s["currentEpoch"][i]),
        "history": history(s["history"][i]), "processed": commit(s["lastProcessed"][i]),
        "vote": vote(s["currentVote"][i]), "clock": str(s["logicalClock"][i]),
        "received": intern("rv", "Map<int,fle::Received>", amap(s["receiveVotes"][i], received)),
        "outside": intern("rv", "Map<int,fle::Received>", amap(s["outOfElection"][i], received)),
        "queue": intern("eq", "Seq<Option<fle::Notification>>", seq(s["recvQueue"][i], queued)),
        "waiting": boolean(s["waitNotmsg"][i]), "leading": aset(s["leadingVoteSet"][i], sid),
    }
    return intern("en", "fle::LServer", "fle::LServer { " + ",".join(f"{k}: {v}" for k, v in fields.items()) + " }")


def node(s, i):
    fields = {
        "phase": "Phase::" + {"ELECTION": "Election", "DISCOVERY": "Discovery", "SYNCHRONIZATION": "Synchronization", "BROADCAST": "Broadcast"}[s["zabState"][i]],
        "accepted": str(s["acceptedEpoch"][i]), "committed": commit(s["lastCommitted"][i]),
        "snapshot": commit(s["lastSnapshot"][i]), "initial": history(s["initialHistory"][i]),
        "learners": aset(s["learners"][i], sid), "connecting": aset(s["connecting"][i], al),
        "electing": aset(s["electing"][i], electing), "ackld": aset(s["ackldRecv"][i], al),
        "forwarding": aset(s["forwarding"][i], sid), "max_epoch": str(s["tempMaxEpoch"][i]),
        "leader": option(s["connectInfo"][i]["sid"]),
        "mode": "Mode::" + {"NONE": "None", "DIFF": "Diff", "TRUNC": "Trunc", "SNAP": "Snap"}[s["connectInfo"][i]["syncMode"]],
        "received_leader": boolean(s["connectInfo"][i]["nlRcv"]),
        "pending": history(s["packetsSync"][i]["notCommitted"]), "commits": seq(s["packetsSync"][i]["committed"], zxid),
        "online": boolean(s["status"][i] == "ONLINE"),
    }
    return intern("n", "LServer", "LServer { " + ",".join(f"{k}: {v}" for k, v in fields.items()) + " }")


def state(s):
    enodes = "map![" + ",".join(f"{sid(i)} => {fnode(s,i)}" for i in IDS) + "]"
    nodes = "map![" + ",".join(f"{sid(i)} => {node(s,i)}" for i in IDS) + "]"
    emsgs = intern("em", "Map<(int,int),Seq<fle::Notification>>", pairmap(s["electionMsgs"], lambda q: seq(q, notification)))
    msgs = intern("pm", "Map<(int,int),Seq<Message>>", pairmap(s["msgs"], lambda q: seq(q, message)))
    partitions = intern("part", "Map<(int,int),bool>", pairmap(s["partition"], boolean))
    leaders = "map![" + ",".join(f"{k+1}int => {aset(q,sid)}" for k, q in enumerate(s["epochLeader"])) + "]"
    proposals = intern("ps", "Set<Proposal>", aset(s["proposalMsgsLog"], proposal))
    return f"LState {{ election: fle::LState {{ nodes: {enodes},msgs: {emsgs} }},nodes: {nodes},msgs: {msgs},partition: {partitions},epoch_leader: {leaders},proposals: {proposals} }}"


def action(edge):
    name, i, j = edge
    args = sid(i) + ("," + sid(j) if name in {"Receive", "Connect", "FollowerInfo", "LeaderInfo", "AckEpoch", "Sync", "SyncMessage", "ProposalSync", "CommitSync", "NewLeader", "AckLd", "UpToDate", "Proposal", "Ack", "Commit"} else "")
    if name in {"Receive", "Timeout", "Handle", "Wait"}:
        return f"Action::Election(fle::Action::{name}({args}))"
    return f"Action::{name}({args})"


rendered = [state(s) for s in states]
parts = ['''//! Finite source trace used as untrusted proof input; every transition is checked.
//! Reproduce with scripts/build_tlaps_bench_zookeeper_counterexample.py.
use vstd::prelude::*;
use super::zookeeper::*;
use super::zab::{self as z,Role,Phase,Txn,Zxid,Commit,AL,Proposal};
use super::zk_election as fle;
use super::zookeeper_trace_ids as ids;
use super::zookeeper_support as support;
use super::temporal::Behavior;
verus! {
broadcast use { vstd::map_lib::group_map_properties, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties };
pub open spec fn constants() -> Constants { Constants { servers: ids::servers(),max_epoch: 4,request_value: 0 } }
pub proof fn domains()
    ensures z::channels(constants()) == set![(ids::a(),ids::a()),(ids::a(),ids::b()),(ids::a(),ids::c()),(ids::b(),ids::a()),(ids::b(),ids::b()),(ids::b(),ids::c()),(ids::c(),ids::a()),(ids::c(),ids::b()),(ids::c(),ids::c())]
{
    ids::geometry();
    let q=set![(ids::a(),ids::a()),(ids::a(),ids::b()),(ids::a(),ids::c()),(ids::b(),ids::a()),(ids::b(),ids::b()),(ids::b(),ids::c()),(ids::c(),ids::a()),(ids::c(),ids::b()),(ids::c(),ids::c())];
    assert(z::channels(constants()) =~= q) by { assert forall |p: (int,int)| #![trigger q.contains(p)] z::channels(constants()).contains(p) <==> q.contains(p) by { super::zab_connections::channel_pair(constants(),p.0,p.1); } }
}
''', *DEFS]
parts += [f"#[verifier::opaque]\npub open spec fn state_{k}() -> LState {{ {s} }}\n" for k, s in enumerate(rendered)]
parts += ["#[verifier::opaque]\npub open spec fn state(k: int) -> LState { match k {\n"]
parts += [f"    _ if k == {k} => state_{k}(),\n" for k in range(len(rendered))]
parts += ["    _ => initial(constants()),\n} }\n#[verifier::opaque]\npub open spec fn action(k: int) -> Action { match k {\n"]
parts += [f"    _ if k == {k} => {action(a)},\n" for k, a in enumerate(actions)]
parts += ["    _ => Action::Stutter,\n} }\n"]
for k in range(len(actions)):
    edge_start = len(parts)
    parts += [f'''pub proof fn edge_{k}()
    ensures enabled(state({k}),constants(),action({k})),apply(state({k}),constants(),action({k})) == state({k+1})
{{
    ids::geometry(); domains(); reveal(state); reveal(state_{k}); reveal(state_{k+1}); reveal(action); reveal(enabled); reveal(apply); reveal(fle::apply); reveal(z::maximum);
    let s=state({k}); let u=apply(s,constants(),action({k})); let v=state({k+1});
''']
    tag, who, _ = actions[k]
    split_edge = INDEX_FAILURE and (tag == "Request" or k in {162, 169, 187})
    peer = actions[k][2]
    msg = states[k]["msgs"][peer][who]
    if tag == "Ack" or tag == "SyncMessage" and msg and msg[0]["mtype"] == "TRUNC":
        target = msg[0]["mzxid" if tag == "Ack" else "mtruncZxid"]
        h = f"s.election.nodes[{sid(who)}].history"
        matches = [p+1 for p,t in enumerate(states[k]["history"][who]) if t["zxid"] == target]
        parts += [f"    assert(Set::range(1,{h}.len() as int+1).filter(|p: int| {h}[p-1].zxid == {zxid(target)}) =~= {aset({'set':matches},str)});\n"]
        if len(matches) == 1:
            parts += [f"    assert(Set::range(1,{h}.len() as int+1).filter(|p: int| {h}[p-1].zxid == {zxid(target)}).contains({matches[0]})); assert(z::index({h},{zxid(target)}) == {matches[0]});\n"]
        if tag == "Ack":
            previous = [p+1 for p,t in enumerate(states[k]["history"][who]) if peer in t["ackSid"]["set"]]
            parts += [f"    assert(Set::range(1,{h}.len() as int+1).filter(|p: int| {h}[p-1].ack.contains({sid(peer)})) =~= {aset({'set':previous},str)});\n"]
            parts += [f"    assert(z::maximum(Set::range(1,{h}.len() as int+1).filter(|p: int| {h}[p-1].ack.contains({sid(peer)}))) == {max(previous,default=-1)});\n"]
    if tag == "Sync":
        parts += ["    reveal_with_fuel(packets,5);\n"]
    if tag == "Receive":
        queue = states[k]["recvQueue"][who]
        expected = seq([m for m in queue if m["mtype"] != "NONE"], queued)
        parts += [f"    reveal_with_fuel(Seq::filter,{len(queue)+1}); assert(s.election.nodes[{sid(who)}].queue.filter(|m: Option<fle::Notification>| m is Some) =~= {expected});\n"]
    if tag == "Request":
        voters = [j for j in states[k]["forwarding"][who]["set"] if states[k]["zabState"][j] == "BROADCAST"] + [who]
        parts += [f"    assert(s.nodes[{sid(who)}].forwarding.filter(|j: int| s.nodes[j].phase == Phase::Broadcast).insert({sid(who)}) =~= {aset({'set': voters},sid)});\n"]
    if tag == "Handle" and states[k]["recvQueue"][who] and states[k]["recvQueue"][who][0]["mtype"] == "NOTIFICATION":
        m = states[k]["recvQueue"][who][0]
        if m["mstate"] == "LOOKING" and m["mround"] >= states[k]["logicalClock"][who]:
            n = states[k+1]
            voters = [j for j in IDS if j == who or n["receiveVotes"][who][j]["vote"] == n["currentVote"][who] and n["receiveVotes"][who][j]["round"] == m["mround"]]
            parts += [f"    assert(fle::vote_set(constants(),{sid(who)},u.election.nodes[{sid(who)}].received,u.election.nodes[{sid(who)}].vote,{m['mround']}) =~= {aset({'set': voters},sid)});\n"]
        elif m["mstate"] != "LOOKING":
            for field, source in [("received", "receiveVotes"), ("outside", "outOfElection")]:
                receipts = dict(states[k][source][who])
                old = receipts[m["msource"]]
                if old["round"] <= m["mround"]:
                    receipts[m["msource"]] = {"vote": m["mvote"], "round": m["mround"], "state": m["mstate"], "version": 1 if old["round"] < m["mround"] else old["version"]+1}
                voters = [j for j in IDS if j == m["msource"] or receipts[j]["vote"] == m["mvote"] and receipts[j]["round"] == m["mround"]]
                q = f"fle::put(s.election.nodes[{sid(who)}].{field},{notification(m)})"
                parts += [f"    assert({q} =~= {amap(receipts,received)});\n"]
                parts += [f"    assert(fle::vote_set(constants(),{sid(m['msource'])},{q},{vote(m['mvote'])},{m['mround']}) =~= {aset({'set': voters},sid)});\n"]
    if tag in {"FollowerInfo", "AckEpoch", "Sync", "AckLd"}:
        for field, source in ([] if INDEX_FAILURE and k in {162, 187} else [("connecting", "connecting"), ("ackld", "ackldRecv")]):
            entries = states[k][source][who]["set"]
            members = {"set": [r["sid"] for r in entries]}
            connected = {"set": [r["sid"] for r in entries if r["connected"]]}
            q = f"s.nodes[{sid(who)}].{field}"
            for r in entries:
                parts += [f"    assert({q}.contains({al(r)})); {q}.lemma_map_contains(|x: AL| x.sid,{sid(r['sid'])});\n"]
                if r["connected"]:
                    parts += [f"    assert({q}.filter(|x: AL| x.connected).contains({al(r)})); {q}.filter(|x: AL| x.connected).lemma_map_contains(|x: AL| x.sid,{sid(r['sid'])});\n"]
            parts += [f"    assert(z::al_ids(s.nodes[{sid(who)}].{field}) =~= {aset(members,sid)});\n"]
            parts += [f"    assert(z::al_connected(s.nodes[{sid(who)}].{field}) =~= {aset(connected,sid)});\n"]
        members = {"set": [r["sid"] for r in states[k]["electing"][who]["set"] if r["inQuorum"]]}
        for r in states[k]["electing"][who]["set"]:
            if r["inQuorum"]:
                q = f"s.nodes[{sid(who)}].electing.filter(|e: Electing| e.quorum)"
                parts += [f"    assert({q}.contains({electing(r)})); {q}.lemma_map_contains(|e: Electing| e.sid,{sid(r['sid'])});\n"]
        parts += [f"    assert(super::zookeeper_quorum_receipts::ids(s.nodes[{sid(who)}].electing) =~= {aset(members,sid)});\n"]
        finished = who in members["set"] and len(members["set"]) >= 2
        parts += [f"    assert(election_finished(s,constants(),{sid(who)}) == {boolean(finished)});\n"]
        peer = actions[k][2]
        if tag in {"FollowerInfo", "AckLd"}:
            field = "connecting" if tag == "FollowerInfo" else "ackld"
            parts += [f"    super::zab_collections::al_update(s.nodes[{sid(who)}].{field},{sid(peer)});\n"]
            source = "connecting" if tag == "FollowerInfo" else "ackldRecv"
            entries = [r for r in states[k][source][who]["set"] if r["sid"] != peer] + [{"sid": peer, "connected": True}]
            q = f"z::update_al(s.nodes[{sid(who)}].{field},{sid(peer)})"
            parts += [f"    assert({q} =~= {aset({'set': entries},al)});\n"]
            for r in entries:
                if r["connected"]:
                    filt = f"{q}.filter(|x: AL| x.connected)"
                    parts += [f"    assert({filt}.contains({al(r)})); {filt}.lemma_map_contains(|x: AL| x.sid,{sid(r['sid'])});\n"]
            parts += [f"    assert(z::al_connected({q}) =~= {aset({'set':[r['sid'] for r in entries if r['connected']]},sid)});\n"]
        if tag == "AckEpoch":
            m = states[k]["msgs"][peer][who][0]
            ok = not (m["mepoch"] > states[k]["currentEpoch"][who] or m["mepoch"] == states[k]["currentEpoch"][who] and m["mzxid"] > states[k]["lastProcessed"][who]["zxid"])
            yes = not finished and m["mepoch"] >= 0 and ok
            q = f"update_e(s.nodes[{sid(who)}].electing,{sid(peer)},{zxid(m['mzxid'])},{boolean(yes)})"
            post = states[k+1]["electing"][who]
            members = {"set": [r["sid"] for r in post["set"] if r["inQuorum"]]}
            parts += [f"    assert({q} =~= {aset(post,electing)});\n"]
            for r in ([] if INDEX_FAILURE and k == 162 else post["set"]):
                if r["inQuorum"]:
                    filt = f"{q}.filter(|e: Electing| e.quorum)"
                    parts += [f"    assert({filt}.contains({electing(r)})); {filt}.lemma_map_contains(|e: Electing| e.sid,{sid(r['sid'])});\n"]
            if not (INDEX_FAILURE and k == 162):
                parts += [f"    assert(super::zookeeper_quorum_receipts::ids({q}) =~= {aset(members,sid)});\n"]
        if tag == "Sync":
            choices = [r for r in states[k]["electing"][who]["set"] if r["sid"] == peer and r["peerLastZxid"] != [-1,-1]]
            assert len(choices) == 1
            r = choices[0]
            parts += [f"    assert(s.nodes[{sid(who)}].electing.contains({electing(r)}));\n"]
            parts += [f"    assert forall |r: Electing| #![trigger s.nodes[{sid(who)}].electing.contains(r)] s.nodes[{sid(who)}].electing.contains(r) && r.sid == {sid(peer)} && r.zxid != unset() implies r == {electing(r)} by {{}}\n"]
    if INDEX_FAILURE and k == 169:
        leader = states[k]["connectInfo"][who]["sid"]
        remaining = [i for i in states[k]["learners"][leader]["set"] if i != who]
        parts += [f"    assert(s.nodes[{sid(leader)}].learners.remove({sid(who)}) =~= {aset({'set':remaining},sid)}); assert(z::quorum(s.nodes[{sid(leader)}].learners.remove({sid(who)}),constants()));\n"]
        for field, source in [("connecting", "connecting"), ("ackld", "ackldRecv")]:
            q = f"s.nodes[{sid(leader)}].{field}"
            entries = states[k][source][leader]["set"]
            old = next(r for r in entries if r["sid"] == who)
            updated = [{**r, "connected": False} if r["sid"] == who else r for r in entries]
            parts += [f"    assert({q}.contains({al(old)})); {q}.lemma_map_contains(|r: AL| r.sid,{sid(who)});\n"]
            parts += [f"    assert forall |r: AL| #![trigger {q}.contains(r)] {q}.contains(r) && r.sid == {sid(who)} implies r == {al(old)} by {{}}\n"]
            parts += [f"    assert(z::disconnect_al({q},{sid(who)}) =~= {aset({'set':updated},al)});\n"]
        q = f"s.nodes[{sid(leader)}].electing"
        old = next(r for r in states[k]["electing"][leader]["set"] if r["sid"] == who)
        parts += [f"    assert({q}.contains({electing(old)})); assert forall |r: Electing| #![trigger {q}.contains(r)] {q}.contains(r) && r.sid == {sid(who)} implies r == {electing(old)} by {{}}\n"]
        parts += [f"    assert(disconnect_e({q},{sid(who)}) =~= {aset(states[k+1]['electing'][leader],electing)});\n"]
    common_end = len(parts)
    for src in IDS:
        for dst in IDS:
            for pos, m in enumerate(states[k+1]["msgs"][src][dst]):
                if m["mtype"] == "SNAP":
                    field = f"msgs[({sid(src)},{sid(dst)})][{pos}]"
                    parts += [f"    assert(u.{field} is Snap);\n"]
                    parts += [f"    assert forall |p: int| #![trigger (u.{field}->Snap_1)[p]] #![trigger (v.{field}->Snap_1)[p]] 0 <= p < (v.{field}->Snap_1).len() implies (u.{field}->Snap_1)[p].ack =~= (v.{field}->Snap_1)[p].ack by {{}}\n"]
                    parts += [f"    assert((u.{field}->Snap_1) =~= (v.{field}->Snap_1)); assert(u.{field} == v.{field});\n"]
    if split_edge:
        for src in IDS:
            for dst in IDS:
                parts += [f"    assert(u.msgs[({sid(src)},{sid(dst)})] =~= v.msgs[({sid(src)},{sid(dst)})]);\n"]
    parts += ["    assert(u.msgs =~~= v.msgs); assert(u.partition =~~= v.partition); assert(u.epoch_leader =~~= v.epoch_leader); assert(u.proposals =~~= v.proposals);\n    assert(u.election.msgs =~~= v.election.msgs);\n"]
    maps_end = len(parts)
    node_ranges = []
    for i in IDS:
        node_start = len(parts)
        if split_edge:
            parts += [f"    assert(u.election.nodes[{sid(i)}] == v.election.nodes[{sid(i)}] && u.nodes[{sid(i)}] == v.nodes[{sid(i)}]) by {{\n"]
        en = f"election.nodes[{sid(i)}]"
        nd = f"nodes[{sid(i)}]"
        for field in [f"{en}.history", f"{nd}.initial", f"{nd}.pending"]:
            parts += [f"    assert forall |p: int| #![trigger u.{field}[p]] #![trigger v.{field}[p]] 0 <= p < v.{field}.len() implies u.{field}[p].ack =~= v.{field}[p].ack by {{}}\n"]
            parts += [f"    assert(u.{field} =~= v.{field});\n"]
        for field in [f"{en}.received", f"{en}.outside", f"{en}.queue", f"{en}.leading", *[f"{nd}.{f}" for f in ["learners", "connecting", "electing", "ackld", "forwarding", "commits"]]]:
            parts += [f"    assert(u.{field} =~~= v.{field});\n"]
        parts += [f"    assert(u.election.nodes[{sid(i)}] =~~= v.election.nodes[{sid(i)}]); assert(u.nodes[{sid(i)}] =~~= v.nodes[{sid(i)}]);\n"]
        if split_edge:
            parts += ["    }\n"]
        node_ranges.append((i, node_start, len(parts)))
    parts += ["    assert(u.election.nodes =~~= v.election.nodes); assert(u.nodes =~~= v.nodes);\n}\n"]
    if split_edge:
        common = parts[edge_start].split("{\n", 1)[1] + "".join(parts[edge_start+1:common_end])
        actual = f"apply(state({k}),constants(),action({k}))"
        expected = f"state({k+1})"
        helpers = []
        helpers.append(f"pub proof fn request_{k}_enabled()\n    ensures enabled(state({k}),constants(),action({k}))\n{{\n{common}}}\n")
        fields = ["msgs", "partition", "epoch_leader", "proposals", "election.msgs", "nodes.dom()", "election.nodes.dom()"]
        conditions = ",".join(f"{actual}.{f} == {expected}.{f}" for f in fields)
        # The map and per-node checks conclude only facts about apply's result.
        result_common = common.replace(" reveal(enabled);", "", 1)
        helpers.append(f"pub proof fn request_{k}_maps()\n    ensures {conditions}\n{{\n{result_common}" + "".join(parts[common_end:maps_end]) + "}\n")
        for i, first, last in node_ranges:
            conditions = ",".join(f"{actual}.{f}[{sid(i)}] == {expected}.{f}[{sid(i)}]" for f in ["nodes", "election.nodes"])
            helpers.append(f"pub proof fn request_{k}_{i}()\n    ensures {conditions}\n{{\n{result_common}" + "".join(parts[first:last]) + "}\n")
        helpers.append(f'''pub proof fn edge_{k}()
    ensures enabled(state({k}),constants(),action({k})),{actual} == {expected}
{{
    request_{k}_enabled(); request_{k}_maps(); request_{k}_a(); request_{k}_b(); request_{k}_c();
    ids::geometry(); reveal(state); reveal(state_{k+1});
    let u={actual}; let v={expected};
    assert(u.nodes =~= v.nodes); assert(u.election.nodes =~= v.election.nodes);
}}
''')
        if tag != "Request":
            helpers = [part.replace(f"request_{k}_", f"step_{k}_") for part in helpers]
        parts[edge_start:] = helpers
parts += [f"pub proof fn edge(k: int)\n    requires 0 <= k < {len(actions)}\n    ensures enabled(state(k),constants(),action(k)),apply(state(k),constants(),action(k)) == state(k+1)\n{{ match k {{\n"]
parts += [f"    _ if k == {k} => edge_{k}(),\n" for k in range(len(actions))]
parts += ["    _ => {},\n} }\n"]
parts += ['''pub proof fn initial_checked()
    ensures state(0) == initial(constants())
{
    ids::geometry(); domains(); reveal(state); reveal(state_0); broadcast use Set::lemma_map_contains;
    let u=state(0); let v=initial(constants());
    assert(u.msgs =~~= v.msgs); assert(u.partition =~~= v.partition); assert(u.epoch_leader =~~= v.epoch_leader); assert(u.proposals =~~= v.proposals);
    assert(u.election.msgs =~~= v.election.msgs);
''']
for i in IDS:
    en = f"election.nodes[{sid(i)}]"
    nd = f"nodes[{sid(i)}]"
    for field in [f"{en}.history", f"{nd}.initial", f"{nd}.pending"]:
        parts += [f"    assert forall |p: int| #![trigger u.{field}[p]] #![trigger v.{field}[p]] 0 <= p < v.{field}.len() implies u.{field}[p].ack =~= v.{field}[p].ack by {{}}\n"]
        parts += [f"    assert(u.{field} =~= v.{field});\n"]
    for field in [f"{en}.received", f"{en}.outside", f"{en}.queue", f"{en}.leading", *[f"{nd}.{f}" for f in ["learners", "connecting", "electing", "ackld", "forwarding", "commits"]]]:
        parts += [f"    assert(u.{field} =~~= v.{field});\n"]
    parts += [f"    assert(u.{en} =~~= v.{en}); assert(u.{nd} =~~= v.{nd});\n"]
parts += ['''    assert(u.election.nodes =~~= v.election.nodes); assert(u.nodes =~~= v.nodes);
}
pub proof fn violations()
    ensures !primary_integrity(state(132),constants()),!prefix_consistency(state(135),constants()),
        !agreement(state(163),constants()),!total_order(state(167),constants())
{
    ids::geometry(); reveal(state); reveal(state_132); reveal(state_135); reveal(state_163); reveal(state_167);
    let p=goal_state(state(132));
    assert(!z::contains_txn(p.nodes[ids::b()],p.nodes[ids::c()].history[1]));
    if primary_integrity(state(132),constants()) {
        assert(p.nodes[ids::b()].role == Role::Leading && p.nodes[ids::c()].role == Role::Following);
        assert(p.nodes[ids::b()].learners.contains(ids::c()) && p.nodes[ids::c()].leader == Some(ids::b()));
        assert(p.nodes[ids::b()].phase == Phase::Broadcast && p.nodes[ids::c()].phase == Phase::Broadcast);
        assert(1 <= 2 <= p.nodes[ids::c()].committed.index && p.nodes[ids::c()].history[2-1].zxid.epoch < p.nodes[ids::b()].current);
        assert(z::contains_txn(p.nodes[ids::b()],p.nodes[ids::c()].history[2-1]));
        assert(false);
    }
    assert(!primary_integrity(state(132),constants()));
    let p=goal_state(state(135));
    assert(!z::equal(p.nodes[ids::b()].history[1],p.nodes[ids::c()].history[1]));
    assert(!prefix_consistency(state(135),constants()));
    let p=goal_state(state(163));
    assert(!z::contains_txn(p.nodes[ids::a()],p.nodes[ids::c()].history[1]));
    assert(!z::contains_txn(p.nodes[ids::c()],p.nodes[ids::a()].history[1]));
    assert(!agreement(state(163),constants()));
    let p=goal_state(state(167));
    assert(z::equal(p.nodes[ids::b()].history[1],p.nodes[ids::c()].history[2]));
    assert(z::contains_txn(p.nodes[ids::b()],p.nodes[ids::c()].history[2]));
    assert(!z::before(p.nodes[ids::b()],p.nodes[ids::c()].history[1],p.nodes[ids::c()].history[2]));
    if total_order(state(167),constants()) {
        assert(p.nodes[ids::b()].committed.index >= 2 && 1 <= 2 < 3 <= p.nodes[ids::c()].committed.index);
        assert(z::before(p.nodes[ids::b()],p.nodes[ids::c()].history[2-1],p.nodes[ids::c()].history[3-1]));
        assert(false);
    }
    assert(!total_order(state(167),constants()));
}
pub proof fn counterexample() -> (b: Behavior<LState>)
    ensures support::safety_spec(b,constants()),!primary_integrity(b[132],constants()),!prefix_consistency(b[135],constants()),
        !agreement(b[163],constants()),!total_order(b[167],constants())
{
    initial_checked(); violations();
    let c=constants(); let b=IMap::new(|k: int| k >= 0,|k: int| state(if k < 167 { k } else { 167 }));
    assert forall |k: int| k >= 0 implies #[trigger] next(b[k],b[k+1],c) by {
        reveal(next);
        if k < 167 { edge(k); assert(enabled(b[k],c,action(k)) && b[k+1] == apply(b[k],c,action(k))); }
        else { reveal(enabled); reveal(apply); assert(enabled(b[k],c,Action::Stutter) && b[k+1] == apply(b[k],c,Action::Stutter)); }
    }
    b
}
} // verus!
''']
proof = "".join(parts)
if INDEX_FAILURE:
    end = len(actions)
    proof = proof.split("pub proof fn violations()", 1)[0] + f'''pub open spec fn invalid_committed_range(s: LState) -> bool {{
    s.election.nodes[ids::c()].role == Role::Following && s.election.nodes[ids::c()].history.len() == 3
    && s.nodes[ids::c()].committed.index == 4 && s.nodes[ids::c()].snapshot.index == 4
}}
pub proof fn violations()
    ensures invalid_committed_range(state({end}))
{{ ids::geometry(); reveal(state); reveal(state_{end}); }}
pub proof fn counterexample() -> (b: Behavior<LState>)
    ensures support::safety_spec(b,constants()),invalid_committed_range(b[{end}])
{{
    initial_checked(); violations();
    let c=constants(); let b=IMap::new(|k: int| k >= 0,|k: int| state(if k < {end} {{ k }} else {{ {end} }}));
    assert forall |k: int| k >= 0 implies #[trigger] next(b[k],b[k+1],c) by {{
        reveal(next);
        if k < {end} {{ edge(k); assert(enabled(b[k],c,action(k)) && b[k+1] == apply(b[k],c,action(k))); }}
        else {{ reveal(enabled); reveal(apply); assert(enabled(b[k],c,Action::Stutter) && b[k+1] == apply(b[k],c,Action::Stutter)); }}
    }}
    b
}}
}} // verus!
'''
    # Longer ground histories need more solver effort than the quantified
    # protocol lemmas. This changes the effort limit, never the obligation.
    proof = proof.replace("pub proof fn edge_", "#[verifier::rlimit(120)]\npub proof fn edge_")
    proof = proof.replace("pub proof fn request_", "#[verifier::rlimit(120)]\npub proof fn request_")
    proof = proof.replace("pub proof fn step_", "#[verifier::rlimit(120)]\npub proof fn step_")
else:
    # As in the index-failure certificate: every ground edge gets the same
    # effort limit, which changes the effort, never the obligation.
    proof = proof.replace("pub proof fn edge_", "#[verifier::rlimit(120)]\npub proof fn edge_")
# A few ground checks are heavier than the rest on current Verus releases;
# like edge_161 above, they get their own effort limit.
HEAVY = {"edge_163": 240, "edge_178": 240, "step_169_maps": 240, "step_169_c": 240} if INDEX_FAILURE else {"edge_160": 480, "edge_161": 240}
for name, limit in HEAVY.items():
    old = f"#[verifier::rlimit(120)]\npub proof fn {name}("
    assert proof.count(old) == 1, name
    proof = proof.replace(old, f"#[verifier::rlimit({limit})]\npub proof fn {name}(")
# Each ground check gets its own solver process, keeping the other checks'
# facts out of its context.
for prefix in ["edge_", "step_", "request_"]:
    proof = proof.replace(f"pub proof fn {prefix}", f"#[verifier::spinoff_prover]\npub proof fn {prefix}")
(arguments.proof_output or ROOT / f"src/protocol/TLAPSBench/{CASE}.rs").write_text(proof)
(REPORT / "actions.json").write_text(json.dumps({"source_trace_indices": trace_indices, "actions": actions}, indent=2) + "\n")
source_names = {
    "Receive": "FLEReceiveNotmsg", "Timeout": "FLENotmsgTimeout", "Handle": "FLEHandleNotmsg", "Wait": "FLEWaitNewNotmsg",
    "Connect": "ConnectAndFollowerSendFOLLOWERINFO", "FollowerInfo": "LeaderProcessFOLLOWERINFO", "LeaderInfo": "FollowerProcessLEADERINFO",
    "AckEpoch": "LeaderProcessACKEPOCH", "Sync": "LeaderSyncFollower", "SyncMessage": "FollowerProcessSyncMessage",
    "ProposalSync": "FollowerProcessPROPOSALInSync", "CommitSync": "FollowerProcessCOMMITInSync", "NewLeader": "FollowerProcessNEWLEADER",
    "AckLd": "LeaderProcessACKLD", "UpToDate": "FollowerProcessUPTODATE", "Request": "LeaderProcessRequest", "Proposal": "FollowerProcessPROPOSAL",
    "Ack": "LeaderProcessACK", "Commit": "FollowerProcessCOMMIT", "Crash": "NodeCrash", "Start": "NodeStart",
}
calls = []
for k, (tag, i, j) in enumerate(actions):
    args = i.upper() if tag in {"Timeout", "Handle", "Wait", "Request", "Crash", "Start"} else i.upper() + "," + j.upper()
    calls.append(f"    {'CASE' if k == 0 else '[]'} replayStep = {k} -> {source_names[tag]}({args})")
replay = """---- MODULE Replay ----
EXTENDS ZkV3_7_0Defs
CONSTANT A,B,C
VARIABLE replayStep
SimulationValue == {0}
ReplayInit == Init /\\ replayStep = 0
ReplayAction ==
""" + "\n".join(calls) + "\n    [] OTHER -> FALSE\n" + f"""ReplayNext == /\\ replayStep < {len(actions)} /\\ ReplayAction /\\ Next /\\ replayStep' = replayStep+1
ReplaySpec == ReplayInit /\\ [][ReplayNext]_<<vars,replayStep>>
====
"""
if INDEX_FAILURE:
    replay = replay.replace("====", "FollowingBound == \\A i \\in Server: state[i] = FOLLOWING => lastCommitted[i].index <= Len(history[i])\n====")
(REPORT / "Replay.tla").write_text(replay)
goals = ["FollowingBound", "Integrity", "GlobalPrimaryOrder", "LocalPrimaryOrder"] if INDEX_FAILURE else ["PrimaryIntegrity", "PrefixConsistency", "Agreement", "TotalOrder"]
for goal in goals:
    (REPORT / f"Replay{goal}.cfg").write_text(f"SPECIFICATION ReplaySpec\nINVARIANT {goal}\nCONSTANTS\nServer = {{a,b,c}}\nMAXEPOCH = 4\nNullPoint = Nil\nA = a\nB = b\nC = c\nValue <- SimulationValue\n")
print(f"Emitted {len(states)} ground states, {len(actions)} edges, and {len(DEFS)} interned values.")
