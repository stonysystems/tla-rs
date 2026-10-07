#!/usr/bin/env python3
"""Emit ground states for an etcd counterexample. Verus checks every transition.

This is a fixed schedule interpreter, not a TLA+ translator. Its output is
untrusted proof input: each adjacent pair must satisfy the handwritten model.
"""
from copy import deepcopy
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]

def frozen(x):
    if isinstance(x, list): return tuple(frozen(y) for y in x)
    return x

def msg(src,dst,term,kind,*fields): return (src,dst,term,kind,*map(frozen,fields))
nodes={i:dict(term=0,role='Follower',vote=None,log=[],commit=0,responded=set(),granted=set(),matched=[0,0,0],disk=(0,None,[],0)) for i in (1,2,3)}
s=dict(nodes=nodes,pending=[],messages=[],votes=set())
states=[deepcopy(s)]; actions=[]

def run(kind,*args):
    global s
    actions.append((kind,*args))
    if kind == 'Receive':
        m,how=args; src,dst,term,body,*f=m; n=s['nodes'][dst]
        if how == 'UpdateTerm': n.update(term=term,role='Follower',vote=None)
        else:
            if how == 'VoteResponse':
                n['responded'].add(src)
                if f[0]: n['granted'].add(src)
            elif how == 'VoteRequest':
                assert term == n['term'] and (n['vote'] is None or n['vote']==src)
                assert f[0] > (n['log'][-1] if n['log'] else 0) or f[0] == (n['log'][-1] if n['log'] else 0) and f[1]>=len(n['log'])
                n['vote']=src;s['pending'].append(msg(dst,src,n['term'],'VoteResponse',True))
            elif how == 'AppendResponse': n['matched'][src-1]=max(n['matched'][src-1],f[2])
            elif how == 'AppendExtend':
                mode,prev,prevterm,entries,commit=f
                n['log']+=list(entries[len(n['log'])-prev:])
            elif how == 'AppendDone':
                mode,prev,prevterm,entries,commit=f
                n['commit']=max(n['commit'],min(commit,prev+len(entries)))
                s['pending'].append(msg(dst,src,n['term'],'AppendResponse',mode,True,prev+len(entries)))
            else: raise ValueError(how)
            if how != 'AppendExtend': s['messages'].remove(m)
    else:
        i=args[0];n=s['nodes'][i]
        if kind=='Timeout':
            n.update(term=n['term']+1,role='Candidate',vote=i,responded=set(),granted=set())
        elif kind=='RequestVote':
            j=args[1]
            s['pending'].append(msg(i,j,n['term'],'VoteResponse',True) if i==j else msg(i,j,n['term'],'VoteRequest',n['log'][-1] if n['log'] else 0,len(n['log'])))
        elif kind=='Ready':
            n['disk']=(n['term'],n['vote'],list(n['log']),n['commit'])
            out=[m for m in s['pending'] if m[0]==i]
            s['votes'].update((m[0],m[2],m[1]) for m in out if m[3]=='VoteResponse' and m[4])
            s['messages']+=out;s['pending']=[m for m in s['pending'] if m[0]!=i]
        elif kind=='BecomeLeader': n.update(role='Leader',matched=[len(n['log']) if j==i else 0 for j in (1,2,3)])
        elif kind=='ClientRequest': n['log'].append(n['term'])
        elif kind=='StepDown': n['role']='Follower'
        elif kind=='SelfAppend': s['pending'].append(msg(i,i,n['term'],'AppendResponse','App',True,len(n['log'])))
        elif kind=='Append':
            j,begin,end=args[1:];prev=begin-1;last=min(len(n['log']),end-1)
            s['pending'].append(msg(i,j,n['term'],'AppendRequest','App',prev,n['log'][prev-1] if prev else 0,n['log'][begin-1:last],min(n['commit'],last)))
        elif kind=='AdvanceCommit':
            agreed=[k for k in range(1,len(n['log'])+1) if 2*sum(x>=k for x in n['matched'])>3]
            if agreed and n['log'][max(agreed)-1]==n['term']: n['commit']=max(n['commit'],max(agreed))
        else: raise ValueError(kind)
    states.append(deepcopy(s))

def recv(src,dst,kind,how):
    m=next(m for m in s['messages'] if m[0]==src and m[1]==dst and m[3]==kind)
    run('Receive',m,how)

def elect(i,j,timeouts):
    for _ in range(timeouts): run('Timeout',i)
    run('RequestVote',i,i);run('RequestVote',i,j);run('Ready',i)
    recv(i,i,'VoteResponse','VoteResponse');recv(i,j,'VoteRequest','UpdateTerm');recv(i,j,'VoteRequest','VoteRequest')
    run('Ready',j);recv(j,i,'VoteResponse','VoteResponse');run('BecomeLeader',i)

elect(1,3,1);run('ClientRequest',1);run('Ready',1)
elect(2,3,2);run('ClientRequest',2);run('Ready',2);run('StepDown',1)
elect(1,3,2);run('ClientRequest',1);run('SelfAppend',1);run('Append',1,3,1,3);run('Ready',1)
recv(1,1,'AppendResponse','AppendResponse');recv(1,3,'AppendRequest','AppendExtend');recv(1,3,'AppendRequest','AppendDone')
run('Ready',3);recv(3,1,'AppendResponse','AppendResponse');run('AdvanceCommit',1)
assert len(actions)==47

def seq(xs): return 'seq!['+','.join(str(x)+'nat' for x in xs)+']'
def iseq(xs): return 'seq!['+','.join(map(str,xs))+']'
def vset(xs): return 'set!['+','.join(str(x)+'int' for x in sorted(xs))+']'
def opt(x): return 'None' if x is None else f'Some({x})'
def message(m):
    src,dst,term,kind,*f=m
    if kind=='VoteRequest': body=f'Body::VoteRequest {{ last_term: {f[0]},last_index: {f[1]} }}'
    elif kind=='VoteResponse': body=f'Body::VoteResponse {{ granted: {str(f[0]).lower()} }}'
    elif kind=='AppendResponse': body=f'Body::AppendResponse {{ mode: Mode::{f[0]},success: {str(f[1]).lower()},matched: {f[2]} }}'
    else: body=f'Body::AppendRequest {{ mode: Mode::{f[0]},prev: {f[1]},prev_term: {f[2]},entries: {seq(f[3])},commit: {f[4]} }}'
    return f'Message {{ source: {src},dest: {dst},term: {term},body: {body} }}'
def bag(ms): return 'Multiset::empty()'+''.join('.insert('+message(m)+')' for m in ms)
def node(n):
    t,v,h,k=n['disk']
    return f"node({n['term']},Role::{n['role']},{opt(n['vote'])},{seq(n['log'])},{n['commit']},{vset(n['responded'])},{vset(n['granted'])},{seq(n['matched'])},{t},{opt(v)},{seq(h)},{k})"
def state(s):
    ns='IMap::empty()'+''.join(f'.insert({i},{node(s["nodes"][i])})' for i in (1,2,3))
    vs='set!['+','.join(f'Ballot {{ voter: {v},term: {t},candidate: {i} }}' for v,t,i in sorted(s['votes']))+']'
    return f'LState {{ nodes: {ns},\n        pending: {bag(s["pending"])},\n        messages: {bag(s["messages"])},votes: {vs} }}'
def action(a):
    kind,*f=a
    if kind=='Receive': return f'Action::Receive {{ m: {message(f[0])},how: Receive::{f[1]} }}'
    if kind=='RequestVote': return f'Action::RequestVote {{ i: {f[0]},j: {f[1]} }}'
    if kind=='Append': return f'Action::Append {{ i: {f[0]},j: {f[1]},begin: {f[2]},end: {f[3]} }}'
    return f'Action::{kind}({f[0]})'
header='''//! Fixed 47-transition counterexample certificate. Every edge is checked by Verus.
//! Reproduce with scripts/build_tlaps_bench_etcd_counterexample.py.
use vstd::prelude::*;
use vstd::multiset::Multiset;
use super::etcd::*;
use super::etcd_election as election;
use super::etcd_origins as origins;
use super::temporal::Behavior;
verus! {
pub open spec fn constants() -> Constants { Constants { servers: set![1int,2int,3int].to_iset(),voters: set![1int,2int,3int] } }
pub open spec fn node(t: nat,r: Role,v: Option<int>,h: Seq<nat>,k: nat,responded: Set<int>,granted: Set<int>,matched: Seq<nat>,dt: nat,dv: Option<int>,dh: Seq<nat>,dk: nat) -> LServer {
    LServer { term: t,role: r,voted_for: v,log: h,commit: k,responded,granted,
        matched: IMap::empty().insert(1,matched[0]).insert(2,matched[1]).insert(3,matched[2]),
        disk: Disk { term: dt,voted_for: dv,log: dh,commit: dk } }
}
#[verifier::opaque]
pub open spec fn state(k: int) -> LState { match k {
'''
parts=[header]+[f'    _ if k == {k} => {state(s)},\n' for k,s in enumerate(states)]
parts+=['    _ => initial(constants()),\n} }\n#[verifier::opaque]\npub open spec fn action(k: int) -> Action { match k {\n']
parts += [f'    _ if k == {k} => {action(a)},\n' for k,a in enumerate(actions)]
parts += ['    _ => Action::Stutter,\n} }\n']
for k in range(len(actions)):
    parts += [f'''pub proof fn edge_{k}()
    ensures enabled(state({k}),constants(),action({k})),apply(state({k}),constants(),action({k})) == state({k+1})
{{
    reveal(state); reveal(action); reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    broadcast use Set::lemma_map_contains;
    broadcast use Multiset::dom_ensures;
    let s=state({k}); let a=action({k}); let u=apply(s,constants(),a); let v=state({k+1});
''']
    if actions[k][0]=='Ready':
        who=actions[k][1]
        for m in states[k]['pending']:
            if m[0]==who and m[3]=='VoteResponse' and m[4]:
                parts += [f'    election::record_released(s,{who},{message(m)});\n']
        parts += [f'    assert forall |b: Ballot| u.votes.contains(b) implies v.votes.contains(b) by {{\n        if !s.votes.contains(b) {{ let m=election::released_origin(s,{who},b); }}\n    }}\n']
    if actions[k][0]=='Append':
        parts += ['    assert(super::etcd::sub(s.nodes[1].log,1,2) =~= seq![1nat,3nat]);\n']
    if actions[k][0]=='AdvanceCommit':
        parts += ['    let agreed=agreed_indices(s.nodes[1],constants());\n    assert forall |index: int| 1 <= index <= 2 implies #[trigger] agreed.contains(index) by {\n        assert(constants().voters.filter(|j: int| s.nodes[1].matched[j] >= index) =~= set![1int,3int]);\n    }\n    assert(agreed =~= set![1int,2int]); origins::maximum_correct(agreed);\n    assert(agreed.contains(2)); assert(maximum(agreed) == 2);\n    assert(u.nodes[1].commit == 2);\n']
    parts += ['    assert(u.messages =~= v.messages); assert(u.pending =~= v.pending); assert(u.votes =~= v.votes);\n']
    for i in (1,2,3):
        parts += [f'    assert(u.nodes[{i}].log =~= v.nodes[{i}].log); assert(u.nodes[{i}].disk.log =~= v.nodes[{i}].disk.log);\n    assert(u.nodes[{i}].matched =~= v.nodes[{i}].matched);\n']
    parts += ['    assert(u.nodes =~= v.nodes);\n}\n']
parts += ['''pub proof fn edge(k: int)
    requires 0 <= k < 47
    ensures enabled(state(k),constants(),action(k)),apply(state(k),constants(),action(k)) == state(k+1)
{ match k {
''']
parts += [f'    _ if k == {k} => edge_{k}(),\n' for k in range(47)]
parts += ['''    _ => {},
} }
pub proof fn counterexample() -> (b: Behavior<LState>)
    ensures election::safety_spec(b,constants()),!leader_completeness(b[47],constants())
{
    reveal(state);
    let c=constants(); let s=state(0);
    broadcast use vstd::multiset::group_multiset_axioms;
    broadcast use Set::lemma_map_contains;
    broadcast use Multiset::dom_ensures;
    assert(s.nodes[1].matched =~= initial(c).nodes[1].matched);
    assert(s.nodes[2].matched =~= initial(c).nodes[2].matched);
    assert(s.nodes[3].matched =~= initial(c).nodes[3].matched);
    assert(s.nodes =~= initial(c).nodes);
    assert(s == initial(c));
    let b=IMap::new(|k: int| k >= 0,|k: int| state(if k < 47 { k } else { 47 }));
    assert forall |k: int| k >= 0 implies #[trigger] next(b[k],b[k+1],c) by {
        reveal(next);
        if k < 47 {
            edge(k); assert(enabled(b[k],c,action(k)) && b[k+1] == apply(b[k],c,action(k)));
        } else {
            reveal(enabled); reveal(apply);
            assert(enabled(b[k],c,Action::Stutter) && b[k+1] == apply(b[k],c,Action::Stutter));
        }
    }
    assert(b[47].nodes[1].commit == 2);
    assert(b[47].nodes[1].log[0] == 1);
    assert(b[47].nodes[2].role == Role::Leader && b[47].nodes[2].term == 2 && b[47].nodes[2].log[0] == 2);
    b
}
} // verus!
''']
(ROOT/'src/protocol/TLAPSBench/etcd_counterexample.rs').write_text(''.join(parts))
print('Wrote 48 ground states and 47 checked edges.')
