//! Explicit watermark production and delivery. No action tests a global safety
//! bound. The abstract model's Publish exists only as a refinement target.
use vstd::prelude::*;
use vstd::imap::IMap as Map;
use vstd::iset::ISet as Set;
use super::model as abs;
use super::model::{Bound, Stream, Tx, Config, bound_le, endpoint, shard, stream};
use super::watermark_math::*;

verus! {

pub struct Settings { pub protocol: Config, pub observers: int }
pub struct WorkerReport { pub stream: Stream, pub value: Bound, pub sealed: bool }
pub struct Gossip { pub dst: int, pub epoch: nat, pub shard: int, pub value: Bound, pub sealed: bool }
pub struct State {
    // core.wm is a ghost join of all delivered observer vectors. Protocol
    // decisions read views instead; the join is used only for refinement.
    pub core: abs::State,
    pub reports: Map<Stream, Bound>,
    pub sealed_reports: Set<Stream>,
    pub local: Map<(nat, int), Bound>,
    pub sealed_local: Set<(nat, int)>,
    pub worker_net: Set<WorkerReport>,
    pub gossip_net: Set<Gossip>,
    pub views: Map<(int, nat, int), Bound>,
    pub sealed_views: Set<(int, nat, int)>,
}
pub open spec fn observer(c: Settings, o: int) -> bool { 0 <= o < c.observers }
pub open spec fn view(c: Settings, s: State, o: int) -> abs::State {
    abs::State { wm: Map::new(|p: (nat, int)| shard(c.protocol, p.1),
        |p: (nat, int)| s.views[(o, p.0, p.1)]), ..s.core }
}
pub open spec fn initial(c: Settings, s: State) -> bool {
    &&& c.observers > 0 && abs::initial(c.protocol, s.core)
    &&& s.reports == Map::new(|k: Stream| stream(c.protocol, k), |k| Bound::Finite(0))
    &&& s.local == Map::new(|p: (nat, int)| shard(c.protocol, p.1), |p| Bound::Finite(0))
    &&& s.views == Map::new(|p: (int, nat, int)| observer(c, p.0) && shard(c.protocol, p.2), |p| Bound::Finite(0))
    &&& s.sealed_reports == Set::<Stream>::empty()
    &&& s.sealed_local == Set::<(nat, int)>::empty()
    &&& s.sealed_views == Set::<(int, nat, int)>::empty()
    &&& s.worker_net == Set::<WorkerReport>::empty()
    &&& s.gossip_net == Set::<Gossip>::empty()
}
pub open spec fn allowed(a: abs::Action) -> bool {
    match a {
        abs::Action::Publish { .. } | abs::Action::Finalize { .. } | abs::Action::Rollback { .. } => false,
        _ => true,
    }
}
pub open spec fn core_result(c: Settings, s: State, o: int, a: abs::Action) -> State {
    // Allowed actions do not modify wm. Their enabling conditions below use
    // only the observer's actual view, while the ghost join is retained.
    State { core: abs::effect(c.protocol, s.core, a), ..s }
}
pub open spec fn report(s: State, k: Stream) -> WorkerReport {
    WorkerReport { stream: k, value: endpoint(s.core, k), sealed: s.core.closed.contains(k) }
}
pub open spec fn sample_result(s: State, k: Stream) -> State {
    State { worker_net: s.worker_net.insert(report(s, k)), ..s }
}
pub open spec fn receive_worker_result(s: State, m: WorkerReport) -> State {
    State { reports: s.reports.insert(m.stream, bmax(s.reports[m.stream], m.value)),
        sealed_reports: if m.sealed { s.sealed_reports.insert(m.stream) } else { s.sealed_reports }, ..s }
}
pub open spec fn all_reported(c: Settings, s: State, e: nat, sh: int) -> bool {
    forall|w: int| 0 <= w < c.protocol.workers ==> #[trigger] s.sealed_reports.contains(worker(e, sh, w))
}
pub open spec fn compute_result(c: Settings, s: State, e: nat, sh: int) -> State {
    State { local: s.local.insert((e, sh), minimum(s.reports, e, sh, c.protocol.workers as nat)),
        sealed_local: if all_reported(c, s, e, sh) { s.sealed_local.insert((e, sh)) } else { s.sealed_local }, ..s }
}
pub open spec fn gossip(s: State, e: nat, sh: int, o: int) -> Gossip {
    Gossip { dst: o, epoch: e, shard: sh, value: s.local[(e, sh)], sealed: s.sealed_local.contains((e, sh)) }
}
pub open spec fn send_result(s: State, e: nat, sh: int, o: int) -> State {
    State { gossip_net: s.gossip_net.insert(gossip(s, e, sh, o)), ..s }
}
pub open spec fn receive_result(c: Settings, s: State, m: Gossip) -> State {
    State { views: s.views.insert((m.dst, m.epoch, m.shard), bmax(s.views[(m.dst, m.epoch, m.shard)], m.value)),
        sealed_views: if m.sealed { s.sealed_views.insert((m.dst, m.epoch, m.shard)) } else { s.sealed_views },
        core: abs::publish_result(c.protocol, s.core, m.epoch, m.shard, bmax(s.core.wm[(m.epoch, m.shard)], m.value)), ..s }
}
pub open spec fn all_final(c: Settings, s: State, o: int, e: nat) -> bool {
    forall|sh: int| shard(c.protocol, sh) ==> #[trigger] s.sealed_views.contains((o, e, sh))
}
pub open spec fn finish_result(c: Settings, s: State, e: nat) -> State {
    State { core: abs::finalize_result(c.protocol, s.core, e), ..s }
}
pub open spec fn rollback_result(c: Settings, s: State, id: int, sh: int) -> State {
    State { core: abs::rollback_result(c.protocol, s.core, id, sh), ..s }
}
pub enum Action {
    Core { observer: int, action: abs::Action },
    Sample { stream: Stream }, ReceiveWorker { report: WorkerReport },
    Compute { epoch: nat, shard: int }, Send { epoch: nat, shard: int, observer: int },
    Receive { message: Gossip }, Finish { epoch: nat, observer: int },
    Rollback { id: int, shard: int, observer: int },
    DropWorker { report: WorkerReport }, DropGossip { message: Gossip },
    RestartObserver { observer: int }, RestartCollector { epoch: nat, shard: int }, Stutter,
}
pub open spec fn resets(a: Action, e: nat, sh: int) -> bool {
    match a { Action::RestartCollector { epoch, shard } => epoch == e && shard == sh, _ => false }
}
pub open spec fn effect(c: Settings, s: State, a: Action) -> State {
    match a {
        Action::Core { observer, action } => core_result(c, s, observer, action),
        Action::Sample { stream } => sample_result(s, stream),
        Action::ReceiveWorker { report } => receive_worker_result(s, report),
        Action::Compute { epoch, shard } => compute_result(c, s, epoch, shard),
        Action::Send { epoch, shard, observer } => send_result(s, epoch, shard, observer),
        Action::Receive { message } => receive_result(c, s, message),
        Action::Finish { epoch, observer } => finish_result(c, s, epoch),
        Action::Rollback { id, shard, observer } => rollback_result(c, s, id, shard),
        Action::DropWorker { report } => State { worker_net: s.worker_net.remove(report), ..s },
        Action::DropGossip { message } => State { gossip_net: s.gossip_net.remove(message), ..s },
        Action::RestartCollector { epoch: e, shard: sh } => State {
            reports: Map::new(|k: Stream| s.reports.dom().contains(k),
                |k: Stream| if k.epoch == e && k.shard == sh { Bound::Finite(0) } else { s.reports[k] }),
            sealed_reports: s.sealed_reports.filter(|k: Stream| k.epoch != e || k.shard != sh),
            local: s.local.insert((e, sh), Bound::Finite(0)), sealed_local: s.sealed_local.remove((e, sh)), ..s },
        Action::RestartObserver { observer: o } => State {
            views: Map::new(|p: (int, nat, int)| s.views.dom().contains(p),
                |p: (int, nat, int)| if p.0 == o { Bound::Finite(0) } else { s.views[p] }),
            sealed_views: s.sealed_views.filter(|p: (int, nat, int)| p.0 != o), ..s },
        Action::Stutter => s,
    }
}
#[verifier::opaque]
pub open spec fn step(c: Settings, s: State, z: State, a: Action) -> bool {
    &&& z == effect(c, s, a)
    &&& match a {
        Action::Core { observer: o, action } => observer(c, o) && allowed(action)
            && abs::step(c.protocol, view(c, s, o), abs::effect(c.protocol, view(c, s, o), action), action),
        Action::Sample { stream: k } => stream(c.protocol, k),
        Action::ReceiveWorker { report: m } => s.worker_net.contains(m),
        Action::Compute { epoch: e, shard: sh } => shard(c.protocol, sh),
        Action::Send { epoch: e, shard: sh, observer: o } => shard(c.protocol, sh) && observer(c, o),
        Action::Receive { message: m } => s.gossip_net.contains(m),
        Action::Finish { epoch: e, observer: o } => observer(c, o) && e < s.core.epoch && all_final(c, s, o, e),
        Action::Rollback { id, shard: sh, observer: o } => observer(c, o)
            && s.core.tx.dom().contains(id) && s.core.installed.contains((id, sh))
            && s.core.finalized.contains(s.core.tx[id].epoch)
            && all_final(c, s, o, s.core.tx[id].epoch)
            && !abs::below_wm(c.protocol, view(c, s, o), s.core.tx[id]),
        Action::DropWorker { report } => true,
        Action::DropGossip { message } => true,
        Action::RestartCollector { epoch: e, shard: sh } => shard(c.protocol, sh),
        Action::RestartObserver { observer: o } => observer(c, o),
        Action::Stutter => true,
    }
}
pub open spec fn next(c: Settings, s: State, z: State) -> bool {
    exists|a: Action| #[trigger] step(c, s, z, a)
}
pub open spec fn behavior(c: Settings, h: Seq<State>) -> bool {
    h.len() > 0 && initial(c, h[0]) &&
        forall|i: int| 0 <= i < h.len() - 1 ==> #[trigger] next(c, h[i], h[i+1])
}
} // verus!
