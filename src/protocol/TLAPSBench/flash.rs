//! Handwritten FLASH directory/cache model from FlashWithMutexModel.
//! Undefined is represented by -1. Node and data constants remain disjoint.
use vstd::prelude::*;
verus! {
pub enum Cache { I, S, E }
pub enum Req { None, Get, GetX }
pub enum Uni { None, Get, GetX, Put, PutX, Nak }
pub enum Inv { None, Inv, Ack }
pub enum Shared { None, ShWb, FAck }
pub struct Proc { pub cmd: Req, pub marked: bool, pub cache: Cache, pub data: int }
pub struct Dir {
    pub pending: bool, pub local: bool, pub dirty: bool, pub head_valid: bool,
    pub head: int, pub sharers_valid: bool, pub sharers: Set<int>, pub invalidating: Set<int>,
}
pub struct UniMsg { pub cmd: Uni, pub node: int, pub data: int }
pub struct WbMsg { pub pending: bool, pub node: int, pub data: int }
pub struct ShWbMsg { pub cmd: Shared, pub node: int, pub data: int }
pub struct Constants { pub nodes: Set<int>, pub data: ISet<int> }
pub struct LState {
    pub home: int, pub procs: Map<int, Proc>, pub dir: Dir, pub mem: int,
    pub uni: Map<int, UniMsg>, pub inv: Map<int, Inv>, pub replace: Map<int, bool>,
    pub wb: WbMsg, pub shwb: ShWbMsg, pub nakc: bool, pub current: int, pub previous: int,
    pub pending_src: int, pub pending_cmd: Option<Uni>, pub collecting: bool,
    pub forward_cmd: Uni, pub forward_src: int,
}
pub open spec fn valid_constants(c: Constants) -> bool {
    !c.nodes.is_empty() && !c.data.is_empty() && !c.nodes.contains(-1) && !c.data.contains(-1)
    && forall |n: int| #![trigger c.data.contains(n)] c.nodes.contains(n) ==> !c.data.contains(n)
}
pub open spec fn no_uni() -> UniMsg { UniMsg { cmd: Uni::None, node: -1, data: -1 } }
pub open spec fn initial(c: Constants, home: int, data: int) -> LState {
    LState {
        home, procs: Map::new(c.nodes, |n: int| Proc { cmd: Req::None, marked: false, cache: Cache::I, data: -1 }),
        dir: Dir { pending: false, local: false, dirty: false, head_valid: false, head: -1,
            sharers_valid: false, sharers: Set::empty(), invalidating: Set::empty() },
        mem: data, uni: Map::new(c.nodes, |n: int| no_uni()), inv: Map::new(c.nodes, |n: int| Inv::None),
        replace: Map::new(c.nodes, |n: int| false), wb: WbMsg { pending: false, node: -1, data: -1 },
        shwb: ShWbMsg { cmd: Shared::None, node: -1, data: -1 }, nakc: false,
        current: data, previous: data, pending_src: -1, pending_cmd: None, collecting: false,
        forward_cmd: Uni::None, forward_src: -1,
    }
}
pub open spec fn inv_nodes(s: LState, c: Constants, exclude: Set<int>) -> Set<int> {
    c.nodes.filter(|p: int| !exclude.contains(p)
        && (s.dir.sharers_valid && s.dir.sharers.contains(p) || s.dir.head_valid && s.dir.head == p))
}
pub open spec fn no_other_sharers(s: LState, req: int) -> bool {
    s.dir.head_valid ==> s.dir.head == req && s.dir.sharers.subset_of(set![req])
}
pub open spec fn invalid(p: Proc, mark: bool) -> Proc {
    Proc { cache: Cache::I, data: -1, marked: p.marked || mark && p.cmd == Req::Get, ..p }
}
pub open spec fn get_cmd(x: bool) -> Uni { if x { Uni::GetX } else { Uni::Get } }
pub open spec fn req_cmd(x: bool) -> Req { if x { Req::GetX } else { Req::Get } }
pub open spec fn home_ready(s: LState, x: bool) -> bool {
    s.procs[s.home].cmd == Req::None && (s.procs[s.home].cache == Cache::I || x && s.procs[s.home].cache == Cache::S)
}
pub open spec fn remote_request(s: LState, src: int, x: bool) -> bool {
    src != s.home && s.uni[src].cmd == get_cmd(x) && s.uni[src].node == s.home
    && (x || !s.replace[src])
}
pub enum Action {
    Store { src: int, data: int }, RemoteRequest { src: int, exclusive: bool },
    LocalForward { exclusive: bool }, LocalGet, LocalGetX,
    RemoteWriteback { dst: int }, LocalWriteback,
    RemoteReplace { src: int }, LocalReplace, ReceiveNak { dst: int }, ClearNak,
    LocalNak { src: int, exclusive: bool }, LocalRelay { src: int, exclusive: bool },
    LocalGrant { src: int, exclusive: bool }, RemoteNak { src: int, dst: int },
    RemoteGrant { src: int, dst: int, exclusive: bool },
    ReceivePut { dst: int }, ReceivePutX { dst: int }, Invalidate { dst: int },
    InvalidateAck { src: int }, ReceiveWriteback, ReceiveForwardAck, ReceiveSharedWriteback,
    ReceiveReplace { src: int }, Stutter,
}
#[verifier::opaque]
pub open spec fn enabled(s: LState, c: Constants, a: Action) -> bool {
    match a {
        Action::Store { src, data } => c.nodes.contains(src) && c.data.contains(data) && s.procs[src].cache == Cache::E,
        Action::RemoteRequest { src, exclusive } => c.nodes.contains(src) && src != s.home
            && s.procs[src].cmd == Req::None && s.procs[src].cache == Cache::I,
        Action::LocalForward { exclusive } => home_ready(s, exclusive) && !s.dir.pending && s.dir.dirty,
        Action::LocalGet => home_ready(s, false) && !s.dir.pending && !s.dir.dirty,
        Action::LocalGetX => home_ready(s, true) && !s.dir.pending && !s.dir.dirty,
        Action::RemoteWriteback { dst } => c.nodes.contains(dst) && dst != s.home && s.procs[dst].cmd == Req::None && s.procs[dst].cache == Cache::E,
        Action::LocalWriteback => s.procs[s.home].cmd == Req::None && s.procs[s.home].cache == Cache::E,
        Action::RemoteReplace { src } => c.nodes.contains(src) && src != s.home && s.procs[src].cmd == Req::None && s.procs[src].cache == Cache::S,
        Action::LocalReplace => s.procs[s.home].cmd == Req::None && s.procs[s.home].cache == Cache::S,
        Action::ReceiveNak { dst } => c.nodes.contains(dst) && s.uni[dst].cmd == Uni::Nak,
        Action::ClearNak => s.nakc,
        Action::LocalNak { src, exclusive } => c.nodes.contains(src) && remote_request(s, src, exclusive)
            && (s.dir.pending || s.dir.dirty && s.dir.local && s.procs[s.home].cache != Cache::E
                || s.dir.dirty && !s.dir.local && s.dir.head == src),
        Action::LocalRelay { src, exclusive } => c.nodes.contains(src) && remote_request(s, src, exclusive)
            && !s.dir.pending && s.dir.dirty && !s.dir.local && s.dir.head != src,
        Action::LocalGrant { src, exclusive } => c.nodes.contains(src) && remote_request(s, src, exclusive)
            && !s.dir.pending && (s.dir.dirty ==> s.dir.local && s.procs[s.home].cache == Cache::E),
        Action::RemoteNak { src, dst } => c.nodes.contains(src) && c.nodes.contains(dst) && src != dst && dst != s.home
            && (s.uni[src].cmd == Uni::Get || s.uni[src].cmd == Uni::GetX) && s.uni[src].node == dst && s.procs[dst].cache != Cache::E,
        Action::RemoteGrant { src, dst, exclusive } => c.nodes.contains(src) && c.nodes.contains(dst) && src != dst && dst != s.home
            && s.uni[src].cmd == get_cmd(exclusive) && s.uni[src].node == dst && s.procs[dst].cache == Cache::E,
        Action::ReceivePut { dst } => c.nodes.contains(dst) && s.uni[dst].cmd == Uni::Put,
        Action::ReceivePutX { dst } => c.nodes.contains(dst) && s.uni[dst].cmd == Uni::PutX && (dst == s.home || s.procs[dst].cmd == Req::GetX),
        Action::Invalidate { dst } => c.nodes.contains(dst) && dst != s.home && s.inv[dst] == Inv::Inv,
        Action::InvalidateAck { src } => c.nodes.contains(src) && src != s.home && s.inv[src] == Inv::Ack && s.dir.pending && s.dir.invalidating.contains(src),
        Action::ReceiveWriteback => s.wb.pending,
        Action::ReceiveForwardAck => s.shwb.cmd == Shared::FAck,
        Action::ReceiveSharedWriteback => s.shwb.cmd == Shared::ShWb,
        Action::ReceiveReplace { src } => c.nodes.contains(src) && s.replace[src],
        Action::Stutter => true,
    }
}
#[verifier::opaque]
pub open spec fn apply(s: LState, c: Constants, a: Action) -> LState {
    let h = s.home;
    let d = s.dir;
    match a {
        Action::Store { src, data } => LState { procs: s.procs.insert(src, Proc { data, ..s.procs[src] }), current: data, ..s },
        Action::RemoteRequest { src, exclusive } => LState {
            procs: s.procs.insert(src, Proc { cmd: req_cmd(exclusive), ..s.procs[src] }),
            uni: s.uni.insert(src, UniMsg { cmd: get_cmd(exclusive), node: h, data: -1 }), ..s },
        Action::LocalForward { exclusive } => LState {
            procs: s.procs.insert(h, Proc { cmd: req_cmd(exclusive), ..s.procs[h] }),
            dir: Dir { pending: true, ..d }, uni: s.uni.insert(h, UniMsg { cmd: get_cmd(exclusive), node: d.head, data: -1 }),
            forward_cmd: if d.head != h { get_cmd(exclusive) } else { s.forward_cmd },
            pending_src: h, pending_cmd: Some(get_cmd(exclusive)), collecting: false, ..s },
        Action::LocalGet => LState {
            dir: Dir { local: true, ..d }, procs: s.procs.insert(h, Proc { cmd: Req::None, marked: false,
                cache: if s.procs[h].marked { Cache::I } else { Cache::S }, data: if s.procs[h].marked { -1 } else { s.mem } }), ..s },
        Action::LocalGetX => {
            let u = LState { procs: s.procs.insert(h, Proc { cmd: Req::None, marked: false, cache: Cache::E, data: s.mem }), ..s };
            if d.head_valid {
                let targets = inv_nodes(s, c, set![h]);
                LState { dir: Dir { pending: true, local: true, dirty: true, head_valid: false, head: -1,
                    sharers_valid: false, sharers: Set::empty(), invalidating: targets },
                    inv: Map::new(c.nodes, |p: int| if targets.contains(p) { Inv::Inv } else { Inv::None }),
                    pending_src: h, collecting: true, previous: s.current, ..u }
            } else { LState { dir: Dir { local: true, dirty: true, ..d }, ..u } }
        },
        Action::RemoteWriteback { dst } => LState { procs: s.procs.insert(dst, invalid(s.procs[dst], false)),
            wb: WbMsg { pending: true, node: dst, data: s.procs[dst].data }, ..s },
        Action::LocalWriteback => LState { procs: s.procs.insert(h, invalid(s.procs[h], false)),
            dir: Dir { dirty: false, local: if d.pending { d.local } else { false }, ..d }, mem: s.procs[h].data, ..s },
        Action::RemoteReplace { src } => LState { procs: s.procs.insert(src, invalid(s.procs[src], false)), replace: s.replace.insert(src, true), ..s },
        Action::LocalReplace => LState { procs: s.procs.insert(h, invalid(s.procs[h], false)), dir: Dir { local: false, ..d }, ..s },
        Action::ReceiveNak { dst } => LState { uni: s.uni.insert(dst, no_uni()), procs: s.procs.insert(dst, Proc { cmd: Req::None, marked: false, ..s.procs[dst] }), ..s },
        Action::ClearNak => LState { nakc: false, dir: Dir { pending: false, ..d }, ..s },
        Action::LocalNak { src, exclusive } => LState { uni: s.uni.insert(src, UniMsg { cmd: Uni::Nak, node: h, data: -1 }), ..s },
        Action::LocalRelay { src, exclusive } => LState { dir: Dir { pending: true, ..d },
            uni: s.uni.insert(src, UniMsg { cmd: get_cmd(exclusive), node: d.head, data: -1 }),
            forward_cmd: if d.head != h { get_cmd(exclusive) } else { s.forward_cmd },
            pending_src: src, pending_cmd: Some(get_cmd(exclusive)), collecting: false, ..s },
        Action::LocalGrant { src, exclusive } => if !exclusive {
            LState {
                dir: if d.dirty { Dir { dirty: false, head_valid: true, head: src, ..d } }
                    else if d.head_valid { Dir { sharers_valid: true, sharers: d.sharers.insert(src), invalidating: d.sharers.insert(src), ..d } }
                    else { Dir { head_valid: true, head: src, ..d } },
                mem: if d.dirty { s.procs[h].data } else { s.mem },
                procs: if d.dirty { s.procs.insert(h, Proc { cache: Cache::S, ..s.procs[h] }) } else { s.procs },
                uni: s.uni.insert(src, UniMsg { cmd: Uni::Put, node: h, data: if d.dirty { s.procs[h].data } else { s.mem } }), ..s }
        } else {
            let u = LState { uni: s.uni.insert(src, UniMsg { cmd: Uni::PutX, node: h, data: if d.dirty { s.procs[h].data } else { s.mem } }), ..s };
            if d.dirty || no_other_sharers(s, src) {
                LState { dir: Dir { local: false, dirty: true, head_valid: true, head: src,
                        sharers_valid: false, sharers: Set::empty(), invalidating: Set::empty(), ..d },
                    procs: s.procs.insert(h, invalid(s.procs[h], !d.dirty && d.local)), ..u }
            } else {
                let targets = inv_nodes(s, c, set![h, src]);
                LState { dir: Dir { pending: true, local: false, dirty: true, head_valid: true, head: src,
                        sharers_valid: false, sharers: Set::empty(), invalidating: targets },
                    procs: if d.local { s.procs.insert(h, invalid(s.procs[h], true)) } else { s.procs },
                    inv: Map::new(c.nodes, |p: int| if targets.contains(p) { Inv::Inv } else { Inv::None }),
                    pending_src: src, pending_cmd: Some(Uni::GetX), collecting: true, previous: s.current, ..u }
            }
        },
        Action::RemoteNak { src, dst } => LState {
            uni: s.uni.insert(src, UniMsg { cmd: Uni::Nak, node: dst, data: -1 }), nakc: true,
            forward_cmd: Uni::None, forward_src: src, ..s },
        Action::RemoteGrant { src, dst, exclusive } => LState {
            procs: s.procs.insert(dst, if exclusive { invalid(s.procs[dst], false) } else { Proc { cache: Cache::S, ..s.procs[dst] } }),
            uni: s.uni.insert(src, UniMsg { cmd: if exclusive { Uni::PutX } else { Uni::Put }, node: dst, data: s.procs[dst].data }),
            forward_cmd: Uni::None, forward_src: src,
            shwb: if src == h { s.shwb } else { ShWbMsg { cmd: if exclusive { Shared::FAck } else { Shared::ShWb },
                node: src, data: if exclusive { -1 } else { s.procs[dst].data } } }, ..s },
        Action::ReceivePut { dst } => LState {
            uni: s.uni.insert(dst, no_uni()), procs: s.procs.insert(dst, Proc { cmd: Req::None, marked: false,
                cache: if s.procs[dst].marked { Cache::I } else { Cache::S }, data: if s.procs[dst].marked { -1 } else { s.uni[dst].data } }),
            dir: if dst == h { Dir { pending: false, dirty: false, local: true, ..d } } else { d },
            mem: if dst == h { s.uni[h].data } else { s.mem }, ..s },
        Action::ReceivePutX { dst } => LState {
            uni: s.uni.insert(dst, no_uni()), procs: s.procs.insert(dst, Proc { cmd: Req::None, marked: false, cache: Cache::E, data: s.uni[dst].data }),
            dir: if dst == h { Dir { pending: false, local: true, head_valid: false, head: -1, ..d } } else { d }, ..s },
        Action::Invalidate { dst } => LState { inv: s.inv.insert(dst, Inv::Ack), procs: s.procs.insert(dst, invalid(s.procs[dst], true)), ..s },
        Action::InvalidateAck { src } => {
            let remaining = d.invalidating.remove(src);
            LState { inv: s.inv.insert(src, Inv::None),
                dir: if remaining.is_empty() { Dir { invalidating: remaining, pending: false, local: if d.local && !d.dirty { false } else { d.local }, ..d } }
                    else { Dir { invalidating: remaining, ..d } },
                collecting: if remaining.is_empty() { false } else { s.collecting }, ..s }
        },
        Action::ReceiveWriteback => LState { wb: WbMsg { pending: false, node: -1, data: -1 },
            dir: Dir { dirty: false, head_valid: false, head: -1, ..d }, mem: s.wb.data, ..s },
        Action::ReceiveForwardAck => LState { shwb: ShWbMsg { cmd: Shared::None, node: -1, data: -1 },
            dir: Dir { pending: false, head: if d.dirty { s.shwb.node } else { d.head }, ..d }, ..s },
        Action::ReceiveSharedWriteback => LState { shwb: ShWbMsg { cmd: Shared::None, node: -1, data: -1 },
            dir: Dir { pending: false, dirty: false, sharers_valid: true, sharers: d.sharers.insert(s.shwb.node), invalidating: d.sharers.insert(s.shwb.node), ..d }, mem: s.shwb.data, ..s },
        Action::ReceiveReplace { src } => LState { replace: s.replace.insert(src, false),
            dir: Dir { sharers: if d.sharers_valid { d.sharers.remove(src) } else { d.sharers },
                invalidating: if d.sharers_valid { d.invalidating.remove(src) } else { d.invalidating }, ..d }, ..s },
        Action::Stutter => s,
    }
}
#[verifier::opaque]
pub open spec fn next(s: LState, u: LState, c: Constants) -> bool {
    exists |a: Action| #[trigger] enabled(s, c, a) && u == apply(s, c, a)
}
pub open spec fn node_u(c: Constants, n: int) -> bool { n == -1 || c.nodes.contains(n) }
pub open spec fn data_u(c: Constants, d: int) -> bool { d == -1 || c.data.contains(d) }
pub open spec fn type_ok(s: LState, c: Constants) -> bool {
    c.nodes.contains(s.home) && c.data.contains(s.mem) && c.data.contains(s.current) && c.data.contains(s.previous)
    && s.procs.dom() == c.nodes && s.uni.dom() == c.nodes && s.inv.dom() == c.nodes && s.replace.dom() == c.nodes
    && node_u(c, s.dir.head) && s.dir.sharers.subset_of(c.nodes) && s.dir.invalidating.subset_of(c.nodes)
    && node_u(c, s.wb.node) && data_u(c, s.wb.data) && node_u(c, s.shwb.node) && data_u(c, s.shwb.data)
    && node_u(c, s.pending_src) && node_u(c, s.forward_src)
    && forall |p: int| #![trigger c.nodes.contains(p)] c.nodes.contains(p) ==> data_u(c, s.procs[p].data)
        && node_u(c, s.uni[p].node) && data_u(c, s.uni[p].data)
}
pub open spec fn cache_data(s: LState, c: Constants) -> bool {
    forall |p: int| #![trigger c.nodes.contains(p)] c.nodes.contains(p) ==>
        (s.procs[p].cache == Cache::E ==> s.procs[p].data == s.current)
        && (s.procs[p].cache == Cache::S ==> s.procs[p].data == if s.collecting { s.previous } else { s.current })
}
pub open spec fn mem_data(s: LState) -> bool { !s.dir.dirty ==> s.mem == s.current }
pub open spec fn lemma_1(s: LState, c: Constants) -> bool {
    forall |p: int| #![trigger c.nodes.contains(p)] c.nodes.contains(p) && s.procs[p].cache == Cache::E ==>
        s.dir.dirty && !s.wb.pending && s.shwb.cmd != Shared::ShWb && s.uni[s.home].cmd != Uni::Put
        && (forall |q: int| #![trigger c.nodes.contains(q)] c.nodes.contains(q) ==> (q != p ==> s.procs[q].cache != Cache::E) && s.uni[q].cmd != Uni::PutX)
}
pub open spec fn lemma_2_3(s: LState, c: Constants, exclusive: bool) -> bool {
    forall |src: int, dst: int| #![trigger c.nodes.contains(src), c.nodes.contains(dst)] c.nodes.contains(src) && c.nodes.contains(dst) && src != dst && dst != s.home
        && s.uni[src].cmd == get_cmd(exclusive) && s.uni[src].node == dst ==>
        s.dir.pending && !s.dir.local && s.pending_src == src && s.forward_cmd == get_cmd(exclusive)
}
pub open spec fn lemma_4(s: LState, c: Constants) -> bool {
    forall |p: int| #![trigger s.inv[p]] c.nodes.contains(p) && p != s.home && s.inv[p] == Inv::Ack ==>
        s.dir.pending && s.collecting && !s.nakc && s.shwb.cmd == Shared::None
        && (forall |q: int| #![trigger c.nodes.contains(q)] c.nodes.contains(q) ==>
            ((s.uni[q].cmd == Uni::Get || s.uni[q].cmd == Uni::GetX) ==> s.uni[q].node == s.home)
            && (s.uni[q].cmd == Uni::PutX ==> s.uni[q].node == s.home && s.pending_src == q))
}
} // verus!
