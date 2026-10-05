//! State of the CausalMesh model: versions, dual caches, FIFO chains, clients
//! and a ghost history of client operations.
use vstd::prelude::*;
use super::vc::*;

verus! {

/// A write, identified by its origin server and the vector clock it received.
pub struct Version {
    pub key: int,
    pub value: int,
    pub vc: VC,
    /// The client's deps merged with its own earlier writes (Fact 3).
    pub deps: Map<int, VC>,
    pub origin: int,
}

/// A consistent-cache entry, or a value a client observed: no dependencies.
pub struct Entry { pub value: int, pub vc: VC }

pub struct Server {
    pub gvc: VC,
    pub icache: Set<Version>,
    pub ccache: Map<int, Entry>,
}

/// A propagation message. Its receiver is the server `hop` steps past `origin`.
pub struct Msg { pub version: Version, pub hop: nat }

pub struct Client {
    pub deps: Map<int, VC>,
    pub local: Map<int, Entry>,
}

/// Ghost record of one client operation. `ctx` is the set of writes that
/// happen before the operation or that it observes, including itself.
pub enum Event {
    Write { client: int, version: Version, ctx: Set<Version> },
    Read { client: int, key: int, server_vc: VC, vc: VC, value: int, ctx: Set<Version> },
    Fork { parent: int, child: int, ctx: Set<Version> },
}

/// `rounds` is 2 for the protocol of arXiv v1/v2 and 1 for the VLDB version.
/// The merged value of concurrent versions is left open (any contributor);
/// the paper's deterministic tie-break is one instance.
pub struct Constants {
    pub n: nat,
    pub rounds: nat,
}

pub struct State {
    pub servers: Seq<Server>,
    /// chans[s] is the FIFO queue from s to its successor (Fact 2).
    pub chans: Seq<Seq<Msg>>,
    pub clients: Map<int, Client>,
    // Ghost state below; no protocol guard reads it.
    pub writes: Set<Version>,
    pub seen: Seq<Set<Version>>,
    pub sent: Seq<Seq<Msg>>,
    pub ctx: Map<int, Set<Version>>,
    pub history: Seq<Event>,
}

pub open spec fn valid_constants(c: Constants) -> bool { c.n >= 1 && c.rounds >= 1 }

pub open spec fn initial_entry(n: nat) -> Entry { Entry { value: 0, vc: zero(n) } }

pub open spec fn entry(s: Server, n: nat, k: int) -> Entry {
    if s.ccache.dom().contains(k) { s.ccache[k] } else { initial_entry(n) }
}

pub open spec fn dep(d: Map<int, VC>, n: nat, k: int) -> VC {
    if d.dom().contains(k) { d[k] } else { zero(n) }
}

pub open spec fn local_entry(cl: Client, n: nat, k: int) -> Entry {
    if cl.local.dom().contains(k) { cl.local[k] } else { initial_entry(n) }
}

pub open spec fn empty_server(n: nat) -> Server {
    Server { gvc: zero(n), icache: Set::empty(), ccache: Map::empty() }
}

pub open spec fn empty_client() -> Client { Client { deps: Map::empty(), local: Map::empty() } }

} // verus!
