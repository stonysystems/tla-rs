//! Constructive non-vacuity check: a fast client response before base execution.
use vstd::prelude::*;
use super::{application as a, execution as e, ordering as o, recovery as r, registers as kv};

verus! {

pub type S = e::State<Map<int, int>, int>;
pub open spec fn initial() -> S {
    let c = kv::example_config();
    let empty = Map::new(c.nodes, |n: int| Set::<int>::empty());
    let order = o::State {
        calls: Set::empty(), base: Set::empty(), pending: Set::empty(), proposers: set![0int],
        queues: Map::new(c.nodes, |n: int| Seq::<int>::empty()), acks: empty,
        phase: 0, cut: Set::empty(), core: o::seeded(c, empty), recovery_ballot: -1, batch: Set::empty(),
    };
    e::State { order, base: Seq::empty(), pending: Seq::empty(), linear: Seq::empty(),
        available: Map::empty(), calls: Map::empty(), points: Map::empty(), replies: Map::empty(),
        returns: Map::empty(), clock: 0, application: kv::machine(kv::example_operations()) }
}
pub open spec fn ack_state(s: S, n: int) -> S {
    e::State { clock: s.clock + 1,
        order: o::State { acks: s.order.acks.insert(n, s.order.acks[n].insert(0)), ..s.order }, ..s }
}
pub proof fn fast_reply_is_reachable()
    ensures exists|states: Seq<S>, actions: Seq<e::Action>|
        e::behavior(states, actions, kv::example_config(), set![0int], kv::machine(kv::example_operations()))
        && states.len() == 8 && states[7].replies.dom().contains(0)
        && states[7].replies[0] == 0 && states[7].base.len() == 0,
{
    kv::example_application_is_valid();
    let c = kv::example_config();
    let m = kv::machine(kv::example_operations());
    let s0 = initial();
    let s1 = e::State { clock: 1, calls: s0.calls.insert(0, 0),
        order: o::State { calls: s0.order.calls.insert(0), ..s0.order }, ..s0 };
    let s2 = e::State { clock: 2,
        order: o::State { queues: s1.order.queues.insert(0, seq![0int]), ..s1.order }, ..s1 };
    let s3 = ack_state(s2, 0);
    let s4 = ack_state(s3, 1);
    let s5 = ack_state(s4, 2);
    let s6 = e::State { clock: 6,
        order: o::State { pending: set![0int], ..s5.order },
        pending: seq![0int], linear: seq![0int], points: s5.points.insert(0, 5),
        available: s5.available.insert(0, 0), ..s5 };
    let s7 = e::State { clock: 7, replies: s6.replies.insert(0, 0), returns: s6.returns.insert(0, 6), ..s6 };
    let states = seq![s0, s1, s2, s3, s4, s5, s6, s7];
    let actions = seq![
        e::Action::Protocol { action: o::Action::Invoke { command: 0 } },
        e::Action::Protocol { action: o::Action::Propose { proposer: 0, command: 0 } },
        e::Action::Protocol { action: o::Action::Acknowledge { node: 0, command: 0 } },
        e::Action::Protocol { action: o::Action::Acknowledge { node: 1, command: 0 } },
        e::Action::Protocol { action: o::Action::Acknowledge { node: 2, command: 0 } },
        e::Action::Protocol { action: o::Action::Fast { command: 0 } },
        e::Action::Reply { command: 0 },
    ];
    assert(r::init(s0.order.core, c));
    assert(o::init(s0.order, c, set![0int]));
    assert(e::init(s0, c, set![0int], m));
    assert(r::support(s5.order.acks, c.nodes, 0) =~= c.nodes);
    assert(o::certificate(s5.order, c, 0));
    assert(a::run(m, s5.base).state == Map::<int, int>::empty());
    assert forall|k: int| 0 <= k < actions.len()
        implies #[trigger] e::next(states[k], states[k + 1], c, actions[k]) by {
        if k == 0 {
            assert(o::invoke(s0.order, s1.order, c, 0));
            assert(e::protocol_step(s0, s1, c, o::Action::Invoke { command: 0 }));
        } else if k == 1 {
            assert(s1.order.queues[0].push(0) =~= seq![0int]);
            assert(o::propose(s1.order, s2.order, 0, 0));
            assert(e::protocol_step(s1, s2, c, o::Action::Propose { proposer: 0, command: 0 }));
        } else if k == 2 {
            assert(s2.order.queues[0][0] == 0);
            assert(s2.order.queues[0].contains(0));
            assert forall|y: int| #![trigger s2.order.base.contains(y)] s2.order.queues[0].contains(y) && !s2.order.base.contains(y)
                implies !c.conflict.contains((0, y)) by {
                let j = choose|j: int| 0 <= j < s2.order.queues[0].len() && s2.order.queues[0][j] == y;
                assert(j == 0 && y == 0);
            }
            assert(o::acknowledge(s2.order, s3.order, c, 0, 0));
            assert(e::protocol_step(s2, s3, c, o::Action::Acknowledge { node: 0, command: 0 }));
        } else if k == 3 {
            assert(o::acknowledge(s3.order, s4.order, c, 1, 0));
            assert(e::protocol_step(s3, s4, c, o::Action::Acknowledge { node: 1, command: 0 }));
        } else if k == 4 {
            assert(o::acknowledge(s4.order, s5.order, c, 2, 0));
            assert(e::protocol_step(s4, s5, c, o::Action::Acknowledge { node: 2, command: 0 }));
        } else if k == 5 {
            assert(o::fast(s5.order, s6.order, c, 0));
            assert(e::protocol_step(s5, s6, c, o::Action::Fast { command: 0 }));
        } else { assert(e::reply(s6, s7, 0)); }
    }
    assert(e::behavior(states, actions, c, set![0int], m));
    assert(states.len() == 8 && states[7].replies.dom().contains(0)
        && states[7].replies[0] == 0 && states[7].base.len() == 0);
}

} // verus!
