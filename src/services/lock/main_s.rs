#![allow(unused_imports)]
use vstd::prelude::*;
use std::collections::HashMap;

use crate::common::framework::args_t::{abstractify_args, Args};
use crate::common::framework::environment_s::*;
use crate::common::logic::*;
use crate::common::native::io_s::*;
use crate::implementation::common::cmd_line_parser_i::{parse_args, parse_end_points};
use crate::implementation::lock::host_i::HostState;
use crate::implementation::lock::host_s::EventResults;
use crate::implementation::lock::message_i::{abstractify_net_packet_to_lock_packet, CMessage, lock_demarshal_data};
use crate::implementation::lock::netlock_i::{
    abstractify_net_event_to_lock_io, abstractify_raw_log_to_ios, lock_marshal_data_injective, net_packet_is_abstractable,
};
use crate::implementation::lock::node_i::{valid_config, ConcreteConfig};
use crate::protocol::lock::distributed_system_procotol_i::{ls_init, ls_next, AbstractLSState};
use crate::protocol::lock::node::{AbstractConfig, AbstractNode};
use crate::protocol::lock::types::{LockEnvironment, LockIo, LockMessage, LockPacket};
use vstd::hash_map::HashMapWithView;
use vstd::seq_lib::group_seq_properties;
use vstd::set_lib::group_set_properties;
use vstd::view::*;
use vstd::{modes::*, prelude::*, seq::*, set::*, *};
use crate::protocol::lock::distributed_system_procotol_i::*;
use crate::protocol::lock::node::*;
use crate::services::lock::abstractservice_s::*;
use crate::protocol::lock::refinement_proof_i::*;
use super::distributed_system_s::{
    abstractify_concrete_env_sent_packets, abstractify_concrete_environment,
    concrete_env_is_abstractable, ConcreteEnvironment, DSStateLock,
};

verus! {
    pub open spec fn is_valid_behavior(config: ConcreteConfig, db: Seq<DSStateLock>) -> bool {
        &&& db.len() > 0
        &&& DSStateLock::init_requires(db[0], config)
        &&&  forall |i: int, j: int| #![trigger DSStateLock::next_requires(db[i], db[j])] 0 <= i < db.len() - 1 && j == i+1 ==> DSStateLock::next_requires(db[i], db[j])
    }

    pub open spec fn is_valid_behavior_ls(config:ConcreteConfig, db:Seq<AbstractLSState>) -> bool
    {
        &&& db.len() > 0
        &&& ls_init(db[0], abstractify_end_points(config))
        &&& forall |i: int, j: int| #![trigger ls_next(db[i], db[j])] 0 <= i < db.len() - 1 && j == i+1 ==> ls_next(db[i], db[i+1])
    }

    pub proof fn lemma_deduce_transition_from_ds_behavior(
        config:ConcreteConfig,
        db:Seq<DSStateLock>,
        i:int
        )
        requires
            is_valid_behavior(config, db),
            0 <= i < db.len() - 1,
        ensures
            DSStateLock::next_requires(db[i], db[i+1])
    {

    }

    pub proof fn lemma_ds_next_offset(db:Seq<DSStateLock>, index:int)
        requires
            db.len() > 0,
            0 < index < db.len(),
            forall |i: int, j: int| #![trigger DSStateLock::next_requires(db[i], db[j])] 0 <= i < db.len() - 1 && j == i+1 ==> DSStateLock::next_requires(db[i], db[j]),
        ensures
            DSStateLock::next_requires(db[index-1], db[index]),
    {
        let i = index - 1;
        assert(DSStateLock::next_requires(db[i], db[i+1])); // OBSERVE trigger for the forall
    }

    pub proof fn lemma_ds_consistency(config:ConcreteConfig, db:Seq<DSStateLock>, i:int)
    requires
        is_valid_behavior(config, db),
        0 <= i < db.len(),
    ensures
        abstractify_end_points(db[i].config) =~= abstractify_end_points(config),
        db[i].servers.dom() =~= db[0].servers.dom(),
    decreases
        i
    {
        if i == 0 {
            assert(abstractify_end_points(db[i].config) =~= abstractify_end_points(config));
            assert(db[i].servers.dom() =~= db[0].servers.dom());
        } else {
            lemma_ds_consistency(config, db, i-1);
            lemma_deduce_transition_from_ds_behavior(config, db, i-1);

            assert(forall |server: AbstractEndPoint| db[i-1].servers.contains_key(server) ==> db[i].servers.contains_key(server));
            assert(forall |server: AbstractEndPoint| db[i].servers.contains_key(server) ==> db[i-1].servers.contains_key(server));
        }
    }


    pub proof fn lemma_is_valid_env_step(de: ConcreteEnvironment, le: LockEnvironment)
        requires
            IsValidLEnvStep(de, de.nextStep),
            de.nextStep is LEnvStepHostIos,
            concrete_env_is_abstractable(de),
            abstractify_concrete_environment(de) == le,
        ensures
            IsValidLEnvStep(le, le.nextStep),
    {
        let id = de.nextStep->actor;
        let ios = de.nextStep->ios;
        let r_ios = le.nextStep->ios;

        assert(LIoOpSeqCompatibleWithReduction(r_ios));

        assert forall |io| #![auto] r_ios.contains(io) implies IsValidLIoOp(io, id, le) by {
            assert(forall |j: int| #![auto] 0 <= j < r_ios.len() ==> abstractify_net_event_to_lock_io(ios[j]) == r_ios[j]);
            assert(forall |j: int| #![auto] 0 <= j < r_ios.len() ==> IsValidLIoOp::<AbstractEndPoint, Seq<u8>>(ios[j], id, de));
        };
    }


    pub proof fn lemma_ios_relations(ios:Seq<NetEvent>, r_ios:Seq<LockIo>) -> (rc: (Set<NetPacket>, Set<LockPacket>))
        requires
            r_ios =~= abstractify_raw_log_to_ios(ios),
        ensures
        ({
            let (sends, r_sends) = rc;

            &&& sends =~= ios.filter(|io:NetEvent| io is Send).map_values(|io: NetEvent| io->s).to_set()
            &&& r_sends =~=  r_ios.filter(|io:LockIo| io is Send).map_values(|io: LockIo| io->s).to_set()
            &&& r_sends == abstractify_concrete_env_sent_packets(sends)
            &&& sends.finite()
            &&& r_sends.finite()
        }),
    {
        assert(r_ios.len() == ios.len());

        let sends = ios.filter(|io:NetEvent| io is Send).map_values(|io: NetEvent| io->s).to_set();

        let r_sends = r_ios.filter(|io:LockIo| io is Send).map_values(|io: LockIo| io->s).to_set();

        let refined_sends = abstractify_concrete_env_sent_packets(sends);

        // Prove r_sends == refined_sends by showing bidirectional containment.
        // Key: r_ios[j] = abstractify_io(ios[j]), and abstractify preserves Send variant,
        // so both sets are { abstractify_pkt(ios[j]->s) | ios[j] is Send }.
        let abs_io = |evt: NetEvent| abstractify_net_event_to_lock_io(evt);
        let abs_pkt = |p: NetPacket| abstractify_net_packet_to_lock_packet(p);
        let pred_c = |io: NetEvent| io is Send;
        let pred_r = |io: LockIo| io is Send;
        let ext_c = |io: NetEvent| io->s;
        let ext_r = |io: LockIo| io->s;

        // Bridge: abstractify preserves Send variant and packet extraction
        assert forall |j: int| 0 <= j < ios.len() implies
            (r_ios[j] is Send <==> ios[j] is Send) &&
            (ios[j] is Send ==> r_ios[j]->s == abs_pkt(ios[j]->s))
        by {
            assert(r_ios[j] =~= abs_io(ios[j]));
        };

        // Forward: r_sends ⊆ refined_sends
        assert forall |r: LockPacket| r_sends.contains(r) implies refined_sends.contains(r) by {
            broadcast use vstd::seq_lib::group_filter_ensures;
            // r ∈ r_ios.filter(Send).map_values(->s).to_set() means the seq contains r
            let mapped_r = r_ios.filter(pred_r).map_values(ext_r);
            assert(mapped_r.contains(r));
            let k = choose |k: int| 0 <= k < mapped_r.len() && mapped_r[k] == r;
            // filtered_r[k] is Send (from filter_pred broadcast)
            let io_r = r_ios.filter(pred_r)[k];
            // io_r ∈ r_ios (filter is subset)
            r_ios.lemma_filter_contains_rev(pred_r, io_r);
            let j = choose |j: int| 0 <= j < r_ios.len() && r_ios[j] == io_r;
            // ios[j] is Send (variant preserved) and ios[j]->s ∈ sends
            assert(ios[j] is Send);
            let pkt = ios[j]->s;
            // ios.filter(Send).contains(ios[j]) (from filter_contains broadcast)
            let filtered_c = ios.filter(pred_c);
            assert(filtered_c.contains(ios[j]));
            let k2 = choose |k2: int| 0 <= k2 < filtered_c.len() && filtered_c[k2] == ios[j];
            assert(filtered_c.map_values(ext_c)[k2] == pkt);
            assert(sends.contains(pkt));
            // r = abstractify(pkt), so r ∈ sends.map(abstractify) = refined_sends
            assert(r == abs_pkt(pkt));
        };

        // Backward: refined_sends ⊆ r_sends
        assert forall |r: LockPacket| refined_sends.contains(r) implies r_sends.contains(r) by {
            broadcast use vstd::seq_lib::group_filter_ensures;
            // r ∈ sends.map(abstractify): ∃pkt ∈ sends with abstractify(pkt) == r
            let pkt = choose |pkt: NetPacket| sends.contains(pkt) && abs_pkt(pkt) == r;
            // pkt ∈ ios.filter(Send).map_values(->s)
            let mapped_c = ios.filter(pred_c).map_values(ext_c);
            assert(mapped_c.contains(pkt));
            let k = choose |k: int| 0 <= k < mapped_c.len() && mapped_c[k] == pkt;
            let io_c = ios.filter(pred_c)[k];
            // io_c ∈ ios (filter is subset)
            ios.lemma_filter_contains_rev(pred_c, io_c);
            let j = choose |j: int| 0 <= j < ios.len() && ios[j] == io_c;
            // r_ios[j] is Send and r_ios[j]->s == r
            assert(r_ios[j] is Send);
            assert(r_ios[j]->s == r);
            // r_ios.filter(Send).contains(r_ios[j]) (from filter_contains broadcast)
            let filtered_r = r_ios.filter(pred_r);
            assert(filtered_r.contains(r_ios[j]));
            let k2 = choose |k2: int| 0 <= k2 < filtered_r.len() && filtered_r[k2] == r_ios[j];
            assert(filtered_r.map_values(ext_r)[k2] == r);
            assert(r_sends.contains(r));
        };

        assert_sets_equal!(r_sends, refined_sends);

        (sends, r_sends)
    }

    pub proof fn lemma_LEnvironmentNextHost(
            de :ConcreteEnvironment,
            le :LockEnvironment,
            de_next:ConcreteEnvironment,
            le_next:LockEnvironment)
        requires
            concrete_env_is_abstractable(de),
            concrete_env_is_abstractable(de_next),
            abstractify_concrete_environment(de)  == le,
            abstractify_concrete_environment(de_next) == le_next,
            de.nextStep is LEnvStepHostIos,
            LEnvironment_Next(de, de_next),
            de.sentPackets.finite(),
        ensures
            LEnvironment_Next(le, le_next),
        {
            // Set::map preserves finiteness, so le.sentPackets is finite.


            // Set::map also makes le_next.sentPackets finite.

            lemma_is_valid_env_step(de, le);
            let id = de.nextStep->actor;
            let ios = de.nextStep->ios;
            let r_ios = le.nextStep->ios;

            assert(LEnvironment_PerformIos(de, de_next, id, ios));

            let (sends, r_sends) = lemma_ios_relations(ios, r_ios);

            // Prove: de.sentPackets + sends == de_next.sentPackets
            // From LEnvironment_PerformIos: de_next.sentPackets =~= de.sentPackets ∪ ios.filter(Send).map_values(->s).to_set()
            // From lemma_ios_relations: sends =~= ios.filter(Send).map_values(->s).to_set()
            assert(de.sentPackets + sends =~= de_next.sentPackets);

            // Prove: le.sentPackets + r_sends == le_next.sentPackets
            // le_next.sentPackets = de_next.sentPackets.map(f_pkt) = (de.sentPackets ∪ sends).map(f_pkt)
            // Set::map distributes over union: = de.sentPackets.map(f_pkt) ∪ sends.map(f_pkt) = le.sentPackets ∪ r_sends
            assert(le.sentPackets =~= de.sentPackets.map(f_pkt));
            de.sentPackets.lemma_map_union_commute(sends, f_pkt);
            assert(le.sentPackets + r_sends =~= le_next.sentPackets);

            // Prove: abstract Receive ios are in le.sentPackets
            // Bridge: r_io ∈ r_ios, r_io is Receive → ∃j. r_ios[j] == r_io, ios[j] is Receive
            //         → de.sentPackets.contains(ios[j]->r)  (from PerformIos match_ios_recv)
            //         → le.sentPackets.contains(abs_pkt(ios[j]->r)) = le.sentPackets.contains(r_io->r)
            assert forall |r_io: LockIo| r_ios.contains(r_io) && r_io is Receive
                implies le.sentPackets.contains(r_io->r) by
            {
                let j = choose |j: int| 0 <= j < r_ios.len() && r_ios[j] == r_io;
                assert(r_ios[j] =~= abstractify_net_event_to_lock_io(ios[j]));
                assert(ios[j] is Receive);
                assert(ios.contains(ios[j]));
                assert(de.sentPackets.contains(ios[j]->r) && f_pkt(ios[j]->r) == r_io->r);
            };

            // Prove: LEnvironment_PerformIos(le, le_next, id, r_ios)
            // (1) sentPackets: le_next.sentPackets =~= le.sentPackets ∪ r_ios.filter(Send).map_values(->s).to_set()
            //     already proved via le.sentPackets + r_sends =~= le_next.sentPackets
            // (2) match_ios_recv: forall io. r_ios.contains(io) ==> match_ios_recv(io, le.sentPackets) — proved above
            // (3) time: le_next.time == le.time — from abstractify preserving time through PerformIos
            assert(LEnvironment_PerformIos(le, le_next, id, r_ios));
        }

    pub proof fn RefinementToLSStateHelper(ds:DSStateLock, ds_next:DSStateLock, ss:AbstractLSState, ss_next:AbstractLSState)
        requires
            ds.abstractable(),
            ds_next.abstractable(),
            ss == ds@,
            ss_next == ds_next@,
            DSStateLock::next_requires(ds, ds_next),
        ensures
            ls_next(ss, ss_next)
    {
        match ds.environment.nextStep {
            LEnvStep::LEnvStepHostIos{actor, ios} => {
                lemma_LEnvironmentNextHost(ds.environment, ss.environment, ds_next.environment, ss_next.environment);

                // ss.servers.dom() =~= ds.servers.dom() by definition of map_values
                assert(ss.servers.dom() =~= ds.servers.dom());
                assert(ss_next.servers.dom() =~= ds_next.servers.dom());

                // Config preservation: NodeNext preserves config in all branches
                let actor = ds.environment.nextStep->actor;
                assert(DSStateLock::next_one_server_requires(ds, ds_next, actor, ds.environment.nextStep->ios));
                assert(HostState::next(ds.servers[actor]@, ds_next.servers[actor]@, ds.environment.nextStep->ios));
                assert(ds_next.servers[actor]@.config =~= ds.servers[actor]@.config);
                // ss.servers[actor] == ds.servers[actor]@ by map_values definition
                assert(ss_next.servers.index(ss.environment.nextStep->actor).config =~= ss.servers.index(ss.environment.nextStep->actor).config);

                assert(ls_next(ss, ss_next));
            },
            _ => {
                assert(ls_next(ss, ss_next));
            },
        }
    }

    pub proof fn RefinementToLSState(config:ConcreteConfig, db:Seq<DSStateLock>) -> (sb:Seq<AbstractLSState>)
        requires
            db.len() > 0,
            DSStateLock::init_requires(db[0], config),
            forall |i: int, j: int| #![trigger DSStateLock::next_requires(db[i], db[j])] 0 <= i < db.len() - 1 && j == i+1 ==> DSStateLock::next_requires(db[i], db[j]),
        ensures
            sb.len() == db.len(),
            ls_init(sb[0], abstractify_end_points(db[0].config)),
            forall |i: int, j: int| #![trigger ls_next(sb[i], sb[j])] 0 <= i < sb.len() - 1 && j == i+1 ==> ls_next(sb[i], sb[j]),
            forall |i: int| #![auto] 0 <= i < db.len() ==> db[i].abstractable() && sb[i] == db[i]@,
        decreases db.len()
    {
        if db.len() == 1 {
            let ls = db[0]@;
            let sb = seq![ ls ];
            let config_abs = abstractify_end_points(db[0].config);

            // From init_requires: all servers satisfy host_init
            assert(forall |id: AbstractEndPoint| #![auto] db[0].servers.contains_key(id)
                ==> HostState::host_init(db[0].servers[id], config_abs, id));

            // 1. LEnvironment_Init bridging: empty concrete sentPackets → empty abstract sentPackets
            broadcast use vstd::set::group_set_lemmas;
            assert(db[0].environment.sentPackets =~= Set::<NetPacket>::empty());
            assert(abstractify_concrete_env_sent_packets(db[0].environment.sentPackets)
                =~= Set::<LockPacket>::empty());
            assert(LEnvironment_Init(sb[0].environment));

            // 2-3. config.len() > 0 and seq_is_unique from valid_config
            assert(config_abs.len() > 0);
            assert(seq_is_unique(config_abs));

            // 4. Server domain ↔ config containment
            // map_values preserves domain: sb[0].servers.dom() =~= db[0].servers.dom()
            // init_requires: db[0].servers.dom() =~= config_abs.to_set()
            assert(sb[0].servers.dom() =~= config_abs.to_set());

            // 5. NodeInit at each position i: host_init gives NodeInit with my_index,
            //    seq_is_unique proves my_index == i
            assert forall |i: int| #![auto] 0 <= i < config_abs.len()
                implies NodeInit(sb[0].servers[config_abs[i]], i as nat, config_abs) by {
                let id = config_abs[i];
                assert(config_abs.to_set().contains(id));
                assert(db[0].servers.contains_key(id));
                assert(HostState::host_init(db[0].servers[id], config_abs, id));
                // host_init → NodeInit(servers[id]@, servers[id]@.my_index, config_abs)
                // host_init → servers[id]@.config[servers[id]@.my_index] == id
                // Since servers[id]@.config =~= config_abs:
                //   config_abs[servers[id]@.my_index] == id == config_abs[i]
                // seq_is_unique → servers[id]@.my_index == i
                // sb[0].servers[id] == db[0].servers[id]@ (map_values definition)
            };

            // 6-7. Finiteness
            assert(sb[0].servers.dom().finite());
            assert(sb[0].environment.sentPackets.finite());

            assert(ls_init(sb[0], config_abs));
            sb
        } else {
            lemma_deduce_transition_from_ds_behavior(config, db, db.len()-2);
            lemma_ds_consistency(config, db, db.len()-2);
            let ls = db[db.len()-2]@;
            let ls_next_state = db.last()@;
            let rest = RefinementToLSState(config, db.drop_last());

            let sb = rest + seq![ls_next_state];
            assert forall |i: int, j: int| 0 <= i < sb.len() - 1 && j == i+1 implies ls_next(sb[i], sb[j]) by {
                if (0 <= i < sb.len()-2) {
                    assert(ls_next(sb[i], sb[j]));
                } else {
                    // Prove db[j].abstractable() where j = db.len()-1
                    // IH gives db[i].abstractable() for i = db.len()-2
                    lemma_ds_consistency(config, db, j);
                    assert(db[j].abstractable());
                    RefinementToLSStateHelper(db[i], db[j], sb[i], sb[j]);
                }
            }

            assert(forall |i: int| #![auto] 0 <= i < db.len() ==> valid_config(db[i].config));
            assert(forall |i: int| #![auto] 0 <= i < db.len() ==> db[i].environment.sentPackets.finite());
            assert(forall |i: int| #![auto] 0 <= i < db.len() ==> db[i].servers.dom().finite());
            assert(forall |i: int, r: AbstractEndPoint| #![auto] 0 <= i < db.len() ==> abstractify_end_points( db[i].config).contains(r) ==>  db[i].servers.contains_key(r));
            // db[i].abstractable() follows from the four components proved above (lines 262-265)
            assert( forall |i: int| #![auto] 0 <= i < db.len() ==> db[i].abstractable());
            /*
            &&& valid_config(self.config)
            // TODO: maybe this trigger needs a change
            &&& forall |r: AbstractEndPoint| #![auto] abstractify_end_points(self.config).contains(r) ==> self.servers.contains_key(r)
            &&& self.environment.sentPackets.finite()
            &&& self.servers.dom().finite()
             */
            assert(forall |i: int| #![auto] 0 <= i < db.len() ==> sb[i] == db[i]@);

            sb
        }
    }

    pub proof fn lemma_DeduceTransitionFromLsBehavior(config:ConcreteConfig, db:Seq<AbstractLSState>, i:int)
        requires is_valid_behavior_ls(config, db),
                 0 <= i < db.len() - 1,
        ensures 
                ls_next(db[i], db[i+1]),
    {

    }

    
    pub proof fn lemma_LsConsistency(config:ConcreteConfig, lb:Seq<AbstractLSState>, i:int)
        requires is_valid_behavior_ls(config, lb),
                0 <= i < lb.len(),
        ensures  lb[i].servers.dom() =~= lb[0].servers.dom(),
                 forall |e| lb[i].servers.contains_key(e) ==> lb[0].servers.contains_key(e) && lb[i].servers[e].config =~= lb[0].servers[e].config,
        decreases i
    {
        if i == 0 {

        } else {
            lemma_LsConsistency(config, lb, i-1);
            lemma_DeduceTransitionFromLsBehavior(config, lb, i-1);

            assert(forall |server| lb[i-1].servers.contains_key(server) ==> lb[i].servers.contains_key(server));
            assert(forall |server| lb[i].servers.contains_key(server) ==> lb[i-1].servers.contains_key(server));

            assert forall |server| lb[i-1].servers.contains_key(server) implies lb[i].servers.contains_key(server) by
            {
                assert(lb[i-1].servers.contains_key(server));
                assert(lb[i].servers.contains_key(server));
            }

            assert forall |server| lb[i].servers.contains_key(server) implies lb[i-1].servers.contains_key(server) by
            {
                assert(lb[i].servers.contains_key(server));
                assert(lb[i-1].servers.contains_key(server));
            }
        }
    }

    #[verifier::rlimit(2)]
    pub proof fn MakeGLSBehaviorFromLS(config:ConcreteConfig, db:Seq<AbstractLSState>) -> (sb:Seq<AbstractGLSState>)
    requires db.len() > 0,
             ls_init(db[0], abstractify_end_points(config)),
             forall |i: int, j: int| #![trigger ls_next(db[i], db[j])] 0 <= i < db.len() - 1 && j == i+1 ==> ls_next(db[i], db[j]),
    ensures sb.len() == db.len(),
            gls_init(sb[0], abstractify_end_points(config)),
            forall |i: int, j: int| #![trigger gls_next(sb[i], sb[j])] 0 <= i < sb.len() - 1 && j == i+1 ==> gls_next(sb[i], sb[j]),
            forall |i: int| 0 <= i < db.len() ==> sb[i].ls =~= db[i],
    decreases db.len()
{
    if (db.len() == 1) {
        let sb = seq![AbstractGLSState{
            ls: db[0], 
            history: seq![config[0]@],
        }];
        // assume(gls_init(sb[0], abstractify_end_points(config)));
        // assume(forall |i: int, j: int| #![trigger gls_next(sb[i], sb[j])] 0 <= i < sb.len() - 1 && j == i+1 ==> gls_next(sb[i], sb[j]));
        // assume(forall |i: int| 0 <= i < db.len() ==> sb[i].ls =~= db[i]);
        sb
    } else {
        let rest = MakeGLSBehaviorFromLS(config, db.drop_last());
        let last_history = rest.last().history;
        let ls = db[db.len()-2];
        let ls_new = db[db.len()-1];
        if ls.environment.nextStep is LEnvStepHostIos &&  ls.servers.contains_key(ls.environment.nextStep->actor) {
            let id = ls.environment.nextStep->actor;
            let ios = ls.environment.nextStep->ios;
            lemma_DeduceTransitionFromLsBehavior(config, db, db.len()-2);
            assert(ls_next(ls, ls_new));
            assert(ls_next_one_server(ls, ls_new, id, ios));
            let node = ls.servers[id];
            let node_next = ls_new.servers[id];
            assert(NodeNext(node, node_next, ios));
            let mut new_history = Seq::<AbstractEndPoint>::empty();
            if NodeGrant(node, node_next, ios) && node.held && node.epoch < 0xFFFF_FFFF_FFFF_FFFF{
                new_history = last_history + seq![node.config[((node.my_index+1) % node.config.len()) as int]];
            } else {
                new_history = last_history;
            }
            let sb = rest + seq![AbstractGLSState{
                ls: db[db.len()-1], 
                history: new_history}];
            // Prove gls_next(sb[sb.len()-2], sb[sb.len()-1])
            // sb[sb.len()-2] = rest.last(), whose .ls =~= ls from IH
            assert(sb[sb.len()-2] == rest.last());
            assert(sb[sb.len()-2].ls =~= ls);
            assert(sb[sb.len()-2].history == last_history);
            assert(sb[sb.len()-1].ls == ls_new);
            assert(sb[sb.len()-1].history == new_history);
            // ls_next transfers via =~=
            assert(ls_next(sb[sb.len()-2].ls, sb[sb.len()-1].ls));
            // Bridge NodeGrant through =~=
            assert(sb[sb.len()-2].ls.servers[id] =~= node);
            assert(sb[sb.len()-1].ls.servers[id] =~= node_next);
            assert(gls_next(sb[sb.len()-2], sb[sb.len()-1]));

            // sb[i].ls =~= db[i]: from IH for i < db.len()-1, by construction for i == db.len()-1
            assert forall |i: int| 0 <= i < db.len() implies sb[i].ls =~= db[i] by {
                if i < db.len() - 1 {
                    assert(sb[i] == rest[i]);
                } else {
                    // i == db.len() - 1: sb[i] = AbstractGLSState{ls: db[db.len()-1], ...}
                }
            };

            sb
        } else {
            let sb = rest + seq![AbstractGLSState{ls: db[db.len()-1], history: last_history}];

            // sb[i].ls =~= db[i]: from IH for i < db.len()-1, by construction for i == db.len()-1
            assert forall |i: int| 0 <= i < db.len() implies sb[i].ls =~= db[i] by {
                if i < db.len() - 1 {
                    assert(sb[i] == rest[i]);
                } else {
                    // i == db.len() - 1: sb[i] = AbstractGLSState{ls: db[db.len()-1], ...}
                }
            };
            sb
            }   
        }
    }

    #[verifier::rlimit(2)]
    pub proof fn RefinementToServiceState(config:ConcreteConfig, glb:Seq<AbstractGLSState>) -> (sb:Seq<AbstractLockServiceState>)
    requires glb.len() > 0,
             gls_init(glb[0], abstractify_end_points(config)),
             forall |i: int, j: int| #![trigger gls_next(glb[i], glb[j])] 0 <= i < glb.len() - 1 && j == i+1 ==> gls_next(glb[i], glb[j]),
    ensures sb.len() == glb.len(),
            service_init(sb[0], abstractify_end_points(config).to_set()),
            forall |i: int, j: int| #![trigger service_next(sb[i], sb[j])] 0 <= i < sb.len() - 1 && j == i+1 ==> sb[i] == sb[j] || service_next(sb[i], sb[j]),
            forall |i: int| 0 <= i < glb.len() ==> sb[i] == abstractify_gls_state(glb[i]),
            forall |i: int| 0 <= i < sb.len() ==> #[trigger] sb[i].hosts =~= sb[0].hosts,
            sb[sb.len()-1] == abstractify_gls_state(glb[glb.len()-1]),
    decreases
        glb.len()
    {
        if glb.len() == 1 {
            let sb = seq![abstractify_gls_state(glb[0])];
            lemma_init_refines(glb[0], abstractify_end_points(config));
            assert(service_init(abstractify_gls_state(glb[0]), abstractify_end_points(config).to_set()));
            sb
        } else {
            let rest = RefinementToServiceState(config, glb.drop_last());
            let gls = glb.drop_last().last();
            let gls_n = glb.last();

            lemma_ls_next_abstract(glb, abstractify_end_points(config), glb.len()-2);
            let sb = rest + seq![abstractify_gls_state(gls_n)];
            if (abstractify_gls_state(gls) == abstractify_gls_state(gls_n)) {
                assert(sb[sb.len()-2] == sb[sb.len()-1]);
            } else {
                assert(service_next(sb[sb.len()-2], sb[sb.len()-1]));
            }

            // Prove the service_next quantifier by IH + last step
            assert forall |i: int, j: int| #![trigger service_next(sb[i], sb[j])]
                0 <= i < sb.len() - 1 && j == i+1
                implies sb[i] == sb[j] || service_next(sb[i], sb[j])
            by {
                if i < rest.len() - 1 {
                    // IH case: both sb[i] and sb[i+1] are from rest
                    assert(sb[i] == rest[i]);
                    assert(sb[i+1] == rest[i+1]);
                }
                // else: i == sb.len()-2, already proved in lines 567-571
            };

            sb
        }
    }

    pub proof fn lemma_LockedPacketImpliesTransferPacket(
        config:ConcreteConfig,
        lb:Seq<AbstractLSState>,
        i:int,
        p:LockPacket,
        )
        requires is_valid_behavior_ls(config, lb), 
                 0 <= i < lb.len(), 
                 lb[i].environment.sentPackets.contains(p), 
                 lb[i].servers.contains_key(p.src), 
                 p.msg is Locked,
        ensures exists |q| lb[i].environment.sentPackets.contains(q) && q.msg is Transfer && lb[i].servers.contains_key(q.src) && q.msg->transfer_epoch =~= p.msg->locked_epoch && q.dst == p.src,
        decreases i
    {
        if i == 0 {
            // sentPackets is empty from LEnvironment_Init → contradicts lb[0].sentPackets.contains(p)
            assert(ls_init(lb[0], abstractify_end_points(config)));
            assert(LEnvironment_Init(lb[0].environment));
            lb[0].environment.sentPackets.lemma_len0_is_empty();
            // lb[0].environment.sentPackets == Set::empty(), so contains(p) is false — vacuously true
            return;
        }

        lemma_DeduceTransitionFromLsBehavior(config, lb, i-1);
        lemma_LsConsistency(config, lb, i);
        assert(lb[i].servers.dom() =~= lb[0].servers.dom());
        assert(ls_init(lb[0], abstractify_end_points(config)));
        
        assert(ls_next(lb[i-1], lb[i]));
        assert(LEnvironment_Next(lb[i-1].environment, lb[i].environment));

        if lb[i-1].environment.sentPackets.contains(p) {
            // Recursive case: p was already in lb[i-1]
            lemma_LockedPacketImpliesTransferPacket(config, lb, i-1, p);
            // IH: exists |q| lb[i-1].sentPackets.contains(q) && ...
            // Propagate witness to lb[i] via sentPackets monotonicity
            lemma_LsConsistency(config, lb, i-1);
            let q = choose |q: LockPacket|
                lb[i-1].environment.sentPackets.contains(q)
                && q.msg is Transfer
                && lb[i-1].servers.contains_key(q.src)
                && q.msg->transfer_epoch =~= p.msg->locked_epoch
                && q.dst == p.src;
            // sentPackets monotone: old ⊆ old ∪ new (from LEnvironment_Next)
            assert(lb[i].environment.sentPackets.contains(q));
            // servers dom preserved
            assert(lb[i-1].servers.dom() =~= lb[0].servers.dom());
            assert(lb[i].servers.contains_key(q.src));
        } else {
            // p is newly sent in the transition from lb[i-1] to lb[i]
            let s = lb[i-1];
            let s_n = lb[i];

            if !(s.environment.nextStep is LEnvStepHostIos) {
                // Not HostIos: Stutter/AdvanceTime/DeliverPacket → sentPackets unchanged
                assert(s_n.environment.sentPackets =~= s.environment.sentPackets);
                // p ∈ s_n.sentPackets =~= s.sentPackets contradicts p ∉ s.sentPackets
                return;
            }

            assert(s.environment.nextStep is LEnvStepHostIos);
            let id = s.environment.nextStep->actor;
            let ios = s.environment.nextStep->ios;
            assert(LEnvironment_PerformIos(s.environment, s_n.environment, id, ios));
            assert(IsValidLEnvStep(s.environment, s.environment.nextStep));
            reveal_with_fuel(Seq::<LockIo>::filter, 3);

            if !s.servers.contains_key(id) {
                // Unknown server: servers unchanged, sentPackets grows
                // All newly sent packets have src == id (from IsValidLIoOp for Send)
                // But p.src ∈ lb[i].servers and id ∉ servers → contradiction
                assert(s_n.servers =~= s.servers);
                let f_send = |io: LockIo| io is Send;
                let f_pkt = |io: LockIo| io->s;
                let filtered = ios.filter(f_send);
                let mapped = filtered.map_values(f_pkt);
                let sends = mapped.to_set();
                // p ∉ s.sentPackets and p ∈ s_n.sentPackets = s.sentPackets ∪ sends → p ∈ sends
                assert(sends.contains(p));
                // p ∈ sends → mapped.contains(p) → exists k: mapped[k] == p
                assert(mapped.contains(p));
                let k = choose |k: int| 0 <= k < mapped.len() && mapped[k] == p;
                // mapped[k] == filtered[k]->s == p
                assert(filtered[k]->s == p);
                // From filter: filtered[k] is Send and ios.contains(filtered[k])
                assert(filtered[k] is Send);
                assert(filtered.contains(filtered[k]));
                ios.filter_lemma(f_send);
                assert(ios.contains(filtered[k]));
                // From IsValidLEnvStep: IsValidLIoOp(filtered[k], id, e)
                assert(IsValidLIoOp(filtered[k], id, s.environment));
                // Send: src == actor → filtered[k]->s.src == id → p.src == id
                assert(p.src == id);
                // But id ∉ servers and p.src ∈ lb[i].servers → contradiction
                assert(false);
                return;
            }

            assert(s.servers.contains_key(id));
            assert(ls_next_one_server(s, s_n, id, ios));
            let node = s.servers[id];
            let node_n = s_n.servers[id];
            assert(NodeNext(node, node_n, ios));

            // p is newly sent and p.msg is Locked
            // NodeGrant only produces Transfer packets (never Locked):
            //   Grant branch: ios.len()==1, ios[0] is Send, ios[0]->s.msg is Transfer
            //   Stutter: ios.len()==0, no new packets
            // In either NodeGrant case: no Locked packet is newly sent
            // So NodeAccept must hold (and specifically the accept sub-branch)
            assert(NodeAccept(node, node_n, ios));

            // Prove ios[0] is Receive by elimination:
            if ios[0] is Send {
                // Corrected NodeAccept returns false for Send → contradiction
                assert(false);
            } else if ios[0] is TimeoutReceive {
                // NodeAccept: s == s_, ios.len() == 1, no Send io
                // → filter gives empty seq → sends = empty → sentPackets unchanged
                assert(ios.len() == 1);
                assert(s_n.environment.sentPackets =~= s.environment.sentPackets);
                assert(false);
            } else if ios[0] is ReadClock {
                // Same argument: ios.len() == 1, no Send io
                assert(ios.len() == 1);
                assert(s_n.environment.sentPackets =~= s.environment.sentPackets);
                assert(false);
            }
            // ios[0] is Receive
            assert(ios[0] is Receive);

            // In NodeAccept Receive branch: accept or ignore
            // Ignore branches have ios.len()==1, no Send → sentPackets unchanged → contradiction
            // So the accept condition must hold
            if ios.len() == 1 {
                // Ignore or alt-ignore: no Send io → sentPackets unchanged
                assert(s_n.environment.sentPackets =~= s.environment.sentPackets);
                assert(false);
            }
            // Accept sub-branch
            assert(ios.len() == 2);
            assert(ios[1] is Send);
            assert(ios[1]->s.msg is Locked);

            let packet = ios[0]->r;
            assert(IsValidLIoOp(ios[0], id, s.environment));
            assert(IsValidLIoOp(ios[1], id, s.environment));

            // Conjunct 1: packet (= ios[0]->r) is in sentPackets
            // match_ios_recv for Receive: s.sentPackets.contains(ios[0]->r)
            assert(ios.contains(ios[0]));
            assert(s.environment.sentPackets.contains(packet));
            // sentPackets monotone (union adds, never removes)
            assert(lb[i].environment.sentPackets.contains(packet));

            // Conjunct 2: packet.msg is Transfer (from accept condition)
            assert(packet.msg is Transfer);

            // Conjuncts 3,4: epoch chain and dst == src
            // From IsValidLIoOp: Receive → dst == actor, Send → src == actor
            assert(packet.dst == id);
            assert(ios[1]->s.src == id);
            // From accept: s_.epoch == ios[0]->r.msg->transfer_epoch == ios[1]->s.msg->locked_epoch
            assert(node_n.epoch == packet.msg->transfer_epoch);
            assert(node_n.epoch == ios[1]->s.msg->locked_epoch);
            // p == ios[1]->s: the only new packet (sends = {ios[1]->s})
            // p ∉ s.sentPackets, p ∈ s_n.sentPackets = s.sentPackets ∪ {ios[1]->s}
            // So p == ios[1]->s
            assert(packet.msg->transfer_epoch == p.msg->locked_epoch);
            assert(packet.dst == p.src);

            // Conjunct 5: node.config.contains(packet.src) (from accept condition)
            assert(node.config.contains(packet.src));

            // Establish witness for ensures
            assert(node.config =~= lb[0].servers[id].config);
            assert(lb[0].servers[id].config =~= lb[i].servers[id].config);
            assert(forall|e| lb[i].servers[id].config.contains(e) <==> lb[i].servers.contains_key(e));
            assert(lb[i].servers.contains_key(packet.src));
        }
    }

    pub proof fn lemma_PacketSentByServerIsDemarshallable(
        config:ConcreteConfig,
        db:Seq<DSStateLock>,
        i:int,
        p:NetPacket,
        )
        requires is_valid_behavior(config, db),
                 0 <= i < db.len(),
                 abstractify_end_points(config).contains(p.src),
                 db[i].environment.sentPackets.contains(p),
        ensures 
            net_packet_is_abstractable(p),
        decreases
            i
    {
        if i == 0 {
            return;
        }

        if db[i-1].environment.sentPackets.contains(p) {
            lemma_PacketSentByServerIsDemarshallable(config, db, i-1, p);
            return;
        }

        lemma_deduce_transition_from_ds_behavior(config, db, i-1);
        lemma_ds_consistency(config, db, i-1);
    }

    pub proof fn RefinementProof(config:ConcreteConfig, db:Seq<DSStateLock>) -> (sb:Seq<AbstractLockServiceState>)
        requires db.len() > 0,
                 DSStateLock::init_requires(db[0], config),
                 forall |i: int, j: int| #![trigger DSStateLock::next_requires(db[i], db[j])] 0 <= i < db.len() - 1 && j == i+1 ==> DSStateLock::next_requires(db[i], db[j])
        ensures db.len() == sb.len(),
                service_init(sb[0], db[0].servers.dom()),
                forall |i: int, j: int| #![trigger service_next(sb[i], sb[j])] 0 <= i < sb.len() - 1 && j == i+1 ==> sb[i] == sb[j] || service_next(sb[i], sb[j]),
                forall |i: int| 0 <= i < db.len() ==> service_correspondence(db[i].environment.sentPackets, sb[i])
    {
        let lsb = RefinementToLSState(config, db);
        let glsb = MakeGLSBehaviorFromLS(config, lsb);
        let sb = RefinementToServiceState(config, glsb);
        //assert forall i :: 0 <= i < sb.len() - 1 ==> Service_Next(sb[i], sb[i+1]);
        
        // Establish is_valid_behavior_ls(config, lsb) once for use in the proof
        assert(is_valid_behavior_ls(config, lsb));

        assert forall |i: int| 0 <= i < db.len()
            implies service_correspondence(db[i].environment.sentPackets, sb[i])
            by
        {
            let ls = lsb[i];
            let gls = glsb[i];
            let ss = sb[i];
            let history = make_lock_history(glsb, abstractify_end_points(config), i);
            assert(history == gls.history);

            // Prove service_correspondence by proving its inner quantifier
            assert forall |p: NetPacket, epoch: int| #![auto]
                db[i].environment.sentPackets.contains(p)
                && ss.hosts.contains(p.src)
                && ss.hosts.contains(p.dst)
                && 0 <= epoch < 0x1_0000_0000_0000_0000
                && p.msg =~= marshall_lock_message(epoch)
            implies
                1 <= epoch <= ss.history.len() && p.src == ss.history[epoch - 1]
            by {
                // Step 1: marshall_lock_message(epoch) = seq![1u8] + (epoch as u64).ghost_serialize()
                //       = CMessage::CLocked{locked_epoch: epoch as u64}.ghost_serialize()
                let witness = CMessage::CLocked{locked_epoch: epoch as u64};
                assert(witness.is_marshalable());
                // witness.ghost_serialize() == marshall_lock_message(epoch) since both unfold to
                // seq![1u8] + (epoch as u64).ghost_serialize() for 0 <= epoch < 2^64
                assert(witness.ghost_serialize() =~= p.msg);

                // Step 2: lock_demarshal_data(p.msg) has a valid witness, so choose gives
                // a marshalable CMessage with same serialization as p.msg
                let d = lock_demarshal_data(p.msg);

                // Step 3: By serialization injectivity, d@ == witness@ == Locked{locked_epoch: epoch}
                lock_marshal_data_injective(&d, &witness);
                assert(d@ == LockMessage::Locked{locked_epoch: epoch});

                // Step 4: Construct abstract packet
                let ap = abstractify_net_packet_to_lock_packet(p);
                assert(ap.msg == d@);
                assert(ap.msg is Locked);
                assert(ap.msg->locked_epoch == epoch);

                // Step 5: Show ap is in lsb[i].environment.sentPackets via Set::map witness
                let f = |p_: NetPacket| abstractify_net_packet_to_lock_packet(p_);
                assert(lsb[i].environment.sentPackets =~= db[i].environment.sentPackets.map(f));
                assert(f(p) == ap);
                assert(lsb[i].environment.sentPackets.contains(ap));

                // Step 6: Show ap.src is a known server in lsb[i]
                assert(lsb[i].servers.dom() =~= db[i].servers.dom());
                assert(lsb[i].servers.contains_key(ap.src));

                // Step 7: Bridge to glsb[i] (glsb[i].ls =~= lsb[i])
                assert(glsb[i].ls =~= lsb[i]);

                // Step 8: Use lemma_LockedPacketImpliesTransferPacket
                lemma_LockedPacketImpliesTransferPacket(config, lsb, i, ap);
                let q = choose |q: LockPacket|
                    lsb[i].environment.sentPackets.contains(q)
                    && q.msg is Transfer
                    && lsb[i].servers.contains_key(q.src)
                    && q.msg->transfer_epoch =~= ap.msg->locked_epoch
                    && q.dst == ap.src;

                // Step 9: Use make_lock_history Transfer postconditions
                // q is in glsb[i].ls.sentPackets (= lsb[i].sentPackets via =~=)
                assert(glsb[i].ls.environment.sentPackets.contains(q));
                assert(glsb[i].ls.servers.contains_key(q.src));
                assert(q.msg->transfer_epoch == epoch);
                // make_lock_history: 2 <= transfer_epoch <= history.len()
                assert(2 <= epoch <= history.len());
                // make_lock_history: history[transfer_epoch - 1] == q.dst
                assert(history[epoch - 1] == q.dst);
                assert(q.dst == ap.src);
                assert(ap.src == p.src);
                assert(ss.history == history);
            };
        }
        sb
    }
}
