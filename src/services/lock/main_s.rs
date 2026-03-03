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
use crate::implementation::lock::message_i::abstractify_net_packet_to_lock_packet;
use crate::implementation::lock::netlock_i::{
    abstractify_net_event_to_lock_io, abstractify_raw_log_to_ios, net_packet_is_abstractable,
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
            // Derive le.sentPackets.finite() from de.sentPackets.finite():
            // le.sentPackets = abstractify_concrete_env_sent_packets(de.sentPackets) = de.sentPackets.map(f)
            let f_pkt = |p: NetPacket| abstractify_net_packet_to_lock_packet(p);
            de.sentPackets.lemma_map_finite(f_pkt);

            // Derive de_next.sentPackets.finite() from de.sentPackets.finite() + LEnvironment_Next
            lemma_environment_next_preserves_sentpackets_finite(de, de_next);

            // Derive le_next.sentPackets.finite() from de_next.sentPackets.finite()
            de_next.sentPackets.lemma_map_finite(f_pkt);

            lemma_is_valid_env_step(de, le);
            let id = de.nextStep->actor;
            let ios = de.nextStep->ios;
            let r_ios = le.nextStep->ios;

            assert(LEnvironment_PerformIos(de, de_next, id, ios));

            let (sends, r_sends) = lemma_ios_relations(ios, r_ios);

            assume(de.sentPackets + sends == de_next.sentPackets);
            assume(le.sentPackets + r_sends == le_next.sentPackets);

            assume(forall |r_io| #![auto] r_ios.contains(r_io) && r_io is Receive ==>  le.sentPackets.contains(r_io->r ));
            assume(LEnvironment_PerformIos(le, le_next, id, r_ios));
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
            broadcast use vstd::set::group_set_axioms;
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
                    // sentPackets.finite(): from IH + LEnvironment_Next preservation
                    lemma_environment_next_preserves_sentpackets_finite(
                        db[i].environment, db[j].environment);
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
            forall |i: int, j: int| #![trigger service_next(sb[i], sb[j])] 0 <= i < sb.len() - 1 ==> sb[i] == sb[j] || service_next(sb[i], sb[j]),
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

            assume(forall |i: int, j: int| #![trigger service_next(sb[i], sb[j])] 0 <= i < sb.len() - 1 ==> sb[i] == sb[j] || service_next(sb[i], sb[j]));

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
            assume(exists |q: LockPacket| lb[i].environment.sentPackets.contains(q) && q.msg is Transfer && lb[i].servers.contains_key(q.src) && q.msg->transfer_epoch =~= p.msg->locked_epoch && q.dst == p.src);
            return;    
        }

        lemma_DeduceTransitionFromLsBehavior(config, lb, i-1);
        lemma_LsConsistency(config, lb, i);
        assert(lb[i].servers.dom() =~= lb[0].servers.dom());
        assert(ls_init(lb[0], abstractify_end_points(config)));
        
        if lb[i-1].environment.sentPackets.contains(p) {
            lemma_LockedPacketImpliesTransferPacket(config, lb, i-1, p);
        } else {
            let s = lb[i-1];
            let s_n = lb[i];
            assert(ls_next(lb[i-1], lb[i]));
            if s.environment.nextStep is LEnvStepHostIos && s.servers.contains_key(s.environment.nextStep->actor) {
                assert(ls_next_one_server(s, s_n, s.environment.nextStep->actor, s.environment.nextStep->ios));
                let id = s.environment.nextStep->actor;
                let node = s.servers[id];
                let node_n = s_n.servers[id];
                let ios = s.environment.nextStep->ios;
                if NodeAccept(node, node_n, ios) {
                    let packet = ios[0]->r;
                    assert(IsValidLIoOp(ios[0], id, s.environment));
                    assume(lb[i].environment.sentPackets.contains(packet)
                         && packet.msg is Transfer
                         && packet.msg->transfer_epoch == p.msg->locked_epoch
                         && packet.dst == p.src
                         && node.config.contains(packet.src));
                    
                    assert(node.config =~= lb[0].servers[id].config);
                    assert(lb[0].servers[id].config =~= lb[i].servers[id].config);
                    assert(forall|e| lb[i].servers[id].config.contains(e) <==> lb[i].servers.contains_key(e));
                    assert(lb[i].servers.contains_key(packet.src));
                }
            }
        }
        assume(exists |q: LockPacket| lb[i].environment.sentPackets.contains(q) 
                            && q.msg is Transfer 
                            && lb[i].servers.contains_key(q.src) 
                            && q.msg->transfer_epoch =~= p.msg->locked_epoch 
                            && q.dst == p.src
                        );
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
                forall |i: int, j: int| #![trigger service_next(sb[i], sb[j])] 0 <= i < sb.len() - 1 ==> sb[i] == sb[j] || service_next(sb[i], sb[j]),
                forall |i: int| 0 <= i < db.len() ==> service_correspondence(db[i].environment.sentPackets, sb[i])
    {
        let lsb = RefinementToLSState(config, db);
        let glsb = MakeGLSBehaviorFromLS(config, lsb);
        let sb = RefinementToServiceState(config, glsb);
        //assert forall i :: 0 <= i < sb.len() - 1 ==> Service_Next(sb[i], sb[i+1]);
        
        assert forall |i: int| 0 <= i < db.len()
            implies service_correspondence(db[i].environment.sentPackets, sb[i])
            by
        {
            let ls = lsb[i];
            let gls = glsb[i];
            let ss = sb[i];
            let history = make_lock_history(glsb, abstractify_end_points(config), i);
            assert(history == gls.history);
            assume(forall |p: NetPacket, epoch| 
                            db[i].environment.sentPackets.contains(p)
                         && ss.hosts.contains(p.src) 
                         && ss.hosts.contains(p.dst)
                         && p.msg == marshall_lock_message(epoch) 
                ==> 2 <= epoch <= ss.history.len()
                     && p.src == ss.history[epoch-1]
        );
        }
        sb
    }
}
