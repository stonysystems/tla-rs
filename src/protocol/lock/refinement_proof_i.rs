#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::{map::*, modes::*, prelude::*, seq::*, seq_lib::*, *};

use super::distributed_system_procotol_i::*;
use super::node::*;
use super::types::*;

use crate::common::collections::maps::lemma_MapSizeIsDomainSize;
use crate::common::collections::seq_is_unique_v::{
    seq_is_unique, singleton_seq_to_set_is_singleton_set, test_unique,
};
use crate::common::framework::environment_s::LEnvStep;
use crate::common::framework::environment_s::*;
use crate::common::native::io_s::*;
use crate::services::lock::abstractservice_s::*;

use vstd::seq_lib::lemma_seq_properties;
use vstd::set_lib::lemma_set_properties;

verus! {
    pub open spec fn abstractify_gls_state(gls: AbstractGLSState) -> AbstractLockServiceState {
        AbstractLockServiceState{
            hosts: gls.ls.servers.dom(),
            history: gls.history,
        }
    }

    pub proof fn lemma_init_refines(gls: AbstractGLSState, config: AbstractConfig)
        requires
            gls_init(gls, config),
        ensures service_init(abstractify_gls_state(gls), config.to_set())
    {
        assert(config.contains(config[0]));
        let s = abstractify_gls_state(gls);

        config.unique_seq_to_set();
        assert(config.to_set() =~= gls.ls.servers.dom());

        calc!{
            (==)
            s.hosts; {}
            gls.ls.servers.dom(); {}
            config.to_set();
        }

        config.unique_seq_to_set();
        assert(config.contains(config[0]));
        assert(config.to_set().contains(config[0]));
    }

    pub open spec fn is_valid_behaviour(glb: Seq<AbstractGLSState>, config: AbstractConfig) -> bool {
        &&& glb.len() > 0
        &&& gls_init(glb[0], config)
        &&& forall |i: int, j: int| #![trigger gls_next(glb[i], glb[j])]  0 <= i < glb.len() - 1 && j == i+1 ==> gls_next(glb[i], glb[j])
    }

    pub proof fn lemma_ls_next(glb: Seq<AbstractGLSState>, config: AbstractConfig, i: int)
        requires
            is_valid_behaviour(glb, config),
            0 <= i < glb.len() - 1,
        ensures
            gls_next(glb[i], glb[i+1])
    {
    }

    pub proof fn lemma_ls_consistent(glb: Seq<AbstractGLSState>, config: AbstractConfig, i: int)
        requires
            is_valid_behaviour(glb, config),
            0 <= i < glb.len(),
        ensures
            glb[i].ls.servers.len() == config.len(),
            forall |e: AbstractEndPoint| config.contains(e) <==> #[trigger] glb[i].ls.servers.contains_key(e),
            glb[i].ls.servers.dom() =~= glb[0].ls.servers.dom(),
            forall |id: AbstractEndPoint| config.contains(id) ==> #[trigger] glb[0].ls.servers[id].config =~= glb[i].ls.servers[id].config,
        decreases
            i
    {
        // lemma_seq_properties::<AbstractEndPoint>();
        // lemma_set_properties::<AbstractEndPoint>();
        assert(config.no_duplicates());
        config.unique_seq_to_set();

        if (i == 0) {
            assert(config.to_set() =~= glb[0].ls.servers.dom());
            assert(config.len() == glb[0].ls.servers.dom().len());

            calc!{
                (==)
                config.to_set(); {}
                glb[0].ls.servers.dom();
            }

            calc!{
                (==)
                glb[0].ls.servers.dom().len(); { lemma_MapSizeIsDomainSize(glb[0].ls.servers.dom(), glb[0].ls.servers); }
                glb[0].ls.servers.len();
            }
        } else {
            lemma_ls_next(glb, config, i-1);
            lemma_ls_consistent(glb, config, i-1);
        }
    }

    pub proof fn lemma_ls_node_consistent(glb:Seq<AbstractGLSState>, config:AbstractConfig, i:int, candidate:AbstractEndPoint, e:AbstractEndPoint)
    requires
        is_valid_behaviour(glb, config),
        0 <= i < glb.len(),
        glb[i].ls.servers.contains_key(e),
    ensures
        glb[i].ls.servers.contains_key(candidate) <==> glb[i].ls.servers[e].config.contains(candidate)
    decreases
        i
    {
        if i == 0 {

        } else {
            lemma_ls_next(glb, config, i-1);
            lemma_ls_consistent(glb, config, i-1);
            lemma_ls_node_consistent(glb, config, i-1, candidate, e);

            assert(glb[i].ls.servers.contains_key(candidate) <==> glb[i].ls.servers[e].config.contains(candidate));
        }
    }

    pub proof fn lemma_history_increment(glb:Seq<AbstractGLSState>, config:AbstractConfig, i:int)
    requires
        is_valid_behaviour(glb, config),
        0 <= i < glb.len() - 1
    ensures
        glb[i].history.len() + 1 == glb[i].history.len() || glb[i].history =~= glb[i].history
    { }

    pub proof fn lemma_history_size(glb:Seq<AbstractGLSState>, config:AbstractConfig, i:int)
        requires
            is_valid_behaviour(glb, config),
            0 <= i < glb.len(),
        ensures
            1 <= glb[i].history.len() <= i + 1
        decreases
            i
    {
        if i == 0 {
            let locked_packets = Set::new(|p:LockPacket| glb[0].ls.environment.sentPackets.contains(p) && p.msg is Locked);
            // TODO: Prove this

            // assert(locked_packets.len() == 0) by {
            //     assert(LEnvironment_Init(glb[0].ls.environment) ==> !(exists |p:LockPacket| glb[0].ls.environment.sentPackets.contains(p) && p.msg is Locked ));
            //     assert(glb[0].ls.environment.sentPackets.len() == 0);
            // };
            assert(exists |host| (glb[i]).ls.servers.contains_key(host) && #[trigger] (glb[i]).ls.servers[host].held);
            assert(glb[i].history.len() == 1);
        } else {
            lemma_history_size(glb, config, i - 1);
            lemma_history_increment(glb, config, i - 1);
            assert(gls_next(glb[i-1], glb[i]));
        }
    }


    pub proof fn lemma_history_membership(glb:Seq<AbstractGLSState>, config:AbstractConfig, i:int)
        requires
            is_valid_behaviour(glb, config),
            0 <= i < glb.len(),
        ensures
            1 <= glb[i].history.len() <= i + 1,
            glb[i].ls.servers.contains_key(glb[i].history.last())
        decreases
            i
    {
        lemma_history_size(glb, config, i);

        if i == 0 {
        } else {
            lemma_ls_next(glb, config, i - 1);
            lemma_ls_consistent(glb, config, i - 1);
            lemma_ls_consistent(glb, config, i);
            lemma_history_membership(glb, config, i-1);
        }
    }

    pub proof fn lemma_ls_next_abstract(glb:Seq<AbstractGLSState>, config:AbstractConfig, i:int)
    requires
        is_valid_behaviour(glb, config),
        0 <= i < glb.len() - 1
    ensures
        ({
            ||| service_next(abstractify_gls_state(glb[i]), abstractify_gls_state(glb[i+1]))
            ||| abstractify_gls_state(glb[i]) == abstractify_gls_state(glb[i+1])
        })
    {
        lemma_ls_consistent(glb, config, i);
        lemma_ls_consistent(glb, config, i+1);
        assert(gls_next(glb[i], glb[i+1]));
        if i == 0 {
            assert(glb[i].ls.servers[config[0]].held);
            assert(abstractify_gls_state(glb[i]).hosts =~= abstractify_gls_state(glb[i+1]).hosts);
        } else {
            lemma_history_size(glb, config, i);
            assert(glb[i].history.len() > 0);
            lemma_history_membership(glb, config, i);
            assert(glb[i].ls.servers.contains_key(glb[i].history.last()));
            assert(abstractify_gls_state(glb[i]).hosts =~= abstractify_gls_state(glb[i+1]).hosts);
            assert((exists |new_lock_holder: AbstractEndPoint| #![auto] abstractify_gls_state(glb[i]).hosts.contains(new_lock_holder)));
        }
    }

    // TODO: NOT PROVEN
    pub proof fn make_lock_history(glb:Seq<AbstractGLSState>, config:AbstractConfig, i:int) -> (history:Seq<AbstractEndPoint>)
    requires is_valid_behaviour(glb, config),
             0 <= i < glb.len(),
    ensures
            history.len() > 0,
            forall |p: LockPacket| #![auto] glb[i].ls.environment.sentPackets.contains(p) && p.msg is Transfer && glb[i].ls.servers.contains_key(p.src) ==> 2 <= p.msg->transfer_epoch <= history.len(),
            forall |p: LockPacket| #![auto] glb[i].ls.environment.sentPackets.contains(p) && p.msg is Transfer && glb[i].ls.servers.contains_key(p.src) ==> history[p.msg->transfer_epoch-1] == p.dst,
            forall |h: AbstractEndPoint, j: int| #![auto] glb[i].ls.servers.contains_key(h) && 0 <= j < history.len()-1 && history[j] == h ==> j+1 <= glb[i].ls.servers[h].epoch,
            forall |h: AbstractEndPoint| #![auto] glb[i].ls.servers.contains_key(h) && h != history.last() ==> !glb[i].ls.servers[h].held,
            forall |h: AbstractEndPoint| #![auto] glb[i].ls.servers.contains_key(h) && glb[i].ls.servers[h].held ==> glb[i].ls.servers[h].epoch == history.len(),
            history == glb[i].history,
    decreases
        i
    {
        assume(forall |i: int| 0 <= i < glb.len() ==> glb[i].ls.environment.sentPackets.finite());
        // lemma_seq_properties::<AbstractEndPoint>();
        // lemma_set_properties::<AbstractEndPoint>();
        if i == 0 {
            let history = seq![config[0]];

            // This doesn't work
            // assume(forall |p: LockPacket| #![auto] glb[i].ls.environment.sentPackets.contains(p) && p.msg is Transfer && glb[i].ls.servers.contains_key(p.src) ==> 2 <= p.msg->transfer_epoch <= history.len());
            history

        } else {
            let prev_history = make_lock_history(glb, config, i-1);
            let mut history = prev_history;

            lemma_ls_next(glb, config, i-1);
            lemma_ls_consistent(glb, config, i-1);
            lemma_ls_consistent(glb, config, i);
            let s_prev = glb[i-1];
            let s_next = glb[i];
            assert(LEnvironment_Next(s_prev.ls.environment, s_next.ls.environment));

            if s_prev.ls.environment.nextStep is LEnvStepHostIos &&  s_prev.ls.servers.contains_key(s_prev.ls.environment.nextStep->actor) {
                let id = s_prev.ls.environment.nextStep->actor;
                let ios = s_prev.ls.environment.nextStep->ios;

                if NodeGrant(s_prev.ls.servers[id], s_next.ls.servers[id], ios) {
                    if s_prev.ls.servers[id].held && s_prev.ls.servers[id].epoch < 0xFFFF_FFFF_FFFF_FFFF {
                        history = prev_history + seq![ios[0]->s.dst];
                    } else {
                        history = prev_history;
                    }
                    // This passes
                    // assert(forall |p: LockPacket| glb[i].ls.environment.sentPackets.contains(p) && p.msg is Transfer && glb[i].ls.servers.contains_key(p.src) ==> 2 <= p.msg->transfer_epoch <= history.len());
                    // assert(forall |p: LockPacket| glb[i].ls.environment.sentPackets.contains(p) && p.msg is Transfer && glb[i].ls.servers.contains_key(p.src) ==> history[p.msg->transfer_epoch-1] == p.dst);
                    // assert(forall |h: AbstractEndPoint, j: int| glb[i].ls.servers.contains_key(h) && 0 <= j < history.len()-1 && history[j] == h ==> j+1 <= glb[i].ls.servers[h].epoch);
                    // assert(forall |h: AbstractEndPoint| glb[i].ls.servers.contains_key(h) && h != history.last() ==> !glb[i].ls.servers[h].held);
                    // assert(forall |h: AbstractEndPoint| glb[i].ls.servers.contains_key(h) && glb[i].ls.servers[h].held ==> glb[i].ls.servers[h].epoch == history.len());

                } else {
                    if !(ios[0] is TimeoutReceive)
                    && !s_prev.ls.servers[id].held
                    && s_prev.ls.servers[id].config.contains(ios[0]->r.src)
                    && ios[0]->r.msg is Transfer
                    && ios[0]->r.msg->transfer_epoch > s_prev.ls.servers[id].epoch {
                        let p = ios[0]->r;
                        assert(IsValidLIoOp(ios[0], id, s_prev.ls.environment));     // trigger
                        assume(p.dst == id);
                    }

                    history = prev_history;

                    // All of the post conditions fail here
                    assume(forall |p: LockPacket| #![auto] glb[i].ls.environment.sentPackets.contains(p) && p.msg is Transfer && glb[i].ls.servers.contains_key(p.src) ==> 2 <= p.msg->transfer_epoch <= history.len());
                    assume(forall |p: LockPacket| #![auto] glb[i].ls.environment.sentPackets.contains(p) && p.msg is Transfer && glb[i].ls.servers.contains_key(p.src) ==> history[p.msg->transfer_epoch-1] == p.dst);
                    assume(forall |h: AbstractEndPoint, j: int| #![auto] glb[i].ls.servers.contains_key(h) && 0 <= j < history.len()-1 && history[j] == h ==> j+1 <= glb[i].ls.servers[h].epoch);
                    assume(forall |h: AbstractEndPoint| #![auto] glb[i].ls.servers.contains_key(h) && h != history.last() ==> !glb[i].ls.servers[h].held);
                    assume(forall |h: AbstractEndPoint| #![auto] glb[i].ls.servers.contains_key(h) && glb[i].ls.servers[h].held ==> glb[i].ls.servers[h].epoch == history.len());
                }
            } else {
                history = prev_history;

                assume(forall |p: LockPacket| #![auto] glb[i].ls.environment.sentPackets.contains(p) && p.msg is Transfer && glb[i].ls.servers.contains_key(p.src) ==> 2 <= p.msg->transfer_epoch <= history.len());
                assume(forall |p: LockPacket| #![auto] glb[i].ls.environment.sentPackets.contains(p) && p.msg is Transfer && glb[i].ls.servers.contains_key(p.src) ==> history[p.msg->transfer_epoch-1] == p.dst);

                // assert(forall |h: AbstractEndPoint, j: int| glb[i].ls.servers.contains_key(h) && 0 <= j < history.len()-1 && history[j] == h ==> j+1 <= glb[i].ls.servers[h].epoch);
                // assert(forall |h: AbstractEndPoint| glb[i].ls.servers.contains_key(h) && h != history.last() ==> !glb[i].ls.servers[h].held);
                // assert(forall |h: AbstractEndPoint| glb[i].ls.servers.contains_key(h) && glb[i].ls.servers[h].held ==> glb[i].ls.servers[h].epoch == history.len());
            }

            history
        }
    }
}
