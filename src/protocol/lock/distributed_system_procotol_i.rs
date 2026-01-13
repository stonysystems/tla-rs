#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::{map::*, modes::*, prelude::*, seq::*, *};

use crate::common::collections::seq_is_unique_v::seq_is_unique;
use crate::common::framework::environment_s::LEnvStep;
use crate::common::framework::environment_s::*;
use crate::common::native::io_s::*;

use super::node::{AbstractConfig, AbstractNode, NodeAccept, NodeGrant, NodeInit, NodeNext};
use super::types::{LockEnvironment, LockIo};

verus! {
    pub struct AbstractLSState {
        pub environment: LockEnvironment,
        pub servers: Map<AbstractEndPoint, AbstractNode>,
    }

    // LS_Init
    pub open spec fn ls_init(s: AbstractLSState, config: AbstractConfig) -> bool {
        &&& LEnvironment_Init(s.environment)
        &&& config.len() > 0
        &&& seq_is_unique(config)
        &&& forall |e: AbstractEndPoint| config.contains(e)  <==> #[trigger] s.servers.contains_key(e)
        &&& forall |i: int| #![auto] 0 <= i < config.len() ==> NodeInit(s.servers[config[i]], i as nat, config)
        &&& s.servers.dom().finite()
        &&& s.environment.sentPackets.finite()
    }

    pub open spec fn ls_next_one_server(s: AbstractLSState, s_: AbstractLSState, id: AbstractEndPoint, ios: Seq<LockIo>) -> bool
        recommends
            s.servers.contains_key(id) && s.servers.dom().finite() && s_.servers.dom().finite()
    {
        &&& s_.servers.contains_key(id)
        &&& NodeNext(s.servers[id], s_.servers[id], ios)
        &&& s_.servers =~= s.servers.insert(id, s_.servers[id])
        &&& s_.servers[id].config =~= s.servers[id].config // not sure if this is right either
        &&& s_.servers.len() == s.servers.len() // I think this is right? Since s.servers contains id, so it might just be modified
        &&& s_.servers.dom().finite()
        &&& s.servers.dom().finite()
        // &&& s.environment.sentPackets.finite()
        // &&& s_.environment.sentPackets.finite()
    }

    pub open spec fn node_acquires_lock(e:AbstractEndPoint, s:AbstractLSState, s_:AbstractLSState) -> bool
    {
        s.servers.contains_key(e) && s_.servers.contains_key(e) && !s.servers[e].held && s_.servers[e].held
    }

    pub open spec fn ls_next(s:AbstractLSState, s_:AbstractLSState) -> bool
    {
        &&& LEnvironment_Next(s.environment, s_.environment)
        &&& if s.environment.nextStep is LEnvStepHostIos &&  s.servers.contains_key(s.environment.nextStep->actor) {
            ls_next_one_server(s, s_, s.environment.nextStep->actor, s.environment.nextStep->ios)
            } else { s_.servers =~= s.servers }
    }

    pub struct AbstractGLSState {
        pub ls: AbstractLSState,
        pub history: Seq<AbstractEndPoint>,
    }

    pub open spec fn gls_init(s: AbstractGLSState, config: AbstractConfig) -> bool {
        &&& ls_init(s.ls, config)
        &&& s.history =~= seq![config[0]]
    }

    pub open spec fn gls_next(s: AbstractGLSState, s_: AbstractGLSState) -> bool {
        &&& ls_next(s.ls, s_.ls)
        &&& if s.ls.environment.nextStep is LEnvStepHostIos && s.ls.servers.contains_key(s.ls.environment.nextStep->actor)
               && NodeGrant(s.ls.servers[s.ls.environment.nextStep->actor], s_.ls.servers[s.ls.environment.nextStep->actor], s.ls.environment.nextStep->ios)
               && s.ls.servers[s.ls.environment.nextStep->actor].held && s.ls.servers[s.ls.environment.nextStep->actor].epoch < 0xFFFF_FFFF_FFFF_FFFF {
                  s_.history == s.history + seq![s.ls.servers[s.ls.environment.nextStep->actor].config[( (s.ls.servers[s.ls.environment.nextStep->actor].my_index + 1) % (s.ls.servers[s.ls.environment.nextStep->actor].config.len())) as int ] ]
               } else{
                    s_.history == s.history
               }
    }
}
