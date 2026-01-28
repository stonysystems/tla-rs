#![allow(unused_imports)]
use crate::common::logic::*;
use vstd::prelude::*;
use vstd::{modes::*, prelude::*, seq::*, *};

verus! {
    pub struct LPacket<IdType, MessageType>{
        pub dst: IdType,
        pub src: IdType,
        pub msg: MessageType
     }

    pub enum LIoOp<IdType, MessageType> {
        Send{s: LPacket<IdType, MessageType>},
        Receive{r: LPacket<IdType, MessageType>},
        TimeoutReceive,
        ReadClock{t: int},
    }

    pub enum LEnvStep<IdType, MessageType> {
        LEnvStepHostIos{actor: IdType, ios: Seq<LIoOp<IdType, MessageType>>},
        LEnvStepDeliverPacket{p: LPacket<IdType, MessageType>},
        LEnvStepAdvanceTime,
        LEnvStepStutter,
    }

    pub struct LHostInfo<IdType, MessageType> {
        pub queue: Seq<LPacket<IdType, MessageType>>
    }

    #[verifier::reject_recursive_types(IdType)]
    #[verifier::reject_recursive_types(MessageType)]
    pub struct LEnvironment<IdType, MessageType> {
        pub time:int,
        pub sentPackets:Set<LPacket<IdType, MessageType>>,
        pub hostInfo:Map<IdType, LHostInfo<IdType, MessageType>>,
        pub nextStep:LEnvStep<IdType, MessageType>
    }

    pub open spec fn IsValidLIoOp<IdType, MessageType>(io:LIoOp<IdType, MessageType>, actor:IdType, e:LEnvironment<IdType, MessageType>) -> bool
    {
        match io {
            LIoOp::Send{s} => s.src == actor,
            LIoOp::Receive{r} => r.dst == actor,
            LIoOp::TimeoutReceive => true,
            LIoOp::ReadClock{t} => true,
        }
    }


    pub open spec fn LIoOpOrderingOKForAction<IdType, MessageType>(
        io1:LIoOp<IdType, MessageType>,
        io2:LIoOp<IdType, MessageType>
        ) -> bool
      {
        io1 is Receive || io2 is Send
      }

      pub open spec fn LIoOpSeqCompatibleWithReduction<IdType, MessageType>(
        ios:Seq<LIoOp<IdType, MessageType>>
        ) -> bool
      {
        forall |i: int, j: int| #![trigger ios[i], ios[j]] 0 <= i < ios.len() - 1 && j == i+1 ==> LIoOpOrderingOKForAction(ios[i], ios[j])
      }

      pub open spec fn IsValidLEnvStep<IdType, MessageType>(e:LEnvironment<IdType, MessageType>, step:LEnvStep<IdType, MessageType>) -> bool
      {
        match step {
            // @todo decide the right trigger here
        LEnvStep::LEnvStepHostIos{actor, ios} => {&&&( forall |io| ios.contains(io) ==>  #[trigger] IsValidLIoOp(io, actor, e))
                                              &&& LIoOpSeqCompatibleWithReduction(ios)
        },
        LEnvStep::LEnvStepDeliverPacket{p} => e.sentPackets.contains(p),
        LEnvStep::LEnvStepAdvanceTime => true,
        LEnvStep::LEnvStepStutter => true,
        }
      }

      pub open spec fn LEnvironment_Init<IdType, MessageType>(
        e:LEnvironment<IdType, MessageType>
        ) -> bool
      {
        &&& e.sentPackets.len() == 0
        &&& e.time >= 0
      }

      pub open spec fn match_ios_recv<IdType, MessageType>(io: LIoOp<IdType, MessageType>, sentPackets: Set<LPacket<IdType, MessageType>>) -> bool {
        match io {
            LIoOp::Receive { r } => sentPackets.contains(r),
            _ => true,
        }
      }

      pub open spec fn LEnvironment_PerformIos<IdType, MessageType>(
        e:LEnvironment<IdType, MessageType>,
        e_:LEnvironment<IdType, MessageType>,
        actor:IdType,
        ios:Seq<LIoOp<IdType, MessageType>>
        ) -> bool
      {
        &&& e_.sentPackets =~= e.sentPackets.union(
                                        ios.map_values(|io: LIoOp<IdType, MessageType>| io->Send_s)
                                            .to_set())
        &&& (forall |io| ios.contains(io) && match_ios_recv(io, e.sentPackets) )
        // &&& (forall |io| ios.contains(io) && io is Receive ==> e.sentPackets.contains(io->r))
        &&& e_.time == e.time
      }

      pub open spec fn LEnvironment_AdvanceTime<IdType, MessageType>(
        e:LEnvironment<IdType, MessageType>,
        e_:LEnvironment<IdType, MessageType>
        ) -> bool
      {
        &&& e_.time > e.time
        &&& e_.sentPackets =~= e.sentPackets
      }

      pub open spec fn LEnvironment_Stutter<IdType, MessageType>(
        e:LEnvironment<IdType, MessageType>,
        e_:LEnvironment<IdType, MessageType>
        ) -> bool
      {
        &&& e_.time == e.time
        &&& e_.sentPackets =~= e.sentPackets
      }

      pub open spec fn LEnvironment_Next<IdType, MessageType>(
        e:LEnvironment<IdType, MessageType>,
        e_:LEnvironment<IdType, MessageType>
        ) -> bool
      {
        &&& IsValidLEnvStep(e, e.nextStep)
        &&& match e.nextStep {
            LEnvStep::LEnvStepHostIos{actor, ios} => LEnvironment_PerformIos(e, e_, actor, ios),
            LEnvStep::LEnvStepDeliverPacket{p} => LEnvironment_Stutter(e, e_), // this is only relevant for synchrony
            LEnvStep::LEnvStepAdvanceTime => LEnvironment_AdvanceTime(e, e_),
            LEnvStep::LEnvStepStutter => LEnvironment_Stutter(e, e_),
        }
      }

      // #[verifier(opaque)] -> can't make it opaque for the proof to work???
      pub open spec fn EnvironmentNextTemporal<IdType,MessageType>(b:Behavior<LEnvironment<IdType, MessageType>>) -> temporal
      {
        stepmap(Map::new(|i: int| i == i, |i: int| LEnvironment_Next(b[i], b[nextstep(i)])))
      }

      pub proof fn lemma_EnvironmentNextTemporal<IdType,MessageType>(b:Behavior<LEnvironment<IdType, MessageType>>)
        ensures forall |i: int| #![auto] sat(i, EnvironmentNextTemporal(b)) <==> LEnvironment_Next(b[i], b[nextstep(i)])
      {}

      pub open spec fn predicate_LEnvironment_BehaviorSatisfiesSpec<IdType, MessageType>(
        b:Behavior<LEnvironment<IdType, MessageType>>
        ) -> bool
      {
        &&& LEnvironment_Init(b[0])
        &&& sat(0, always(EnvironmentNextTemporal(b)))
      }

} // !verus
