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
        &&& e.sentPackets.finite()
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
                                        ios.filter(|io: LIoOp<IdType, MessageType>| io is Send)
                                            .map_values(|io: LIoOp<IdType, MessageType>| io->s)
                                            .to_set())
        &&& (forall |io| ios.contains(io) ==> match_ios_recv(io, e.sentPackets) )
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

      /// Generic one-step preservation: if sentPackets is finite and LEnvironment_Next holds,
      /// then sentPackets is finite in the next state.
      pub proof fn lemma_environment_next_preserves_sentpackets_finite<IdType, MessageType>(
          e: LEnvironment<IdType, MessageType>,
          e_: LEnvironment<IdType, MessageType>,
      )
          requires
              e.sentPackets.finite(),
              LEnvironment_Next(e, e_),
          ensures
              e_.sentPackets.finite()
      {
          match e.nextStep {
              LEnvStep::LEnvStepHostIos{actor, ios} => {
                  broadcast use vstd::seq_lib::seq_to_set_is_finite;
                  broadcast use vstd::set::group_set_axioms;
                  let new_set = ios.filter(|io: LIoOp<IdType, MessageType>| io is Send)
                      .map_values(|io: LIoOp<IdType, MessageType>| io->s).to_set();
                  assert(new_set.finite());
                  assert(e.sentPackets.union(new_set).finite());
              },
              LEnvStep::LEnvStepDeliverPacket{p} => {},
              LEnvStep::LEnvStepAdvanceTime => {},
              LEnvStep::LEnvStepStutter => {},
          }
      }

      /// If a packet appears in the new sentPackets but not the old ones,
      /// and LEnvironment_PerformIos holds, then the ios must contain Send{s:pkt}.
      pub proof fn lemma_new_packet_in_ios<IdType, MessageType>(
          e: LEnvironment<IdType, MessageType>,
          e_: LEnvironment<IdType, MessageType>,
          actor: IdType,
          ios: Seq<LIoOp<IdType, MessageType>>,
          pkt: LPacket<IdType, MessageType>,
      )
          requires
              LEnvironment_PerformIos(e, e_, actor, ios),
              e_.sentPackets.contains(pkt),
              !e.sentPackets.contains(pkt),
          ensures
              ios.contains(LIoOp::Send{s:pkt}),
      {
          broadcast use vstd::seq_lib::group_filter_ensures;
          let pred = |io: LIoOp<IdType, MessageType>| io is Send;
          let ext = |io: LIoOp<IdType, MessageType>| io->s;
          let filtered = ios.filter(pred);
          let mapped = filtered.map_values(ext);
          // pkt is in e_.sentPackets but not e.sentPackets, so it must be in the new sends
          assert(mapped.to_set().contains(pkt));
          assert(mapped.contains(pkt));
          let j = choose |j: int| 0 <= j < mapped.len() && mapped[j] == pkt;
          let io_elem = filtered[j];
          // filter_pred broadcast: filtered[j] satisfies the predicate
          assert(io_elem is Send);
          assert(io_elem->s == pkt);
          // filter_contains_rev: filtered element is in original sequence
          ios.lemma_filter_contains_rev(pred, io_elem);
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
