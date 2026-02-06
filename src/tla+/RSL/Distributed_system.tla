---- MODULE Distributed_system ----
\* Auto-generated from Verus spec by verus2tla
\* DO NOT EDIT MANUALLY

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS RslIo, Constants, RslState, AbstractEndPoint

RslState ==
    [constants |-> Constants, environment |-> Environment, replicas |-> Seq(Scheduler), clients |-> Seq(AbstractEndPoint)]

RslMapsComplete(ps) ==
    Len(ps.replicas) = Len(ps.constants.config.replica_ids)

RslConstantsUnchanged(ps, ps_) ==
    /\ Len(ps_.replicas) = Len(ps.replicas)
    /\ ps_.clients = ps.clients
    /\ ps_.constants = ps.constants

RslInit(con, ps) ==
    /\ WellFormedLConfiguration(con.config)
    /\ WFLParameters(con.params)
    /\ ps.constants = con
    /\ Environment_Init(ps.environment)
    /\ RslMapsComplete(ps)
    /\ \A i \in Int : (0 <= i /\ i < Len(con.config.replica_ids)) => SchedulerInit(ps.replicas[i], [my_index |-> i, all |-> con])

RslNextCommon(ps, ps_) ==
    /\ RslMapsComplete(ps)
    /\ RslConstantsUnchanged(ps, ps_)
    /\ Environment_Next(ps.environment, ps_.environment)

RslNextOneReplica(ps, ps_, idx, ios) ==
    /\ RslNextCommon(ps, ps_)
    /\ 0 <= idx
    /\ idx < Len(ps.constants.config.replica_ids)
    /\ SchedulerNext(ps.replicas[idx], ps_.replicas[idx], ios)
    /\ ps.environment.nextStep = [actor |-> ps.constants.config.replica_ids[idx], ios |-> ios]
    /\ ps_.replicas = update(ps.replicas, idx, ps_.replicas[idx])

RslNextEnvironment(ps, ps_) ==
    /\ RslNextCommon(ps, ps_)
    /\ ~ps.environment.nextStep.tag = LEnvStepHostIos
    /\ ps_.replicas = ps.replicas

RslNextOneExternal(ps, ps_, eid, ios) ==
    /\ RslNextCommon(ps, ps_)
    /\ ~eid \in ps.constants.config.replica_ids
    /\ ps.environment.nextStep = [actor |-> eid, ios |-> ios]
    /\ ps_.replicas = ps.replicas

RslNext(ps, ps_) ==
    \/ \E idx \in Int, ios \in Seq(RslIo) : RslNextOneReplica(ps, ps_, idx, ios)
    \/ \E eid \in AbstractEndPoint, ios \in Seq(RslIo) : RslNextOneExternal(ps, ps_, eid, ios)
    \/ RslNextEnvironment(ps, ps_)

====
