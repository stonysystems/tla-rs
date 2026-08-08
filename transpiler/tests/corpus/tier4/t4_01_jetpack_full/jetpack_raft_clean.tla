------------------------ MODULE jetpack_raft_clean --------------------------
(***************************************************************************)
(* Jetpack composed with base Raft, in the clean subset (C1-C5).           *)
(*                                                                         *)
(* This is **the spec**. `base_raft_clean` and `jetpack_clean` are library *)
(* modules: they declare state and define actions, and neither has an      *)
(* `Init`/`Next` of its own. Linting either alone reports "no next-state   *)
(* relation", which is correct -- a library is not a spec. This module is  *)
(* what the linter and the translator consume, and the frontend resolves   *)
(* the `INSTANCE`s into it (Phase 55.1).                                   *)
(*                                                                         *)
(* The structure mirrors the original three modules exactly: the same two  *)
(* layers, instantiated the same way, composed in the same `Next`.         *)
(*                                                                         *)
(* WHAT THIS KEEPS THAT `tier3/t3_01_jetpack` DROPPED                      *)
(*                                                                         *)
(*   - the **fast path** (Preaccept, client quorum counting, Resubmit)     *)
(*   - the **base protocol** (elections, replication, commit)              *)
(*   - **views and reconfiguration**                                       *)
(*   - the **client layer**                                                *)
(*                                                                         *)
(* WHAT IS STILL NOT FAITHFUL, and each has a reason:                      *)
(*                                                                         *)
(*   - the message **bag** is a set, so duplication is not modelled;       *)
(*   - the four global counters are per-node, because a global budget has  *)
(*     no projection;                                                      *)
(*   - execution tracking (`execution_cmds`) is absent: it is a history    *)
(*     variable, and the properties stated over it are restated here over  *)
(*     the replicas' own state.                                            *)
(***************************************************************************)
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS Server, Client, Commands, CmdId, Key,
          MaxTerm, MaxLogLen, MaxElections, MaxRestarts, MaxEpoch

Node == Server \cup Client

ASSUME ServerClientDisjoint == Server \cap Client = {}

(***************************************************************************)
(* State. Declared once here and shared with both layers -- which is what   *)
(* `INSTANCE` means, and is how the original composes as well.             *)
(***************************************************************************)
VARIABLES
  \* base protocol
  currentTerm, ostate, votedFor, log, commitIndex, votesGranted,
  nextIndex, matchIndex, config, pendingReconfig, electionCtr, restartCtr,
  \* Jetpack layer
  jstate, jepoch, oepoch, viewEpoch, viewMembers, viewProposers,
  maxSeenBallot, acceptedBallot, acceptedValue, cmdPool,
  recoverySet, prepRcvd, acceptRcvd, chosenValue,
  highestSeenBallot, highestSeenValue,
  \* client role
  clientPending, clientSuccesses, clientHeardFrom,
  clientEpoch, clientMembers, clientProposers,
  \* the one network (C4)
  msgs

B == INSTANCE base_raft_clean
J == INSTANCE jetpack_clean

baseVars == <<currentTerm, ostate, votedFor, log, commitIndex, votesGranted,
              nextIndex, matchIndex, config, pendingReconfig,
              electionCtr, restartCtr>>

jetpackVars == <<jstate, jepoch, oepoch, viewEpoch, viewMembers,
                 viewProposers, maxSeenBallot, acceptedBallot, acceptedValue,
                 cmdPool, recoverySet, prepRcvd, acceptRcvd, chosenValue,
                 highestSeenBallot, highestSeenValue>>

clientVars == <<clientPending, clientSuccesses, clientHeardFrom,
                clientEpoch, clientMembers, clientProposers>>

vars == <<baseVars, jetpackVars, clientVars, msgs>>

TypeOK == B!BaseTypeOK /\ J!JetpackTypeOK /\ msgs \subseteq (B!Message \cup J!Message)

Init ==
  /\ currentTerm = [i \in Node |-> 1]
  /\ ostate = [i \in Node |-> IF i \in Server THEN B!Follower ELSE B!NotMember]
  /\ votedFor = [i \in Node |-> B!Nil]
  (* Every member starts with the cluster-forming entry already committed,  *)
  (* as upstream does -- its Init gives each member `<<firstEntry>>` and     *)
  (* sets the leader's nextIndex to 2. An empty initial log is not just a    *)
  (* smaller model: `AppendEntries` sends `mprevLogIndex = nextIndex - 1`,   *)
  (* and `LogOk` rejects any request carrying entries at prevLogIndex 0, so  *)
  (* the first entry could never be replicated and `AdvanceCommitIndex` was  *)
  (* unreachable. TLC's coverage table is what pointed at it.                *)
  /\ log = [i \in Node |->
              IF i \in Server THEN << B!FirstEntry >> ELSE << >>]
  /\ commitIndex = [i \in Node |-> IF i \in Server THEN 1 ELSE 0]
  /\ votesGranted = [i \in Node |-> {}]
  /\ nextIndex = [i \in Node |-> [j \in Server |-> 1]]
  /\ matchIndex = [i \in Node |-> [j \in Server |-> 0]]
  /\ config = [i \in Node |-> [id |-> 0, members |-> Server, committed |-> TRUE]]
  /\ pendingReconfig = [i \in Node |-> B!NoReconfig]
  /\ electionCtr = [i \in Node |-> 0]
  /\ restartCtr = [i \in Node |-> 0]
  /\ jstate = [i \in Node |-> J!Ready]
  /\ jepoch = [i \in Node |-> 0]
  /\ oepoch = [i \in Node |-> 0]
  /\ viewEpoch = [i \in Node |-> 0]
  /\ viewMembers = [i \in Node |-> Server]
  /\ viewProposers = [i \in Node |-> Server]
  /\ maxSeenBallot = [i \in Node |-> 0]
  /\ acceptedBallot = [i \in Node |-> 0]
  /\ acceptedValue = [i \in Node |-> {}]
  /\ cmdPool = [i \in Node |-> [k \in Key |-> J!NilCmd]]
  /\ recoverySet = [i \in Node |-> {}]
  /\ prepRcvd = [i \in Node |-> {}]
  /\ acceptRcvd = [i \in Node |-> {}]
  /\ chosenValue = [i \in Node |-> {}]
  /\ highestSeenBallot = [i \in Node |-> 0]
  /\ highestSeenValue = [i \in Node |-> {}]
  /\ clientPending = [i \in Node |-> J!NilCmd]
  /\ clientSuccesses = [i \in Node |-> {}]
  /\ clientHeardFrom = [i \in Node |-> {}]
  /\ clientEpoch = [i \in Node |-> 0]
  /\ clientMembers = [i \in Node |-> Server]
  /\ clientProposers = [i \in Node |-> Server]
  /\ msgs = {}

(***************************************************************************)
(* The coupling that makes this a composition rather than two specs side   *)
(* by side: a candidate that won an election waits in `ToBeLeader` until    *)
(* Jetpack's recovery finishes, and only then becomes Leader.              *)
(***************************************************************************)
PromoteToLeader(i) ==
  /\ i \in Server
  /\ ostate[i] = B!ToBeLeader
  /\ jstate[i] = J!Ready
  /\ ostate' = [ostate EXCEPT ![i] = B!Leader]
  /\ msgs' = msgs
  /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, votesGranted,
                 nextIndex, matchIndex, config, pendingReconfig,
                 electionCtr, restartCtr>>
  /\ UNCHANGED jetpackVars
  /\ UNCHANGED clientVars

(***************************************************************************)
(* A node that wins an election starts recovery, which is what Jetpack adds *)
(* to Raft: the new leader must recover any command the old view may have   *)
(* accepted before it may serve.                                            *)
(***************************************************************************)
StartRecoveryOnElection(i) ==
  /\ i \in Server
  /\ ostate[i] = B!ToBeLeader
  /\ jstate[i] = J!Ready
  /\ jepoch[i] < MaxEpoch
  /\ J!SendBeginRecovery(i, jepoch[i] + 1)
  /\ UNCHANGED baseVars
  /\ UNCHANGED clientVars

BaseAction(i) ==
  \/ B!Restart(i) /\ UNCHANGED jetpackVars /\ UNCHANGED clientVars
  \/ B!RequestVote(i) /\ UNCHANGED jetpackVars /\ UNCHANGED clientVars
  \/ B!BecomeToBeLeader(i) /\ UNCHANGED jetpackVars /\ UNCHANGED clientVars
  \/ B!AdvanceCommitIndex(i) /\ UNCHANGED jetpackVars /\ UNCHANGED clientVars
  \/ \E v \in Commands :
        B!ClientRequest(i, v) /\ UNCHANGED jetpackVars /\ UNCHANGED clientVars
  \/ \E j \in Server :
        B!AppendEntries(i, j) /\ UNCHANGED jetpackVars /\ UNCHANGED clientVars
  \/ \E op \in {B!ReconfigAdd, B!ReconfigRemove} : \E t \in Server :
        B!RequestReconfig(i, op, t) /\ UNCHANGED jetpackVars
                                    /\ UNCHANGED clientVars

JetpackAction(i) ==
  \/ J!CompleteBeginRecovery(i) /\ UNCHANGED baseVars /\ UNCHANGED clientVars
  \/ J!SendPrepare(i) /\ UNCHANGED baseVars /\ UNCHANGED clientVars
  \/ J!CompletePrepare(i) /\ UNCHANGED baseVars /\ UNCHANGED clientVars
  \/ J!SendAccept(i) /\ UNCHANGED baseVars /\ UNCHANGED clientVars
  \/ J!CompleteAccept(i) /\ UNCHANGED baseVars /\ UNCHANGED clientVars
  \/ J!Resubmit(i) /\ UNCHANGED baseVars /\ UNCHANGED clientVars
  \/ J!FinishRecovery(i) /\ UNCHANGED baseVars /\ UNCHANGED clientVars

ClientAction(i) ==
  \E cmd \in [cmd_id: CmdId, key: Key] :
      J!ClientSendPreaccept(i, cmd) /\ UNCHANGED baseVars

(***************************************************************************)
(* Receipt. The original writes it as an existential over the message set,   *)
(* deriving the node from the message; C5 rejects that because no node is   *)
(* bound. Binding the node and guarding on `m.mdest = i` is the same set of *)
(* steps, stated so that a node can take one.                              *)
(***************************************************************************)
Receive(i, m) ==
  \/ B!UpdateTerm(i, m) /\ UNCHANGED jetpackVars /\ UNCHANGED clientVars
  \/ B!HandleRequestVoteRequest(i, m) /\ UNCHANGED jetpackVars
                                      /\ UNCHANGED clientVars
  \/ B!HandleRequestVoteResponse(i, m) /\ UNCHANGED jetpackVars
                                       /\ UNCHANGED clientVars
  \/ B!RejectAppendEntriesRequest(i, m) /\ UNCHANGED jetpackVars
                                        /\ UNCHANGED clientVars
  \/ B!AcceptAppendEntriesRequest(i, m) /\ UNCHANGED jetpackVars
                                        /\ UNCHANGED clientVars
  \/ B!HandleAppendEntriesResponse(i, m) /\ UNCHANGED jetpackVars
                                         /\ UNCHANGED clientVars
  \/ J!HandlePreacceptRequest(i, m) /\ UNCHANGED baseVars
                                    /\ UNCHANGED clientVars
  \/ J!HandlePreacceptResponse(i, m) /\ UNCHANGED baseVars
  \/ J!HandleBeginRecoveryRequest(i, m) /\ UNCHANGED baseVars
                                        /\ UNCHANGED clientVars
  \/ J!HandleBeginRecoveryResponse(i, m) /\ UNCHANGED baseVars
                                         /\ UNCHANGED clientVars
  \/ J!HandlePrepareRequest(i, m) /\ UNCHANGED baseVars
                                  /\ UNCHANGED clientVars
  \/ J!HandlePrepareResponse(i, m) /\ UNCHANGED baseVars
                                   /\ UNCHANGED clientVars
  \/ J!HandleAcceptRequest(i, m) /\ UNCHANGED baseVars
                                 /\ UNCHANGED clientVars
  \/ J!HandleAcceptResponse(i, m) /\ UNCHANGED baseVars
                                  /\ UNCHANGED clientVars
  \/ J!HandleFinishRecovery(i, m) /\ UNCHANGED baseVars
                                  /\ UNCHANGED clientVars

Next ==
  \E i \in Node :
      \/ BaseAction(i)
      \/ JetpackAction(i)
      \/ ClientAction(i)
      \/ PromoteToLeader(i)
      \/ StartRecoveryOnElection(i)
      \/ \E m \in msgs : Receive(i, m)

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Safety. Recovery is Paxos, so its safety property is Paxos's: two nodes  *)
(* cannot have a quorum accept different values at the same ballot.         *)
(*                                                                         *)
(* The original states this over the global `committed` map and over        *)
(* `execution_cmds`, both of which are history variables. Restated here     *)
(* over the acceptors' own state, which is where a node can check it.       *)
(***************************************************************************)
ChosenAt(b, v) ==
  J!IsQuorum({i \in Server : acceptedBallot[i] = b /\ acceptedValue[i] = v},
             Server)

Consistency ==
  \A b1 \in 0 .. MaxEpoch : \A b2 \in 0 .. MaxEpoch :
    \A v1 \in SUBSET Commands : \A v2 \in SUBSET Commands :
      (ChosenAt(b1, v1) /\ ChosenAt(b2, v2)) => v1 = v2

(***************************************************************************)
(* Raft's election safety, which the composition must not break: at most    *)
(* one Leader per term.                                                     *)
(***************************************************************************)
OneLeaderPerTerm ==
  \A i \in Server : \A j \in Server :
    (/\ i # j
     /\ ostate[i] = B!Leader
     /\ ostate[j] = B!Leader) => currentTerm[i] # currentTerm[j]

(***************************************************************************)
(* The coupling stated as a property: a node serves as Leader only once its *)
(* recovery has finished. This is what Jetpack adds to Raft, and it is the  *)
(* reason the two layers are composed rather than run side by side.         *)
(***************************************************************************)
(* Stated as an ACTION property, not a state invariant, and the difference  *)
(* is the whole point. TLC refuted the state-invariant version                *)
(*   \A i \in Server : ostate[i] = B!Leader => jstate[i] = J!Ready            *)
(* at depth 37: a Leader receives a BeginRecoveryRequest for a later view   *)
(* and re-enters Recovery as a *participant*. `jstate` carries both roles    *)
(* -- driving your own recovery, and taking part in someone else's -- so as *)
(* a state predicate the implication is false, and it is false in the       *)
(* original too: upstream `HandleBeginRecoveryRequest` adopts the incoming  *)
(* view unconditionally, with no epoch guard. The rewrite is faithful; the  *)
(* invariant was mis-stated.                                                *)
(*                                                                          *)
(* What the composition actually guarantees is about the *transition*: the  *)
(* only way into Leader is through ToBeLeader with recovery complete. That  *)
(* is exactly what running the two layers side by side would not give.      *)
LeaderOnlyAfterRecovery ==
  [][ \A i \in Server :
        (ostate[i] # B!Leader /\ ostate'[i] = B!Leader)
          => (ostate[i] = B!ToBeLeader /\ jstate[i] = J!Ready) ]_vars

SmallState == Cardinality(msgs) <= 3

=============================================================================
