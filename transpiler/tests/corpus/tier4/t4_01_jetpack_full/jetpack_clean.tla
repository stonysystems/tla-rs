--------------------------- MODULE jetpack_clean ----------------------------
(***************************************************************************)
(* Jetpack's plugin layer, rewritten into the clean subset (C1-C5).        *)
(*                                                                         *)
(* A **library module** like `base_raft_clean`: state and actions, no      *)
(* `Init`/`Next`. `jetpack_raft_clean` composes the two.                   *)
(*                                                                         *)
(* Unlike `tier3/t3_01_jetpack`, this keeps **the fast path** -- Preaccept, *)
(* the client-side quorum counting, and the resubmit that closes recovery.  *)
(* That slice dropped it, and the reason it gave ("not projectable") was    *)
(* never tested; see 55.3.a, where `FastpathQuorum` is shown to be          *)
(* node-computable.                                                        *)
(*                                                                         *)
(* Rewrite decisions:                                                      *)
(*                                                                         *)
(*  - **One node set.** The original has `Server` and `Client` as separate  *)
(*    constants, and C5 rejects a `Next` disjunct binding `Client`. Here    *)
(*    `Node == Server \cup Client` and every node carries both roles'       *)
(*    state, with actions guarded on `i \in Client` / `i \in Server`. This  *)
(*    is `t1_02_twophase`'s decision about the transaction manager, applied *)
(*    to a second role.                                                     *)
(*  - **Views stay.** `Server` is a constant and never changes; what a node *)
(*    holds is its own opinion of the membership. That is per-node state,   *)
(*    so Q2 does not exclude it (55.0.c).                                   *)
(*  - **`jpool` splits** into the acceptor triple plus the conflict pool,   *)
(*    because a record-of-records projects worse than named fields and the  *)
(*    protocol only ever touches one field at a time.                       *)
(*  - **Response tables become counters.** `br_responses`/`prep_responses`/ *)
(*    `accept_responses` were `[Server -> reply]` tables scanned by the     *)
(*    `Complete*` actions. They become a set of responders plus an online   *)
(*    aggregate of the highest-ballot value -- the same value once the      *)
(*    quorum is in, and what an implementation does.                        *)
(***************************************************************************)
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS Node, Server, Client, CmdId, Key, MaxEpoch


(***************************************************************************)
(* Recovery phases.                                                        *)
(***************************************************************************)
Ready              == "ready"
Recovery           == "recovery"
AfterBeginRecovery == "afterBeginRecovery"
AfterPrepare       == "afterPrepare"
AfterAccept        == "afterAccept"
AfterResubmit      == "afterResubmit"

(***************************************************************************)
(* Message tags.                                                           *)
(***************************************************************************)
PreacceptRequest      == "paq"
PreacceptResponse     == "pap"
BeginRecoveryRequest  == "brq"
BeginRecoveryResponse == "brp"
PrepareRequest        == "pq"
PrepareResponse       == "pp"
AcceptRequest         == "aq"
AcceptResponse        == "ap"
FinishRecoveryNotice  == "fin"

VARIABLES
  jstate,            \* recovery phase at this node
  jepoch,            \* the ballot this node drives recovery with
  oepoch,            \* the view epoch this node has observed
  viewEpoch,         \* epoch of this node's current view
  viewMembers,       \* replica_ids of this node's current view
  viewProposers,     \* proposing_replica_ids of that view
  maxSeenBallot,     \* acceptor: highest ballot promised
  acceptedBallot,    \* acceptor: ballot of the last accept
  acceptedValue,     \* acceptor: value of the last accept
  cmdPool,           \* acceptor: key -> command, for conflict detection
  recoverySet,       \* proposer: who answered BeginRecovery
  prepRcvd,          \* proposer: who promised
  acceptRcvd,        \* proposer: who accepted
  chosenValue,       \* proposer: the value it will propose
  highestSeenBallot, \* proposer: highest accepted ballot reported
  highestSeenValue,  \* proposer: the value reported with it
  clientPending,     \* client: the command in flight, NilCmd if none
  clientSuccesses,   \* client: replicas that accepted it
  clientHeardFrom,   \* client: replicas that answered at all
  clientEpoch,       \* client: epoch of the view it is using
  clientMembers,     \* client: replica_ids of that view
  clientProposers,   \* client: proposing_replica_ids of that view
  msgs               \* messages sent -- shared with the base layer, since
                     \* C4 allows exactly one network for the whole spec

Command == [cmd_id: CmdId, key: Key]
NilCmd  == [cmd_id |-> 0, key |-> 0]

(* The sentinel is not a command, so every slot that may hold "no command"   *)
(* is typed to admit it -- the same shape base_raft uses for `votedFor`.     *)
CommandOrNil == Command \cup {NilCmd}

Epoch == 0 .. MaxEpoch

(***************************************************************************)
(* P4, and the finding that made the fast path reachable at all (55.3.a).  *)
(*                                                                         *)
(* The original defines                                                    *)
(*                                                                         *)
(*   FastpathQuorum(v) == {q \in JQuorum(v) :                               *)
(*       /\ v.proposing_replica_ids \subseteq q                            *)
(*       /\ \A q2 \in JQuorum(v) :                                         *)
(*            v.proposing_replica_ids \subseteq q2                        *)
(*              => (q \cap q2) \in JQuorum(v)}                            *)
(*                                                                         *)
(* which quantifies over every other quorum -- exactly what a node cannot   *)
(* evaluate. It collapses: writing P for the proposers and n for the view   *)
(* size, a fast quorum is any majority containing P when |P|*2 > n, and     *)
(* otherwise only the full membership. Verified by brute force against the  *)
(* literal definition over all 1,022 (n, P) combinations for n <= 9.        *)
(***************************************************************************)
IsQuorum(s, members) == Cardinality(s) * 2 > Cardinality(members)

IsFastQuorum(s, members, proposers) ==
  /\ proposers \subseteq s
  /\ IF Cardinality(proposers) * 2 > Cardinality(members)
       THEN Cardinality(s) * 2 > Cardinality(members)
       ELSE s = members

(***************************************************************************)
(* Two commands conflict when they touch the same key. The pool is keyed by *)
(* key, so a conflict is a lookup rather than a scan.                       *)
(***************************************************************************)
HasConflict(pool, cmd) ==
  /\ cmd.key \in DOMAIN pool
  /\ pool[cmd.key] # cmd

Message ==
       [mtype: {PreacceptRequest}, mepoch: Epoch, mcmd: Command,
        msource: Node, mdest: Node]
  \cup [mtype: {PreacceptResponse}, msuccess: BOOLEAN, mjepoch: Epoch,
        mviewEpoch: Epoch, mviewMembers: SUBSET Server,
        mviewProposers: SUBSET Server, mcmd: Command,
        msource: Node, mdest: Node]
  \cup [mtype: {BeginRecoveryRequest}, mjepoch: Epoch,
        mviewEpoch: Epoch, mviewMembers: SUBSET Server,
        mviewProposers: SUBSET Server, msource: Node, mdest: Node]
  \cup [mtype: {BeginRecoveryResponse}, maccepted_ballot: Epoch,
        maccepted_value: SUBSET Command, msource: Node, mdest: Node]
  \cup [mtype: {PrepareRequest}, mballot: Epoch, moepoch: Epoch,
        msource: Node, mdest: Node]
  \cup [mtype: {PrepareResponse}, mballot: Epoch,
        maccepted_ballot: Epoch, maccepted_value: SUBSET Command,
        msource: Node, mdest: Node]
  \cup [mtype: {AcceptRequest}, mballot: Epoch,
        mvalue: SUBSET Command, msource: Node, mdest: Node]
  \cup [mtype: {AcceptResponse}, mballot: Epoch, msource: Node, mdest: Node]
  \cup [mtype: {FinishRecoveryNotice}, mjepoch: Epoch,
        msource: Node, mdest: Node]

PreacceptReq(s, d, e, c) ==
  [mtype |-> PreacceptRequest, mepoch |-> e, mcmd |-> c,
   msource |-> s, mdest |-> d]

PreacceptResp(s, d, ok, je, ve, vm, vp, c) ==
  [mtype |-> PreacceptResponse, msuccess |-> ok, mjepoch |-> je,
   mviewEpoch |-> ve, mviewMembers |-> vm, mviewProposers |-> vp,
   mcmd |-> c, msource |-> s, mdest |-> d]

BeginRecoveryReq(s, d, je, ve, vm, vp) ==
  [mtype |-> BeginRecoveryRequest, mjepoch |-> je, mviewEpoch |-> ve,
   mviewMembers |-> vm, mviewProposers |-> vp, msource |-> s, mdest |-> d]

BeginRecoveryResp(s, d, ab, av) ==
  [mtype |-> BeginRecoveryResponse, maccepted_ballot |-> ab,
   maccepted_value |-> av, msource |-> s, mdest |-> d]

PrepareReq(s, d, b, oe) ==
  [mtype |-> PrepareRequest, mballot |-> b, moepoch |-> oe,
   msource |-> s, mdest |-> d]

PrepareResp(s, d, b, ab, av) ==
  [mtype |-> PrepareResponse, mballot |-> b, maccepted_ballot |-> ab,
   maccepted_value |-> av, msource |-> s, mdest |-> d]

AcceptReq(s, d, b, v) ==
  [mtype |-> AcceptRequest, mballot |-> b, mvalue |-> v,
   msource |-> s, mdest |-> d]

AcceptResp(s, d, b) ==
  [mtype |-> AcceptResponse, mballot |-> b, msource |-> s, mdest |-> d]

FinishNotice(s, d, je) ==
  [mtype |-> FinishRecoveryNotice, mjepoch |-> je, msource |-> s, mdest |-> d]

BroadcastPreaccept(c, e, cmd, members) ==
  { PreacceptReq(c, d, e, cmd) : d \in members }
BroadcastBeginRecovery(i, je, ve, vm, vp, members) ==
  { BeginRecoveryReq(i, d, je, ve, vm, vp) : d \in members }
BroadcastPrepare(i, b, oe, members) == { PrepareReq(i, d, b, oe) : d \in members }
BroadcastAccept(i, b, v, members) == { AcceptReq(i, d, b, v) : d \in members }
BroadcastFinish(i, je, members) == { FinishNotice(i, d, je) : d \in members }

JetpackTypeOK ==
  /\ jstate \in [Node -> {Ready, Recovery, AfterBeginRecovery,
                          AfterPrepare, AfterAccept, AfterResubmit}]
  /\ jepoch \in [Node -> Epoch]
  /\ oepoch \in [Node -> Epoch]
  /\ viewEpoch \in [Node -> Epoch]
  /\ viewMembers \in [Node -> SUBSET Server]
  /\ viewProposers \in [Node -> SUBSET Server]
  /\ maxSeenBallot \in [Node -> Epoch]
  /\ acceptedBallot \in [Node -> Epoch]
  /\ acceptedValue \in [Node -> SUBSET Command]
  /\ recoverySet \in [Node -> SUBSET Server]
  /\ prepRcvd \in [Node -> SUBSET Server]
  /\ acceptRcvd \in [Node -> SUBSET Server]
  /\ chosenValue \in [Node -> SUBSET Command]
  /\ highestSeenBallot \in [Node -> Epoch]
  /\ highestSeenValue \in [Node -> SUBSET Command]
  /\ clientSuccesses \in [Node -> SUBSET Server]
  /\ clientHeardFrom \in [Node -> SUBSET Server]
  /\ clientEpoch \in [Node -> Epoch]
  /\ clientMembers \in [Node -> SUBSET Server]
  /\ clientProposers \in [Node -> SUBSET Server]
  /\ cmdPool \in [Node -> [Key -> CommandOrNil]]
  /\ clientPending \in [Node -> CommandOrNil]

(***************************************************************************)
(* FAST PATH                                                              *)
(*                                                                         *)
(* This is what `tier3/t3_01_jetpack` left out, and it is the part the     *)
(* paper is named for. A client proposes a command to the view's replicas; *)
(* each accepts if its epoch matches, it is not recovering, and the command*)
(* does not conflict with one it already holds for that key. The client    *)
(* commits as soon as the accepting replicas form a fast quorum.           *)
(***************************************************************************)
ClientSendPreaccept(c, cmd) ==
  /\ c \in Client
  /\ clientPending[c] = NilCmd
  /\ clientPending' = [clientPending EXCEPT ![c] = cmd]
  /\ clientSuccesses' = [clientSuccesses EXCEPT ![c] = {}]
  /\ clientHeardFrom' = [clientHeardFrom EXCEPT ![c] = {}]
  /\ msgs' = msgs \cup BroadcastPreaccept(c, clientEpoch[c], cmd,
                                          clientMembers[c])
  /\ UNCHANGED <<jstate, jepoch, oepoch, viewEpoch, viewMembers,
                 viewProposers, maxSeenBallot, acceptedBallot, acceptedValue,
                 cmdPool, recoverySet, prepRcvd, acceptRcvd, chosenValue,
                 highestSeenBallot, highestSeenValue, clientEpoch,
                 clientMembers, clientProposers>>

(***************************************************************************)
(* A replica pre-accepts. The original also appends to the leader's log     *)
(* here; that write belongs to the base protocol and is kept there, so the  *)
(* composition conjoins it (see `jetpack_raft_clean`).                      *)
(***************************************************************************)
HandlePreacceptRequest(i, m) ==
  /\ i \in Server
  /\ m.mdest = i
  /\ m.mtype = PreacceptRequest
  /\ cmdPool' =
       IF /\ m.mepoch = jepoch[i]
          /\ jstate[i] = Ready
          /\ ~HasConflict(cmdPool[i], m.mcmd)
         THEN [cmdPool EXCEPT ![i] = [cmdPool[i] EXCEPT ![m.mcmd.key] = m.mcmd]]
         ELSE cmdPool
  /\ msgs' = (msgs \ {m}) \cup
       {PreacceptResp(i, m.msource,
                      /\ m.mepoch = jepoch[i]
                      /\ jstate[i] = Ready
                      /\ ~HasConflict(cmdPool[i], m.mcmd),
                      jepoch[i], viewEpoch[i], viewMembers[i],
                      viewProposers[i], m.mcmd)}
  /\ UNCHANGED <<jstate, jepoch, oepoch, viewEpoch, viewMembers,
                 viewProposers, maxSeenBallot, acceptedBallot, acceptedValue,
                 recoverySet, prepRcvd, acceptRcvd, chosenValue,
                 highestSeenBallot, highestSeenValue, clientPending,
                 clientSuccesses, clientHeardFrom, clientEpoch,
                 clientMembers, clientProposers>>

(***************************************************************************)
(* The client tallies. Two powerset quantifications in the original become  *)
(* counting, and both use the same closed form:                            *)
(*                                                                         *)
(*  - success:  `newSuccesses \in FastpathQuorum(view)`                    *)
(*  - abandon:  `~\E q \in FastpathQuorum(view) : q \subseteq (successes    *)
(*               \cup unheard)`                                            *)
(*                                                                         *)
(* The second is `~IsFastQuorum(successes \cup unheard)` because a fast     *)
(* quorum is upward-closed among the sets that qualify: if the largest set  *)
(* still reachable is not one, no subset of it can be.                     *)
(***************************************************************************)
HandlePreacceptResponse(c, m) ==
  /\ c \in Client
  /\ m.mdest = c
  /\ m.mtype = PreacceptResponse
  /\ clientPending[c] # NilCmd
  /\ LET heard == clientHeardFrom[c] \cup {m.msource}
         succ  == IF m.msuccess
                    THEN clientSuccesses[c] \cup {m.msource}
                    ELSE clientSuccesses[c]
         fastOk == IsFastQuorum(succ, clientMembers[c], clientProposers[c])
         canStill == IsFastQuorum(succ \cup (clientMembers[c] \ heard),
                                  clientMembers[c], clientProposers[c])
         done == fastOk \/ ~canStill
     IN /\ clientSuccesses' = [clientSuccesses EXCEPT ![c] =
                                 IF done THEN {} ELSE succ]
        /\ clientHeardFrom' = [clientHeardFrom EXCEPT ![c] =
                                 IF done THEN {} ELSE heard]
        /\ clientPending' = [clientPending EXCEPT ![c] =
                               IF done THEN NilCmd ELSE clientPending[c]]
  /\ clientEpoch' = IF ~m.msuccess /\ m.mviewEpoch > clientEpoch[c]
                      THEN [clientEpoch EXCEPT ![c] = m.mviewEpoch]
                      ELSE clientEpoch
  /\ clientMembers' = IF ~m.msuccess /\ m.mviewEpoch > clientEpoch[c]
                        THEN [clientMembers EXCEPT ![c] = m.mviewMembers]
                        ELSE clientMembers
  /\ clientProposers' = IF ~m.msuccess /\ m.mviewEpoch > clientEpoch[c]
                          THEN [clientProposers EXCEPT ![c] = m.mviewProposers]
                          ELSE clientProposers
  /\ msgs' = msgs \ {m}
  /\ UNCHANGED <<jstate, jepoch, oepoch, viewEpoch, viewMembers,
                 viewProposers, maxSeenBallot, acceptedBallot, acceptedValue,
                 cmdPool, recoverySet, prepRcvd, acceptRcvd, chosenValue,
                 highestSeenBallot, highestSeenValue>>

(***************************************************************************)
(* RECOVERY -- phase 1, BeginRecovery.                                     *)
(***************************************************************************)
SendBeginRecovery(i, b) ==
  /\ i \in Server
  /\ jstate[i] = Ready
  /\ b > jepoch[i]
  /\ jepoch' = [jepoch EXCEPT ![i] = b]
  /\ jstate' = [jstate EXCEPT ![i] = Recovery]
  /\ recoverySet' = [recoverySet EXCEPT ![i] = {}]
  /\ highestSeenBallot' = [highestSeenBallot EXCEPT ![i] = 0]
  /\ highestSeenValue' = [highestSeenValue EXCEPT ![i] = {}]
  /\ msgs' = msgs \cup BroadcastBeginRecovery(i, b, viewEpoch[i],
                                              viewMembers[i],
                                              viewProposers[i],
                                              viewMembers[i])
  /\ UNCHANGED <<oepoch, viewEpoch, viewMembers, viewProposers,
                 maxSeenBallot, acceptedBallot, acceptedValue, cmdPool,
                 prepRcvd, acceptRcvd, chosenValue, clientPending,
                 clientSuccesses, clientHeardFrom, clientEpoch,
                 clientMembers, clientProposers>>

HandleBeginRecoveryRequest(i, m) ==
  /\ i \in Server
  /\ m.mdest = i
  /\ m.mtype = BeginRecoveryRequest
  /\ jstate' = [jstate EXCEPT ![i] = Recovery]
  /\ viewEpoch' = [viewEpoch EXCEPT ![i] = m.mviewEpoch]
  /\ viewMembers' = [viewMembers EXCEPT ![i] = m.mviewMembers]
  /\ viewProposers' = [viewProposers EXCEPT ![i] = m.mviewProposers]
  /\ oepoch' = [oepoch EXCEPT ![i] = m.mviewEpoch]
  /\ msgs' = (msgs \ {m}) \cup
       {BeginRecoveryResp(i, m.msource, acceptedBallot[i], acceptedValue[i])}
  /\ UNCHANGED <<jepoch, maxSeenBallot, acceptedBallot, acceptedValue,
                 cmdPool, recoverySet, prepRcvd, acceptRcvd, chosenValue,
                 highestSeenBallot, highestSeenValue, clientPending,
                 clientSuccesses, clientHeardFrom, clientEpoch,
                 clientMembers, clientProposers>>

HandleBeginRecoveryResponse(i, m) ==
  /\ i \in Server
  /\ m.mdest = i
  /\ m.mtype = BeginRecoveryResponse
  /\ jstate[i] = Recovery
  /\ recoverySet' = [recoverySet EXCEPT ![i] = recoverySet[i] \cup {m.msource}]
  /\ highestSeenBallot' =
       IF m.maccepted_ballot > highestSeenBallot[i]
         THEN [highestSeenBallot EXCEPT ![i] = m.maccepted_ballot]
         ELSE highestSeenBallot
  /\ highestSeenValue' =
       IF m.maccepted_ballot > highestSeenBallot[i]
         THEN [highestSeenValue EXCEPT ![i] = m.maccepted_value]
         ELSE highestSeenValue
  /\ msgs' = msgs \ {m}
  /\ UNCHANGED <<jstate, jepoch, oepoch, viewEpoch, viewMembers,
                 viewProposers, maxSeenBallot, acceptedBallot, acceptedValue,
                 cmdPool, prepRcvd, acceptRcvd, chosenValue, clientPending,
                 clientSuccesses, clientHeardFrom, clientEpoch,
                 clientMembers, clientProposers>>

CompleteBeginRecovery(i) ==
  /\ i \in Server
  /\ jstate[i] = Recovery
  /\ IsQuorum(recoverySet[i], viewMembers[i])
  /\ chosenValue' = [chosenValue EXCEPT ![i] = highestSeenValue[i]]
  /\ jstate' = [jstate EXCEPT ![i] = AfterBeginRecovery]
  /\ prepRcvd' = [prepRcvd EXCEPT ![i] = {}]
  /\ msgs' = msgs
  /\ UNCHANGED <<jepoch, oepoch, viewEpoch, viewMembers, viewProposers,
                 maxSeenBallot, acceptedBallot, acceptedValue, cmdPool,
                 recoverySet, acceptRcvd, highestSeenBallot,
                 highestSeenValue, clientPending, clientSuccesses,
                 clientHeardFrom, clientEpoch, clientMembers,
                 clientProposers>>

(***************************************************************************)
(* RECOVERY -- phase 2, Prepare. Paxos phase 1 under another name.         *)
(***************************************************************************)
SendPrepare(i) ==
  /\ i \in Server
  /\ jstate[i] = AfterBeginRecovery
  /\ msgs' = msgs \cup BroadcastPrepare(i, jepoch[i], oepoch[i],
                                        viewMembers[i])
  /\ UNCHANGED <<jstate, jepoch, oepoch, viewEpoch, viewMembers,
                 viewProposers, maxSeenBallot, acceptedBallot, acceptedValue,
                 cmdPool, recoverySet, prepRcvd, acceptRcvd, chosenValue,
                 highestSeenBallot, highestSeenValue, clientPending,
                 clientSuccesses, clientHeardFrom, clientEpoch,
                 clientMembers, clientProposers>>

HandlePrepareRequest(i, m) ==
  /\ i \in Server
  /\ m.mdest = i
  /\ m.mtype = PrepareRequest
  /\ m.moepoch >= oepoch[i]
  /\ m.mballot >= maxSeenBallot[i]
  /\ maxSeenBallot' = [maxSeenBallot EXCEPT ![i] = m.mballot]
  /\ oepoch' = [oepoch EXCEPT ![i] = m.moepoch]
  /\ msgs' = (msgs \ {m}) \cup
       {PrepareResp(i, m.msource, m.mballot,
                    acceptedBallot[i], acceptedValue[i])}
  /\ UNCHANGED <<jstate, jepoch, viewEpoch, viewMembers, viewProposers,
                 acceptedBallot, acceptedValue, cmdPool, recoverySet,
                 prepRcvd, acceptRcvd, chosenValue, highestSeenBallot,
                 highestSeenValue, clientPending, clientSuccesses,
                 clientHeardFrom, clientEpoch, clientMembers,
                 clientProposers>>

HandlePrepareResponse(i, m) ==
  /\ i \in Server
  /\ m.mdest = i
  /\ m.mtype = PrepareResponse
  /\ m.mballot = jepoch[i]
  /\ prepRcvd' = [prepRcvd EXCEPT ![i] = prepRcvd[i] \cup {m.msource}]
  /\ highestSeenBallot' =
       IF m.maccepted_ballot > highestSeenBallot[i]
         THEN [highestSeenBallot EXCEPT ![i] = m.maccepted_ballot]
         ELSE highestSeenBallot
  /\ highestSeenValue' =
       IF m.maccepted_ballot > highestSeenBallot[i]
         THEN [highestSeenValue EXCEPT ![i] = m.maccepted_value]
         ELSE highestSeenValue
  /\ msgs' = msgs \ {m}
  /\ UNCHANGED <<jstate, jepoch, oepoch, viewEpoch, viewMembers,
                 viewProposers, maxSeenBallot, acceptedBallot, acceptedValue,
                 cmdPool, recoverySet, acceptRcvd, chosenValue,
                 clientPending, clientSuccesses, clientHeardFrom,
                 clientEpoch, clientMembers, clientProposers>>

(***************************************************************************)
(* Paxos's safety core, and the one conjunct that must not be weakened: if  *)
(* any promise reported an accepted value, propose that value.             *)
(***************************************************************************)
CompletePrepare(i) ==
  /\ i \in Server
  /\ jstate[i] = AfterBeginRecovery
  /\ IsQuorum(prepRcvd[i], viewMembers[i])
  /\ chosenValue' = IF highestSeenBallot[i] > 0
                      THEN [chosenValue EXCEPT ![i] = highestSeenValue[i]]
                      ELSE chosenValue
  /\ jstate' = [jstate EXCEPT ![i] = AfterPrepare]
  /\ acceptRcvd' = [acceptRcvd EXCEPT ![i] = {}]
  /\ msgs' = msgs
  /\ UNCHANGED <<jepoch, oepoch, viewEpoch, viewMembers, viewProposers,
                 maxSeenBallot, acceptedBallot, acceptedValue, cmdPool,
                 recoverySet, prepRcvd, highestSeenBallot, highestSeenValue,
                 clientPending, clientSuccesses, clientHeardFrom,
                 clientEpoch, clientMembers, clientProposers>>

(***************************************************************************)
(* RECOVERY -- phase 3, Accept. Paxos phase 2.                            *)
(***************************************************************************)
SendAccept(i) ==
  /\ i \in Server
  /\ jstate[i] = AfterPrepare
  /\ msgs' = msgs \cup BroadcastAccept(i, jepoch[i], chosenValue[i],
                                       viewMembers[i])
  /\ UNCHANGED <<jstate, jepoch, oepoch, viewEpoch, viewMembers,
                 viewProposers, maxSeenBallot, acceptedBallot, acceptedValue,
                 cmdPool, recoverySet, prepRcvd, acceptRcvd, chosenValue,
                 highestSeenBallot, highestSeenValue, clientPending,
                 clientSuccesses, clientHeardFrom, clientEpoch,
                 clientMembers, clientProposers>>

HandleAcceptRequest(i, m) ==
  /\ i \in Server
  /\ m.mdest = i
  /\ m.mtype = AcceptRequest
  /\ m.mballot >= maxSeenBallot[i]
  /\ maxSeenBallot' = [maxSeenBallot EXCEPT ![i] = m.mballot]
  /\ acceptedBallot' = [acceptedBallot EXCEPT ![i] = m.mballot]
  /\ acceptedValue' = [acceptedValue EXCEPT ![i] = m.mvalue]
  /\ msgs' = (msgs \ {m}) \cup {AcceptResp(i, m.msource, m.mballot)}
  /\ UNCHANGED <<jstate, jepoch, oepoch, viewEpoch, viewMembers,
                 viewProposers, cmdPool, recoverySet, prepRcvd, acceptRcvd,
                 chosenValue, highestSeenBallot, highestSeenValue,
                 clientPending, clientSuccesses, clientHeardFrom,
                 clientEpoch, clientMembers, clientProposers>>

HandleAcceptResponse(i, m) ==
  /\ i \in Server
  /\ m.mdest = i
  /\ m.mtype = AcceptResponse
  /\ m.mballot = jepoch[i]
  /\ acceptRcvd' = [acceptRcvd EXCEPT ![i] = acceptRcvd[i] \cup {m.msource}]
  /\ msgs' = msgs \ {m}
  /\ UNCHANGED <<jstate, jepoch, oepoch, viewEpoch, viewMembers,
                 viewProposers, maxSeenBallot, acceptedBallot, acceptedValue,
                 cmdPool, recoverySet, prepRcvd, chosenValue,
                 highestSeenBallot, highestSeenValue, clientPending,
                 clientSuccesses, clientHeardFrom, clientEpoch,
                 clientMembers, clientProposers>>

CompleteAccept(i) ==
  /\ i \in Server
  /\ jstate[i] = AfterPrepare
  /\ IsQuorum(acceptRcvd[i], viewMembers[i])
  /\ jstate' = [jstate EXCEPT ![i] = AfterAccept]
  /\ msgs' = msgs
  /\ UNCHANGED <<jepoch, oepoch, viewEpoch, viewMembers, viewProposers,
                 maxSeenBallot, acceptedBallot, acceptedValue, cmdPool,
                 recoverySet, prepRcvd, acceptRcvd, chosenValue,
                 highestSeenBallot, highestSeenValue, clientPending,
                 clientSuccesses, clientHeardFrom, clientEpoch,
                 clientMembers, clientProposers>>

(***************************************************************************)
(* Resubmit: the recovered value is re-proposed through the fast path, then *)
(* recovery finishes and the base protocol may promote the node to Leader.  *)
(* `t3_01_jetpack` dropped both because it had no fast path to resubmit to. *)
(***************************************************************************)
Resubmit(i) ==
  /\ i \in Server
  /\ jstate[i] = AfterAccept
  /\ jstate' = [jstate EXCEPT ![i] = AfterResubmit]
  /\ msgs' = msgs \cup
       { PreacceptReq(i, d, jepoch[i], cmd) :
           d \in viewProposers[i], cmd \in chosenValue[i] }
  /\ UNCHANGED <<jepoch, oepoch, viewEpoch, viewMembers, viewProposers,
                 maxSeenBallot, acceptedBallot, acceptedValue, cmdPool,
                 recoverySet, prepRcvd, acceptRcvd, chosenValue,
                 highestSeenBallot, highestSeenValue, clientPending,
                 clientSuccesses, clientHeardFrom, clientEpoch,
                 clientMembers, clientProposers>>

FinishRecovery(i) ==
  /\ i \in Server
  /\ jstate[i] = AfterResubmit
  /\ jstate' = [jstate EXCEPT ![i] = Ready]
  /\ recoverySet' = [recoverySet EXCEPT ![i] = {}]
  /\ prepRcvd' = [prepRcvd EXCEPT ![i] = {}]
  /\ acceptRcvd' = [acceptRcvd EXCEPT ![i] = {}]
  /\ msgs' = msgs \cup BroadcastFinish(i, jepoch[i], viewMembers[i])
  /\ UNCHANGED <<jepoch, oepoch, viewEpoch, viewMembers, viewProposers,
                 maxSeenBallot, acceptedBallot, acceptedValue, cmdPool,
                 chosenValue, highestSeenBallot, highestSeenValue,
                 clientPending, clientSuccesses, clientHeardFrom,
                 clientEpoch, clientMembers, clientProposers>>

HandleFinishRecovery(i, m) ==
  /\ i \in Server
  /\ m.mdest = i
  /\ m.mtype = FinishRecoveryNotice
  /\ jstate' = [jstate EXCEPT ![i] = IF jstate[i] = Recovery
                                       THEN Ready ELSE jstate[i]]
  /\ msgs' = msgs \ {m}
  /\ UNCHANGED <<jepoch, oepoch, viewEpoch, viewMembers, viewProposers,
                 maxSeenBallot, acceptedBallot, acceptedValue, cmdPool,
                 recoverySet, prepRcvd, acceptRcvd, chosenValue,
                 highestSeenBallot, highestSeenValue, clientPending,
                 clientSuccesses, clientHeardFrom, clientEpoch,
                 clientMembers, clientProposers>>

=============================================================================
