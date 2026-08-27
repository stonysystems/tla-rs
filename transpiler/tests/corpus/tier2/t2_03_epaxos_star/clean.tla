--------------------------- MODULE EPaxosStarClean -------------------------
(***************************************************************************)
(* EPaxos* -- the corrected Egalitarian Paxos -- rewritten into the clean   *)
(* subset (C1-C5) of docs/clean_tla_subset.md.                             *)
(*                                                                          *)
(* Upstream is docs/epaxos_reference/EPaxosCommitWithRecovery.tla, the TLA+ *)
(* model attached to Ryabinin/Gotsman/Sutra, OPODIS 2025. See rewrite.md.   *)
(*                                                                          *)
(* THE SLICE: commit and recovery, which is all the reference has.          *)
(* Execution -- the dependency-graph ordering that makes EPaxos a state     *)
(* machine -- is absent HERE because it is absent THERE, and absent from    *)
(* the 2013 spec too, where `executed'` never appears.                      *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS
    Proc,                   \* the node set
    Payload,                \* real command payloads
    Nop,                    \* recovery's abort value; conflicts with everything
    Bottom,                 \* "no payload yet"; conflicts with nothing
    ConflictPairs,          \* the conflict relation, as a model constant
    MaxNum,                 \* model bound: instances per node
    MaxRecoveryAttempts,    \* model bound: recovery attempts per node per instance
    F,                      \* crash tolerance
    E                       \* fast-path tolerance

N == Cardinality(Proc)

Max2(a, b) == IF a > b THEN a ELSE b
ASSUME N >= Max2(2*E + F - 1, 2*F + 1)
ASSUME E <= F
\* Ballots are k*N + p, so a process identity has to be arithmetic -- and it
\* must be non-zero, because `StartRecover`'s first ballot for p IS p and
\* `ApplyRecover` requires `bal < b`. With 0 \in Proc, replica 0 could never
\* start recovery. The reference has Proc = {1,2,3} and relies on this
\* silently; stating it is the point.
ASSUME Proc \subseteq Nat \ {0}

(***************************************************************************)
(* An instance identifier carries its owner.                                *)
(*                                                                          *)
(* The reference uses a flat `Id` set plus a GLOBAL `initCoord[id]` map and *)
(* a GLOBAL `submitted` set -- the only two variables in it that are not    *)
(* per-node, and so its only two C1 violations. Every read of               *)
(* `initCoord[id]` is "who owns this id", and `submitted` is read only as   *)
(* "have I used this id". Folding the owner into the identifier turns the   *)
(* first into a projection and the second into a per-node counter. This is  *)
(* how the 2013 spec writes an instance too: <<cleader, crtInst[cleader]>>. *)
(***************************************************************************)
Id == [owner: Proc, num: 1..MaxNum]
MkId(o, n) == [owner |-> o, num |-> n]

Cmds == Payload \cup {Nop, Bottom}

InitialPhase == "initial"
PreAccepted  == "pre-accepted"
Accepted     == "accepted"
Committed    == "committed"
Phases == {InitialPhase, PreAccepted, Accepted, Committed}

StartP    == "start"
RecoverOKP == "recover-ok"
ValidateOKP == "validate-ok"
PostWaitingP == "post-waiting"
RecoveryPhases == {StartP, RecoverOKP, ValidateOKP, PostWaitingP}

(***************************************************************************)
(* Conflicts. Bottom conflicts with nothing -- a replica that has seen no   *)
(* payload cannot order anything against it. Nop conflicts with everything, *)
(* which is what makes it safe for recovery to substitute.                  *)
(***************************************************************************)
Conflicts(c1, c2) ==
    IF c1 = Bottom \/ c2 = Bottom THEN FALSE
    ELSE IF c1 = Nop \/ c2 = Nop THEN TRUE
    ELSE <<c1, c2>> \in ConflictPairs \/ <<c2, c1>> \in ConflictPairs

(***************************************************************************)
(* P4: quorums by counting. The two sizes are what separates the fast path  *)
(* from the slow one, and keeping them distinct is the point.               *)
(***************************************************************************)
IsQuorum(s)     == Cardinality(s) >= N - F
IsFastQuorum(s) == Cardinality(s) >= N - E

(***************************************************************************)
(* Message types.                                                           *)
(***************************************************************************)
PreAcceptT == "paq"
PreAcceptOKT == "pap"
AcceptT == "aq"
AcceptOKT == "ap"
CommitT == "cmt"
RecoverT == "rec"
RecoverOKT == "recok"
ValidateT == "val"
ValidateOKT == "valok"
WaitingT == "wait"

Invalidator == [id: Id, phase: Phases]
RecoverInfo == [from: Proc, abal: Nat, cmd: Cmds, dep: SUBSET Id,
                initDep: SUBSET Id, phase: Phases]

VARIABLES
    \* ---- protocol state, per node per instance ----
    phase, bal, abal, initCmd, cmd, initDep, dep,
    \* ---- reply accumulators ----
    (* The clean subset does not let an action scan the network for a       *)
    (* quorum (C4 whitelists send/receive, not search), so each quorum rule *)
    (* becomes record-then-act and the accumulator carries what the rule    *)
    (* reads. `t2_02_epaxos/clean.tla` made the same move for the same      *)
    (* reason. The ballot-scoped ones are cleared when the ballot moves,    *)
    (* because the reference re-filters `msgs` on `bal` every time.         *)
    preAcceptRcvd, preAcceptAgreed, preAcceptDepUnion,
    acceptRcvd, recoverReplies, validateRcvd,
    \* ---- recovery bookkeeping ----
    recovered, recoveryPhase, qvar, cvar, dvar, ivar, cardRmax, recoveryBal,
    \* ---- per-node instance allocator (replaces the global `submitted`) ----
    crtInst,
    \* ---- the network ----
    msgs

vars == <<phase, bal, abal, initCmd, cmd, initDep, dep,
          preAcceptRcvd, preAcceptAgreed, preAcceptDepUnion,
          acceptRcvd, recoverReplies, validateRcvd,
          recovered, recoveryPhase, qvar, cvar, dvar, ivar, cardRmax,
          recoveryBal, crtInst, msgs>>

Message ==
       [mtype: {PreAcceptT}, minst: Id, mcmd: Cmds, mdep: SUBSET Id,
        msource: Proc, mdest: Proc]
  \cup [mtype: {PreAcceptOKT}, minst: Id, mdep: SUBSET Id,
        msource: Proc, mdest: Proc]
  \cup [mtype: {AcceptT}, minst: Id, mbal: Nat, mcmd: Cmds, mdep: SUBSET Id,
        msource: Proc, mdest: Proc]
  \cup [mtype: {AcceptOKT}, minst: Id, mbal: Nat, msource: Proc, mdest: Proc]
  \cup [mtype: {CommitT}, minst: Id, mbal: Nat, mcmd: Cmds, mdep: SUBSET Id,
        msource: Proc, mdest: Proc]
  \cup [mtype: {RecoverT}, minst: Id, mbal: Nat, msource: Proc, mdest: Proc]
  \cup [mtype: {RecoverOKT}, minst: Id, mbal: Nat, mabal: Nat, mcmd: Cmds,
        mdep: SUBSET Id, minitDep: SUBSET Id, mphase: Phases,
        msource: Proc, mdest: Proc]
  \cup [mtype: {ValidateT}, minst: Id, mbal: Nat, mcmd: Cmds, mdep: SUBSET Id,
        msource: Proc, mdest: Proc]
  \cup [mtype: {ValidateOKT}, minst: Id, mbal: Nat, miq: SUBSET Invalidator,
        msource: Proc, mdest: Proc]
  \cup [mtype: {WaitingT}, minst: Id, mk: Nat, msource: Proc, mdest: Proc]

TypeOK ==
    /\ phase \in [Proc -> [Id -> Phases]]
    /\ bal \in [Proc -> [Id -> Nat]]
    /\ abal \in [Proc -> [Id -> Nat]]
    /\ initCmd \in [Proc -> [Id -> Cmds]]
    /\ cmd \in [Proc -> [Id -> Cmds]]
    /\ initDep \in [Proc -> [Id -> SUBSET Id]]
    /\ dep \in [Proc -> [Id -> SUBSET Id]]
    /\ preAcceptRcvd \in [Proc -> [Id -> SUBSET Proc]]
    /\ preAcceptAgreed \in [Proc -> [Id -> SUBSET Proc]]
    /\ preAcceptDepUnion \in [Proc -> [Id -> SUBSET Id]]
    /\ acceptRcvd \in [Proc -> [Id -> SUBSET Proc]]
    /\ recoverReplies \in [Proc -> [Id -> SUBSET RecoverInfo]]
    /\ validateRcvd \in [Proc -> [Id -> SUBSET Proc]]
    /\ recovered \in [Proc -> [Id -> 0..MaxRecoveryAttempts]]
    /\ recoveryPhase \in [Proc -> [Id -> RecoveryPhases]]
    /\ qvar \in [Proc -> [Id -> SUBSET Proc]]
    /\ cvar \in [Proc -> [Id -> Cmds]]
    /\ dvar \in [Proc -> [Id -> SUBSET Id]]
    /\ ivar \in [Proc -> [Id -> SUBSET Invalidator]]
    /\ cardRmax \in [Proc -> [Id -> 0..N]]
    /\ recoveryBal \in [Proc -> [Id -> Nat]]
    /\ crtInst \in [Proc -> 1..(MaxNum + 1)]
    /\ msgs \subseteq Message

Init ==
    /\ phase = [i \in Proc |-> [d \in Id |-> InitialPhase]]
    /\ bal = [i \in Proc |-> [d \in Id |-> 0]]
    /\ abal = [i \in Proc |-> [d \in Id |-> 0]]
    /\ initCmd = [i \in Proc |-> [d \in Id |-> Bottom]]
    /\ cmd = [i \in Proc |-> [d \in Id |-> Bottom]]
    /\ initDep = [i \in Proc |-> [d \in Id |-> {}]]
    /\ dep = [i \in Proc |-> [d \in Id |-> {}]]
    /\ preAcceptRcvd = [i \in Proc |-> [d \in Id |-> {}]]
    /\ preAcceptAgreed = [i \in Proc |-> [d \in Id |-> {}]]
    /\ preAcceptDepUnion = [i \in Proc |-> [d \in Id |-> {}]]
    /\ acceptRcvd = [i \in Proc |-> [d \in Id |-> {}]]
    /\ recoverReplies = [i \in Proc |-> [d \in Id |-> {}]]
    /\ validateRcvd = [i \in Proc |-> [d \in Id |-> {}]]
    /\ recovered = [i \in Proc |-> [d \in Id |-> 0]]
    /\ recoveryPhase = [i \in Proc |-> [d \in Id |-> StartP]]
    /\ qvar = [i \in Proc |-> [d \in Id |-> {}]]
    /\ cvar = [i \in Proc |-> [d \in Id |-> Bottom]]
    /\ dvar = [i \in Proc |-> [d \in Id |-> {}]]
    /\ ivar = [i \in Proc |-> [d \in Id |-> {}]]
    /\ cardRmax = [i \in Proc |-> [d \in Id |-> 0]]
    /\ recoveryBal = [i \in Proc |-> [d \in Id |-> 0]]
    /\ crtInst = [i \in Proc |-> 1]
    /\ msgs = {}

(***************************************************************************)
(* Dependencies a node computes for a payload: every instance it knows      *)
(* whose payload conflicts.                                                 *)
(***************************************************************************)
ConflictingIds(i, c) == { d \in Id : Conflicts(cmd[i][d], c) }

SeenId(i, d) ==
    \/ cmd[i][d] # Bottom
    \/ \E d2 \in Id : d \in dep[i][d2]

Broadcast(i, m) == { [m EXCEPT !.mdest = q] : q \in Proc \ {i} }
BroadcastTo(i, S, m) == { [m EXCEPT !.mdest = q] : q \in S \ {i} }


(***************************************************************************)
(* Frame groups. Most commit-path actions touch none of the recovery       *)
(* bookkeeping, so naming it once keeps the UNCHANGED lists readable.       *)
(***************************************************************************)
recVars == <<recovered, recoveryPhase, qvar, cvar, dvar, ivar, cardRmax, recoveryBal>>

(***************************************************************************)
(* Commit path                                                              *)
(***************************************************************************)

Submit(i, c) ==
    LET d  == MkId(i, crtInst[i])
        D0 == ConflictingIds(i, c)
    IN  /\ crtInst[i] <= MaxNum
        /\ bal[i][d] = 0
        /\ phase[i][d] = InitialPhase
        /\ crtInst' = [crtInst EXCEPT ![i] = crtInst[i] + 1]
        /\ phase'   = [phase   EXCEPT ![i][d] = PreAccepted]
        /\ cmd'     = [cmd     EXCEPT ![i][d] = c]
        /\ initCmd' = [initCmd EXCEPT ![i][d] = c]
        /\ initDep' = [initDep EXCEPT ![i][d] = D0]
        /\ dep'     = [dep     EXCEPT ![i][d] = D0]
        /\ msgs' = msgs
             \cup Broadcast(i, [mtype |-> PreAcceptT, minst |-> d, mcmd |-> c,
                                mdep |-> D0, msource |-> i, mdest |-> i])
             \cup {[mtype |-> PreAcceptOKT, minst |-> d, mdep |-> D0,
                    msource |-> i, mdest |-> i]}
        /\ UNCHANGED <<bal, abal, preAcceptRcvd, preAcceptAgreed,
                       preAcceptDepUnion, acceptRcvd, recoverReplies,
                       validateRcvd>>
        /\ UNCHANGED recVars

HandlePreAccept(i, m) ==
    /\ m.mtype = PreAcceptT
    /\ m.mdest = i
    /\ bal[i][m.minst] = 0
    /\ phase[i][m.minst] = InitialPhase
    /\ LET Dfinal == m.mdep \cup ConflictingIds(i, m.mcmd) IN
        /\ phase'   = [phase   EXCEPT ![i][m.minst] = PreAccepted]
        /\ cmd'     = [cmd     EXCEPT ![i][m.minst] = m.mcmd]
        /\ initCmd' = [initCmd EXCEPT ![i][m.minst] = m.mcmd]
        /\ initDep' = [initDep EXCEPT ![i][m.minst] = m.mdep]
        /\ dep'     = [dep     EXCEPT ![i][m.minst] = Dfinal]
        /\ msgs' = (msgs \ {m}) \cup
             {[mtype |-> PreAcceptOKT, minst |-> m.minst, mdep |-> Dfinal,
               msource |-> i, mdest |-> m.msource]}
    /\ UNCHANGED <<bal, abal, preAcceptRcvd, preAcceptAgreed,
                   preAcceptDepUnion, acceptRcvd, recoverReplies,
                   validateRcvd, crtInst>>
    /\ UNCHANGED recVars

RecordPreAcceptOK(i, m) ==
    /\ m.mtype = PreAcceptOKT
    /\ m.mdest = i
    /\ bal[i][m.minst] = 0
    /\ phase[i][m.minst] = PreAccepted
    /\ m.msource \notin preAcceptRcvd[i][m.minst]
    /\ preAcceptRcvd' = [preAcceptRcvd EXCEPT ![i][m.minst] = @ \cup {m.msource}]
    /\ preAcceptAgreed' =
         IF m.mdep = initDep[i][m.minst]
           THEN [preAcceptAgreed EXCEPT ![i][m.minst] = @ \cup {m.msource}]
           ELSE preAcceptAgreed
    /\ preAcceptDepUnion' = [preAcceptDepUnion EXCEPT ![i][m.minst] = @ \cup m.mdep]
    /\ msgs' = msgs \ {m}
    /\ UNCHANGED <<phase, bal, abal, initCmd, cmd, initDep, dep,
                   acceptRcvd, recoverReplies, validateRcvd, crtInst>>
    /\ UNCHANGED recVars

CommitFast(i, d) ==
    /\ bal[i][d] = 0
    /\ phase[i][d] = PreAccepted
    /\ IsQuorum(preAcceptRcvd[i][d])
    /\ IsFastQuorum(preAcceptAgreed[i][d])
    /\ phase' = [phase EXCEPT ![i][d] = Committed]
    /\ abal'  = [abal  EXCEPT ![i][d] = 0]
    /\ dep'   = [dep   EXCEPT ![i][d] = initDep[i][d]]
    /\ msgs' = msgs \cup
         Broadcast(i, [mtype |-> CommitT, minst |-> d, mbal |-> 0,
                       mcmd |-> cmd[i][d], mdep |-> initDep[i][d],
                       msource |-> i, mdest |-> i])
    /\ UNCHANGED <<bal, initCmd, cmd, initDep, preAcceptRcvd, preAcceptAgreed,
                   preAcceptDepUnion, acceptRcvd, recoverReplies,
                   validateRcvd, crtInst>>
    /\ UNCHANGED recVars

StartAccept(i, d) ==
    /\ bal[i][d] = 0
    /\ phase[i][d] = PreAccepted
    /\ IsQuorum(preAcceptRcvd[i][d])
    /\ ~IsFastQuorum(preAcceptAgreed[i][d])
    /\ phase' = [phase EXCEPT ![i][d] = Accepted]
    /\ abal'  = [abal  EXCEPT ![i][d] = 0]
    /\ dep'   = [dep   EXCEPT ![i][d] = preAcceptDepUnion[i][d]]
    /\ acceptRcvd'    = [acceptRcvd    EXCEPT ![i][d] = {}]
    /\ recoverReplies' = [recoverReplies EXCEPT ![i][d] = {}]
    /\ validateRcvd'  = [validateRcvd  EXCEPT ![i][d] = {}]
    /\ msgs' = msgs
         \cup Broadcast(i, [mtype |-> AcceptT, minst |-> d, mbal |-> 0,
                            mcmd |-> cmd[i][d], mdep |-> preAcceptDepUnion[i][d],
                            msource |-> i, mdest |-> i])
         \cup {[mtype |-> AcceptOKT, minst |-> d, mbal |-> 0,
                msource |-> i, mdest |-> i]}
    /\ UNCHANGED <<bal, initCmd, cmd, initDep, preAcceptRcvd, preAcceptAgreed,
                   preAcceptDepUnion, crtInst>>
    /\ UNCHANGED recVars

HandleAccept(i, m) ==
    /\ m.mtype = AcceptT
    /\ m.mdest = i
    /\ bal[i][m.minst] <= m.mbal
    /\ (bal[i][m.minst] = m.mbal => phase[i][m.minst] # Committed)
    /\ phase' = [phase EXCEPT ![i][m.minst] = Accepted]
    /\ bal'   = [bal   EXCEPT ![i][m.minst] = m.mbal]
    /\ abal'  = [abal  EXCEPT ![i][m.minst] = m.mbal]
    /\ cmd'   = [cmd   EXCEPT ![i][m.minst] = m.mcmd]
    /\ dep'   = [dep   EXCEPT ![i][m.minst] = m.mdep]
    /\ acceptRcvd'    = [acceptRcvd    EXCEPT ![i][m.minst] = {}]
    /\ recoverReplies' = [recoverReplies EXCEPT ![i][m.minst] = {}]
    /\ validateRcvd'  = [validateRcvd  EXCEPT ![i][m.minst] = {}]
    /\ msgs' = (msgs \ {m}) \cup
         {[mtype |-> AcceptOKT, minst |-> m.minst, mbal |-> m.mbal,
           msource |-> i, mdest |-> m.msource]}
    /\ UNCHANGED <<initCmd, initDep, preAcceptRcvd, preAcceptAgreed,
                   preAcceptDepUnion, crtInst>>
    /\ UNCHANGED recVars

RecordAcceptOK(i, m) ==
    /\ m.mtype = AcceptOKT
    /\ m.mdest = i
    /\ phase[i][m.minst] = Accepted
    /\ m.mbal = bal[i][m.minst]
    /\ m.msource \notin acceptRcvd[i][m.minst]
    /\ acceptRcvd' = [acceptRcvd EXCEPT ![i][m.minst] = @ \cup {m.msource}]
    /\ msgs' = msgs \ {m}
    /\ UNCHANGED <<phase, bal, abal, initCmd, cmd, initDep, dep,
                   preAcceptRcvd, preAcceptAgreed, preAcceptDepUnion,
                   recoverReplies, validateRcvd, crtInst>>
    /\ UNCHANGED recVars

CommitSlow(i, d) ==
    /\ phase[i][d] = Accepted
    /\ IsQuorum(acceptRcvd[i][d])
    /\ phase' = [phase EXCEPT ![i][d] = Committed]
    /\ abal'  = [abal  EXCEPT ![i][d] = bal[i][d]]
    /\ msgs' = msgs \cup
         Broadcast(i, [mtype |-> CommitT, minst |-> d, mbal |-> bal[i][d],
                       mcmd |-> cmd[i][d], mdep |-> dep[i][d],
                       msource |-> i, mdest |-> i])
    /\ UNCHANGED <<bal, initCmd, cmd, initDep, dep, preAcceptRcvd,
                   preAcceptAgreed, preAcceptDepUnion, acceptRcvd,
                   recoverReplies, validateRcvd, crtInst>>
    /\ UNCHANGED recVars

HandleCommit(i, m) ==
    /\ m.mtype = CommitT
    /\ m.mdest = i
    /\ bal[i][m.minst] = m.mbal
    /\ phase' = [phase EXCEPT ![i][m.minst] = Committed]
    /\ abal'  = [abal  EXCEPT ![i][m.minst] = m.mbal]
    /\ cmd'   = [cmd   EXCEPT ![i][m.minst] = m.mcmd]
    /\ dep'   = [dep   EXCEPT ![i][m.minst] = m.mdep]
    /\ msgs' = msgs \ {m}
    /\ UNCHANGED <<bal, initCmd, initDep, preAcceptRcvd, preAcceptAgreed,
                   preAcceptDepUnion, acceptRcvd, recoverReplies,
                   validateRcvd, crtInst>>
    /\ UNCHANGED recVars


(***************************************************************************)
(* Recovery -- helpers                                                      *)
(***************************************************************************)
Abals(i, d)   == { r.abal : r \in recoverReplies[i][d] }
MaxAbal(i, d) == CHOOSE b \in Abals(i, d) : \A b2 \in Abals(i, d) : b >= b2
USet(i, d)    == { r \in recoverReplies[i][d] : r.abal = MaxAbal(i, d) }
RmaxSet(i, d) == { r \in recoverReplies[i][d] :
                     r.phase = PreAccepted /\ r.dep = r.initDep }
QSet(i, d)    == { r.from : r \in recoverReplies[i][d] }

(***************************************************************************)
(* `I`: commands that could invalidate committing (c, D) for d -- outside   *)
(* D, conflicting with c, and not carrying d among their own dependencies.  *)
(***************************************************************************)
ComputeI(i, d, c, D) ==
    { [id |-> d3, phase |-> phase[i][d3]] : d3 \in
        { d4 \in Id :
            /\ d4 # d
            /\ d4 \notin D
            /\ (phase[i][d4] = Committed =>
                  /\ cmd[i][d4] # Nop
                  /\ d \notin dep[i][d4]
                  /\ Conflicts(c, cmd[i][d4]))
            /\ (phase[i][d4] # Committed =>
                  /\ initCmd[i][d4] # Bottom
                  /\ d \notin initDep[i][d4]
                  /\ Conflicts(c, initCmd[i][d4])) } }

(***************************************************************************)
(* Recovery                                                                 *)
(***************************************************************************)

StartRecover(i, d) ==
    LET b == IF bal[i][d] = 0 THEN i ELSE bal[i][d] + N IN
    /\ recovered[i][d] < MaxRecoveryAttempts
    /\ SeenId(i, d)
    /\ bal[i][d] < b
    /\ bal' = [bal EXCEPT ![i][d] = b]
    /\ recovered' = [recovered EXCEPT ![i][d] = @ + 1]
    /\ recoveryPhase' = [recoveryPhase EXCEPT ![i][d] = RecoverOKP]
    /\ acceptRcvd'     = [acceptRcvd     EXCEPT ![i][d] = {}]
    /\ recoverReplies' = [recoverReplies EXCEPT ![i][d] =
         {[from |-> i, abal |-> abal[i][d], cmd |-> cmd[i][d],
           dep |-> dep[i][d], initDep |-> initDep[i][d], phase |-> phase[i][d]]}]
    /\ validateRcvd'   = [validateRcvd   EXCEPT ![i][d] = {}]
    /\ msgs' = msgs \cup
         Broadcast(i, [mtype |-> RecoverT, minst |-> d, mbal |-> b,
                       msource |-> i, mdest |-> i])
    /\ UNCHANGED <<phase, abal, initCmd, cmd, initDep, dep, preAcceptRcvd,
                   preAcceptAgreed, preAcceptDepUnion, crtInst,
                   qvar, cvar, dvar, ivar, cardRmax, recoveryBal>>

HandleRecover(i, m) ==
    /\ m.mtype = RecoverT
    /\ m.mdest = i
    /\ bal[i][m.minst] < m.mbal
    /\ bal' = [bal EXCEPT ![i][m.minst] = m.mbal]
    /\ acceptRcvd'     = [acceptRcvd     EXCEPT ![i][m.minst] = {}]
    /\ recoverReplies' = [recoverReplies EXCEPT ![i][m.minst] = {}]
    /\ validateRcvd'   = [validateRcvd   EXCEPT ![i][m.minst] = {}]
    /\ msgs' = (msgs \ {m}) \cup
         {[mtype |-> RecoverOKT, minst |-> m.minst, mbal |-> m.mbal,
           mabal |-> abal[i][m.minst], mcmd |-> cmd[i][m.minst],
           mdep |-> dep[i][m.minst], minitDep |-> initDep[i][m.minst],
           mphase |-> phase[i][m.minst], msource |-> i, mdest |-> m.msource]}
    /\ UNCHANGED <<phase, abal, initCmd, cmd, initDep, dep, preAcceptRcvd,
                   preAcceptAgreed, preAcceptDepUnion, crtInst>>
    /\ UNCHANGED recVars

RecordRecoverOK(i, m) ==
    /\ m.mtype = RecoverOKT
    /\ m.mdest = i
    /\ recoveryPhase[i][m.minst] = RecoverOKP
    /\ m.mbal = bal[i][m.minst]
    /\ m.msource \notin QSet(i, m.minst)
    /\ recoverReplies' = [recoverReplies EXCEPT ![i][m.minst] = @ \cup
         {[from |-> m.msource, abal |-> m.mabal, cmd |-> m.mcmd,
           dep |-> m.mdep, initDep |-> m.minitDep, phase |-> m.mphase]}]
    /\ msgs' = msgs \ {m}
    /\ UNCHANGED <<phase, bal, abal, initCmd, cmd, initDep, dep,
                   preAcceptRcvd, preAcceptAgreed, preAcceptDepUnion,
                   acceptRcvd, validateRcvd, crtInst>>
    /\ UNCHANGED recVars

RecoverReady(i, d) ==
    /\ recoveryPhase[i][d] = RecoverOKP
    /\ IsQuorum(QSet(i, d))

\* Branch 1: someone at the highest abal had committed. Adopt it.
RecoverCommitted(i, d) ==
    /\ RecoverReady(i, d)
    /\ \E r \in USet(i, d) : r.phase = Committed
    /\ LET w == CHOOSE r \in USet(i, d) : r.phase = Committed IN
        /\ phase' = [phase EXCEPT ![i][d] = Committed]
        /\ abal'  = [abal  EXCEPT ![i][d] = bal[i][d]]
        /\ cmd'   = [cmd   EXCEPT ![i][d] = w.cmd]
        /\ dep'   = [dep   EXCEPT ![i][d] = w.dep]
        /\ msgs' = msgs \cup
             Broadcast(i, [mtype |-> CommitT, minst |-> d, mbal |-> bal[i][d],
                           mcmd |-> w.cmd, mdep |-> w.dep,
                           msource |-> i, mdest |-> i])
    /\ recoveryPhase' = [recoveryPhase EXCEPT ![i][d] = StartP]
    /\ UNCHANGED <<bal, initCmd, initDep, preAcceptRcvd, preAcceptAgreed,
                   preAcceptDepUnion, acceptRcvd, recoverReplies,
                   validateRcvd, crtInst, recovered, qvar, cvar, dvar, ivar,
                   cardRmax, recoveryBal>>

\* Branch 2: nobody committed, but someone at the highest abal had accepted.
RecoverAccepted(i, d) ==
    /\ RecoverReady(i, d)
    /\ ~(\E r \in USet(i, d) : r.phase = Committed)
    /\ \E r \in USet(i, d) : r.phase = Accepted
    /\ LET w == CHOOSE r \in USet(i, d) : r.phase = Accepted IN
        /\ phase' = [phase EXCEPT ![i][d] = Accepted]
        /\ abal'  = [abal  EXCEPT ![i][d] = bal[i][d]]
        /\ cmd'   = [cmd   EXCEPT ![i][d] = w.cmd]
        /\ dep'   = [dep   EXCEPT ![i][d] = w.dep]
        /\ msgs' = msgs
             \cup Broadcast(i, [mtype |-> AcceptT, minst |-> d, mbal |-> bal[i][d],
                                mcmd |-> w.cmd, mdep |-> w.dep,
                                msource |-> i, mdest |-> i])
             \cup {[mtype |-> AcceptOKT, minst |-> d, mbal |-> bal[i][d],
                    msource |-> i, mdest |-> i]}
    /\ recoveryPhase' = [recoveryPhase EXCEPT ![i][d] = StartP]
    /\ acceptRcvd'     = [acceptRcvd     EXCEPT ![i][d] = {}]
    /\ recoverReplies' = [recoverReplies EXCEPT ![i][d] = {}]
    /\ validateRcvd'   = [validateRcvd   EXCEPT ![i][d] = {}]
    /\ UNCHANGED <<bal, initCmd, initDep, preAcceptRcvd, preAcceptAgreed,
                   preAcceptDepUnion, crtInst, recovered, qvar, cvar, dvar,
                   ivar, cardRmax, recoveryBal>>

\* Branches 3 and 5: take Nop. Branch 3 is "the owner is in the quorum and
\* would have told us"; branch 5 is "too few pre-accepted unchanged for the
\* fast path to have been possible".
RecoverNop(i, d) ==
    /\ RecoverReady(i, d)
    /\ ~(\E r \in USet(i, d) : r.phase = Committed)
    /\ ~(\E r \in USet(i, d) : r.phase = Accepted)
    /\ \/ d.owner \in QSet(i, d)
       \/ Cardinality(RmaxSet(i, d)) + E < Cardinality(QSet(i, d))
    /\ phase' = [phase EXCEPT ![i][d] = Accepted]
    /\ abal'  = [abal  EXCEPT ![i][d] = bal[i][d]]
    /\ cmd'   = [cmd   EXCEPT ![i][d] = Nop]
    /\ dep'   = [dep   EXCEPT ![i][d] = {}]
    /\ msgs' = msgs
         \cup Broadcast(i, [mtype |-> AcceptT, minst |-> d, mbal |-> bal[i][d],
                            mcmd |-> Nop, mdep |-> {}, msource |-> i, mdest |-> i])
         \cup {[mtype |-> AcceptOKT, minst |-> d, mbal |-> bal[i][d],
                msource |-> i, mdest |-> i]}
    /\ recoveryPhase' = [recoveryPhase EXCEPT ![i][d] = StartP]
    /\ acceptRcvd'     = [acceptRcvd     EXCEPT ![i][d] = {}]
    /\ recoverReplies' = [recoverReplies EXCEPT ![i][d] = {}]
    /\ validateRcvd'   = [validateRcvd   EXCEPT ![i][d] = {}]
    /\ UNCHANGED <<bal, initCmd, initDep, preAcceptRcvd, preAcceptAgreed,
                   preAcceptDepUnion, crtInst, recovered, qvar, cvar, dvar,
                   ivar, cardRmax, recoveryBal>>

\* Branch 4 -- the paper's contribution. Enough of the quorum pre-accepted
\* with dependencies unchanged that the fast path MIGHT have committed, so
\* probe rather than guess.
RecoverValidate(i, d) ==
    /\ RecoverReady(i, d)
    /\ ~(\E r \in USet(i, d) : r.phase = Committed)
    /\ ~(\E r \in USet(i, d) : r.phase = Accepted)
    /\ d.owner \notin QSet(i, d)
    /\ Cardinality(RmaxSet(i, d)) + E >= Cardinality(QSet(i, d))
    /\ LET w == CHOOSE r \in RmaxSet(i, d) : TRUE IN
        /\ cvar'    = [cvar    EXCEPT ![i][d] = w.cmd]
        /\ dvar'    = [dvar    EXCEPT ![i][d] = w.dep]
        /\ cmd'     = [cmd     EXCEPT ![i][d] = w.cmd]
        /\ initCmd' = [initCmd EXCEPT ![i][d] = w.cmd]
        /\ initDep' = [initDep EXCEPT ![i][d] = w.dep]
        /\ msgs' = msgs
             \cup BroadcastTo(i, QSet(i, d),
                    [mtype |-> ValidateT, minst |-> d, mbal |-> bal[i][d],
                     mcmd |-> w.cmd, mdep |-> w.dep, msource |-> i, mdest |-> i])
             \cup {[mtype |-> ValidateOKT, minst |-> d, mbal |-> bal[i][d],
                    miq |-> ComputeI(i, d, w.cmd, w.dep),
                    msource |-> i, mdest |-> i]}
    /\ qvar'     = [qvar     EXCEPT ![i][d] = QSet(i, d)]
    /\ cardRmax' = [cardRmax EXCEPT ![i][d] = Cardinality(RmaxSet(i, d))]
    /\ recoveryBal' = [recoveryBal EXCEPT ![i][d] = bal[i][d]]
    /\ recoveryPhase' = [recoveryPhase EXCEPT ![i][d] = ValidateOKP]
    /\ validateRcvd' = [validateRcvd EXCEPT ![i][d] = {}]
    /\ ivar' = [ivar EXCEPT ![i][d] = {}]
    /\ UNCHANGED <<phase, bal, abal, dep, preAcceptRcvd, preAcceptAgreed,
                   preAcceptDepUnion, acceptRcvd, recoverReplies, crtInst,
                   recovered>>


(***************************************************************************)
(* Validation sub-protocol                                                  *)
(***************************************************************************)

HandleValidate(i, m) ==
    /\ m.mtype = ValidateT
    /\ m.mdest = i
    /\ bal[i][m.minst] = m.mbal
    /\ cmd'     = [cmd     EXCEPT ![i][m.minst] = m.mcmd]
    /\ initCmd' = [initCmd EXCEPT ![i][m.minst] = m.mcmd]
    /\ initDep' = [initDep EXCEPT ![i][m.minst] = m.mdep]
    /\ msgs' = (msgs \ {m}) \cup
         {[mtype |-> ValidateOKT, minst |-> m.minst, mbal |-> m.mbal,
           miq |-> ComputeI(i, m.minst, m.mcmd, m.mdep),
           msource |-> i, mdest |-> m.msource]}
    /\ UNCHANGED <<phase, bal, abal, dep, preAcceptRcvd, preAcceptAgreed,
                   preAcceptDepUnion, acceptRcvd, recoverReplies,
                   validateRcvd, crtInst>>
    /\ UNCHANGED recVars

RecordValidateOK(i, m) ==
    /\ m.mtype = ValidateOKT
    /\ m.mdest = i
    /\ recoveryPhase[i][m.minst] = ValidateOKP
    /\ m.mbal = bal[i][m.minst]
    /\ m.msource \notin validateRcvd[i][m.minst]
    /\ validateRcvd' = [validateRcvd EXCEPT ![i][m.minst] = @ \cup {m.msource}]
    /\ ivar' = [ivar EXCEPT ![i][m.minst] = @ \cup m.miq]
    /\ msgs' = msgs \ {m}
    /\ UNCHANGED <<phase, bal, abal, initCmd, cmd, initDep, dep,
                   preAcceptRcvd, preAcceptAgreed, preAcceptDepUnion,
                   acceptRcvd, recoverReplies, crtInst, recovered,
                   recoveryPhase, qvar, cvar, dvar, cardRmax, recoveryBal>>

\* The reference requires the responder set to be EXACTLY Q, not a
\* quorum-sized subset of it.
ValidateReady(i, d) ==
    /\ recoveryPhase[i][d] = ValidateOKP
    /\ validateRcvd[i][d] = qvar[i][d]

ValidateSettled(i, d) ==
    \/ \E x \in ivar[i][d] : x.phase = Committed
    \/ /\ cardRmax[i][d] + E = Cardinality(qvar[i][d])
       /\ \E x \in ivar[i][d] : x.id.owner \notin qvar[i][d]

\* Branch 1: nothing objected. The carried value is safe.
ValidateAccept(i, d) ==
    /\ ValidateReady(i, d)
    /\ ivar[i][d] = {}
    /\ phase' = [phase EXCEPT ![i][d] = Accepted]
    /\ abal'  = [abal  EXCEPT ![i][d] = bal[i][d]]
    /\ cmd'   = [cmd   EXCEPT ![i][d] = cvar[i][d]]
    /\ dep'   = [dep   EXCEPT ![i][d] = dvar[i][d]]
    /\ msgs' = msgs
         \cup Broadcast(i, [mtype |-> AcceptT, minst |-> d, mbal |-> bal[i][d],
                            mcmd |-> cvar[i][d], mdep |-> dvar[i][d],
                            msource |-> i, mdest |-> i])
         \cup {[mtype |-> AcceptOKT, minst |-> d, mbal |-> bal[i][d],
                msource |-> i, mdest |-> i]}
    /\ recoveryPhase' = [recoveryPhase EXCEPT ![i][d] = StartP]
    /\ acceptRcvd'     = [acceptRcvd     EXCEPT ![i][d] = {}]
    /\ recoverReplies' = [recoverReplies EXCEPT ![i][d] = {}]
    /\ validateRcvd'   = [validateRcvd   EXCEPT ![i][d] = {}]
    /\ UNCHANGED <<bal, initCmd, initDep, preAcceptRcvd, preAcceptAgreed,
                   preAcceptDepUnion, crtInst, recovered, qvar, cvar, dvar,
                   ivar, cardRmax, recoveryBal>>

\* Branch 2: an objection settles it. Take Nop.
ValidateNop(i, d) ==
    /\ ValidateReady(i, d)
    /\ ivar[i][d] # {}
    /\ ValidateSettled(i, d)
    /\ phase' = [phase EXCEPT ![i][d] = Accepted]
    /\ abal'  = [abal  EXCEPT ![i][d] = bal[i][d]]
    /\ cmd'   = [cmd   EXCEPT ![i][d] = Nop]
    /\ dep'   = [dep   EXCEPT ![i][d] = {}]
    /\ msgs' = msgs
         \cup Broadcast(i, [mtype |-> AcceptT, minst |-> d, mbal |-> bal[i][d],
                            mcmd |-> Nop, mdep |-> {}, msource |-> i, mdest |-> i])
         \cup {[mtype |-> AcceptOKT, minst |-> d, mbal |-> bal[i][d],
                msource |-> i, mdest |-> i]}
    /\ recoveryPhase' = [recoveryPhase EXCEPT ![i][d] = StartP]
    /\ acceptRcvd'     = [acceptRcvd     EXCEPT ![i][d] = {}]
    /\ recoverReplies' = [recoverReplies EXCEPT ![i][d] = {}]
    /\ validateRcvd'   = [validateRcvd   EXCEPT ![i][d] = {}]
    /\ UNCHANGED <<bal, initCmd, initDep, preAcceptRcvd, preAcceptAgreed,
                   preAcceptDepUnion, crtInst, recovered, qvar, cvar, dvar,
                   ivar, cardRmax, recoveryBal>>

\* Branch 3: objections exist but none settles anything. Announce and wait.
ValidateWait(i, d) ==
    /\ ValidateReady(i, d)
    /\ ivar[i][d] # {}
    /\ ~ValidateSettled(i, d)
    /\ recoveryPhase' = [recoveryPhase EXCEPT ![i][d] = PostWaitingP]
    /\ msgs' = msgs \cup
         Broadcast(i, [mtype |-> WaitingT, minst |-> d, mk |-> cardRmax[i][d],
                       msource |-> i, mdest |-> i])
    /\ UNCHANGED <<phase, bal, abal, initCmd, cmd, initDep, dep,
                   preAcceptRcvd, preAcceptAgreed, preAcceptDepUnion,
                   acceptRcvd, recoverReplies, validateRcvd, crtInst,
                   recovered, qvar, cvar, dvar, ivar, cardRmax, recoveryBal>>

PostWaitingReady(i, d) ==
    /\ recoveryPhase[i][d] = PostWaitingP
    /\ recoveryBal[i][d] = bal[i][d]

\* Disjunct 1: an objector committed a real command that does not list d.
\* Committing d now would break Visibility.
PostWaitingNop(i, d) ==
    /\ PostWaitingReady(i, d)
    /\ \E x \in ivar[i][d] :
         /\ phase[i][x.id] = Committed
         /\ cmd[i][x.id] # Nop
         /\ d \notin dep[i][x.id]
    /\ phase' = [phase EXCEPT ![i][d] = Accepted]
    /\ abal'  = [abal  EXCEPT ![i][d] = bal[i][d]]
    /\ cmd'   = [cmd   EXCEPT ![i][d] = Nop]
    /\ dep'   = [dep   EXCEPT ![i][d] = {}]
    /\ msgs' = msgs
         \cup Broadcast(i, [mtype |-> AcceptT, minst |-> d, mbal |-> bal[i][d],
                            mcmd |-> Nop, mdep |-> {}, msource |-> i, mdest |-> i])
         \cup {[mtype |-> AcceptOKT, minst |-> d, mbal |-> bal[i][d],
                msource |-> i, mdest |-> i]}
    /\ recoveryPhase' = [recoveryPhase EXCEPT ![i][d] = StartP]
    /\ acceptRcvd'     = [acceptRcvd     EXCEPT ![i][d] = {}]
    /\ recoverReplies' = [recoverReplies EXCEPT ![i][d] = {}]
    /\ validateRcvd'   = [validateRcvd   EXCEPT ![i][d] = {}]
    /\ UNCHANGED <<bal, initCmd, initDep, preAcceptRcvd, preAcceptAgreed,
                   preAcceptDepUnion, crtInst, recovered, qvar, cvar, dvar,
                   ivar, cardRmax, recoveryBal>>

\* Disjunct 2: every objector settled leaving d visible to it.
PostWaitingAccept(i, d) ==
    /\ PostWaitingReady(i, d)
    /\ \A x \in ivar[i][d] :
         /\ phase[i][x.id] = Committed
         /\ (cmd[i][x.id] = Nop \/ d \in dep[i][x.id])
    /\ phase' = [phase EXCEPT ![i][d] = Accepted]
    /\ abal'  = [abal  EXCEPT ![i][d] = bal[i][d]]
    /\ cmd'   = [cmd   EXCEPT ![i][d] = cvar[i][d]]
    /\ dep'   = [dep   EXCEPT ![i][d] = dvar[i][d]]
    /\ msgs' = msgs
         \cup Broadcast(i, [mtype |-> AcceptT, minst |-> d, mbal |-> bal[i][d],
                            mcmd |-> cvar[i][d], mdep |-> dvar[i][d],
                            msource |-> i, mdest |-> i])
         \cup {[mtype |-> AcceptOKT, minst |-> d, mbal |-> bal[i][d],
                msource |-> i, mdest |-> i]}
    /\ recoveryPhase' = [recoveryPhase EXCEPT ![i][d] = StartP]
    /\ acceptRcvd'     = [acceptRcvd     EXCEPT ![i][d] = {}]
    /\ recoverReplies' = [recoverReplies EXCEPT ![i][d] = {}]
    /\ validateRcvd'   = [validateRcvd   EXCEPT ![i][d] = {}]
    /\ UNCHANGED <<bal, initCmd, initDep, preAcceptRcvd, preAcceptAgreed,
                   preAcceptDepUnion, crtInst, recovered, qvar, cvar, dvar,
                   ivar, cardRmax, recoveryBal>>

\* Disjunct 3 -- THE DEADLOCK ESCAPE, and EPaxos*'s fix for the original
\* protocol deadlocking even with finitely many commands. A peer recovering
\* one of our objectors is blocked on us in turn; somebody gives way.
PostWaitingOnWaiting(i, d, m) ==
    /\ PostWaitingReady(i, d)
    /\ m.mtype = WaitingT
    /\ m.mdest = i
    /\ \E x \in ivar[i][d] : x.id = m.minst
    /\ m.mk + F + E > N
    /\ phase' = [phase EXCEPT ![i][d] = Accepted]
    /\ abal'  = [abal  EXCEPT ![i][d] = bal[i][d]]
    /\ cmd'   = [cmd   EXCEPT ![i][d] = Nop]
    /\ dep'   = [dep   EXCEPT ![i][d] = {}]
    /\ msgs' = (msgs \ {m})
         \cup Broadcast(i, [mtype |-> AcceptT, minst |-> d, mbal |-> bal[i][d],
                            mcmd |-> Nop, mdep |-> {}, msource |-> i, mdest |-> i])
         \cup {[mtype |-> AcceptOKT, minst |-> d, mbal |-> bal[i][d],
                msource |-> i, mdest |-> i]}
    /\ recoveryPhase' = [recoveryPhase EXCEPT ![i][d] = StartP]
    /\ acceptRcvd'     = [acceptRcvd     EXCEPT ![i][d] = {}]
    /\ recoverReplies' = [recoverReplies EXCEPT ![i][d] = {}]
    /\ validateRcvd'   = [validateRcvd   EXCEPT ![i][d] = {}]
    /\ UNCHANGED <<bal, initCmd, initDep, preAcceptRcvd, preAcceptAgreed,
                   preAcceptDepUnion, crtInst, recovered, qvar, cvar, dvar,
                   ivar, cardRmax, recoveryBal>>

\* Disjunct 4: a RecoverOK arrived from OUTSIDE the quorum we used, and it
\* knows more than the quorum did. Follow it.
PostWaitingOnRecoverOK(i, d, m) ==
    /\ PostWaitingReady(i, d)
    /\ m.mtype = RecoverOKT
    /\ m.mdest = i
    /\ m.minst = d
    /\ m.msource \notin qvar[i][d]
    /\ \/ m.mphase = Committed
       \/ m.mphase = Accepted
       \/ m.msource = d.owner
    /\ abal' = [abal EXCEPT ![i][d] = bal[i][d]]
    /\ IF m.mphase = Committed
         THEN /\ phase' = [phase EXCEPT ![i][d] = Committed]
              /\ cmd'   = [cmd   EXCEPT ![i][d] = m.mcmd]
              /\ dep'   = [dep   EXCEPT ![i][d] = m.mdep]
              /\ msgs' = (msgs \ {m}) \cup
                   Broadcast(i, [mtype |-> CommitT, minst |-> d, mbal |-> bal[i][d],
                                 mcmd |-> m.mcmd, mdep |-> m.mdep,
                                 msource |-> i, mdest |-> i])
         ELSE /\ phase' = [phase EXCEPT ![i][d] = Accepted]
              /\ cmd'   = [cmd   EXCEPT ![i][d] =
                             IF m.mphase = Accepted THEN m.mcmd ELSE Nop]
              /\ dep'   = [dep   EXCEPT ![i][d] =
                             IF m.mphase = Accepted THEN m.mdep ELSE {}]
              /\ msgs' = (msgs \ {m})
                   \cup Broadcast(i, [mtype |-> AcceptT, minst |-> d,
                                      mbal |-> bal[i][d],
                                      mcmd |-> IF m.mphase = Accepted THEN m.mcmd ELSE Nop,
                                      mdep |-> IF m.mphase = Accepted THEN m.mdep ELSE {},
                                      msource |-> i, mdest |-> i])
                   \cup {[mtype |-> AcceptOKT, minst |-> d, mbal |-> bal[i][d],
                          msource |-> i, mdest |-> i]}
    /\ recoveryPhase' = [recoveryPhase EXCEPT ![i][d] = StartP]
    /\ acceptRcvd'     = [acceptRcvd     EXCEPT ![i][d] = {}]
    /\ recoverReplies' = [recoverReplies EXCEPT ![i][d] = {}]
    /\ validateRcvd'   = [validateRcvd   EXCEPT ![i][d] = {}]
    /\ UNCHANGED <<bal, initCmd, initDep, preAcceptRcvd, preAcceptAgreed,
                   preAcceptDepUnion, crtInst, recovered, qvar, cvar, dvar,
                   ivar, cardRmax, recoveryBal>>

(***************************************************************************)
(* Next -- C5: every action is parameterised by the acting node.            *)
(***************************************************************************)
Next ==
    \E i \in Proc :
        \/ \E c \in Payload : Submit(i, c)
        \/ \E d \in Id :
             \/ CommitFast(i, d)
             \/ StartAccept(i, d)
             \/ CommitSlow(i, d)
             \/ StartRecover(i, d)
             \/ RecoverCommitted(i, d)
             \/ RecoverAccepted(i, d)
             \/ RecoverNop(i, d)
             \/ RecoverValidate(i, d)
             \/ ValidateAccept(i, d)
             \/ ValidateNop(i, d)
             \/ ValidateWait(i, d)
             \/ PostWaitingNop(i, d)
             \/ PostWaitingAccept(i, d)
        \/ \E m \in msgs :
             \/ HandlePreAccept(i, m)
             \/ RecordPreAcceptOK(i, m)
             \/ HandleAccept(i, m)
             \/ RecordAcceptOK(i, m)
             \/ HandleCommit(i, m)
             \/ HandleRecover(i, m)
             \/ RecordRecoverOK(i, m)
             \/ HandleValidate(i, m)
             \/ RecordValidateOK(i, m)
             \/ \E d \in Id :
                  \/ PostWaitingOnWaiting(i, d, m)
                  \/ PostWaitingOnRecoverOK(i, d, m)

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Safety -- the reference's own two properties (.tla:554-571).             *)
(***************************************************************************)
Agreement ==
    \A d \in Id : \A i, j \in Proc :
        (phase[i][d] = Committed /\ phase[j][d] = Committed)
          => (cmd[i][d] = cmd[j][d] /\ dep[i][d] = dep[j][d])

Visibility ==
    \A d1, d2 \in Id : \A i, j \in Proc :
        (   /\ d1 # d2
            /\ cmd[i][d1] # Nop
            /\ cmd[j][d2] # Nop
            /\ phase[i][d1] = Committed
            /\ phase[j][d2] = Committed
            /\ Conflicts(cmd[i][d1], cmd[j][d2]) )
          => (d1 \in dep[j][d2] \/ d2 \in dep[i][d1])

(***************************************************************************)
(* Model-checking bound: every send is a broadcast and only some receives   *)
(* consume, so the message set is what grows.                               *)
(***************************************************************************)
SmallState == Cardinality(msgs) <= 6

=============================================================================
