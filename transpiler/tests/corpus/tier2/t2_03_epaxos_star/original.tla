----------------------------- MODULE EPaxosCommitWithRecovery -----------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC, ExtraConfiguration

(*

A TLA+ specification of the EPaxos* protocol from the following OPODIS'25 paper:
Making Democracy Work: Fixing and Simplifying Egalitarian Paxos.
Fedor Ryabinin, Alexey Gotsman, and Pierre Sutra.
https://doi.org/10.4230/LIPIcs.OPODIS.2025.22 (conference version)
https://arxiv.org/pdf/2511.02743 (extended version)

This file contains the specification of the commit and recovery protocols,
corresponding to Figures 3 and 5 in the paper.

Author: Alexandre SIRET

*)

CONSTANTS
    Proc,           \* set of processes
    F,              \* maximum number of crash failures
    E,              \* e-fast parameter (E <= F)
    Cmd,            \* set of command payloads
    Id,             \* set of command identifiers  
    Nop,            \* a special value representing a Nop command
    Bottom,         \* a special value representing no command payload
    NoProc,         \* a special value representing no process
    NumberOfRecoveryAttempts \* maximum number of recovery attempts per process and command to avoid state-space explosion

N == Cardinality(Proc)
QuorumSize == N - F

Max(a, b) == IF a > b THEN a ELSE b
ASSUME N >= Max(2*E+F-1, 2*F+1)

\* Message types
TypePreAccept == 1
TypePreAcceptOK == 2
TypeAccept == 3
TypeAcceptOK == 4
TypeCommit == 5
TypeRecover == 6
TypeRecoverOK == 7
TypeValidate == 8
TypeValidateOK == 9
TypeWaiting == 10
TypePostWaiting == 11

\* Phase constants
InitialPhase == 1
PreAcceptedPhase == 2
AcceptedPhase == 3
CommittedPhase == 4

\* Recovery phase constants
StartPhase == 1
RecoverOKPhase == 2
ValidateOKPhase == 3
PostWaitingPhase == 4

Message(type, from, to, body) ==
    [type |-> type, from |-> from, to |-> to, body |-> body]

PreAcceptMsg(p, q, id, c, D) ==
    Message(TypePreAccept, p, q, [id |-> id, c |-> c, D |-> D])

PreAcceptOKMsg(p, q, id, Dq) ==
    Message(TypePreAcceptOK, p, q, [id |-> id, Dq |-> Dq])

AcceptMsg(p, q, b, id, c, D) ==
    Message(TypeAccept, p, q, [id |-> id, b  |-> b, c |-> c, D |-> D])

AcceptOKMsg(p, q, b, id) ==
    Message(TypeAcceptOK, p, q, [id |-> id, b |-> b])

CommitMsg(p, q, b, id, c, D) ==
    Message(TypeCommit, p, q, [id |-> id, b  |-> b, c |-> c, D |-> D])

RecoverMsg(p, q, b, id) ==
    Message(TypeRecover, p, q, [ b |-> b, id |-> id])

RecoverOKMsg(p, q, b, id, abalq, cq, depq, initDepq, phaseq) ==
    Message(TypeRecoverOK, p, q, [b |-> b, id |-> id, abalq |-> abalq, cq |-> cq, depq |-> depq, initDepq |-> initDepq, phaseq |-> phaseq])

ValidateMsg(p, q, b, id, c, D) ==
    Message(TypeValidate, p, q, [ b |-> b, id |-> id, c |-> c, D |-> D])

ValidateOKMsg(p, q, b, id, Iq) ==
    Message(TypeValidateOK, p, q, [ b |-> b, id |-> id, Iq |-> Iq])

WaitingMsg(p, q, id, k) ==
    Message(TypeWaiting, p, q, [ id |-> id, k |-> k])

VARIABLES
    msgs,               \* set of network messages
    submitted,          \* set of submitted ids
    initCoord,          \* initCoord[id] = process that submitted id
    phase,              \* phase[p][id] ∈ {InitialPhase,PreAcceptedPhase,AcceptedPhase,CommittedPhase}
    bal,                \* bal[p][id] = current ballot known by process p for command id
    abal,               \* abal[p][id] = the last ballot where p accepted a slow path value
    initCmd,            \* initCmd[p][id] = payload received in PreAccept
    cmd,                \* cmd[p][id] = command payload at p
    initDep,            \* initDep[p][id] = dependencies sent by the initial coordinator
    dep,                \* dep[p][id] = dependency set at p for command id
    recovered,          \* recovered[p][id] = counter of times recovery is invoked
    \* The following variables are used to persist to local state in the RecoverOK handler, which is split into 3 in the TLA spec:
    Qvar,               \* Qvar[p][id] = Q in the RecoverOK handler
    Cvar,               \* Cvar[p][id] = c in the RecoverOK handler
    Dvar,               \* Dvar[p][id] = D in the RecoverOK handler
    CardinalityRmax,    \* CardinalityRmax[p][id] = |R_max| in the RecoverOK handler
    Ivar,               \* Ivar[p][id] = I in the RecoverOK handler
    recoveryAttemptBal, \* recoveryAttemptBal[p][id] = the ballot of the current recovery attempt for p and id
    recoveryPhase       \* recoveryPhase[p][id] ∈ {StartPhase,RecoverOKPhase,ValidateOKPhase,PostWaitingPhase}

vars ==
    <<bal, abal, cmd, initCmd, dep, initDep, phase, msgs, submitted, initCoord, recovered, Qvar, CardinalityRmax, Cvar, Dvar, Ivar, recoveryAttemptBal, recoveryPhase>>

(***************************************************************************)
(* Initialization                                                          *)
(***************************************************************************)

Init ==
    /\  msgs = {}
    /\  submitted = {}
    /\  initCoord = [id \in Id |-> NoProc]
    /\  phase = [p \in Proc |-> [id \in Id |-> InitialPhase]]
    /\  bal = [p \in Proc |-> [id \in Id |-> 0]]
    /\  abal = [p \in Proc |-> [id \in Id |-> 0]]
    /\  initCmd = [p \in Proc |-> [id \in Id |-> Bottom]]
    /\  cmd = [p \in Proc |-> [id \in Id |-> Bottom]]
    /\  initDep = [p \in Proc |-> [id \in Id |-> {}]]
    /\  dep = [p \in Proc |-> [id \in Id |-> {}]]
    /\  recovered = [p \in Proc |-> [id \in Id |-> 0]]
    /\  Qvar = [p \in Proc |-> [id \in Id |-> {}]]
    /\  Cvar = [p \in Proc |-> [id \in Id |-> Bottom]]
    /\  Dvar = [p \in Proc |-> [id \in Id |-> {}]]
    /\  recoveryAttemptBal = [p \in Proc |-> [id \in Id |-> 0]]
    /\  Ivar = [p \in Proc |-> [id \in Id |-> {}]]
    /\  CardinalityRmax = [p \in Proc |-> [id \in Id |-> 0]]
    /\  recoveryPhase = [p \in Proc |-> [id \in Id |-> StartPhase]]

(***************************************************************************)
(* Helpers                                                                 *)
(***************************************************************************)

\* ConflictPairs is a model constant defined in ExtraConfiguration
Conflicts(c1, c2) ==
    IF c1 = Bottom \/ c2 = Bottom THEN FALSE
    ELSE IF c1 = Nop \/ c2 = Nop THEN TRUE
    ELSE <<c1, c2>> \in ConflictPairs \/ <<c2, c1>> \in ConflictPairs

IsQuorumSized(set) == Cardinality(set) >= Cardinality(Proc) - F
IsFastQuorumSized(set) == Cardinality(set) >= Cardinality(Proc) - E

ConflictingIds(p, c) ==
    { id \in Id :
        Conflicts(cmd[p][id], c)
    }

SeenIds(p) ==
    {id \in Id : 
        \/  cmd[p][id] # Bottom
        \/  \E id2 \in Id : id \in dep[p][id2]}

(***************************************************************************)
(* State-changing actions                                                  *)
(***************************************************************************)

(***************************************************************************)
(* When received PreAccept (lines 12–17)                                   *)
(***************************************************************************)
ApplyPreAccept(p, q, id, c, D) ==
    /\  bal[p][id] = 0
    /\  phase[p][id] = InitialPhase
    /\  cmd'     = [cmd     EXCEPT ![p][id] = c]
    /\  initCmd' = [initCmd EXCEPT ![p][id] = c]
    /\  initDep' = [initDep EXCEPT ![p][id] = D]
    /\  LET Dfinal == D \cup ConflictingIds(p, c)
        IN  dep' = [dep EXCEPT ![p][id] = Dfinal]
    /\  phase' = [phase EXCEPT ![p][id] = PreAcceptedPhase]

(***************************************************************************)
(* When received Accept (lines 27–32)                                      *)
(***************************************************************************)
ApplyAccept(p, q, b, id, c, D) ==
    /\  bal[p][id] <= b
    /\  (bal[p][id] = b => phase[p][id] # CommittedPhase)
    /\  bal'   = [bal    EXCEPT ![p][id] = b]
    /\  abal'  = [abal   EXCEPT ![p][id] = b]
    /\  cmd'   = [cmd    EXCEPT ![p][id] = c]
    /\  dep'   = [dep    EXCEPT ![p][id] = D]
    /\  phase' = [phase  EXCEPT ![p][id] = AcceptedPhase]

(***************************************************************************)
(* When received Commit (lines 38–42)                                      *)
(***************************************************************************)
ApplyCommit(p, q, b, id, c, D) ==
    /\  bal[p][id] = b
    /\  abal'    = [abal     EXCEPT ![p][id] = b]
    /\  cmd'     = [cmd      EXCEPT ![p][id] = c]
    /\  dep'     = [dep      EXCEPT ![p][id] = D]
    /\  phase'   = [phase    EXCEPT ![p][id] = CommittedPhase]

(***************************************************************************)
(* When received Recover (lines 47–48)                                     *)
(***************************************************************************)
ApplyRecover(p, q, b, id) ==
    /\  bal[p][id] < b
    /\  bal' = [bal EXCEPT ![p][id] = b]

(***************************************************************************)
(* When received Validate (lines 82–85)                                    *)
(***************************************************************************)
ApplyValidate(p, q, b, id, c, D) == 
    /\  bal[p][id] = b
    /\  cmd'     = [cmd      EXCEPT ![p][id] = c]
    /\  initCmd' = [initCmd  EXCEPT ![p][id] = c]
    /\  initDep' = [initDep  EXCEPT ![p][id] = D]

ComputeI(p, id, c, D) == {<<id2, phase[p][id2]>> : id2 \in 
                                { id3 \in Id :
                                    /\  id3 # id 
                                    /\  id3 \notin D 
                                    /\  (phase[p][id3] = CommittedPhase => (cmd[p][id3] # Nop /\ id \notin dep[p][id3] /\ Conflicts(c, cmd[p][id3]) ))
                                    /\  (phase[p][id3] # CommittedPhase => (initCmd[p][id3] # Bottom /\ id \notin initDep[p][id3] /\ Conflicts(c, initCmd[p][id3])))
                                }
                          }

(***************************************************************************)
(* Message handling actions                                                *)
(* Self-addressed messages are handled immediately, hence the calls to     *)
(* Apply functions below                                                   *)
(***************************************************************************)

(***************************************************************************)
(* Submit (lines 8–10)                                                     *)
(***************************************************************************)
Submit(p, id, c) ==
    /\  id \notin submitted
    /\  submitted' = submitted \cup {id}
    /\  initCoord' = [initCoord EXCEPT ![id] = p]
    /\  LET D0 == ConflictingIds(p, c)
        IN
        /\   ApplyPreAccept(p, p, id, c, D0)
        /\   msgs' = msgs \cup { PreAcceptMsg(p, q, id, c, D0) : q \in Proc \ {p} } 
                        \cup { PreAcceptOKMsg(p, p, id, D0) }
    /\  UNCHANGED <<bal, abal, recovered, Qvar, CardinalityRmax, Cvar, Dvar, Ivar, recoveryAttemptBal, recoveryPhase>> 

(***************************************************************************)
(* HandlePreAccept (lines 11–18)                                           *)
(***************************************************************************)                    
HandlePreAccept(m) ==
    /\  m.type = TypePreAccept
    /\  LET Dfinal == m.body.D \cup ConflictingIds(m.to, m.body.c)
        IN  
        /\  ApplyPreAccept(m.to, m.from, m.body.id, m.body.c, m.body.D)
        /\  msgs' = (msgs \ {m}) \cup { PreAcceptOKMsg(m.to, m.from, m.body.id, Dfinal) }
    /\  UNCHANGED <<abal, submitted, bal, initCoord, recovered, Qvar, CardinalityRmax, Cvar, Dvar, Ivar, recoveryAttemptBal, recoveryPhase>>

(***************************************************************************)
(* HandlePreAcceptOK (lines 19–25)                                         *)
(***************************************************************************)
HandlePreAcceptOK(p, id) ==
    /\  bal[p][id] = 0
    /\  phase[p][id] = PreAcceptedPhase
    /\  LET quorumOfMessages ==
            { m \in msgs :
                /\ m.type = TypePreAcceptOK
                /\ m.body.id = id
                /\ m.to = p
            }
        IN
        /\  IsQuorumSized(quorumOfMessages)
        /\  LET largestFastQuorum ==
                { m \in quorumOfMessages : m.body.Dq = initDep[p][id] }
            IN
            IF  IsFastQuorumSized(largestFastQuorum) THEN
                    /\  ApplyCommit(p, p, 0, id, cmd[p][id], initDep[p][id])
                    /\  msgs' = (msgs \ largestFastQuorum) \cup { CommitMsg(p, q, 0, id, cmd[p][id], initDep[p][id]) : q \in Proc \ {p} }
                    /\  UNCHANGED bal
            ELSE        
                    LET Dfinal == UNION { m.body.Dq : m \in quorumOfMessages }
                    IN
                    /\  ApplyAccept(p, p, 0, id, cmd[p][id], Dfinal)
                    /\  msgs' = (msgs \ quorumOfMessages) \cup { AcceptMsg(p, q, 0, id, cmd[p][id], Dfinal) : q \in Proc \ {p} }
                                                          \cup { AcceptOKMsg(p, p, 0, id) }
    /\  UNCHANGED <<initCmd, initDep, submitted, initCoord, recovered, Qvar, CardinalityRmax, Cvar, Dvar, Ivar, recoveryAttemptBal, recoveryPhase>>

(***************************************************************************)
(* HandleAccept (lines 26–33)                                              *)
(***************************************************************************)                    
HandleAccept(m) ==
    /\  m.type = TypeAccept
    /\  ApplyAccept(m.to, m.from, m.body.b, m.body.id, m.body.c, m.body.D)
    /\  msgs' = (msgs \ {m}) \cup { AcceptOKMsg(m.to, m.from, m.body.b, m.body.id) }
    /\  UNCHANGED <<initCmd, initDep, submitted, initCoord, recovered, Qvar, CardinalityRmax, Cvar, Dvar, Ivar, recoveryAttemptBal, recoveryPhase>>

(***************************************************************************)
(* HandleAcceptOK (lines 34–36)                                            *)
(***************************************************************************)
HandleAcceptOK(p, id) ==
    /\  phase[p][id] = AcceptedPhase
    /\  LET quorumOfMessages == 
            { k \in msgs :
                /\  k.type = TypeAcceptOK
                /\  k.to = p
                /\  k.body.b = bal[p][id]
                /\  k.body.id = id 
            }   
        IN
        /\  IsQuorumSized(quorumOfMessages)
        /\  ApplyCommit(p, p, bal[p][id], id, cmd[p][id], dep[p][id])
        /\  msgs' = (msgs \ quorumOfMessages) \cup { CommitMsg(p, q, bal[p][id], id, cmd[p][id], dep[p][id]) : q \in Proc \ {p} }
    /\  UNCHANGED <<bal, initCmd, initDep, submitted, initCoord, recovered, Qvar, CardinalityRmax, Cvar, Dvar, Ivar, recoveryAttemptBal, recoveryPhase>>

(***************************************************************************)
(* HandleCommit (lines 37–42)                                              *)
(***************************************************************************)
HandleCommit(m) ==
    /\  m.type = TypeCommit
    /\  ApplyCommit(m.to, m.from, m.body.b, m.body.id, m.body.c, m.body.D)
    /\  msgs' = msgs \ {m}
    /\  UNCHANGED <<bal, initCmd, initDep, submitted, initCoord, recovered, Qvar, CardinalityRmax, Cvar, Dvar, Ivar, recoveryAttemptBal, recoveryPhase>>

(***************************************************************************)
(* StartRecover (lines 43–45)                                              *)
(***************************************************************************)
StartRecover(p, id) ==
    \*  We count the number of times a process has tried to recover a command to avoid state-space explosion
    /\  recovered[p][id] < NumberOfRecoveryAttempts
    /\  id \in SeenIds(p)
    /\  recovered' = [recovered EXCEPT ![p][id] = recovered[p][id] + 1]
    \*  Ballots owned by p are of the form k*N + p
    /\  LET  b == IF bal[p][id] = 0 THEN p ELSE bal[p][id] + Cardinality(Proc)
        IN
        /\  ApplyRecover(p, p, b, id)
        /\  msgs' = msgs \cup { RecoverMsg(p, q, b, id) : q \in Proc \ {p} } 
                         \cup { RecoverOKMsg(p, p, b, id, abal[p][id], cmd[p][id], dep[p][id], initDep[p][id], phase[p][id]) }
        /\  recoveryPhase' = [recoveryPhase EXCEPT ![p][id] = RecoverOKPhase]
    /\  UNCHANGED <<abal, cmd, initCmd, dep, initDep, phase, submitted, initCoord, Qvar, CardinalityRmax, Cvar, Dvar, Ivar, recoveryAttemptBal>>

(***************************************************************************)
(* HandleRecover (lines 46–49)                                             *)
(***************************************************************************)
HandleRecover(m) ==
    /\  m.type = TypeRecover
    /\  LET p == m.to
            q == m.from
            id == m.body.id
            b == m.body.b
        IN
        /\  ApplyRecover(p, q, b, id)
        /\  msgs' = (msgs \ {m}) \cup { RecoverOKMsg(p, q, b, id, abal[p][id], cmd[p][id], dep[p][id], initDep[p][id], phase[p][id]) }
    /\  UNCHANGED <<abal, cmd, initCmd, dep, initDep, phase, submitted, initCoord, recovered, Qvar, CardinalityRmax, Cvar, Dvar, Ivar, recoveryAttemptBal, recoveryPhase>>

(***************************************************************************)
(* HandleRecoverOK (lines 50–60)                                           *)
(***************************************************************************)
HandleRecoverOK(p, id) ==
    /\  recoveryPhase[p][id] = RecoverOKPhase
    /\  LET quorumOfMessages ==
            { k \in msgs :
                /\  k.type = TypeRecoverOK
                /\  k.to = p 
                /\  k.body.id = id 
                /\  k.body.b = bal[p][id]  
            }
        IN
        /\  IsQuorumSized(quorumOfMessages) 
        /\  LET Q == { k.from : k \in quorumOfMessages }
                Abals == { k.body.abalq : k \in quorumOfMessages }
                bmax == CHOOSE val \in Abals : \A val2 \in Abals : val >= val2
                U == { k \in quorumOfMessages : k.body.abalq = bmax }
            IN
            /\  IF (\E n \in U : n.body.phaseq = CommittedPhase)
                        THEN
                            /\  LET n == CHOOSE n \in U :
                                            n.body.phaseq = CommittedPhase
                                IN
                                /\  ApplyCommit(p, p, bal[p][id], id, n.body.cq, n.body.depq)                    
                                /\  msgs' = (msgs \ quorumOfMessages) \cup { CommitMsg(p, q2, bal[p][id], id, n.body.cq, n.body.depq) : q2 \in Proc  \ {p} }
                                /\  recoveryPhase' = [recoveryPhase EXCEPT ![p][id] = StartPhase]
                                /\  UNCHANGED <<Qvar, CardinalityRmax, Cvar, Dvar, recoveryAttemptBal, bal, initCmd, initDep>>
                ELSE    IF (\E n \in U : n.body.phaseq = AcceptedPhase)
                        THEN    
                            /\  LET n == CHOOSE n \in U :
                                    n.body.phaseq = AcceptedPhase
                                IN
                                /\  ApplyAccept(p, p, bal[p][id], id, n.body.cq, n.body.depq)  
                                /\  msgs' = (msgs \ quorumOfMessages) \cup { AcceptMsg(p, q2, bal[p][id], id, n.body.cq, n.body.depq) : q2 \in Proc \ {p} } 
                                                                       \cup { AcceptOKMsg(p, p, bal[p][id], id) }
                                /\  recoveryPhase' = [recoveryPhase EXCEPT ![p][id] = StartPhase]
                                /\  UNCHANGED <<Qvar, CardinalityRmax, Cvar, Dvar, recoveryAttemptBal, initCmd, initDep>>
                ELSE    IF (initCoord[id] \in Q)
                        THEN
                            /\  ApplyAccept(p, p, bal[p][id], id, Nop, {})
                            /\  msgs' = (msgs \ quorumOfMessages) \cup { AcceptMsg(p, q, bal[p][id], id, Nop, {}) : q \in Proc \ {p} } 
                                                                  \cup { AcceptOKMsg(p, p, bal[p][id], id) }
                            /\  recoveryPhase' = [recoveryPhase EXCEPT ![p][id] = StartPhase]
                            /\  UNCHANGED <<Qvar, CardinalityRmax, Cvar, Dvar, recoveryAttemptBal, initCmd, initDep>>
                ELSE    IF (LET Rmax == { n \in quorumOfMessages :
                                                /\ n.body.phaseq = PreAcceptedPhase
                                                /\ n.body.depq = n.body.initDepq }
                            IN Cardinality(Rmax) >= Cardinality(quorumOfMessages) - E)
                        THEN
                        LET Rmax == { n \in quorumOfMessages :
                                                /\ n.body.phaseq = PreAcceptedPhase
                                                /\ n.body.depq = n.body.initDepq }
                        IN
                        /\  LET n == CHOOSE n \in Rmax : TRUE
                            IN
                            LET c == n.body.cq
                                D == n.body.depq
                            IN
                            /\  Qvar' = [Qvar EXCEPT ![p][id] = Q]
                            /\  Cvar' = [Cvar EXCEPT ![p][id] = c]
                            /\  Dvar' = [Dvar EXCEPT ![p][id] = D]
                            /\  CardinalityRmax' = [CardinalityRmax EXCEPT ![p][id] = Cardinality(Rmax)]
                            /\  recoveryAttemptBal' = [recoveryAttemptBal EXCEPT ![p][id] = bal[p][id]]
                            /\  recoveryPhase' = [recoveryPhase EXCEPT ![p][id] = ValidateOKPhase]
                            /\  LET I == ComputeI(p, id, c, D)
                                IN
                                /\  ApplyValidate(p, p, bal[p][id], id, c, D)
                                /\  msgs' = (msgs \ quorumOfMessages) \cup { ValidateMsg(p, q, bal[p][id], id, c, D) : q \in Q \ {p} } 
                                                                      \cup { ValidateOKMsg(p, p, bal[p][id], id, I) }
                                /\  UNCHANGED <<bal, abal, dep, phase>>
                ELSE (  /\  ApplyAccept(p, p, bal[p][id], id, Nop, {})  
                        /\  msgs' = (msgs \ quorumOfMessages) \cup { AcceptMsg(p, q, bal[p][id], id, Nop, {}) : q \in Proc \ {p} } 
                                                              \cup { AcceptOKMsg(p, p, bal[p][id], id) }
                        /\  recoveryPhase' = [recoveryPhase EXCEPT ![p][id] = StartPhase]
                        /\  UNCHANGED <<Qvar, CardinalityRmax, Cvar, Dvar, recoveryAttemptBal, initCmd, initDep>> )
    /\  UNCHANGED <<submitted, initCoord, recovered, Ivar>>

(***************************************************************************)
(* HandleValidate (lines 81–87)                                            *)
(***************************************************************************)
HandleValidate(m) ==
    /\  m.type = TypeValidate
    /\  LET p == m.to
            q == m.from
            id == m.body.id
            c == m.body.c
            D == m.body.D
            b == m.body.b
        IN
        LET I == ComputeI(p, id, c, D)
        IN
        /\  ApplyValidate(p, q, b, id, c, D)
        /\  msgs' = (msgs \ {m}) \cup { ValidateOKMsg(p, q, b, id, I) }
    /\  UNCHANGED <<bal, abal, dep, phase, submitted, initCoord, recovered, Qvar, CardinalityRmax, Cvar, Dvar, Ivar, recoveryAttemptBal, recoveryPhase>>

(***************************************************************************)
(* HandleValidateOK (lines 61–68)                                          *)
(***************************************************************************)
HandleValidateOK(p, id) ==
    /\  recoveryPhase[p][id] = ValidateOKPhase
    /\  LET Q == Qvar[p][id]
            c == Cvar[p][id]
            D == Dvar[p][id]
        IN 
        LET quorumOfMessages ==
            { m \in msgs :
                /\ m.type = TypeValidateOK 
                /\ m.to = p 
                /\ m.body.id = id 
                /\ m.body.b = bal[p][id]
            }
            I == UNION { m.body.Iq : m \in quorumOfMessages }
        IN
        /\  { n.from : n \in quorumOfMessages } = Q
        /\  IF (I = {}) THEN
                /\  ApplyAccept(p, p, bal[p][id], id, c, D)    
                /\  msgs' = (msgs \ quorumOfMessages) \cup { AcceptMsg(p, q, bal[p][id], id, c, D) : q \in Proc \ {p} } 
                                                      \cup { AcceptOKMsg(p, p, bal[p][id], id) }
                /\  recoveryPhase' = [recoveryPhase EXCEPT ![p][id] = StartPhase]
                /\  UNCHANGED <<Ivar>>
            ELSE IF 
                ((\E x \in I : x[2] = CommittedPhase) \/ (CardinalityRmax[p][id] = Cardinality(Q) - E /\ \E x \in I : initCoord[x[1]] \notin Q))
                THEN
                /\  ApplyAccept(p, p, bal[p][id], id, Nop, {})     
                /\  msgs' = (msgs \ quorumOfMessages) \cup { AcceptMsg(p, q, bal[p][id], id, Nop, {}) : q \in Proc  \ {p} } 
                                                      \cup { AcceptOKMsg(p, p, bal[p][id], id) }
                /\  recoveryPhase' = [recoveryPhase EXCEPT ![p][id] = StartPhase]
                /\  UNCHANGED <<Ivar>>
            ELSE
                /\  Ivar' = [Ivar EXCEPT ![p][id] = I]
                /\  recoveryPhase' = [recoveryPhase EXCEPT ![p][id] = PostWaitingPhase]
                /\  msgs' = (msgs \ quorumOfMessages) \cup { WaitingMsg(p, q, id, CardinalityRmax[p][id]) : q \in Proc \ {p} }
                /\  UNCHANGED <<bal, abal, cmd, phase, dep>>
    /\  UNCHANGED <<initCmd, initDep, submitted, initCoord, recovered, Qvar, CardinalityRmax, Cvar, Dvar, recoveryAttemptBal>>

(***************************************************************************)
(* HandlePostWaiting (lines 69–80)                                         *)
(***************************************************************************)
HandlePostWaiting(p, id) ==
    /\  recoveryPhase[p][id] = PostWaitingPhase
    /\  recoveryAttemptBal[p][id] = bal[p][id]
    /\  LET 
           I == Ivar[p][id]
           Q == Qvar[p][id]
           b == bal[p][id]
           c == Cvar[p][id]
           D == Dvar[p][id] 
        IN      \/  (\E x \in I :
                    /\  phase[p][x[1]] = CommittedPhase /\ cmd[p][x[1]] # Nop /\ id \notin dep[p][x[1]]
                    /\  ApplyAccept(p, p, bal[p][id], id, Nop, {})
                    /\  msgs' = msgs \cup { AcceptMsg(p, q, bal[p][id], id, Nop, {}) : q \in Proc \ {p} } 
                                     \cup { AcceptOKMsg(p, p, bal[p][id], id) }
                    /\  recoveryPhase' = [recoveryPhase EXCEPT ![p][id] = StartPhase])    
                \/ (\A x \in I :
                    /\  phase[p][x[1]] = CommittedPhase /\ (cmd[p][x[1]] = Nop \/ id \in dep[p][x[1]])
                    /\  ApplyAccept(p, p, bal[p][id], id, c, D)
                    /\  msgs' =  msgs \cup { AcceptMsg(p, q, bal[p][id], id, c, D) : q  \in Proc \ {p} } 
                                      \cup { AcceptOKMsg(p, p, bal[p][id], id) }
                    /\  recoveryPhase' = [recoveryPhase EXCEPT ![p][id] = StartPhase])
                \/ (\E x \in I :
                        \E m2 \in msgs :
                            m2.type = TypeWaiting /\
                            m2.to = p /\
                            m2.body.id = x[1] /\
                            m2.body.k > N - F - E
                    /\  ApplyAccept(p, p, bal[p][id], id, Nop, {})
                    /\  msgs' =  msgs \cup { AcceptMsg(p, q, bal[p][id], id, Nop, {}) : q \in Proc \ {p} } 
                                      \cup { AcceptOKMsg(p, p, bal[p][id], id) }
                    /\  recoveryPhase' = [recoveryPhase EXCEPT ![p][id] = StartPhase])
                \/ (\E m2 \in msgs :
                        /\  m2.type = TypeRecoverOK 
                        /\  m2.to = p 
                        /\  m2.body.id = id 
                        /\  m2.from \notin Q 
                        /\  (m2.body.phaseq = CommittedPhase \/ m2.body.phaseq = AcceptedPhase \/ m2.from = initCoord[id])
                        /\  IF m2.body.phaseq = CommittedPhase THEN
                                /\  ApplyCommit(p, p, bal[p][id], id, m2.body.cq, m2.body.depq)
                                /\  msgs' = msgs \cup { CommitMsg(p, q, bal[p][id], id, m2.body.cq, m2.body.depq) : q \in Proc \ {p} }
                                /\  recoveryPhase' = [recoveryPhase EXCEPT ![p][id] = StartPhase]
                                /\  UNCHANGED bal
                            ELSE IF m2.body.phaseq = AcceptedPhase THEN
                                /\  ApplyAccept(p, p, bal[p][id], id, m2.body.cq, m2.body.depq)
                                /\  msgs' = msgs \cup { AcceptMsg(p, q, bal[p][id], id, m2.body.cq, m2.body.depq) : q \in Proc \ {p} } 
                                                 \cup { AcceptOKMsg(p, p, bal[p][id], id) }
                                /\  recoveryPhase' = [recoveryPhase EXCEPT ![p][id] = StartPhase]
                            ELSE
                                /\  ApplyAccept(p, p, bal[p][id], id, Nop, {})
                                /\  msgs' = msgs \cup { AcceptMsg(p, q, bal[p][id], id, Nop, {}) : q \in Proc \ {p} } 
                                                 \cup { AcceptOKMsg(p, p, bal[p][id], id) }
                                /\  recoveryPhase' = [recoveryPhase EXCEPT ![p][id] = StartPhase]
                                )
    /\  UNCHANGED <<initCmd, initDep, submitted, initCoord, recovered, Qvar, CardinalityRmax, Cvar, Dvar, Ivar, recoveryAttemptBal>>

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)                 

Agreement ==
  \A id \in Id :
    \A p, q \in Proc :
      /\  phase[p][id] = CommittedPhase
      /\  phase[q][id] = CommittedPhase
      => /\  dep[p][id] = dep[q][id]
         /\  cmd[p][id] = cmd[q][id]

Visibility ==
  \A id, id2 \in Id : \A p, q \in Proc :
    /\  id # id2
    /\  cmd[p][id] # Nop
    /\  cmd[q][id2] # Nop 
    /\  phase[p][id] = CommittedPhase
    /\  phase[q][id2] = CommittedPhase
    /\  Conflicts(cmd[p][id], cmd[q][id2])
    => \/  id \in dep[q][id2]
       \/  id2 \in dep[p][id]

TypeInv ==
    /\  \A p \in Proc, id \in Id :
        /\  bal[p][id] >= 0 
        /\  abal[p][id] >= 0
        /\  (cmd[p][id] \in Cmd \/ cmd[p][id] = Nop \/ cmd[p][id] = Bottom)
        /\  (initCmd[p][id] \in Cmd \/ initCmd[p][id] = Nop \/ initCmd[p][id] = Bottom)
        /\  dep[p][id] \subseteq Id
        /\  initDep[p][id] \subseteq Id
        /\  phase[p][id] \in {InitialPhase, PreAcceptedPhase, AcceptedPhase, CommittedPhase}
        /\  recovered[p][id] >= 0 /\ recovered[p][id] <= NumberOfRecoveryAttempts
        /\  Ivar[p][id] \subseteq { <<id2, phase2>> : id2 \in Id, phase2 \in {InitialPhase, PreAcceptedPhase, AcceptedPhase, CommittedPhase} }
        /\  Qvar[p][id] \subseteq Proc
        /\  CardinalityRmax[p][id] >= 0 /\ CardinalityRmax[p][id] <= Cardinality(Proc)
    /\  \A m \in msgs :
            m.type \in {TypePreAccept, TypePreAcceptOK, TypeAccept, TypeAcceptOK, TypeCommit,
                        TypeRecover, TypeRecoverOK, TypeValidate, TypeValidateOK,
                        TypeWaiting, TypePostWaiting} 
    /\  \A id \in Id :
        /\  initCoord[id] \in Proc \cup {NoProc}
    /\  submitted \subseteq Id

(***************************************************************************)
(* Next state relation                                                     *)
(***************************************************************************)

Next == \/ \E m \in msgs :
            \/  HandlePreAccept(m) 
            \/  HandleAccept(m)
            \/  HandleCommit(m) 
            \/  HandleRecover(m) 
            \/  HandleValidate(m) 
        \/ \E p \in Proc, id \in Id :
            \/  Submit(p, id, id) \* Use id as the payload for model checking
            \/  StartRecover(p, id)
            \/  HandlePreAcceptOK(p, id) 
            \/  HandleValidateOK(p, id) 
            \/  HandlePostWaiting(p, id) 
            \/  HandleRecoverOK(p, id) 
            \/  HandleAcceptOK(p, id)

Spec ==
    Init /\ [][Next]_<<vars>>

=============================================================================
