---- MODULE Epaxos ----
\* Hand-written single-instance EPaxos spec for DPOR case 19.
\* Replaces the prior verus2tla-emitted parameterized Init/Next that TLC
\* could not enumerate (untyped record-tag access on s.phase.tag).
\*
\* Models one EPaxos instance from the perspective of one replica
\* (my_id). Other replicas are abstracted as nondeterministic event
\* sources via existential quantification over Replicas.

EXTENDS Naturals, FiniteSets

VARIABLE ballot, phase, cmd, seq, dep_count, is_leader,
         committed_count, executed_count,
         preaccept_senders, accept_senders,
         has_conflict, max_resp_seq

\* Phase encoded as a small integer to avoid TLC model-value pitfalls.
Empty       == 0
PreAccepted == 1
Accepted    == 2
Committed   == 3
Executed    == 4
Phases      == {Empty, PreAccepted, Accepted, Committed, Executed}

NumReplicas    == 2
QuorumSize     == 2
FastQuorumSize == 2
MyId           == 0
Replicas       == 0..(NumReplicas - 1)

Values   == {1}
MaxBallot == 1

Init ==
    /\ ballot = 0
    /\ phase = Empty
    /\ cmd = 0
    /\ seq = 0
    /\ dep_count = 0
    /\ is_leader = FALSE
    /\ committed_count = 0
    /\ executed_count = 0
    /\ preaccept_senders = {}
    /\ accept_senders = {}
    /\ has_conflict = FALSE
    /\ max_resp_seq = 0

Propose(value) ==
    /\ phase = Empty
    /\ ballot' = ballot
    /\ phase' = PreAccepted
    /\ cmd' = value
    /\ seq' = committed_count + 1
    /\ dep_count' = 0
    /\ is_leader' = TRUE
    /\ committed_count' = committed_count
    /\ executed_count' = executed_count
    /\ preaccept_senders' = {MyId}
    /\ accept_senders' = {}
    /\ has_conflict' = FALSE
    /\ max_resp_seq' = 0

SendPreAcceptOk(local_conflict, local_seq) ==
    /\ UNCHANGED <<ballot, phase, cmd, seq, dep_count, is_leader,
                   committed_count, executed_count,
                   preaccept_senders, accept_senders,
                   has_conflict, max_resp_seq>>

ReceivePreAcceptOk(pa_sender, pa_seq, pa_conflict) ==
    /\ phase = PreAccepted
    /\ is_leader = TRUE
    /\ pa_sender \notin preaccept_senders
    /\ preaccept_senders' = preaccept_senders \cup {pa_sender}
    /\ has_conflict' = IF pa_conflict THEN TRUE ELSE has_conflict
    /\ dep_count'    = IF pa_conflict THEN dep_count + 1 ELSE dep_count
    /\ max_resp_seq' = IF pa_seq > max_resp_seq THEN pa_seq ELSE max_resp_seq
    /\ seq'          = IF pa_seq > seq THEN pa_seq ELSE seq
    /\ ballot' = ballot
    /\ phase' = phase
    /\ cmd' = cmd
    /\ is_leader' = is_leader
    /\ committed_count' = committed_count
    /\ executed_count' = executed_count
    /\ accept_senders' = accept_senders

FastCommit ==
    /\ phase = PreAccepted
    /\ is_leader = TRUE
    /\ Cardinality(preaccept_senders) >= FastQuorumSize
    /\ has_conflict = FALSE
    /\ ballot' = ballot
    /\ phase' = Committed
    /\ cmd' = cmd
    /\ seq' = seq
    /\ dep_count' = dep_count
    /\ is_leader' = is_leader
    /\ committed_count' = committed_count + 1
    /\ executed_count' = executed_count
    /\ preaccept_senders' = preaccept_senders
    /\ accept_senders' = accept_senders
    /\ has_conflict' = has_conflict
    /\ max_resp_seq' = max_resp_seq

StartAccept ==
    /\ phase = PreAccepted
    /\ is_leader = TRUE
    /\ Cardinality(preaccept_senders) >= QuorumSize
    /\ has_conflict = TRUE
    /\ ballot' = ballot
    /\ phase' = Accepted
    /\ cmd' = cmd
    /\ seq' = seq
    /\ dep_count' = dep_count
    /\ is_leader' = is_leader
    /\ committed_count' = committed_count
    /\ executed_count' = executed_count
    /\ preaccept_senders' = preaccept_senders
    /\ accept_senders' = {MyId}
    /\ has_conflict' = has_conflict
    /\ max_resp_seq' = max_resp_seq

SendAcceptOk ==
    /\ UNCHANGED <<ballot, phase, cmd, seq, dep_count, is_leader,
                   committed_count, executed_count,
                   preaccept_senders, accept_senders,
                   has_conflict, max_resp_seq>>

ReceiveAcceptOk(ao_sender) ==
    /\ phase = Accepted
    /\ is_leader = TRUE
    /\ ao_sender \notin accept_senders
    /\ accept_senders' = accept_senders \cup {ao_sender}
    /\ ballot' = ballot
    /\ phase' = phase
    /\ cmd' = cmd
    /\ seq' = seq
    /\ dep_count' = dep_count
    /\ is_leader' = is_leader
    /\ committed_count' = committed_count
    /\ executed_count' = executed_count
    /\ preaccept_senders' = preaccept_senders
    /\ has_conflict' = has_conflict
    /\ max_resp_seq' = max_resp_seq

SlowCommit ==
    /\ phase = Accepted
    /\ is_leader = TRUE
    /\ Cardinality(accept_senders) >= QuorumSize
    /\ ballot' = ballot
    /\ phase' = Committed
    /\ cmd' = cmd
    /\ seq' = seq
    /\ dep_count' = dep_count
    /\ is_leader' = is_leader
    /\ committed_count' = committed_count + 1
    /\ executed_count' = executed_count
    /\ preaccept_senders' = preaccept_senders
    /\ accept_senders' = accept_senders
    /\ has_conflict' = has_conflict
    /\ max_resp_seq' = max_resp_seq

Execute ==
    /\ phase = Committed
    /\ ballot' = ballot
    /\ phase' = Executed
    /\ cmd' = cmd
    /\ seq' = seq
    /\ dep_count' = dep_count
    /\ is_leader' = is_leader
    /\ committed_count' = committed_count
    /\ executed_count' = executed_count + 1
    /\ preaccept_senders' = preaccept_senders
    /\ accept_senders' = accept_senders
    /\ has_conflict' = has_conflict
    /\ max_resp_seq' = max_resp_seq

Recover(new_ballot) ==
    /\ (phase = PreAccepted \/ phase = Accepted)
    /\ new_ballot > ballot
    /\ ballot' = new_ballot
    /\ phase' = PreAccepted
    /\ cmd' = cmd
    /\ seq' = seq
    /\ dep_count' = 0
    /\ is_leader' = TRUE
    /\ committed_count' = committed_count
    /\ executed_count' = executed_count
    /\ preaccept_senders' = {MyId}
    /\ accept_senders' = {}
    /\ has_conflict' = FALSE
    /\ max_resp_seq' = 0

NewInstance ==
    /\ phase = Executed
    /\ ballot' = ballot
    /\ phase' = Empty
    /\ cmd' = 0
    /\ seq' = 0
    /\ dep_count' = 0
    /\ is_leader' = FALSE
    /\ committed_count' = committed_count
    /\ executed_count' = executed_count
    /\ preaccept_senders' = {}
    /\ accept_senders' = {}
    /\ has_conflict' = FALSE
    /\ max_resp_seq' = 0

Next ==
    \/ \E v \in Values : Propose(v)
    \/ \E lc \in BOOLEAN, ls \in 0..MaxBallot : SendPreAcceptOk(lc, ls)
    \/ \E pas \in Replicas, ps \in 0..MaxBallot, pc \in BOOLEAN :
            ReceivePreAcceptOk(pas, ps, pc)
    \/ FastCommit
    \/ StartAccept
    \/ SendAcceptOk
    \/ \E aos \in Replicas : ReceiveAcceptOk(aos)
    \/ SlowCommit
    \/ Execute
    \/ \E nb \in 1..MaxBallot : Recover(nb)
    \/ NewInstance

TypeOK ==
    /\ ballot \in 0..MaxBallot
    /\ phase \in Phases
    /\ cmd \in (Values \cup {0})
    /\ seq \in Nat
    /\ dep_count \in Nat
    /\ is_leader \in BOOLEAN
    /\ committed_count \in Nat
    /\ executed_count \in Nat
    /\ preaccept_senders \subseteq Replicas
    /\ accept_senders \subseteq Replicas
    /\ has_conflict \in BOOLEAN
    /\ max_resp_seq \in Nat

================================================================================
