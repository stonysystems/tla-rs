--------------------------- MODULE EPaxosClean -----------------------------
(***************************************************************************)
(* Egalitarian Paxos, rewritten into the clean subset (C1-C5) of           *)
(* docs/clean_tla_subset.md. See rewrite.md; this header states the slice, *)
(* because a reader has to know what is NOT here before reading what is.   *)
(*                                                                         *)
(* The slice is the **phase-1 commit path**: a replica proposes a command  *)
(* in its own instance, pre-accepts it, collects replies, and commits — on *)
(* the fast path when the replies agree, on the slow path via an explicit  *)
(* Accept round when they do not.                                          *)
(*                                                                         *)
(* Out of the slice: recovery (`SendPrepare` / `ReplyPrepare` /            *)
(* `PrepareFinalize` / `TryPreaccept`), execution, and the `executed` log. *)
(* Recovery is what non-zero ballots exist for, so ballots collapse to the *)
(* leader's own identity and `ballots` — a shared counter — goes with them.*)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANT Replicas, Commands, MaxInstance, MaxSeq

(***************************************************************************)
(* Statuses. The original's "executed" belongs to the execution layer,     *)
(* which is out of the slice.                                              *)
(***************************************************************************)
PreAccepted == "pre-accepted"
Accepted    == "accepted"
Committed   == "committed"

(***************************************************************************)
(* Message tags.                                                           *)
(***************************************************************************)
PreAcceptRequest  == "paq"
PreAcceptResponse == "pap"
AcceptRequest     == "aq"
AcceptResponse    == "ap"
CommitNotice      == "cmt"

VARIABLES
  cmdLog,        \* this replica's records, one per instance it knows about
  crtInst,       \* the next instance number this replica will use
  leading,       \* the instance this replica is currently leading, 0 if none
  preAcceptRcvd, \* replicas that answered the current pre-accept
  acceptRcvd,    \* replicas that answered the current accept
  agreed,        \* whether every pre-accept reply so far matched the leader's
  leaderDeps,    \* the leader's current dependency set for the instance it leads
  leaderSeq,     \* the leader's current sequence number for it
  msgs           \* messages sent

(***************************************************************************)
(* An instance is a pair (owner, number). The original writes it as a      *)
(* tuple `<<cleader, crtInst[cleader]>>`; a record projects to a struct    *)
(* while a tuple would need a product type the projection does not have,   *)
(* and the two carry exactly the same information.                         *)
(***************************************************************************)
Instance == [owner: Replicas, num: 1 .. MaxInstance]

Inst(o, n) == [owner |-> o, num |-> n]

(***************************************************************************)
(* One replica's knowledge of one instance.                                *)
(***************************************************************************)
Record == [inst: Instance, status: {PreAccepted, Accepted, Committed},
           cmd: Commands, deps: SUBSET Instance, seq: 0 .. MaxSeq]

Rec(i, st, c, d, s) ==
  [inst |-> i, status |-> st, cmd |-> c, deps |-> d, seq |-> s]

Message ==
       [mtype: {PreAcceptRequest}, minst: Instance, mcmd: Commands,
        mdeps: SUBSET Instance, mseq: 0 .. MaxSeq,
        msource: Replicas, mdest: Replicas]
  \cup [mtype: {PreAcceptResponse}, minst: Instance,
        mdeps: SUBSET Instance, mseq: 0 .. MaxSeq,
        msource: Replicas, mdest: Replicas]
  \cup [mtype: {AcceptRequest}, minst: Instance, mcmd: Commands,
        mdeps: SUBSET Instance, mseq: 0 .. MaxSeq,
        msource: Replicas, mdest: Replicas]
  \cup [mtype: {AcceptResponse}, minst: Instance,
        msource: Replicas, mdest: Replicas]
  \cup [mtype: {CommitNotice}, minst: Instance, mcmd: Commands,
        mdeps: SUBSET Instance, mseq: 0 .. MaxSeq,
        msource: Replicas, mdest: Replicas]

PreAcceptReq(s, d, i, c, dp, sq) ==
  [mtype |-> PreAcceptRequest, minst |-> i, mcmd |-> c, mdeps |-> dp,
   mseq |-> sq, msource |-> s, mdest |-> d]

PreAcceptResp(s, d, i, dp, sq) ==
  [mtype |-> PreAcceptResponse, minst |-> i, mdeps |-> dp, mseq |-> sq,
   msource |-> s, mdest |-> d]

AcceptReq(s, d, i, c, dp, sq) ==
  [mtype |-> AcceptRequest, minst |-> i, mcmd |-> c, mdeps |-> dp,
   mseq |-> sq, msource |-> s, mdest |-> d]

AcceptResp(s, d, i) ==
  [mtype |-> AcceptResponse, minst |-> i, msource |-> s, mdest |-> d]

Commit(s, d, i, c, dp, sq) ==
  [mtype |-> CommitNotice, minst |-> i, mcmd |-> c, mdeps |-> dp,
   mseq |-> sq, msource |-> s, mdest |-> d]

BroadcastPreAccept(s, i, c, dp, sq) ==
  { PreAcceptReq(s, d, i, c, dp, sq) : d \in Replicas }
BroadcastAccept(s, i, c, dp, sq) ==
  { AcceptReq(s, d, i, c, dp, sq) : d \in Replicas }
BroadcastCommit(s, i, c, dp, sq) ==
  { Commit(s, d, i, c, dp, sq) : d \in Replicas }

(***************************************************************************)
(* P4. The original quantifies over `FastQuorums(cleader)` and             *)
(* `SlowQuorums(cleader)`, both sets of subsets. A replica cannot evaluate *)
(* those; it can count what it has heard.                                  *)
(*                                                                         *)
(* The two quorum sizes are what distinguishes the fast path from the slow *)
(* one, and the difference is real: the fast path needs a larger quorum    *)
(* *and* unanimous agreement on the attributes.                            *)
(***************************************************************************)
IsSlowQuorum(s) == Cardinality(s) * 2 > Cardinality(Replicas)
IsFastQuorum(s) == Cardinality(s) * 4 > Cardinality(Replicas) * 3

(***************************************************************************)
(* The dependency set and sequence number a replica computes for a new     *)
(* command: every instance it already knows about, and one past the        *)
(* highest sequence number it has seen.                                    *)
(***************************************************************************)
Max(s) == CHOOSE x \in s : \A y \in s : x >= y

KnownInstances(log) == {rec.inst : rec \in log}

(***************************************************************************)
(* One past the highest sequence number in the log, exactly as the         *)
(* original's `1 + Max({t.seq : t \in cmdLog[cleader]})`. Bounded by       *)
(* `MaxSeq` for model checking, the way `MaxBallot` bounds Paxos: a spec   *)
(* whose counter is unbounded has no finite state space, and capping the   *)
(* value silently would be a different protocol.                           *)
(***************************************************************************)
NextSeq(log) == 1 + Max({rec.seq : rec \in log} \cup {0})

TypeOK ==
  /\ cmdLog \in [Replicas -> SUBSET Record]
  /\ crtInst \in [Replicas -> 1 .. MaxInstance + 1]
  /\ leading \in [Replicas -> 0 .. MaxInstance]
  /\ preAcceptRcvd \in [Replicas -> SUBSET Replicas]
  /\ acceptRcvd \in [Replicas -> SUBSET Replicas]
  /\ agreed \in [Replicas -> BOOLEAN]
  /\ leaderDeps \in [Replicas -> SUBSET Instance]
  /\ leaderSeq \in [Replicas -> 0 .. MaxSeq]
  /\ msgs \subseteq Message

Init ==
  /\ cmdLog = [r \in Replicas |-> {}]
  /\ crtInst = [r \in Replicas |-> 1]
  /\ leading = [r \in Replicas |-> 0]
  /\ preAcceptRcvd = [r \in Replicas |-> {}]
  /\ acceptRcvd = [r \in Replicas |-> {}]
  /\ agreed = [r \in Replicas |-> TRUE]
  /\ leaderDeps = [r \in Replicas |-> {}]
  /\ leaderSeq = [r \in Replicas |-> 0]
  /\ msgs = {}

(***************************************************************************)
(* A client offers command `c` to replica `i`, which becomes the command   *)
(* leader for a new instance of its own.                                   *)
(*                                                                         *)
(* The original tracks offered commands in a global `proposed` set, purely *)
(* so `Nontriviality` can say "nothing is committed that was not           *)
(* proposed". That set is not per-node and nothing reads it, so it goes;   *)
(* the command arrives as an action parameter, which is what a client      *)
(* request actually is.                                                    *)
(***************************************************************************)
Propose(i, c) ==
  /\ leading[i] = 0
  /\ crtInst[i] <= MaxInstance
  /\ NextSeq(cmdLog[i]) <= MaxSeq
  /\ leading' = [leading EXCEPT ![i] = crtInst[i]]
  /\ crtInst' = [crtInst EXCEPT ![i] = crtInst[i] + 1]
  /\ leaderDeps' = [leaderDeps EXCEPT ![i] = KnownInstances(cmdLog[i])]
  /\ leaderSeq' = [leaderSeq EXCEPT ![i] = NextSeq(cmdLog[i])]
  /\ preAcceptRcvd' = [preAcceptRcvd EXCEPT ![i] = {}]
  /\ acceptRcvd' = [acceptRcvd EXCEPT ![i] = {}]
  /\ agreed' = [agreed EXCEPT ![i] = TRUE]
  /\ cmdLog' = [cmdLog EXCEPT ![i] = cmdLog[i] \cup
       {Rec(Inst(i, crtInst[i]), PreAccepted, c,
            KnownInstances(cmdLog[i]), NextSeq(cmdLog[i]))}]
  /\ msgs' = msgs \cup BroadcastPreAccept(i, Inst(i, crtInst[i]), c,
                                          KnownInstances(cmdLog[i]),
                                          NextSeq(cmdLog[i]))

(***************************************************************************)
(* A replica pre-accepts, unioning the leader's dependencies with its own  *)
(* and taking the larger sequence number — the heart of EPaxos, and the    *)
(* reason the replies may disagree with the leader.                        *)
(***************************************************************************)
HandlePreAcceptReq(i, m) ==
  /\ m.mdest = i
  /\ m.mtype = PreAcceptRequest
  /\ NextSeq(cmdLog[i]) <= MaxSeq
  /\ cmdLog' = [cmdLog EXCEPT ![i] = cmdLog[i] \cup
       {Rec(m.minst, PreAccepted, m.mcmd,
            m.mdeps \cup KnownInstances(cmdLog[i]),
            IF NextSeq(cmdLog[i]) > m.mseq THEN NextSeq(cmdLog[i]) ELSE m.mseq)}]
  /\ msgs' = (msgs \ {m}) \cup
       {PreAcceptResp(i, m.msource, m.minst,
                      m.mdeps \cup KnownInstances(cmdLog[i]),
                      IF NextSeq(cmdLog[i]) > m.mseq
                        THEN NextSeq(cmdLog[i]) ELSE m.mseq)}
  /\ UNCHANGED <<crtInst, leading, preAcceptRcvd, acceptRcvd, agreed,
                 leaderDeps, leaderSeq>>

(***************************************************************************)
(* The leader records a reply and, crucially, whether it *matched*.        *)
(*                                                                         *)
(* The original scans `sentMsg` in `Phase1Fast` for a quorum's worth of    *)
(* replies and asks `\A r1, r2 \in replies : r1.deps = r2.deps /\ ...`.    *)
(* A replica cannot read the network that way, so agreement is accumulated *)
(* here: `agreed` stays TRUE only while every reply has matched what the   *)
(* leader proposed. Once the quorum is in, "all replies agreed" is the     *)
(* same fact.                                                              *)
(***************************************************************************)
HandlePreAcceptResp(i, m) ==
  /\ m.mdest = i
  /\ m.mtype = PreAcceptResponse
  /\ m.minst.owner = i
  /\ m.minst.num = leading[i]
  /\ preAcceptRcvd' = [preAcceptRcvd EXCEPT ![i] = preAcceptRcvd[i] \cup {m.msource}]
  /\ agreed' = [agreed EXCEPT ![i] =
       agreed[i] /\ m.mdeps = leaderDeps[i] /\ m.mseq = leaderSeq[i]]
  /\ msgs' = msgs \ {m}
  /\ UNCHANGED <<cmdLog, crtInst, leading, acceptRcvd, leaderDeps, leaderSeq>>

(***************************************************************************)
(* Fast path: a fast quorum replied and every reply matched, so the        *)
(* command commits without an Accept round. This is what EPaxos is for.    *)
(***************************************************************************)
CommitFast(i) ==
  /\ leading[i] # 0
  /\ IsFastQuorum(preAcceptRcvd[i])
  /\ agreed[i]
  /\ \E rec \in cmdLog[i] :
       /\ rec.inst = Inst(i, leading[i])
       /\ rec.status = PreAccepted
       /\ cmdLog' = [cmdLog EXCEPT ![i] = (cmdLog[i] \ {rec}) \cup
            {Rec(rec.inst, Committed, rec.cmd, leaderDeps[i], leaderSeq[i])}]
       /\ msgs' = msgs \cup BroadcastCommit(i, rec.inst, rec.cmd,
                                            leaderDeps[i], leaderSeq[i])
  /\ leading' = [leading EXCEPT ![i] = 0]
  /\ UNCHANGED <<crtInst, preAcceptRcvd, acceptRcvd, agreed,
                 leaderDeps, leaderSeq>>

(***************************************************************************)
(* Slow path: a slow quorum replied but the replies did not all match, so  *)
(* the leader must run an explicit Accept round on the attributes it now   *)
(* holds.                                                                  *)
(***************************************************************************)
StartAccept(i) ==
  /\ leading[i] # 0
  /\ IsSlowQuorum(preAcceptRcvd[i])
  /\ ~agreed[i]
  /\ \E rec \in cmdLog[i] :
       /\ rec.inst = Inst(i, leading[i])
       /\ rec.status = PreAccepted
       /\ cmdLog' = [cmdLog EXCEPT ![i] = (cmdLog[i] \ {rec}) \cup
            {Rec(rec.inst, Accepted, rec.cmd, leaderDeps[i], leaderSeq[i])}]
       /\ msgs' = msgs \cup BroadcastAccept(i, rec.inst, rec.cmd,
                                            leaderDeps[i], leaderSeq[i])
  /\ acceptRcvd' = [acceptRcvd EXCEPT ![i] = {}]
  /\ UNCHANGED <<crtInst, leading, preAcceptRcvd, agreed,
                 leaderDeps, leaderSeq>>

HandleAcceptReq(i, m) ==
  /\ m.mdest = i
  /\ m.mtype = AcceptRequest
  /\ cmdLog' = [cmdLog EXCEPT ![i] = cmdLog[i] \cup
       {Rec(m.minst, Accepted, m.mcmd, m.mdeps, m.mseq)}]
  /\ msgs' = (msgs \ {m}) \cup {AcceptResp(i, m.msource, m.minst)}
  /\ UNCHANGED <<crtInst, leading, preAcceptRcvd, acceptRcvd, agreed,
                 leaderDeps, leaderSeq>>

HandleAcceptResp(i, m) ==
  /\ m.mdest = i
  /\ m.mtype = AcceptResponse
  /\ m.minst.owner = i
  /\ m.minst.num = leading[i]
  /\ acceptRcvd' = [acceptRcvd EXCEPT ![i] = acceptRcvd[i] \cup {m.msource}]
  /\ msgs' = msgs \ {m}
  /\ UNCHANGED <<cmdLog, crtInst, leading, preAcceptRcvd, agreed,
                 leaderDeps, leaderSeq>>

CommitSlow(i) ==
  /\ leading[i] # 0
  /\ IsSlowQuorum(acceptRcvd[i])
  /\ \E rec \in cmdLog[i] :
       /\ rec.inst = Inst(i, leading[i])
       /\ rec.status = Accepted
       /\ cmdLog' = [cmdLog EXCEPT ![i] = (cmdLog[i] \ {rec}) \cup
            {Rec(rec.inst, Committed, rec.cmd, rec.deps, rec.seq)}]
       /\ msgs' = msgs \cup BroadcastCommit(i, rec.inst, rec.cmd,
                                            rec.deps, rec.seq)
  /\ leading' = [leading EXCEPT ![i] = 0]
  /\ UNCHANGED <<crtInst, preAcceptRcvd, acceptRcvd, agreed,
                 leaderDeps, leaderSeq>>

(***************************************************************************)
(* Any replica told that an instance committed records it.                 *)
(***************************************************************************)
HandleCommit(i, m) ==
  /\ m.mdest = i
  /\ m.mtype = CommitNotice
  /\ cmdLog' = [cmdLog EXCEPT ![i] = cmdLog[i] \cup
       {Rec(m.minst, Committed, m.mcmd, m.mdeps, m.mseq)}]
  /\ msgs' = msgs \ {m}
  /\ UNCHANGED <<crtInst, leading, preAcceptRcvd, acceptRcvd, agreed,
                 leaderDeps, leaderSeq>>

Next ==
  \E i \in Replicas :
      \/ \E c \in Commands : Propose(i, c)
      \/ CommitFast(i)
      \/ StartAccept(i)
      \/ CommitSlow(i)
      \/ \E m \in msgs :
            \/ HandlePreAcceptReq(i, m)
            \/ HandlePreAcceptResp(i, m)
            \/ HandleAcceptReq(i, m)
            \/ HandleAcceptResp(i, m)
            \/ HandleCommit(i, m)

vars == <<cmdLog, crtInst, leading, preAcceptRcvd, acceptRcvd, agreed,
          leaderDeps, leaderSeq, msgs>>

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Safety. The original states this over the global `committed` map, which *)
(* is a history variable and does not survive C1/C3. Restated over the     *)
(* replicas' own logs, it says the same thing: no two replicas commit the  *)
(* same instance with different attributes.                                *)
(***************************************************************************)
Consistency ==
  \A r1, r2 \in Replicas :
      \A a \in cmdLog[r1] :
          \A b \in cmdLog[r2] :
              (a.status = Committed /\ b.status = Committed /\ a.inst = b.inst)
                => (a.cmd = b.cmd /\ a.deps = b.deps /\ a.seq = b.seq)

(***************************************************************************)
(* Model-checking bound: every send is a broadcast and receipt consumes,   *)
(* so the message set is what grows.                                       *)
(***************************************************************************)
SmallState == Cardinality(msgs) <= 4

=============================================================================
