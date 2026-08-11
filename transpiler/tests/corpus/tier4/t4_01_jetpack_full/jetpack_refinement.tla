---------------------- MODULE jetpack_refinement ----------------------------
(***************************************************************************)
(* The rewrite checked against the ORIGINAL's own safety properties.       *)
(*                                                                         *)
(* Everything in `tier4/t4_01_jetpack_full` so far checks the rewrite      *)
(* against invariants *I* wrote. That is worth something, and it is not    *)
(* the question anyone actually has, which is whether the rewrite still    *)
(* satisfies what the original claims.                                     *)
(*                                                                         *)
(* So: INSTANCE the unmodified upstream composition under an explicit      *)
(* mapping from the rewrite's state, and check ITS invariant definitions   *)
(* -- `O!NoLogDivergence`, not a retyped copy of it. Retyping is the       *)
(* failure mode this construction exists to avoid: a transcription slip in *)
(* a hand-copied invariant makes the check pass and says nothing. The      *)
(* three files under `orig_` differ from upstream only in their MODULE     *)
(* line and their INSTANCE targets, so that they can sit in one directory  *)
(* beside the rewrite.                                                     *)
(*                                                                         *)
(* WHAT THIS IS NOT: trace refinement. It does not establish that every    *)
(* behaviour of the rewrite is a behaviour of the original. It establishes *)
(* that every reachable state of the rewrite, mapped, satisfies the        *)
(* original's stated safety invariants. Full refinement additionally needs *)
(* step correspondence, and the bag/set difference in the network plus the *)
(* rewrite's handler decomposition mean that is not a mapping away.        *)
(***************************************************************************)
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS Server, Client, Commands, CmdId, Key,
          MaxTerm, MaxLogLen, MaxElections, MaxRestarts, MaxEpoch

VARIABLES
  currentTerm, ostate, votedFor, log, commitIndex, votesGranted,
  nextIndex, matchIndex, config, pendingReconfig, electionCtr, restartCtr,
  jstate, jepoch, oepoch, viewEpoch, viewMembers, viewProposers,
  maxSeenBallot, acceptedBallot, acceptedValue, cmdPool, recoverySet,
  prepRcvd, acceptRcvd, chosenValue, highestSeenBallot, highestSeenValue,
  clientPending, clientSuccesses, clientHeardFrom, clientEpoch,
  clientMembers, clientProposers,
  msgs

(* The rewrite itself, unchanged. *)
R == INSTANCE jetpack_raft_clean

(***************************************************************************)
(* THE MAPPING                                                             *)
(*                                                                         *)
(* Only two things differ in the state the checked invariants read:        *)
(*                                                                         *)
(*  - the original indexes logs by proposer, `log[i]["sole"]`, because it  *)
(*    is written for a multi-proposer protocol and then instantiated with  *)
(*    a single one. The rewrite drops the index, which is exact rather     *)
(*    than a specialisation because the original hardcodes "sole" at every *)
(*    use. Re-adding it is the mapping.                                    *)
(*  - the original's variables range over `Server`; the rewrite's range    *)
(*    over `Node == Server \cup Client`. Restrict.                         *)
(***************************************************************************)
MapLog         == [i \in Server |-> [p \in {"sole"} |-> log[i]]]
MapCommitIndex == [i \in Server |-> [p \in {"sole"} |-> commitIndex[i]]]

(***************************************************************************)
(* State the rewrite does not carry, and which the checked invariants      *)
(* never read. `execution_cmds` and `original_execution_cmds` are the      *)
(* history variables the rewrite deletes; the two invariants that read     *)
(* them are therefore NOT checkable here and are named in the write-up     *)
(* rather than quietly dropped.                                            *)
(***************************************************************************)
Nothing == [x \in {} |-> 0]

O == INSTANCE orig_composition WITH
       Server                   <- Server,
       Client                   <- Client,
       CmdId                    <- CmdId,
       Key                      <- Key,
       InitialMembers           <- Server,
       MinClusterSize           <- 1,
       MaxClusterSize           <- Cardinality(Server),
       MaxElections             <- MaxElections,
       MaxRestarts              <- MaxRestarts,
       MaxAddReconfigs          <- 0,
       MaxRemoveReconfigs       <- 0,
       IncludeThesisBug         <- FALSE,
       messages                 <- Nothing,
       currentTerm              <- [i \in Server |-> currentTerm[i]],
       ostate                   <- [i \in Server |-> ostate[i]],
       log                      <- MapLog,
       commitIndex              <- MapCommitIndex,
       votedFor                 <- [i \in Server |-> votedFor[i]],
       votesGranted             <- [i \in Server |-> votesGranted[i]],
       nextIndex                <- [i \in Server |-> nextIndex[i]],
       matchIndex               <- [i \in Server |-> matchIndex[i]],
       config                   <- [i \in Server |-> config[i]],
       pending_reconfig         <- [i \in Server |-> pendingReconfig[i]],
       electionCtr              <- 0,
       restartCtr               <- 0,
       addReconfigCtr           <- 0,
       removeReconfigCtr        <- 0,
       jstate                   <- [i \in Server |-> jstate[i]],
       jepoch                   <- [i \in Server |-> jepoch[i]],
       oepoch                   <- [i \in Server |-> oepoch[i]],
       old_view                 <- Nothing,
       new_view                 <- Nothing,
       jpool                    <- Nothing,
       recovery_set             <- [i \in Server |-> recoverySet[i]],
       chosen_value             <- [i \in Server |-> chosenValue[i]],
       br_responses             <- Nothing,
       prep_responses           <- Nothing,
       accept_responses         <- Nothing,
       client_view              <- Nothing,
       client_pending           <- Nothing,
       client_successes         <- Nothing,
       client_heard_from        <- Nothing,
       original_execution_cmds  <- << >>,
       execution_cmds           <- << >>

(***************************************************************************)
(* The three of the original's five safety invariants that are about state *)
(* the rewrite still has. These are its definitions, reached through the   *)
(* INSTANCE -- nothing here restates them.                                 *)
(***************************************************************************)
OrigCommittedLogAgreement        == O!CommittedLogAgreement
OrigNoLogDivergence              == O!NoLogDivergence
OrigMaxOneReconfigurationAtATime == O!MaxOneReconfigurationAtATime

SmallState == R!SmallState
Spec       == R!Spec

=============================================================================
