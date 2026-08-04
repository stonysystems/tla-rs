---- MODULE TLAPS ----
(***************************************************************************)
(* Minimal stub. `Voting.tla` and `Consensus.tla` are proof modules that    *)
(* EXTEND the real TLAPS library; TLC never checks proofs, so all it needs  *)
(* from that library is for the names cited in `BY` clauses to resolve.     *)
(*                                                                         *)
(* Nothing here can affect the comparison. `Paxos.tla` mentions `V!` only   *)
(* in its `THEOREM` and in `Inv`, neither of which `Spec` reaches, and      *)
(* `tlc_fidelity.sh` checks no invariant -- it only dumps states.           *)
(***************************************************************************)
PTL == TRUE
SMT == TRUE
Zenon == TRUE
Isa == TRUE
Blast == TRUE
Auto == TRUE
AutoUSE == TRUE
LS4 == TRUE
ExpandENABLED == TRUE
ExpandENABLEDWF == TRUE
ExpandENABLEDSF == TRUE
=============================================================================
