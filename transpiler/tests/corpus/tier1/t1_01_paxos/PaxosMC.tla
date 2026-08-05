---------------------------- MODULE PaxosMC --------------------------------
(***************************************************************************)
(* Model-checking wrapper for `Paxos.tla` (= this case's `original.tla`).   *)
(* It exists only so `tlc_fidelity.sh` can run the original *unmodified*.   *)
(*                                                                         *)
(* Two of the original's definitions are not enumerable:                    *)
(*                                                                         *)
(*   Ballot == Nat                                                          *)
(*   None   == CHOOSE v : v \notin Value                                    *)
(*                                                                         *)
(* TLC overrides a definition only with another definition, so the cfg says *)
(* `Ballot <- MCBallot` and `None <- MCNone`, and they live here.           *)
(*                                                                         *)
(* `MCNone == -1` is chosen to match `clean.tla`'s `None == -1`. That is    *)
(* not a thumb on the scale: the original already uses `-1` for "no ballot" *)
(* in `maxBal` and `maxVBal`, and `None` is only required to lie outside    *)
(* `Value`, which `-1` does for the model values used here. A different     *)
(* sentinel would make the two specs' `maxVal` incomparable for a reason    *)
(* about notation rather than about behaviour.                              *)
(*                                                                         *)
(* `MCBallot` must agree with `clean.cfg`'s `MaxBallot = 1`, or the         *)
(* comparison would be between two different models rather than two specs.  *)
(***************************************************************************)
EXTENDS Paxos

MCBallot == 0 .. 1
MCNone == -1

=============================================================================
