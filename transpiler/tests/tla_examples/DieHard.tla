-------------------------------- MODULE DieHard --------------------------------
(* The Die Hard water jug puzzle from the movie Die Hard 3.
   Two jugs: a big one (5 gallons) and a small one (3 gallons).
   Goal: Measure exactly 4 gallons using only these jugs. *)

EXTENDS Naturals

VARIABLE big, small

TypeOK == big \in Nat /\ small \in Nat /\ big <= 5 /\ small <= 3

Init == big = 0 /\ small = 0

FillBig == big' = 5 /\ small' = small

FillSmall == big' = big /\ small' = 3

EmptyBig == big' = 0 /\ small' = small

EmptySmall == big' = big /\ small' = 0

SmallToBig ==
    IF big + small <= 5
    THEN big' = big + small /\ small' = 0
    ELSE big' = 5 /\ small' = small - (5 - big)

BigToSmall ==
    IF big + small <= 3
    THEN small' = big + small /\ big' = 0
    ELSE small' = 3 /\ big' = big - (3 - small)

Next == FillBig \/ FillSmall \/ EmptyBig \/ EmptySmall \/ SmallToBig \/ BigToSmall

================================================================================
