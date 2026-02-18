-------------------------------- MODULE DieHard --------------------------------
(* 
  The Die Hard problem from the movie Die Hard 3.
  You have a 3 gallon jug and a 5 gallon jug, and need to measure exactly 4 gallons.
  
  This is a good test spec because:
  - Small state space (~30 states)
  - Has a reachable goal state
  - Tests basic TLC functionality
*)

EXTENDS Naturals

VARIABLES 
    small,   \* 3 gallon jug
    big      \* 5 gallon jug

vars == <<small, big>>

(* Type invariant - jugs can't be overfilled *)
TypeOK ==
    /\ small \in 0..3
    /\ big \in 0..5

(* Initial state - both jugs empty *)
Init ==
    /\ small = 0
    /\ big = 0

(* Fill the small jug completely *)
FillSmall ==
    /\ small' = 3
    /\ big' = big

(* Fill the big jug completely *)
FillBig ==
    /\ big' = 5
    /\ small' = small

(* Empty the small jug *)
EmptySmall ==
    /\ small' = 0
    /\ big' = big

(* Empty the big jug *)
EmptyBig ==
    /\ big' = 0
    /\ small' = small

(* Pour small jug into big jug *)
SmallToBig ==
    LET amount == IF small + big <= 5 
                  THEN small 
                  ELSE 5 - big
    IN /\ small' = small - amount
       /\ big' = big + amount

(* Pour big jug into small jug *)
BigToSmall ==
    LET amount == IF small + big <= 3 
                  THEN big 
                  ELSE 3 - small
    IN /\ big' = big - amount
       /\ small' = small + amount

(* All possible actions *)
Next ==
    \/ FillSmall
    \/ FillBig
    \/ EmptySmall
    \/ EmptyBig
    \/ SmallToBig
    \/ BigToSmall

(* The complete specification *)
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Properties to check *)

(* Safety: TypeOK should always hold *)
TypeInvariant == TypeOK

(* 
  NotSolved: The goal is to get exactly 4 gallons in the big jug.
  If we use this as an invariant, TLC should find a counterexample
  showing how to reach the goal state.
*)
NotSolved == big /= 4

=============================================================================
