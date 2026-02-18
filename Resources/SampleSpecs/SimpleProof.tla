-------------------------------- MODULE SimpleProof --------------------------------
(*
  A simple specification with basic proofs to test TLAPS integration.
  
  This spec defines a simple counter that increments from 0 to a maximum value.
  It includes a theorem with a proof that TLAPS can check.
*)

EXTENDS Naturals, TLAPS

CONSTANT Max  \* Maximum counter value

ASSUME MaxAssumption == Max \in Nat /\ Max > 0

VARIABLE counter

vars == <<counter>>

-----------------------------------------------------------------------------
(* Type invariant *)
TypeOK == counter \in 0..Max

(* Initial state *)
Init == counter = 0

(* Increment action *)
Increment ==
    /\ counter < Max
    /\ counter' = counter + 1

(* Stutter step *)
Stutter == UNCHANGED counter

(* Next state relation *)
Next == Increment \/ Stutter

(* Complete specification *)
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Theorems and Proofs *)

(* Theorem: Type invariant is preserved *)
THEOREM TypeOKInvariant == Spec => []TypeOK
<1>1. Init => TypeOK
    BY MaxAssumption DEF Init, TypeOK
<1>2. TypeOK /\ [Next]_vars => TypeOK'
    <2>1. CASE Increment
        BY <2>1, MaxAssumption DEF Increment, TypeOK
    <2>2. CASE Stutter
        BY <2>2 DEF Stutter, TypeOK
    <2>3. CASE UNCHANGED vars
        BY <2>3 DEF vars, TypeOK
    <2>. QED BY <2>1, <2>2, <2>3 DEF Next
<1>. QED BY <1>1, <1>2, PTL DEF Spec

(* Theorem: Counter never exceeds Max *)
THEOREM BoundedCounter == Spec => [](counter <= Max)
<1>1. TypeOK => counter <= Max
    BY DEF TypeOK
<1>. QED BY <1>1, TypeOKInvariant, PTL

(* A simpler theorem for quick testing *)
THEOREM SimpleTheorem == Init => TypeOK
PROOF BY MaxAssumption DEF Init, TypeOK

=============================================================================
