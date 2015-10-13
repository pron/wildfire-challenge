------------------------------- MODULE Peano -------------------------------
(***************************************************************************)
(* This module defines Nat to be a set of natural numbers, Zero to be 0,   *)
(* and Succ to be the successor function [i \in Nat |-> i+1].  The         *)
(* definitions do not use strings or tuples.  Strings and tuples are       *)
(* defined in terms of natural numbers.  This module can therefore serve   *)
(* as the TLA semantic definition of the natural numbers, without          *)
(* introducing any circularity.                                            *)
(***************************************************************************)

PeanoAxioms(N, Z, Sc) == 
  (*************************************************************************)
  (* This formula asserts that the set N with the zero element Z and the   *)
  (* successor function Sc satisfies Peano's axioms.                       *)
  (*************************************************************************)
  /\ Z \in N
  /\ Sc \in [N -> N]
  /\ \A n \in N : (\E m \in N : n = Sc[m]) <=> (n # Z)
  /\ \A S \in SUBSET N : /\ Z \in S 
                           /\ \A n \in S : Sc[n] \in S
                           => S = N

ASSUME \E N, Z, Sc : PeanoAxioms(N, Z, Sc)
  (*************************************************************************)
  (* This assumption asserts the existence of the set of natural numbers.  *)
  (*************************************************************************)

Succ == CHOOSE Sc : \E N, Z : PeanoAxioms(N, Z, Sc)
Nat  == DOMAIN Succ
Zero == CHOOSE Z : PeanoAxioms(Nat, Z, Succ)
=============================================================================
