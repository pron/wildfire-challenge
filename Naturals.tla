------------------------------ MODULE Naturals ------------------------------ 
(***************************************************************************)
(* The set Nat of natural numbers and almost all of its operators are      *)
(* already defined in module ProtoReals.  We just have to import them      *)
(* locally with renaming (so this module doesn't export everything defined *)
(* in ProtoReals) and then define the operators we want to equal the       *)
(* corresponding renamed, imported ones.                                   *)
(***************************************************************************)

LOCAL R == INSTANCE ProtoReals

Nat == R!Nat

a + b == a R!+ b
a - b == a R!- b
a * b == a R!* b
a ^ b == a R!^ b
a \leq b == a R!\leq b
a \geq b == b \leq a
a < b == (a \leq b) /\ (a # b)
a > b == b < a
a .. b == 
  (*************************************************************************)
  (* This defines a..b to be the set {a, a+1, ..., b} of integers.  It is  *)
  (* left undefined if a and b are not integers.                           *)
  (*************************************************************************)
  CASE (a \in R!Int) /\ (b \in R!Int) -> 
           {i \in Nat : (a \leq i) /\ (i \leq b)}

(***************************************************************************)
(* We define % and \div so that                                            *)
(*                                                                         *)
(*   (1) a = b * (a \div b) + (a % b)                                      *)
(*   (2) a % b \in 0 .. b-1                                                *)
(*                                                                         *)
(* if a and b ar integers and b > 0.                                       *)
(***************************************************************************)
a \div b == CHOOSE n \in R!Int : \E r \in 0 .. (b-1) : a =  b * n + r
a % b    ==  a  -  b * (a \div b)
=============================================================================
