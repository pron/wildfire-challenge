----------------------------- MODULE ProtoReals ----------------------------- 
(***************************************************************************)
(* The Naturals module must define the operator + to be addition of        *)
(* natural numbers.  The Reals module must define the operator + to be     *)
(* addition of real numbers.  A priori, we would have no reason to expect  *)
(* these operators to be the same.  All we would expect is that they both  *)
(* give the same definition of m + n if m and n are naturals.  This could  *)
(* cause a problem if a module EXTENDS both the Naturals and the Reals     *)
(* module.  Of course, there's no reason to write                          *)
(*                                                                         *)
(*   EXTENDS Naturals, Reals                                               *)
(*                                                                         *)
(* However, one could certainly write                                      *)
(*                                                                         *)
(*   EXTENDS Reals, Sequences                                              *)
(*                                                                         *)
(* which would cause the same problem since the Sequences module EXTENDS   *)
(* Naturals.                                                               *)
(*                                                                         *)
(* The solution to this problem is to make the operator + be the same      *)
(* operator in both the Naturals and Reals module--which means that it     *)
(* must represent addition of real numbers.  This causes no problem in     *)
(* using the Naturals module because, when working with natural numbers,   *)
(* we don't care what 2 + 1.5 equals, or what 3/2 equals.                  *)
(*                                                                         *)
(* This module defines most of the operators needed by the Naturals,       *)
(* Integers, and Reals modules.  In particular, it defines the following   *)
(* sets of numbers                                                         *)
(*                                                                         *)
(*    Nat  Int  Real                                                       *)
(*                                                                         *)
(* where Nat \subseteq Int \subseteq Real, and the following operators     *)
(* on the set Real of real numbers                                         *)
(*                                                                         *)
(*    +  *  -  /  ^  \leq                                                  *)
(*                                                                         *)
(* that will be used in the Naturals, Integers, and Reals modules.  It     *)
(* also defines the function NumValue from strings of digits to the        *)
(* natural numbers they represent---for example, NumValue["411"] equals    *)
(* the number 411.                                                         *)
(***************************************************************************)

EXTENDS Peano

IsModelOfReals(R, Plus, Times, Leq) == 
  LET IsAbelianGroup(G, Id, _+_) == 
        (*******************************************************************)
        (* This asserts that G is an Abelian group with identity Id and    *)
        (* operator +.                                                     *)
        (*******************************************************************)
        /\ Id \in G
        /\ \A a, b \in G : a + b \in G
        /\ \A a \in G : Id + a = Id
        /\ \A a, b, c \in G : (a + b) + c = a + (b + c)
        /\ \A a \in G : \E nega \in G : a + nega = Id
        /\ \A a, b \in G : a + b = b + a
     (**********************************************************************)
     (* Plus and Times are functions and Leq is a set, but it's more       *)
     (* convenient to turn them into the infix operators +, *, and \leq    *)
     (**********************************************************************)
      a + b    == Plus[a, b]
      a * b    == Times[a, b]
      a \leq b == <<a, b>> \in Leq
      RPos     == {r \in R \ {Zero} : Zero \leq r}
        (*******************************************************************)
        (* RPos is the set of positive reals.                              *)
        (*******************************************************************)
      Dist(a, b) == CHOOSE r \in RPos \cup {Zero} : \/ a = b + r
                                                    \/ b = a + r
        (*******************************************************************)
        (* Dist(a, b) equals |a - b|.                                      *)
        (*******************************************************************)
  IN  (*********************************************************************)
      (* Nat is a subset of R and Succ is the +1 function.                 *)
      (*********************************************************************)
      /\ Nat \subseteq R
      /\ \A n \in Nat : Succ[n] = n + Succ[Zero]
      (*********************************************************************)
      (* R is a field                                                      *)
      (*********************************************************************)
      /\ IsAbelianGroup(R, Zero, +)
      /\ IsAbelianGroup(R \ {Zero}, Succ[Zero], *)
      /\ \A a, b, c \in R : a * (b + c) = (a * b) + (a * c) 
      (*********************************************************************)
      (* R is an ordered field.                                            *)
      (*********************************************************************)
      /\ \A a, b \in R : /\ (a \leq b) \/ (b \leq a)
                         /\ (a \leq b) /\ (b \leq a) <=> (a = b)
      /\ \A a, b, c \in R : /\ (a \leq b) /\ (b \leq c) => (a \leq c)
                            /\ (a \leq b) => 
                                 /\ (a + c) \leq (b + c)
                                 /\ (Zero \leq c) => (a * c) \leq (b * c)
      (*********************************************************************)
      (* Every subset of R bounded from above has a least upper bound.     *)
      (*********************************************************************)
      /\ \A S \in SUBSET R :
           LET SBound(a) == \A s \in S : s \leq a
           IN  (\E a \in R : SBound(a)) => 
                  (\E sup \in R : /\ SBound(sup) 
                                  /\ \A a \in R : SBound(a) => (sup\leq a))

THEOREM \E R, Plus, Times, Leq : IsModelOfReals(R, Plus, Times, Leq)
  (*************************************************************************)
  (* The standard mathematical development of the reals involves           *)
  (* constructing a model of the reals.                                    *)
  (*************************************************************************)

-----------------------------------------------------------------------------

(***************************************************************************)
(* We now define RM to be an arbitrary value having components that        *)
(* form a model of the reals, and we use it to define Real, +, *, /, and   *)
(* \leq.  We also define (binary) -, Int, and the set RPos of positive     *)
(* reals.                                                                  *)
(***************************************************************************)
RM == CHOOSE RM : IsModelOfReals(RM.R, RM.Plus, RM.Times, RM.Leq)

Real  == RM.R

-----------------------------------------------------------------------------

(***************************************************************************)
(* It is sometimes useful in specifications to have values plus and minus  *)
(* infinity that are greater and smaller than any real number.  We         *)
(* therefore define Infinity so that -Infinity < r < Infinity for all real *)
(* numbers r.  We don't bother to define things like 3 + Infinity.         *)
(* However, to define -Infinity to have the right meaning, we do wind up   *)
(* defining r - Infinity for all real numbers r.                           *)
(***************************************************************************)
Infinity == CHOOSE x : x \notin Real
LOCAL MinusInfinity == CHOOSE x : x \notin Real \cup {Infinity}

a + b == RM.Plus[a, b]

a \leq b == CASE a \in Real /\ b \in Real -> <<a, b>> \in RM.Leq
              [] a = Infinity /\ b \in Real \cup {MinusInfinity} -> FALSE
              [] a \in Real  \cup {MinusInfinity} /\ b = Infinity -> TRUE
              [] a = b -> TRUE

a - b == CASE a \in Real /\ b \in Real -> CHOOSE c \in Real : c + b = a
           [] a \in Real /\ b = Infinity -> MinusInfinity
           [] a \in Real /\ b = MinusInfinity -> Infinity 

a * b == RM.Times[a, b]

a / b == CHOOSE c \in Real : a = b * c
  (*************************************************************************)
  (* This defintion tells us that 1/0 equals CHOOSE c : FALSE, and doesn't *)
  (* tell us much of anything about "abc"/17.                              *)
  (*************************************************************************)

Int  == Nat \cup {Zero - n : n \in Nat}
-----------------------------------------------------------------------------
(***************************************************************************)
(*                            Exponentiation                               *)
(*                                                                         *)
(* Defining exponentiation of reals is a little tricky.  For example, \pi  *)
(* ^ \pi is a perfectly fine real number, as is (-\pi)^(-342).  However,   *)
(* (-1)^(1/2) and 0^-1 aren't.  We define a ^ b whenever (i) a # 0 and     *)
(* b \in Int, (ii) a > 0, or (iii) a = 0 and b > 0.                        *)
(***************************************************************************)
a ^ b == 
  LET RPos == {r \in Real \ {Zero} : Zero \leq r}
      exp  == CHOOSE f \in [(RPos \X Real) \cup ((Real \ {0}) \X Int)
                               \cup ({0} \X RPos) -> Real] :
               /\ \A r \in Real :
                    /\ f[r, Succ[Zero]] = r
                    /\ \A m, n \in Int : f[r, m+n] = f[r, m] * f[r, n]
               /\ \A r \in RPos :
                    /\ f[Zero, r] = Zero
                    /\ \A s, t \in Real : f[r, s*t] = f[f[r, s], t]
                    /\ \A s, t \in RPos : (s \leq t) => (f[r,s] \leq f[r,t])
  IN  exp[a, b]
-----------------------------------------------------------------------------
(***************************************************************************)
(* We don't have any way yet of writing numbers in the usual fashion, like *)
(* 305.  This is done in the Naturals module, in terms of the function     *)
(* NumValue on strings such that NumValue["305"] equals the number 305.    *)
(* For later use, we also define NumValue[""] to be zero.  To understand   *)
(* how that's done, you need to realize that, in TLA+, the string "305" is *)
(* a tuple of characters, which is a function with domain {1,2,3} that     *)
(* maps 1 to the character '3', etc.                                       *)
(***************************************************************************)
NumValue[s \in STRING] ==
  LET OneTo(n)   == {i \in Nat : (1 \leq i) /\ (i \leq n)}
        (*******************************************************************)
        (* The set {1, ... , n}.                                           *)
        (*******************************************************************)

      Length(ss) ==  CHOOSE n \in Nat : (DOMAIN ss) = OneTo(n)
        (*******************************************************************)
        (* The length of the string ss.                                    *)
        (*******************************************************************)

      AllButLast(ss)  == [i \in OneTo(Length(ss)-Succ[Zero]) |-> ss[i]]
        (*******************************************************************)
        (* AllButLast("305") = "30".                                       *)
        (*******************************************************************)
        
      Ten == Length("0123456789")
        (*******************************************************************)
        (* The number 10.                                                  *)
        (*******************************************************************)

      DigitVal(digit) == 
        (*******************************************************************)
        (* The numeric value of digit.  Thus, DigitVal("7"[1]) equals    *)
        (* the number 7.                                                   *)
        (*******************************************************************)
        (CHOOSE i \in OneTo(Ten) : "0123456789"[i] = digit) - Succ[Zero]

  IN  (*********************************************************************)
      (* The usual recursive definition:                                   *)
      (*    NumValue["305"] = 5 + 10 * NumValue["30"].                     *)
      (*********************************************************************)
      IF s = "" 
        THEN Zero
        ELSE DigitVal(s[Length(s)]) + Ten * NumValue[AllButLast(s)]
=============================================================================


