
From elpi Require Import elpi.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssralg countalg poly polydiv. (* all_algebra *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(** 
#<div class="slide">#
 ** The Polynomials Library : 
#<a href="https://math-comp.github.io/htmldoc_2_0_alpha1/mathcomp.algebra.poly.html">poly.v</a>#
  - A  library for univariate polynomials over
    ring  structures
  - with extensions for  polynomials whose coefficients range over
    - commutative rings 
    - integral domains
#</div>#
----
#<div class="slide">#
 ** The Polynomials

Roadmap of the lesson:
 - Definitions
 - Ring Structure
 - Evaluation
 - Derivative
 - Roots
#</div>#
----
#<div class="slide">#
** Definition 
 - P = a_n X^n + ... + a_2 X^2 + a_1 X + a_0 

#<div class="note">(notes)<div class="note-text">#
   - list of coefficients (decreasing/increasing  degrees)
   - list of pairs (degree, coef)
#</div></div>#

#</div>#
----
#<div class="slide">#
** Math Components library choice:

 - P = a_0 + a_1 X + a_2 X^2 + ... + a_n X^n

   - a list of coefficients (increasing  degrees)

   - A  normalized (i.e. no trailing 0) sequence of coefficients
<<
Record polynomial (R : ringType) := 
Polynomial {polyseq :> seq R; _ : last 1 polyseq != 0}.
>>

#<div>#
*)

Open Scope ring_scope.

Check Polynomial.

Variable R: ringType.
Variable x :R.

Fact hs: last 1 [::1;x;0;1 ] != 0.
rewrite /=.
exact: GRing.oner_neq0.
Qed.

Definition P := Polynomial hs.




(**
#</div>#
#</div>#
----
#<div class="slide ">#

 ** First properties 
 
Polynomials are coercible to sequences:
 - one can directly take the k_th element of a polynomial

   -  P'_k i.e. retrieve the coefficient of X^k in P.

 - size of a polynomial 
 - the degree of a polynomial is its size minus 1
#<div>#

#<div class="note">(notes)<div class="note-text">#
   Look theorems ans definitions about size, lead_coef in poly.v
  #</div></div>#
*)

Check (size P).

Eval compute in (size P).

Eval compute in  P`_1.

Definition deg (Q : polynomial R):= ((size Q) - 1)%N.



(**
#</div>#
#</div>#
----
#<div class="slide ">#
** Notations
 - {poly R}: polynomials over R (a Ring)
 - Poly s : the polynomial built from sequence s
 - 'X: monomial
 - 'X^n : monomial to the power of n
 - [a%:P] : constant polynomial
 - standard notations of ssralg (+, -, *, *:, ^+)
#<div>#
*)


Definition P1 := Poly [::1;x;0;x].

Check 'X. 
Check (x*:'X + 1%:P).

(**
#</div>#
#</div>#
----

#<div class="slide ">#
** Definition by extension
 - [\poly_(i < n) E i] 
    is the polynomial:

    - (E 0) + (E 1)  *: 'X + ...  + E (n - 1) *: 'X^(n-1)
#</div>#
----
#<div class="slide">#

** Ring Structure
 - addition 
 - multiplication
#<div>#
*)

Let  P2: {poly R}:= \poly_(i < 10 ) i%:R.

Definition add_poly (p q : {poly R}) := 
\poly_(i < maxn (size p) (size q)) (p`_i + q`_i).

(*  multiplication  *)

Definition mul_poly (p q : {poly R}) :=
  \poly_(i < (size p + size q).-1)
    (\sum_(j < i.+1) p`_j * q`_(i - j)).

(** 
#</div>#
#</div>#
----
#<div class="slide  ">#

** The ring of polynomials
 - The type of polynomials has been equipped
     with a (commutative / integral) ring structure.

 - All related lemmas of ssralg can be used.
#</div>#
----
#<div class="slide vfill">#
** Evaluation of polynomials
 - Warning: type of x 
#<div>#
*)

Fixpoint horner s (x:R) :=
  if s is a :: s'
    then horner s' x * x + a
    else 0.

Notation "p .[ x ]" := (horner p x).


(** 
#</div>#
#</div>#
----
#<div class="slide">#

** Properties of coefficients
 - Lifting a ring predicate to polynomials.
#<div>#
 *)

Definition polyOver (S : {pred R}) :=
  [qualify a p : {poly R} | all (mem S) p].

Lemma polyOver_poly (S : {pred R}) n E :
  (forall i, (i < n)%N -> E i \in S) -> \poly_(i < n) E i \is a polyOver S.
Admitted.

(** 
#</div>#
#</div>#
----
#<div class="slide ">#
** polyOver's lemmas
 - predicate associate to S: at least an addrPred
   -  polyOver0
   - polyOverC 
   -  polyOverX
   - rpred* (from ssralg)
#<div>#
*)
Check polyOver0.


(** 
#</div>#
#</div>#
----
#<div class="slide  ">#
** Derivative
 - definition 
 - notation
 - properties
#<div>#
*)



Definition deriv (p:{poly R}) := 
   \poly_(i < (size p).-1) (p`_i.+1 *+ i.+1).

Local Notation "p ^` ()" := (deriv p).

Fact deriv_is_linear : linear deriv.
Admitted.

Lemma derivM p q : 
(p * q)^`() = p^`() * q + p * q^`().
Admitted.

Definition derivn n p := iter n deriv p.

Notation "p ^` ( n )" := (derivn n p) : ring_scope.

Check polyOver_deriv.

(** 
#</div>#
#</div>#
----
#<div class="slide vfill ">#
** Roots
 -  root p x == x is a root of p 
#<div>#
*)
Definition root p : pred R := fun x => p.[x] == 0.

Theorem factor_theorem p a : 
  reflect (exists q, p = q * ('X - a%:P)) 
      (root p a).
Admitted.

Theorem max_poly_roots (p: {poly R}) rs :
  p != 0 -> all (root p) rs -> uniq rs -> 
   (size rs < size p)%N.
Admitted.



(** 
#</div>#
#</div>#
----
#<div class="slide  ">#
** Division
- division and its theory are in the #<a href="https://math-comp.github.io/htmldoc_2_0_alpha1/mathcomp.algebra.polydiv.html">polydiv.v</a># file

#</div>#
*)
