From elpi Require Import elpi.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg poly ssrnum ssrint rat intdiv.
From mathcomp Require Import zify ring lra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
(**
  ----
  ** Triangular number from Exercise session 2

Use the [lia] and [nia] tactics to prove the following lemmas.
*)
Definition delta (n : nat) := (n.+1 * n)./2.

Lemma deltaS (n : nat) : delta n.+1 = delta n + n.+1.
Proof.
(*D*)rewrite /delta; lia.
(*A*)Qed.

Lemma leq_delta (m n : nat) : m <= n -> delta m <= delta n.
Proof.
(*D*)move=> lemn; apply: half_leq; nia.
(*A*)Qed.

(** Use induction and the [lia] tactic to prove the following lemma. *)

Lemma delta_square (n : nat) : (8 * delta n).+1 = n.*2.+1 ^ 2.
Proof.
(*D*)elim: n => // n IHn; rewrite deltaS mulnDr -addSn IHn; lia.
(*A*)Qed.
(**
  ----
  ** Exercise 4 from Excersise session 3

Use induction and the [nia] tactic to prove the following lemmas.
*)
Lemma gauss_ex_nat1 (n : nat) : (\sum_(i < n) i).*2 = n * n.-1.
Proof.
(*D*)elim: n => [|n IH]; first by rewrite big_ord0.
(*D*)by rewrite big_ord_recr /= doubleD {}IH; nia.
(*A*)Qed.

Lemma gauss_ex_nat2 (n : nat) : \sum_(i < n) i = (n * n.-1)./2.
Proof.
(*D*)elim: n => [|n IH]; first by rewrite big_ord0.
(*D*)rewrite big_ord_recr /= {}IH; nia.
(*A*)Qed.
(**
Use induction and the [ring] tactic to prove the following lemma (it is also
possible to use [lia] though).

_NB_: there is a bug in the [ring] tactic of Algebra Tactics that it does not
recognize [_.+1] (successor) inside [_%:R] (generic embedding of natural numbers
to ring). You have to explicitly rewrite it by the [natr1] lemma for now.
*)
Lemma gauss_ex_int1 (n : nat) (m : int) :
  ((\sum_(i < n) (m + i%:R)) * 2 = (m * 2 + n%:R - 1) * n%:R)%R.
Proof.
(*D*)elim: n => [|n IH]; first by rewrite big_ord0 mulr0.
(*D*)rewrite big_ord_recr /= mulrDl {}IH -natr1; ring.
(*A*)Qed.
(**
  ----
  ** Pyramidal numbers

Use induction and the [nia] tactic to prove the following lemmas.
*)
Lemma sum_squares_p1 (n : nat) :
  (\sum_(i < n) i ^ 2) * 6 = n.-1 * n * (n * 2).-1.
Proof.
(*D*)elim: n => [|n IHn]; first by rewrite big_ord0.
(*D*)by rewrite mulSn add2n /= big_ord_recr /= mulnDl {}IHn; nia.
(*A*)Qed.

Lemma sum_squares_p2 (n : nat) :
  \sum_(i < n) i ^ 2 = (n.-1 * n * (n * 2).-1) %/ 6.
Proof.
(*D*)elim: n => [|n IHn]; first by rewrite big_ord0.
(*D*)rewrite mulSn add2n /= big_ord_recr /= {}IHn; nia.
(*A*)Qed.

Lemma sum_cubes_p1 (n : nat) : (\sum_(i < n) i ^ 3) * 4 = (n * n.-1) ^ 2.
Proof.
(*D*)elim: n => [|n IHn]; first by rewrite big_ord0.
(*D*)rewrite big_ord_recr /= mulnDl {}IHn; nia.
(*A*)Qed.
(**
Use induction and the [lia] tactic to prove the following lemma.

_NB_: Apparently, [nia] is not powerful enough to deal with nonlinearity and
Euclidean division by 2 at the same time in this problem. You have to deal with
Euclidean division by 2 manually.
*)
Lemma sum_cubes_p2 (n : nat) : \sum_(i < n) i ^ 3 = ((n * n.-1) %/ 2) ^ 2.
Proof.
(*D*)elim: n => [|n IHn]; first by rewrite big_ord0.
(*D*)rewrite big_ord_recr /= {}IHn; case: n => //= n.
(*D*)rewrite [in RHS]mulnC -[in RHS]add2n mulnDr divnMDl // sqrnD.
(*D*)rewrite -addnA addnCA mulnCA [2 * _]mulnC divnK; first lia.
(*D*)rewrite dvdn2 oddM; lia.
(*A*)Qed.
(**
  ----
  ** Polynomials

Use the [ring] tactic to prove the following lemma.

_NB_: the [ring] tactic does not directly support the scalar multiplication
operator [(_ *: _)]. You have to explicitly rewrite them.
*)
Lemma polyeq_p1 (R : comRingType) :
  (4 *: 'X^3 - 3 *: 'X + 1)%R = (('X + 1) * (2 *: 'X - 1) ^+ 2)%R :> {poly R}.
Proof.
(*D*)rewrite -!mul_polyC; ring.
(*A*)Qed.
