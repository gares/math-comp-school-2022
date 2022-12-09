From elpi Require Import elpi.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint rat intdiv.
From mathcomp Require Import zify ring lra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

(**
  ----
  ** Triangular number from Exercise session 2

Use the [lia] tactic to simplify the following proofs.
*)
Definition delta (n : nat) := (n.+1 * n)./2.

Lemma deltaS (n : nat) : delta n.+1 = delta n + n.+1.
Proof.
(*
rewrite /delta -addn2 mulnDl mulnC halfD.
rewrite !oddM andbF add0n mul2n.
suff -> : ((n.+1).*2)./2 = n.+1 by [].
by rewrite -[RHS](half_bit_double n.+1 false).
*)
(*D*)rewrite /delta; lia.
(*A*)Qed.

Lemma leq_delta (m n : nat) : m <= n -> delta m <= delta n.
Proof.
(* by move=> H; apply: half_leq; apply: leq_mul. *)
(*D*)move=> lemn; apply: half_leq; nia.
(*A*)Qed.

Lemma delta_square (n : nat) : (8 * delta n).+1 = n.*2.+1 ^ 2.
Proof.
(*
elim: n => // n IHn.
rewrite deltaS mulnDr -addSn IHn.
rewrite doubleS -addn1 -addnS -addSn addn1.
rewrite sqrnD -addnA /=.
congr (_ + _).
rewrite mulnS.
rewrite [_ * 2]mulSn mulnDr addnA.
congr (_ + _).
by rewrite mulnCA -muln2 -!mulnA mulnC.
*)
(*D*)elim: n => // n IHn; rewrite deltaS mulnDr -addSn IHn; lia.
(*A*)Qed.

(**
  ----
  ** Exercise 4 from Excersise session 3

Use the [lia] or [ring] tactic to simplify the following proofs.
*)

Lemma gauss_ex_nat1 (n : nat) : (\sum_(i < n) i).*2 = (n * n.-1)%N.
Proof.
(*
elim: n => [|n IH]; first by rewrite big_ord0.
rewrite big_ord_recr /=.
rewrite doubleD {}IH.
rewrite -muln2 -mulnDr addn2 mulnC.
by case: n.
*)
(*D*)elim: n => [|n IH]; first by rewrite big_ord0.
(*D*)by rewrite big_ord_recr /= doubleD {}IH; nia.
(*A*)Qed.

Lemma gauss_ex_nat2 (n : nat) : (\sum_(i < n) i)%N = (n * n.-1)./2.
Proof.
(*
elim: n => [|n IH]; first by rewrite big_ord0.
rewrite big_ord_recr /= {}IH.
case: n => // n.
rewrite -add2n mulnDl halfD 2!oddM mul2n doubleK /=.
by rewrite add0n addnC mulnC.
*)
(*D*)elim: n => [|n IH]; first by rewrite big_ord0.
(*D*)rewrite big_ord_recr /= {}IH; nia.
(*A*)Qed.

(**
  ----
  ** Square pyramidal number
*)
Lemma sum_square_p1 (n : nat) :
  ((\sum_(i < n) i ^ 2) * 6 = n.-1 * n * (n * 2).-1)%N.
Proof.
(*D*)elim: n => [|n IHn]; first by rewrite big_ord0.
(*D*)by rewrite mulSn add2n /= big_ord_recr /= mulnDl {}IHn; nia.
(*A*)Qed.

Lemma sum_square_p2 (n : nat) :
  ((\sum_(i < n) i ^ 2) = (n.-1 * n * (n * 2).-1) %/ 6)%N.
Proof.
(*D*)elim: n => [|n IHn]; first by rewrite big_ord0.
(*D*)rewrite mulSn add2n /= big_ord_recr /= {}IHn; nia.
(*A*)Qed.
