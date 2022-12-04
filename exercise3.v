From elpi Require Import elpi.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(**
  ----
  ** Exercise 1 *)

(**
Try to define a next function over 'I_n that correspond to the
successor function over the natural plus the special case that
"n -1" is mapped to zero

Hint: potentially useful theorems are: [ltn_neqAle], [ltnS], [negbT], [ifP]

Hint: potentially useful tactics are [case], [move], [rewrite]

Hint: you may also need to use the val function (or \val notation) *)

Definition onext n (x : 'I_n) : 'I_n.
Proof.
refine (
(* sub takes two arguments: a value and a proof *)
  sub
(* Write the valued in the following line *)
(*D*)(if val x == n.-1 then 0 else x.+1)
(* Leave _ for the proof, you will fill it in by tactics later *)
_
).
(*D*)case: x => [m /=].
(*D*)case: n => [ | n] /=.
(*D*)  by [].
(*D*)case: ifP.
(*D*)  move/eqP=> misn.
(*D*)  move=> _.
(*D*)  by [].
(*D*)move=> test_false.
(*D*)rewrite ltnS.
(*D*)move=> mlen.
(*D*)rewrite ltnS.
(*D*)have neq := negbT test_false.
(*D*)rewrite ltn_neqAle.
(*D*)rewrite neq.
(*D*)rewrite mlen.
(*D*)by [].
Defined.

Eval compute in val (onext (Ordinal (isT : 2 < 4))).
Eval compute in val (onext (Ordinal (isT : 3 < 4))).

(**
  ----
  ** Exercise 2
*)

(**
   Show that injectivity is decidable for a function [f : aT -> rT]
   when [aT] is a finite type.

   As a first step, we exhibit a boolean formulation of injectivity:
   a boolean formula, based on boolean "forall", "exists", and "==>" and
   boolean equality, which expresses the property of injectivity.

   We then show that this boolean formula is equivalent to th existing notion
   of [injective], which is not injective in general.
*)

Module MyInj.

Check injective.

Definition injectiveb (aT : finType) (rT : eqType) (f : aT -> rT) : bool :=
(*D*) [forall x : aT, forall y : aT, (f x == f y) ==> (x == y)].

Lemma injectiveP (aT : finType) (rT : eqType) (f : aT -> rT) :
  reflect (injective f) (injectiveb f).
Proof.
apply: (iffP forallP).
(*D*)  move=> Ibf.
(*D*)  move=> x.
(*D*)  move=> y.
(*D*)  move=> Efxy.
(*D*)  have {Ibf}:= Ibf x.
(*D*)  move=>/forallP Ibf'.
(*D*)  have {Ibf'} := Ibf' y.
(*D*)  move=>/implyP.
(*D*)  rewrite Efxy.
(*D*)  rewrite eqxx.
(*D*)  move=>Ibf''.
(*D*)  have{Ibf''} := Ibf'' isT.
(*D*)  move/eqP.
(*D*)  by [].
(*D*)move=> If x.
(*D*)apply/forallP=> y.
(*D*)apply/implyP=> /eqP Efxfy.
(*D*)apply/eqP.
(*D*)apply: If.
(*D*)by [].
(*A*)Qed.

End MyInj.
(**
  ----
  ** Exercise 3

  Build a function that maps an element of an ordinal to another element
  of the same ordinal with a p subtracted from it.

  Hint: if [i] has type ['I_n], then [i] can also be used for type [nat]
  and [i < n] is given by theorem [ltn_ord].  Others potentially useful
  theorems are [leq_ltn_trans] and [leq_subr]
*)

Lemma neg_offset_ord_proof n (i : 'I_n) (p : nat) : i - p < n.
Proof.
(*D*)have : i < n.
(*D*)  apply: ltn_ord.
(*D*)apply: leq_ltn_trans.
(*D*)by apply: leq_subr.
(*A*)Qed.

Definition neg_offset_ord n (i : 'I_n) p := Ordinal (neg_offset_ord_proof i p).

Eval compute in (val (neg_offset_ord (Ordinal (isT : 7 < 9)) 4)).

(**
  ----
  ** Exercise 4
*)

(**
   Prove the following statement by induction in several ways.
   - a proof by induction
   - a proof by reorganization:
     2 * (1 + 2 ... + n) = (1 + 2 ... + (n - 1) + n) +
                           (n + (n - 1) ... + 2 + 1)
                         =  (1 + n) + (2 + n - 1) + ... + (n + 1)
                         = n * (1 + n)
   Hint: potentially useful theorems: [big_ord0], [big_ord_recr],
     [doubleD], [muln2], [mulnDr], [addn2], [mulnC], [leq_trans],
     [ltnS], [leq_subr], [neg_offset_ord], [reindex_inj], [ord_max],
     [val_eqP], [eqP], [subKn], [ltnS], [big_split], [eqxx], [subnK],
     [eq_bigr], [sum_nat_const], [card_ord], [rev_ord_inj], [subSS]
                         
 *)

Lemma gauss_ex_p1 : forall n, (\sum_(i < n) i).*2 = n * n.-1.
Proof.
(*D*)elim=> [|n IH].
(*D*)  rewrite big_ord0.
(*D*)  by [].
(*D*)rewrite big_ord_recr /=.
(*D*)rewrite doubleD.
(*D*)rewrite {}IH.
(*D*)case: n => [| n /=].
(*D*)  by [].
(*D*)rewrite -muln2.
(*D*)rewrite -mulnDr.
(*D*)rewrite addn2.
(*D*)rewrite mulnC.
(*D*)by [].
(*A*)Qed.

Lemma gauss_ex_p2 : forall n, (\sum_(i < n) i).*2 = n * n.-1.
Proof.
(*D*)case=> [|n/=].
(*D*)  by rewrite big_ord0.
(*D*)rewrite -addnn.
(*D*)have Hf i : n - i < n.+1.
(*D*)  rewrite ltnS.
(*D*)  by apply: leq_subr.
(*D*)pose f (i : 'I_n.+1) := neg_offset_ord (@ord_max n) i.
(*D*)have f_inj : injective f.
(*D*)  move=> x y.
(*D*)  rewrite /f /=.
(*D*)  move=>/val_eqP/eqP /= Efxfy.
(*D*)  apply/val_eqP => /=.
(*D*)  have -> : \val x = n - (n - x).
(*D*)    rewrite subKn.
(*D*)      by [].
(*D*)    rewrite -ltnS.
(*D*)    by [].
(*D*)  rewrite Efxfy.
(*D*)  rewrite subKn.
(*D*)  rewrite eqxx.
(*D*)  by [].
(*D*)rewrite -ltnS.
(*D*)by [].
(*D*)rewrite {1}(reindex_inj f_inj) /=.
(*D*)rewrite -big_split /=.
(*D*)have ext_eq : forall i : 'I_n.+1, true -> n - i + i = n.
(*D*)  move=> i _.
(*D*)  rewrite subnK.
(*D*)    by [].
(*D*)  rewrite -ltnS.
(*D*)  by [].
(*D*)rewrite (eq_bigr (fun _ => n) ext_eq).
(*D*)rewrite sum_nat_const.
(*D*)rewrite card_ord.
(*D*)by[].
Qed.

Lemma gauss_ex_p3 : forall n, (\sum_(i < n) i).*2 = n * n.-1.
Proof.
(*D*)case=> [|n/=]; first by rewrite big_ord0.
(*D*)rewrite -addnn {1}(reindex_inj rev_ord_inj) -big_split /=.
(*D*)rewrite -[X in _ = X * _]card_ord -sum_nat_const.
(*D*)by apply: eq_bigr => i _; rewrite subSS subnK // -ltnS.
(*A*)Qed.

(**
  ----
  ** Exercise 5
*)

(**
   Try to formalize the following problem
*)

(**
  Given a parking  where the boolean indicates if the slot is occupied or not
*)

Definition parking n := 'I_n -> 'I_n -> bool.

(**
   Number of cars at line i
*)

Definition sumL n (p : parking n) i := \sum_(j < n) p i j.

(**
   Number of cars at column j
*)

Definition sumC n (p : parking n) j := \sum_(i < n) p i j.

(**
   Show that if 0 < n there is always two lines, or two columns, or a column and a line
   that have the same numbers of cars
*)

(* Two intermediate lemmas to use injectivity  *)

Lemma leq_sumL n (p : parking n) i : sumL p i < n.+1.
Proof.

(*D*)have {2}<-: \sum_(i < n) 1 = n by rewrite -[X in _ = X]card_ord sum1_card.
(*D*)by apply: leq_sum => k; case: (p _ _).
(*A*)Qed.

Lemma leq_sumC n (p : parking n) j : sumC p j < n.+1.
Proof.
(*D*)have {2}<-: \sum_(i < n) 1 = n by rewrite -[X in _ = X]card_ord sum1_card.
(*D*)by apply: leq_sum => k; case: (p _ _).
(*A*)Qed.

Lemma inl_inj {A B} : injective (@inl A B). Proof. by move=> x y []. Qed.
Lemma inr_inj {A B} : injective (@inr A B). Proof. by move=> x y []. Qed.

Lemma result n (p : parking n) : 0 < n ->
  exists i, exists j,
   [\/  (i != j) /\ (sumL p i = sumL p j),
        (i != j) /\ (sumC p i = sumC p j) | sumL p i = sumC p j].
Proof.
(*D*)case: n p => [//|[|n]] p _ /=.
(*D*)  exists ord0, ord0; apply: Or33.
(*D*)  by rewrite /sumL /sumC !big_ord_recl !big_ord0.
(*D*)pose sLC (i : 'I_n.+2 + 'I_n.+2) :=
(*D*)  match i with
(*D*)  | inl i => Ordinal (leq_sumL p i)
(*D*)  | inr i => Ordinal (leq_sumC p i) end.
(*D*)have [sC_inj | /injectivePn /=] := altP (injectiveP sLC).
(*D*)  have := max_card (mem (codom sLC)); rewrite card_codom // card_sum !card_ord.
(*D*)  by rewrite !addnS !addSn !ltnS -ltn_subRL subnn ltn0.
(*D*)move=> [[i|i] [[j|j] //=]]; [| |move: i j => j i|];
(*D*)rewrite ?(inj_eq inj_inl, inj_eq inj_inr) => neq_ij [];
(*D*)by exists i, j; do ?[exact: Or31|exact: Or32|exact: Or33].
(*A*)Qed.


(**
  ----
   ** Exercise 6
*)

Lemma sum_odd1 : forall n, \sum_(i < n) (2 * i + 1) = n ^ 2.
Proof.
(*D*)case=> [|n/=]; first by rewrite big_ord0.
(*D*)rewrite big_split -big_distrr /= mul2n gauss_ex_p3 sum_nat_const.
(*D*)by rewrite card_ord -mulnDr addn1 mulnn.
(*A*)Qed.

(**
  ----
  ** Exercise 7
*)

Lemma sum_exp : forall x n, x ^ n.+1 - 1 = (x - 1) * \sum_(i < n.+1) x ^ i.
Proof.
(*D*)move=> x n.
(*D*)rewrite mulnBl big_distrr mul1n /=.
(*D*)rewrite big_ord_recr [X in _ = _ - X]big_ord_recl /=.
(*D*)rewrite [X in _ = _ - (_ + X)](eq_bigr (fun i : 'I_n =>  x * x ^ i))
(*D*)      => [|i _]; last by rewrite -expnS.
(*D*)rewrite [X in _ = X - _]addnC [X in _ = _ - X]addnC subnDA addnK.
(*D*)by rewrite expnS expn0.
(*A*)Qed.

(**
  ----
 ** Exercise 8
*)

(** Prove the following statement by induction and by using a similar trick
   as for Gauss noticing that n ^ 3 = n * (n ^ 2) *)

Lemma bound_square : forall n, \sum_(i < n) i ^ 2 <= n ^ 3.
Proof.
(*D*)move=> n.
(*D*)rewrite expnS -[X in _ <= X * _]card_ord -sum_nat_const /=.
(*D*)elim/big_ind2: _ => // [* |i]; first exact: leq_add.
(*D*)by rewrite leq_exp2r // ltnW.
(*A*)Qed.

(**
  ----
  ** Exercise 9

  Prove the following statement using only big operator theorems.
  [big_cat_nat], [big_nat_cond], [big_mkcondl], [big1]
*)
Lemma sum_prefix_0 (f : nat -> nat) n m : n <= m ->
  (forall k, k < n -> f k = 0) ->
  \sum_(0 <= i < m) f i = \sum_(n <= i < m) f i.
Proof.
(*D*)pose H := big_cat_nat.
(*D*)move => nm f0; rewrite (big_cat_nat _ _ f (leq0n n)) /=; last by [].
(*D*)rewrite big_nat_cond big_mkcondl big1 ?add0n //.
(*D*)move => i _; case cnd : (0 <= i < n) => //.
(*D*)apply: f0.
(*D*)by move/andP: cnd => [_ it].
(*A*)Qed.

(**
  ----
  ** Exercise 10
*)

(**
  building a monoid law
*)

Section cex.

Variable op2 : nat -> nat -> nat.

Hypothesis op2n0 : right_id 0 op2.

Hypothesis op20n : left_id 0 op2.

Hypothesis op2A : associative op2.

Hypothesis op2add : forall x y, op2 x y = x + y.

HB.instance Definition _ := Monoid.isLaw.Build nat 0 op2 op2A op20n op2n0.

Lemma ex_op2 : \big[op2/0]_(i < 3) i = 3.
Proof.
(*D*)by rewrite !big_ord_recr big_ord0 /= !op2add.
(*A*)Qed.

End cex.
