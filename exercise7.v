From elpi Require Import elpi.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Open Scope ring_scope.

Section CPGE.
(** #<div class='slide'>#
* Preliminaries

 - Every morphism induces an ismorphism between a complement of its kernel and its image.  The function #<code>pinvmx</code># is the inverse of this isomporhism, but since the complement of the kernel that was used to produce #<code>pinvmx</code># is arbitrary, we must project the result of #<code>pinvmx</code># on S in order to get the specific inverse with image S.

 - We thus define a matrix pinvmx_on S u, which represents the partial inverse of u that maps the image of u (represented by u) to S, and which is correct only when S is indeed a complement of kermx u.

#<div>#
*)
Lemma pinvmx_on_key : unit. Proof. exact: tt. Qed.
Definition pinvmx_on (F : fieldType) (m n : nat) (S : 'M_m)
   (A : 'M[F]_(m, n)) : 'M_(n, m) :=
 locked_with pinvmx_on_key (pinvmx A *m proj_mx S (kermx A)).

Lemma pinvmx_on_sub (F : fieldType) (m n : nat) (S : 'M_(m))
   (A : 'M[F]_(m, n)) : (pinvmx_on S A <= S)%MS.
Proof.
rewrite [pinvmx_on _ _]unlock.
by rewrite (submx_trans (proj_mx_sub _ _ _)) ?genmxE.
Qed.

Lemma mulmxKpV_on (F : fieldType) (m1 m2 n : nat) (S : 'M_(m2))
  (A : 'M[F]_(m1, n)) (B : 'M_(m2, n)) :
  (S :&: kermx B)%MS = 0 ->
  (S + kermx B == 1%:M)%MS ->
  (A <= B)%MS -> A *m pinvmx_on S B *m B = A.
Proof.
move=> SIkB0 SDkB1 subAB; rewrite [pinvmx_on _ _]unlock.
(*D*)rewrite -[RHS](mulmxKpV subAB).
(*D*)symmetry; apply: subr0_eq; rewrite -mulmxBl -mulmxBr (sub_kermxP _) //.
(*D*)by rewrite mulmx_sub // proj_mx_compl_sub // (eqmxP SDkB1) submx1.
(*A*)Qed.

(**
#</div>#
#</div>#
*)
(** -------------------------------------------- *)
(** #<div class='slide'>#

* Exercices de mathématiques oraux X-ens Algebre 1

* Exercise 6.12: Endomorphisms u such that Ker u = Im u.

Let E be a vector space (any dimension, but in Coq we reason in finite
dimension).
#<div>#
*)
Section ex_6_12.

Variables (F : fieldType) (n' : nat).
Let n := n'.+1.

Section Q1.
(**
#</div>#
** Question 1.

Let u be an endomorphism of E, such that Ker u = Im u and S be a
complement of Im u, so that E is the direct sum of S and Im u.

- First, prove that E is the direct sum of S and Ker u

#<div># *)
Variable (u : 'M[F]_n) (S : 'M[F]_n).
Hypothesis eq_keru_imu : (kermx u :=: u)%MS.
Hypothesis S_u_direct : (S :&: u)%MS = 0.
Hypothesis S_u_eq1 : (S + u == 1)%MS.

Fact S_ku_direct : (S :&: kermx u)%MS = 0.
Proof.
(*D*)apply/eqmx0P; rewrite !(cap_eqmx (eqmx_refl _) eq_keru_imu).
(*D*)by rewrite !S_u_direct submx_refl.
(*A*)Qed.
Hint Resolve S_ku_direct.

Fact S_ku_eq1 : (S + kermx u == 1)%MS.
(*A*)Proof. by rewrite !(adds_eqmx (eqmx_refl _) eq_keru_imu) S_u_eq1. Qed.
Hint Resolve S_ku_eq1.

Implicit Types (x y z : 'rV[F]_n).
(** #</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#

*** Question 1.a.

Show that for all x in E, there is a unique pair (y, z) in S² such
that x = y + u (z), and pose v and z so that y = v(x) and z = w(x).

Instead of defining y and z for each x, we now define explicitly the
matrix that computes y and z from x.

 - A direct consequence of this is that v and w will be morphisms by
  construction, you can thus skip the part of the paper proof that
  deals with this.

#<div># *)
Definition w := locked (proj_mx S u).
Definition v := locked (proj_mx u S * pinvmx_on S u).
(** #</div>#

Note that we used locking in order to protect w and v from expanding
unexpectedly during proofs.

#</div>#
*)
(** -------------------------------------------- *)
(** #<div class='slide'>#

**** Question 1.a.i.

Prove the following lemmas.

#<div># *)
Lemma wS x : (x *m w <= S)%MS.
Proof.
unlock w.
(*D*)by rewrite proj_mx_sub.
(*A*)Qed.

Lemma vS x : (x *m v <= S)%MS.
Proof.
unlock v.
(*D*) by rewrite mulmxA mulmx_sub ?pinvmx_on_sub.
(*A*)Qed.

Lemma w_id x : (x <= S)%MS -> x *m w = x.
Proof.
unlock w => xS.
(*D*)by rewrite proj_mx_id ?S_u_direct.
(*A*)Qed.
(** #</div>#

**** Question 1.a.ii.

#<div># *)
Lemma Su_rect x : x = x *m w + (x *m v) *m u.
Proof.
unlock v w.
(*D*)rewrite [x *m (_ *_)]mulmxA mulmxKpV_on ?proj_mx_sub//.
(*D*)by rewrite add_proj_mx // (eqmxP S_u_eq1) submx1.
(*A*)Qed.

(** #</div># #</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#

**** Question 1.a.iii.

From the following lemma

#<div># *)
Lemma Su_dec_eq0 y z : (y <= S)%MS -> (z <= S)%MS ->
  (y + z *m u == 0) = (y == 0) && (z == 0).
Proof.
move=> yS zS; apply/idP/idP; last first.
  by move=> /andP[/eqP -> /eqP ->]; rewrite add0r mul0mx.
rewrite addr_eq0 -mulNmx => /eqP eq_y_Nzu.
have : (y <= S :&: u)%MS by rewrite sub_capmx yS eq_y_Nzu submxMl.
rewrite S_u_direct // submx0 => /eqP y_eq0.
move/eqP: eq_y_Nzu; rewrite y_eq0 eq_sym mulNmx oppr_eq0 eqxx /= => /eqP.
move=> /sub_kermxP; rewrite eq_keru_imu => z_keru.
have : (z <= S :&: u)%MS by rewrite sub_capmx zS.
by rewrite S_u_direct // submx0.
Qed.
(** #</div>#
deduce

#<div># *)
Lemma Su_dec_uniq y y' z z' : (y <= S)%MS -> (z <= S)%MS ->
                              (y' <= S)%MS -> (z' <= S)%MS ->
  (y + z *m u == y' + z' *m u) = (y == y') && (z == z').
Proof.
(*D*)move=> yS zS y'S z'S; rewrite -subr_eq0 opprD addrACA -mulmxBl.
(*D*)by rewrite Su_dec_eq0 ?addmx_sub ?eqmx_opp // !subr_eq0.
(*A*)Qed.
(** #</div># #</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#
**** Question 1.a.iii.

Show some simplification lemmas
- the two first are direct
- the two last use Su_dec_uniq.

#<div># *)
Lemma u2_eq0 : u *m u = 0.
(*A*)Proof. by apply/sub_kermxP; rewrite eq_keru_imu. Qed.

Lemma u2K m (a : 'M_(m,n)) : a *m u *m u = 0.
(*D*)Proof. by rewrite -mulmxA u2_eq0 mulmx0. Qed.

Lemma uv x : (x <= S)%MS -> (x *m u) *m v = x.
Proof.
(*D*)move=> xS; have /eqP := Su_rect (x *m u).
(*D*)rewrite -[X in X == _]add0r Su_dec_uniq ?sub0mx ?vS ?wS //.
(*D*)by move=> /andP [_ /eqP <-].
(*A*)Qed.

Lemma uw x : (x <= S)%MS -> (x *m u) *m w = 0.
Proof.
(*D*)move=> xS; have /eqP := Su_rect (x *m u).
(*D*)rewrite -[X in X == _]add0r Su_dec_uniq ?sub0mx ?vS ?wS //.
(*D*)by move=> /andP [/eqP <-].
(*A*)Qed.
(** #</div># #</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#

*** Question 1.b.

- Show that v is linear. (by definition)
- Show that u o v + v o u = 1.

#<pre>#
Indeed u (v x) + v (u x)
  = u (v x) + v (u (w x)) + v (u (u (v x))) by Su_rect
  = u (v x) + v (u (w x)) by u2K
  = u (v x) + w x by uv
  = x by -Su_rect
#</pre>#
#<div># *)
Lemma add_uv_vu : v *m u + u *m v = 1.
Proof.
(*D*)apply/row_matrixP => i; rewrite !rowE; set x := delta_mx _ _.
(*D*)rewrite mulmx1 mulmxDr !mulmxA {2}[x]Su_rect mulmxDl u2K addr0.
(*D*)by rewrite uv ?wS // addrC -Su_rect.
(*A*)Qed.
(** #</div>#

*** Question 1.c.

- Show that w is linear.
- Show that u o w + w o u = u.

#<pre>#
Indeed u (w x) + w (u x)
  = u (w x) + w (u (w x)) + w (u (u (v x))) by Su_rect
  = u (w x) + w (u (w x)) by u2K
  = u (w x) by uw
  = u (x - u (v x)) by  Su_rect
  = u x by u2K
#</pre>#
#<div># *)
Lemma add_wu_uw : w *m u + u *m w = u.
Proof.
(*D*)apply/row_matrixP => i; rewrite !rowE; set x := delta_mx _ _.
(*D*)rewrite mulmxDr !mulmxA {2}[x]Su_rect mulmxDl u2K addr0 uw ?wS // addr0.
(*D*)by have /(canLR (addrK _)) <- := Su_rect x; rewrite mulmxBl u2K subr0.
(*A*)Qed.

End Q1.
(** #</div># #</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#

** Questions 2 and 3

Let u be a endomorphism of E such that u^2 = 0.

- Q2. Suppose there is a v such that u v + v u = 1, prove the kernel and image of u are equal.

- Q3. Suppose u != 0 and suppose there is a w such that uw + wu = u. Find a counter example of Ker u = Im u. (Hint: take u e1 = 0, u e2 = 0 and u e3 = e2 in 'M_3 and use a dimension argument).

#<div>#
*)

Section Q2.

Variable (u : 'M[F]_n).

Lemma u20_eq_u_kermx v : u ^+ 2 = 0 -> v *m u + u *m v = 1 -> (u == kermx u)%MS.
Proof.
(*D*)move=> u20 vuDuv_eq1; apply/andP; split; first by apply/sub_kermxP.
(*D*)apply/rV_subP => x /sub_kermxP xu_eq0.
(*D*)have /(congr1 (fun w => x *m w)) := vuDuv_eq1; rewrite mulmx1 => <-.
(*D*)by rewrite mulmxDr !mulmxA xu_eq0 mul0mx addr0 mulmx_sub.
(*A*)Qed.

End Q2.

Section Q3.

Hypothesis charF_neq2 : [char F]^'.-nat 2%N.

Let u : 'M[F]_3 :=
(*D*)\matrix_(i, j) ((i == 2%N :> nat) && (j == 1%N :> nat))%:R.
Let w : 'M[F]_3 :=
(*D*)2%:R^-1 *: 1.

Lemma u_neq0 : u != 0.
(*D*)by apply/negP => /eqP /matrixP /(_ 2%:R 1) /eqP; rewrite !mxE !eqxx oner_eq0.
(*A*)Qed.

Lemma wuDuw_eq_u : w *m u + u *m w = u.
Proof.
(*D*)rewrite -scalemxAl -scalemxAr mul1mx mulmx1 -scalerDl.
(*D*)by rewrite -mulr2n -mulr_natl divff ?natf_neq0 // scale1r.
(*A*)Qed.

Lemma neq_u_kermxu : (u != kermx u)%MS.
Proof.
(*D*)suff: \rank u != \rank (kermx u) by apply: contraNneq=> <-.
(*D*)by rewrite mxrank_ker; have := rank_leq_row u; case: (\rank _) => [|[|[]]].
(*A*)Qed.

End Q3.
End ex_6_12.
End CPGE.
