From mathcomp Require Import all_ssreflect all_algebra all_field.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory UnityRootTheory.
Open Scope ring_scope.

Section PreliminaryLemmas.
(** -------------------------------------------- *)
(** #<div class='slide'>#
* Preliminaries

In this exercise session, we will use complex algebraic numbers
instead of complex numbers. This is for a technical reason, please
think of algebraic numbers as if they were complex numbers, since they
enjoy the same first order theory.

Let's extend the library of algebraic numbers with some easy lemmas
first.

** Question 1: prove that if a sum of natural numbers is 1 then one of its term is 0 and the other is 1

Note that we do not consider nat but the copy of nat which is embeded
in the algebraic numbers algC. The theorem is easy to prove for nat,
so we suggest you use a compatibility lemma numbers between nat and
Cnat

#<div># *)
Lemma Cnat_add_eq1 : {in Cnat &, forall x y,
   (x + y == 1) = ((x == 1) && (y == 0))
               || ((x == 0) && (y == 1))}.
Proof.
(*D*)move=> x y /CnatP [n ->] /CnatP [m ->]; rewrite -natrD !pnatr_eq1 ?pnatr_eq0.
(*D*)by move: n m => [|[|?]] [|[|?]].
(*A*)Qed.
(**
#</div>#
** Question 2: The real part of product
#<div>#
*)
Lemma ReM (x y : algC) :
  'Re (x * y) = 'Re x * 'Re y - 'Im x * 'Im y.
Proof.
(*D*)rewrite {1}[x]algCrect {1}[y]algCrect mulC_rect Re_rect //;
(*D*)by rewrite rpredD ?rpredN // rpredM // ?Creal_Re ?Creal_Im.
(*A*)Qed.
(**
#</div>#
** Question 3: The imaginary part of product

(it's the same proof except for 2 characters, don't do it if takes more than 5s)
#<div>#
*)
Lemma ImM (x y : algC) :
  'Im (x * y) = 'Re x * 'Im y + 'Re y * 'Im x.
Proof.
(*D*)rewrite {1}[x]algCrect {1}[y]algCrect mulC_rect Im_rect //;
(*D*)by rewrite rpredD ?rpredN // rpredM // ?Creal_Re ?Creal_Im.
(*A*)Qed.

End PreliminaryLemmas.
(**
#</div>#
#</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#
* The ring of Gaussian integers

References:
 - #<a href="https://en.wikipedia.org/wiki/Gaussian_integer">Gaussian Integer on wikipedia</a>#
 - exercices de mathematiques oraux X-ENS algebre 1, Exercice 3.10. ENS Lyon

Gaussian integers are complex numbers of the form (n + i m) where n and m are integers. We will prove they form a ring, and determine the units of this ring.

#<div>#
*)
Section GaussianIntegers.
(**
#</div>#
- First we define a predicate for the algebraic numbers which are Gaussian integers.
#<div>#
*)
Definition gaussInteger :=
  [qualify a x | ('Re x \in Cint) && ('Im x \in Cint)].
(**
#</div>#
- You need to use qualifE to reduce (x \ in gaussInteger) to its definition.

** Question 4: Prove that integers are Gaussian integers
#<div>#
*)
Lemma Cint_GI (x : algC) : x \in Cint -> x \is a gaussInteger.
Proof.
(*D*)move=> x_int; rewrite qualifE (Creal_ReP _ _) ?(Creal_ImP _ _) ?Creal_Cint //.
(*D*)by rewrite x_int rpred0.
(*A*)Qed.
(** #</div>#
#</div>#
 *)
(** -------------------------------------------- *)
(** #<div class='slide'>#
** Question 5: Prove that Gaussian integers form a subring
#<div>#
*)
Lemma GI_subring : subring_closed gaussInteger.
Proof.
(*D*)split => [|x y /andP[??] /andP[??]|x y /andP[??] /andP[??]].
(*D*)- by rewrite Cint_GI.
(*D*)- by rewrite qualifE !raddfB /= ?rpredB.
(*D*)by rewrite qualifE ReM ImM rpredB ?rpredD // rpredM.
(*A*)Qed.
(**
#</div>#
- There follows the boilerplate to use the proof GI_subring in order to canonically provide a subring structure to the predicate gaussInteger.
#<div>#
*)
Fact GI_key : pred_key gaussInteger. Proof. by []. Qed.
Canonical GI_keyed := KeyedQualifier GI_key.
Canonical GI_opprPred := OpprPred GI_subring.
Canonical GI_addrPred := AddrPred GI_subring.
Canonical GI_mulrPred := MulrPred GI_subring.
Canonical GI_zmodPred := ZmodPred GI_subring.
Canonical GI_semiringPred := SemiringPred GI_subring.
Canonical GI_smulrPred := SmulrPred GI_subring.
Canonical GI_subringPred := SubringPred GI_subring.
(**
#</div>#
- Finally, we define the type of Gaussian Integer, as a sigma type of algebraic numbers. We soon prove that this is in fact a sub type.
#<div>#
*)
Record GI := GIof {
  algGI : algC;
  algGIP : algGI \is a gaussInteger }.
Hint Resolve algGIP.
(**
#</div>#

- We provide the subtype property, this makes it possible to use the generic operator "val" to get an algC from a Gaussian Integer.
#<div>#
*)
Canonical GI_subType := [subType for algGI].
(**
#</div>#
- We deduce that the real and imaginary parts of a GI are integers
#<div>#
*)
Lemma GIRe (x : GI) : 'Re (val x) \in Cint.
Proof. by have /andP [] := algGIP x. Qed.
Lemma GIIm (x : GI) : 'Im (val x) \in Cint.
Proof. by have /andP [] := algGIP x. Qed.
Hint Resolve GIRe GIIm.

Canonical ReGI x := GIof (Cint_GI (GIRe x)).
Canonical ImGI x := GIof (Cint_GI (GIIm x)).
(**
#</div>#
- We provide a ring structure to the type GI, using the subring canonical property for the predicate gaussInteger
#<div>#
*)
Definition GI_eqMixin := [eqMixin of GI by <:].
Canonical GI_eqType := EqType GI GI_eqMixin.
Definition GI_choiceMixin := [choiceMixin of GI by <:].
Canonical GI_choiceType := ChoiceType GI GI_choiceMixin.
Definition GI_countMixin := [countMixin of GI by <:].
Canonical GI_countType := CountType GI GI_countMixin.
Definition GI_zmodMixin := [zmodMixin of GI by <:].
Canonical GI_zmodType := ZmodType GI GI_zmodMixin.
Definition GI_ringMixin := [ringMixin of GI by <:].
Canonical GI_ringType := RingType GI GI_ringMixin.
Definition GI_comRingMixin := [comRingMixin of GI by <:].
Canonical GI_comRingType := ComRingType GI GI_comRingMixin.
(* Definition GI_unitRingMixin := [unitRingMixin of GI by <:]. *)
(* Canonical GI_unitRingType := UnitRingType GI GI_unitRingMixin. *)
(**
#</div>#

 - Now we build the unitRing and comUnitRing structure of gauss
   integers. Contrarily to the previous structures, the operator is
   not the same as on algebraics. Indeed the invertible algebraics are
   not necessarily invertible Gaussian integers.

 - Hence, we define the inverse of Gaussian integers as follow : if the
   algebraic inverse happens to be a Gaussian integer we recover the
   proof and package it together with the element and get a gauss
   integer, otherwise, we default to the identity.

 - A Gaussian integer is invertible if the algbraic inverse is a gauss
   integer.
#<div>#
*)
Definition invGI (x : GI) := insubd x (val x)^-1.
Definition unitGI := [pred x : GI | (x != 0)
          && ((val x)^-1 \is a gaussInteger)].
(**
#</div>#
#</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#

** Question 6: prove a few facts in order to find a comUnitRingMixin for GI, and then instantiate the interfaces of unitRingType and comUnitRingType.

Do only one of the following proofs.

#<div>#
*)
Fact mulGIr : {in unitGI, left_inverse 1 invGI *%R}.
Proof.
(*D*)move=> x /andP [x_neq0 xVGI]; rewrite /invGI.
(*D*)by apply: val_inj; rewrite /= insubdK // mulVr ?unitfE.
(*A*)Qed.

Fact unitGIP (x y : GI) : y * x = 1 -> unitGI x.
Proof.
(*D*)rewrite /unitGI => /(congr1 val) /=.
(*D*)have [-> /eqP|x_neq0] := altP (x =P 0); first by rewrite mulr0 eq_sym oner_eq0.
(*D*)by move=> /(canRL (mulfK x_neq0)); rewrite mul1r => <- /=.
(*A*)Qed.

Fact unitGI_out : {in [predC unitGI], invGI =1 id}.
Proof.
move=> x.
(*D*)rewrite !inE /= /unitGI.
(*D*)rewrite negb_and negbK => /predU1P [->|/negPf xGIF];
(*D*)by apply: val_inj; rewrite /invGI ?val_insubd /= ?xGIF // invr0 if_same.
(*A*)Qed.
(*D*)
Definition GI_comUnitRingMixin :=
  ComUnitRingMixin mulGIr unitGIP unitGI_out.
Canonical GI_unitRingType := UnitRingType GI GI_comUnitRingMixin.
Canonical GI_comUnitRingType := [comUnitRingType of GI].
(**
#</div>#
#<div>#
*)
(** -------------------------------------------- *)
(** #<div class='slide'>#

** Question 7: Show that Gaussian integers are stable by conjugation.

#<div>#
*)
Lemma conjGIE x : (x^* \is a gaussInteger) = (x \is a gaussInteger).
(*A*)Proof. by rewrite ![_ \is a _]qualifE Re_conj Im_conj rpredN. Qed.
(**
#</div>#
- We use this fact to build the conjugation of a Gaussian Integers
#<div>#
*)
Fact conjGI_subproof (x : GI) : (val x)^* \is a gaussInteger.
Proof. by rewrite conjGIE. Qed.

Canonical conjGI x := GIof (conjGI_subproof x).
(**
#</div>#
- We now define the norm (stasm) for Gaussian integer, we don't need to specialize it to Gaussian integer so we define it over algebraic numbers instead.
#<div>#
*)
Definition gaussNorm (x : algC) := x * x^*.
Lemma gaussNorm_val (x : GI) : gaussNorm (val x) = val (x * conjGI x).
Proof. by []. Qed.
(**
#</div>#
#</div>#
*)
(** -------------------------------------------- *)
(** #<div class='slide'>#

** Question 8: Show that the gaussNorm of x is the square of the complex modulus of x

Hint: only one rewrite with the right theorem.
#<div>#
*)
Lemma gaussNormE x : gaussNorm x = `|x| ^+ 2.
(*A*)Proof. by rewrite normCK. Qed.
(**
#</div>#

** Question 9: Show that the gaussNorm of an Gaussian integer is a natural number.

#<div>#
*)
Lemma gaussNormCnat (x : GI) : gaussNorm (val x) \in Cnat.
(*A*)Proof. by rewrite /gaussNorm -normCK normC2_Re_Im rpredD // Cnat_exp_even. Qed.
Hint Resolve gaussNormCnat.
(**
#</div>#

** Question 10: Show that gaussNorm is multiplicative (on all algC).

Hint: use morphism lemmas #<code>rmorph1</code># and #<code>rmorphM</code>#
#<div>#
*)
Lemma gaussNorm1 : gaussNorm 1 = 1.
(*A*)Proof. by rewrite /gaussNorm rmorph1 mulr1. Qed.

Lemma gaussNormM : {morph gaussNorm : x y / x * y}.
(*A*)Proof. by move=> x y; rewrite /gaussNorm rmorphM mulrACA. Qed.
(**
#</div>#
#</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#

** Question 11 (hard): Find the invertible elements of GI

Do unitGI_norm1 first, and come back to side lemmas later.
#<div>#
*)
Lemma rev_unitrPr (R : comUnitRingType) (x y : R) :
   x * y = 1 -> x \is a GRing.unit.
Proof. by move=> ?; apply/unitrPr; exists y. Qed.

Lemma eq_algC a b :
  (a == b :> algC) = ('Re a == 'Re b) && ('Im a == 'Im b).
Proof.
rewrite -subr_eq0 [a - b]algCrect -normr_eq0 -sqrf_eq0.
rewrite normC2_rect ?paddr_eq0 ?sqr_ge0 -?realEsqr ?Creal_Re ?Creal_Im //.
by rewrite !sqrf_eq0 !raddfB ?subr_eq0.
Qed.
(*
Lemma primitive_root_i : 4.-primitive_root 'i.
Proof.
(*D*)have : 'i ^+ 4 = 1 by rewrite [_ ^+ (2 * 2)]exprM sqrCi -signr_odd expr0.
(*D*)move=> /prim_order_exists [] // [//|[|[|[//|[//|//]]]]] /prim_expr_order.
(*D*)  rewrite expr1 => /(congr1 (fun x => 'Im x)) /eqP.
(*D*)  by rewrite Im_i (Creal_ImP _ _) ?oner_eq0 ?rpred1.
(*D*)by move/eqP; rewrite sqrCi eq_sym -addr_eq0 paddr_eq0 ?ler01 ?oner_eq0.
(*A*)Qed.

Lemma primitive_rootX_unity (C: fieldType) n (x : C) :
  n.-primitive_root x ->
  n.-unity_root =i [seq x ^+ (val k) | k <- enum 'I_n].
Proof.
(*D*)move=> x_p y; rewrite -topredE /= unity_rootE; apply/idP/idP; last first.
(*D*)  by move=> /mapP [k _ ->]; rewrite exprAC [x ^+ _]prim_expr_order // expr1n.
(*D*)by move=> /eqP/(prim_rootP x_p)[k ->]; apply/mapP; exists k; rewrite ?mem_enum.
(*A*)Qed.

Lemma unitGI_norm1 (a : GI) :
  (a \in GRing.unit) = (val a \in 4.-unity_root).
(*D*)Proof. (*give trace*)
transitivity (gaussNorm (val a) == 1).
  apply/idP/idP; last first.
(*a*)    by rewrite gaussNorm_val (val_eqE _ (1 : GI)) => /eqP /rev_unitrPr.
(*D*)  move=> /unitrPr [b /(congr1 (gaussNorm \o val)) /=] /eqP.
(*a*) by rewrite gaussNormM gaussNorm1 Cnat_mul_eq1 // => /andP [].
rewrite (primitive_rootX_unity primitive_root_i).
rewrite (map_comp (GRing.exp 'i) val) val_enum_ord /=.
rewrite /= expr0 expr1 sqrCi exprSr sqrCi mulN1r.
rewrite !in_cons in_nil ?orbF orbA orbAC !orbA orbAC -!orbA.
(*D*)rewrite [val a in LHS]algCrect gaussNormE normC2_rect ?Creal_Re ?Creal_Im //.
(*D*)rewrite Cnat_add_eq1 ?Cnat_exp_even // !sqrf_eq0 !sqrf_eq1.
(*D*)rewrite andb_orr andb_orl -!orbA.
(*D*)rewrite ?[val _ == _]eq_algC !raddfN /=.
(*a*)by rewrite Re_i Im_i ?(Creal_ReP 1 _) ?(Creal_ImP 1 _) ?oppr0.
(*A*)Qed.
*)
End GaussianIntegers.
