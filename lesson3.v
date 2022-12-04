From elpi Require Import elpi.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** 

----
#<div class="slide">#
** Roadmap for lessons 3 and 4

    - finite types
    - big operators

*)

(**
#</div>#
----
#<div class="slide">#
** Lesson 3 

    - The math-comp library gives some support for finite types.
    - ['I_n] is the the set of natural numbers smaller than n.
    - [a : 'I_n] is composed of a value m and a proof that [m < n].

    - Example : [oid] modifies the proof part with an equivalent one.

#<div>#
*)

Definition oid n (x : 'I_n) : 'I_n.
Proof.
pose v := nat_of_ord x.
pose H := ltn_ord x.
pose H1 := leq_trans H (leqnn n).
exact: Ordinal H1.
Defined.

(** 
#</div>#
** Note

    - [nat_of_ord] is a coercion (see H)
    - ['I_0] is an empty type
#<div>#
*)

Lemma empty_i0 (x : 'I_0) : false.
Proof. 
case: x. 
by [].
Qed.

(** 
#</div>#
#</div>#
----
#<div class="slide">#
  ** Equality

    - Every finite type is also an equality type.
    - For ['I_n], only the numeric value matters (the proof is irrelevant)
    - This characteristic comes with the notion of subtype.
      together with a function val (injection from the subtype to the
      larger type)

#<div>#
*)

Definition i3 := Ordinal (isT : 3 < 4).

Lemma ieq : oid i3 == i3.
Proof.
exact: eqxx.
Qed.

Lemma ieq' (h : 3 < 4) : Ordinal h == i3.
Proof.
apply/eqP.
pose H := val_inj.
apply:val_inj.
rewrite /=.
by [].
Qed.

(**
#</div>#
#</div>#
----
#<div class="slide">#
   ** An optimistic map from [nat] to [ordinal] : [inord]

    - Takes a natural number as input and return an element of ['I_n.+1]
    - The _same number_ if it is small enough, otherwise [0].
    - The expected type has to have the shape ['I_n.+1] because ['I_0] is empty

#<div>#
*)

Check inord.

Check inordK.

Check inord_val.

Example inord_val_3_4 : inord 3 = (Ordinal (isT : 3 < 4)) :> 'I_4.
Proof.
apply:val_inj. rewrite /=. rewrite inordK. by []. by [].
Qed.

(** 
#</div>#
** Note
    - The equality in [inordK] is in type [nat]
    - The equality in [inord_val] is in type ['I_n.+1]
#<div>#
*)

(** 
#</div>#
#</div>#
----
#<div class="slide">#
  ** Sequence

    - a finite type can be seen as a sequence
    - if [T] is a finite type, [enum T] gives this sequence.
    - it is duplicate free.
    - it relates to the cardinal of a finite type

#<div>#
*)

Lemma iseq n (x : 'I_n) : x \in 'I_n.
Proof.
set l := enum 'I_n.
rewrite /= in l.
have ordinal_finType_n := [finType of 'I_n].
have mem_enum := mem_enum.
have enum_uniq := enum_uniq.
have cardT := cardT.
have cardE := cardE.
by [].
Qed.

(** 
#</div>#
** Note
    - None of the lines before [by []] are needed for the proof
    - [mem_enum] et [enum_uniq] are generic theorems for any predicate
       on the finite type (practically: subsets)
    - In this excerpt, we start a habit of making some theorems appear
      in the context, under the same or a similar name, just for
      scrutiny (here [mem_enum], [enum_uniq], [cardT], and [cardE]
#<div>#
*)

(** 
#</div>#
#</div>#
----
#<div class="slide">#
  ** Boolean theory of finite types. 

    - for finite type, boolean reflection can be extended to quantifiers
    - getting closer to classical logic!

#<div>#
*)

Lemma iforall (n : nat) : [forall x: 'I_n, x < n].
Proof. 
apply/forallP.
rewrite /=.
move=> x.
exact: ltn_ord.
Qed.

Lemma iexists  (n : nat) : (n == 0) || [exists x: 'I_n, x == 0 :> nat].
Proof.
case: n.
  by [].
move=> n.
rewrite /=. (* optional, try removing this line. *)
apply/existsP.
pose H : 0 < n.+1 := isT. (* use of small scale reflection. *)
pose x := Ordinal H.
exists x.
by [].  (* mention function ord0. *)
Qed.

(** 
#</div>#
** Note
    - Small scale reflection is used in several places here.
    - The equality in [inord_val] is in type ['I_n.+1]
#<div>#
*)

(** 
#</div>#
#</div>#
----
#<div class="slide">#
  ** Selecting an element
    - pick selects an element that has a given property
    - pickP triggers the reflection
#<div>#
*)
Check pick.

Definition izero n (x : 'I_n) := odflt x [pick i : 'I_n | i == 0 :> nat].

Check izero.

Lemma izero_def n (x : 'I_n.+1) : izero x == 0 :> nat.
Proof.
rewrite /izero.
case: pickP.
  rewrite /=.
  by [].
rewrite /=.
move=> H.
have := H (Ordinal (isT : 0 < n.+1)).
rewrite /=.
by [].
Qed.

(**
#</div>#
#</div>#
----
#<div class="slide">#
  ** Building finite types
    - The property of finiteness is inherited through a large variety of
      type constructors
    - For instance, when constructing a cartesian product of finite types
    - For functions there is an explicit construction [ffun x => body]
#<div>#
*)
Check [finType of ('I_3 * 'I_4)%type].
Fail Check [finType of ('I_3 * nat)%type].

Lemma ipair : [forall x : 'I_3 * 'I_4, x.1 * x.2 < 12].
Proof.
apply/forallP.
rewrite /=.
case.
rewrite /=.
move=> a b.
have H := ltn_mul.
have -> : 12 = 3 * 4 by [].
apply: H.
  by [].
by [].
Qed.

Check [finType of {ffun 'I_3 -> 'I_4}].
Fail Check [finType of ('I_3 -> 'I_4)].

Lemma ifun : [exists f : {ffun 'I_3 -> 'I_4}, forall x, f x == x :> nat].
Proof.
apply/existsP.
rewrite /=.
have H : forall n x, x < n -> x < n.+1.
  move=> n x H.
  rewrite ltnS.
  by rewrite ltnW.
exists [ffun x : 'I_3 => Ordinal (H 3 x (ltn_ord x))].
apply/forallP.
move=> x.
have ffunE' := ffunE.
rewrite ffunE'.
rewrite /=.
by [].
Qed.

(** 
#</div>#
** Note
    - Equipping an arbitrary type that is provably finite with
      the [finType] structure will be done in a later lesson
#<div>#
*)Inductive forest_monster :=
  Lion | Tiger | Bear.

Fail Check [finType of forest_monster].

(**
#</div>#
#</div>#
   ----
   ----
#<div class="slide">#
  ** Big operators
    - Big operators provide a library to manipulate iterations in math-comp
    - this is an encapsulation of the fold function
 #<div>#
*)
Section Illustrate_fold.

Definition f (x : nat) := 2 * x.
Definition g x y := x + y.
Definition r := [::1; 2; 3].

Lemma bfold : foldr (fun val res => g (f val) res) 0 r = 12.
Proof.
rewrite /=.
rewrite /g.
by [].
Qed.

End Illustrate_fold.

(**
#</div>#
#</div>#
----
#<div class="slide">#
   ** Notation

    - iteration is provided by the \big notation
    - the basic operation is on list
    - special notations are introduced for usual case (\sum, \prod, \bigcap ..) 
#<div>#
*)
Lemma bfoldl : \big[addn/0]_(i <- [::1; 2; 3]) i.*2 = 12.
Proof.
rewrite big_cons.
rewrite big_cons.
rewrite big_cons.
rewrite big_nil.
by [].
Qed.

Lemma bfoldlm : \big[muln/1]_(i <- [::1; 2; 3]) i.*2 = 48.
Proof.
rewrite big_cons.
rewrite big_cons.
rewrite big_cons.
rewrite big_nil.
by [].
Qed.

(**
#</div>#
#</div>#
----
#<div class="slide">#
   ** Range 
    - different ranges are provided
#<div>#
*)
Lemma bfoldl1 : \sum_(1 <= i < 4) i.*2 = 12.
Proof.
have big_ltn' := big_ltn.
have big_geq' := big_geq.
rewrite big_ltn.
  rewrite big_ltn.
    rewrite big_ltn.
      rewrite big_geq.
        by [].
      by [].
    by [].
  by [].
by [].
Qed.

Lemma bfoldl2 : \sum_(i < 4) i.*2 = 12.
Proof.
rewrite big_ord_recl.
rewrite /=.
rewrite big_ord_recl.
rewrite /=.
rewrite /bump.
rewrite big_ord_recl.
rewrite big_ord_recl.
rewrite big_ord0.
by [].
Qed.

Lemma bfoldl3 : \sum_(i : 'I_4) i.*2 = 12.
Proof.
exact: bfoldl2.
Qed.

(**
#</div>#
#</div>#
----
#<div class="slide">#
   ** Filtering 
    - it is possible to filter elements from the range 
#<div>#
*)
Lemma bfoldl4 : \sum_(i <- [::1; 2; 3; 4; 5; 6] | ~~ odd i) i = 12.
Proof.
have big_pred0' := big_pred0.
have big_hasC' := big_hasC.
pose x :=  \sum_(i < 8 | ~~ odd i) i.
pose y :=  \sum_(0 <= i < 8 | ~~ odd i) i.
rewrite big_cons.
rewrite /=.
rewrite big_cons.
rewrite /=.
rewrite big_cons.
rewrite /=.
rewrite big_cons.
rewrite /=.
rewrite big_cons.
rewrite /=.
rewrite big_cons.
rewrite /=.
rewrite big_nil.
by [].
Qed.

(**
#</div>#
#</div>#
----
#<div class="slide">#
   ** Switching range
    - it is possible to change representation (big_nth, big_mkord).
#<div>#
*)
Lemma bswitch :  \sum_(i <- [::1; 2; 3]) i.*2 =
                 \sum_(i < 3) (nth 0 [::1; 2; 3] i).*2.
Proof.
have big_nth' := big_nth.
rewrite (big_nth 0).
rewrite /=.
have big_mkord' := big_mkord.
rewrite big_mkord.
by [].
Qed.

(**
#</div>#
#</div>#
----
#<div class="slide">#
  ** Big operators and equality
    - one can exchange function and/or predicate
 #<div>#
*)
Lemma beql : 
  \sum_(i < 4 | odd i || ~~ odd i) i.*2 =  \sum_(i < 4) i.*2.
Proof.
have eq_bigl' := eq_bigl.
apply: eq_bigl.
rewrite /=.
move=> u.
by rewrite orbN.
Qed.

Lemma beqr : 
  \sum_(i < 4) i.*2 = \sum_(i < 4) (i + i).
Proof.
have eq_bigr' := eq_bigr.
apply: eq_bigr.
rewrite /=.
move=> u _.
rewrite addnn.
by [].
Qed.

Lemma beq : 
  \sum_(i < 4 | odd i || ~~ odd i) i.*2 = \sum_(i < 4) (i + i).
Proof.
have eq_big' := eq_big.
apply: eq_big; rewrite /=.
  move=> e.
  by apply: orbN.
move=> i Hi.
rewrite addnn.
by [].
Qed.

(**
#</div>#
#</div>#
----
#<div class="slide">#
  ** Monoid structure
    - one can use associativity to reorganize the bigop
 #<div>#
*)
Lemma bmon1 : \sum_(i <- [::1; 2; 3]) i.*2 = 12.
Proof.
have H := big_cat.
have -> : [:: 1; 2; 3] = [::1] ++ [::2; 3].
  by [].
rewrite big_cat.
rewrite /=.
rewrite big_cons.
rewrite big_nil.
rewrite !big_cons big_nil.
by [].
Qed.

Lemma bmon2 : \sum_(1 <= i < 4) i.*2 = 12.
Proof.
have big_cat_nat' := big_cat_nat.
rewrite (big_cat_nat _ _ _ (isT: 1 <= 2)).
  rewrite /=.
  rewrite big_ltn //=.
  rewrite big_geq //.
  by rewrite 2?big_ltn //= big_geq.
by [].
Qed.

Lemma bmon3 : \sum_(i < 4) i.*2 = 12.
Proof.
have big_ord_recl' := big_ord_recl.
have big_ord_recr' := big_ord_recr.
(* Note the added assumption on the operator in big_ord_recr *)
rewrite big_ord_recr.
rewrite /=.
rewrite !big_ord_recr //=.
rewrite big_ord0.
by [].
Qed.

Lemma bmon4 : \sum_(i < 8 | ~~ odd i) i = 12.
Proof.
have big_mkcond' := big_mkcond.
rewrite big_mkcond.
rewrite /=.
rewrite !big_ord_recr /=.
rewrite big_ord0.
by [].
Qed.

(**
#</div>#
#</div>#
----
#<div class="slide">#
  ** Abelian Monoid structure
    - one can use communitativity to massage the bigop
 #<div>#
*)

Lemma bab : \sum_(i < 4) i.*2 = 12.
Proof.
have bigD1' := bigD1.
pose x := Ordinal (isT: 2 < 4).
rewrite (bigD1 x).
  rewrite /=.
  rewrite big_mkcond /=.
  rewrite !big_ord_recr /= big_ord0.
  by [].
by []. (* This is about proving that the (hidden) filter predicate
   of the big operation is satisfied for x *)
Qed.

Lemma bab1 : \sum_(i < 4) (i + i.*2) = 18.
Proof.
have big_split' := big_split.
rewrite big_split /=.
rewrite bab.
rewrite !big_ord_recr big_ord0 /=.
by [].
Qed.

Lemma bab2 : \sum_(i < 3) \sum_(j < 4) (i + j) =
                 \sum_(i < 4) \sum_(j < 3) (i + j).
Proof.
have exchange_big' := exchange_big.
have reindex_inj' := reindex_inj.
rewrite exchange_big.
rewrite /=.
apply: eq_bigr.
move=> i _.
apply: eq_bigr.
move=> j _.
by rewrite addnC.
Qed.

(**
#</div>#
#</div>#
----
#<div class="slide">#
  ** Distributivity
    - one can exchange sum and product
 #<div>#
*)
Lemma bab3 : \sum_(i < 4) (2 * i) = 2 * \sum_(i < 4) i.
Proof.
have big_distrr' := big_distrr.
by rewrite big_distrr.
Qed.

Lemma bab4 : 
  (\prod_(i < 3) \sum_(j < 4) (i ^ j)) = 
  \sum_(f : {ffun 'I_3 -> 'I_4}) \prod_(i < 3) (i ^ (f i)).
Proof.
have big_distr_big' := big_distr_big.
rewrite  (big_distr_big ord0).
rewrite /=.
apply: eq_bigl.
move=> f.
rewrite /=.
apply/forallP.
rewrite /=.
by [].
Qed.

(**
#</div>#
#</div>#
----
#<div class="slide">#
  ** Property, Relation and Morphism
 #<div>#
*)
Lemma bap n : ~~ odd (\sum_(i < n) i.*2). 
Proof.
have big_ind' := big_ind.
have big_ind2' := big_ind2.
have big_morph' := big_morph.
elim/big_ind: _.
- by [].
- move=> x y.
  rewrite oddD.
  case: odd.
     by [].
  by [].
move=> i _.
by rewrite odd_double.
Qed.
(**
#</div>#
#</div>#
*)


