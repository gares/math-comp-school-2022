From elpi Require Import elpi.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From mathcomp Require ssralg ssrnum zmodp. (* all_algebra *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** #<div class='slide'>#
* The algebra library

 - This is a central part of the mathematical components library.
 - This library register a various range of (mathematical) structures.
  - types with decidable equality: [eqType]
  - types with a finite number of elements: [finType]
  - finite groups: [finGroupType]
  - abelian (not possibly finite) groups: [zmodType]
  - rings: [ringType]
  - rings with invertible elements: [unitRingType]
  - commutative rings: [comRingType]
  - integral domains: [idomainType]
  - fields: [fieldType]
  - left modules: [lmodType]
  - left algebra: [lalgType]
  - algebra: [algType]
  - finite dimensional vector spaces: [vectType]
  - ...

- These structures share operators: e.g. the operator [(_ + _)],
  introduced for abelian groups ([zmodType]), is also available for all
  the structures that inherit it (rings, domains, fields, etc...)

- All of these structures are "discrete": they all have decidable
  equality: the operator [(_ == _)] is available on all of them.

- #<a href="http://www-sop.inria.fr/teams/marelle/advanced-coq-16/mc_hieralg.pdf">  Here is a picture of the begining of the hierarchy</a>#

  Extensive documentation in the header of:
 - #<a href="https://math-comp.github.io/htmldoc_2_0_alpha1/mathcomp.algebra.ssralg.html">ssralg</a>#
 - #<a href="https://math-comp.github.io/htmldoc_2_0_alpha1/mathcomp.algebra.ssrnum.html">ssrnum</a>#

- In addition there are structures for maps (additive morphisms, ring
  morphisms, etc...), and substructures (subgroup, subsemiring, subring,
  subfield, etc...)

- From math-comp 2.0 alpha, structures are generated by the external tool
  #<a href="https://github.com/math-comp/hierarchy-builder/">Hierarchy Builder</a>#

#</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#

* Roadmap for the lesson:
 - introduction of the general definition pattern for algebraic structures
 - instantiation of a structure in the library
 - exploration of the theory provided by this structure and naming
   conventions
 - creation of a algebraic substructure and predicate and their use
#</div>#
*)
(** -------------------------------------------- *)
(** #<div class='slide'>#
* Defining a mathematical structure in Coq.

This is how mathematical structures are defined in the library.
We define structures as sets of "mixins"
(they look more like "traits" in object oriented slang)
#<div>#
*)
Module AlgebraicStructuresDemo.

HB.mixin Record hasAbsorbingOp T := {
(* symbols: constants and operators *)
  c    : T;
  op   : T -> T -> T;

(* axioms: properties on the symbols *)
  opxc : forall x, op x c = c;
  opC : forall x y, op x y = op y x
}.
(* Absorbing operator structure *)
HB.structure Definition AbsorbingOp := {T of hasAbsorbingOp T}.

HB.about AbsorbingOp.
(*
HB: AbsorbingOp.type is a structure (from "(stdin)", line 16)
HB: AbsorbingOp.type characterizing operations and axioms are:
    - opC
    - opxc
    - op
    - c
HB: AbsorbingOp is a factory for the following mixins:
    - hasAbsorbingOp (* new, not from inheritance *)
*)

(* Notations for the symbols which are immediately available after the definition of the structure*)
Notation "x * y" := (op x y).
Notation "0" := c.

(* Once this is done, we can write the theory associated to this structure *)
Section my_struct_theory.

Variable s : AbsorbingOp.type.

(* Theory of the structure *)
Lemma opcx (x : s) : c * x = c.
Proof. by rewrite opC opxc. Qed.

End my_struct_theory.
(** #</div></div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#
* Defining a mathematical hierarchy in Coq.

Adding a structure is adding more mixins and packaging them into structures.
#<div>#
*)
HB.mixin Record hasFunnyPred T of hasAbsorbingOp T := {
(* symbols: constants and operators *)
  pr   : pred T;
(* axioms: properties on the symbols *)
  pr_xc : forall x, pr (x * c)
}.
HB.structure Definition Funny :=
  {T of AbsorbingOp T & hasFunnyPred T}.

HB.about Funny.
(*#
HB: Funny.type is a structure (from "(stdin)", line 52)
HB: Funny.type characterizing operations and axioms are:
    - pr_xc
    - pr
HB: Funny is a factory for the following mixins:
    - hasAbsorbingOp
    - hasFunnyPred (* new, not from inheritance *)
HB: Funny inherits from:
    - AbsorbingOp
#*)

Section my_struct2_theory.

Variable s : Funny.type.

(* [pr] becomes immediately available *)
Lemma pr_c : pr (c : s).
Proof. by rewrite -(opcx c) pr_xc. Qed.

Lemma pr_cx (x : s) : pr (c * x).
Proof. by rewrite opC pr_xc. Qed.

End my_struct2_theory.
(** #</div></div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#
* Adding alternative definitions of structures to the hierarchy.

We need a factory and builders
#<div># *)
HB.factory Record hasPredOnC T of hasAbsorbingOp T := {
(* symbols: constants and operators *)
  pr   : pred T;
(* axioms: properties on the symbols *)
  pr_c : pr c
}.
HB.builders Context T of hasPredOnC T.
Lemma pr_xc x : pr (x * c). Proof. by rewrite opxc pr_c. Qed.
(* this is a particular case of instanciation, see next section *)
HB.instance Definition _ := hasFunnyPred.Build T pr_xc.
HB.end.

Fail HB.structure Definition already_defined :=
  {T of hasAbsorbingOp T & hasPredOnC T}.

End AlgebraicStructuresDemo.
(** #</div><div>#

Hierarchy Builder (HB) now automatically recognizes that [hasPredOnC]
can define a [Funny.type] and only that, hence the failing structure definition.
Now, one can use the factory [hasPredOnC] instead of [hasFunnyPred]
to define a [Funny.type].

#</div></div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#
* Inhabiting the mathematical structures hierarchy.

 - We now show on the example of integers how to instantiate the
   mathematical structures that integers satisfy.

 - In order to minimize the work of the user, the library lets you inhabit
   structures by instanciating mixins and factory, one at a time.
   Each time we want to build structures, we only declare the
   mixin/factory as an [HB.instance].
   One or several structures will be automatically instantiated.

 - We catagorize five different ways to build structures.
   Th three first will be shown here.
   The fourth will be shown in the exercices, and the fifth one won't be shown.

  - using a partially isomorphic structure (and providing the witness).
  - by instanciating just the required mixin from scratch,
  - by instanciating a factory to create one or several structures,
  - by subtyping (in the exercise session),
  - by quotienting (out of scope of the school).

#<div># *)
Module InstantiationInteger.

Import ssralg GRing.Theory.
Local Open Scope ring_scope.

(* one can show the currently loaded hierarchy as follows: *)
HB.graph "hierarchy.dot". (* use e.g. tred hierarchy.dot | xdot - *)
(** #</div></div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#
** First we define [int]

#<div># *)
Variant int : Set := Posz of nat | Negz of nat.
Local Coercion Posz : nat >-> int.

Notation "n %:Z" := (Posz n)
  (at level 2, left associativity, format "n %:Z", only parsing).
(** #</div><div>#

** Equality, countable and choice types, by injection

We provide an injection with explicit partial inverse,
from [int] to [nat + nat], this will be enough to provide the mixins for equality,
countable and choice types.

#</div><div># *)
Definition natsum_of_int (m : int) : nat + nat :=
  match m with Posz p => inl _ p | Negz n => inr _ n end.

Definition int_of_natsum (m : nat + nat) :=
  match m with inl p => Posz p | inr n => Negz n end.

Lemma natsum_of_intK : cancel natsum_of_int int_of_natsum.
Proof. by case. Qed.
(** #</div>#

We create the mixins for equality, countable and choice types from
this injection, and gradually inhabit the hierarchy.

#<div># *)
HB.howto Countable.type.
(* HB: solutions (use 'HB.about F.Build' to see the arguments of each factory F):
    - hasDecEq; hasChoice; isCountable *)

HB.instance Definition _ : hasDecEq int := CanEqMixin natsum_of_intK.
HB.instance Definition _ : hasChoice int := CanChoiceMixin natsum_of_intK.
HB.instance Definition _ : isCountable int := CanCountMixin natsum_of_intK.

(* Advanced way of doing it one go: *)
(* HB.instance Definition _ := Countable.copy int (can_type natsum_of_intK). *)
(** #</div></div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#
** Abelian group structure, from scratch

We now create the abelian group structure of integers (here called
Z-module), from scratch, introducing the operators and proving exactly
the required properties.

#<div># *)
Module intZmod.
Section intZmod.
HB.about GRing.isZmodule.Build.
(*# HB: arguments: GRing.isZmodule.Build V [zero] [opp] [add] addrA addrC add0r addNr
    - V : Type
    - zero : GRing.Zmodule.sort V
    - opp : V -> V
    - add : V -> V -> V
    - addrA : associative +%R
    - addrC : commutative +%R
    - add0r : left_id 0 +%R
    - addNr : left_inverse 0 -%R +%R #*)

Definition addz (m n : int) := match m, n with
  | Posz m', Posz n' => Posz (m' + n')
  | Negz m', Negz n' => Negz (m' + n').+1
  | Posz m', Negz n' => if n' < m' then Posz (m' - n'.+1)
                        else Negz (n' - m')
  | Negz n', Posz m' => if n' < m' then Posz (m' - n'.+1)
                          else Negz (n' - m') end.
Definition oppz m := match m with
    | Posz n => if n is (n'.+1)%N then Negz n' else Posz 0
    | Negz n => Posz (n.+1)%N end.
Lemma addzC : commutative addz. Admitted.
Lemma add0z : left_id (Posz 0) addz. Admitted.
Lemma oppzK : involutive oppz. Admitted.
Lemma addzA : associative addz. Admitted.
Lemma addNz : left_inverse (Posz 0) oppz addz. Admitted.

Definition Mixin := GRing.isZmodule.Build int addzA addzC add0z addNz.
End intZmod.
End intZmod.
(* We declare the instance *)
HB.instance Definition _ := intZmod.Mixin.
(*# We can check that int can be converted to a [zmodType] #*)
Check (int : zmodType). (** #</div><div>#

Remark: we may develop here a piece of abelian group theory which is
specific to the theory of integers. E.g.
#</div><div># *)Lemma PoszD : {morph Posz : n m / (n + m)%N >-> n + m}.
Proof. by []. Qed. (** #</div></div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#
*** Ring and Commutative ring structure, the stronger the better

This time, we will build directly a rich commutative ring factory first
and use it to instanciate both the ring structure and the commutative
ring struture at the same time. This is not only an economy
of space, but an economy of proofs, since the
commutativity property reduces the number of ring axioms to prove.

#<div>#
*)
Module intRing.
Section intRing.

HB.howto comRingType.
(*# HB: no solution found at depth 3 looking at depth 4
HB: solutions (use 'HB.about F.Build' to see the arguments of each factory F):
    - hasDecEq; hasChoice; GRing.isRing; GRing.Ring_hasCommutativeMul
    - hasDecEq; hasChoice; GRing.isZmodule; GRing.Zmodule_isComRing #*)

HB.about GRing.Zmodule_isComRing.Build.
(*# HB: arguments: GRing.Zmodule_isComRing.Build R [one] [mul] mulrA mulrC mul1r mulrDl oner_neq0
    - R : Type
    - one : R
    - mul : R -> R -> R
    - mulrA : associative mul
    - mulrC : commutative mul
    - mul1r : left_id one mul
    - mulrDl : left_distributive mul +%R
    - oner_neq0 : is_true (one != 0) #*)

Definition mulz (m n : int) := match m, n with
    | Posz m', Posz n' => (m' * n')%N%:Z
    | Negz m', Negz n' => (m'.+1%N * n'.+1%N)%N%:Z
    | Posz m', Negz n' => - (m' * (n'.+1%N))%N%:Z
    | Negz n', Posz m' => - (m' * (n'.+1%N))%N%:Z end.
Lemma mulzA : associative mulz. Admitted.
Lemma mulzC : commutative mulz. Admitted.
Lemma mul1z : left_id (Posz 1) mulz. Admitted.
Lemma mulz_addl : left_distributive mulz (+%R). Admitted.
Lemma onez_neq0 : (Posz 1) != 0. Proof. by []. Qed.

Definition comMixin := GRing.Zmodule_isComRing.Build int mulzA mulzC mul1z mulz_addl onez_neq0.
End intRing.
End intRing.
(* We declare the instance *)
HB.instance Definition _ := intRing.comMixin.
(*# We can check that [int] can be converted to a [ringType] and a [comRingType] #*)
Check (int : ringType).
Check (int : comRingType).

End InstantiationInteger. (** #</div># *)
(** #</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#
* Other structures and instances
#<div>#
*)
Module OtherStructures.
Import ssralg GRing.Theory.
Local Open Scope ring_scope.
(**
#</div>#
** About other algebraic structures:

- read the documentation of  #<a href="https://math-comp.github.io/htmldoc_2_0_alpha1/mathcomp.algebra.ssralg.html">ssralg</a># and #<a href="https://math-comp.github.io/htmldoc_2_0_alpha1/mathcomp.algebra.ssrnum.html">ssrnum</a># (algebraic structures with order and absolute value)

- Canonical instances in the library are:
 - integers ([int]) (forms an integral domain)
 - rationals ([rat]) (forms an archimedian field)
 - algebraic numbers ([algC]) (forms an algebraically closed field)
 - polynomials [{poly R}] (forms an integral domain under sufficient hypothesis on the base ring)
 - matrices ['M[R]_(m, n)] (forms a module / a finite dimension vector space)
 - square matrices ['M[R]_n] (forms an algebra, if [n := m.+1])

** Group theory (not in this course):

- see fingroup, perm, action, ...

** Structures for morphisms:
#<div>#
*)
Search "linear" in ssralg.

Search "raddf" in ssralg.

Search "rmorph" in ssralg.

HB.about GRing.RMorphism.
(** #</div>
** Structure preserving predicates:
#<div># *)
Print GRing.subring_closed.
Print GRing.subr_2closed.
Print GRing.mulr_2closed.

Search "rpred" in ssralg.

End OtherStructures.
(** #</div></div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#
* Naming conventions.

The two most important things to get your way out of a situation:
 - Knowing your math
 - Searching the library for what you think you know

For that you have the ssreflect Search command. To use its full power, one should combine seach by identifier (Coq definition), pattern (partial terms) and name (a string contained in the name of the theorem).

The two first methods are straightforward to use (except if you instanciate your patterns more than necessary), but searching by name requires to be aware of naming conventions.

#</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#
** Names in the library are usually obeying one of following the convention

 - #<pre>(condition_)?mainSymbol_suffixes</pre>#
 - #<pre>mainSymbol_suffixes(_condition)?</pre>#

Or in the presence of a property denoted by a nary or unary predicate:
 - #<pre>naryPredicate_mainSymbol+</pre>#
 - #<pre>mainSymbol_unaryPredicate</pre>#

** Where :

 - "mainSymbol" is the most meaningful part of the lemma. It generally
   is the head symbol of the right-hand side of an equation or the
   head symbol of a theorem. It can also simply be the main object of
   study, head symbol or not. It is usually either

  - one of the main symbols of the theory at hand. For example, it will be #<code>opp</code>#, #<code>add</code>#, #<code>mul</code>#, etc...

  - or a special "canonical" operation, such as a ring morphism or a
    subtype predicate. e.g. #<code>linear</code>#, #<code>raddf</code>#, #<code>rmorph</code>#, #<code>rpred</code>#, etc ...

 - "condition" is used when the lemma applies under some hypothesis.

 - "suffixes" are there to refine what shape and/or what other symbols  the lemma has. It can either be the name of a symbol ("add", "mul",  etc...), or the (short) name of a predicate ("#<code>inj</code>#" for "#<code>injectivity</code>#", "#<code>id</code>#" for "identity", ...) or an abbreviation.

Abbreviations are in the header of the file which introduce them. We list here the main abbreviations.

  - A -- associativity, as in #<code>andbA : associative andb.</code>#
  - AC -- right commutativity.
  - ACA -- self-interchange (inner commutativity), e.g.,
        #<code>orbACA : (a || b) || (c || d) = (a || c) || (b || d).</code>#
  - b -- a boolean argument, as in #<code>andbb : idempotent andb.</code>#
  - C -- commutativity, as in #<code>andbC : commutative andb</code>#,
    or predicate complement, as in #<code>predC.</code>#
  - CA -- left commutativity.
  - D -- predicate difference, as in #<code>predD.</code>#
  - E -- elimination, as in #<code>negbFE : ~~ b = false -> b</code>#.
  - F or f -- boolean false, as in #<code>andbF : b && false = false.</code>#
  - I -- left/right injectivity, as in #<code>addbI : right_injective addb</code># or predicate  intersection, as in #<code>predI.</code>#
  - l -- a left-hand operation, as #<code>andb_orl : left_distributive andb orb.</code>#
  - N or n -- boolean negation, as in #<code>andbN : a && (~~ a) = false.</code>#
  - n -- alternatively, it is a natural number argument
  - P -- a characteristic property, often a reflection lemma, as in
     #<code>andP : reflect (a /\ b) (a && b)</code>#.
  - r -- a right-hand operation, as #<code>orb_andr : right_distributive orb andb.</code>#
      -- alternatively, it is a ring argument
  - T or t -- boolean truth, as in #<code>andbT: right_id true andb.</code>#
  - U -- predicate union, as in #<code>predU</code>#.
  - W -- weakening, as in #<code>in1W : {in D, forall x, P} -> forall x, P.</code>#
  - 0 -- ring 0, as in #<code>addr0 : x + 0 = x.</code>#
  - 1 -- ring 1, as in #<code>mulr1 : x * 1 = x.</code>#
  - D -- ring addition, as in #<code>linearD : f (u + v) = f u + f v.</code>#
  - B -- ring subtraction, as in #<code>opprB : - (x - y) = y - x.</code>#
  - M -- ring multiplication, as in #<code>invfM : (x * y)^-1 = x^-1 * y^-1.</code>#
  - Mn -- ring by nat multiplication, as in #<code>raddfMn : f (x *+ n) = f x *+ n.</code>#
  - mx -- a matrix argument
  - N -- ring opposite, as in #<code>mulNr : (- x) * y = - (x * y).</code>#
  - V -- ring inverse, as in #<code>mulVr : x^-1 * x = 1.</code>#
  - X -- ring exponentiation, as in #<code>rmorphX : f (x ^+ n) = f x ^+ n.</code>#
  - Z -- (left) module scaling, as in #<code>linearZ : f (a *: v)  = s *: f v.</code>#
  - z -- a int operation

** My most used search pattern

#<pre>Search "prefix" "suffix"* (symbol|pattern)* in library.</pre>#

** Examples
#<div>#
*)
Module Conventions.
Import ssralg ssrnum GRing.Theory.
Local Open Scope ring_scope.

Search *%R "A" in GRing.Theory.

Search "unit" in ssralg.

Search "inj" in ssralg.

Search "rmorph" "M" in ssralg.

Search "rpred" "D" in ssralg.

End Conventions.
(** #</div></div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#
** Revisiting an exercise from session 2

Instead of reasonning using [(_ %| _)] and [(_ %% _)], we switch to ['Z_p]
#<div># *)
Section ReasoningModuloInZp.
Import ssralg zmodp GRing.Theory.
Local Open Scope ring_scope.

Lemma pred_Zp k : 1 < k -> (k.-1%:R = - 1 :> 'Z_k)%R.
Proof. by case: k => // k k_gt0; rewrite -subn1 natrB ?char_Zp ?sub0r. Qed.

Lemma dvd_exp_odd a k : 0 < a -> odd k -> (a.+1 %| (a ^ k).+1).
Proof.
move=> aP kO; apply/eqP; rewrite -val_Zp_nat//.
by rewrite -natr1 natrX pred_Zp// -signr_odd kO addNr.
Qed.

End ReasoningModuloInZp.
(** #</div></div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#
* More about structure preserving predicates.

There is a notion of subobject for a few algebraic concepts.

#<div>#
**)
Import ssralg GRing.Theory.
Fail HB.howto GRing.SubringClosed.type. (* alpha release sorry *)
HB.howto GRing.SubringClosed.type_.
(* HB: solutions (use 'HB.about F.Build' to see the arguments of each factory F):
    - GRing.isSubringClosed *)
HB.about GRing.isSubringClosed.Build.
(* HB: arguments: GRing.isSubringClosed.Build R S subring_closed_subproof
    - R : ringType
    - S : R -> bool
    - subring_closed_subproof : subring_closed S *)
Print subring_closed.
(* Notation subring_closed := GRing.subring_closed *)
Print GRing.subring_closed.
(* GRing.subring_closed =
fun (R : ringType) (S : {pred R}) => [/\ 1%R \in S, GRing.subr_2closed S & GRing.mulr_2closed S]
     : forall R : ringType, {pred R} -> Prop *)
(** #</div>

See the [hierarchy.dot], use [HB.about], [HB.howto] or read documentation headers to discover other substructure preserving predicates.

</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#
 * A reminder on subtyping.

 - In Coq, #<code>sT := {x : T | P x}</code># is a way to form a
  sigma-type. We say it is a #<b>subtype</b># if there is only one
  element it #<code>sT</code># for each element in
  #<code>T</code>#. This happens when #<code>P</code># is a boolean
  predicate. Another way to form a subtype is to create a record :
  #<code>Record sT := ST {x : T; px : P x}</code>#.

 - In mathcomp, to deal with subtypes independently from how they are
   formed, we have a structure.
#<div>#
*)
HB.about Sub.
HB.about isSub.

(* In essence *)
Module SubType.
Section SubType.
Variables (T : Type) (P : pred T).
Structure subType : Type := SubType {
  sub_sort :> Type;
  val : sub_sort -> T;
  Sub : forall x, P x -> sub_sort;
  (* elimination rule for sub_sort *)
  _ : forall K (_ : forall x Px, K (@Sub x Px)) u, K u;
  _ : forall x Px, val (@Sub x Px) = x
}.
End SubType.
End SubType.
(**
#</div><div>#
 - The most important operators to know on subtypes are
  #<code>val : sT -> T</code>#, #<code>insub : T -> option sT</code># and
  #<code>insubd : sT -> T -> sT</code>#.

- And the most important theorems to know are
  #<code>val_inj, val_eqE, val_insubd, insubdK</code># and #<code>insub</code>#

#</div><div>#
*)
About val_inj.
About val_eqE.
About insubK.
About val_insubd.
About insubdK.
(** #</div></div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#

* Substructures

Substructures are subtypes that happen to have the same structure as their base type.

There are special factories to instantiate them easily.

#<div>#
**)
Import ssralg GRing.Theory.
HB.howto GRing.SubRing.type.
(*#
HB: no solution found at depth 3 looking at depth 4
HB: solutions (use 'HB.about F.Build' to see the arguments of each factory F):
    - hasDecEq; isSub; hasChoice; GRing.SubChoice_isSubRing
#*)

HB.about GRing.SubChoice_isSubRing.
(*#
HB: GRing.SubChoice_isSubRing is a factory (from "./ssralg.v", line 5073)
HB: GRing.SubChoice_isSubRing operations and axioms are:
    - subring_closed_subproof
HB: GRing.SubChoice_isSubRing requires the following mixins:
    - hasChoice
    - hasDecEq
    - isSub
HB: GRing.SubChoice_isSubRing provides the following mixins:
    - GRing.Zmodule_isRing
    - GRing.isSubRing
    - GRing.isZmodule
    - GRing.isSubZmodule
#*)
HB.about GRing.SubChoice_isSubRing.Build.
(*#
HB: arguments: GRing.SubChoice_isSubRing.Build R S U subring_closed_subproof
    - R : ringType
    - S : pred R
    - U : Type
    - subring_closed_subproof : subring_closed S
#*)
(** #</div># 

Moreover, when a predicate is declared as a structure preserving predicate, we can use it to declare a substructure automatically (see exercise session).

*)
(** #</div># *)
