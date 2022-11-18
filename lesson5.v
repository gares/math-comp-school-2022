From mathcomp Require Import all_ssreflect.
From mathcomp Require all_algebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** #<div class='slide'>#
* The algebra library

 - This is a central part of the mathematical components library.
 - This library register a various range of (mathematical) structures.
  - types with decidable equality: eqType
  - types with a finite number of elements: finType
  - finite groups: finGroupType
  - abelian (not possibly finite) groups: zmodType
  - rings: ringType
  - rings with invertible elements: unitRingType
  - commutative rings: comRingType
  - integral domains: idomainType
  - fields: fieldType
  - left modules: lmodType
  - left algebra: lalgType
  - algebra: algType
  - finite dimensional vector spaces: vectType
  - ...

- Some of these structures share operators: e.g. the operator (_ + _),
  introduced for abelian groups (zmodType), is also available for all
  the structures that require it (rings, domains, fields, etc...)

- All of these structures are discrete: they all have decidable
  equality: the operator (_ == _) is available on all of them.

- #<a href="http://www-sop.inria.fr/teams/marelle/advanced-coq-16/mc_hieralg.pdf">  Here is a picture of the begining of the hierarchy</a>#

  Extensive documentation in the header of:
 - #<a href="http://math-comp.github.io/math-comp/htmldoc/mathcomp.algebra.ssralg.html">ssralg</a>#
 - #<a href="http://math-comp.github.io/math-comp/htmldoc/mathcomp.algebra.ssrnum.html">ssrnum</a>#

- In addition there are structures for maps (additive morphisms, ring
  morphisms, etc...), and substructures (subgroup, subsemiring, subring,
  subfield, etc...)
#</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#

* Roadmap for the lesson:
 - introduction of the general definition pattern for algebraic structures
 - instantiation of a structure in the library
 - exploration of the theory provided by this structure and naming
   conventions
 - creation of a subalgebraic structure predicate and use
#<div>#
*)
Module AlgebraicStructures.
(**
#</div>#
#</div>#
*)
(** -------------------------------------------- *)
(** #<div class='slide'>#
* Defining a mathematical structure in Coq.

This is how mathematical structures are defined in the library.
Unless you need to add a new mathematical structure to the library,
you will only need to read this.
#<div>#
*)
Structure my_struct := My_struct {
(* domain/carrier/sort of the structure *)
  dom  : Type;

(* symbols: constants and operators *)
  c    : dom;
  op   : dom -> dom -> dom;

(* axioms: properties on the symbols *)
  opxc : forall x, op x c = c;
  opC : forall x y, op x y = op y x}.

(* Notations and modifiers for the symbols *)
Arguments op {m} x y.
Arguments c {m}.
Notation "x * y" := (op x y).

Section my_struct_theory.

Variable s : my_struct.

(* Theory of the structure *)
Lemma opcx (x : dom s) : c * x = c.
Proof. by rewrite opC opxc. Qed.

End my_struct_theory.

End AlgebraicStructures.
(**
#</div>#

This packaging is very elementary, and the mathematical components
library uses a refinement of this.

#</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#

* Packaging mathematical structures

We briefly explain how to do inheritance with two structures. This is
another simplified version of what happens in the library.  The
complete process is described in #<a href="https://hal.inria.fr/inria-00368403v1/document">Packaging Mathematical Structures (Garillot, Gonthier, Mahboubi, Rideau)</a># and in the #<a href="http://math-comp.github.io/mcb">Mathematical Components Book</a>#.

#<div>#
*)
Section AlgebraicStructuresInheritance.

Record my_mixin1 dom := My_mixin1 {
(* symbols: constants and operators *)
  my_c    : dom;
  my_op   : dom -> dom -> dom;
(* axioms: properties on the symbols *)
  my_opxc : forall x, my_op x my_c = my_c;
  my_opC : forall x y, my_op x y = my_op y x}.

Definition my_class1 := my_mixin1.

Structure my_struct1 := My_struct1 {
(* domain/carrier/sort of the structure *)
  dom1 :> Type;
  class1 : my_mixin1 dom1}.

Definition op {s : my_struct1} := my_op (class1 s).
Definition c {s : my_struct1} := my_c (class1 s).
Notation "x * y" := (op x y).

Record my_mixin2 (dom : my_struct1) := My_mixin2 {
(* symbols: constants and operators *)
  my_pred   : pred dom;
(* axioms: properties on the symbols *)
  my_predc : forall x, my_pred (op c x)}.

Record my_class2 dom := My_class2 {
  base2 :> my_class1 dom;
  mixin2 :> my_mixin2 (@My_struct1 dom base2)}.

Structure my_struct2 := My_struct2 {
  dom2  :> Type;
  class2 : my_class2 dom2}.

Definition pr {s : my_struct2} := my_pred (class2 s).

Canonical my_struct1_2 (s : my_struct2) : my_struct1 :=
  @My_struct1 (dom2 s) (class2 s : my_class1 _).

Section my_struct1_theory.

Variable s : my_struct1.

Lemma opC (x y : s) : x * y = y * x.
Proof. by case: s x y => ? []. Qed.

Lemma opxc (x : s) : x * c = c.
Proof. by case: s x => ? []. Qed.

(* Theory of the structure *)
Lemma opcx (x : s) : c * x = c.
Proof. by rewrite opC opxc. Qed.

End my_struct1_theory.

Section my_struct2_theory.

Variable s : my_struct2.

Lemma pr_xc (x : s) : pr (c * x).
Proof. by case: s x => ? [? []]. Qed.

Lemma pr_c : pr (c : s).
Proof. by rewrite -(opcx c) pr_xc. Qed.

End my_struct2_theory.

End AlgebraicStructuresInheritance.
(**
#</div>#
#</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#
* Inhabiting the mathematical structures hierarchy.

 - We now show on the example of integers how to instantiate the
   mathematical structures that integers satisfy.

 - In order to minimize the work of the user, the library lets you inhabit
   sub-structures by providing one mixin at a time.
   The general pattern is to build the mixin of a
   structure, declare the canonical structure associated with it and
   go on with creating the next mixin and creating the new
   structure. Each time we build a new structure, we provide only the
   mixin, as the class can be inferred from the previous canonical
   structures.

 - We now show three different ways to build mixins here and an
   additional fourth will be shown in the exercices

  - using a reference structure (by injection or partial isomorphism),
  - building the required mixin from scratch (just provide the contents of the mixin yourself),
  - building a more informative mixin and using it for a weaker structure (prove a more elaborate property, and deduce the actual mixin from it),
  - by subtyping (in the exercise session).

#<div>#
*)
Module InstantiationInteger.

From mathcomp Require Import ssralg.
Import GRing.Theory.
Local Open Scope ring_scope.
(**
#</div>#
#</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#
** First we define int

#<div>#
*)
CoInductive int : Set := Posz of nat | Negz of nat.
Local Coercion Posz : nat >-> int.

Notation "n %:Z" := (Posz n)
  (at level 2, left associativity, format "n %:Z", only parsing).
(**
#</div>#

** Equality, countable and choice types, by injection

We provide an injection with explicit partial inverse, grom int to nat
+ nat, this will be enough to provide the mixins for equality,
countable and choice types.

#<div>#
*)
Definition natsum_of_int (m : int) : nat + nat :=
  match m with Posz p => inl _ p | Negz n => inr _ n end.

Definition int_of_natsum (m : nat + nat) :=
  match m with inl p => Posz p | inr n => Negz n end.

Lemma natsum_of_intK : cancel natsum_of_int int_of_natsum.
Proof. by case. Qed.
(**
#</div>#

We create the mixins for equality, countable and choice types from
this injection, and gradually inhabit the hierarchy. Try to swap any
of the three blocks to see what happen.

#<div>#
*)
Definition int_eqMixin := CanEqMixin natsum_of_intK.
Canonical int_eqType := EqType int int_eqMixin.

Definition int_choiceMixin := CanChoiceMixin natsum_of_intK.
Canonical int_choiceType := ChoiceType int int_choiceMixin.

Definition int_countMixin := CanCountMixin natsum_of_intK.
Canonical int_countType := CountType int int_countMixin.
(**
#</div>#

#</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#
** Abelian group structure, from scratch

We now create the abelian group structure of integers (here called
Z-module), from scratch, introducing the operators and proving exactly
the required properties.

#<div>#
*)
Module intZmod.
Section intZmod.

Definition addz (m n : int) :=
  match m, n with
    | Posz m', Posz n' => Posz (m' + n')
    | Negz m', Negz n' => Negz (m' + n').+1
    | Posz m', Negz n' => if n' < m' then Posz (m' - n'.+1)
                          else Negz (n' - m')
    | Negz n', Posz m' => if n' < m' then Posz (m' - n'.+1)
                          else Negz (n' - m')
  end.

Definition oppz m := nosimpl
  match m with
    | Posz n => if n is (n'.+1)%N then Negz n' else Posz 0
    | Negz n => Posz (n.+1)%N
  end.

Lemma addzC : commutative addz. Admitted.
Lemma add0z : left_id (Posz 0) addz. Admitted.
Lemma oppzK : involutive oppz. Admitted.
Lemma addzA : associative addz. Admitted.
Lemma addNz : left_inverse (Posz 0) oppz addz. Admitted.

Definition Mixin := ZmodMixin addzA addzC add0z addNz.

End intZmod.
End intZmod.

Canonical int_ZmodType := ZmodType int intZmod.Mixin.
(**
#</div>#

Remark: we may develop here a piece of abelian group theory which is
specific to the theory of integers.

#<div>#
*)
Section intZmoduleTheory.

Lemma PoszD : {morph Posz : n m / (n + m)%N >-> n + m}.
Proof. by []. Qed.

End intZmoduleTheory.
(**
#</div>#

*** Ring and Commutative ring structure, the stronger the better

This time, we will build directly a rich commutative ring mixin first
and use it to instanciate both the ring structure and the commutative
ring struture at the same time. This is not only a structural economy
of space, but a mathematical economy of proofs, since the
commutativity property reduces the number of ring axioms to prove.

#<div>#
*)

Module intRing.
Section intRing.

Definition mulz (m n : int) :=
  match m, n with
    | Posz m', Posz n' => (m' * n')%N%:Z
    | Negz m', Negz n' => (m'.+1%N * n'.+1%N)%N%:Z
    | Posz m', Negz n' => - (m' * (n'.+1%N))%N%:Z
    | Negz n', Posz m' => - (m' * (n'.+1%N))%N%:Z
  end.

Lemma mulzA : associative mulz. Admitted.
Lemma mulzC : commutative mulz. Admitted.
Lemma mul1z : left_id (Posz 1) mulz. Admitted.
Lemma mulz_addl : left_distributive mulz (+%R). Admitted.
Lemma onez_neq0 : (Posz 1) != 0. Proof. by []. Qed.

Definition comMixin := ComRingMixin mulzA mulzC mul1z mulz_addl onez_neq0.

End intRing.
End intRing.

Canonical int_Ring := RingType int intRing.comMixin.
Canonical int_comRing := ComRingType int intRing.mulzC.

End InstantiationInteger.
(**
#</div>#
#</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#
* Other structures and instances
#<div>#
*)
Module OtherStructures.
Import ssralg ssrnum.
Import GRing.Theory.
Local Open Scope ring_scope.
(**
#</div>#
** Extensions of rings

- read the documentation of  #<a href="http://math-comp.github.io/math-comp/htmldoc/mathcomp.algebra.ssralg.html">ssralg</a># and #<a href="http://math-comp.github.io/math-comp/htmldoc/mathcomp.algebra.ssrnum.html">ssrnum</a># (algebraic structures with order and absolute value)

- Canonical instances in the library are:
 - integers (int) (forms an integral domain)
 - rationals (rat) (forms an archimedian field)
 - algebraic numbers (algC) (forms an algebraically closed field)
 - polynomials {poly R} (forms an integral domain under sufficient hypothesis on the base ring)
 - matrices 'M[R]_(m, n) (forms a module / a finite dimension vector space)
 - square matrices 'M[R]_n (forms an algebra)

** Group theory (not in this course)

- see fingroup, perm, action, ...

** Structures for morphisms
#<div>#
*)

Search "linear" in ssralg.

Search "raddf" in ssralg.

Search "rmorph" in ssralg.
(**
#</div>#
** Substructures
#<div>#
*)

Print ssralg.GRing.subring_closed.
Print ssralg.GRing.subr_2closed.
Print ssralg.GRing.mulr_2closed.

Search "rpred" in ssralg.

End OtherStructures.
(**
#</div>#
#</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#
* Naming conventions.

The two most important things to get your way out of a situation:
 - Knowing your math
 - Searching the library for what you think you know

For that you have the ssreflect Search command. To use its full power, one should combine seach by identifier (Coq definition), pattern (partial terms) and name (a string contained in the name of the theorem).

The two first methods are straightforward to use (except if you instanciate your patterns more than necessary), but searching by name requires to be aware of naming conventions.

*)
(** #</div># *)
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

#<pre>Search _ "prefix" "suffix"* (symbol|pattern)* in library.</pre>#

** Examples
#<div>#
*)
Module Conventions.
From mathcomp Require Import ssralg ssrnum.
Import GRing.Theory.
Local Open Scope ring_scope.

Search _ *%R "A" in GRing.Theory.

Search _ "unit" in ssralg.

Search _ "inj" in ssralg.

Search _ "rmorph" "M" in ssralg.

Search _ "rpred" "D" in ssralg.

End Conventions.


(**
#</div>#
#</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#
 * A reminder on subtyping.
**)(**

 - In Coq, #<code>sT := {x : T | P x}</code># is a way to form a
  sigma-type. We say it is a #<b>subtype</b># if there is only one
  element it #<code>sT</code># for each element in
  #<code>T</code>#. This happens when #<code>P</code># is a boolean
  predicate. Another way to form a subtype is to create a record :
  #<code>Record sT := ST {x : T; px : P x}</code>#.

 - In mathcomp, to deal with subtypes independently from how they are
   form, we have a canonical structure.
#<div>#
*)

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
#</div>#
 - The most important operators to know on subtypes are
  #<code>val : sT -> T</code>#, #<code>insub : T -> option sT</code># and
  #<code>insubd : sT -> T -> sT</code>#.

- And the most important theorems to know are
  #<code>val_inj, val_eqE, val_insubd, insubdK</code># and #<code>insub</code>#

#<div>#
*)
About val_inj.
About val_eqE.
About insubK.
About val_insubd.
About insubdK.
(** #</div># *)
(** #</div># *)
