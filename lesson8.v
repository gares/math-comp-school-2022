From Coq Require Import ZifyClasses ZArith_base.
From elpi Require Import elpi.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint rat intdiv.
From mathcomp Require Import ssrZ zify ring lra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Delimit Scope Z_scope with coqZ.
(** #<div class='slide'>#
* Lesson 8: Proof automation

** Goals
- This lecture explains how to use proof-automation tactics in MathComp
- ... and how to implement such proof-automation tactics for MathComp, but very
  briefly (because this is still an active research subject and intricate.)

** Tools we use
- The #<a href="https://github.com/math-comp/mczify">Mczify</a># library adapts the
  #<a href="https://coq.github.io/doc/V8.16.1/refman/addendum/micromega.html&#35;coq:tacn.lia"><code>lia</code></a># and
  #<a href="https://coq.github.io/doc/V8.16.1/refman/addendum/micromega.html&#35;coq:tacn.nia"><code>nia</code></a>#
  tactics to MathComp.
  - This adaptation is done by relying on the
    #<a href="https://coq.github.io/doc/V8.16.1/refman/addendum/micromega.html&#35;coq:tacn.zify"><code>zify</code></a>#
    tactic, which provides an extensible preprocessing facility for the [lia]
    tactic.
- The #<a href="https://github.com/math-comp/algebra-tactics">Algebra Tactics</a>#
  library provides a reimplementation of
  #<a href="https://coq.github.io/doc/V8.16.1/refman/addendum/ring.html&#35;coq:tacn.ring"><code>ring</code></a>#,
  #<a href="https://coq.github.io/doc/V8.16.1/refman/addendum/ring.html&#35;coq:tacn.field"><code>field</code></a>#,
  #<a href="https://coq.github.io/doc/V8.16.1/refman/addendum/micromega.html&#35;coq:tacn.lra"><code>lra</code></a>#,
  #<a href="https://coq.github.io/doc/V8.16.1/refman/addendum/micromega.html&#35;coq:tacn.nra"><code>nra</code></a>#, and
  #<a href="https://coq.github.io/doc/V8.16.1/refman/addendum/micromega.html&#35;coq:tacn.psatz"><code>psatz</code></a>#
  tactics for MathComp.
  - These tactics ([lia] too) use _large-scale_ Boolean reflection (cf. Lesson
    1): they have proof procedures implemented in Coq, and run them inside the
    Coq kernel to check that the goal propositions hold.
  - This reimplementation is done by reimplementing reification procedures in
    #<a href="https://github.com/LPCIC/coq-elpi">Coq-Elpi</a># and reusing the
    proof procedures bundled in Coq.
    A reification procedure is a _meta_-function that takes the goal and
    produces a syntax tree representing the goal, that we can manipulate inside
    Coq.
    Coq-Elpi allows us to write Coq plugins in
    #<a href="https://github.com/LPCIC/elpi">Elpi</a>#, a dialect of a
    higher-order logic programming language called λProlog.

#</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#

** [lia]: linear integer arithmetic (a.k.a. Presburger arithmetic) solver

This tactic provides a certifying decision procedure for quantifier-free linear
integer arithmetic.

<div> *)
Goal forall m n : nat, n <= m -> n.*2 <= m + n.
Proof.
lia.
(*
move=> m n lenm.
Zify.zify.
lia.
*)
Qed.

Goal forall m n : int, (n <= m -> n * 2 <= m + n)%R.
Proof. lia. Qed.

(* A complicated example taken from the Coq reference manual. *)
Goal forall m n : int,
  (27 <= 11 * m + 13 * n <= 45)%R -> (-10 <= 7 * m - 9 * n <= 4)%R -> False.
Proof. lia. Qed.
(** #</div>#

The [zify] and [lia] tactics support some [bool] operators.

#<div># *)
Goal forall m n : nat, (n <= m) = ~~ (m.*2 < n.*2).
Proof. lia. Qed.
(** #</div></div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#

** Some advanced features of the [lia] tactic

The [lia] tactic performs normalization with respect to (semi)ring axioms, and
can actually solve some non-linear problems.

#<div># *)
Goal forall m n : nat, m * n = n * m.
Proof. lia. Qed.

Goal forall m n : nat, (m + n) ^ 2 = m ^ 2 + n ^ 2 + 2 * m * n.
Proof. lia. Qed.
(** #</div>#

The Mczify library also pre-processes Euclidean division and the divisibility
relation.

#<div># *)
Goal forall m : nat, m %/ 2 <= m.
Proof.
lia.
(*
move=> m.
Zify.zify.
lia.
*)
Qed.

Goal forall m : nat, 6 %| m -> 4 %| m -> 12 %| m.
Proof. lia. Qed.

Goal forall m : nat, (6 %| m) && (4 %| m) = (12 %| m).
Proof. lia. Qed.
(** #</div></div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#

** [nia]: non-linear integer arithmetic solver

The [nia] tactic is an extension of the [lia] tactic that allows for some
non-linear reasoning by propagating positivity and negativity conditions through
multiplication and exponentiation.

#<div># *)
Goal forall m n : int, (0 <= m -> 0 <= n -> 0 <= m * n)%R.
Proof. nia. Qed.

Goal forall (m : int) (n : nat), (0 <= (m ^+ 2) ^+ n)%R.
Proof. nia. Qed.

Goal forall m n : nat, n <= m -> n ^ 2 <= m * n.
Proof. nia. Qed.

Goal forall m n p : int,
  (0 <= n)%R -> (m %/ (n * p))%Z = ((m %/ n) %/ p)%Z.
Proof.
(* Too slow in jsCoq: *)
(* nia. *)
Abort.
(** #</div></div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#

** Instructing the [zify] tactic to pre-process new arithmetic operators

The [zify] and [lia] tactics do not recognize user-defined operators out of the box:

#<div># *)
Definition triple (n : nat) : nat := n * 3.

Goal forall n, triple (triple n) = n * 9.
Proof.
Fail lia.
Zify.zify.
Abort.
(** #</div>#

Declare an instance of type [UnOp triple], and register it through the
[Add Zify UnOp] command:

#<div># *)
Fact Op_triple_subproof (n : nat) : Z.of_nat (triple n) = (3 * Z.of_nat n)%coqZ.
Proof. rewrite /triple; lia. Qed.

#[global]
Instance Op_triple : UnOp triple :=
  { TUOp := Z.mul 3; TUOpInj := Op_triple_subproof }.
Add Zify UnOp Op_triple.
(** #</div>#

Then, the [zify] tactic starts recognizing the new operator [triple]:

#<div># *)
Goal forall n, triple (triple n) = n * 9.
Proof. lia. Qed.
(** #</div></div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#

** [ring]: polynomial equation solver

This tactic provides a certified decision procedure for polynomial equations
over commutative rings.

#<div># *)
Goal forall a b : int, ((a + b) ^+ 2 = a ^+ 2 + b ^+ 2 + 2 * a * b :> int)%R.
Proof. move=> a b; ring. Qed.
(** #</div>#

It works for any abstract or concrete commutative rings:

#<div># *)
Goal forall a b : rat, ((a + b) ^+ 2 = a ^+ 2 + b ^+ 2 + 2 * a * b :> rat)%R.
Proof. move=> a b; ring. Qed.

Goal forall (R : comRingType) (a b : R),
    ((a + b) ^+ 2 = a ^+ 2 + b ^+ 2 + 2 * a * b :> R)%R.
Proof. move=> R a b; ring. Qed.

Goal forall (R : comRingType) (a : R) (b : R * int),
    (((a, 1) + b) ^+ 2 = (a, 1) ^+ 2 + b ^+ 2 + 2 * (a, 1) * b :> R * int)%R.
Proof. move=> R a b; ring. Qed.
(** #</div></div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#

** Some advanced features of the [ring] tactic

The [ring] tactic can prove polynomial equations modulo monomial equalities:

#<div># *)
Goal forall a b : int, (a * b = 15 -> (a + b) ^+ 2 = a ^+ 2 + b ^+ 2 + 30)%R.
Proof.
move=> a b H.
ring: H.
Qed.
(** #</div>#

The Algebra Tactics library implements preprocessors to push down homomorphism
applications:

#<div># *)
Goal forall (R : ringType) (S : comRingType) (f : {rmorphism R -> S}) (a b : R),
    (f ((a + b) ^+ 2) = f a ^+ 2 + f b ^+ 2 + 2 * f a * f b)%R.
Proof.
move=> R S f a b.
rewrite rmorphX rmorphD. (* This line can be removed. *)
ring.
Qed.
(** #</div></div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#

** [field]: rational equation solver

This tactic provides a certified decision procedure for rational equations over
fields.

#<div># *)
Goal forall (F : fieldType) (x : F),
    (x != 0 -> (1 - 1 / x) * x - x + 1 = 0)%R.
Proof.
move=> F x x_neq0.
field.
(*
The field tactic leaves a proof obligation saying that the denominators in the
input are non-zero.
*)
exact: x_neq0.
Qed.

Goal forall (F : fieldType) (n : nat),
    (n%:R != 0 :> F -> (2 * n)%:R / n%:R = 2 :> F)%R.
Proof.
move=> F n n_neq0.
field.
exact: n_neq0.
Qed.
(** #</div>#

For a partially ordered field ([numFieldType]), non-nullity conditions of the
form [n%:R != 0] and [n%:~R != 0] where [n] is a non-zero constant are trivial,
and thus are not generated.

#<div># *)
Goal forall (F : numFieldType) (x : F), ((x / 2) * 2)%R = x.
Proof.
move=> F x.
field.
by [].
Qed.
(** #</div>#

As in the [ring] tactic, the [field] tactic supports homomorphisms and reasoning
modulo monomial equalities.

#</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#

** [lra] and [nra]: linear and non-linear real arithmetic

NB: The support for the [lra] and [nra] tactics in Algebra Tactics is
experimental for the moment.

#<div># *)
Goal forall (x y : int), (y <= x -> 0 <= x -> y <= x * 2)%R.
Proof. move=> R x y; lra. Qed.
(** #</div>#

For [realFieldType]s, division and multiplicative inverse are avairable.

#<div># *)
Goal forall (x y : rat), (y <= x -> 0 <= x -> y / 2 <= x)%R.
Proof. move=> R x y; lra. Qed.
(** #</div>#

These tactics work for any abstract or concrete [realDomainType] or
[realFieldType].

#<div># *)
Goal forall (R : realDomainType) (x y : R),
  (x + 2 * y <= 3 -> 2 * x + y <= 3 -> x + y <= 2)%R.
Proof. move=> R x y; lra. Qed.
(** #</div></div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#

** How do they work? -- proof by large-scale reflection

We first prove the following reflection lemma (but do not try to understand the
formal statement and proof).

#<div># *)
Import Ring_polynom.

Lemma ring_correct
  (R : comRingType)
  (* `l` below is called a variable map, whose i-th item gives the            *)
  (* interpretation of the variable i.                                        *)
  (l : seq R)
  (* `pe1` and `pe2` below are polynomial expressions with integer            *)
  (* coefficients, representing the LHS and RHS of the equation to prove.     *)
  (pe1 pe2 : PExpr Z) :
  (* If `pe1` and `pe2` normalized to polynomials (in horner normal form) are *)
  (* equal,                                                                   *)
  Peq Z.eqb (norm_subst 0%R 1%R Z.add Z.mul Z.sub Z.opp Z.eqb
               (triv_div 0%R 1%R Z.eqb) 0 [::] pe1)
            (norm_subst 0%R 1%R Z.add Z.mul Z.sub Z.opp Z.eqb
               (triv_div 0%R 1%R Z.eqb) 0 [::] pe2) ->
  (* `pe1` and `pe2` interpreted as values of the ring `R` are equal.         *)
  PEeval 0%R 1%R +%R *%R (fun x y => (x - y)%R) -%R%R
    (fun n => ((int_of_Z n)%:~R)%R) id (fun x n => (x ^+ N.to_nat n)%R) l pe1 =
  PEeval 0%R 1%R +%R *%R (fun x y => (x - y)%R) -%R%R
    (fun n => ((int_of_Z n)%:~R)%R) id (fun x n => (x ^+ N.to_nat n)%R) l pe2.
Proof. exact: (@Internals.Rcorrect R 0 l [::]). Qed.
(** #</div>#

Let us apply the above lemma to the example below.

#<div># *)
Goal forall a b : int, ((a + b) ^+ 2 = a ^+ 2 + b ^+ 2 + 2 * a * b :> int)%R.
Proof.
move=> a b.
(* Variable map:                                                              *)
pose l := [:: a; b].
(* Polynomial expressions representing the LHS and RHS, where numbers `1` and *)
(* `2` given as arguments of `PEX` represents 1st and 2nd variables, namely,  *)
(* `a` and `b`:                                                               *)
pose pe1 : PExpr Z := PEpow (PEadd (PEX _ 1) (PEX _ 2)) 2.
pose pe2 : PExpr Z := PEadd (PEadd (PEpow (PEX _ 1) 2) (PEpow (PEX _ 2) 2))
                        (PEmul (PEmul (PEc 2%coqZ) (PEX _ 1)) (PEX _ 2)).
(* Apply the reflection lemma with the variable map and polynomial            *)
(* expressions given above:                                                   *)
apply: (@ring_correct _ [:: a; b] pe1 pe2).
(* By reducing some subterms, we notice that we are comparing the same normal *)
(* form:                                                                      *)
rewrite /norm_subst [p1 in Peq _ p1 _]/= [p2 in Peq _ _ p2]/=.
(* Actually, the entire goal reduces to `true`:                               *)
rewrite /=.
by [].
Qed.
(** #</div>#

The only missing piece in turning this methodology into a fully-automated tactic
is how to obtain the variable map and the polynomial expressions from the goal,
which is called _reification_.

#</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#

** Further reading

- Benjamin Grégoire, Assia Mahboubi.
  #<a href="https://hal.archives-ouvertes.fr/hal-00819484">Proving Equalities in a Commutative Ring Done Right in Coq</a>#.
  In: TPHOLs 2005.

  This paper explains the implementation of the [ring] tactic.
- Frédéric Besson.
  #<a href="http://people.rennes.inria.fr/Frederic.Besson/Fast_Reflexive_Arithmetics_Tactics.pdf">Fast Reflexive Arithmetic Tactics the Linear Case and Beyond</a>#.
  In: TYPES 2006.

  This paper explains the implementation of the [lia], [nia], [lra], [nra], and
  [psatz] tactics.
- Kazuhiko Sakaguchi.
  #<a href="https://drops.dagstuhl.de/opus/volltexte/2022/16738/">Reflexive tactics for algebra, revisited</a>#.
  In: ITP 2022.

  This paper explains:
  - a toy reflexive tactic for [zmodType] equations,
  - its reification procedure implemented in Coq-Elpi, that works in the
    presence of an inheritance hierarchy and overloaded operators
    (cf. Lesson 5),
  - how to preprocess homomorphisms by reflection efficiently, and
  - the application of Mczify and Algebra Tactics to
    #<a href="https://github.com/coq-community/apery">the formal proof of the irrationality of ζ(3)</a>#.

- Enrico Tassi. #<a href="https://github.com/LPCIC/coq-elpi">Coq-Elpi</a>#.

#</div># *)
