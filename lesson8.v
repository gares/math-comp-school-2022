From Coq Require Import ZArith_base. (* Required only for better printing of Z constants and operators. *)
From elpi Require Import elpi.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint intdiv.
From mathcomp Require Import zify ring lra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
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

** [lia]: linear integer arithmetic (a.k.a. Presburger arithmetic)

This tactic provides a certifying decision procedure for quantifier-free linear
integer arithmetic.

<div>
*)
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
Proof.
lia.
Qed.
(** #</div>#

The [zify] and [lia] tactics support some [bool] operators.

#<div>#
*)
Goal forall m n : nat, (n <= m) = ~~ (m.*2 < n.*2).
Proof.
lia.
Qed.
(** #</div></div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#

** Some advanced features of the [lia] tactic

The [lia] tactic performs normalization with respect to (semi)ring axioms, and
can actually solve some non-linear problems.

#<div>#
 *)
Goal forall m n : nat, m * n = n * m.
Proof.
lia.
Qed.

Goal forall m n : nat, (m + n) ^ 2 = m ^ 2 + n ^ 2 + 2 * m * n.
Proof.
lia.
Qed.
(** #</div>#

The Mczify library also pre-processes Euclidean division and the divisibility
relation.

#<div>#
*)
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
Proof.
lia.
Qed.

Goal forall m : nat, (6 %| m) && (4 %| m) = (12 %| m).
Proof.
lia.
Qed.
(** #</div></div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#

** [nia]: non-linear integer arithmetic

The [nia] tactic is an extension of the [lia] tactic that allows for some
non-linear reasoning by propagating positivity and negativity conditions through
multiplication and exponentiation.

<div>
*)
Goal forall m n : int, (0 <= m -> 0 <= n -> 0 <= m * n)%R.
Proof.
nia.
Qed.

Goal forall (m : int) (n : nat), (0 <= (m ^+ 2) ^+ n)%R.
Proof.
nia.
Qed.

Goal forall m n : nat, n <= m -> n ^ 2 <= m * n.
Proof.
nia.
Qed.

Goal forall m n p : int,
  (0 <= n)%R -> (m %/ (n * p))%Z = ((m %/ n) %/ p)%Z.
Proof.
nia.
Qed.
(** #</div></div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#

** Instructing the [zify] tactic to pre-process new arithmetic operators

<div>
*)

(* TODO *)

(** #</div></div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#

** [ring]: polynomial equation solver

<div>
*)

(* TODO *)

(** #</div></div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#

** Some advanced features of the [ring] tactic

<div>
*)

(* TODO *)

(** #</div></div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#

** [field]: rational equation solver

<div>
*)

(* TODO *)

(** #</div></div># *)

(** -------------------------------------------- *)
(** #<div class='slide'>#

** [lra] and [nra]: linear and non-linear real arithmetic

<div>
*)

(* TODO *)

(** #</div></div># *)
