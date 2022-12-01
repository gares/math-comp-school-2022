From elpi Require Import elpi.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint.
From mathcomp Require Import zify ring. (* lra. *)

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

(* TODO: some examples on nat and int *)

(** #</div>#

TODO: normalization with respect to (semi)ring axioms

#<div>#
*)

(* TODO: examples *)

(** #</div>#

TODO: euclidean division

#<div>#
*)

(* TODO: examples *)

(** #</div></div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#

** [nia]: non-linear integer arithmetic

<div>
*)

(** #</div></div># *)
