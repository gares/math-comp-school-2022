From elpi Require Import elpi.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** 
#<div class="slide">#
** Objective of this course

  Give you access to the 
  #<a href="http://math-comp.github.io/math-comp/">Mathematical Components library</a>#

  - formalization principles
  - proof language
  - familiarize with some theories


#</div>#

----------------------------------------------------------
#<div class="slide">#
** Why another library? Why another language?

  - large, consistent, library organized as a programming language
    library (interfaces, overload, naming conventions, ...)
  - maintainable in the long term (compact, stable, ...)
  - validated on large formalization projects

#<div class="note">(notes)<div class="note-text">#
The mathematical components library was used to formalize the
#<a href="https://en.wikipedia.org/wiki/Feit%E2%80%93Thompson_theorem">
Odd Order Theorem (Feit Thompson)
</a>#, literally a 250 pages book. Such proof amounts to 40k lines
of Coq scripts, on top of 120k lines of mathematical components.
The library has been maintained for more than 10 years now.
#</div></div>#

#</div>#

----------------------------------------------------------
#<div class="slide">#
** Roadmap of the first  lessons

  - boolean reflection (small scale reflection)
  - the ssreflect proof language (SSReflect)
  - basic libraries ([ssrbool], [seq]) and [==]

#</div>#

----------------------------------------------------------
#<div class="slide">#
** Disclaimer: this is not standard Coq

  - things are done differently, very differently, than usual
  - it is not easy to appreciate the benefits on small examples,
    but we will try hard ;-)
  - not enough time to explain eveything, I'll focus on
    intuition rather than technical details
#</div>#

----------------------------------------------------------
----------------------------------------------------------
#<div class="slide">#
** Boolean reflection

  - when a concept is "computable", lets represent it as a
    computable function (a program), not as an inductive relation
  - Coq knows how to compute, even symbolically, and computation is
    a very stable form of automation
  - functions (to bool) are a "simple" concept in type theory
    - Excluded Middle (EM) just holds
    - Uniqueness of Identity Proofs holds uniformly

#<div>#
*)

Module BooleanReflection.
(**
#</div>#

#<div class="note">(notes)<div class="note-text">#
Decideable predicates are quite common in both computer
science and mathematics. On this class or predicates the
excluded middle principle needs not to be an axiom; in particular
its computational content can be expressed inside Coq as a program.
Writing this program in Coq may be non trivial (e.g. being a prime
number requires some effort) but once the program is written it
provides notable benefits.  First, one can use the program as a
decision procedure for closed terms. Second, the proofs of such
predicate are small. E.g. a proof of [prime 17 = true] is just
[erefl true].

Last, the proofs of these predicates are irrelevant (i.e. unique).
This means that we can form subtypes without problems. E.g. the
in habitants of the subtype of prime numbers [{ x | prime x = true }]
are pairs, the number (relevant) and the proof (always [erefl true]).
Hence when we compare these pairs we can ignore the proof part, that is,
prime numbers behave exactly as numbers.

A way to see this is that we are using Coq as a logical framework
and that we are setting up an environment where one can
reason classically (as in set theory, EM, subsets..) but also take
advantage of computations as valid reasoning steps (unlike set theory TT
manipulates effective programs)
#</div></div>#

#</div>#
----------------------------------------------------------
#<div class="slide">#

** The first predicate: leq
   - order relation on [nat] is a program
   - [if-is-then] syntax (simply a 2-way match-with-end)
   - [.+1] syntax (postfix notations [.something] are recurrent)

#<div>#
*)
Fixpoint leq (n m : nat) : bool :=
  if n is p.+1 then
    if m is q.+1 then leq p q
    else false
  else true.

Arguments leq !n !m.
Infix "<=" := leq.

(** 
#</div>#

#<div class="note">(notes)<div class="note-text">#
We give a taste of boolean reflection by examples
  - these examples, to stay simple, are a bit artificial
  - in the library the same concepts are defeined in a slightly
    different way, but following the same ideas
#</div></div>#

#</div>#
------------------------------------------------------
#<div class="slide">#
 ** The first proof about leq
   - [... = true] to "state" something
   - proof by computation
   - [by []] to say, provable by trivial means (no mean is inside []).
   - [by tac] to say: tac must solve the goal (up to trivial leftovers)

#<div>#
*)
Lemma leq0n n : (0 <= n) = true.
Proof. (* compute. *) by []. Qed.

(**
#</div>#

#</div>#
------------------------------------------------------
#<div class="slide">#
** Another lemma about leq
   - equality as a double implication
   - naming convention

#<div>#
*)
Lemma leqSS n m : (n.+1 <= m.+1) = (n <= m).
Proof. (* simpl. *) by []. Qed.

(**
#</div>#

#</div>#
------------------------------------------------------
#<div class="slide">#
** Lets (not) use these lemmas
   - elim with naming and automatic clear of n
   - indentation for subgoals
   - no need to mention lemmas proved by computation
   - apply, exact, rewrite
#<div>#
*)
Lemma leqnn n : (n <= n) = true.
Proof.
(*#
elim: n => [|m IHm].
  by apply: leq0n.  exact: leq0n.
by rewrite leqSS; rewrite IHm.
#*)
by elim: n. Qed.

(** 
#</div>#

#</div>#
------------------------------------------------------
#<div class="slide">#
*** Connectives can be booleans too 

#<div>#
*)
Definition andb (b1 b2 : bool) : bool :=
  if b1 then b2 else false.
Infix "&&" := andb.

Definition orb (b1 b2 : bool) : bool :=
  if b1 then true else b2.
Infix "||" := orb.

Definition negb b : bool :=
  if b then false else true.
Notation "~~ b" := (negb b).

(** 
#</div>#

#</div>#
------------------------------------------------------
#<div class="slide">#
*** Proofs by truth tables
   - we can use EM to reason about boolean predicates
     and connectives
   - [move=> name]
   - [case:]
   - [move=> /=]
   - naming convention: [C] suffix
#<div>#
*)
Lemma andbC : forall b1 b2, (b1 && b2) = (b2 && b1).
Proof.
(*
move=> b1 b2.
case: b1.
  move=> /=.
  by case: b2.
by case: b2.
*)
by move=> b1 b2; case: b1; case: b2. Qed.

End BooleanReflection.

(** 
#</div>#

#<div class="note">(notes)<div class="note-text">#
Naming convention is key to find lemmas in a large library.
It is worth mentioning here
- [C] for commutativity
- [A] for associativity
- [K] for cancellation
#</div></div>#

#</div>#
------------------------------------------------------
#<div class="slide">#
** Recap: formalization approach and basic tactics
   - boolean predicates and connectives
   - think "up to" computation
   - [case], [elim], [move], basic [rewrite]
   - [if-is-then-else], [.+1]
   - naming convetion

#</div>#
------------------------------------------------------
------------------------------------------------------
#<div class="slide">#
** The real MathComp library
  
   Things to know:
   - [Search something inside library]
     - patterns [ _ <= _]
     - names ["SS"]
     - constants [leq]
   - [(a < b)] is a notation for [(a.+1 <= b)]
   - [==] stands for computable equality (overloaded)
   - [!=] is [~~ (_ == _)]
   - [is_true] coercion

#<div>#
*)
Search (_ <= _) inside ssrnat.
Search "SS" inside ssrnat.
Locate "_ < _".
Check (forall x, x.+1 <= x).
Search "orb" "C".
Print commutative.
Check (3 == 4) || (3 <= 4).
Eval compute in (3 == 4) || (3 <= 4).
Check (true == false).
Check (3 != 4).

Lemma test_is_true_coercion : true.
Proof. unfold is_true. by []. Qed.

(**
#</div>#

#</div>#
-------------------------------------------------------------
#<div class="slide">#
** Equality
   - privileged role (many lemmas are stated with = or is_true)
   - the [eqP] view: "is_true (a == b)   <->    a = b"
   - [=> /eqP] (both directions)
   - notation [.*2]
   - [rewrite lem1 lem2]

#<div>#
*)
Lemma test_eqP n m :
  n == m -> n.+1 + m.+1 = m.+1.*2.
Proof.
(*#
Check eqP.
move=> /eqP. move=> /eqP. move=> /eqP. move=> Enm. rewrite Enm.
Search (_ + _) _.*2 inside ssrnat.
exact: addnn.
#*)
by move=> /eqP; move=> Enm; rewrite Enm -addnn. Qed.


(**
#</div>#

#</div>#
-------------------------------------------------------------
#<div class="slide">#
 ** Infix [==] is overloaded
   - and [eqP] is too
#<div>#
*)
Lemma test2_eqP b1 b2 :
  b1 == ~~ b2 -> b1 || b2.
Proof.
(*
Search orb negb.
*)
by move=> /eqP; move=> Eb1; rewrite Eb1 orNb.
Qed.

(**
#</div>#

#</div>#

-------------------------------------------------------------
#<div class="slide">#
 ** connectives like [&&] have a view as well
   - [andP] and [[]]
   - [apply/viewP]
#<div>#
*)
Lemma test_andP b1 b2 :
  b1 && b2 -> b1 || b2.
Proof.
(*
move=> /andP Hb1b2.
case: Hb1b2.
move=> Hb1 Hb2.
apply/orP.

by rewrite Hb1.
*)
move=> /andP[Hb1 Hb2].
by rewrite Hb1.
Qed.

(**
#</div>#

#</div>#
-------------------------------------------------------------
#<div class="slide">#
 ** [move:] to move back down to the goal
#<div>#
*)
Lemma test_move_colon b1 b2 :
  b1 && (b1 == b2) -> b2.
Proof.
move=> /andP[Hb1 Hb12].
move: Hb12.
move=> /eqP Hb2.
by rewrite -Hb2 Hb1.
Qed.

(**
#</div>#

#</div>#

--------------------------------------------------------
--------------------------------------------------------
#<div class="slide">#
** Sequences
  - an alias for lists (used to be differnt)
  - many notations

#<div>#
*)
Check [::].
Check [:: 3 ; 4].
Check [::] ++ [:: true ; false].
Eval compute in [seq x.+1 | x <- [:: 1; 2; 3]].
Eval compute in [seq x <- [::3; 4; 5] | odd x ].
Eval compute in rcons [:: 4; 5] 3.
Eval compute in all odd [:: 3; 5].

Module polylist.

(**
#</div>#

#<div class="note">(notes)<div class="note-text">#
Notations for sequentes are documented the header of the 
#<a href="https://math-comp.github.io/htmldoc_1_15_0/mathcomp.ssreflect.seq.html">seq.v</a># file.
[rcons] is like [cons] but the new element is placed in the last position.
Indeed it is not a real constructor, but rather a function that appends the singleton list.
This special case of append has its own name and collection of theorems.
#</div></div>#

#</div>#
--------------------------------------------------------
#<div class="slide">#
** Polymorphic lists
   - This statement makes no assumptions on T
   - we can use [=> ... //] to kill a goal
   - we can use [=> ... /=] to simplify a goal

#<div>#
*)
Lemma size_cat T (s1 s2 : seq T) : size (s1 ++ s2) = size s1 + size s2.
Proof.
elim: s1 => [//|x s1 IH /=].
  (*by [].*)
(*move=> /=.*)
by rewrite IH.
Qed.

End polylist.

Eval compute in 3 \in [:: 7; 4; 3].

Fail Check forall T : Type, forall x : T, x \in [:: x ].

(** 
#</div>#

#</div>#
--------------------------------------------------------
#<div class="slide">#
** Had-hoc polymorphism
  - T : Type |- l : list T 
  - T : eqType |- l : list T
  - eqType means: a type with a decidable equality (_ == _)
#<div>#
*)

Check forall T : eqType, forall x : T, x \in [:: x ].

(**
#</div>#

#<div class="note">(notes)<div class="note-text">#
Had-hoc polymorphism is a well established concept in object
oriented programming languages and as well in functional
languages equipped with type classes like Haskell.
Whenever [T] is an [eqType], we have a comparison
function for all terms of type [T] ([x] in the example above).
#</div></div>#

#</div>#
--------------------------------------------------------
#<div class="slide">#
** The \in notation
   - overloaded as [(_ == _)]
   - pushing \in with inE
   - computable.
   - rewrite flag [!]
   - [rewrite !inE] idiom
#<div>#
*)
Lemma test_in l : 3 \in [:: 4; 5] ++ l -> l != [::].
Proof.
rewrite inE.
rewrite inE.
(*rewrite !inE*)
move=> /=.
apply: contraL.
move=> /eqP El.
rewrite El.
by [].
Qed.

(**
#</div>#

#</div>#

----
#<div class="slide">#
** References for this lesson
  - SSReflect #<a href="https://hal.inria.fr/inria-00258384">manual</a>#
  - documentation of the
       #<a href="https://math-comp.github.io/htmldoc_1_15_0/libgraph.html">library</a>#
    - in particular #<a href="https://math-comp.github.io/htmldoc_1_15_0/mathcomp.ssreflect.ssrbool.html">ssrbool</a>#
    - in particular #<a href="https://math-comp.github.io/htmldoc_1_15_0/mathcomp.ssreflect.ssrnat.html">ssrnat</a>#
  - #<a href="http://math-comp.github.io/mcb/">Book</a># (draft) on the Mathematical Components library
    #<img src="https://math-comp.github.io/mcb/cover-front-web.png"/>#
#</div># 
*)
