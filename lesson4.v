From elpi Require Import elpi.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
#<div class="slide">#
** Recap of lesson 1

 Proof language
   - [move=>] [name] [/view] [//] [/=] [[..|..]] to name/change the goal
   - [: name], [: (lem arg)]
   - [rewrite lem -lem]
   - [apply: lem]
   - [apply/view]
 Library
   - naming convention: [addnC], [eqP], [orbN], [orNb], ...
   - notations: [.+1], [if-is-then-else]
   - [Search (_ + _) inside ssrnat]
   - [Search addn "C" inside ssrnat]
   - Use the HTML doc!
 Approach
   - boolean predicates
   - [reflect P b] to link [bool] with [Prop]

#</div>#
--------------------------------------------------------
#<div class="slide">#
** Today
   - the SSReflect proof language (part 2)
     - stack model and views
     - [rewrite] idioms and patterns
     - forward reasoning with [have]
   - spec lemmas
     - [reflect]
     - [fooP]
     - idioms


#</div>#
--------------------------------------------------------

#<div class="slide">#
*** Bookkeeping 101
   - the goal is a stack
   - defective case/elim (the _top_ implicit tactic argument)
   - tactical [=>] for post processing
   - tactical [:] for pre processing
   - "rename", "reorder"
#<div>#
*)
Lemma negb_and :
  forall b c, ~~ (b && c) = ~~ b || ~~ c.
Proof.
(*
move=> b. move=> c. move: b. move: c. (* up and down *)
move=> c b. move: b c.  (* reverse order, it's a stack *)
move=> b; case: b. move=> c; case: c. (* no need to name _top_, it's the default subject *)
*)
by case; case. Qed.

(**
#</div>#

#<div class="note">(notes)<div class="note-text">#
We say that the goal (under the horizontal bar) is a stack, since
items can only be accessed accorrding to a stack discipline.
If the goal is [forall x y, x = 1 + 2 * y -> odd x] one has to
deal with [x] and [y] before accessing [x = 1 + 2 * y].
#</div></div>#

#</div>#
--------------------------------------------------------

#<div class="slide">#
*** Induction
  - [elim] with generalization
  - [in x *] alternative
  - [rewrite (lem args)] to specialize a lemma
#<div>#
*)
Lemma induction_fold (l : seq nat) x :
  foldl addn x l = x + foldl addn 0 l.
Proof.
(*#
elim: l => [|y ys IH] /=. (* first attempt *)
  by rewrite addn0.
(* we are stuck *)
#*)
elim: l x => [|y ys IH] x /=. (* better attempt, generalize and re-introduce x *)
  by rewrite addn0.
by rewrite IH (IH y) addnA. (* IH is now quantified *)
Qed.

(**
#</div>#

#<div class="note">(notes)<div class="note-text">#
Recall that [elim] (or [case]) actually operate on
the top of the stack, which is the last item generalized
by [:].
#</div></div>#

#</div>#



------------------------------------------------------------
#<div class="slide">#
** Views are just lemmas (plus some automatic adaptors)
   - lemmas like [A -> B] can be used as views too
   - boolean connectives have associated views ("P" suffix)

#<div>#
*)

Lemma test_leqW i j k :
  (i <= k) && (k.+1 <= j) -> i <= j.+1.
Proof.
(*# move=> /andP H; case: H. move=> /leqW leq_ik1. #*)
move=> /andP[/leqW leq_ik1 /leqW leq_k1j1]. (* process fully, then name *)
by apply: leq_trans leq_ik1 leq_k1j1.
Qed.

(**
#</div>#

#<div class="note">(notes)<div class="note-text">#
There is nothin special with the [/andP[H1 H2]] we did
in lesson 1, it is just the composition of [/view]
followed by a case split [[]] (in this case only one branch)
#</div></div>#

#</div>#

--------------------------------------
#<div class="slide">#
** [rewrite], one command to rule them all
  - 1/3 of the lines of Math Comp proofs are [rewrite]
  - side conditions handling via [//] and [?]
  - rewrite a boolean predicate ([is_true] hides an eqaution)
#<div>#
*)

Lemma test_leq_cond p : prime p -> p.-1.+1 + p = p.*2.
Proof.
(*#
move=> pr_p.
Search predn inside ssrnat.
rewrite prednK. (* main step *)
  by rewrite addnn. (* side condition *)
Search prime leq 0.
by apply: prime_gt0. (* conclusion *)
#*)
(* idiomatic use of conditional rewrite rules *)
by move=> pr_p; rewrite prednK ?addnn // prime_gt0.
Qed.

(**
#</div>#

#</div># 

--------------------------------------------------------
#<div class="slide">#
** [rewrite] and subterm selection
   - keyed matching drives the search
   - specialization via argument passing
   - specialization via pattern
   - localization via contextual pattern (approximate or precise)
   - LHS and RHS notations
#<div>#*)
Lemma subterm_selection n m :
  n + (m * 2).+1 = n * (m + m.+1).
Proof.
rewrite addnC.
rewrite (addnC m).
rewrite [_ + m]addnC.
rewrite [in n * _]addnC.
rewrite [X in _ = _ * X]addnC.
rewrite [in RHS]addnC.
Abort.

Lemma occurrence_selection n m :
  n + m = n + m.
Proof.
rewrite addnC. (* all occurrecens of the rule are replaced *)
rewrite [in RHS]addnC. (* limit to RHS of the goal *)
Abort.

Lemma no_pattern_from_the_rewrite_rule n : n + 0 = n.
Proof.
rewrite -[n in RHS]addn0. (* precise patterns for ambiguous rules *)
Abort.

(**
#</div>#

#<div class="note">(notes)<div class="note-text">#
The details can be found in the reference #<a href="https://coq.inria.fr/refman/proof-engine/ssreflect-proof-language.html">manual</a>#
or in the #<a href="https://hal.inria.fr/hal-00652286">paper</a>#
#</div></div>#

#</div>#

------------------------------------------------------------
------------------------------------------------------------
#<div class="slide">#
** The reflect predicate
   - [reflect P b] is the preferred way to state that
     the predicate [P] (in [Prop]) is logically equivalent
     to [b = true]

#<div>#
*)
Module reflect_for_eqP.

Print reflect.

(* we use this boolean predicate in the examples below *)
Fixpoint eqn m n :=
  match m, n with
  | 0, 0 => true
  | j.+1,k.+1 => eqn j k
  | _, _ => false
  end.
Arguments eqn !m !n.

(**
#</div>#

#</div>#
----------------------------------------------------------
#<div class="slide">#
** Proving the reflection lemma for [eqn]
    - the convenience lemma [iffP]
    - the [congr] tactic
    - trivial branches [=> //]
    - rewrite on the fly [->]
    - [first by]
    - [congr]
#<div>#
*)
Lemma myeqP m n : reflect (m = n) (eqn m n).
Proof.
(*#
apply: (iffP idP) => [|->]; last by elim: n.
elim: m n; first by case.
move=> n IHn m eq_n1m.
case: m eq_n1m => // m eq_n1m1. (* case with generalization *)
congr (_.+1). (* cleanup of the goal *)
by apply: IHn.
#*)
apply: (iffP idP) => [|->]; last by elim: n.
by elim: m n => [|m IHm] // [|n] // /IHm->.
Qed.

Lemma test_myeqP n m : (eqn n m) -> m = n.
Proof. by move=> /myeqP ->. Qed.

End reflect_for_eqP.

(** 
#</div>#

#</div># 

--------------------------------------------------------
#<div class="slide">#
** Spec lemmas
   - Inductive predicates to drive the proof:
     - you chose how many branches
     - you chose which equations are automatically applied
     - you chose which extra assumption a branch has
   - [of] syntax for inductives
#<div>#*)

Inductive leq_xor_gtn m n : bool -> bool -> Prop :=
  | LeqNotGtn of m <= n : leq_xor_gtn m n true false
  | GtnNotLeq of n < m  : leq_xor_gtn m n false true.

Axiom leqP : forall m n : nat, leq_xor_gtn m n (m <= n) (n < m).

(**
#</div>#

#</div>#
--------------------------------------------------------
#<div class="slide">#
** Let's try out [leqP] on an ugly goal
   - matching of indexes uses the same discipline of [rewrite]

   Bonus (time permitting):
   - generalization of unresolved implicits after [/leq_trans]
   - specialization of the top stack item via [/(_ arg)]
#<div>#*)
Lemma test_leqP m n1 n2 :
  (m <= (if n1 < n2 then n1 else n2)) =
  (m <= n1) && (m <= n2) && ((n1 < n2) || (n2 <= n1)).
Proof.
(* the indexes of [leqP] give rise to patterns, which are matched
   right to left. So the first one is [_ < _] which finds [n1 < n2]
   and replaces it with [false] in the first branch and [true] in the
   second. Then it is the turn of [n2 <= n1].
   
   use: Set Debug "ssreflect". for a slow motion *)
case: leqP => [leqn21 | /ltnW ltn12 ]; rewrite /= andbT.
  by rewrite andb_idl // => /leq_trans /(_ leqn21).
by rewrite andb_idr // => /leq_trans->.
Qed.

(**
#</div>#

#<div class="note">(notes)<div class="note-text">#
While I presonally find [/leq_trans] too clever and
likely unnecessary, it is used in the library, hence this slide
#</div></div>#

#</div>#
--------------------------------------------------------
#<div class="slide">#
** Another commodity: [ifP]
   - a spec lemma for if-then-else
   - handy with case, since matching spares you to write
     the expressions involved
   - remark how the goal is used as a work space
#<div>#*)
Lemma test_ifP n m : if n <= m then 0 <= m - n else m - n == 0.
Proof.
case: ifP => //.
(* MC idiom: don't introduce hyps if not necessary *)
by move=> /negbT; rewrite subn_eq0 leqNgt negbK=> /ltnW.
Qed.

(**
#</div>#
#</div>#
--------------------------------------------------------
--------------------------------------------------------
#<div class="slide">#
** Forward reasoning
   - [have : statement.]
   - [have := proof]
   - [have /view ... : .. := ..] and variations

Definition of all
<<
Fixpoint all a s := if s is x :: s' then a x && all a s' else true.
>>

Definition of count
<<
Fixpoint count a s := if s is x :: s' then a x + count s' else 0.
>>

A lemma linking the two concepts 

#<div>#
*)
Lemma all_count (T : Type) (a : pred T) s :
  all a s = (count a s == size s).
Proof.
(* common start *)
elim: s => //= x s.

(* first try at using EM *)
have EM_a : a x || ~~ a x.
  by apply: orbN.
move: EM_a => /orP EM_a. case: EM_a => [-> | /negbTE-> ] //= _.

(*#
(* second try using views and have *)
have /orP[ ax | /negbTE n_ax ] : a x || ~~ a x by case: (a x).
  by rewrite ax.
rewrite n_ax /= => ?.
#*)

(*#
(* this is the best way of doing it *)
have [ax//|n_ax ?] := boolP (a x).
#*)

(* common conclusion *)
by rewrite add0n eqn_leq ltnNge count_size /= andbC.
Qed.

(**
#</div>#
#</div>#

--------------------------------------------------------
#<div class="slide">#
** References for this lesson:
  - SSReflect #<a href="https://coq.inria.fr/refman/proof-engine/ssreflect-proof-language.html">manual</a>#
  - documentation of the
       #<a href="https://math-comp.github.io/htmldoc_2_0_alpha1/libgraph.html">library</a>#
    - in particular #<a href="https://math-comp.github.io/htmldoc_2_0_alpha1/mathcomp.ssreflect.seq.html">seq</a>#

#</div>#
--------------------------------------------------------
#<div class="slide">#
** Demo (time permitting, or as an exercise)
   - you should be now able to read this proof

#<div>#*)

Lemma dvdn_fact m n : 0 < m <= n -> m %| n`!.
Proof.
case: m => //= m; elim: n => //= n IHn; rewrite ltnS leq_eqVlt.
by move=> /orP[ /eqP-> | /IHn]; [apply: dvdn_mulr | apply: dvdn_mull].
Qed.

Lemma prime_above m : {p | m < p & prime p}.
Proof.
(*# Check pdivP. #*)
have /pdivP[p pr_p p_dv_m1]: 1 < m`! + 1 by rewrite addn1 ltnS fact_gt0.
exists p => //; rewrite ltnNge; apply: contraL p_dv_m1 => p_le_m.
(*# Check dvdn_addr. #*)
by rewrite dvdn_addr ?dvdn_fact ?prime_gt0 // gtnNdvd ?prime_gt1.
Qed.
    
(** 
#</div># 

#<div class="note">(notes)<div class="note-text">#
This proof is also explained in the
#<a href="https://math-comp.github.io/mcb/">Math Comp Book</a>#
#</div></div>#


#</div># 
*)


