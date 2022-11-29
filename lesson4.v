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
   - [: name], to prepare the goal for a tactic
   - [rewrite lem -lem]
   - [apply: lem] or [exact: lem]
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
     - reflect
     - fooP
     - idioms


#</div>#
--------------------------------------------------------

#<div class="slide">#
*** Bookkeeping 101
   - the goal is a stack
   - defective case (the _top_ implicit tactic argument)
   - tactic=> this that
   - tactic: this that     (caveat: tactic != apply or exact)
   - "rename", "reorder"
#<div>#
*)
Lemma negb_and :
  forall b c, ~~ (b && c) = ~~ b || ~~ c.
Proof.
(*
move=> b. move=> c. move: b. move: c.
move=> c b. move: b c.
move=> b; case: b; move=> c; case: c.
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
------------------------------------------------------------
#<div class="slide">#
** Views are just lemmas (plus some automatic adaptors)
   - lemmas like [A -> B] can be used as views too
   - boolean connectives have associated views ("P" suffix)
   - [=> [ ... ]]

#<div>#
*)

Lemma test_leqW i j k :
  (i <= k) && (k.+1 <= j) -> i <= j.+1.
Proof.
(*# move=> /andP. move=> H; case: H. move=> /leqW. move=> leq_ik1. #*)
move=> /andP[/leqW leq_ik1 /leqW leq_k1j1].
exact: leq_trans leq_ik1 leq_k1j1.
Qed.

(**
#</div>#

#</div>#

--------------------------------------
#<div class="slide">#
** rewrite, one command to rule them all
  - rewrite
  - side condition and // ? 
  - rewrite a boolean predicate (is_true hides an eqaution)
#<div>#
*)

Lemma test_leq_cond p : prime p -> p.-1.+1 + p = p.*2.
Proof.
(*#
move=> pr_p.
Search predn inside ssrnat.
rewrite prednK.
  by rewrite addnn.
Search prime leq 0.
by apply: prime_gt0.
#*)
by move=> pr_p; rewrite prednK ?addnn // prime_gt0.
Qed.

(**
#</div>#

#</div># 

--------------------------------------------------------
#<div class="slide">#
** Rewrite on steroids
   - keyed matching
   - instantiation
   - localization
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
rewrite addnC.
rewrite [in RHS]addnC.
Abort.

Lemma no_pattern_from_the_rewrite_rule n : n + 0 = n.
Proof.
rewrite -[n in RHS]addn0.
Abort.

(**
#</div>#
#</div>#

------------------------------------------------------------
------------------------------------------------------------
#<div class="slide">#
** The reflect predicate
   - [reflect P b] is the preferred way to state that
     the predicate [P] (in [Prop]) is logically equivalent
     to [b=true]

#<div>#
*)
Module reflect_for_eqP.

Print reflect.

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
** Proving the reflection lemma for eqn
    - the convenience lemma [iffP]
    - the [congr] tactic
    - trivial branches [//]
    - rewrite on the fly [->]
    - loaded induction [elim: n m]
    - [congr]
#<div>#
*)
Lemma myeqP m n : reflect (m = n) (eqn m n).
Proof.
(*#
apply: (iffP idP) => [|->]; last by elim: n.
elim: m n; first by case.
move=> n IHn m eq_n1m.
case: m eq_n1m => // m eq_n1m1.
congr (_.+1).
exact: IHn.
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
   - Inductive predicates to drive the proof
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
** Let's try out leqP on an ugly goal
   - matching of indexes
   - generalization of unresolved implicits
   - instantiation by matching
#<div>#*)
Lemma test_leqP m n1 n2 :
  (m <= (if n1 < n2 then n1 else n2)) =
  (m <= n1) && (m <= n2) && ((n1 < n2) || (n2 <= n1)).
Proof.
case: leqP => [leqn21 | /ltnW ltn12 ]; rewrite /= andbT.
  by rewrite andb_idl // => /leq_trans /(_ leqn21).
by rewrite andb_idr // => /leq_trans->.
Qed.

(**
#</div>#
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
by move=> /negbT; rewrite subn_eq0 leqNgt negbK=> /ltnW.
Qed.

(**
#</div>#
#</div>#
--------------------------------------------------------
--------------------------------------------------------
#<div class="slide">#
** Forward reasoning
   - have
   - have :=
   - have + views

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
elim: s => //= x s.

have EM_a : a x || ~~ a x.
  by exact: orbN.
move: EM_a => /orP EM_a. case: EM_a => [-> | /negbTE-> ] //= _.

(*#
have /orP[ ax | /negbTE n_ax ] : a x || ~~ a x by case: (a x).
  by rewrite ax.
rewrite n_ax /= => ?.
#*)
(*#have [ax//|n_ax ?] := boolP (a x).#*)

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
       #<a href="https://math-comp.github.io/htmldoc_1_15_0/libgraph.html">library</a>#
    - in particular #<a href="https://math-comp.github.io/htmldoc_1_15_0/mathcomp.ssreflect.seq.html">seq</a>#

#</div>#
--------------------------------------------------------
#<div class="slide">#
** Demo:
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
#</div># 
*)


