Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
(**
#<div class="slide">#
** Recap

 Proof language
   - [: name], to prepare the goal for a tactic
   - [=>] [name] [/view] [//] [/=] [{name}] [[]], to post-process the goal
   - [rewrite lem -lem // /= /def]
   - [apply: lem]
 Library
   - naming convention: [addnC], [eqP], [orbN], [orNb], ...
   - notations: [.+1], [if-is-then-else]
   - [Search _ (_ + _) in ssrnat]
   - [Search _ addn "C" in ssrnat]
   - Use the HTML doc!
 Approach
   - boolean predicates
   - [reflect P b] to link bool with Prop

#</div>#
--------------------------------------------------------
#<div class="slide">#
** Today
   - The [seq] library
   - forward reasoning with [have]
   - spec lemmas
   - [rewrite] patterns

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
#<a href="http://math-comp.github.io/math-comp/htmldoc/mathcomp.ssreflect.seq.html">seq.v</a># file.
[rcons] is like [cons] but the new element is placed in the last position.
Indeed it is not a real constructor, but rather a function that appends the singleton list.
This special case of append has its own name and collection of theorems.
#</div></div>#

#</div>#
--------------------------------------------------------
#<div class="slide">#
** Polymorphic lists
   - This statement makes no assumptions on T
   - recap: [// /= ->]

#<div>#
*)
Lemma size_cat T (s1 s2 : seq T) : size (s1 ++ s2) = size s1 + size s2.
Proof.  by elim: s1 => //= x s1 ->. Qed.

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
   - rewrite !inE
#<div>#
*)
Lemma test_in l : 3 \in [:: 4; 5] ++ l -> l != [::].
Proof.
by rewrite !inE => /=; apply: contraL => /eqP->.
Qed.


(**
#</div>#

#</div>#
--------------------------------------------------------
#<div class="slide">#
** Forward reasoning
   - have
   - have :=
   - have + views
   - do I need eqType here?


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
Lemma all_count (T : eqType) (a : pred T) s :
  all a s = (count a s == size s).
Proof.
elim: s => //= x s.
have EM_a : a x || ~~ a x.
  by exact: orbN.
move: EM_a => /orP EM_a. case: EM_a => [-> | /negbTE-> ] //= _.
(*# have /orP[ ax | n_ax ] : a x || ~~ a x by case: (a x). #*)
(*# Search _ count size in seq. #*)
by rewrite add0n eqn_leq andbC ltnNge count_size.
(*# have := boolP (a x). #*)
Qed.

(**
#</div>#
#</div>#
--------------------------------------------------------
--------------------------------------------------------
#<div class="slide">#
** Spec lemmas
   - Inductive predicates to drive the proof
#<div>#*)

Module myreflect1.

Inductive reflect (P : Prop) (b : bool) : Prop :=
  | ReflectT (p : P) (e : b = true)
  | ReflectF (np : ~ P) (e : b = false).

Fixpoint eqn m n :=
  match m, n with
  | 0, 0 => true
  | j.+1,k.+1 => eqn j k
  | _, _ => false
  end.
Arguments eqn !m !n.

Axiom eqP : forall m n, reflect (m = n) (eqn m n).

Lemma test_reflect1 m n : ~~ (eqn m n) || (n <= m <= n).
Proof.
case: (eqn m n) => /=.
(*# case: (eqP m n) => [Enm -> | nE_mn ->] /=. #*)
Admitted.

End myreflect1.

(*#
Module myreflect2.

Inductive reflect (P : Prop) : bool-> Prop :=
  | ReflectT (p : P) : reflect P true
  | ReflectF (np : ~ P) : reflect P false.

Fixpoint eqn m n :=
  match m, n with
  | 0, 0 => true
  | j.+1,k.+1 => eqn j k
  | _, _ => false
  end.
Arguments eqn !m !n.

Axiom eqP : forall m n, reflect (m = n) (eqn m n).
Arguments eqP {m n}.

Lemma test_reflect1 m n : ~~ (eqn m n) || (n <= m <= n).
Proof.
case: (@eqP m n) => [Enm | nE_mn ] /=.
by case: eqP => [->|] //=; rewrite leqnn.
Qed.

End myreflect2.

Check (_ =P _).
Check eqP.

#*)

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
--------------------------------------------------------
#<div class="slide">#
** References for this lesson:
  - SSReflect #<a href="https://hal.inria.fr/inria-00258384">manual</a>#
  - documentation of the
       #<a href="http://math-comp.github.io/math-comp/htmldoc/libgraph.html">library</a>#
    - in particular #<a href="http://math-comp.github.io/math-comp/htmldoc/mathcomp.ssreflect.seq.html">seq</a>#

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


