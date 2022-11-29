From elpi Require Import elpi.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Implicit Type p q r : bool.
Implicit Type m n a b c : nat.

(** *** Exercise 1:
    - use no lemma to prove the following statement
*)
Lemma orbC p q : p || q = q || p.
(*D*)Proof. by case: p; case: q. Qed.

(** *** Exercise 2:
   - look up what [==>] is check if there are relevant views
   - prove that as you like
*)
Lemma Peirce p q : ((p ==> q) ==> p) ==> p.
(*D*)Proof. by case: p; case: q. Qed. 

(** *** Exercise 3:
    - look for lemmas supporting contrapositive reasoning
*)
Lemma bool_gimmics1 a : a != a.-1 -> a != 0.
(*D*)Proof.
(*D*)apply: contra.
(*D*)move => /eqP Ha.
(*D*)by rewrite Ha.
(*A*)Qed.

(** *** Exercise 4:
    - what is [(+)] ?
    - find the right view to prove this statement
    - now find another proof without the view
*)
Lemma find_me p q :  ~~ p = q -> p (+) q.
(*D*)Proof.
(*D*)move=> Hq.
(*D*)by rewrite -Hq addbN negb_add eqxx.
(*A*)Qed.

(** *** Exercise 5:
   - it helps to find out what is behind [./2] and [.*2] in order to [Search]
   - any proof would do, but there is one not using [implyP]
*)
Lemma view_gimmics1 p a b : p -> (p ==> (a == b.*2)) -> a./2 = b.
(*D*)Proof.
(*D*)move=> Hp.
(*D*)rewrite Hp.
(*D*)move=> /eqP Hq.
(*D*)by rewrite Hq doubleK.
(*A*)Qed.


(** *** Exercise 6:
    - prove that using [case:]
    - then prove that without using [case:]
*)
Lemma bool_gimmics2 p q r : ~~ p && (r == q) -> q ==> (p || r).
(*D*)Proof.
(*D*)move=> /andP[Hp Hr].
(*D*)move: Hp.
(*D*)move=> /negbTE Hp.
(*D*)rewrite Hp.
(*D*)move: Hr.
(*D*)move=> /eqP Hq.
(*D*)rewrite Hq.
(*D*)exact: implybb.
(*A*)Qed.

(** *** Exercise 7:
    - look up the definition of [iter]
    - prove this satement by induction
*)
Lemma iterSr A n (f : A -> A) x : iter n.+1 f x = iter n f (f x).
(*D*)Proof. by elim: n => [//|n IH /=]; rewrite -IH. Qed.

(** *** Exercise 8:
   - the only tactics allowed are [rewrite] and [by]
   - use [Search] to find the relevant lemmas (all are good but for
     [ltn_neqAle]) or browse the #<a href="https://math-comp.github.io/htmldoc_1_15_0/mathcomp.ssreflect.ssrnat.html">online doc</a>#
   - proof sketch:
<<
        m < n = ~~ (n <= m)
              = ~~ (n == m || n < m)
              = n != m && ~~ (n < m)
              = ...
>> *)
Lemma ltn_neqAle m n : (m < n) = (m != n) && (m <= n).
(*D*)Proof. by rewrite ltnNge leq_eqVlt negb_or -leqNgt eq_sym. Qed.

