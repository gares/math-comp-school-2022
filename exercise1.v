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
(*D*)(* proof by truth table *)
(*D*)Proof. by case: p; case: q. Qed.

(** *** Exercise 2:
   - look up what [==>] is check if there are relevant views
   - prove that as you like
*)
Lemma Peirce p q : ((p ==> q) ==> p) ==> p.
(*D*)(* we have classical logic *)
(*D*)Proof. by case: p; case: q. Qed. 

(** *** Exercise 3:
    - look for lemmas supporting contrapositive reasoning
*)
Lemma bool_gimmics1 a : a != a.-1 -> a != 0.
(*D*)(* Search "contra", and use /eqP *)
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
(*D*)(* Locate "(+)", Seach addb *)
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
(*D*)(* Views, /andP[], move: ... gimmicks *)
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

(** Exercise 8:
    - induction on lists
*)
Lemma mem_cat (T : eqType) (x : T) s1 s2 :
  (x \in s1 ++ s2) = (x \in s1) || (x \in s2).
Proof.
(*D*)(* rewrite inE, // and /= *)
(*D*)elim: s1 => [//|y s1 IHs /=].
(*D*)by rewrite !inE /= -orbA -IHs.
(*A*)Qed.

