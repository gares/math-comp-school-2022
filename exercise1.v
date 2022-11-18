From mathcomp Require Import all_ssreflect.

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
(*D*)Proof. by apply: contra => /eqP->. Qed.

(** *** Exercise 4:
    - what is [(+)] ?
    - find the right view to prove this statement
    - now find another proof without the view
*)
Lemma find_me p q :  ~~ p = q -> p (+) q.
(*D*)Proof. by move=> <-; rewrite addbN negb_add eqxx. Qed.

(** *** Exercise 5:
   - it helps to find out what is behind [./2] and [.*2] in order to [Search]
   - any proof would do, but there is one not using [implyP]
*)
Lemma view_gimmics1 p a b : p -> (p ==> (a == b.*2)) -> a./2 = b.
(*D*)Proof. by move=> -> /eqP->; exact: doubleK. Qed.


(** *** Exercise 6:
    - prove that using [case:]
    - then prove that without using case:
*)
Lemma bool_gimmics2 p q r : ~~ p && (r == q) -> q ==> (p || r).
(*D*)Proof. by move=> /andP[/negbTE-> /eqP->]; exact: implybb. Qed.

(** *** Exercise 7:
    - look up the definition of [iter]
    - prove this satement by induction
*)
Lemma iterSr A n (f : A -> A) x : iter n.+1 f x = iter n f (f x).
(*D*)Proof. by elim: n => //= n <-. Qed.

(** *** Exercise 8:
    - look up the definition of [iter] (note there is an accumulator varying
      during recursion)
    - prove the following statement by induction
*)
Lemma iter_predn m n : iter n predn m = m - n.
(*D*)Proof. by elim: n m => /= [|n IHn] m; rewrite ?subn0 // IHn subnS. Qed.

(** *** Exercise 9:
   - the only tactics allowed are [rewrite] and [by]
   - use [Search] to find the relevant lemmas (all are good but for
     [ltn_neqAle]) or browse the #<a href="http://math-comp.github.io/math-comp/htmldoc/mathcomp.ssreflect.ssrnat.html">online doc</a>#
   - proof sketch:
<<
        m < n = ~~ (n <= m)
              = ~~ (n == m || n < m)
              = n != m && ~~ (n < m)
              = ...
>> *)
Lemma ltn_neqAle m n : (m < n) = (m != n) && (m <= n).
(*D*)Proof. by rewrite ltnNge leq_eqVlt negb_or -leqNgt eq_sym. Qed.

(** *** Exercise 10:
  - there is no need to prove [reflect] with [iffP]: here just use [rewrite] and [apply]
  - check out the definitions and theory of [leq] and [maxn]
  - proof sketch:
<<
   n <= m = n - m == 0
          = m + n - m == m + 0
          = maxn m n == m
>> *)
Lemma maxn_idPl m n : reflect (maxn m n = m) (m >= n).
(*D*)Proof. by rewrite -subn_eq0 -(eqn_add2l m) addn0 -maxnE; apply: eqP. Qed.

