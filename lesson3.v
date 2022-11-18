From mathcomp Require Import all_ssreflect. 
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** 

----
** Lesson 4 Arithmetics
  - Order
  - Division
  - Primality

*)


(**
  ** Reminder  
*)

Check nat.

Print nat.

Check O.

Check S O.

Check S (S O).

Compute 3.+1.

(**  Proof by case *)

Goal forall (P : pred nat), 
     (P 0) -> (forall n, P n.+1) -> forall n, P n.
Proof.
move=> P H0 SH n.
case: n => [|n].
  exact: H0.
by apply: SH.
Qed.

(**  Proof by induction *)

Goal forall (P : pred nat), 
     (P 0) -> (forall n, P n -> P n.+1) -> forall n, P n.
Proof.
move=> P H0 SH n.
elim: n => [|n IH].
  exact: H0.
by apply: SH.
Qed.


(** Eqtype *)

Check eqn.

Compute 1 == 1.

Compute 2 == 3.

Print eqn.

Goal forall m n, m.+1 == n.+1 -> m == n.
Proof.
move=> m n mEn.
exact: mEn.
Qed.
 
(** Addition *)

Check addn.

Check addn 2 3.

Compute 2 + 3.

Goal forall m n, m.+1 + n = (m + n).+1.
Proof.
move=> m n.
by [].
Qed.

Search _ (_.+1 + _ = _.+1) in ssrnat.

Goal forall m n, m + n.+1 = (m + n).+1.
Proof.
move=> m n.
elim: m => [|m IH].
  by [].
rewrite !addSn.
rewrite IH.
by [].
Qed.

Search _ (_ + _.+1 = _.+1) in ssrnat.

Search _ (_.+1 + _ = _ + _.+1) in ssrnat.

(** Subtraction *)

Check subn.

Check subn 3 2.

Compute (3 - 2).

Compute 3 - 4.

Goal forall n, 0 - n = 0.
Proof.
move=> n.
by [].
Qed.

Search _ left_zero subn in ssrnat.

Goal forall n, n - 0 = n.
Proof.
case => [|n].
- by [].
by [].
Qed.

Search _ (_.+1 - 0 = _) in ssrnat.
Search _ (_.+1 - _.+1 = _) in ssrnat.


(** 
    Order 
*)


Check leq.

Check (0 <= 2).

Compute (0 <= 2).

Print leq.

(** One overloaded definition *)

Goal forall m n, m >= n -> n <= m.
Proof.
by [].
Qed.

Goal forall m n, m.+1 <= n -> m < n.
Proof.
by [].
Qed.

Goal forall n, n <= n.+1.
Proof.
elim=> [|n IH].
  by [].
exact: IH.
Qed.

Search _ (?_1 <= ?_1.+1) in ssrnat.

(** Reflexivity *)

Search _ (?_1 <= ?_1) in ssrnat.

(** Antisymmetric *)

Search _ (~~ _) (_ <= _) in ssrnat.
Search _ (_ == _) (_ <= _) in ssrnat.

(** Transitivity *)

Search _ nat "trans" in ssrnat.

Goal forall m n p, m < n -> n <= p -> m < p.
Proof.
move=> m n p.
have trans := leq_trans.
have trans_Sm_n := leq_trans (_ : m < n) (_ : n <= p).
by [].
Qed.

Goal forall (P : pred nat), 
      P 0 ->
      (forall m,  (forall n, n <= m -> P n) -> P m.+1) ->
      (forall m, P m).
Proof.
move=> P HC IHs m.
move: (leqnn m).
move: {-2}m.
elim: m => [|m IH].
  by case.
case=> // n nLm.
apply: IHs => k kLn.
apply: IH.
apply: leq_trans kLn nLm.
Qed.

Goal forall a b c,
   a < b -> b < c -> a <= c.
Proof.
move=> a b c aLb bLc.
apply: leq_trans (_ : b <= _).
  by apply: ltnW.
by apply: ltnW.
Qed.

(** Scaling down  *)

Check leq_eqVlt.

Goal forall (P : pred nat) m n, P n ->
    (forall m, m < n -> P m) -> m <= n -> P m.
Proof.
move=> P m n Pn PL.
rewrite leq_eqVlt.
move=> /orP[|].
  move/eqP->.
  by [].
exact: PL.
Qed.

(** Addition *)

Search  _ (_ <= _ + _) in ssrnat.

Goal forall m n, n <= m -> n.*2 <= m + n.
Proof.
move=> m n nLm.
rewrite -addnn.
rewrite leq_add2r.
by [].
Qed.

(** Multiplication *)

Search  _ (_ <= _ * _) in ssrnat.

Goal forall m n, n <= m -> n ^ 2 <= m * n.
Proof.
move=> m n nLm.
rewrite -mulnn.
rewrite leq_mul2r.
rewrite nLm.
rewrite orbT.
by [].
Qed.

(** Conditional comparison **)

Check subset_leqif_cards.

Search _ (_ <= _ ?= iff _) (_ && _) in ssrnat.

(** Division **)

Check (modn 21 2).
Compute 21 %% 2.

Check (divn 21 2).
Compute 21 %/ 2.

Check (dvdn 2 21).
Compute 2 %| 21.

Print dvdn.

Search (_ %| _ + _) in div.

Search ((_ + _) %/ _) in div.

Search (?_1 %/ ?_1) in div.

Compute 0 %/ 0.

Search (_ %| _ * _) in div.

Search ((_ * _) %/ _) in div.

(** odd **)

Compute odd 4.
Compute odd 5.
Print odd.

Search _ odd (_ %% _) in div.

(** gcd & lcm **)

Compute gcdn 42 49.

Compute lcmn 42 49.

Search _ gcdn lcmn in div.

Search _ gcdn (_ * _) in div.

(** Coprime **)

Check coprime.

Compute coprime 3 5.
Compute coprime 21 7.

Print coprime.

Search _ coprime (_ %| _) in div prime.

(** Primality **)

Check prime.

Compute prime 21.

Compute prime 22.

Compute prime 23.

Print prime.

Compute primes 23.

Check primeP.

Goal prime 2.
Proof.
apply/primeP.
split.
  by [].
move=> d.
case: d.
  by [].
case.
  by [].
by case.
Qed.

Search _ prime (_ %| _) in div prime.

Check logn.

Compute logn 3 8.

Compute logn 3 9.

Search _ logn in prime.



