From elpi Require Import elpi.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** 

----------------------------------------------------------
#<div class="slide">#
** Roadmap of the second lesson 

  Playing with basic arithmetics

  - Order
  - Division
  - Primality

#</div>#
----------------------------------------------------------
*)

(**
----------------------------------------------------------
#<div class="slide">#
** Reminder  

  Natural numbers

#<div>#
*)
Check nat.
(* nat : Set *)

Print nat.
(* Inductive nat : Set :=
   O : nat | S : nat -> nat *)

Check O.
(* 0 : nat *)

Check S O.
(* 1 : nat *)

Check S (S O).
(* 2 : nat *)

Check 2.+1.
(* 3 : nat *)

Set Printing All.
Check 4.
(* S (S (S O)) : nat *)

Unset Printing All.
Check 5.
(* 5 : nat *)

(**
#</div></div>#
----------------------------------------------------------
*)

(**
----------------------------------------------------------
#<div class="slide">#
** Reminder  

  Proof by case 

#<div>#
*)

Goal forall (P : pred nat), 
     P 0 -> (forall n, P n.+1) -> forall n, P n.
Proof.
move=> P HP0 HPS n.
case: n => [|n].
  exact: HP0.
by apply: HPS.
Qed.

(**
----------------------------------------------------------
#</div>#
#</div>#
*)

(**
----------------------------------------------------------
#<div class="slide">#
** Reminder  

  Proof by induction 

#<div>#
*)

Goal forall (P : pred nat), 
     P 0 -> (forall n, P n -> P n.+1) -> forall n, P n.
Proof.
move=> P HP0 HPS n.
elim: n => [|n IH].
  exact: HP0.
by apply: HPS.
Qed.

(**
----------------------------------------------------------
#</div>#
#</div>#
*)

(**
----------------------------------------------------------
#<div class="slide">#
** Reminder  

  Eq type 

#<div>#
*)

Check eqn.
(* eqn : nat -> nat -> bool *)

Print eqn.
(* fix eqn (m n : nat) {struct m} : bool :=
   match m with ... end. *)

Compute 1 == 1.
(* false : bool *)

Compute 2 == 3.
(* true : bool *)

Goal forall m n, m.+1 == n.+1 -> m == n.
Proof.
move=> m n mEn.
exact: mEn.
Qed.
(**
----------------------------------------------------------
#</div>#
#</div>#
*)
 

(**
----------------------------------------------------------
#<div class="slide">#
** Natural numbers  

  Addition
#<div>#
*)

Check addn.
(* addn : nat -> nat -> nat *)

Compute 2 + 3.
(* 5 : nat *)

Goal forall m n, m.+1 + n = (m + n).+1.
Proof.
move=> m n.
by [].
Qed.

Search _ (_.+1 + _ = _.+1) in ssrnat.
(*
add1n: forall n : nat, 1 + n = n.+1
addSn: forall m n : nat, m.+1 + n = (m + n).+1
add2n: forall m : nat, 2 + m = m.+2
add3n: forall m : nat, 3 + m = m.+3
add4n: forall m : nat, 4 + m = m.+4
*)

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
(*
addn1: forall n : nat, n + 1 = n.+1
addnS: forall m n : nat, m + n.+1 = (m + n).+1
addn2: forall m : nat, m + 2 = m.+2
addn3: forall m : nat, m + 3 = m.+3
addn4: forall m : nat, m + 4 = m.+4
*)

Search _ (_.+1 + _ = _ + _.+1) in ssrnat.
(* addSnnS: forall m n : nat, m.+1 + n = m + n.+1*)

(**
----------------------------------------------------------
#</div>#
#</div>#
*)

(**
----------------------------------------------------------
#<div class="slide">#
** Natural Numbers  
  Subtraction 
  
#<div>#
*)

Check subn.
(* subn : nat -> nat -> nat *)

Compute 3 - 2.
(* 1 : nat *)

Compute 3 - 4.
(* 0 : nat *)

Goal forall n, 0 - n = 0.
Proof.
move=> n.
by [].
Qed.

Search _ left_zero subn in ssrnat.
(* sub0n: left_zero 0 subn *)

Goal forall n, n - 0 = n.
Proof.
case => [|n].
- by [].
by [].
Qed.

Search _ (_.+1 - _.+1 = _) in ssrnat.
(* sub0n: left_zero 0 subn *)

(**
----------------------------------------------------------
#</div>#
#</div>#
*)


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



