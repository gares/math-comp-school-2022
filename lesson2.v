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
(* true : bool *)

Compute 2 == 3.
(* false : bool *)

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

Check addn 2 3.
(* 2 + 3 : nat *)

Compute 2 + 3.
(* 5 : nat *)

Goal forall m n, m.+1 + n = (m + n).+1.
Proof.
move=> m n.
by [].
Qed.

Search (_.+1 + _ = _.+1) in ssrnat.
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

Search (_ + _.+1 = _.+1) in ssrnat.
(*
addn1: forall n : nat, n + 1 = n.+1
addnS: forall m n : nat, m + n.+1 = (m + n).+1
addn2: forall m : nat, m + 2 = m.+2
addn3: forall m : nat, m + 3 = m.+3
addn4: forall m : nat, m + 4 = m.+4
*)

Search (_.+1 + _ = _ + _.+1) in ssrnat.
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

Check subn 3 2.
(* 3 - 2 : nat *)

Compute 3 - 2.
(* 1 : nat *)

Compute 3 - 4.
(* 0 : nat *)

Goal forall n, 0 - n = 0.
Proof.
move=> n.
by [].
Qed.

Search left_zero subn in ssrnat.
(* sub0n: left_zero 0 subn *)

Goal forall n, n - 0 = n.
Proof.
case => [|n].
- by [].
by [].
Qed.

Search (_.+1 - _.+1 = _) in ssrnat.
(* sub0n: left_zero 0 subn *)

(**
----------------------------------------------------------
#</div>#
#</div>#
*)

(**
----------------------------------------------------------
#<div class="slide">#
** Natural Numbers  
  Order 
  
#<div>#
*)

Check leq.
(* nat -> nat -> bool *)

Check 0 <= 2.
(* 0 <= 2 : bool *)

Compute (0 <= 2).
(* true : bool *)

Print leq.
(* leq = fun m n : nat => m - n == 0
     : nat -> nat -> bool
*)

(**
#</div>#

  One definition several notations  

#<div>#
  
*)

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

Search (?_1 <= ?_1.+1) in ssrnat.
(* eqnSn: forall n : nat, n <= n.+1 *)

(**
#</div>#

  Reflexivity  

#<div>#
  
*)

Search (?_1 <= ?_1) in ssrnat.
(*
leqnn: forall n : nat, n <= n
ltnSn: forall n : nat, n < n.+1
*)

(**
#</div>#

  Antisymmetry
 
#<div>#
  
*)

Search (~~ _) (_ <= _) in ssrnat.
(*
ltnNge: forall m n : nat, (m < n) = ~~ (n <= m)
leqNgt: forall m n : nat, (m <= n) = ~~ (n < m)
lt0n_neq0: forall [n : nat], 0 < n -> n != 0
ltnNleqif: forall [x y : nat] [C : bool], x <= y ?= iff ~~ C -> (x < y) = C
ltn_leqif: forall [a b : nat] [C : bool], a <= b ?= iff C -> (a < b) = ~~ C
lt0n: forall n : nat, (0 < n) = (n != 0)
eqn0Ngt: forall n : nat_eqType, (n == 0) = ~~ (0 < n)
contraNleq: forall [b : bool] [m n : nat], (n < m -> b) -> ~~ b -> m <= n
contra_leqT: forall [b : bool] [m n : nat], (~~ b -> m < n) -> n <= m -> b
contra_ltnT: forall [b : bool] [m n : nat], (~~ b -> m <= n) -> n < m -> b
contraTleq: forall [b : bool] [m n : nat], (n < m -> ~~ b) -> b -> m <= n
contraNltn: forall [b : bool] [m n : nat], (n <= m -> b) -> ~~ b -> m < n
contra_ltnN: forall [b : bool] [m n : nat], (b -> m <= n) -> n < m -> ~~ b
contraTltn: forall [b : bool] [m n : nat], (n <= m -> ~~ b) -> b -> m < n
contra_leqN: forall [b : bool] [m n : nat], (b -> m < n) -> n <= m -> ~~ b
*)

Search (_ == _ = _) (_ <= _) in ssrnat.
(*
subn_eq0: forall m n : nat, (m - n == 0) = (m <= n)
eqn0Ngt: forall n : nat_eqType, (n == 0) = ~~ (0 < n)
eqn_leq: forall m n : nat_eqType, (m == n) = (m <= n <= m)
ltn_eqF: forall [m n : nat], m < n -> (m == n) = false
gtn_eqF: forall [m n : nat], m < n -> (n == m) = false
neq0_lt0n: forall [n : nat_eqType], (n == 0) = false -> 0 < n
expn_eq0: forall m e : nat, (m ^ e == 0) = (m == 0) && (0 < e)
eqn_pmul2l: forall [m n1 n2 : nat], 0 < m -> (m * n1 == m * n2) = (n1 == n2)
eqn_exp2r: forall (m n : nat) [e : nat], 0 < e -> (m ^ e == n ^ e) = (m == n)
eqn_pmul2r: forall [m n1 n2 : nat], 0 < m -> (n1 * m == n2 * m) = (n1 == n2)
eqn_exp2l:
  forall [m : nat] (n1 n2 : nat), 1 < m -> (m ^ n1 == m ^ n2) = (n1 == n2)
*)

(**
#</div>#

  Transitivity
 
#<div>#
  
*)

Search nat "trans" in ssrnat.
(*
leq_trans: forall [n m p : nat], m <= n -> n <= p -> m <= p
leqif_trans:
  forall [m1 m2 m3 : nat] [C12 C23 : bool],
  m1 <= m2 ?= iff C12 -> m2 <= m3 ?= iff C23 -> m1 <= m3 ?= iff C12 && C23
leq_ltn_trans: forall [n m p : nat], m <= n -> n < p -> m < p
ltn_trans: forall [n m p : nat], m < n -> n < p -> m < p
*)

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

(**
#</div>#

  Proof by case
 
#<div>#
  
*)

Goal forall (m : nat) (n : nat) (P : nat -> bool), 
   (n <= m -> P n) -> (m < n -> P n) -> P n.
Proof.
move=> m n P LP GP.
case: (leqP n m).
  by apply: LP.
by apply: GP.
Qed.

Goal forall (m : nat) (n : nat) (P : nat -> bool), 
   (n < m -> P n) -> (m < n -> P n) -> (n = m -> P n) -> P n.
Proof.
move=> m n P LP GP EP.
case: (ltngtP n m).
- by apply: LP.
- by apply: GP.
by apply: EP.
Qed.

Check leq_eqVlt.
(* leq_eqVlt
	 : forall m n : nat, (m <= n) = (m == n) || (m < n)
*)

Goal forall (P : pred nat) m n, P n ->
    (m < n -> P m) -> m <= n -> P m.
Proof.
move=> P m n Pn PL.
rewrite leq_eqVlt.
move=> /orP[|].
  move/eqP->.
  by [].
exact: PL.
Qed.

Goal forall (P : pred nat) m n, P n ->
    (m < n -> P m) -> m <= n -> P m.
Proof.
move=> P m n Pn GP.
case: ltngtP.
- move=> mLn _.
  by apply: GP.
- by [].
move=> -> _.
exact: Pn.
Qed.

(**
#</div>#

  Addition
  
#<div>#
  
*)

Search (_ <= _ + _) in ssrnat.
(*
leq_addr: forall m n : nat, n <= n + m
leq_addl: forall m n : nat, n <= m + n
leq_add2r: forall p m n : nat, (m + p <= n + p) = (m <= n)
leq_add2l: forall p m n : nat, (p + m <= p + n) = (m <= n)
ltn_addl: forall [m n : nat] (p : nat), m < n -> m < p + n
leq_subLR: forall m n p : nat, (m - n <= p) = (m <= n + p)
ltn_addr: forall [m n : nat] (p : nat), m < n -> m < n + p
ltn_add2r: forall p m n : nat, (m + p < n + p) = (m < n)
ltn_add2l: forall p m n : nat, (p + m < p + n) = (m < n)
leq_add:
  forall [m1 m2 n1 n2 : nat], m1 <= n1 -> m2 <= n2 -> m1 + m2 <= n1 + n2
addn_gt0: forall m n : nat, (0 < m + n) = (0 < m) || (0 < n)
ltn_subLR: forall [m n : nat] (p : nat), n <= m -> (m - n < p) = (m < n + p)
ltn_psubLR: forall (m n : nat) [p : nat], 0 < p -> (m - n < p) = (m < n + p)
*)

Goal forall m n, n <= m -> n.*2 <= m + n.
Proof.
move=> m n nLm.
rewrite -addnn.
rewrite leq_add2r.
by [].
Qed.

(**
#</div>#

  Multiplication
  
#<div>#
  
*)

Search  _ (_ <= _ * _) in ssrnat.
(*
leq_pmulr: forall (m : nat) [n : nat], 0 < n -> m <= m * n
leq_pmull: forall (m : nat) [n : nat], 0 < n -> m <= n * m
leq_mul:
  forall [m1 m2 n1 n2 : nat], m1 <= n1 -> m2 <= n2 -> m1 * m2 <= n1 * n2
ltn_Pmull: forall [m n : nat], 1 < n -> 0 < m -> m < n * m
ltn_Pmulr: forall [m n : nat], 1 < n -> 0 < m -> m < m * n
muln_gt0: forall m n : nat, (0 < m * n) = (0 < m) && (0 < n)
ltn_mul: forall [m1 m2 n1 n2 : nat], m1 < n1 -> m2 < n2 -> m1 * m2 < n1 * n2
leq_pmul2l: forall [m n1 n2 : nat], 0 < m -> (m * n1 <= m * n2) = (n1 <= n2)
leq_pmul2r: forall [m n1 n2 : nat], 0 < m -> (n1 * m <= n2 * m) = (n1 <= n2)
leq_mul2r: forall m n1 n2 : nat, (n1 * m <= n2 * m) = (m == 0) || (n1 <= n2)
leq_mul2l: forall m n1 n2 : nat, (m * n1 <= m * n2) = (m == 0) || (n1 <= n2)
ltn_mul2l: forall m n1 n2 : nat, (m * n1 < m * n2) = (0 < m) && (n1 < n2)
ltn_mul2r: forall m n1 n2 : nat, (n1 * m < n2 * m) = (0 < m) && (n1 < n2)
ltn_pmul2r: forall [m n1 n2 : nat], 0 < m -> (n1 * m < n2 * m) = (n1 < n2)
ltn_pmul2l: forall [m n1 n2 : nat], 0 < m -> (m * n1 < m * n2) = (n1 < n2)
*)

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

Search (_ <= _ ?= iff _) (_ && _) in ssrnat.
(*
eqif_trans:
  forall [m1 m2 m3 : nat] [C12 C23 : bool],
  m1 <= m2 ?= iff C12 -> m2 <= m3 ?= iff C23 -> m1 <= m3 ?= iff C12 && C23
leqif_add:
  forall [m1 n1 : nat] [C1 : bool] [m2 n2 : nat] [C2 : bool],
  m1 <= n1 ?= iff C1 ->
  m2 <= n2 ?= iff C2 -> m1 + m2 <= n1 + n2 ?= iff C1 && C2
leqif_mul:
  forall [m1 n1 : nat] [C1 : bool] [m2 n2 : nat] [C2 : bool],
  m1 <= n1 ?= iff C1 ->
  m2 <= n2 ?= iff C2 -> m1 * m2 <= n1 * n2 ?= iff (n1 * n2 == 0) || C1 && C2
*)

(**
----------------------------------------------------------
#</div>#
#</div>#
*)

(**
----------------------------------------------------------
#<div class="slide">#
** Natural Numbers  

  Division 
  
#<div>#
*)

Check (modn 21 2).
(* 21 %% 2 : nat *)

Compute 21 %% 2.
(* 1 : nat *)

Check (divn 21 2).
(* 21 %/ 2 : nat *)

Compute 21 %/ 2.
(* 10 : nat *)

Check (dvdn 2 21).

Compute 2 %| 21.

Print dvdn.
(*
dvdn = fun d m : nat => m \%\% d == 0
	 : nat -> nat -> bool
*)

Search (_ %| _ + _) in div.
(* 
dvdn_add: forall [d m n : nat], d %| m -> d %| n -> d %| m + n
dvdn_add_eq: forall [d m n : nat], d %| m + n -> (d %| m) = (d %| n)
dvdn_addl: forall [n d : nat] (m : nat), d %| n -> (d %| m + n) = (d %| m)
dvdn_addr: forall [m d : nat] (n : nat), d %| m -> (d %| m + n) = (d %| n)
Bezoutl:
  forall [m : nat] (n : nat),
  0 < m -> {a : nat | a < m & m %| gcdn m n + a * n}
Bezoutr:
  forall (m : nat) [n : nat],
  0 < n -> {a : nat | a < n & n %| gcdn m n + a * m}
*)

Search ((_ + _) %/ _) in div.
(*
divnDr:
  forall (m : nat) [n d : nat], d %| n -> (m + n) %/ d = m %/ d + n %/ d
divnDl:
  forall [m : nat] (n : nat) [d : nat],
  d %| m -> (m + n) %/ d = m %/ d + n %/ d
leq_divDl: forall p m n : nat, (m + n) %/ p <= m %/ p + n %/ p + 1
divnDMl: forall (q m : nat) [d : nat], 0 < d -> (m + q * d) %/ d = m %/ d + q
divnMDl: forall (q m : nat) [d : nat], 0 < d -> (q * d + m) %/ d = q + m %/ d
divnD:
  forall (m n : nat) [d : nat],
  0 < d -> (m + n) %/ d = m %/ d + n %/ d + (d <= m %% d + n %% d)
*)

Search (?_1 %/ ?_1) in div.
(* divnn: forall d : nat, d %/ d = (0 < d) *)

Compute 0 %/ 0.
(* 0 : nat *)

Search (_ %| _ * _) in div.
(* 
dvdn_mulr: forall [d m : nat] (n : nat), d %| m -> d %| m * n
dvdn_mull: forall [d : nat] (m : nat) [n : nat], d %| n -> d %| m * n
dvdn_mul:
  forall [d1 d2 m1 m2 : nat], d1 %| m1 -> d2 %| m2 -> d1 * d2 %| m1 * m2
Gauss_dvdl:
  forall [m : nat] (n : nat) [p : nat],
  coprime m p -> (m %| n * p) = (m %| n)
Gauss_dvdr:
  forall [m n : nat] (p : nat), coprime m n -> (m %| n * p) = (m %| p)
dvdn_pmul2l: forall [p d m : nat], 0 < p -> (p * d %| p * m) = (d %| m)
dvdn_pmul2r: forall [p d m : nat], 0 < p -> (d * p %| m * p) = (d %| m)
dvdn_divLR:
  forall [p d : nat] (m : nat),
  0 < p -> p %| d -> (d %/ p %| m) = (d %| m * p)
*)

Search ((_ * _) %/ _) in div.
(*
divnA: forall (m : nat) [n p : nat], p %| n -> m %/ (n %/ p) = (m * p) %/ n
muln_divA:
  forall [d : nat] (m : nat) [n : nat], d %| n -> m * (n %/ d) = (m * n) %/ d
divn_mulAC: forall [d m : nat] (n : nat), d %| m -> m %/ d * n = (m * n) %/ d
mulKn: forall (m : nat) [d : nat], 0 < d -> (d * m) %/ d = m
mulnK: forall (m : nat) [d : nat], 0 < d -> (m * d) %/ d = m
divnMl: forall [p m d : nat], 0 < p -> (p * m) %/ (p * d) = m %/ d
divnMr: forall [p m d : nat], 0 < p -> (m * p) %/ (d * p) = m %/ d
*)

(**
----------------------------------------------------------
#</div>#
#</div>#
*)

(**
----------------------------------------------------------
#<div class="slide">#
** Natural Numbers  

  Odd 
  
#<div>#
*)

Compute odd 4.
(* false : bool *)

Compute odd 5.
(* true : bool *)

Print odd.
(* 
odd = 
fix odd (n : nat) : bool :=
  match n with
  | 0 => false
  | n'.+1 => ~~ odd n'
  end
	 : nat -> bool
*)

Search odd (_ %% _) in div.
(* 
modn2: forall m : nat, m %% 2 = odd m
odd_mod: forall (m : nat) [d : nat], odd d = false -> odd (m %% d) = odd m
*)

(**
----------------------------------------------------------
#</div>#
#</div>#
*)

(**
----------------------------------------------------------
#<div class="slide">#
** Natural Numbers  

  Gcd and Lcm
  
#<div>#
*)

Compute gcdn 42 49.
(* 7 : nat *)

Compute lcmn 42 49.
(* 294 : nat *)

Search gcdn lcmn in div.
(* 
muln_lcm_gcd: forall m n : nat, lcmn m n * gcdn m n = m * n
*)

Search gcdn (_ * _) in div.
(* 
gcdnMr: forall n m : nat, gcdn n (n * m) = n
gcdnMl: forall n m : nat, gcdn n (m * n) = n
muln_lcm_gcd: forall m n : nat, lcmn m n * gcdn m n = m * n
gcdnMDl: forall k m n : nat, gcdn m (k * m + n) = gcdn m n
muln_divCA_gcd: forall n m : nat, n * (m %/ gcdn n m) = m * (n %/ gcdn n m)
Gauss_gcdl:
  forall [p : nat] (m : nat) [n : nat],
  coprime p n -> gcdn p (m * n) = gcdn p m
Gauss_gcdr:
  forall [p m : nat] (n : nat), coprime p m -> gcdn p (m * n) = gcdn p n
Bezoutl:
  forall [m : nat] (n : nat),
  0 < m -> {a : nat | a < m & m %| gcdn m n + a * n}
Bezoutr:
  forall (m : nat) [n : nat],
  0 < n -> {a : nat | a < n & n %| gcdn m n + a * m}
EgcdnSpec:
  forall [m n km kn : nat],
  km * m = kn * n + gcdn m n -> kn * gcdn m n < m -> egcdn_spec m n (km, kn)
*)

(**
----------------------------------------------------------
#</div>#
#</div>#
*)

(**
----------------------------------------------------------
#<div class="slide">#
** Natural Numbers  

  Coprime & Prime 
  
#<div>#
*)

Check coprime.
(* coprime : nat -> nat -> bool *)

Compute coprime 3 5.
(* true : bool *)

Compute coprime 21 7.
(* false : true *)

Print coprime.
(* 
coprime = fun m n : nat => gcdn m n == 1
	 : nat -> nat -> bool
*)

Search coprime (_ %| _) in div prime.
(*
coprime_dvdr: forall [m n p : nat], m %| n -> coprime p n -> coprime p m
coprime_dvdl: forall [m n p : nat], m %| n -> coprime n p -> coprime m p
prime_coprime:
  forall [p : nat] (m : nat), prime p -> coprime p m = ~~ (p %| m)
Gauss_dvdr:
  forall [m n : nat] (p : nat), coprime m n -> (m %| n * p) = (m %| p)
Gauss_dvdl:
  forall [m : nat] (n : nat) [p : nat],
  coprime m p -> (m %| n * p) = (m %| n)
Gauss_dvd:
  forall [m n : nat] (p : nat),
  coprime m n -> (m * n %| p) = (m %| p) && (n %| p)
*)

Check prime.
(* prime : nat -> bool *)

Compute prime 21.
(* false : bool *)

Compute prime 22.
(* false : bool *)

Compute prime 23.
(* true : bool *)

Print prime.
(*
prime = 
fun p : nat =>
match prime_decomp p with
| [::] => false
| p0 :: l =>
	let (_, n0) := p0 in
    match n0 with
    | 0 => false
    | n1.+1 =>
        match n1 with
        | 0 => match l with
               | [::] => true
               | _ :: _ => false
               end
        | _.+1 => false
        end
    end
end
     : nat -> bool
*)

Compute primes 21.
(* [:: 3, 7] : seq nat *)
Compute primes 22.
(* [:: 2; 11] : seq nat*)

Compute primes 23.
(* [:: 23] : seq nat *)

Check primeP.
(* 
primeP
	 : reflect (1 < ?p /\ (forall d : nat, d %| ?p -> (d == 1) || (d == ?p)))
         (prime ?p)
*)

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

Search prime (_ %| _) in div prime.
(*
Euclid_dvd1: forall [p : nat], prime p -> (p %| 1) = false
prime_coprime:
  forall [p : nat] (m : nat), prime p -> coprime p m = ~~ (p %| m)
dvdn_prime2: forall [p q : nat], prime p -> prime q -> (p %| q) = (p == q)
pdivP: forall [n : nat], 1 < n -> {p : nat | prime p & p %| n}
Euclid_dvdM:
  forall (m n : nat) [p : nat],
  prime p -> (p %| m * n) = (p %| m) || (p %| n)
p'natE: forall [p : nat] (n : nat), prime p -> (p^').-nat n = ~~ (p %| n)
Euclid_dvdX:
  forall (m n : nat) [p : nat], prime p -> (p %| m ^ n) = (p %| m) && (0 < n)
dvdn_pfactor:
  forall [p : nat] (d n : nat),
  prime p -> reflect (exists2 m : nat, m <= n & d = p ^ m) (d %| p ^ n)
lognE:
  forall p m : nat,
  logn p m =
  (if [&& prime p, 0 < m & p %| m] then (logn p (m %/ p)).+1 else 0)
pfactor_dvdn:
  forall [p : nat] (n : nat) [m : nat],
  prime p -> 0 < m -> (p ^ n %| m) = (n <= logn p m)
prime_nt_dvdP:
  forall [d : nat_eqType] [p : nat],
  prime p -> d != 1 -> reflect (d = p) (d %| p)
pnatP:
  forall (pi : nat_pred) [n : nat],
  0 < n ->
  reflect (forall p : nat, prime p -> p %| n -> p \in pi) (pi.-nat n)
mem_primes:
  forall (p : nat_eqType) (n : nat),
  (p \in primes n) = [&& prime p, 0 < n & p %| n]
primePn:
  forall {n : nat},
  reflect (n < 2 \/ (exists2 d : nat, 1 < d < n & d %| n)) (~~ prime n)
logn_count_dvd:
  forall [p : nat] (n : nat),
  prime p -> logn p n = \sum_(1 <= k < n) (p ^ k %| n)
primePns:
  forall {n : nat},
  reflect (n < 2 \/ (exists p : nat, [/\ prime p, p ^ 2 <= n & p %| n]))
	(~~ prime n)
primeP:
  forall {p : nat},
  reflect (1 < p /\ (forall d : nat, d %| p -> xpred2 1 p d)) (prime p)
Euclid_dvd_prod:
  forall [I : Type] (r : seq I) (P : pred I) (f : I -> nat) [p : nat],
  prime p ->
  (p %| \prod_(i <- r | P i) f i) = \big[orb/false]_(i <- r | P i) (p %| f i)
mem_prime_decomp:
  forall [n : nat] [p e : nat_eqType],
  (p, e) \in prime_decomp n -> [/\ prime p, 0 < e & p ^ e %| n]
*)

Check logn.
(* logn : nat -> nat -> nat*)

Compute logn 3 8.
(* 0 : nat *)
Compute logn 3 9.
(* 2 : nat *)

Search logn in prime.
(* 
logn0: forall p : nat, logn p 0 = 0
logn1: forall p : nat, logn p 1 = 0
pfactor_dvdnn: forall p n : nat, p ^ logn p n %| n
logn_part: forall p m : nat, logn p m`_p = logn p m
logn_coprime: forall [p m : nat], coprime p m -> logn p m = 0
lognX: forall p m n : nat, logn p (m ^ n) = n * logn p m
p_part: forall p n : nat, n`_p = p ^ logn p n
pfactorK: forall [p : nat] (n : nat), prime p -> logn p (p ^ n) = n
pfactor_gt0: forall p n : nat, 0 < p ^ logn p n
ltn_logl: forall (p : nat) [n : nat], 0 < n -> logn p n < n
ltn_log0: forall [p n : nat], n < p -> logn p n = 0
logn_Gauss:
  forall [p m : nat] (n : nat), coprime p m -> logn p (m * n) = logn p n
pfactorKpdiv:
  forall [p : nat] (n : nat), prime p -> logn (pdiv (p ^ n)) (p ^ n) = n
logn_prime: forall (p : nat) [q : nat], prime q -> logn p q = (p == q)
logn_div:
  forall (p : nat) [m n : nat],
  m %| n -> logn p (n %/ m) = logn p n - logn p m
dvdn_leq_log:
  forall (p : nat) [m n : nat], 0 < n -> m %| n -> logn p m <= logn p n
prime_decompE:
  forall n : nat, prime_decomp n = [seq (p, logn p n) | p <- primes n]
eqn_from_log:
  forall [m n : nat], 0 < m -> 0 < n -> logn^~ m =1 logn^~ n -> m = n
logn_gt0: forall p n : nat, (0 < logn p n) = (p \in primes n)
lognE:
  forall p m : nat,
  logn p m =
  (if [&& prime p, 0 < m & p %| m] then (logn p (m %/ p)).+1 else 0)
logn_lcm:
  forall (p : nat) [m n : nat],
  0 < m -> 0 < n -> logn p (lcmn m n) = maxn (logn p m) (logn p n)
lognM:
  forall (p : nat) [m n : nat],
  0 < m -> 0 < n -> logn p (m * n) = logn p m + logn p n
logn_gcd:
  forall (p : nat) [m n : nat],
  0 < m -> 0 < n -> logn p (gcdn m n) = minn (logn p m) (logn p n)
pfactor_dvdn:
  forall [p : nat] (n : nat) [m : nat],
  prime p -> 0 < m -> (p ^ n %| m) = (n <= logn p m)
pfactor_coprime:
  forall [p n : nat],
  prime p -> 0 < n -> {m : nat | coprime p m & n = m * p ^ logn p n}
logn_count_dvd:
  forall [p : nat] (n : nat),
  prime p -> logn p n = \sum_(1 <= k < n) (p ^ k %| n)
totientE:
  forall [n : nat],
  0 < n -> totient n = \prod_(p <- primes n) (p.-1 * p ^ (logn p n).-1)
widen_partn:
  forall [m : nat] (pi : nat_pred) [n : nat],
  n <= m -> n`_pi = \prod_(0 <= p < m.+1 | p \in pi) p ^ logn p n
eq_partn_from_log:
  forall [m n : nat] [pi : nat_pred],
  0 < m -> 0 < n -> {in pi, logn^~ m =1 logn^~ n} -> m`_pi = n`_pi
*)

(**
----------------------------------------------------------
#</div>#
#</div>#
*)

