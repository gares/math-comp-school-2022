From elpi Require Import elpi.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Elements *)

Definition elements {A} (f : _ -> A) n :=
  let l := iota 0 n.+1 in zip l (map f l).

(** Triangular number *)
Definition delta n := (n.+1 * n)./2.

Compute elements delta 10.

(** Hints : halfD half_bit_double *)
Lemma deltaS n : delta n.+1 = delta n + n.+1.
Proof.
(*D*)rewrite /delta -addn2 mulnDl mulnC halfD.
(*D*)rewrite !oddM andbF add0n mul2n.
(*D*)by rewrite -{4}(half_bit_double n.+1 false).
(*A*)Qed.

(** Hints   big_ord_recr big_ord_recl big_ord0 *)
Lemma deltaE n : delta n = \sum_(i < n.+1) i.
Proof.
(*D*)elim: n => [|n IH]; first by rewrite big_ord_recl big_ord0.
(*D*)by rewrite big_ord_recr /= -IH deltaS.
(*A*)Qed.

(* Hints half_leq *)
Lemma leq_delta m n : m <= n -> delta m <= delta n.
Proof.
(*D*)by move=> H; apply/half_leq/leq_mul.
(*A*)Qed.

(** Hints sqrnD *)
Lemma delta_square n : (8 * delta n).+1 = n.*2.+1 ^ 2.
Proof.
(*D*)elim: n => // n IH.
(*D*)rewrite deltaS mulnDr -addSn IH.
(*D*)rewrite doubleS -addn1 -addnS -addSn addn1.
(*D*)rewrite sqrnD -addnA /=.
(*D*)congr (_ + _).
(*D*)rewrite mulnS.
(*D*)rewrite [_ * 2]mulSn mulnDr addnA.
(*D*)congr (_ + _).
(*D*)by rewrite mulnCA -muln2 -!mulnA mulnC.
(*A*)Qed.

(**  Triangular root *)
Definition troot n := 
 let l := iota 0 n.+2 in
 (find (fun x => n < delta x) l).-1.

Compute elements troot 10.

Lemma troot_gt0 n : 0 < n -> 0 < troot n.
Proof.
(*D*)by case: n.
(*A*)Qed.

(** Hints before_find find_size size_iota nth_iota *)
Lemma leq_delta_root m : delta (troot m) <= m.
Proof.
(*D*)rewrite /troot leqNgt.
(*D*)set l := iota _ _; set f := (fun _ => _).
(*D*)case E : _.-1 => [|n] //.
(*D*)have  /(before_find 0) : 
(*D*)   (find f l).-1 < find f l by rewrite prednK // E.
(*D*)rewrite E  nth_iota // /f => [->//|].
(*D*)rewrite -[m.+2](size_iota 0) -E prednK; first by apply: find_size.
(*D*)by case: find E.
(*A*)Qed.

(** Hints hasP mem_iota half_bit_double half_leq nth_find nth_iota *)
Lemma ltn_delta_root m : m < delta (troot m).+1.
Proof.
(*D*)rewrite /troot leqNgt.
(*D*)set l := iota _ _; set f := (fun _ => _).
(*D*)have Hfl : has f l.
(*D*)  apply/hasP; exists m.+1; first by rewrite mem_iota leq0n leqnn.
(*D*)  rewrite /f /delta -{1}[m.+1](half_bit_double _ false).
(*D*)  by apply/half_leq; rewrite add0n -mul2n leq_mul2r orbT.
(*D*)have := nth_find 0 Hfl; rewrite {1}/f.
(*D*)case E : _.-1 => [|n] //.
(*D*)  case: find E => // [] [|n] //.
(*D*)  by rewrite nth_iota //=; case: (m).
(*D*)rewrite nth_iota.
(*D*)  by rewrite -E prednK // ltnNge ltnS.
(*D*)by rewrite -(size_iota 0 m.+2) -has_find.
(*A*)Qed.

Lemma leq_root_delta m n : (n <= troot m) = (delta n <= m).
Proof.
(*D*)case: leqP => [/leq_delta/leq_trans->//|dmLn].
(*D*)  apply: leq_delta_root.
(*D*)apply/sym_equal/idP/negP.
(*D*)rewrite -ltnNge.
(*D*)by apply: leq_trans (ltn_delta_root _) (leq_delta dmLn).
(*A*)Qed.

Lemma leq_troot m n : m <= n -> troot m <= troot n.
Proof.
(*D*)by move=> mLn; rewrite leq_root_delta (leq_trans (leq_delta_root _)).
(*A*)Qed.

Lemma trootE m n : (troot m == n) = (delta n <= m < delta n.+1).
Proof.
(*D*)by rewrite ltnNge -!leq_root_delta -ltnNge ltnS -eqn_leq eq_sym.
(*A*)Qed.

Lemma troot_deltaK n : troot (delta n) = n.
Proof.
(*D*)by apply/eqP; rewrite trootE leqnn deltaS -addn1 leq_add2l.
(*A*)Qed.

(**  The modulo for triangular numbers *)
Definition tmod n := n - delta (troot n).

Lemma tmod_delta n : tmod (delta n) = 0.
Proof.
(*D*)by rewrite /tmod troot_deltaK subnn.
(*A*)Qed.

Lemma tmodE n : n = delta (troot n) + tmod n.
Proof.
(*D*)by rewrite addnC (subnK (leq_delta_root _)).
(*A*)Qed.

Lemma leq_tmod_troot n : tmod n <= troot n.
Proof.
(*D*)by rewrite leq_subLR -ltnS -addnS -deltaS ltn_delta_root.
(*A*)Qed.

Lemma ltn_troot m n : troot m < troot n -> m < n.
Proof.
(*D*)rewrite leq_root_delta deltaS => /(leq_trans _) -> //.
(*D*)by rewrite {1}[m]tmodE ltn_add2l ltnS leq_tmod_troot.
(*A*)Qed.

Lemma leq_tmod m n : troot m = troot n -> (tmod m <= tmod n) = (m <= n).
Proof.
(*D*)by move=> tmEtn; rewrite {2}[m]tmodE {2}[n]tmodE tmEtn leq_add2l.
(*A*)Qed.

Lemma leq_troot_mod m n : 
   m <= n = 
   ((troot m < troot n) || ((troot m == troot n) && (tmod m <= tmod n))).
Proof.
(*D*)case: leqP => [|dmGdn] /= ; last first.
(*D*)  apply/idP.
(*D*)  apply: (leq_trans (_ : _ <= delta (troot m).+1)).
(*D*)    by rewrite ltnW // ltn_delta_root.
(*D*)  apply: (leq_trans (_ : _ <= delta (troot n))).
(*D*)    by apply: leq_delta.
(*D*)  by apply: leq_delta_root.
(*D*)rewrite leq_eqVlt => /orP[/eqP dnEdm|dmLdn].
(*D*)  rewrite dnEdm eqxx /=.
(*D*)  by rewrite {1}[m]tmodE {1}[n]tmodE dnEdm leq_add2l.
(*D*)rewrite (gtn_eqF dmLdn) /=.
(*D*)apply/idP/negP.
(*D*)rewrite -ltnNge.
(*D*)apply: (leq_trans (ltn_delta_root _)).
(*D*)apply: (leq_trans _ (leq_delta_root _)).
(*D*)by apply: leq_delta.
(*A*)Qed.

(** Fermat Numbers *)

Definition fermat n := (2 ^ (2 ^ n)).+1.

Compute elements (prime \o fermat) 4.

(** Hints : subn_sqr subnBA odd_double_half *)
Lemma dvd_exp_odd a k : 
  0 < a -> odd k -> a.+1 %| (a ^ k).+1.
Proof.
move=> aP kO.
(*D*)rewrite -[k]odd_double_half {}kO add1n.
(*D*)elim: {k}_./2 => [|k IH]; first by apply/dvdnn. 
(*D*)rewrite doubleS.
(*D*)rewrite (_ : (a ^ k.*2.+3).+1 = 
(*D*)             (a ^ 2 * (a ^ k.*2.+1).+1) - (a ^ 2 - 1)); last first.
(*D*)  rewrite mulnSr -expnD !addSn subnBA ?expn_gt0 ?aP //.
(*D*)  by rewrite addnAC addnK addn1.
(*D*)rewrite dvdn_sub ?dvdn_mull //.
(*D*)by rewrite -{2}[1](exp1n 2) subn_sqr addn1 dvdn_mull.
(*A*)Qed.

(** Hints: logn_gt0 mem_primes dvdn2 *)
Lemma odd_log_eq0 n : 0 < n -> logn 2 n = 0 -> odd n.
Proof.
(*D*)case: n => // n _ HL.
(*D*)have : 2 \notin primes n.+1.
(*D*)  rewrite -logn_gt0.
(*D*)  by case: (logn 2 n.+1) HL.
(*D*)by rewrite mem_primes /= dvdn2 negbK.
(*A*)Qed.

(** Hints pfactor_dvdnn logn_div pfactorK *)
Lemma odd_div_log n : 0 < n -> odd (n %/ 2 ^ logn 2 n).
Proof.
(*D*)move=> nP.
(*D*)apply: odd_log_eq0.
(*D*)  rewrite divn_gt0 ?expn_gt0 //.
(*D*)  apply: dvdn_leq => //.
(*D*)  apply: pfactor_dvdnn.
(*D*)rewrite logn_div.
(*D*)  by rewrite pfactorK // subnn.
(*D*)by apply: pfactor_dvdnn.
(*A*)Qed.

(** Hints divnK pfactor_dvdnn prime_nt_dvdP prime_nt_dvdP *)
Lemma prime_2expS m : 
  0 < m -> prime (2 ^ m).+1 -> m = 2 ^ logn 2 m.
Proof.
(*D*)move=> mP Hp.
(*D*)pose a := 2 ^ logn 2 m.
(*D*)pose b := m %/ a.
(*D*)have : (2 ^ a).+1 %| (2 ^ m).+1. 
(*D*)  rewrite -(divnK (pfactor_dvdnn 2 m)).
(*D*)  rewrite mulnC expnM.
(*D*)apply: dvd_exp_odd; first by apply: expn_gt0.
(*D*)  by apply: odd_div_log.
(*D*)have F : (2 ^ a).+1 != 1.
(*D*)  by rewrite eq_sym neq_ltn ltnS expn_gt0.
(*D*)move=> /(prime_nt_dvdP Hp).
(*D*)move=> /(_ F) [] /eqP.
(*D*)by rewrite eqn_exp2l // => /eqP{1}<-.
(*A*)Qed.

(** Hints oddX neq_ltn expn_gt0 *)
Lemma odd_fermat n : odd (fermat n).
Proof.
(*D*)by rewrite /= oddX negb_or eq_sym neq_ltn expn_gt0.
(*A*)Qed.

(** Hint subn_sqr *)
Lemma dvdn_exp2m1 a k : a.+1 %| (a ^ (2 ^ k.+1)).-1.
Proof.
(*D*)elim: k => /= [|k IH].
(*D*)  rewrite expn1 -subn1 -{2}[1](exp1n 2) subn_sqr addn1 dvdn_mull //.
(*D*)rewrite -subn1 -{2}[1](exp1n 2) expnS mulnC expnM subn_sqr.
(*D*)by rewrite dvdn_mulr // subn1.
(*A*)Qed.

(** Hints subnK expnD expnM *)
Lemma dvdn_fermat m n : m < n -> fermat m %| (fermat n).-2.
Proof.
(*D*)move=> mLn.
(*D*)rewrite /fermat /= -(subnK mLn) -addSnnS addnC.
(*D*)by rewrite expnD expnM dvdn_exp2m1.
(*A*)Qed.

Lemma fermat_gt1 n : 1 < fermat n.
Proof.
(*D*)by rewrite ltnS expn_gt0.
(*A*)Qed.

(** Hints gcdnMDl coprimen2 *)
Lemma coprime_fermat m n : m < n -> coprime (fermat m) (fermat n).
Proof.
(*D*)move=> mLn.
(*D*)rewrite /coprime -(subnK (fermat_gt1 n)) subn2.
(*D*)case/dvdnP: (dvdn_fermat mLn) => k ->.
(*D*)by rewrite gcdnMDl [_ == _]coprimen2 odd_fermat.
(*A*)Qed.



