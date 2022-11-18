From mathcomp Require Import all_ssreflect.

(** Elements *)

Definition elements {A} (f : _ -> A) n :=
  let l := iota 0 n.+1 in zip l (map f l).

(** Triangular number *)
Definition delta n := (n.+1 * n)./2.

Compute elements delta 10.

(** Hints : halfD half_bit_double *)
Lemma deltaS n : delta n.+1 = delta n + n.+1.
Admitted.

(** Hints   big_ord_recr big_ord_recl big_ord0 *)
Lemma deltaE n : delta n = \sum_(i < n.+1) i.
Admitted.

(* Hints half_leq *)
Lemma leq_delta m n : m <= n -> delta m <= delta n.
Admitted.

(** Hints sqrnD *)
Lemma delta_square n : (8 * delta n).+1 = n.*2.+1 ^ 2.
Admitted.

(**  Triangular root *)
Definition troot n := 
 let l := iota 0 n.+2 in
 (find (fun x => n < delta x) l).-1.

Compute elements troot 10.

Lemma troot_gt0 n : 0 < n -> 0 < troot n.
Admitted.

(** Hints before_find find_size size_iota nth_iota *)
Lemma leq_delta_root m : delta (troot m) <= m.
Admitted.

(** Hints hasP mem_iota half_bit_double half_leq nth_find nth_iota *)
Lemma ltn_delta_root m : m < delta (troot m).+1.
Admitted.

Lemma leq_root_delta m n : (n <= troot m) = (delta n <= m).
Admitted.

Lemma leq_troot m n : m <= n -> troot m <= troot n.
Admitted.

Lemma trootE m n : (troot m == n) = (delta n <= m < delta n.+1).
Admitted.

Lemma troot_deltaK n : troot (delta n) = n.
Admitted.

(**  The modulo for triangular numbers *)
Definition tmod n := n - delta (troot n).

Lemma tmod_delta n : tmod (delta n) = 0.
Admitted.

Lemma tmodE n : n = delta (troot n) + tmod n.
Admitted.

Lemma leq_tmod_troot n : tmod n <= troot n.
Admitted.

Lemma ltn_troot m n : troot m < troot n -> m < n.
Admitted.

Lemma leq_tmod m n : troot m = troot n -> (tmod m <= tmod n) = (m <= n).
Admitted.

Lemma leq_troot_mod m n : 
   m <= n = 
   ((troot m < troot n) || ((troot m == troot n) && (tmod m <= tmod n))).
Admitted.

(** Fermat Numbers *)

Definition fermat n := (2 ^ (2 ^ n)).+1.

Compute elements (prime \o fermat) 4.

(** Hints : subn_sqr subnBA odd_double_half *)
Lemma dvd_exp_odd a k :  0 < a -> odd k -> a.+1 %| (a ^ k).+1.
Admitted.

(** Hints: logn_gt0 mem_primes dvdn2 *)
Lemma odd_log_eq0 n : 0 < n -> logn 2 n = 0 -> odd n.
Admitted.

(** Hints pfactor_dvdnn logn_div pfactorK *)
Lemma odd_div_log n : 0 < n -> odd (n %/ 2 ^ logn 2 n).
Admitted.

(** Hints divnK pfactor_dvdnn prime_nt_dvdP prime_nt_dvdP *)
Lemma prime_2expS m : 0 < m -> prime (2 ^ m).+1 -> m = 2 ^ logn 2 m.
Admitted.

(** Hints odd_exp neq_ltn expn_gt0 *)
Lemma odd_fermat n : odd (fermat n).
Admitted.

(** Hint subn_sqr *)
Lemma dvdn_exp2m1 a k : a.+1 %| (a ^ (2 ^ k.+1)).-1.
Admitted.

Lemma fermat_gt1 n : 1 < fermat n.
Admitted.

(** Hints subnK expnD expnM *)
Lemma dvdn_fermat m n : m < n -> fermat m %| (fermat n).-2.
Admitted.

(** Hints gcdnMDl coprimen2 *)
Lemma coprime_fermat m n : m < n -> coprime (fermat m) (fermat n).
Admitted.



