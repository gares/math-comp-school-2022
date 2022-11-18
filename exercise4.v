Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.

(** # This is the <a href="http://math-comp.github.io/math-comp/htmldoc/mathcomp.ssreflect.seq.html">doc of seq</a>, use it! #*)

(**

----
Exercise 1: 
    - look up the documentation of [take] and [drop]
    - prove this by induction (mind the recursive argument)
*)
Lemma cat_take_drop T n (s : seq T) : take n s ++ drop n s = s.
Proof.
(*D*)by elim: s n => [|x s IHs] [|n] //=; rewrite IHs.
(*A*)Qed.

(** Exercise 2:
   - look at the definition of [take] and [size] and prove the following lemma
   - the proof goes by cases 
*)
Lemma size_take T n (s : seq T) :
  size (take n s) = if n < size s then n else size s.
Proof.
(*D*)have [le_sn | lt_ns] := leqP (size s) n; first by rewrite take_oversize.
(*D*)by rewrite size_takel // ltnW.
(*A*)Qed.

(** Exercise 3:
    - another proof by cases 
*)
Lemma takel_cat T n (s1 s2 : seq T) :
  n <= size s1 -> take n (s1 ++ s2) = take n s1.
Proof.
(*D*)move=> Hn; rewrite take_cat ltn_neqAle Hn andbT.
(*D*)by case: (n =P size s1) => //= ->; rewrite subnn take0 cats0 take_size.
(*A*)Qed.

(** Exercise 4:
    - Look up the definition of [rot]
    - Look back in this file the lemma [cat_take_drop] 
    - can you rewrite with it right-to-left in the right-hand-side of the goal? 
*)
Lemma size_rot T n (s : seq T) : size (rot n s) = size s.
Proof.
(*D*)by rewrite -[s in RHS](cat_take_drop _ n) /rot !size_cat addnC.
(*A*)Qed.

(** Exercise 5:
    - which is the size of an empty sequence?
    - Use lemmas about [size] and [filter] 
*)
Lemma has_filter (T : eqType) a (s : seq T)  : has a s = (filter a s != [::]).
Proof.
(*D*)by rewrite -size_eq0 size_filter has_count lt0n.
(*A*)Qed.

(** Exercise 6:
    - prove that by induction 
*)
Lemma filter_all T a (s : seq T) : all a (filter a s).
Proof. 
(*D*)by elim: s => //= x s IHs; case: ifP => //= ->. 
(*A*)Qed.

(** Exercise 7:
  - prove that view (one branch is by induction) 
*)
Lemma all_filterP T a (s : seq T) :
  reflect (filter a s = s) (all a s).
Proof.
(*D*)apply: (iffP idP) => [| <-]; last exact: filter_all.
(*D*)by elim: s => //= x s IHs /andP[-> Hs]; rewrite IHs.
(*A*)Qed.

(** Exercise 8:
    - induction once more 
*)
Lemma mem_cat (T : eqType) (x : T) s1 s2 :
  (x \in s1 ++ s2) = (x \in s1) || (x \in s2).
Proof.
(*D*)by elim: s1 => //= y s1 IHs; rewrite !inE /= -orbA -IHs.
(*A*)Qed.

(** Exercise 9:
    - prove this by induction on [s] 
*)
Lemma allP (T : eqType) (a : pred T) (s : seq T) :
  reflect (forall x, x \in s -> a x) (all a s).
Proof.
(*D*)elim: s => [|x s IHs] /=; first by exact: ReflectT.
(*D*)rewrite andbC; case: IHs => IHs /=.
(*D*)  apply: (iffP idP) => [Hx y|].
(*D*)    by rewrite inE => /orP[ /eqP-> // | /IHs ].
(*D*)  by move=> /(_ x); apply; rewrite inE eqxx.
(*D*)by apply: ReflectF=> H; apply: IHs => y Hy; apply H; rewrite inE orbC Hy.
(*A*)Qed.



