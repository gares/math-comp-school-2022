
From elpi Require Import elpi.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssralg finalg countalg zmodp matrix mxalgebra. (* all_algebra *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

(** #<div class='slide'>#

* Linear algebra in mathematical components

Extensive documentation in the header of:
 - the library #<a href="https://math-comp.github.io/htmldoc_2_0_alpha1/mathcomp.algebra.matrix.html">matrix</a>#
 - and the library #<a href="https://math-comp.github.io/htmldoc_2_0_alpha1/mathcomp.algebra.mxalgebra.html">mxalgebra</a>#


* Roadmap for the lesson:
 - definition of matrices
 - main theorems
 - help with depend types
 - vector spaces as matrices

*)
(** #<div># *)
Module DefinitionMatrices.
(** #</div># *)
(** #</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#

* Defining Matrices

(Credits "ITP 2013 tutorial: The Mathematical Components library" by Enrico Tassi and Assia Mahboubi)

*)
(** #<div># *)
Reserved Notation "''M[' R ]_ n"
  (at level 8, n at level 2, format "''M[' R ]_ n").
Reserved Notation "''M[' R ]_ ( m , n )"
  (at level 8, format "''M[' R ]_ ( m ,  n )").

Reserved Notation "\matrix_ ( i , j ) E"
  (at level 36, E at level 36, i, j at level 50,
   format "\matrix_ ( i ,  j )  E").

Reserved Notation "x %:M"   (at level 8, format "x %:M").
Reserved Notation "A *m B" (at level 40, left associativity, format "A  *m  B").
Reserved Notation "A ^T"    (at level 8, format "A ^T").
Reserved Notation "\tr A"   (at level 10, A at level 8, format "\tr  A").
(** #</div># *)
(**

** A matrix is a 2-dimension array

*)
(** #<div># *)
Inductive matrix (R : Type) (m n : nat) : Type :=
  Matrix of {ffun 'I_m * 'I_n -> R}.
(** #</div># *)
(**

Some notations : size inside parentheses, type of coefficients inside
square brackets. NB: In the library, the type of coefficients can also
be ommitted.

*)
(** #<div># *)
Notation "''M[' R ]_ ( m , n )" := (matrix R m n) : type_scope.
Notation "''M[' R ]_ n" := 'M[R]_(n, n) : type_scope.

(* Test *)
Check 'M[nat]_(2,3).
Check 'M[nat]_2.
(** #</div># *)
(**

The type "matrix" is just a tag over ffun: it inherits from its structure.
We can "transfer" automatically all structures from the type of finite
functions by "trivial subTyping".

*)
(** #<div># *)
Definition mx_val R m n (A : 'M[R]_(m,n)) : {ffun 'I_m * 'I_n -> R} :=
  let: Matrix g := A in g.

HB.instance Definition _ R m n := [isNew for @mx_val R m n].

HB.instance Definition _ (R : eqType) m n     := [Equality of 'M[R]_(m, n) by <:].
HB.instance Definition _ (R : choiceType) m n := [Choice of 'M[R]_(m, n) by <:].
HB.instance Definition _ (R : countType) m n  := [Countable of 'M[R]_(m, n) by <:].
HB.instance Definition _ (R : finType) m n    := [Finite of 'M[R]_(m, n) by <:].

(** #</div># *)
(**
Test overloaded "_ == _" notation
*)
(** #<div># *)
Check 'M[nat]_2 : eqType.
Check forall A : 'M[nat]_2, A == A.
(** #</div># *)
(**

Since matrices over nat are comparable with _ == _, matrices over
matrices over nat are also comparable

*)
(** #<div># *)
Check forall AA : 'M[ 'M[nat]_3 ]_2, AA == AA.
(** #</div># *)
(**

We define a coercion in order to access elements as if matrices were
functions.

*)
(** #<div># *)
Definition fun_of_mx R m n (A : 'M[R]_(m,n)) : 'I_m -> 'I_n -> R :=
fun i j => mx_val A (i, j).  Coercion fun_of_mx : matrix >-> Funclass.

Check forall (A : 'M[nat]_3) i j, A i j == 37%N.
(** #</div># *)
(**

We provide a notation to build matrices from a general term.

*)
(** #<div># *)
Definition mx_of_fun R m n (F : 'I_m -> 'I_n -> R) : 'M[R]_(m,n) :=
  Matrix [ffun ij => F ij.1 ij.2].
Notation "\matrix_ ( i , j ) E" := (mx_of_fun (fun i j => E))
  (at level 36, E at level 36, i, j at level 50) : ring_scope.

Check \matrix_(i,j) (i - j)%N  :  'M[nat]_(3,4).


End DefinitionMatrices.

Module MatrixProperties.
(** #</div># *)
(** #</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#

* Main Theorems

We now show the most used theorems for matrix manipulation.

** mxE

mxE is an equation to compute a term in the matrix at given
coordinates: it extracts the general term of the matrix and compute
the substitution of indexes. It is generally the right move when you
have <pre>(A complicated matrix) i j</pre>

in your goal.

*)
(** #<div># *)
Check mxE.
(** #</div># *)
(**

** matrixP

matrixP is the "extensionality theorem" for matrices, it says two
matrices are equal if and only if all their coefficients are pairwise
equal.

*)
(** #<div># *)
Check matrixP.
(** #</div># *)
(** #</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#

** Operations on matrices

*** Specific operation: trace and transpose

(do not confuse the names)

*)
(** #<div># *)
Print mxtrace.
Locate "\tr".

Print trmx.
Locate "^T".
(** #</div># *)
(**

*** Specific operation scalar matrix

*)
(** #<div># *)
Print scalar_mx.
Locate "%:M".
(** #</div># *)
(**

*** Matrices on rings are provided with a R-module canonical structure.

But not a ring as the multiplication is heterogeneous.

*)
(** #<div># *)
Lemma test1 (R : ringType) m n (A B : 'M[R]_(m,n)) : A + B = B + A.
Proof. exact: addrC. Qed.

Print mulmx.

Lemma test2 (R : ringType) m n (a : R) (A : 'M[R]_(m,n)) : a *: A = a%:M *m A.
Proof. by rewrite mul_scalar_mx. Qed.
(** #</div># *)
(**

*** Square matrices with explicit non zero size have a ring canonical structure.

This ring product coincides with the matrix product.

*)
(** #<div># *)
Lemma test3 (R : ringType) n (A B : 'M[R]_n.+1) : A * B = A *m B.
Proof. reflexivity. Qed.
(** #</div># *)
(**

*** Specific operation: the determinant.

*)
(** #<div># *)
Print determinant.
Locate "\det".
(** #</div># *)
(**

*** Square matrices on a commutative unit ring with explicit non zero size have a unit ring canonical structure.

and these notions of inversibility are definitionally equivalent.
*)
(** #<div># *)
Lemma test4 (R : comUnitRingType) n (A : 'M[R]_n.+1) :
  (unitmx A) = (A \is a GRing.unit)
  /\ (A \is a GRing.unit) = (\det A \is a GRing.unit).
Proof. split; reflexivity. Qed.

End MatrixProperties.
(** #</div># *)
(** #</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#

* SUB VECTOR SPACES AS MATRICES

** General understanding

 - A specificity of the mathematical components library is to allow to
  reason on matrices as if they represented their own image.

 - The doc and the code are in #<a href="https://math-comp.github.io/htmldoc_2_0_alpha1/mathcomp.algebra.mxalgebra.html">mxalgebra</a>#

 - rows can be seen as vectors, and matrix can be seen as the familiy
  of its row vectors.

 - #<b>WARNING</b># Following the diagramatic convention (which is
    opposite to the usual convention), composition/application of
    linear maps represented by matrices should be done left to right:
    applying A to u is <pre>u *m A</pre>

 - the scope MS (matrix space) contains all notions about this vision
   of matrices (comparison, addition, intersection of spaces).

 - as a consequence, membership to a space is the same operation as
   comparison of spaces.

*** The rank of a matrix is also the dimension of the space it represents

*)
(** #<div># *)
Locate "\rank".
About mxrank.
(** #</div># *)
(**

*** Inclusion can be used both for elements (row vectors) and subspaces (matrices).

*)
(** #<div># *)
Locate "_ <= _".
About submx.
(** #</div># *)
(**

*** The total space is represented by 1, and the trivial space by 0.

*)
(** #<div># *)
About submx1.
About sub1mx.
About sub0mx.
About submx0.
(** #</div># *)
(**

*** Addition of subspaces is not the same thing as addition of matrices.
(In Coq: same notation, different scope)

*)
(** #<div># *)
Locate "_ + _".
About addsmx.
(** #</div># *)
(**

*** Intersection of subspaces

*)
(** #<div># *)
Locate "_ :&: _".
About capmx.
About sub_capmx.
(** #</div># *)
(**

*** Equality of subspaces is double inclusion.

Alternatively, the library provides an equivalent definition (via
eqmxP) that can be used for rewriting in inclusion statements or rank.

*)
(** #<div># *)
Locate "_ == _".
Check (_ == _)%MS.

Locate "_ :=: _".
About eqmx.
Print eqmx.

About mxdirectE.
About mxdirect_addsP.
(** #</div># *)
(** #</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#

** Usage.

 - Im A is represented by the matrix A itself.

 - vectors of a space represented by the matrix A are linear
   combinations of the rows of A, which amount to making a product by
   an element (i.e. row of coefficients, or coordinates in the family
   generated by A) on the left.

*)
(** #<div># *)
About submxP.
About row_subP.
About submxMl.
(** #</div># *)
(**

 - Ker A is represented by the square matrix kermx A.
*)
(** #<div># *)
About kermx.
About sub_kermxP.
(** #</div># *)
(** #</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#
** Let's do an example together

*)
(** #<div># *)
Section ex_6_12.

Variables (F : fieldType) (n' : nat).
Let n := n'.+1.
Variable (u : 'M[F]_n) (S : 'M[F]_n).
Hypothesis eq_keru_imu : (kermx u :=: u)%MS.
Hypothesis S_u_direct : (S :&: u)%MS = 0.
Hypothesis S_u_eq1 : (S + u :=: 1)%MS.
Implicit Types (x y z : 'rV[F]_n).

Lemma Su_rect x : exists2 yz, x = yz.1 + yz.2 *m u
                              & (yz.1 <= S)%MS && (yz.2 <= S)%MS.
Proof.
pose y := x *m proj_mx S u.
have /submxP [z'] := proj_mx_sub u S x => xpu.
pose z := z' *m proj_mx S u.
exists (y, z) => /=; last by rewrite !proj_mx_sub.
rewrite -{1}(@add_proj_mx _ _ _ S u x) ?S_u_direct ?S_u_eq1 ?submx1 //.
congr (_ + _); apply/eqP; rewrite xpu -subr_eq0 -mulmxBl.
apply/eqP/sub_kermxP.
by rewrite eq_keru_imu proj_mx_compl_sub ?S_u_eq1 ?submx1.
Qed.

Lemma Su_dec_eq0 y z : (y <= S)%MS -> (z <= S)%MS ->
  (y + z *m u == 0) = (y == 0) && (z == 0).
Proof.
move=> yS zS; apply/idP/idP; last first.
  by move=> /andP[/eqP -> /eqP ->]; rewrite add0r mul0mx.
rewrite addr_eq0 -mulNmx => /eqP eq_y_Nzu.
have : (y <= S :&: u)%MS by rewrite sub_capmx yS eq_y_Nzu submxMl.
rewrite S_u_direct // submx0 => /eqP y_eq0.
move/eqP: eq_y_Nzu; rewrite y_eq0 eq_sym mulNmx oppr_eq0 eqxx /= => /eqP.
move=> /sub_kermxP; rewrite eq_keru_imu => z_keru.
have : (z <= S :&: u)%MS by rewrite sub_capmx zS.
by rewrite S_u_direct // submx0.
Qed.

End ex_6_12.
(** #</div># *)
(** #</div># *)
