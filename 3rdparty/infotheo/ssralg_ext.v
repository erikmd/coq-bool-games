(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
From mathcomp Require Import fintype tuple finfun bigop prime ssralg poly polydiv finset.
From mathcomp Require Import fingroup perm finalg zmodp matrix mxalgebra mxrepresentation.
Require Import ssr_ext f2.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory.
Local Open Scope ring_scope.

(** * Additional lemmas about algebraic datatypes *)

Section AboutRingType.

Variable F : ringType.

Lemma iter_addr0 : forall n x, iter n (+%R (0 : F)) x = x.
Proof. elim=> //= n IH x. by rewrite (IH x) add0r. Qed.

Lemma iter_addr0_cV : forall r n (x : 'cV[F]_r), iter n (+%R 0) x = x.
Proof. move=> r; elim=> //= n IH x; by rewrite (IH x) add0r. Qed.

Lemma subr_add2r : forall (p m n : F), m + p - (n + p) = m - n.
Proof.
move=> p m n; apply/eqP.
by rewrite subr_eq -addrA (addrC (-n)) (addrC n) addrK.
Qed.

End AboutRingType.

Notation "x '``_' i" := (x ord0 i) (at level 9) : vec_ext_scope.

Local Open Scope vec_ext_scope.

Definition row_set B n (n0 : 'I_n) (x : B) (d : 'rV_n) :=
  \row_(i < n) if i == n0 then x else d ``_ i.

Notation "v `[ i := x ]" := (row_set i x v) (at level 20) : vec_ext_scope.

Lemma row_set_comm n A (i1 i2 : 'I_n) (x1 x2 : A) d :
  i1 != i2 -> d `[ i2 := x2 ] `[ i1 := x1 ] = (d `[ i1 := x1 ]) `[ i2 := x2 ].
Proof.
move=> Hneq.
apply/rowP => i; rewrite !mxE.
case Hi1: (i == i1); case Hi2: (i == i2) => //=.
by rewrite -(eqP Hi1) (eqP Hi2) eqxx in Hneq.
Qed.

(** Big sums lemmas for row vectores (in progress)  *)

Section row_mx_ext.

Context {A : Type}.

Definition rbehead {n} (x : 'rV[A]_n.+1) := \row_(i < n) x ``_ (lift ord0 i).

Lemma rbehead_row_mx {n} (x : 'rV_n) (i : A) : rbehead (row_mx (\row_(j < 1) i) x) = x.
Proof.
rewrite /rbehead.
apply/matrixP => a b; rewrite {a}(ord1 a) !mxE.
case: splitP.
  move=> j; rewrite {j}(ord1 j); by rewrite lift0.
move=> n0; rewrite lift0 add1n => bn0.
f_equal.
by case: bn0 => /ord_inj.
Qed.

Lemma row_mx_row_ord0 {n} (x : 'rV_n) (i : A) : (row_mx (\row_(k < 1) i) x) ord0 ord0 = i.
Proof.
rewrite mxE.
case: splitP.
  move=> k.
  rewrite {k}(ord1 k) => _; by rewrite mxE.
move=> /= k.
by rewrite add1n.
Qed.

Lemma row_mx_rbehead {n} (x : 'rV_(1 + n)) (i : A) (b : 'I_(1 + n)) :
  x ``_ ord0 = i ->
  (row_mx (\row__ i) (rbehead x)) ord0 b = x ``_ b.
Proof.
move=> xi.
rewrite /rbehead mxE.
case: splitP.
  move=> j; rewrite {j}(ord1 j) => Hb.
  rewrite mxE -xi.
  f_equal.
  rewrite /= in Hb.
  by apply val_inj.
move=> k bk.
rewrite mxE.
f_equal.
by apply val_inj.
Qed.

End row_mx_ext.

(** Big sums lemmas for tuples (end) *)

Section AboutPermPid.

Variable R : comRingType.

(* s : 0 -> s0; 1 -> s1, etc.
in column 0, there is a 1 at line s0

         | 0 1 |
[a b ] * | 1 0 |  = [b a]
*)
Lemma vec_perm_mx : forall n (s : 'S_n) (z : 'rV[R]_n),
  z *m perm_mx s = \matrix_(i < 1, j < n) z i ((s^-1)%g j).
Proof.
move=> n s z; apply/matrixP => i j.
rewrite (ord1 i) {i} !mxE (bigID (pred1 ((s^-1)%g j))) /=.
rewrite big_pred1_eq !mxE {2}permE perm_invK eqxx mulr1 (eq_bigr (fun _ => 0)).
- by rewrite big_const_seq iter_addr0 addr0.
- move=> i H.
  rewrite !mxE (_ : (s i == j) = false); first by rewrite mulr0.
  apply/eqP; move/eqP : H => H; contradict H.
  by rewrite -H -permM (mulgV s) perm1.
Qed.

Lemma perm_mx_vec : forall n (s : 'S_n) (z : 'cV[R]_n),
  perm_mx s *m z = \matrix_(i < n, j < 1) z (s i) j.
Proof.
move=> n s z; apply/matrixP => i j.
rewrite (ord1 j) {j} !mxE (bigID (pred1 (s i))) /=.
rewrite big_pred1_eq {1}/perm_mx !mxE eqxx mul1r (eq_bigr (fun _ => 0)).
- by rewrite big_const_seq iter_addr0 addr0.
- move=> j; move/negbTE => H.
  by rewrite !mxE eq_sym H /= mul0r.
Qed.

Lemma pid_mx_inj : forall r n (a b : 'rV[R]_r), r <= n ->
  a *m (@pid_mx _ r n r) = b *m (@pid_mx _ r n r) -> a = b.
Proof.
move=> r n a b Hrn /matrixP Heq.
apply/matrixP => x y.
move: {Heq}(Heq x (widen_ord Hrn y)).
rewrite !mxE (ord1 x){x} (bigID (pred1 y)) /= big_pred1_eq (eq_bigr (fun _ => 0)); last first.
  move=> i Hiy.
  rewrite mxE /= (_ : nat_of_ord _ == nat_of_ord _ = false) /=; last first.
    by move/negbTE : Hiy.
  by rewrite mulr0.
rewrite big_const_seq iter_addr0 (bigID (pred1 y)) /= big_pred1_eq (eq_bigr (fun _ => 0)); last first.
  move=> i Hiy.
  rewrite mxE /= (_ : nat_of_ord i == nat_of_ord y = false) /=; last first.
    by move/negbTE : Hiy.
  by rewrite mulr0.
by rewrite big_const_seq iter_addr0 !addr0 !mxE /= eqxx /= (ltn_ord y) /= 2!mulr1.
Qed.

End AboutPermPid.

(* NB: similar to mulmx_sum_row in matrix.v *)
Lemma mulmx_sum_col : forall {R : comRingType} m n (u : 'cV[R]_n) (A : 'M_(m, n)),
  A *m u = \sum_i u i 0 *: col i A.
Proof.
move=> R m n u A; apply/colP=> j; rewrite mxE summxE; apply: eq_bigr => i _.
by rewrite !mxE mulrC.
Qed.

Section AboutRowTuple.

Variables A B : predArgType.

Definition tuple_of_row n (v : 'rV[A]_n) := [tuple v ``_ i | i < n].

Local Open Scope tuple_ext_scope.

Definition row_of_tuple n (t : n.-tuple A) := \row_(i < n) (t \_ i).

Lemma row_of_tupleK n (t : n.-tuple A) : tuple_of_row (row_of_tuple t) = t.
Proof. apply eq_from_tnth => n0; by rewrite tnth_mktuple mxE. Qed.

Lemma tuple_of_row_inj n : injective (@tuple_of_row n).
Proof.
move=> i j ij.
apply/rowP => m0.
move/(congr1 (fun x => x \_ m0)) : ij.
by rewrite 2!tnth_mktuple.
Qed.

Local Close Scope tuple_ext_scope.

Lemma tuple_of_rowK n (v : 'rV[A]_n) : row_of_tuple (tuple_of_row v) = v.
Proof. apply tuple_of_row_inj; by rewrite row_of_tupleK. Qed.

Definition bitseq_to_row
  (f : B -> A) (b : B) {l : seq B} {n} (H : size l == n) : 'rV[A]_n.
Proof.
exact (matrix_of_fun matrix_key (fun i j => f (nth b l j))).
Defined.

Lemma bitseq_to_rowK n l H f b :
  map f l = tuple_of_row (@bitseq_to_row f b l n H).
Proof.
apply/(@eq_from_nth _ (f b)) => [|i Hi].
  by rewrite size_map size_tuple (eqP H).
rewrite size_map in Hi.
rewrite (nth_map b) //.
rewrite (eqP H) in Hi.
transitivity (tnth (tuple_of_row (bitseq_to_row f b H)) (Ordinal Hi)).
  by rewrite tnth_mktuple mxE.
apply set_nth_default; by rewrite size_tuple.
Qed.

Definition bitseq_to_col
  (f : B -> A) (b : B) {l : seq B} {n} (H : size l == n) : 'cV[A]_n.
Proof.
exact (matrix_of_fun matrix_key (fun i j => f (nth b l i))).
Defined.

End AboutRowTuple.

(*Implicit Arguments tuple_of_row [A n].
Implicit Arguments row_of_tuple [A n].*)
Implicit Arguments bitseq_to_row [A B l n].
Implicit Arguments bitseq_to_col [A B l n].

Local Open Scope tuple_ext_scope.

Lemma tuple_of_row_row_mx {C : finType} n1 n2 (v1 : 'rV[C]_n1) (B : 'rV[C]_n2) :
  tuple_of_row (row_mx v1 B) = [tuple of tuple_of_row v1 ++ tuple_of_row B].
Proof.
apply eq_from_tnth => n0.
rewrite tnth_mktuple mxE.
case: splitP => [n3 n0n3|n3 n0n1n3].
  rewrite /tnth nth_cat size_tuple (_ : (n0 < n1 = true)%nat); last by rewrite n0n3 ltn_ord.
  transitivity ((tuple_of_row v1) \_ n3); first by rewrite tnth_mktuple.
  rewrite /tnth n0n3; apply set_nth_default; by rewrite size_tuple.
rewrite /tnth nth_cat size_tuple (_ : (n0 < n1 = false)%nat); last first.
  rewrite n0n1n3; apply/negbTE; by rewrite -leqNgt leq_addr.
  transitivity ((tuple_of_row B) \_ n3); first by rewrite tnth_mktuple.
  rewrite /tnth (_ : (n0 - n1 = n3)%nat); last by rewrite n0n1n3 addnC addnK.
  apply set_nth_default; by rewrite size_tuple.
Qed.

Local Close Scope tuple_ext_scope.

Section rsum_row_of_tuple_sect.

Variables (A : finType) (R : Type) (idx : R).
Variable op : Monoid.com_law idx.
Variable n : nat.
Variable C : {set 'rV[A]_n}.

Lemma rsum_row_of_tuple cst :
  \big[op/idx]_(i | row_of_tuple i \in C) cst = \big[op/idx]_(i | i \in C) cst.
Proof.
rewrite (reindex_onto (fun p => row_of_tuple p) (fun y => tuple_of_row y)) /=.
apply eq_bigl => i.
by rewrite row_of_tupleK eqxx andbC.
move=> v v_C.
by rewrite tuple_of_rowK.
Qed.

End rsum_row_of_tuple_sect.

Lemma row_to_seq_0 n : tuple_of_row 0 = [tuple of nseq n ( 0 : 'F_2)].
Proof.
apply eq_from_tnth => i.
by rewrite {2}/tnth nth_nseq (ltn_ord i) tnth_mktuple mxE.
Qed.

Definition rowF2_tuplebool {n : nat} (M : 'rV['F_2]_n) : n.-tuple bool :=
  [tuple of map (fun x => x != 0) (tuple_of_row M)].
Definition bitseq_F2row := bitseq_to_row F2_of_bool false.
Definition bitseq_F2col := bitseq_to_col F2_of_bool false.

Lemma trmx_cV_0 {k} (x : 'cV['F_2]_k) : (x ^T == 0) = (x == 0).
Proof.
case Hlhs : (_ ^T == _).
  symmetry.
  move/eqP in Hlhs.
  by rewrite -(trmxK x) Hlhs trmx0 eqxx.
symmetry; apply/eqP.
move=> abs; subst x.
by rewrite trmx0 eqxx in Hlhs.
Qed.

Section AboutRank.

Variable F : fieldType.

Lemma rank_I n : \rank (1%:M : 'M[F]_n) = n.
Proof.
apply/eqP. apply/row_freeP.
exists (1%:M : 'M[F]_n); by rewrite mulmx1.
Qed.

Lemma rank_row_mx n (A : 'M[F]_n) m (B : 'M[F]_(n, m)) :
  \rank A = n -> \rank (row_mx A B) = n.
Proof.
move=> HA.
apply/eqP. apply/row_freeP.
exists (col_mx ((invmx (row_ebase A)) *m (invmx (col_ebase A))) 0).
rewrite mul_row_col mulmx0 addr0 -{1}(mulmx_ebase A) HA pid_mx_1 mulmx1 -!mulmxA.
have -> : row_ebase A *m (invmx (row_ebase A) *m invmx (col_ebase A)) =
  invmx (col_ebase A).
  rewrite !mulmxA mulmxV.
  by rewrite mul1mx.
  by apply: row_ebase_unit.
rewrite mulmxV //.
by apply: col_ebase_unit.
Qed.

Lemma empty_rV {A : comRingType} (a : 'rV[A]_O) : a = 0.
Proof. apply/matrixP => x []; by rewrite (ord1 x). Qed.

Lemma full_rank_inj m n (A : 'M[F]_(m, n)) : m <= n -> \rank A = m ->
  forall (a b : 'rV[F]_m),  a *m A = b *m A -> a = b.
Proof.
move=> Hmn Hrank a b Hab.
move: Hrank.
rewrite /mxrank.
destruct m => //= [_|].
  by rewrite (empty_rV a) (empty_rV b).
destruct n => //=.
unlock.
move Herk : (Gaussian_elimination A) => LUr /= Htmp.
move: (mulmx_ebase A) => Heq.
rewrite -Heq !mulmxA in Hab.
have {Hab}Hab :
  a *m col_ebase A *m pid_mx (\rank A) *m row_ebase A *m (invmx (row_ebase A)) =
  b *m col_ebase A *m pid_mx (\rank A) *m row_ebase A *m (invmx (row_ebase A)).
  by rewrite Hab.
rewrite -!mulmxA mulmxV in Hab; last by exact: row_ebase_unit.
rewrite mulmx1 !mulmxA /mxrank /= in Hab.
unlock in Hab.
rewrite !Htmp in Hab.
move: {Heq}(@pid_mx_inj _ _ _ (a *m col_ebase A) (b *m col_ebase A) Hmn Hab) => Heq.
have {Hab}Hab : a *m col_ebase A *m (invmx (col_ebase A)) =
  b *m col_ebase A *m (invmx (col_ebase A)) by rewrite Heq.
rewrite -!mulmxA mulmxV in Hab; last by apply: col_ebase_unit.
by rewrite !mulmx1 in Hab.
Qed.

End AboutRank.
