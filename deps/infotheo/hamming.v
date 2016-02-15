(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div fintype finfun finset.
From mathcomp Require Import bigop prime fingroup zmodp ssralg perm matrix tuple poly.
From mathcomp Require Import finalg mxalgebra mxpoly mxrepresentation binomial.
Require Import ssr_ext ssralg_ext f2 num_occ natbin.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope num_occ_scope.

Lemma addb_nseq b : forall r v, size v = r ->
  [seq x.1 (+) x.2 | x <- zip (nseq r b) v] = map (pred1 (negb b)) v.
Proof.
elim; first by case.
move=> r IH [|h t] //= [] r_t.
rewrite IH //; by destruct b; destruct h.
Qed.

Definition addb_seq a b := [seq x.1 (+) x.2 |  x <- zip a b].

Lemma addb_seq_com : forall n a b, size a = n -> size b = n ->
  addb_seq a b = addb_seq b a.
Proof.
elim => [ [] // [] // | n IH [|ha ta] // [|hb tb] // ] [Ha] [Hb].
by rewrite /addb_seq /= -!/(addb_seq _ _) IH // addbC.
Qed.

Lemma addb_tri_ine : forall a b c, a (+) b <= (a (+) c) + (c (+) b).
Proof. by move=> [] [] []. Qed.

Lemma addb_seq_cat : forall a b c d, size a = size c ->
  addb_seq (a ++ b) (c ++ d) = addb_seq a c ++ addb_seq b d.
Proof. move=> a b c d a_c; by rewrite /addb_seq /= -map_cat zip_cat. Qed.

Lemma addb_seq_map : forall n {A : Type} (a b : seq A) f, size a = n ->
  size b = n ->
  addb_seq (map f a) (map f b) = map (fun x => f x.1 (+) f x.2) (zip a b).
Proof.
elim.
  by move=> ? [] // [].
move=> n IH A [|ha ta] // [|hb tb] //= f [Ha] [Hb].
rewrite /addb_seq /=.
f_equal.
by apply IH.
Qed.

Module HammingMetricBitstring.

Definition wH_b (a : bitseq) := N(true | a).

Definition dH_b (a b : bitseq) : nat := wH_b (addb_seq a b).

Lemma dH_b_count : forall n a b, size a = n ->
  dH_b (nseq n b) a = count (pred1 (negb b)) a.
Proof.
elim; first by case.
move=> n IH [|[|] ta] [] // [H]; rewrite /dH_b in IH;
  by rewrite /= /dH_b /= IH.
Qed.

Lemma dH_b_sym : forall n a b, size a = n -> size b = n ->
  dH_b a b = dH_b b a.
Proof. move=> n a b Ha Hb. by rewrite /dH_b (@addb_seq_com n). Qed.

Lemma dH_b_tri_ine : forall n a b c, size a = n -> size b = n -> size c = n ->
  dH_b a b <= dH_b a c + dH_b c b.
Proof.
elim.
  by case=> // [] // [].
move=> n IH [|ha ta] // [|hb tb] // [|hc tc] // [Ha] [Hb] [Hc].
rewrite /dH_b /= -/(dH_b ta tb) -/(dH_b ta tc) -/(dH_b tc tb).
move: {IH}(IH _ _ _ Ha Hb Hc) => IH.
eapply leq_trans.
- apply leq_add; [by apply leqnn | by apply IH].
- rewrite !eqb_id.
  rewrite !addnA -(addnC (hc (+) hb)) addnA -2!addnA; apply leq_add.
  + rewrite addnC; by apply addb_tri_ine.
  + by apply leqnn.
Qed.

Lemma dH_b_cat a b c d : size a = size c -> size b = size d ->
  dH_b (a ++ b) (c ++ d) = dH_b a c + dH_b b d.
Proof. move=> ac bd; by rewrite /dH_b /wH_b addb_seq_cat // /num_occ count_cat. Qed.

End HammingMetricBitstring.

Local Open Scope ring_scope.

(** * Hamming Metric

   We define the Hamming metric for row vectors and prove expected
   properties such as symmetry and the triangular inequality. *)

Section HammingMetric.

(** Hamming weight (NB: a matrix can be seen as a function with two arguments (for the row and the column)): *)

Definition wH n (v : 'rV['F_2]_n) := N(1 | tuple_of_row v).

Lemma wH_wH_b n (a : 'rV_n) :
  wH a = HammingMetricBitstring.wH_b (tval (rowF2_tuplebool a)).
Proof.
rewrite /wH /HammingMetricBitstring.wH_b /= /num_occ.num_occ /= [in RHS]count_map.
apply eq_in_count => /= ? ?; by rewrite F2_0_1' eqb_id.
Qed.

Lemma max_wH {n} (a : 'rV['F_2]_n) : wH a <= n.
Proof. rewrite /wH. apply num_occ.num_occ_leq_n. Qed.

Lemma wH0_helper2 n : @wH n 0 = O.
Proof.
rewrite /wH row_to_seq_0 /=.
apply/eqP.
rewrite -num_occ.notin_num_occ_0.
by apply/negP => /mem_nseq.
Qed.

Lemma wH0_helper n (v : 'rV_n) : wH v = O -> v = 0.
Proof.
move=> wH_v; apply/rowP => y; rewrite mxE.
apply/eqP; rewrite F2_0_1''.
move/eqP : wH_v.
rewrite -notin_num_occ_0 -has_pred1 -all_predC.
move/allP/(_ (v ord0 y)); apply; apply/tnthP.
exists y; by rewrite tnth_mktuple.
Qed.

Lemma wH0 n (i : 'rV_n) : (wH i == O) = (i == 0).
Proof.
move Hlhs : (wH _ == _) => [|].
  symmetry. apply/eqP. apply wH0_helper. by apply/eqP.
symmetry; apply/negbTE.
move/negbT : Hlhs; apply contra => /eqP ->.
by rewrite wH0_helper2.
Qed.

Lemma wH_opp n (v : 'rV_n) : wH (- v) = wH v.
Proof. by rewrite /wH /= F2_mx_opp. Qed.

Local Open Scope nat_scope.

Local Open Scope tuple_ext_scope.

Lemma wH_def n (v : 'rV_n) : wH v = \sum_(n0 < n) v ord0 n0.
Proof.
rewrite /wH num_occ_sum big_tuple.
apply eq_bigr => n0 _; by rewrite tnth_mktuple.
Qed.

Lemma sum_wH_row n m (H : 'M['F_2]_(m, n)) :
  \sum_(m0 : 'I_m) wH (row m0 H) = \sum_(n0 : 'I_n) wH (col n0 H)^T.
Proof.
transitivity (\sum_(m0 < m) \sum_(n0 < n) H m0 n0).
  apply eq_bigr => m0 _.
  rewrite wH_def.
  apply eq_bigr => n0 _.
  by rewrite mxE.
rewrite exchange_big /=.
apply eq_bigr => n0 _.
rewrite wH_def.
apply eq_bigr => m0 _; by rewrite 2!mxE.
Qed.

Lemma wH_col_1 n (i : 'I_n) : wH (col i 1%:M)^T = 1.
Proof.
rewrite /wH num_occ.num_occ_alt.
apply/eqP/cards1P.
exists i.
apply/setP => n0.
rewrite in_set1 in_set tnth_mktuple 3!mxE.
by case (_ == i).
Qed.

Lemma wH_m_card m0 n0 : #|[set a in 'rV_m0 | wH a == n0]| = 'C(m0, n0).
Proof.
rewrite -[in X in _ = X](card_ord m0) -card_draws -2!sum1dep_card.
pose h' := fun s : {set 'I_m0} => \row_(j < m0) (if j \in s then (1%R : 'F_2) else 0%R).
have h'h (i : 'rV_m0) : h' [set i0 | i ord0 i0 == 1%R] == i.
  apply/eqP/rowP => y.
  rewrite !mxE inE.
  case: ifP => [/eqP -> // |].
  move/negbT.
  by rewrite F2_0_1' negbK => /eqP.
rewrite (reindex_onto (fun x : 'rV_m0 => [set i | x ord0 i == 1%R]) h') /=.
- apply eq_bigl => i.
  rewrite /wH num_occ.num_occ_alt h'h andbC /=.
  congr (_ == _).
  apply eq_card => t.
  by rewrite !inE tnth_mktuple.
- move=> s Hs.
  apply/setP => /= i.
  rewrite !inE /h' mxE.
  by case: ifP.
Qed.

Lemma max_wH' {n0} (a : 'rV['F_2]_n0) : (wH a < n0.+1)%nat.
Proof. rewrite ltnS. by apply max_wH. Qed.

Require Import Reals Reals_ext Rbigop Rssr.

Local Open Scope R_scope.
Local Open Scope ring_scope.

Lemma hamming_01 m p :
  \rsum_(e0 in 'rV_m| e0 \in [set e0 |(1 >= wH e0)%nat])
           ((1 - p) ^ (m - wH e0) * p ^ wH e0)%R =
  ((1 - p) ^ m + INR m * p * (1 - p) ^ (m - 1))%R.
Proof.
rewrite (bigID [pred i | wH i == O]) /=.
rewrite (big_pred1 (0 : 'rV_m)) /=; last first.
  move=> i /=.
  rewrite !inE.
  rewrite -wH0.
  apply andb_idl.
  by move/eqP ->.
rewrite wH0_helper2 pow_O subn0 mulR1; f_equal.
transitivity (\rsum_(i | wH (i : 'rV['F_2]_m) == 1%nat) ((1 - p) ^ (m - 1) * p ^ 1)%R).
  transitivity (\rsum_(i|(wH (i : 'rV_m) == 1)%nat)
      ((1 - p) ^ (m - wH i) * p ^ wH i)%R).
    apply eq_bigl => /= i.
    rewrite !inE.
    case wH_1 : (wH i == 1)%nat.
      move/eqP in wH_1.
      by rewrite wH_1.
    case wH_0 : (wH i) => [|n1].
      by rewrite eqxx.
    rewrite /= andbT.
    case n1_0 : n1 => [|n2].
      by rewrite wH_0 n1_0 in wH_1.
    by [].
  transitivity (\rsum_(i|wH (i : 'rV_m) == 1%N) ((1 - p) ^ (m - 1) * p ^ 1)%R).
    by apply eq_bigr => i /= /eqP ->.
  done.
by rewrite big_const iter_Rplus pow_1 /= -(mulRC p) mulRA -cardsE wH_m_card bin1.
Qed.

Lemma binomial_theorem m p :
 (\rsum_(b|b \in [set: 'rV_m]) (1 - p) ^ (m - wH b) * p ^ wH b = 1)%R.
Proof.
transitivity (((1 - p) + p) ^ m); last first.
  rewrite addRC (_ : (p + (1 - p) = 1)%R); last by field.
  by rewrite pow1.
rewrite RPascal.
transitivity (\rsum_(b : 'rV_m) ((1 - p) ^ (m - wH b) * p ^ wH b)%R).
  apply eq_bigl => /= i; by rewrite inE.
rewrite (classify_big _ (fun s : 'rV_m => Ordinal (max_wH' s)) (fun x => ((1 - p) ^ (m - x) * p ^ x))%R) /=.
apply eq_bigr => i _.
do 2 f_equal.
rewrite -wH_m_card.
apply eq_card => /= x.
by rewrite !inE.
Qed.

(** Hamming distance: *)

Definition dH n (x y : 'rV_n) := wH (x - y).

Lemma dH_wH {k} (a b : 'rV['F_2]_k) : dH a (a + b) = wH b.
Proof. by rewrite /dH F2_mx_opp addrA F2_addmx add0r. Qed.

Lemma max_dH {n} (a b : 'rV['F_2]_n) : (dH a b <= n)%nat.
Proof. rewrite /dH. apply max_wH. Qed.

Lemma dH_dH_bitseq n (a b : 'rV_n) :
  dH a b = HammingMetricBitstring.dH_b (tval (rowF2_tuplebool a)) (tval (rowF2_tuplebool b)).
Proof.
rewrite /dH /wH /HammingMetricBitstring.dH_b /HammingMetricBitstring.wH_b.
transitivity (N(true | map bool_of_F2 (tuple_of_row (a - b)))).
  rewrite num_occ_sum_bool big_map num_occ_sum.
  apply eq_bigr; by case/F2P.
congr (N(true | _)).
apply/(@eq_from_nth _ true) => [|i Hi].
  by rewrite size_map /addb_seq size_map size_zip !size_tuple minnn.
rewrite size_map size_tuple in Hi.
rewrite (nth_map (0 : 'F_2)); last by rewrite size_tuple.
rewrite /addb_seq.
rewrite (nth_map (true, true)); last by rewrite size_zip 2!size_tuple minnn.
rewrite nth_zip /=; last by rewrite 2!size_map 2!size_tuple.
rewrite /bool_of_F2.
rewrite (_ : _ `_ i = [tuple (a - b) ord0 x | x < n] \_ (Ordinal Hi)); last first.
  rewrite tnth_mktuple.
  rewrite (nth_map (Ordinal Hi)) //; last by rewrite size_enum_ord.
  congr (_ ord0 _).
  by rewrite -[RHS](@nth_ord_enum n (Ordinal Hi)).
rewrite tnth_mktuple !mxE.
rewrite (nth_map (0 : 'F_2)); last by rewrite size_map size_enum_ord.
rewrite (nth_map (0 : 'F_2)); last by rewrite size_map size_enum_ord.
rewrite (_ : _ `_ i = (tuple_of_row a) \_ (Ordinal Hi)); last first.
  rewrite tnth_mktuple (nth_map (Ordinal Hi)); last by rewrite size_enum_ord.
  congr (_ ord0 _).
  apply val_inj => /=.
  by rewrite nth_enum_ord.
rewrite (_ : _ `_ i = (tuple_of_row b) \_ (Ordinal Hi)); last first.
  rewrite tnth_mktuple (nth_map (Ordinal Hi)); last by rewrite size_enum_ord.
  congr (_ ord0 _).
  apply val_inj => /=.
  by rewrite nth_enum_ord.
by rewrite 2!tnth_mktuple F2_opp -bool_of_F2_add_xor.
Qed.

Lemma dH_sym n (a b : 'rV_n) : dH a b = dH b a.
Proof.
by rewrite !dH_dH_bitseq (@HammingMetricBitstring.dH_b_sym n) // size_tuple.
Qed.

Lemma dH_tri_ine n (a b c : 'rV_n) : (dH a b <= dH a c + dH c b)%nat.
Proof.
rewrite !dH_dH_bitseq.
apply (@HammingMetricBitstring.dH_b_tri_ine n); by rewrite size_tuple.
Qed.

(** The Hamming weight is preserved by permutation (NB: ${\small perm\_mx\,\left( \begin{array}{c} 1 \mapsto 2 \\ 2 \mapsto 1 \end{array} \right) = \left[ \begin{array}{cc} 0 & 1 \\ 1 & 0 \\ \end{array} \right]}$): *)

Lemma perm_on_Sn n (s : 'S_n) : perm_on [set x | x \in enum 'I_n] s.
Proof. apply/subsetP=> /= x _; by rewrite !in_set mem_enum. Qed.

Lemma perm_eq_enum n (s : 'S_n) : perm_eq (enum 'I_n) (map (s^-1)%g (enum 'I_n)).
Proof.
apply uniq_perm_eq.
- by apply enum_uniq.
- rewrite map_inj_uniq; by [apply enum_uniq | apply: perm_inj].
- move=> /= xi.
  case Hi : (xi \in enum 'I_n).
  + symmetry; apply/mapP; exists (s xi).
    * move: (perm_closed xi (perm_on_Sn s)).
      by rewrite !in_set => ->.
    * by rewrite permK.
  + symmetry; apply/mapP; case=> x Hx Hxxi.
    move: (perm_closed x (perm_on_Sn (s^-1)%g)).
    by rewrite !in_set -Hxxi Hx Hi.
Qed.

Lemma wH_perm_mx n (s : 'S_n) z : wH (z *m perm_mx s) = wH z.
Proof.
rewrite /wH.
suff -> : tuple_of_row (z *m perm_mx s) = perm_tuple (s^-1)%g (tuple_of_row z).
  by apply: num_occ_perm.
apply eq_from_tnth => n0; by rewrite 3!tnth_mktuple vec_perm_mx !mxE.
Qed.

(** We provide some basic, characteristing properties about row
vectors of Hamming weight 1 %and~2%#and 2# (to be used in %Sect.~\ref{sec:hamming_codes}%#for Hamming codes#): *)

Local Notation "l `b_ i" := (@nth _ false l i) (at level 3, i at level 2).

Lemma wHb_1 : forall n l, size l = n ->
  HammingMetricBitstring.wH_b l = 1%nat ->
  exists i, (i < n /\ l `b_ i = true)%nat /\
    forall j, (j < n -> j <> i -> l `b_ j = false)%nat.
Proof.
elim.
- by case.
- move=> n IH [|[] t] // [Hsz] /=.
  + case=> H.
    exists O.
    split; first by done.
    move=> j Hj Hj'.
    destruct j => //=.
    move: (has_count (pred1 true) t).
    rewrite /HammingMetricBitstring.wH_b /num_occ in H.
    rewrite H ltnn.
    move/negbT/hasPn => K.
    move: (@mem_nth _ false t j).
    rewrite ltnS in Hj.
    rewrite Hsz.
    move/(_ Hj).
    move/K => /= {K}K.
    apply Bool.not_true_is_false.
    by apply/eqP.
  + rewrite add0n.
    case/(IH _ Hsz) => i [[H11 H12] H2].
    exists i.+1.
    split; first by done.
    move=> j Hj Hj'.
    destruct j => //=.
    apply H2 => //.
    contradict Hj'; by subst j.
Qed.

Lemma wH_1 n (x : 'rV_n) : wH x = 1%nat ->
  exists i : 'I_n, x 0 i = 1 /\ (forall j : 'I_n, i <> j -> x 0 j = 0).
Proof.
rewrite wH_wH_b.
move/wHb_1.
move/(_ n).
rewrite size_tuple.
case/(_ erefl) => i [] [] H1 H2 H3.
exists (Ordinal H1); split.
  transitivity (F2_of_bool true) => //.
  rewrite -H2 /rowF2_tuplebool (nth_map 0); last by rewrite size_tuple.
  rewrite (_ : _ `_ i = (tuple_of_row x) \_ (Ordinal H1)); last first.
    apply set_nth_default; by rewrite size_tuple.
  rewrite tnth_mktuple {1}(F2_0_1 (x 0 (Ordinal H1))); by case: (x 0 _ != 0).
move=> j Hj.
transitivity (F2_of_bool false) => //.
rewrite -(H3 j) //; last first.
  move=> ?; subst i.
  by apply/Hj/val_inj.
rewrite /rowF2_tuplebool (nth_map 0); last by rewrite size_tuple.
rewrite (_ : _ `_ j = (tuple_of_row x) \_ j); last first.
    apply set_nth_default; by rewrite size_tuple.
rewrite tnth_mktuple {1}(F2_0_1 (x 0 j)); by case: (x 0 _ != 0).
Qed.

Lemma wHb_2 : forall n l, size l = n ->
  HammingMetricBitstring.wH_b l = 2%nat ->
  (exists i, exists k, (i < n /\ l `b_ i = true) /\
    (k < n /\ l `b_ k = true) /\ i <> k /\
    forall j, j < n -> j <> i -> j <> k -> l `b_ j = false)%nat.
Proof.
elim.
- by case.
- case.
  move=> IH l Hsz Hcount.
  rewrite /HammingMetricBitstring.wH_b /num_occ in Hcount.
  move: (count_size (pred1 true) l).
  by rewrite Hcount Hsz ltnn.
- move=> n IH [|[] t] // [Hsz] /=.
  + rewrite add1n.
    case=> X.
    exists O.
    case: (@wHb_1 _ _ Hsz X) => k [[Hk1 Hk11] Hk2].
    exists k.+1.
    split; first by done.
    split.
    split; last by done.
    by apply leq_ltn_trans with n.+1.
    split; first by done.
    move=> j Hj Hj' Hjk.
    destruct j => //=.
    apply Hk2 => //.
    contradict Hjk; by rewrite Hjk.
  + rewrite add0n.
    case/(IH _ Hsz) => i [k [[H11 H12] [H21 [H221 H222]]]].
    exists i.+1, k.+1.
    split; first by done.
    split; first by done.
    split.
    contradict H221; by case: H221.
    move=> j Hj Hj' Hjk.
    destruct j => //=.
    apply H222 => //.
    contradict Hj'; by subst j.
    contradict Hjk; by subst j.
Qed.

Lemma wH_2 n (x : 'rV_n) : wH x = 2%nat ->
  exists i j : 'I_n, i <> j /\ x 0 i = 1 /\ x 0 j = 1 /\
  (forall k : 'I_n, i <> k -> j <> k -> x 0 k = 0).
Proof.
rewrite wH_wH_b.
move/wHb_2.
move/(_ n).
rewrite size_tuple.
case/(_ erefl) => i [] k [] [] H1 [] H2 [] [] H3 [] H4 [] H5 H6.
exists (Ordinal H1), (Ordinal H3); split.
  by case.
split.
  transitivity (F2_of_bool true) => //.
  rewrite -H2 /rowF2_tuplebool (nth_map 0); last by rewrite size_tuple.
  rewrite (_ : _ `_ i = (tuple_of_row x) \_ (Ordinal H1)); last first.
    apply set_nth_default; by rewrite size_tuple.
  rewrite tnth_mktuple {1}(F2_0_1 (x 0 (Ordinal H1))); by case: (x 0 _ != 0).
split.
  transitivity (F2_of_bool true) => //.
  rewrite -H4 /rowF2_tuplebool (nth_map 0); last by rewrite size_tuple.
  rewrite (_ : _ `_ k = (tuple_of_row x) \_ (Ordinal H3)); last first.
    apply set_nth_default; by rewrite size_tuple.
  rewrite tnth_mktuple {1}(F2_0_1 (x 0 (Ordinal H3))); by case: (x 0 _ != 0).
move=> j ij kj.
transitivity (F2_of_bool false) => //.
rewrite -(H6 j) //; last first.
- move=> ?; subst k.
  by apply/kj/val_inj.
- move=> ?; subst i.
  by apply/ij/val_inj.
rewrite /rowF2_tuplebool (nth_map 0); last by rewrite size_tuple.
rewrite (_ : _ `_ j = (tuple_of_row x) \_ j); last first.
    apply set_nth_default; by rewrite size_tuple.
rewrite tnth_mktuple {1}(F2_0_1 (x 0 j)); by case: (x 0 _ != 0).
Qed.

Lemma card_dH {n} (t t' : n.-tuple 'F_2) :
  #| [pred i | t' \_ i != t \_ i ] | = dH (row_of_tuple t) (row_of_tuple t').
Proof.
rewrite /dH /wH num_occ.num_occ_alt /=.
apply eq_card => /= i.
rewrite inE.
move H : (_ \in _) => [|].
  symmetry.
  rewrite F2_0_1'.
  move: H; apply contra.
  by rewrite tnth_mktuple !mxE subr_eq0 eq_sym.
move/negbT in H.
rewrite negbK in H.
apply/esym/negbTE.
rewrite F2_0_1' negbK tnth_mktuple !mxE.
move/eqP : H => ->.
by rewrite subr_eq0.
Qed.

Local Open Scope vec_ext_scope.

(* TODO: rename? move? *)
Lemma card_dH_vec {n} (t t' : 'rV['F_2]_n) :
  #| [pred i | t' /_ i != t /_ i ] | = dH t t'.
Proof.
rewrite /dH /wH num_occ.num_occ_alt /=.
apply eq_card => /= i.
rewrite inE.
move H : (_ \in _) => [|].
  symmetry.
  rewrite F2_0_1'.
  apply: contra H.
  by rewrite tnth_mktuple !mxE subr_eq0 eq_sym.
move/negbT in H.
rewrite negbK in H.
apply/esym/negbTE.
rewrite F2_0_1' negbK tnth_mktuple !mxE.
move/eqP : H => ->.
by rewrite subr_eq0.
Qed.

Lemma card_dHC {n} (t t': 'rV['F_2]_n) :
  #| [pred i | t' /_ i == t /_ i ] | = (n - dH t t')%nat.
Proof.
move: (cardC [pred i | t' /_i == t /_i ]).
rewrite card_ord => H.
by rewrite -[in X in _ = (X - _)%nat]H -card_dH_vec -addnBA // subnn addn0.
Qed.

Local Close Scope vec_ext_scope.

Local Close Scope tuple_ext_scope.

End HammingMetric.

(** * Encoding of Naturals as Vectors *)

(** Here is a function that transforms natural numbers into their binary encodings
   (presented in the form of column-vectors) (e.g., $nat2bin\,3\,1 = \left[ \begin{array}{c} 0 \\ 0 \\ 1 \end{array} \right]$, $nat2bin\,3\,2 = \left[ \begin{array}{c} 0 \\ 1 \\ 0 \end{array} \right]$, $nat2bin\,3\,3 = \left[ \begin{array}{c} 0 \\ 1 \\ 1 \end{array} \right]$, etc.): *)

Definition nat2bin_cV (r i : nat) : 'cV_r := bitseq_F2col (size_nat2bin i r).

(** The only natural that maps to the null row vector is 0: *)

Lemma nat2bin_cV_not_zero r i : i <> O -> i < expn 2 r -> nat2bin_cV r i <> 0.
Proof.
move=> Hi W.
rewrite /nat2bin_cV /bitseq_F2col /bitseq_to_col.
move: (nat2bin_nseq_false i r Hi W) => H.
contradict H.
apply eq_from_nth with false.
- by rewrite /= size_pad_seqL size_nseq.
- move=> j Hj.
  rewrite (_ : size _ = r) in Hj; last first.
    apply/eqP. by apply size_nat2bin.
  move/colP : H => /(_ (Ordinal Hj)).
  rewrite !mxE /= => Hj'.
  rewrite nth_nseq Hj.
  by apply F2_of_bool_0_inv.
Qed.

Lemma nat2bin_cV_inj n i j : nat_of_pos i < expn 2 n -> nat_of_pos j < expn 2 n ->
  nat2bin_cV n (nat_of_pos i) = nat2bin_cV n (nat_of_pos j) -> i = j.
Proof.
move=> Hi Hj.
rewrite /nat2bin_cV /bitseq_F2col /bitseq_to_col.
move/col_nth => X.
have Htmp : size (nat2bin (nat_of_pos i) n) <= n.
  move: (size_nat2bin (nat_of_pos i) n).
  by move/eqP => ->.
apply X in Htmp => //; last first.
  apply trans_eq with n.
  - apply/eqP.
    by apply size_nat2bin.
  - symmetry.
    apply/eqP.
    by apply size_nat2bin.
rewrite /nat2bin in Htmp.
move: (N2bitseq_leading_bit (bin_of_nat (nat_of_pos i))) => U.
lapply U; last by apply bin_of_nat_nat_of_pos_not_0.
case=> ik Hik.
rewrite Hik in Htmp.
move: (N2bitseq_leading_bit (bin_of_nat (nat_of_pos j))) => V.
lapply V; last by apply bin_of_nat_nat_of_pos_not_0.
case=> jk Hjk.
rewrite Hjk in Htmp.
destruct n.
- rewrite expn0 in Hi.
  move: (@nat_of_pos_not_0 i) => W.
  by destruct (nat_of_pos i).
- apply pad_seqL_leading_true_inj in Htmp; last 2 first.
    have XX : size (true :: ik) <= n.+1.
      rewrite -Hik size_rev.
      apply size_N2bitseq_ub => //.
      by apply nat_of_pos_not_0.
    by rewrite /= ltnS in XX.
  have XX : size (true :: jk) <= n.+1.
    rewrite -Hjk size_rev.
    apply size_N2bitseq_ub => //.
    by apply nat_of_pos_not_0.
    by rewrite /= ltnS in XX.
  subst ik.
  rewrite -Hjk in Hik.
  move/rev_inj : Hik.
  by move/N2bitseq_inj/bin_of_nat_inj/nat_of_pos_inj.
Qed.

(** No sum of two non-zero binaries maps to zero: *)

Lemma nat2bin_cV_plus_nat2bin_cV_not_zero r i j : i <> j ->
  i <> O -> j <> O -> i < expn 2 r -> j < expn 2 r -> nat2bin_cV r i + nat2bin_cV r j <> 0.
Proof.
move=> Hij Hi Hj Hin Hjn.
destruct i => //.
destruct j => //.
contradict Hij.
apply F2_addmx0 in Hij.
have [ii Hii] : exists ii, i.+1 = nat_of_pos ii.
  exists (BinPos.P_of_succ_nat i).
  rewrite -Pnat.nat_of_P_o_P_of_succ_nat_eq_succ.
  by rewrite BinPos_nat_of_P_nat_of_pos.
have [jj Hjj] : exists jj, j.+1 = nat_of_pos jj.
  exists (BinPos.P_of_succ_nat j).
  rewrite -Pnat.nat_of_P_o_P_of_succ_nat_eq_succ.
  by rewrite BinPos_nat_of_P_nat_of_pos.
rewrite Hii Hjj in Hij.
apply nat2bin_cV_inj in Hij; last 2 first.
  by rewrite -Hii.
  by rewrite -Hjj.
subst ii.
by rewrite Hjj.
Qed.

Definition nat2bin_rV (r i : nat) : 'rV_r := bitseq_F2row (size_nat2bin i r).

Lemma tr_nat2bin_cV m i : (nat2bin_cV m i)^T = nat2bin_rV m i.
Proof. apply/rowP => y; by rewrite !mxE. Qed.

Lemma wH_two_pow p m : p < m -> wH (nat2bin_rV m (expn 2 p)) = 1%nat.
Proof.
move=> p_m.
rewrite wH_wH_b /nat2bin_rV /bitseq_F2row /bitseq_to_row /rowF2_tuplebool /=.
rewrite /HammingMetricBitstring.wH_b /num_occ.num_occ count_map.
rewrite (eq_count (a2 := pred1 1)); last by move=> ? /=; rewrite eqb_id F2_0_1'.
rewrite -sum1_count big_map /=.
rewrite (eq_bigl (pred1 (Ordinal (rev_ord_proof (Ordinal p_m))))); last first.
  move=> i /=; symmetry; rewrite -[in X in X = _]val_eqE /=.
  rewrite mxE nat2bin_two_pow // nth_cat size_nseq.
  case: ifP => [ i_m | /negbT ].
    rewrite nth_nseq i_m /=.
    apply/negbTE; by rewrite neq_ltn i_m.
  rewrite -leqNgt leq_eqVlt; case/orP => [/eqP Heq | m_i ].
    by rewrite -Heq subnn /= !eqxx.
  rewrite -[in X in _ = X]subnSK //= nth_nseq.
  transitivity false; last by case: ifP.
  apply/negbTE; by rewrite neq_ltn m_i orbC.
by rewrite /= big_filter_cond /= big_pred1_eq.
Qed.

Lemma wH_3 : forall n, 3 <= n -> wH (nat2bin_rV n 3) = 2.
Proof.
case => // [] // [] // [] // n _.
rewrite /wH /num_occ.num_occ /nat2bin_rV.
set tmp := tuple_of_row _.
have -> : tmp = [tuple of rev (1 :: 1 :: nseq n.+1 (0 : 'F_2))].
  apply eq_from_tnth => i.
  rewrite tnth_mktuple /bitseq_F2row /bitseq_to_row /nat2bin mxE.
  rewrite (tnth_nth 0).
  rewrite -(nth_map _ 0); last by rewrite size_cat size_nseq /= addn2.
  congr (_ `_ i).
  rewrite /= map_cat /= -!cat_rcons cats0 (_ : 0 :: nseq n 0 = nseq n.+1 0) //.
  by rewrite 2!rev_cons nseq_S -cat_rcons cats0 rev_rcons /= rev_nseq map_nseq.
rewrite /=.
set y := _ :: _.
rewrite (_ : y = [:: 1; 1; 0] ++ nseq n 0) // rev_cat count_cat /= -(@eq_in_count _ pred0).
  by rewrite count_pred0.
move=> a /=.
rewrite rev_nseq.
by move/mem_nseq/eqP => ->.
Qed.

Lemma wH_7 : forall n, 3 <= n -> wH (nat2bin_rV n 7) = 3.
Proof.
case => // [] // [] // [] // n _.
rewrite /wH /num_occ.num_occ /nat2bin_rV.
set x := tuple_of_row _.
have -> : x =[tuple of rev (1 :: 1 :: 1 :: nseq n (0 : 'F_2))].
  rewrite /x {x}.
  apply eq_from_tnth => i.
  rewrite tnth_mktuple /bitseq_F2row /bitseq_to_row /nat2bin mxE (tnth_nth 0).
  rewrite -(nth_map _ 0); last first.
    rewrite /pad_seqL /=.
    destruct n => //=.
    by rewrite size_cat size_nseq /= addn3.
  congr (_ `_ i).
  rewrite /= !rev_cons /= /pad_seqL /= -addn3 addnK map_cat /= map_nseq /=.
  by rewrite rev_nseq -!cats1 /= -!catA.
rewrite /=.
set y := _ :: _.
rewrite (_ : y = [:: 1; 1; 1] ++ nseq n 0) // rev_cat count_cat /=.
rewrite -(@eq_in_count _ pred0).
  by rewrite count_pred0.
move=> a /=.
rewrite rev_nseq.
by move/mem_nseq/eqP => ->.
Qed.

Lemma rev7_bin : forall m, 2 < m ->
  rev (N2bitseq (BinNums.Npos (xOs (m - 3) (BinNums.xI 3)))) =
  true :: true :: true :: nseq (m - 3) false.
Proof.
elim=> //.
case=> //.
case=> //.
case=> //.
move=> m.
move/(_ Logic.eq_refl).
rewrite -{1}addn3 -addnBA // subnn addn0 => IH _.
rewrite -{1}addn4 -addnBA //= (_ : 4 - 3 = 1)%nat // addn1 /=.
rewrite rev_cons IH /=.
rewrite -{1}addn3 -addnBA // subnn addn0.
rewrite -cats1.
by rewrite -nseq_S.
Qed.

Lemma rev_nat2bin_7 n : 2 < n ->
  rev (nat2bin 7 n) = nat2bin (7 * expn 2 (n - 3)) n.
Proof.
move=>Hn.
rewrite /nat2bin.
rewrite (bin_of_nat_rev7 _ Hn).
rewrite (@bin_of_nat_7 n) //=.
rewrite (rev7_bin Hn) /=.
rewrite {1}/pad_seqL /=.
rewrite Hn.
rewrite rev_cat /=.
rewrite /pad_seqL /=.
rewrite size_nseq.
case: ifP => H //.
  rewrite (_ : n - (n - 3).+3 = 0)%nat //; last first.
  destruct n => //.
  destruct n => //.
  destruct n => //.
  rewrite -addn3.
  by rewrite -(@addnBA n 3 3) // subnn addn0 addn3 subnn.
by rewrite rev_nseq.
suff : False by done.
move/negbT in H.
rewrite -leqNgt in H.
destruct n => //.
destruct n => //.
destruct n => //.
by rewrite -{2}addn3 -addnBA // subnn addn0 ltnn in H.
Qed.

Lemma wH_7_rev7 n : 2 < n ->
  wH (nat2bin_rV n 7) = wH (nat2bin_rV n (7 * expn 2 (n - 3))).
Proof.
move=> Hn.
rewrite /wH /nat2bin_rV.
set lhs := tuple_of_row _.
set rhs := tuple_of_row _.
suff : rev lhs = rhs.
  move=> <-.
  by apply num_occ.num_occ_rev.
rewrite /lhs /rhs.
rewrite /bitseq_F2row.
rewrite -!bitseq_to_rowK.
rewrite -map_rev.
f_equal.
by rewrite rev_nat2bin_7.
Qed.

Definition bin2nat_rV n (y : 'rV_n) :=
  BinNat.N.to_nat (bitseq2N (map bool_of_F2 (tuple_of_row y))).

Lemma bin2nat_rV_up n (y : 'rV_n) : bin2nat_rV y < expn 2 n.
Proof. by rewrite /bin2nat_rV bitseq2N_up // size_map size_tuple. Qed.

Lemma bin2nat_rV_0 k : bin2nat_rV (0 : 'rV_k) = O.
Proof.
rewrite /bin2nat_rV.
set tmp := map _ _.
have -> : tmp = nseq k false.
  rewrite {}/tmp  /= (_ : false = bool_of_F2 0) // -map_nseq.
  congr ([seq _ | i <- _]).
  apply eq_from_nth with 0.
  - by rewrite size_map size_enum_ord size_nseq.
  - move=> i Hi.
    rewrite size_map size_enum_ord in Hi.
    rewrite nth_nseq Hi (nth_map (Ordinal Hi)); last by rewrite size_enum_ord.
    by rewrite mxE.
by rewrite bitseq2N_nseq_false.
Qed.

Require Import BinNat.

Lemma bin2nat_rV_inv_0 n (y : 'rV_n) : (bin2nat_rV y == O) = (y == 0).
Proof.
case Hlhs : (bin2nat_rV _ == O); last first.
  symmetry; apply/negP => /eqP abs; subst y.
  by rewrite bin2nat_rV_0 eqxx in Hlhs.
symmetry; apply/eqP.
move/eqP : Hlhs.
rewrite /bin2nat_rV [X in _ = X -> _](_ : O = N.to_nat 0) //.
move/Nnat.N2Nat.inj/bitseq2N_0.
rewrite size_map size_tuple.
move/(_ _ erefl) => Htmp.
apply tuple_of_row_inj, val_inj.
rewrite -(map_id (val (tuple_of_row y))).
transitivity (map (F2_of_bool \o bool_of_F2) (val (tuple_of_row y))).
  apply eq_in_map => i /= _; by rewrite bool_of_F2K.
by rewrite map_comp Htmp row_to_seq_0 (_ : 0 = F2_of_bool false) // map_nseq.
Qed.

Definition bin2nat_cV n (y : 'cV_n) : nat := bin2nat_rV y^T.

Lemma bin2nat_cV_0 k : bin2nat_cV (0 : 'cV_k) = O.
Proof. by rewrite /bin2nat_cV trmx0 bin2nat_rV_0. Qed.

Lemma bin2nat_rV_tr n (y : 'rV_n) : bin2nat_rV y = bin2nat_cV (y^T).
Proof. by rewrite /bin2nat_cV trmxK. Qed.

Lemma mulmx_nat2vin_col n m (M : 'M_(n, m)) (k : 'I_m) :
  M *m (nat2bin_cV m (expn 2 k)) = col (Ordinal (rev_ord_proof k)) M.
Proof.
rewrite /nat2bin_cV.
apply/colP => x.
rewrite !mxE /=.
transitivity (\sum_(j < m) M x j * nth false (nat2bin (expn 2 k) m) j).
  apply eq_bigr => i _; by rewrite /bitseq_F2col /bitseq_to_col mxE.
rewrite nat2bin_two_pow //.
pose mk := Ordinal (rev_ord_proof k).
rewrite -/mk (bigID (pred1 mk)) /= big_pred1_eq.
set tmp1 := nth _ _ _.
have -> : tmp1 = true.
  by rewrite /tmp1 {tmp1} nth_cat size_nseq {1}/mk ltnn subnn.
rewrite mulr1.
set lhs := \sum_ (_ | _) _.
suff -> : lhs = 0 by rewrite addr0.
transitivity (\sum_(i | i != mk) (0 : 'F_2)).
  apply eq_bigr => i imk.
  set rhs := nth _ _ _.
  suff -> : rhs = false by rewrite mulr0.
  rewrite /rhs nth_cat size_nseq.
  case: ifP => Hcase; first by rewrite nth_nseq Hcase.
  rewrite (_ : true :: _ = [:: true] ++ nseq k false) // nth_cat /=.
  case: ifP => Hcase2.
    suff : False by done.
    clear -Hcase2 imk Hcase.
    have {Hcase2}Hcase2 : i <= m - k.+1 by rewrite ltnS leqn0 in Hcase2.
    rewrite leq_eqVlt Hcase orbC /= in Hcase2.
    move: Hcase2; by apply/negP.
  rewrite nth_nseq; by case: ifP.
by rewrite big_const iter_addr0.
Qed.

Lemma tuple_of_row_ord0 (s : 'rV['F_2]_0) : tuple_of_row s = [tuple of [::]].
Proof. apply eq_from_tnth; by case. Qed.

Lemma bin2nat_cV_ord0 (s : 'cV_0) : bin2nat_cV s = O.
Proof. by rewrite /bin2nat_cV /bin2nat_rV N_bin_to_nat tuple_of_row_ord0. Qed.

Lemma nat2bin_cV_0 n : nat2bin_cV n 0 = 0.
Proof.
rewrite /nat2bin_cV /bitseq_F2col /bitseq_to_col nat2bin_0_n.
apply/colP => b /=.
rewrite 2!mxE nth_nseq; by case: ifP.
Qed.

Lemma bin2nat_cVK n (s : 'cV_n) : nat2bin_cV n (bin2nat_cV s) = s.
Proof.
destruct n as [|n].
  apply/colP; by case.
apply/colP => y.
rewrite mxE /bin2nat_cV /bin2nat_rV.
set tmp := [seq bool_of_F2 i | i <- _].
rewrite [X in nat2bin _ X](_ : _ = size tmp); last by rewrite size_map size_tuple.
rewrite bitseq2NK; last by rewrite size_tuple.
rewrite /tmp (nth_map (0 : 'F_2)); last by rewrite size_tuple.
rewrite bool_of_F2K (_ : _ `_ _ = tnth (tuple_of_row s^T) y); last first.
  apply set_nth_default; by rewrite size_tuple.
by rewrite tnth_mktuple mxE.
Qed.
