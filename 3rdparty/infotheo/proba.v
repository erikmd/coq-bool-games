(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div choice fintype.
From mathcomp Require Import tuple finfun bigop prime binomial ssralg finset fingroup finalg matrix.
Require Import Reals Fourier ProofIrrelevance FunctionalExtensionality.
Require Import Reals_ext ssr_ext ssralg_ext log2 Rssr tuple_prod Rbigop.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope reals_ext_scope.
Local Open Scope tuple_ext_scope.
Local Open Scope Rb_scope.

(** * Distribution *)

(** Distribution over sample space #A#%$A$%
   %(numerically-valued distribution function $p : A \to \mathbb{R}$;
   for any $a \in A$, $0 \leq p(a)$; $\sum_{i \in A} p(i) = 1$)%: *)

Section distribution_definition.

Variable A : finType.

Record dist := mkDist {
  pmf :> A -> R+ ;
  pmf1 : \rsum_(a in A) pmf a = 1 }.

Lemma dist_support_not_empty (P : dist) : (0 < #| A |)%nat.
Proof.
move : (leq0n #|A|).
rewrite leq_eqVlt.
case/orP => // /eqP => abs.
suff : False by done.
apply R1_neq_R0.
rewrite -(pmf1 P).
transitivity (\rsum_(a| false) P a).
  apply eq_bigl => a.
  apply/negP => abs'.
  have : exists a, a \in A by exists a.
  move/card_gt0P.
  by rewrite -abs.
by rewrite big_pred0_eq.
Qed.

Definition makeDist (pmf : A -> R) (H0 : forall a, 0 <= pmf a)
  (H1 : \rsum_(a|a \in A) pmf a = 1) := @mkDist (@mkPosFun _ pmf H0) H1.

Lemma dist_max (P : dist) a : P a <= 1.
Proof.
rewrite -(pmf1 P) (_ : P a = \rsum_(a' in A | a' == a) P a').
  by apply Rle_big_P_true_f, Rle0f.
by rewrite big_pred1_eq.
Qed.

Lemma dist_eq d d' : pmf d = pmf d' -> d = d'.
Proof.
destruct d as [d d1] => /=.
destruct d' as [d' d'1] => /= H.
move: d1 d'1.
rewrite H.
move=> d1 d'1.
by rewrite (proof_irrelevance _ d1 d'1).
Qed.

End distribution_definition.

Definition dist_of (A : finType) := fun phT : phant (Finite.sort A) => dist A.

Notation "{ 'dist' T }" := (dist_of (Phant T))
  (at level 0, format "{ 'dist'  T }") : proba_scope.

(** Uniform distributions *)

Module Uniform.

Section Uniform_sect.

Variable A : finType.
Variable n : nat.
Hypothesis Anot0 : #|A| = n.+1.

Definition f (a : A) := INR 1 / INR #|A|.

Lemma f0 a : 0 <= f a.
Proof. apply Rle_mult_inv_pos. by apply pos_INR. apply lt_0_INR. rewrite Anot0; by apply/ltP. Qed.

Lemma f1 : \rsum_(a | a \in A) f a = 1.
Proof.
rewrite /f /Rdiv -big_distrr /= mul1R big_const iter_Rplus Rinv_r //.
apply not_0_INR.
apply/eqP.
by rewrite Anot0.
Qed.

Definition d : dist A := makeDist f0 f1.

End Uniform_sect.

Lemma d_neq0 (C : finType) (support_non_empty : { m : nat | #| C | = m.+1 }) :
  forall x, d (projT2 support_non_empty) x != 0.
Proof.
move=> x.
rewrite /Uniform.d /= /Uniform.f /=.
apply/eqP/Rmult_integral_contrapositive; split; first by apply not_0_INR.
apply/Rinv_neq_0_compat/not_0_INR/eqP.
by case: support_non_empty => x' ->.
Qed.

End Uniform.

Lemma dom_by_uniform {A : finType} (P : dist A) n (HA : #|A| = n.+1) :
  P << (Uniform.d HA).
Proof.
move=> a; rewrite /Uniform.d /= /Uniform.f /= HA /Rdiv mul1R.
suff : (0 < n.+1)%nat.
  move/ltP/lt_0_INR/Rinv_0_lt_compat/Rlt_not_eq => H1 H2.
  by apply not_eq_sym in H2.
done.
Qed.

(** Uniform distribution with a restricted support *)

Module UniformSupport.
Section UniformSupport_sect.

Variables (A : finType) (C : {set A}).
Hypothesis HC : (0 < #|C|)%nat.

Definition f a := (if a \in C then 1 / INR #|C| else 0)%R.

Lemma f0 a : 0 <= f a.
Proof.
rewrite /f.
case e : (a \in C); last by apply/Rle_refl.
apply Rle_mult_inv_pos; first by fourier.
rewrite -/(INR 0); by apply/lt_INR/ltP.
Qed.

Lemma f1 : \rsum_(a in A) f a = 1%R.
Proof.
rewrite /f.
have HC' : INR #|C| <> 0%R.
  apply/not_0_INR/eqP; by rewrite -lt0n.
transitivity (\rsum_(a in A) (if a \in C then 1 else 0) / INR #|C|)%R.
apply eq_bigr => a _.
  case aC : (a \in C); [reflexivity | by field].
have HC'' : \rsum_(a in A) (if a \in C then 1 else 0)%R = INR #|C|.
  by rewrite -big_mkcondr /= big_const iter_Rplus mulR1.
by rewrite /Rdiv -big_distrl HC'' /= Rinv_r.
Qed.

Lemma restrict g : \rsum_(t in A) (f t * g t)%R = \rsum_(t in C) (f t * g t)%R.
Proof.
rewrite (bigID (fun x => x \in C)) /= addRC (eq_bigr (fun=> 0)).
by rewrite big_const // iter_Rplus mulR0 add0R.
move=> a aC; by rewrite /f (negbTE aC) mul0R.
Qed.

Lemma big_distrr g : \rsum_(t in C) (f t * g t)%R = (/ INR #|C| * \rsum_(t in C) g t)%R.
Proof.
rewrite /= big_distrr /=.
apply eq_bigr => /= i Hi.
by rewrite /f /= Hi /Rdiv mul1R.
Qed.

Definition d : dist A := makeDist f0 f1.

End UniformSupport_sect.
End UniformSupport.

Notation "'`U' HC " := (UniformSupport.d HC) (at level 10, HC at next level) : proba_scope.

(** Distributions over sets with two elements *)

Section bdist_sect.

Variable A : finType.
Hypothesis HA : #|A| = 2%nat.
Variable p : R.
Hypothesis Hp : 0 <= p <= 1.

Definition bdist : dist A.
apply makeDist with [ffun x => if x == Two_set.val0 HA then 1 - p else p].
- move=> a.
  rewrite ffunE.
  case: ifP => _.
  case: Hp => ? ?; fourier.
  by case: Hp.
- rewrite /index_enum -enumT Two_set.enum /=.
  rewrite big_cons /= big_cons /= big_nil addR0 2!ffunE eqxx.
  move: (Two_set.val0_neq_val1 HA).
  rewrite eqtype.eq_sym.
  move/negbTE => ->; by field.
Defined.

End bdist_sect.

(** About distributions over sets with two elements *)

Section charac_bdist_sect.

Variable A : finType.
Variables P Q : dist A.
Hypothesis card_A : #|A| = 2%nat.

Lemma charac_bdist : {r1 | {Hr1 : 0 <= r1 <= 1 & P = bdist card_A Hr1 }}.
Proof.
destruct P as [[pmf pmf0] pmf1].
exists (1 - pmf (Two_set.val0 card_A)).
have Hr1 : 0 <= 1 - pmf (Two_set.val0 card_A) <= 1.
  move: (dist_max (mkDist pmf1) (Two_set.val0 card_A)) => /= H1.
  move: (pmf0 (Two_set.val0 card_A)) => H2.
  split; first by fourier.
  have : forall a, a <= 1 -> 0 <= a -> 1 - a <= 1 by move=> *; fourier.
  by apply.
exists Hr1.
apply dist_eq => /=.
apply pos_fun_eq => /=.
apply FunctionalExtensionality.functional_extensionality => a.
rewrite ffunE.
case: ifP => Ha.
  move/eqP : Ha => ->; by field.
rewrite -pmf1 /index_enum -enumT Two_set.enum.
rewrite big_cons /= big_cons /= big_nil addR0.
move/negbT/Two_set.neq_val0_val1/eqP : Ha => ->.
by field.
Qed.

End charac_bdist_sect.

Local Open Scope proba_scope.

Lemma dist2tuple1 : forall A, dist A -> {dist 1.-tuple A}.
Proof.
move=> A d.
apply makeDist with (fun x => d (thead x)).
move=> a; by apply Rle0f.
rewrite -(pmf1 d); by apply: rsum_1_tuple.
Defined.


Local Open Scope vec_ext_scope.

Lemma dist2rV1 : forall A, dist A -> {dist 'rV[A]_1}.
Proof.
move=> A d.
apply makeDist with (fun x : 'rV[A]_1 => d (x ``_ ord0)).
move=> a; by apply Rle0f.
rewrite -(pmf1 d).
by apply: rsum_rV_1.
Defined.

Local Close Scope vec_ext_scope.

(*Coercion dist2tuple1_coercion := dist2tuple1.*)

Module TupleDist.

Section TupleDist_sect.

Variable A : finType.
Variable P : dist A.
Variable n : nat.

Local Open Scope vec_ext_scope.

Definition f (t : 'rV[A]_n) := \rmul_(i < n) P t ``_ i.

Lemma f0 (t : 'rV[A]_n) : 0 <= f t.
Proof. apply Rle_0_big_mult => ?; by apply Rle0f. Qed.

(** Definition of the product distribution (over a tuple): *)

Lemma f1 : \rsum_(t in 'rV[A]_n) f t = 1.
Proof.
pose P' := fun (a : 'I_n) b => P b.
suff : \rsum_(g : {ffun 'I_n -> A }) \rmul_(i < n) P' i (g i) = 1.

Local Open Scope ring_scope.

  rewrite (reindex_onto (fun j : 'rV[A]_n => finfun (fun x => j ``_ x))
                        (fun i => \row_(j < n) i j)) /=.
  - move=> H; rewrite /f -{2}H {H}.
    apply eq_big => t /=.
    + rewrite inE; apply/esym/eqP/matrixP => a b; by rewrite {a}(ord1 a) mxE ffunE.
    + move=> _; apply eq_bigr => i _ /=; by rewrite ffunE.
  move=> g _.
  apply/ffunP => i; by rewrite ffunE mxE.
rewrite -bigA_distr_bigA /= /P'.
rewrite [X in _ = X](_ : 1 = \rmul_(i < n) 1)%R; last first.
  by rewrite big_const_ord iter_Rmult pow1.
apply eq_bigr => i _; by apply pmf1.
Qed.

Definition d : {dist 'rV[A]_n} := makeDist f0 f1.

End TupleDist_sect.

End TupleDist.

Definition TupleDistd {A : finType} (P : dist A) n := nosimpl TupleDist.d _ P n.

Notation "P `^ n" := (TupleDistd P n) (at level 5) : proba_scope.
Local Open Scope proba_scope.

Local Open Scope vec_ext_scope.

(* TODO: rename *)
Lemma tuple_pmf_singleton A (d : dist A) (i : 'rV[A]_1) :
  forall a : 'rV[A]_1, (d `^ 1) a = d (a ``_ ord0).
Proof.
move=> a.
rewrite /TupleDist.d /= /TupleDist.f /index_enum -enumT enum_ordS big_cons.
rewrite (_ : enum 'I_O = [::]); last by apply size0nil; rewrite size_enum_ord.
by rewrite big_nil mulR1.
Qed.

Local Open Scope ring_scope.

Lemma rsum_rmul_rV_pmf_tnth A n k (P : dist A) :
  \rsum_(t : 'rV[ 'rV[A]_n]_k) \rmul_(m < k) (P `^ n) t ``_ m = 1%R.
Proof.
transitivity (\rsum_(j : {ffun 'I_k -> 'rV[A]_n})
  \rmul_(m : 'I_k) TupleDist.f P (j m)).
  rewrite (reindex_onto (fun p : 'rV_k => [ffun i => p ``_ i]) (fun x : {ffun 'I_k -> 'rV_n} => \row_(i < k) x i)) //=; last first.
    move=> f _.
    apply/ffunP => /= k0.
    by rewrite ffunE mxE.
  apply eq_big => //.
  - move=> v /=.
    by apply/esym/eqP/matrixP => a b; rewrite {a}(ord1 a) mxE ffunE.
  - move=> i _.
    apply eq_bigr => j _; by rewrite ffunE.
rewrite -(bigA_distr_bigA (fun m xn => TupleDist.f P xn)) /= big_const.
rewrite (_ : \rsum_(_ <- _) _ = 1%R); last first.
  transitivity (\rsum_( j : _) P `^ n j) => //; by rewrite pmf1.
by rewrite iter_Rmult pow1.
Qed.

(*
Lemma rsum_rmul_tuple_pmf {A} n k (P : dist A) :
  \rsum_(t in {: 'rV['rV[A]_n]_k}) \big[Rmult/1]_(x <- t) (P `^ n) x = 1.
Proof.
rewrite -[X in _ = X](rsum_rmul_tuple_pmf_tnth n k P).
apply eq_bigr => t _.
rewrite big_tnth /=.
rewrite (reindex_onto (cast_ord (size_tuple t))
  (cast_ord (esym (size_tuple t)))) //=; last first.
  move=> i _; by apply val_inj.
apply eq_big => //= i.
- symmetry.
  apply/val_eqP.
  by apply val_inj.
- move=> _; by rewrite !tvalK tcastE esymK.
Qed.
*)

(** Wolfowitz's counting principle: *)

Section wolfowitz_counting.

Variable B : finType.
Variable P : dist B.
Variable k : nat.
Variable A : {set 'rV[B]_k}.

Lemma wolfowitz a b alpha beta : 0 < alpha -> 0 < beta ->
  a <= \rsum_(x in A) P `^ k x <= b ->
  (forall x : 'rV_k, x \in A -> alpha <= P `^ k x <= beta) ->
  a / beta <= INR #| A | <= b /alpha.
Proof.
move=> Halpha Hbeta H1 H2.
have H3 : \rsum_(x in A) TupleDist.f P x <= INR #|A| * beta.
  have H3 : \rsum_(x in A | predT A ) TupleDist.f P x <= INR #|A| * beta.
    apply Rle_trans with (\rsum_(x in A | predT A) [fun _ => beta] x).
    apply Rle_big_P_f_g_X => i Hi _; by case: (H2 i Hi).
    rewrite -big_filter /= big_const_seq /= iter_Rplus /=.
    apply Rmult_le_compat_r; first by fourier.
    apply Req_le.
    rewrite filter_index_enum count_predT cardE.
    do 2 f_equal.
    apply eq_enum => i; by rewrite /in_mem /= andbC.
  eapply Rle_trans; last by apply H3.
  apply Req_le, eq_bigl => i; by rewrite andbC.
have H4 : INR #|A| * alpha <= \rsum_(x in A) TupleDist.f P x.
  have H4 : INR #|A| * alpha <= \rsum_(x in A | predT A) TupleDist.f P x.
    apply Rle_trans with (\rsum_(x in A | predT A) [fun _ => alpha] x); last first.
      apply Rle_big_P_f_g_X => i Hi _; by case: (H2 i Hi).
    rewrite -big_filter /= big_const_seq /= iter_Rplus /=.
    apply Rmult_le_compat_r; first by fourier.
    apply Req_le.
    rewrite filter_index_enum count_predT cardE.
    do 2 f_equal.
    apply eq_enum => i; by rewrite /in_mem /= andbC.
  eapply Rle_trans; first by apply H4.
  apply Req_le, eq_bigl => i; by rewrite andbC.
case: H1 => H1 H1'.
split.
  apply Rmult_le_reg_l with beta => //.
  rewrite mulRA Rinv_r_simpl_m; last by apply nesym, Rlt_not_eq.
  rewrite mulRC; by eapply Rle_trans; eauto.
apply Rmult_le_reg_l with alpha => //.
rewrite mulRA Rinv_r_simpl_m; last by apply nesym, Rlt_not_eq.
by rewrite mulRC; eapply Rle_trans; eauto.
Qed.

End wolfowitz_counting.

Module ProdDist.

Section ProdDist_sect.

Variables (A B : finType) (P1 : dist A) (P2 : dist B).

Definition f (ab : A * B) := (P1 ab.1 * P2 ab.2)%R.

Lemma f0 (ab : A * B) : 0 <= f ab.
Proof. apply Rmult_le_pos; by apply Rle0f. Qed.

Lemma f1 : \rsum_(ab in {: A * B}) f ab = 1%R.
Proof.
rewrite -(pair_big xpredT xpredT (fun a b => P1 a * P2 b)%R) /= -(pmf1 P1).
apply eq_bigr => a _.
by rewrite -big_distrr /= pmf1 mulR1.
Qed.

Definition d : {dist A * B} := makeDist f0 f1.

Definition proj1 (P : {dist A * B}) : dist A.
apply makeDist with (fun a => \rsum_(b in B) P (a, b)).
- move=> a.
  apply Rle_big_0_P_g => ? _; by apply Rle0f.
- rewrite -(pmf1 P) pair_big /=.
  apply eq_bigr; by case.
Defined.

Definition proj2 (P : {dist A * B}) : dist B.
apply makeDist with (fun b => \rsum_(a in A) P (a, b)).
- move=> a.
  apply: Rle_big_0_P_g => ? _; by apply Rle0f.
- rewrite exchange_big /= -(pmf1 P) pair_big /=.
  apply eq_big; by case.
Defined.

End ProdDist_sect.

End ProdDist.

Notation "P1 `x P2" := (ProdDist.d P1 P2) (at level 6) : proba_scope.

Section tuple_prod_cast.

Variables A B : finType.
Variable n : nat.
Variable P : {dist 'rV[A * B]_n}.

(*
Definition dist_tuple_prod_cast : dist [finType of n.-tuple A * n.-tuple B].
(* begin hide *)
apply makeDist with (fun xy => P (prod_tuple xy)).
(* end hide *)
move=> a; by apply Rle0f.
rewrite -(pmf1 P).
rewrite (reindex_onto (fun x => tuple_prod x) (fun y => prod_tuple y)); last first.
  move=> i _; by rewrite prod_tupleK.
rewrite /=.
apply eq_big => /= i.
- by rewrite inE tuple_prodK eqxx.
- move=> _; by rewrite tuple_prodK.
Defined.
*)

End tuple_prod_cast.

(** * Probability *)

Section probability.

Variable A : finType.
Variable P : dist A.

(** Probability of an event #P#%$P$% with distribution #p#%$p$%
   %($Pr_p[P] = \sum_{i \in A, P\,i} \, p(i)$)%: *)

Definition Pr (E : {set A}) := \rsum_(a in E) P a.

(** Basic properties about probabilities *)

Lemma le_0_Pr E : 0 <= Pr E.
Proof. apply Rle_big_0_P_g => *; by apply Rle0f. Qed.

Lemma Pr_1 E : Pr E <= 1.
Proof. rewrite -(pmf1 P); apply: Rle_big_P_true_f => a; by apply Rle0f. Qed.

Lemma Pr_ext E F : E :=: F -> Pr E = Pr F.
Proof. move=> H; apply eq_bigl => x; by rewrite H. Qed.

Local Open Scope R_scope.

Lemma Pr_0 : Pr set0 = 0.
Proof. rewrite /Pr big_pred0 // => a; by rewrite in_set0. Qed.

Lemma Pr_cplt E : Pr E + Pr (~: E) = 1.
Proof.
rewrite /Pr -bigU /=; last by rewrite -subsets_disjoint.
rewrite -(pmf1 P); apply eq_bigl => /= a.
by rewrite !inE /= orbN.
Qed.

Lemma Pr_to_cplt E : Pr E = 1 - Pr (~: E).
Proof. rewrite -(Pr_cplt E); field. Qed.

Lemma Pr_of_cplt E : Pr (~: E) = 1 - Pr E.
Proof. rewrite -(Pr_cplt E); field. Qed.

Lemma Pr_union E1 E2 : Pr (E1 :|: E2) <= Pr E1 + Pr E2.
Proof.
rewrite /Pr.
rewrite (_ : \rsum_(i in A | [pred x in E1 :|: E2] i) P i =
  \rsum_(i in A | [predU E1 & E2] i) P i); last first.
  apply eq_bigl => x /=; by rewrite inE.
rewrite (_ : \rsum_(i in A | [pred x in E1] i) P i =
  \rsum_(i in A | pred_of_set E1 i) P i); last first.
  apply eq_bigl => x /=; by rewrite unfold_in.
rewrite (_ : \rsum_(i in A | [pred x in E2] i) P i =
  \rsum_(i in A | pred_of_set E2 i) P i); last first.
  apply eq_bigl => x /=; by rewrite unfold_in.
by apply Rle_big_predU_f, Rle0f.
Qed.

Lemma Pr_union_disj E1 E2 :
  E1 :&: E2 = set0 (*NB: use disjoint?*) -> Pr (E1 :|: E2) = (Pr E1 + Pr E2)%R.
Proof.
move=> E1E2.
rewrite -bigU /=; last by rewrite -setI_eq0; apply/eqP.
apply eq_bigl => a /=; by rewrite !inE.
Qed.

Lemma Pr_incl (E E' : {set A}) : (E \subset E') -> Pr E <= Pr E'.
Proof. move=> H; apply Rle_big_f_X_Y; by [apply Rle0f | apply/subsetP]. Qed.

Lemma Pr_bigcup (B : finType) (E : pred B) F :
  Pr (\bigcup_(i | E i) F i) <= \big[Rplus/0]_(i | E i) Pr (F i).
Proof.
rewrite /Pr.
elim: (index_enum _) => [| hd tl IH].
  rewrite big_nil.
  apply: Rle_big_0_P_g => i Hi.
  rewrite big_nil.
  by apply Rle_refl.
rewrite big_cons.
case: ifP => H1.
  move: IH.
  set lhs := \big[Rplus/0]_(_ <- _ | _) _.
  move=> IH.
  eapply Rle_trans.
    eapply Rplus_le_compat_l; by apply IH.
  rewrite [X in _ <= X](exchange_big_dep (fun hd => (hd \in A) && [pred x in \bigcup_(i | E i) F i] hd)) /=; last first.
    move=> b j Pi Fj; apply/bigcupP; by exists b.
  rewrite big_cons /=.
  rewrite H1 big_const iter_Rplus -exchange_big_dep //; last first.
    move=> b j Pi Fj; apply/bigcupP; by exists b.
  apply Rplus_le_compat_r.
  set inr := INR _.
  suff H : 1 <= inr.
    rewrite -{1}(mul1R (P hd)).
    apply Rmult_le_compat_r => //; by apply Rle0f.
  rewrite /inr {inr} (_ : 1 = INR 1) //.
  apply le_INR.
  apply/leP => /=.
  apply/card_gt0P.
  case/bigcupP : H1 => b E_b H1'.
  exists b.
  by rewrite -topredE /= E_b.
eapply Rle_trans; first by apply IH.
apply: Rle_big_P_f_g => b E_b.
rewrite big_cons.
case: ifP => H2.
- set lhs := \big[Rplus/0]_(_ <- _ | _) _.
  rewrite -{1}(add0R lhs).
  by apply Rplus_le_compat_r, Rle0f.
- by apply Rle_refl.
Qed.

End probability.

Section Pr_tuple_prod.

Variables A B : finType.
Variable n : nat.
Variable P : dist [finType of n.-tuple (A * B)%type].
Variable Q : {set [finType of n.-tuple (A * B)%type]}.

(*
Lemma Pr_tuple_prod_cast : Pr (@dist_tuple_prod_cast A B n P) [set x | prod_tuple x \in Q] =
  Pr P Q.
Proof.
rewrite /Pr.
rewrite (reindex_onto (fun x => tuple_prod x) (fun y => prod_tuple y)) /=; last first.
  move=> i _; by rewrite prod_tupleK.
apply eq_big.
move=> tab /=.
  by rewrite !inE tuple_prodK eqxx andbC.
move=> i /= Hi; by rewrite tuple_prodK.
Qed.
*)

End Pr_tuple_prod.

(** * Random Variable *)

(** Definition of a random variable (#R#%$\mathbb{R}$%-valued) with a distribution: *)

Record rvar A := mkRvar {rv_dist : dist A ; rv_fun :> A -> R }.

Definition rvar_of (A : finType) := fun phT : phant (Finite.sort A) => rvar A.

Notation "{ 'rvar' T }" := (rvar_of (Phant T))
  (at level 0, format "{ 'rvar'  T }") : proba_scope.

Notation "`p_ X" := (rv_dist X) (at level 5) : proba_scope.

(** Probability that a random variable evaluates to #r \in R#%$r \in \mathbb{R}$%:*)

Section pr_def.

Variable A : finType.

Definition pr (X : rvar A) r := Pr `p_X [set x | X x == r].

End pr_def.

Notation "'Pr[' X '=' r ']'" := (pr X r) (at level 5, X at next level, r at next level) : proba_scope.

(** Some changes of variables: *)

Local Open Scope R_scope.

Definition scale_rv A k (X : rvar A) :=
  mkRvar `p_X (fun x => k * X x).
Definition add_rv A (X Y : rvar A) (H : `p_X = `p_Y) :=
  mkRvar `p_X (fun x => X x + Y x).
Definition sub_rv A (X Y : rvar A) (H : `p_X = `p_Y) :=
  mkRvar `p_X (fun x => X x - Y x).
Definition trans_add_rv A (X : rvar A) m :=
  mkRvar `p_X (fun x => X x + m).
Definition trans_min_rv A (X : rvar A) m :=
  mkRvar `p_X (fun x => X x - m).
Definition const_rv A cst (X : rvar A) :=
  mkRvar `p_X (fun _ => cst).
Definition comp_rv A (X : rvar A) f :=
  mkRvar `p_X (fun x => f (X x)).
Definition sq_rv A (X : rvar A) := comp_rv X (fun x => x ^ 2).

Notation "k \cst* X" := (@scale_rv _ k X) (at level 49).
Notation "X ''/' n" := (@scale_rv _ (1 / INR n) X) (at level 49, format "X  ''/'  n").
Notation "X \+_( H ) Y" := (@add_rv _ X Y H) (at level 50).
Notation "X \-_( H ) Y" := (@sub_rv _ X Y H) (at level 50).
Notation "X '\+cst' m" := (trans_add_rv X m) (at level 50).
Notation "X '\-cst' m" := (trans_min_rv X m) (at level 50).
Notation "X '\^2' " := (sq_rv X) (at level 49).

(** The ``- log P'' random variable: *)

Definition mlog_rv A (P : dist A) : rvar A := mkRvar P (fun x => - log (P x))%R.

Notation "'--log' P" := (mlog_rv P) (at level 5) : proba_scope.

(** Cast operation: *)

(* TODO: rename *)
Lemma rvar2tuple1 : forall A, rvar A -> {rvar 'rV[A]_1}.
Proof.
move=> A [d f]; apply mkRvar.
- exact (d `^ 1).
- exact (fun x => f (x ``_ ord0)).
Defined.


Definition cast_rv A : 'rV[rvar A]_1 -> {rvar 'rV[A]_1}.
move=> t.
exact (rvar2tuple1 (t ``_ ord0)).
Defined.

Definition img (A : finType) (f : A -> R) :=
  undup (map f (enum A)).

(** * Expected Value *)

Section expected_value_definition.

Variable A : finType.
Variable X : rvar A.

(** Expected value of a random variable: *)

Definition Ex := \rsum_(r <- img X) r * Pr[ X = r ].

(** Alternative (simpler) definition of the expected value: *)

Definition Ex_alt := \rsum_(a in A) X a * `p_X a.

Lemma Ex_Ex_alt : Ex = Ex_alt.
Proof.
rewrite /Ex /Pr.
transitivity (\rsum_(r <- img X) \rsum_(i in A | X i == r) (X i * `p_X i)).
  apply eq_bigr => r _.
  rewrite big_distrr /=.
  apply congr_big => //= a.
  by rewrite inE.
  by rewrite inE; move/eqP => ->.
by rewrite /img -sum_parti_finType.
Qed.

Lemma Ex_alt_pos : (forall a, 0 <= X a) -> 0 <= Ex_alt.
Proof.
move=> HZ.
rewrite /Ex_alt.
apply: Rle_big_0_P_g => i _.
apply Rmult_le_pos; by [apply HZ | apply Rle0f].
Qed.

End expected_value_definition.

Notation "'`E'" := (Ex_alt) (at level 5) : proba_scope.

Section expected_value_for_standard_random_variables.

Variable A : finType.
Variables X Y : rvar A.

(** Properties of the expected value of standard random variables: *)

Lemma E_scale k : `E (k \cst* X) = k * `E X.
Proof.
rewrite /scale_rv /Ex_alt /= big_distrr /=.
apply eq_bigr => i Hi; by rewrite -mulRA.
Qed.

Lemma E_num_int_add (H : `p_X = `p_Y) : `E (X \+_(H) Y) = `E X + `E Y.
Proof.
rewrite /Ex_alt -big_split /=.
apply eq_bigr => i i_A /=; by rewrite mulRDl H.
Qed.

Lemma E_num_int_sub (H : `p_X = `p_Y) : `E (X \-_(H) Y) = `E X - `E Y.
Proof.
rewrite (_ : `E X - `E Y = `E X + - 1 * `E Y)%R; last by field.
rewrite {3}/Ex_alt big_distrr /= -big_split /= /Ex_alt.
apply eq_bigr => i i_A /=; rewrite H; field.
Qed.

Lemma E_const k : `E (const_rv k X) = k.
Proof. by rewrite /Ex_alt /= -big_distrr /= pmf1 mulR1. Qed.

Lemma E_trans_add_rv m : `E (X \+cst m) = `E X + m.
Proof.
rewrite /Ex_alt /trans_add_rv /=.
transitivity (\rsum_(i in A) (X i * `p_X i + m * `p_X i)).
  apply eq_bigr => i Hi /=; field.
by rewrite big_split /= -big_distrr /= pmf1 mulR1.
Qed.

Lemma E_trans_id_rem m :
  `E ( (X \-cst m) \^2) = `E (X \^2 \-_( Logic.eq_refl ) (2 * m \cst* X) \+cst (m ^ 2)).
Proof. rewrite /Ex_alt /=; apply eq_bigr => i Hi; field. Qed.

Lemma E_comp f k : (forall x y, f (x * y) = f x * f y) ->
  `E (comp_rv (k \cst* X) f) = `E (f k \cst* (comp_rv X f)).
Proof.
move=> H; rewrite /comp_rv /= /Ex_alt /=.
apply eq_bigr => i i_in_A; rewrite H; field.
Qed.

Lemma E_comp_rv_ext f : `p_X = `p_Y -> rv_fun X = rv_fun Y ->
  `E (comp_rv X f) = `E (comp_rv Y f).
Proof. move=> H1 H2; by rewrite /Ex_alt /comp_rv /= H1 H2. Qed.

End expected_value_for_standard_random_variables.

Lemma E_rvar2tuple1 A : forall (X : rvar A), `E (rvar2tuple1 X) = `E X.
Proof.
case=> d f.
rewrite /Ex_alt /rvar2tuple1 /=.
apply rsum_rV_1 => // m.
by rewrite -tuple_pmf_singleton.
Qed.

(* TODO: move *)
Lemma RltnNge r1 r2 : (r1 <b r2) = ~~ (r1 >b= r2).
Proof.
rewrite /Rlt_bool /Rge_bool.
destruct (Rlt_dec) as [H|H]; destruct (Rge_dec) as [H'|H'] => //.
by fourier.
apply Rnot_lt_le in H.
apply Rnot_ge_gt in H'.
by fourier.
Qed.

Section markov_inquality.

Variable A : finType.
Variable X : rvar A.
Hypothesis X_nonneg : forall a, 0 <= X a.

Definition pr_geq (X : rvar A) r := Pr `p_X [set x | X x >b= r].

Notation "'Pr[' X '>=' r ']'" := (pr_geq X r) (at level 5, X at next level, r at next level, format "Pr[  X  >=  r  ]") : proba_scope.

Lemma markov (r : R) : 0 < r -> Pr[X >= r] <= `E X / r.
Proof.
move=> r_pos.
rewrite /Rdiv.
apply: (Rmult_le_reg_l r) => //.
rewrite -Rmult_assoc.
rewrite Rinv_r_simpl_m; last first.
  apply: not_eq_sym.
  by apply: Rlt_not_eq.
rewrite /Ex_alt.
rewrite (bigID [pred a' | X a' >b= r]) /=.
rewrite -[a in a <= _]Rplus_0_r.
apply Rplus_le_compat; last first.
  apply Rle_big_0_P_g => a' _.
  apply Rmult_le_pos.
  by apply X_nonneg.
  by apply Rle0f.
apply (Rle_trans _ (\rsum_(i | X i >b= r) r * `p_ X i)).
  rewrite big_distrr /=.
  apply Req_le.
  apply eq_bigl.
  move=> a'.
  by rewrite inE.
apply Rle_big_P_f_g.
move=> a' Xa'r.
apply Rmult_le_compat_r.
apply Rle0f.
by apply/RleP.
Qed.

End markov_inquality.

(** * Variance *)

Section variance_definition.

Variable A : finType.
Variable X : rvar A.

(** Variance of a random variable %($\sigma^2(X) = V(X) = E (X^2) - (E X)^2$)%: *)

Definition Var := let miu := `E X in `E ((X \-cst miu) \^2).

(** Alternative form for computing the variance
   %($V(X) = E(X^2) - E(X)^2$ \cite[Theorem 6.6]{probook})%: *)

Lemma V_alt : Var = `E (X \^2)  - (`E X) ^ 2.
Proof. rewrite /Var E_trans_id_rem E_trans_add_rv E_num_int_sub E_scale; field. Qed.

End variance_definition.

Notation "'`V'" := (Var) (at level 5) : proba_scope.

Section variance_properties.

Variable A : finType.
Variable X : rvar A.

(** The variance is not linear %$V (k X) = k^2 V (X)$ \cite[Theorem 6.7]{probook}%: *)

Lemma V_scale k : `V (k \cst* X) = k ^ 2 * `V X.
Proof.
rewrite {1}/`V [in X in X = _]/= E_scale.
rewrite (@E_comp_rv_ext _ ((k \cst* X) \-cst k * `E X) (k \cst* (X \+cst - `E X))) //; last first.
  rewrite /=; apply FunctionalExtensionality.functional_extensionality => x; field.
rewrite E_comp; last by move=> x y; field.
by rewrite E_scale.
Qed.

End variance_properties.

Lemma V_rvar2tuple1 A : forall (X : rvar A), `V (rvar2tuple1 X) = `V X.
Proof.
case=> d f.
rewrite /`V !E_rvar2tuple1 /Ex_alt /=.
apply: rsum_rV_1 => // i.
by rewrite /TupleDist.f big_ord_recl /= big_ord0 2!mulR1 -tuple_pmf_singleton.
Qed.

(** * Chebyshev's Inequality *)

(** (Probabilistic statement.)
 In any data sample, "nearly all" the values are "close to" the mean value:
 %$Pr[ |X - E X| \geq \epsilon] \leq V(X) / \epsilon^2$% *)

Section chebyshev.

Variable A : finType.
Variable X : rvar A.

Lemma chebyshev_inequality epsilon : 0 < epsilon ->
  Pr `p_X [set a | Rabs (X a - `E X) >b= epsilon] <= `V X / epsilon ^ 2.
Proof.
move=> He.
apply (Rmult_le_reg_l _ _ _ (pow_gt0 He 2)).
rewrite [in X in _ <= X]mulRC /Rdiv -(mulRA _ (/ epsilon ^ 2) (epsilon ^ 2)) -Rinv_l_sym; [rewrite mulR1 | by apply Rgt_not_eq, pow_gt0].
rewrite /`V {2}/Ex_alt.
rewrite (_ : `p_ ((X \-cst `E X) \^2) = `p_ X) //.
apply Rle_trans with (\rsum_(a in A | Rabs (X a - `E X) >b= epsilon)
    (((X \-cst `E X) \^2) a  * `p_X a)%R); last first.
  apply Rle_big_P_true_f => a.
  apply Rmult_le_pos; by [apply Rle0f | rewrite /= -/(_ ^2); apply le_sq].
rewrite /Pr big_distrr [_ \^2]lock /= -!lock.
apply Rle_big_P_Q_f_g => // i Hi; rewrite /= -!/(_ ^ 2).
- apply Rmult_le_compat_r; first by apply Rle0f.
  rewrite inE in Hi.
  move/RgeP/Rge_le in Hi.
  apply sq_incr in Hi.
  + by rewrite Rabs_sq in Hi.
  + by apply Rlt_le.
  + by apply Rabs_pos.
- apply Rmult_le_pos.
  by apply le_sq.
  by apply Rle0f.
- rewrite inE in Hi.
  move/RgeP in Hi.
  by apply/RgeP.
Qed.

End chebyshev.

(** * Joint Distribution *)

Section joint_dist.

Variable A : finType.
Variable P1 : dist A.
Variable n : nat.
Variable P2 : {dist 'rV[A]_n}.
Variable P : {dist 'rV[A]_n.+1}.

Definition joint :=
  (forall x, P1 x = \rsum_(t in 'rV[A]_n.+1 | t ``_ ord0 == x) P t) /\
  (forall x, P2 x = \rsum_(t in 'rV[A]_n.+1 | rbehead t == x) P t).

End joint_dist.

(* TODO: move and rename *)
Lemma TupleDist0 {B : finType} (x : 'rV[B]_0) P : P `^ 0 x = 1.
Proof. by rewrite /= /TupleDist.f big_ord0. Qed.

Lemma TupleDist1 {B : finType} (x : 'rV[B]_1) P : P `^ 1 x = P (x ``_ ord0).
Proof. by rewrite /= /TupleDist.f big_ord_recl big_ord0 mulR1. Qed.

Lemma TupleDistn {B : finType} {n} (x : 'rV[B]_n.+1) P : P `^ n.+1 x = (P (x ``_ ord0) * P `^ n (rbehead x))%R.
Proof.
rewrite /= /TupleDist.f big_ord_recl.
congr (_ * _)%R.
apply eq_bigr => i _.
by rewrite /rbehead mxE.
Qed.

(* begin hide *)
Lemma joint_prod_n_base_case A (P : dist A) : joint P (P `^ O) (P `^ 1).
Proof.
rewrite /joint; split => x.
- rewrite (big_pred1 (\row_(j < 1) x)); first by rewrite TupleDist1 mxE.
  move=> /= m.
  apply/eqP/eqP => [<- | ->].
    by apply/matrixP => a b; rewrite {a}(ord1 a) {b}(ord1 b) mxE.
  by rewrite mxE.
- rewrite TupleDist0 -(pmf1 (P `^ 1)).
  apply eq_bigl => /= m.
  rewrite inE.
  apply/esym/eqP.
  rewrite /rbehead.
  by apply/matrixP => a [].
Qed.
(* end hide *)

(** The tuple distribution is a joint distribution: *)

Lemma joint_prod_n : forall n A (P : dist A), joint P (P `^ n) (P `^ n.+1).
Proof.
case; first by apply joint_prod_n_base_case.
move=> n B d; split => x.
- transitivity (\rsum_(i in 'rV[B]_n.+1) (d `^ n.+1) i * d x)%R.
    by rewrite -big_distrl /= (pmf1 (d `^ n.+1)) mul1R.
  rewrite -big_head_rbehead.
  apply eq_bigr => i Hi.
  by rewrite [in X in _ = X]TupleDistn mulRC row_mx_row_ord0 rbehead_row_mx.
- rewrite -big_head_big_behead.
  transitivity (\rsum_(i in B) d i * (d `^ n.+1 x))%R.
    by rewrite -big_distrl /= (pmf1 d) mul1R.
  apply eq_bigr => i _.
  rewrite [in X in _ = X]TupleDistn.
  by rewrite row_mx_row_ord0 rbehead_row_mx.
Qed.

(** * Identically Distributed Random Variables *)

Section identically_distributed.

Variable A : finType.
Variable P : dist A.
Variable n : nat.

(** The random variables %$Xs$%#Xs# are identically distributed with distribution %$P$%#P#: *)

(*Definition id_dist (Xs : n.-tuple (rvar A)) := forall i, `p_(Xs \_ i) = P.*)
Definition id_dist (Xs : 'rV[rvar A]_n) := forall i, `p_(Xs ``_ i) = P.

End identically_distributed.

(** * Independent random variables *)

Section independent_random_variables.

Variable A : finType.
Variable X : rvar A.
Variable n : nat.
Variable Y : {rvar 'rV[A]_n}.
Variable P : {dist 'rV[A]_n.+1}.

Definition inde_rv := forall x y,
  Pr P [set xy : 'rV_n.+1 | (X (xy ``_ ord0) == x) && (Y (rbehead xy) == y)] =
  (Pr[X = x] * Pr[Y = y])%R.

End independent_random_variables.

Notation "X _| P |_ Y" := (inde_rv X Y P) (at level 50) : proba_scope.

(** Independent random variables over the tuple distribution: *)

Lemma inde_rv_tuple_pmf_dist A (P : dist A) n (x y : R) (Xs : 'rV[rvar A]_n.+2) :
  id_dist P Xs ->
    Pr (P `^ n.+2) [set xy : 'rV__ | (- log (P (xy ``_ ord0)) == x)%R &&
      (\rsum_(i : 'I_n.+1)
       - log (`p_ ((rbehead Xs) ``_ i) (rbehead xy) ``_ i) == y)%R] =
    (Pr P [set a | - log (P a) == x] *
    Pr (P `^ n.+1) [set ta : 'rV__ |
      \rsum_(i : 'I_n.+1) - log (`p_ ((rbehead Xs) ``_ i) ta ``_ i) == y])%R.
Proof.
move=> Hid_dist.
rewrite /Pr.
move: (big_head_rbehead_P_set A n.+1
  (fun i : 'rV[A]_n.+2 => P `^ _ i)
  [set a | (- log (P a) == x)%R]
  [set t : 'rV__ | \rsum_(i < n.+1) - log (`p_ ((rbehead Xs) ``_ i) t ``_ i) == y])%R => H.
eapply trans_eq.
  eapply trans_eq; last by symmetry; apply H.
  apply eq_bigl => ta /=; by rewrite !inE.
transitivity (\rsum_(a in [set a | (- log (P a) == x)%R])
  \rsum_(a' in [set ta : 'rV__ | \rsum_(i < n.+1) - log (`p_ ((rbehead Xs) ``_ i) ta ``_ i) == y])
  P a * P `^ _ a')%R.
  apply eq_bigr => a _.
  apply eq_bigr => ta _.
  by rewrite TupleDistn row_mx_row_ord0 rbehead_row_mx.
rewrite big_distrl /=.
apply eq_bigr => a _; by rewrite -big_distrr.
Qed.

(** * Sum of Random Variables *)

(** The sum of two random variables: *)

Section sum_two_rand_var_def.

Variable A : finType.
Variable X1 : rvar A.
Variable n : nat.
Variable X2 : {rvar 'rV[A]_n.+1}.
Variable X : {rvar 'rV[A]_n.+2}.

Definition sum := joint `p_X1 `p_X2 `p_X /\
  X =1 fun x => (X1 (x ``_ ord0) + X2 (rbehead x))%R.

End sum_two_rand_var_def.

Notation "Z \= X '@+' Y" := (sum X Y Z) (at level 50) : proba_scope.

Section sum_two_rand_var.

Variable A : finType.
Variable X1 : rvar A.
Variable n : nat.
Variable X2 : {rvar 'rV[A]_n.+1}.
Variable X : {rvar 'rV[A]_n.+2}.

(** The expected value of a sum is the sum of expected values,
   whether or not the summands are mutually independent
   (the ``First Fundamental Mystery of Probability''% \cite[Theorem 6.2]{probook}%): *)

Lemma E_linear_2 : X \= X1 @+ X2 -> `E X = (`E X1 + `E X2)%R.
Proof.
case=> Hjoint Hsum.
rewrite /Ex_alt /=.
transitivity (\rsum_(ta in 'rV[A]_n.+2)
  (X1 (ta ``_ ord0) * `p_X ta + X2 (rbehead ta) * `p_X ta)%R).
- apply eq_bigr => ta _; by rewrite Hsum mulRDl.
- rewrite big_split => //=; f_equal.
  + transitivity (\rsum_(a in A) (X1 a * \rsum_(ta in 'rV[A]_n.+1) `p_X (row_mx (\row_(k < 1) a) ta)))%R.
    * rewrite -big_head_behead.
      apply eq_bigr => a _.
      rewrite big_distrr /=.
      apply eq_bigr => i _.
      by rewrite row_mx_row_ord0.
    * apply eq_bigr => a _.
      case: Hjoint.
      move/(_ a) => /= -> _.
      by rewrite big_head_rbehead.
  + transitivity (\rsum_(ta in 'rV[A]_n.+1) (X2 ta * \rsum_(a in A) `p_X (row_mx (\row_(k < 1) a) ta))%R).
    * rewrite -(@big_head_behead _ (n.+1)) exchange_big /=.
      apply eq_bigr => ta _; rewrite big_distrr /=.
      apply eq_bigr => a _.
      by rewrite rbehead_row_mx.
    * apply eq_bigr => ta _.
      case: Hjoint => _.
      move/(_ ta) => /= ->.
      by rewrite -big_head_big_behead.
Qed.

(* TODO: relation with theorem 6.4 of probook (E(XY)=E(X)E(Y))? *)

Lemma E_id_rem_helper : X \= X1 @+ X2 -> X1 _| `p_X |_ X2 ->
  \rsum_(i in 'rV[A]_n.+2)(X1 (i ``_ ord0) * X2 (rbehead i) * `p_X i)%R =
    (`E X1 * `E X2)%R.
Proof.
case=> Hjoint Hsum Hinde.
rewrite -2!Ex_Ex_alt /=.
apply trans_eq with (\rsum_(r <- undup (map X1 (enum A)))
   \rsum_(r' <- undup (map X2 (enum ('rV[A]_n.+1))))
   ( r * r' * Pr[ X1 = r] * Pr[ X2 = r' ]))%R; last first.
  symmetry.
  rewrite big_distrl /=.
  apply eq_bigr => i _.
  rewrite big_distrr /=.
  apply eq_bigr => j _.
  rewrite mulRA. f_equal. rewrite -!mulRA. f_equal. by rewrite mulRC.
rewrite -big_head_behead.
apply trans_eq with (\rsum_(a in A) \rsum_(j in 'rV[A]_n.+1)
  (X1 a * X2 j * `p_X (row_mx (\row_(k < 1) a) j)))%R.
  apply eq_bigr => a _.
  apply eq_bigr => ta _.
  by rewrite row_mx_row_ord0 rbehead_row_mx.
rewrite (@sum_parti _ _ X1); last by rewrite /index_enum -enumT; apply enum_uniq.
rewrite /index_enum -enumT.
apply eq_bigr => r _.
rewrite {1}enumT exchange_big /= (@sum_parti _ _ X2); last first.
  rewrite /index_enum -enumT; by apply enum_uniq.
rewrite /index_enum -enumT.
apply eq_bigr => r' _.
apply trans_eq with (r * r' * \rsum_(i0 | X2 i0 == r') \rsum_(i1 | X1 i1 == r)
    (`p_X (row_mx (\row_(k < 1) i1) i0)))%R.
  rewrite big_distrr /= /index_enum -!enumT.
  apply eq_bigr => ta ta_r'.
  rewrite big_distrr /=.
  apply eq_bigr => a a_l.
  move/eqP : ta_r' => <-.
  by move/eqP : a_l => <-.
rewrite -!mulRA.
congr (_ * (_ * _))%R.
rewrite exchange_big /=.
move: {Hinde}(Hinde r r') => <-.
rewrite /Pr.
move: (big_head_rbehead_P_set _ _ (fun a => `p_ X a) [set j0 | X1 j0 == r] [set i0 | X2 i0 == r']) => H'.
eapply trans_eq.
  eapply trans_eq; last by apply H'.
  apply eq_big.
    move=> a /=; by rewrite inE.
  move=> a /eqP Ha.
  apply eq_bigl => ta /=; by rewrite inE.
apply eq_bigl => ta /=; by rewrite !inE.
Qed.

(** Expected Value of the Square (requires mutual independence): *)

Lemma E_id_rem : X \= X1 @+ X2 -> X1 _| `p_X |_ X2 ->
  `E (X \^2) = (`E (X1 \^2) + 2 * `E X1 * `E X2 + `E (X2 \^2))%R.
Proof.
case=> Hsum1 Hsum2 Hinde.
rewrite {1}/Ex_alt.
apply trans_eq with (\rsum_(i in 'rV[A]_n.+2)
      ((X1 (i ``_ ord0) + X2 (rbehead i)) ^ 2%N * `p_X i))%R.
  apply eq_bigr => i _; by rewrite /sq_rv /= Hsum2.
apply trans_eq with (\rsum_(i in 'rV[A]_n.+2)
      ((X1 (i ``_ ord0)) ^ 2 + 2 * X1 (i ``_ ord0) * X2 (rbehead i) + (X2 (rbehead i)) ^ 2) * `p_X i)%R.
  apply eq_bigr => i _; by rewrite id_rem_plus.
apply trans_eq with (\rsum_(i in 'rV[A]_n.+2)
      ((X1 (i ``_ ord0)) ^ 2 * `p_X i +  2 * X1 (i ``_ ord0) * X2 (rbehead i) * `p_X i +
        (X2 (rbehead i)) ^ 2 * `p_X i))%R.
  apply eq_bigr => i Hi; by field.
rewrite !big_split [pow]lock /= -lock.
f_equal.
- f_equal.
  + rewrite /Ex_alt -big_head_behead /=.
    apply eq_bigr => i _.
    apply trans_eq with (X1 i ^ 2 * \rsum_(j in 'rV[A]_n.+1) `p_X (row_mx (\row_(k < 1) i) j))%R.
    * rewrite big_distrr /=.
      apply eq_bigr => i0 _.
      by rewrite row_mx_row_ord0.
    * congr (_ * _)%R.
      case: Hsum1 => -> _.
      by apply big_head_rbehead.
  + rewrite -mulRA -(E_id_rem_helper (conj Hsum1 Hsum2)) // big_distrr /=.
    apply eq_bigr => i _; field.
- rewrite /Ex_alt -big_head_behead.
  rewrite exchange_big /=.
  apply eq_bigr => t _.
  apply trans_eq with (X2 t ^ 2 * \rsum_(i0 in A) (`p_X (row_mx (\row_(k < 1) i0) t)))%R.
  + rewrite big_distrr [pow]lock /= -lock //; apply eq_bigr => i0 Hi0.
    by rewrite rbehead_row_mx.
  + congr (_ * _)%R.
    case: Hsum1 => _ ->.
    by apply big_head_big_behead.
Qed.

(** The variance of the sum is the sum of variances for any two
  independent random variables %(\cite[Theorem 6.8]{probook})%: *)

Lemma V_linear_2 : X \= X1 @+ X2 -> X1 _| `p_X |_ X2  -> `V X = (`V X1 + `V X2)%R.
Proof.
move=> Hsum Hinde.
rewrite !V_alt E_id_rem // (E_linear_2 Hsum) id_rem_plus; by field.
Qed.

End sum_two_rand_var.

Section sum_n_rand_var_def.

Variable A : finType.

(** The sum of #n >= 1#%$n \geq 1$% random variable(s): *)

Reserved Notation "X '\=sum' Xs" (at level 50).

Inductive sum_n : forall n,
  {rvar 'rV[A]_n} -> 'rV[rvar A]_n -> Prop :=
| sum_n_1 : forall X, cast_rv X \=sum X
| sum_n_cons : forall n (Xs : 'rV_n.+1) Y X Z,
  Y \=sum Xs -> Z \= X @+ Y -> Z \=sum (row_mx (\row_(k < 1) X) Xs)
where "X '\=sum' Xs" := (sum_n X Xs) : proba_scope.

End sum_n_rand_var_def.

Notation "X '\=sum' Xs" := (sum_n X Xs) (at level 50) : proba_scope.

Section sum_n_rand_var.

Variable A : finType.

Lemma E_linear_n : forall n (Xs : 'rV[rvar A]_n) X,
  X \=sum Xs -> `E X = \rsum_(i < n) `E Xs ``_ i.
Proof.
elim => [Xs Xbar | [_ Xs Xbar | n IHn Xs Xbar] ].
- by inversion 1.
- inversion 1; subst.
  apply Eqdep_dec.inj_pair2_eq_dec in H0; last by exact eq_nat_dec.
  apply Eqdep_dec.inj_pair2_eq_dec in H1; last by exact eq_nat_dec.
  subst Xs Xbar.
  rewrite big_ord_recl big_ord0 addR0 /cast_rv.
  by rewrite E_rvar2tuple1.
- inversion 1; subst.
  apply Eqdep_dec.inj_pair2_eq_dec in H1; last by exact eq_nat_dec.
  apply Eqdep_dec.inj_pair2_eq_dec in H2; last by exact eq_nat_dec.
  subst Z Xs.
  move: {IHn}(IHn _ _ H3) => IHn'.
  rewrite big_ord_recl.
  have -> : \rsum_(i : 'I_n.+1) `E ((row_mx (\row_(k < 1) X) Xs0) ``_ (lift ord0 i)) =
       \rsum_(i : 'I_n.+1) `E (Xs0 ``_ i).
    apply eq_bigr => i _ /=.
    rewrite /`E /=.
    apply eq_bigr => a _ /=.
    set tmp := row_mx _ _ _ _.
    suff : tmp = Xs0 ``_ i by move=> ->.
    rewrite /tmp.
    rewrite mxE.
    case: splitP => //.
      by move=> j; rewrite {j}(ord1 j).
    move=> k.
    by rewrite lift0 add1n => [] [] /ord_inj ->.
  rewrite -IHn' (E_linear_2 H4).
  by rewrite row_mx_row_ord0.
Qed.

End sum_n_rand_var.

Section sum_n_independent_rand_var_def.

Variable A : finType.

(** The sum of #n >= 1#%$n \geq 1$% independent random variables: *)

Reserved Notation "X '\=isum' Xs" (at level 50).

Inductive isum_n : forall n,
  {rvar 'rV[A]_n} -> 'rV[rvar A]_n -> Prop :=
| isum_n_1 : forall X, cast_rv X \=isum X
| isum_n_cons : forall n (Ys : 'rV_n.+1) Y X Z,
  Y \=isum Ys -> Z \= X @+ Y -> X _| `p_Z |_ Y ->
  Z \=isum (row_mx (\row_(k < 1) X) Ys)
where "X '\=isum' Xs" := (isum_n X Xs) : proba_scope.

End sum_n_independent_rand_var_def.

Notation "X '\=isum' Xs" := (isum_n X Xs) (at level 50) : proba_scope.

Section sum_n_independent_rand_var.

Variable A : finType.

Lemma sum_n_i_sum_n : forall n (Xs : 'rV[rvar A]_n) X,
  X \=isum Xs -> X \=sum Xs.
Proof.
move=> n Xs Xsum.
elim.
- move=> X; by constructor 1.
- move=> n0 lst Z W Z' H1 H2 H3 H4.
  by econstructor 2; eauto.
Qed.

Lemma V_linearity_isum : forall n
  (X : {rvar 'rV[A]_n}) (Xs : 'rV[rvar A]_n),
  X \=isum Xs ->
  forall sigma2, (forall i, `V (Xs ``_ i) = sigma2) ->
  `V X = (INR n * sigma2)%R.
Proof.
elim.
  move=> X Xs X_Xs sigma2 Hsigma2.
  by inversion X_Xs.
case=> [_ | n IH] Xsum Xs Hsum s Hs.
  inversion Hsum.
  apply Eqdep_dec.inj_pair2_eq_dec in H; last by exact eq_nat_dec.
  apply Eqdep_dec.inj_pair2_eq_dec in H0; last by exact eq_nat_dec.
  subst Xs Xsum.
  rewrite /cast_rv V_rvar2tuple1 /= mul1R.
  by apply Hs.
have {IH}IH : forall Xsum (Xs : 'rV[rvar A]_n.+1),
  Xsum \=isum Xs ->
  forall sigma2, (forall i, `V (Xs ``_ i) = sigma2) ->
    `V Xsum = (INR n.+1 * sigma2)%R by apply IH.
move: Hsum; inversion 1.
apply Eqdep_dec.inj_pair2_eq_dec in H0; last by exact eq_nat_dec.
apply Eqdep_dec.inj_pair2_eq_dec in H1; last by exact eq_nat_dec.
subst Z n0 Xs.
move: {IH}(IH Y Ys H2) => IH.
rewrite S_INR mulRDl -IH.
+ by rewrite mul1R addRC (@V_linear_2 _ _ _ _ _ H3) // -(Hs ord0) /= row_mx_row_ord0.
+ move=> i; rewrite -(Hs (lift ord0 i)).
  congr (`V _).
  rewrite mxE.
  case: splitP.
    move=> j; by rewrite {j}(ord1 j) lift0.
  move=> k.
  rewrite lift0 add1n.
  by case => /ord_inj ->.
Qed.

(** The variance of the average for independent random variables: *)

Lemma V_average_isum n (X : {rvar 'rV[A]_n}) Xs (sum_Xs : X \=isum Xs) :
  forall sigma2, (forall i, `V (Xs ``_ i) = sigma2) ->
  (INR n * `V (X '/ n))%R = sigma2.
Proof.
move=> s Hs.
destruct n.
  by inversion sum_Xs.
rewrite (V_scale X) // (V_linearity_isum sum_Xs Hs) //; field; by apply not_0_INR.
Qed.

End sum_n_independent_rand_var.

(** * The Weak Law of Large Numbers *)

Section weak_law_of_large_numbers.

Variable A : finType.
Variable P : dist A.
Variable n : nat.
Variable Xs : 'rV[rvar A]_n.+1.     Hypothesis Xs_id : id_dist P Xs.
Variable miu : R.                   Hypothesis E_Xs : forall i, `E Xs ``_ i = miu.
Variable sigma2 : R.                Hypothesis V_Xs : forall i, `V Xs ``_ i = sigma2.
Variable X : {rvar 'rV[A]_n.+1}.
Variable X_Xs : X \=isum Xs.

Lemma wlln epsilon : 0 < epsilon ->
  Pr `p_X [set t | Rabs ((X '/ n.+1) t - miu) >b= epsilon] <= sigma2 / ((INR n.+1) * epsilon ^ 2).
Proof.
move=> He.
have HV : `V (X '/ n.+1) = sigma2 / INR n.+1.
  rewrite -(V_average_isum X_Xs V_Xs) V_scale //; by field; apply not_0_INR.
rewrite /Rdiv Rinv_mult_distr; last 2 first.
  by apply not_0_INR.
  by apply Rgt_not_eq, pow_gt0.
rewrite mulRA (_ : sigma2 * / INR n.+1 = sigma2 / INR n.+1)%R // -{}HV.
have HE : `E (X '/ n.+1) = miu.
  rewrite E_scale (E_linear_n (sum_n_i_sum_n X_Xs)).
  set su := \rsum_(_<-_) _.
  have -> : su = (INR n.+1 * miu)%R.
    rewrite /su.
    transitivity (\rsum_(i < n.+1) miu); first by apply eq_bigr.
    by rewrite big_const /= iter_Rplus cardE /= size_enum_ord.
  by field; apply not_0_INR.
rewrite -{}HE.
have cheby : Pr `p_(X '/ n.+1)
  [set t | Rabs (X t / INR n.+1 - `E (X '/ n.+1)) >b= epsilon] <= `V (X '/ n.+1) / epsilon ^ 2.
  move: (chebyshev_inequality (X '/ n.+1) He) => cheby.
  set g := [set _ | _] in cheby; rewrite (@Pr_ext _ _ _ g) //.
  apply/setP => ta /=.
  by rewrite !inE /= mulRC mulRA mulR1.
set p1 := Pr _ _ in cheby. set p2 := Pr _ _. suff : p2 = p1 by move=> ->.
rewrite /p1 /p2 /=.
apply Pr_ext; apply/setP => ta /=; by rewrite !inE mulRC /Rdiv mul1R.
Qed.

End weak_law_of_large_numbers.
