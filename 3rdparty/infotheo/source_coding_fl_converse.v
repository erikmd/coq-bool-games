(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div choice fintype.
From mathcomp Require Import tuple finfun bigop prime binomial ssralg finset fingroup finalg matrix.
Require Import Reals Fourier.
Require Import Rssr Reals_ext log2 Rbigop proba entropy aep typ_seq source_code.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope source_code_scope.
Local Open Scope entropy_scope.
Local Open Scope reals_ext_scope.

Section source_coding_converse'.

Variable A : finType.
Variable P : dist A.
Variables num den : nat.
Let r := INR num / INR den.+1.
Hypothesis Hr : 0 < r < `H P.

Variable n : nat.
Variable k : nat.
Variable sc : scode_fl A k.+1 n.
Hypothesis r_sc : r = SrcRate sc.

Variable epsilon : R.
Hypothesis Hepsilon : 0 < epsilon < 1.

Notation "'max(' x ',' y ')'" := (Rmax x y) : reals_ext_scope.

Definition lambda := min((1 - epsilon) / 2, (`H P - r) / 2).
Definition delta := min((`H P - r) / 2, lambda / 2).

Definition SrcConverseBound := max(max(
  aep_bound P delta, - ((log delta) / (`H P - r - delta))), INR n / r).

Hypothesis Hk : SrcConverseBound <= INR k.+1.

Lemma Hr1 : 0 < (`H P - r) / 2.
Proof.
apply Rlt_mult_inv_pos; last by fourier.
case: Hr => ? ?; fourier.
Qed.

Lemma Hepsilon1 : 0 < (1 - epsilon) / 2.
Proof.
apply Rlt_mult_inv_pos; last by fourier.
case: Hepsilon => ? ? ;fourier.
Qed.

Lemma Hlambda : 0 < lambda.
Proof. rewrite /lambda; apply P_Rmin => //; [exact Hepsilon1 | exact Hr1]. Qed.

Lemma Hdelta : 0 < delta.
Proof.
rewrite /delta.
apply Rmin_pos.
case: Hr => ? ?; apply Rlt_mult_inv_pos; fourier.
apply Rlt_mult_inv_pos; [exact Hlambda | fourier].
Qed.

Definition e0 := `H P - r.

Lemma e0_delta : e0 <> delta.
Proof.
rewrite /e0 /delta /lambda -/r.
apply Rmin_case_strong => H1.
- apply neq_Rdiv.
  case: Hr => ? ? ?; fourier.
  move=> ?; fourier.
  move=> ?; fourier.
- apply Rmin_case_strong => H2.
  + apply nesym, Rlt_not_eq.
    eapply Rle_lt_trans.
    * eapply Rle_trans; last by apply H2.
      apply Rdiv_le; last by fourier.
      by apply Rlt_le, Hepsilon1.
    * apply Rdiv_lt; last by fourier.
      case: Hr => ? ?; fourier.
  + rewrite /Rdiv -mulRA (_ : ( _ * / 2 ) = / 4); last by field.
    apply neq_Rdiv.
    case: Hr => ? ? ?; fourier.
    move=> ?; fourier.
    move=> ?; fourier.
Qed.

Definition no_failure := [set x : 'rV[A]_k.+1 | dec sc (enc sc x) == x].

Lemma no_failure_sup : INR #| no_failure | <= exp2 (INR k.+1 * (`H P - e0)).
Proof.
apply Rle_trans with (exp2 (INR n)).
  rewrite /no_failure.
  have Hsubset : [set x | dec sc (enc sc x) == x] \subset dec sc @: (enc sc @: [set: 'rV[A]_k.+1]).
    apply/subsetP => x.
    rewrite inE => Hx.
    apply/imsetP.
    exists (enc sc x).
    - apply mem_imset; by rewrite inE.
    - by move/eqP in Hx.
  apply Rle_trans with (INR #| dec sc @: (enc sc @: [set: 'rV[A]_k.+1]) |).
    apply/le_INR/leP.
    by case/subset_leqif_cards : Hsubset.
  apply Rle_trans with (INR #| dec sc @: [set: 'rV[bool]_n] |).
    apply/le_INR/leP/subset_leqif_cards/imsetS.
    apply/subsetP => x Hx.
    by rewrite inE.
  apply Rle_trans with (INR #| [set: 'rV[bool]_n] |).
    apply/le_INR/leP/leq_imset_card.
    rewrite cardsT card_matrix /= card_bool exp2_pow2 mul1n; by apply Rle_refl.
apply exp2_le_increasing.
rewrite /e0 [X in _ <= _ * X](_ : _ = r); last by field.
apply Rmult_le_reg_r with (1 / r) => //.
apply Rlt_mult_inv_pos; [fourier | tauto].
rewrite -mulRA {2}/Rdiv mul1R Rinv_r; last first.
  case: Hr => ? ? ?; fourier.
rewrite mulR1 /Rdiv mul1R; exact: proj2 (Rmax_Rle_in Hk).
Qed.

Local Open Scope proba_scope.

Lemma step1 : (1 - esrc(P , sc)) = \rsum_(x in no_failure) P `^ k.+1 x.
Proof.
rewrite /SrcErrRate /no_failure /Pr.
set a := \rsum_(_ | _) _.
set b := \rsum_(_ | _) _.
suff : 1 = a + b by move=> ->; field.
rewrite /a {a}.
have -> : b = \rsum_(i in [set i | dec sc (enc sc i) == i]) TupleDist.f P i.
  apply eq_big => // i /=; by rewrite inE.
rewrite -(pmf1 (P `^ k.+1)).
rewrite (bigID [pred a | a \in [set i0 | dec sc (enc sc i0) == i0]]) /= addRC.
f_equal.
apply eq_bigl => t /=; by rewrite !inE.
Qed.

Local Open Scope typ_seq_scope.

Lemma step2 : 1 - (esrc(P , sc)) =
  \rsum_(x in 'rV[A]_k.+1 | x \in no_failure :&: ~: `TS P k.+1 delta) P `^ k.+1 x +
  \rsum_(x in 'rV[A]_k.+1 | x \in no_failure :&: `TS P k.+1 delta) P `^ k.+1 x.
Proof.
rewrite step1 (bigID [pred x | x \in `TS P k.+1 delta]) /= addRC.
f_equal.
- apply eq_bigl => x; by rewrite in_setI in_setC.
- apply eq_bigl => x; by rewrite in_setI.
Qed.

Lemma step3 : 1 - (esrc(P , sc)) <=
  \rsum_(x in 'rV[A]_k.+1 | x \in ~: `TS P k.+1 delta) P `^ k.+1 x +
  \rsum_(x in 'rV[A]_k.+1 | x \in no_failure :&: `TS P k.+1 delta) P `^ k.+1 x.
Proof.
rewrite step2.
apply Rplus_le_compat_r, Rle_big_P_Q_f_X => [a | i].
- by apply (Rle0f (P `^ k.+1) a).
- rewrite in_setI; by case/andP.
Qed.

Lemma step4 : 1 - (esrc(P , sc)) <= delta +
  INR #| no_failure :&: `TS P k.+1 delta| * exp2 (- INR k.+1 * (`H P - delta)).
Proof.
eapply Rle_trans; first by apply step3.
apply Rplus_le_compat.
- move: (Pr_TS_1 Hdelta (proj1 (Rmax_Rle_in (proj1 (Rmax_Rle_in Hk))))) => H2.
  set p1 := Pr _ _ in H2.
  rewrite -/(Pr (P `^ k.+1) _) Pr_to_cplt /= (_ : Pr _ _ = p1); last first.
    rewrite /p1; apply Pr_ext; apply/setP => i /=; by rewrite !inE negbK.
  fourier.
- apply Rle_trans with
  (\rsum_(x in 'rV[A]_k.+1 | x \in no_failure :&: `TS P k.+1 delta)
    exp2 (-INR k.+1 * (`H P - delta))).
    apply Rle_big_P_f_g => i.
    rewrite in_setI.
    case/andP => _ /andP [] i_B i_TS.
    move: (typ_seq_definition_equiv2 i_TS) => [H1 _].
    apply log_le_inv.
    + rewrite /`TS inE /typ_seq in i_TS.
      case/andP : i_TS.
      move/RleP => i_TS _.
      eapply Rlt_le_trans; by [apply exp2_pos | apply i_TS].
    + by apply exp2_pos.
    + rewrite log_exp2.
      apply Rmult_le_reg_l with (1 / INR k.+1) => //.
      * rewrite /Rdiv.
        apply Rlt_mult_inv_pos => //; first by fourier.
        by apply/lt_0_INR/ltP.
      * apply Rge_le.
        rewrite -mulRA mul1R mulRA Ropp_mult_distr_r_reverse -Rinv_l_sym;
          last by apply not_0_INR.
        apply Rle_ge, Ropp_le_cancel.
        rewrite -Ropp_mult_distr_l_reverse (_ : - -1 = 1); last by field.
        by rewrite mul1R -Ropp_mult_distr_l_reverse.
  rewrite big_const iter_Rplus; by apply Rle_refl.
Qed.

Lemma step5 : 1 - (esrc(P , sc)) <= delta + exp2 (- INR k.+1 * (e0 - delta)).
Proof.
apply Rle_trans with (delta + INR #| no_failure | * exp2 (- INR k.+1 * (`H P - delta))).
- eapply Rle_trans; first by apply step4.
  apply Rplus_le_compat_l, Rmult_le_compat_r.
  by apply Rlt_le, exp2_pos.
  by apply/le_INR/leP/subset_leqif_cards/subsetIl.
- apply Rplus_le_compat_l.
  apply Rle_trans with (exp2 (INR k.+1 * (`H P - e0)) * exp2 (- INR k.+1 * (`H P - delta)));
    last first.
    rewrite -exp2_plus.
    apply exp2_le_increasing, Req_le; by field.
  apply Rmult_le_compat_r; [by apply Rlt_le, exp2_pos | exact no_failure_sup].
Qed.

Lemma step6 : (esrc(P , sc)) >= 1 - 2 * delta.
Proof.
have H : exp2 (- INR k.+1 * (e0 - delta)) <= delta.
  apply log_le_inv.
  - by apply exp2_pos.
  - exact Hdelta.
  - rewrite log_exp2.
    apply Rmult_le_reg_r with (1 / (e0 - delta)) => //.
    + apply Rlt_mult_inv_pos; first by fourier.
      rewrite /e0 /delta /r.
      apply Rlt_Rminus.
      have H1 : (`H P - r) / 2 < `H P - r.
        rewrite -[X in _ < X]mulR1.
        apply Rmult_lt_compat_l.
        case: Hr => ? ?; fourier.
        fourier.
      apply Rmin_case_strong => H2 //.
      eapply Rle_lt_trans; [by apply H2 | exact H1].
    + rewrite -mulRA /Rdiv mul1R Rinv_r; last first.
        apply Rminus_eq_contra; exact e0_delta.
      apply Ropp_le_cancel, Rge_le.
      rewrite -Ropp_mult_distr_l_reverse Ropp_involutive.
      apply Rle_ge.
      rewrite mulR1 /e0.
      by move: (proj2 (Rmax_Rle_in (proj1 (Rmax_Rle_in Hk)))).
suff : 1 - (esrc(P , sc)) <= delta + delta by move=> *; fourier.
eapply Rle_trans; by [apply step5 | apply Rplus_le_compat_l].
Qed.

Theorem source_coding_converse' : esrc(P , sc) >= epsilon.
Proof.
eapply Rge_trans; first by apply step6.
apply Rle_ge, Ropp_le_cancel.
rewrite Ropp_minus_distr.
apply Rplus_le_reg_l with 1.
rewrite addRC (_ : 2 * delta - _ + _ = 2 * delta); last by field.
rewrite (_ : 1 + - epsilon = 1 - epsilon); last by field.
apply Rmult_le_reg_l with (/ 2); first by fourier.
rewrite mulRA Rinv_l; last by move=> ?; fourier.
rewrite mul1R /delta.
have H1 : lambda / 2 <= / 2 * (1 - epsilon).
  apply Rle_trans with lambda.
  apply Rdiv_le; [apply Rlt_le; exact Hlambda | fourier].
  - rewrite /lambda mulRC; by apply Rmin_l.
apply Rmin_case_strong => ? //.
by apply Rle_trans with (lambda / 2).
Qed.

End source_coding_converse'.

Section source_coding_converse.

Variable A : finType.
Variable P : dist A.

(** * Source coding theorem (converse part) #<a name="label_source_coding_converse"> </a># *)

Theorem source_coding_converse : forall epsilon, 0 < epsilon < 1 ->
  forall r : Qplus, 0 < r < `H P ->
    forall n k (sc : scode_fl A k.+1 n),
      SrcRate sc = r ->
      SrcConverseBound P (num r) (den r) n epsilon <= INR k.+1 ->
      esrc(P , sc) >= epsilon.
Proof.
move=> epsilon Hespilon r r_HP n k sc r_sc Hk_bound.
by apply source_coding_converse' with (num := num r) (den := den r).
Qed.

End source_coding_converse.

Check source_coding_converse.
