(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div choice fintype.
From mathcomp Require Import finfun bigop prime binomial ssralg finset fingroup finalg matrix.
Require Import Reals Fourier.
Require Import Reals_ext Rssr log2 Rbigop proba entropy aep.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** * Typical Sequences *)

Local Open Scope Rb_scope.
Local Open Scope entropy_scope.
Local Open Scope proba_scope.

Section typical_sequence_definition.

Variable A : finType.
Variable P : dist A.
Variable n : nat.
Variable epsilon : R.

(** Definition a typical sequence: *)

Definition typ_seq (t : 'rV[A]_n) :=
  exp2 (- INR n * (`H P + epsilon)) <b= P `^ n t <b= exp2 (- INR n * (`H P - epsilon)).

Definition set_typ_seq := [set ta | typ_seq ta].

End typical_sequence_definition.

Notation "'`TS'" := (set_typ_seq) : typ_seq_scope.

Local Open Scope typ_seq_scope.

Lemma set_typ_seq_incl A (P : dist A) n epsilon : 0 <= epsilon -> forall r, 1 <= r ->
  `TS P n (epsilon / 3) \subset `TS P n epsilon.
Proof.
move=> He r Hr.
apply/subsetP => x.
rewrite /typ_seq !inE /typ_seq.
case/andP. move/RleP => H2. move/RleP => H3.
apply/andP; split; apply/RleP.
- eapply Rle_trans; last by apply H2.
  apply exp2_le_increasing.
  rewrite !Ropp_mult_distr_l_reverse.
  apply Ropp_le_contravar, Rmult_le_compat_l; first by apply pos_INR.
  apply Rplus_le_compat_l, Rdiv_le => //; fourier.
- eapply Rle_trans; first by apply H3.
  apply exp2_le_increasing.
  rewrite !Ropp_mult_distr_l_reverse.
  apply Ropp_le_contravar, Rmult_le_compat_l; first by apply pos_INR.
  apply Rplus_le_compat_l, Ropp_le_contravar, Rdiv_le => //; fourier.
Qed.

Section typ_seq_prop.

Variable A : finType.
Variable P : dist A.
Variable epsilon : R.
Variable n : nat.

(** The total number of typical sequences is upper-bounded by 2^(k*(H P + e)): *)

Lemma TS_sup : INR #| `TS P n epsilon | <= exp2 (INR n * (`H P + epsilon)).
Proof.
suff Htmp : 1 >= INR #| `TS P n epsilon | * exp2 (- INR n * (`H P + epsilon)).
  apply Rmult_le_reg_l with (exp2 (- INR n * (`H P + epsilon))).
  by apply exp2_pos.
  rewrite -exp2_plus {2}Ropp_mult_distr_l_reverse Rplus_opp_l {2}/exp2 mul0R exp_0 mulRC.
  by apply Rge_le.
rewrite -(pmf1 (P `^ n)).
rewrite (_ : _ * _ = \rsum_(x in `TS P n epsilon) (exp2 (- INR n * (`H P + epsilon)))); last first.
  by rewrite big_const iter_Rplus.
apply Rle_ge.
apply: Rle_big_P_true_f_g.
- move=> a; by apply Rle0f.
- move=> i.
  rewrite inE.
  case/andP.
  by move/RleP.
Qed.

Lemma typ_seq_definition_equiv x : x \in `TS P n epsilon ->
  exp2 (- INR n * (`H P + epsilon)) <= P `^ n x <= exp2 (- INR n * (`H P - epsilon)).
Proof.
rewrite inE /typ_seq.
case/andP => H1 H2; split; by apply/RleP.
Qed.

Lemma typ_seq_definition_equiv2 x : x \in `TS P n.+1 epsilon ->
  `H P - epsilon <= - (1 / INR n.+1) * log (P `^ n.+1 x) <= `H P + epsilon.
Proof.
rewrite inE /typ_seq.
case/andP => H1 H2.
split.
- apply Rmult_le_reg_l with (INR n.+1); first by apply lt_0_INR; apply/ltP.
  rewrite Ropp_mult_distr_l_reverse Ropp_mult_distr_r_reverse.
  rewrite /Rdiv mul1R mulRA Rinv_r_simpl_r; last by apply not_0_INR.
  rewrite -(Ropp_involutive (INR n.+1 * (`H P - epsilon))).
  apply Ropp_le_contravar, exp2_le_inv.
  rewrite exp2_log; last first.
    move/RleP in H1.
    by eapply Rlt_le_trans; by [apply exp2_pos | apply H1].
  apply/RleP.
  by rewrite -Ropp_mult_distr_l_reverse.
- apply Rmult_le_reg_l with (INR n.+1); first by apply lt_0_INR; apply/ltP.
  rewrite Ropp_mult_distr_l_reverse Ropp_mult_distr_r_reverse.
  rewrite /Rdiv mul1R mulRA Rinv_r_simpl_r; last by apply not_0_INR.
  rewrite -(Ropp_involutive (INR n.+1 * (`H P + epsilon))).
  apply Ropp_le_contravar, exp2_le_inv.
  rewrite exp2_log; last first.
    move/RleP in H1.
    by eapply Rlt_le_trans; by [apply exp2_pos | apply H1].
  apply/RleP.
  by rewrite -Ropp_mult_distr_l_reverse.
Qed.

End typ_seq_prop.

Section typ_seq_more_prop.

Variable A : finType.
Variable P : dist A.
Variable epsilon : R.
Variable n : nat.

Hypothesis He : 0 < epsilon.

Lemma Pr_TS_1 : aep_bound P epsilon <= INR n.+1 -> Pr (P `^ n.+1) (`TS P n.+1 epsilon) >= 1 - epsilon.
Proof.
move=> k0_k.
have -> : Pr P `^ n.+1 (`TS P n.+1 epsilon) =
  Pr P `^ n.+1 [set i | (i \in `TS P n.+1 epsilon) &&
  (0 <b P `^ n.+1 i) ].
  apply Pr_ext.
  apply/setP => t.
  rewrite !inE.
  move LHS : (typ_seq _ _ _) => [|] //=.
  rewrite /typ_seq in LHS.
  case/andP : LHS => LHS _.
  symmetry.
  apply/RltP.
  move/RleP in LHS.
  eapply Rlt_le_trans; last by apply LHS.
  by apply exp2_pos.
set p := [set _ | _].
move: (Pr_cplt (P `^ n.+1) p) => Htmp.
rewrite Pr_to_cplt.
suff ? : Pr (P `^ n.+1) (~: p) <= epsilon.
  by apply Rplus_ge_compat_l, Ropp_ge_contravar, Rle_ge.
have -> : Pr P `^ n.+1 (~: p) =
  Pr P `^ n.+1 [set x | P `^ n.+1 x == 0]
  +
  Pr P `^ n.+1 [set x | (0 <b P `^ n.+1 x) && (Rabs (- (1 / INR n.+1) * log (P `^ n.+1 x) - `H P) >b epsilon) ].
  have H1 : ~: p =
    [set x | P `^ n.+1 x == 0 ] :|:
    [set x | (0 <b P `^ n.+1 x) &&
               (Rabs (- (1 / INR n.+1) * log (P `^ n.+1 x) - `H P) >b epsilon)].
    apply/setP => i.
    rewrite !inE.
    rewrite negb_and.
    rewrite orbC.
    move LHS : (_ || _) => [|].
    + case/orP : LHS => LHS.
      * symmetry.
        apply/orP; left.
        rewrite -RleNgt in LHS.
        move/RleP in LHS.
        apply/eqP/Rle_antisym => //; by apply Rle0f.
      * rewrite /typ_seq negb_and in LHS.
        case/orP : LHS => LHS.
        - rewrite RleNgt negbK in LHS.
          case/boolP : (P `^ n.+1 i == 0) => H1; first by done.
          apply/esym/orP; right.
          apply/andP; split.
            rewrite RltNge.
            apply: contra H1 => H1.
            apply/eqP/Rle_antisym; by [apply/RleP | apply Rle0f].
          move/RltP in LHS.
          apply log_increasing in LHS; last first.
            apply/RltP.
            rewrite RltNge.
            apply: contra H1 => /RleP H1.
            apply/eqP/Rle_antisym => //; by apply Rle0f.
          rewrite log_exp2 in LHS.
          apply (Rmult_lt_compat_l (1 / INR n.+1)) in LHS; last first.
            apply Rlt_mult_inv_pos => //.
            fourier.
            by apply/lt_0_INR/ltP.
          rewrite mulRA Ropp_mult_distr_r_reverse {2}/Rdiv -mulRA -Rinv_l_sym in LHS; last first.
            by apply not_0_INR.
          rewrite mulR1 in LHS.
          apply Ropp_gt_lt_contravar in LHS.
          rewrite -Ropp_mult_distr_l_reverse Ropp_involutive mul1R in LHS.
          have H2 : forall a b c, a + b < c -> b < c - a by move=> *; fourier.
          apply H2 in LHS.
          move/RltP in LHS.
          rewrite Ropp_mult_distr_l_reverse.
          suff : Rabs (- (1 / INR n.+1 * log (P `^ n.+1 i)) - `H P) =
            - (1 / INR n.+1 * log (P `^ n.+1 i)) - `H P.
            by move=> ->.
          apply Rabs_pos_eq.
          move/RltP in LHS.
          by move/Rlt_le: (Rlt_trans _ _ _ He LHS).
        - rewrite RleNgt negbK in LHS.
          apply/esym/orP; right.
          apply/andP; split.
            apply/RltP.
            move/RltP in LHS.
            apply: Rlt_trans _ LHS; by apply exp2_pos.
          move/RltP in LHS.
          apply log_increasing in LHS; last by apply exp2_pos.
          rewrite log_exp2 in LHS.
          apply (Rmult_lt_compat_l (1 / INR n.+1)) in LHS; last first.
            apply Rlt_mult_inv_pos => //.
            fourier.
            by apply/lt_0_INR/ltP.
          rewrite mulRA Ropp_mult_distr_r_reverse {1}/Rdiv -mulRA -Rinv_l_sym in LHS; last first.
            by apply not_0_INR.
          rewrite mulR1 Rmult_minus_distr_l !Ropp_mult_distr_l_reverse !mul1R in LHS.
          have H2 : forall a b c, - a  - - b < c -> - c - a < - b by move=> *; fourier.
          apply H2 in LHS.
          have -> : Rabs (- (1 / INR n.+1) * log (P `^ n.+1 i) - `H P) =
            - (- (1 / INR n.+1) * log (P `^ n.+1 i) - `H P).
            rewrite Rabs_left1 //.
            eapply Rle_trans.
              apply Rlt_le.
              rewrite !Ropp_mult_distr_l_reverse.
              by apply LHS.
            fourier.
          apply/RltP/Ropp_lt_cancel.
          by rewrite Ropp_involutive // !Ropp_mult_distr_l_reverse.
      * move/negbT : LHS.
        rewrite negb_or 2!negbK.
        case/andP => H1 H2.
        rewrite /typ_seq in H2.
        apply/esym/negbTE.
        rewrite negb_or.
        apply/andP; split.
          rewrite RltNge in H1.
          apply: contra H1 => /eqP ->.
          by rewrite leRR.
        rewrite negb_and.
        apply/orP; right.
        rewrite /Rgt_bool RltNge negbK.
        case/andP : H2 => /RleP LHS LHS'.
        apply log_increasing_le in LHS; last by apply exp2_pos.
        rewrite log_exp2 in LHS.
        apply (Rmult_le_compat_l (1 / INR n.+1)) in LHS; last first.
          apply Rle_mult_inv_pos => //.
          fourier.
          apply lt_0_INR; by apply/ltP.
        rewrite mulRA Ropp_mult_distr_r_reverse {1}/Rdiv -mulRA -Rinv_l_sym in LHS; last first.
            by apply not_0_INR.
        rewrite mulR1 mulRDr !Ropp_mult_distr_l_reverse !mul1R in LHS.
        have H2 : forall a b c, - a + - b <= c -> - c - a <= b.
          move=> *; fourier.
        apply H2 in LHS.
        move/RleP in LHS'.
        apply log_increasing_le in LHS'; last by apply/RltP.
        rewrite log_exp2 in LHS'.
        apply (Rmult_le_compat_l (1 / INR n.+1)) in LHS'; last first.
          apply Rle_mult_inv_pos => //.
          fourier.
          by apply/lt_0_INR/ltP.
        rewrite mulRA Ropp_mult_distr_r_reverse {2}/Rdiv -mulRA -Rinv_l_sym in LHS'; last first.
            by apply not_0_INR.
        rewrite mulR1 mulRDr !Ropp_mult_distr_l_reverse !mul1R Ropp_involutive in LHS'.
        have H3 : forall a b c, a <= - c + b -> - b <= - a - c by move=> *; fourier.
        apply H3 in LHS'.
        move: (Rabs_le (- (1 / INR n.+1) * log (P `^ n.+1 i) - `H P) epsilon).
        rewrite /Rle_bool => ->.
        apply/andP; split;
          apply/RleP; by rewrite !Ropp_mult_distr_l_reverse.
  rewrite H1 Pr_union_disj; last first.
    apply disjoint_setI0.
    rewrite disjoints_subset.
    apply/subsetP => i.
    rewrite !inE /= => Hi.
    rewrite negb_and.
    apply/orP; left.
    move/eqP : Hi => ->.
    by rewrite ltRR.
    congr (_ + _); apply Pr_ext => i /=; by rewrite !inE.
have -> : Pr P `^ n.+1 [set x | P `^ n.+1 x == 0] = 0.
  rewrite /Pr.
  transitivity (\rsum_(a in 'rV[A]_n.+1 | P `^ n.+1 a == 0) 0).
    apply eq_big => // i.
    by rewrite !inE.
    rewrite inE.
    by move/eqP.
  by rewrite big_const /= iter_Rplus mulR0.
rewrite add0R.
move: (@aep _ P n _ He k0_k) => H1.
apply: Rle_trans _ H1.
apply/Pr_incl/subsetP => t.
rewrite inE /= -/(INR n.+1).
case/andP => H2 H3.
rewrite inE.
apply/andP; split => //.
apply/RleP.
move/RltP in H3.
apply RltW.
by rewrite Ropp_mult_distr_r_reverse -Ropp_mult_distr_l_reverse.
Qed.

Variable He1 : epsilon < 1.

(** In particular, for k big enough, the set of typical sequences is not empty: *)

Lemma set_typ_seq_not0 : aep_bound P epsilon <= INR n.+1 ->
  #| `TS P n.+1 epsilon | <> O.
Proof.
move/Pr_TS_1 => H.
case/boolP : (#| `TS P n.+1 epsilon |== O) => Heq; last by apply/eqP.
suff : False by done.
rewrite cards_eq0 in Heq.
move/eqP in Heq.
rewrite Heq (_ : Pr _ _ = 0) in H; last by rewrite /Pr big_set0.
fourier.
Qed.

(** the typical sequence of index 0 *)

Definition TS_0 (H : aep_bound P epsilon <= INR n.+1) : [finType of 'rV[A]_n.+1].
apply (@enum_val _ (pred_of_set (`TS P n.+1 epsilon))).
have -> : #| `TS P n.+1 epsilon| = #| `TS P n.+1 epsilon|.-1.+1.
  rewrite prednK //.
  move/set_typ_seq_not0 in H.
  rewrite lt0n; by apply/eqP.
exact ord0.
Defined.

Lemma TS_0_is_typ_seq (k_k0 : aep_bound P epsilon <= INR n.+1) :
  TS_0 k_k0 \in `TS P n.+1 epsilon.
Proof. rewrite /TS_0. apply/enum_valP. Qed.

(** The total number of typical sequences is lower-bounded by (1 - e)*2^(k*(H P - e))
    for k big enough: *)

Lemma TS_inf : aep_bound P epsilon <= INR n.+1 ->
  (1 - epsilon) * exp2 (INR n.+1 * (`H P - epsilon)) <= INR #| `TS P n.+1 epsilon |.
Proof.
move=> k0_k.
have H1 : 1 - epsilon <= Pr (P `^ n.+1) (`TS P n.+1 epsilon) <= 1.
  split; by [apply Rge_le, Pr_TS_1 | apply Pr_1].
have H2 :(forall x, x \in `TS P n.+1 epsilon ->
  exp2 (- INR n.+1 * (`H P + epsilon)) <= P `^ n.+1 x <= exp2 (- INR n.+1 * (`H P - epsilon))).
  move=> x; rewrite inE; by apply Rle2P.
move: (@wolfowitz _ P _ (`TS _ _ _) _ _ _ _ (exp2_pos _) (exp2_pos _) H1 H2).
rewrite Ropp_mult_distr_l_reverse exp2_Ropp {1}/Rdiv Rinv_involutive; last first.
  by apply nesym, Rlt_not_eq, exp2_pos.
by case.
Qed.

End typ_seq_more_prop.
