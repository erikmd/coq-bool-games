(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice fintype.
From mathcomp Require Import tuple finfun bigop prime binomial ssralg finset fingroup finalg matrix.
Require Import Reals Fourier Rpower.
Require Import Reals_ext Ranalysis_ext Rssr log2 ln_facts Rbigop proba entropy.
Require Import channel_code channel divergence conditional_divergence variation_dist.
Require Import pinsker.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope divergence_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Local Open Scope channel_scope.
Local Open Scope reals_ext_scope.

Section mutinfo_distance_bound.

Variable A B : finType.
Variables V W : `Ch_1(A, B).
Variable P : dist A.
Hypothesis V_dom_by_W : V << W | P.
Hypothesis cdiv_ub : D(V || W | P) <= (exp(-2)) ^ 2 * / 2.

Let cdiv_bounds : 0 <= sqrt (2 * D(V || W | P)) <= exp (-2).
Proof.
split; first by apply sqrt_pos.
apply pow2_Rle_inv; [ by apply sqrt_pos | by apply Rlt_le, exp_pos | ].
rewrite [in X in X <= _]/= mulR1 sqrt_sqrt; last first.
  apply Rmult_le_pos; by [fourier | apply leq0cdiv].
apply (Rmult_le_reg_r (/ 2)); first by by apply Rinv_0_lt_compat, Rlt_R0_R2.
rewrite mulRC mulRA Rinv_l; first by rewrite mul1R.
by apply not_eq_sym, Rlt_not_eq, Rlt_R0_R2.
Qed.

Local Open Scope variation_distance_scope.

(** Distance from the output entropy of one channel to another: *)

Lemma out_entropy_dist_ub : Rabs (`H(P `o V) - `H(P `o W)) <=
  / ln 2 * INR #|B| * - xlnx (sqrt (2 * D(V || W | P))).
Proof.
rewrite 2!xlnx_entropy /Rminus.
rewrite -Ropp_mult_distr_r_reverse -mulRDr Rabs_mult Rabs_right; last first.
  rewrite -(mul1R (/ ln 2)); apply Rle_ge, Rle_mult_inv_pos;
  by [apply Rle_0_1 | apply ln_2_pos].
rewrite -mulRA; apply Rmult_le_compat_l.
  rewrite -(mul1R (/ ln 2)); apply Rle_mult_inv_pos;
  by [apply Rle_0_1 | apply ln_2_pos].
rewrite Ropp_involutive (big_morph _ morph_Ropp Ropp_0) -big_split /=.
eapply Rle_trans; first by apply big_Rabs.
rewrite -iter_Rplus_Rmult -big_const.
apply: Rle_big_P_f_g => b _; rewrite addRC.
apply Rabs_xlnx => //.
- split; by [apply (Rle0f (`O(P , W))) | apply (dist_max (`O(P, W)))].
- split; by [apply (Rle0f (`O(P , V))) | apply (dist_max (`O(P, V)))].
- rewrite /Rminus (big_morph _ morph_Ropp Ropp_0) -big_split /=.
  eapply Rle_trans; first by apply big_Rabs.
  apply (Rle_trans _ (d(`J(P , V), `J(P , W)))).
  + rewrite /var_dist /=.
    apply (Rle_trans _ (\rsum_(a : A) \rsum_(b : B) Rabs (V a b * P a - W a b * P a))); last first.
      apply Req_le; rewrite pair_bigA; by apply eq_bigr.
    apply: Rle_big_P_f_g => a _.
    rewrite (bigD1 b) //= Rabs_minus_sym /Rminus -[X in X <= _]addR0.
    apply Rplus_le_compat_l; apply: Rle_big_0_P_g => b1 _; by apply Rabs_pos.
  + rewrite cdiv_is_div_joint_dist => //.
    by apply Pinsker_inequality_weak, joint_dom.
Qed.

(** Distance from the joint entropy of one channel to another: *)

Lemma joint_entropy_dist_ub : Rabs (`H(P , V) - `H(P , W)) <=
  / ln 2 * INR #|A| * INR #|B| * - xlnx (sqrt (2 * D(V || W | P))).
Proof.
rewrite 2!xlnx_entropy.
rewrite /Rminus -Ropp_mult_distr_r_reverse -mulRDr Rabs_mult Rabs_right; last first.
  rewrite -(mul1R (/ ln 2)); apply Rle_ge, Rle_mult_inv_pos;
  by [apply Rle_0_1 | apply ln_2_pos].
rewrite -2!mulRA; apply Rmult_le_compat_l.
  rewrite -(mul1R (/ ln 2)); apply Rle_mult_inv_pos;
  by [apply Rle_0_1 | apply ln_2_pos].
rewrite Ropp_involutive (big_morph _ morph_Ropp Ropp_0) -big_split /=.
eapply Rle_trans; first apply big_Rabs.
rewrite -2!iter_Rplus_Rmult -2!big_const pair_bigA /=.
apply: Rle_big_P_f_g; case => a b _; rewrite addRC /=.
apply Rabs_xlnx => //.
- split; [exact (Rle0f (`J(P, W)) (a, b)) | by apply (dist_max (`J(P, W)) (a, b))].
- split; [exact (Rle0f (`J(P, V)) (a, b)) | by apply (dist_max (`J(P, V)) (a, b))].
- apply (Rle_trans _ (d(`J(P , V) , `J(P , W)))).
    rewrite /var_dist /R_dist (bigD1 (a, b)) //= Rabs_minus_sym /Rminus.
    rewrite -[X in X <= _]addR0.
    apply Rplus_le_compat_l; apply: Rle_big_0_P_g => b1 _; by apply Rabs_pos.
  rewrite cdiv_is_div_joint_dist => //.
  by apply Pinsker_inequality_weak, joint_dom.
Qed.

(** * Distance from the mutual information of one channel to another *)

Lemma mut_info_dist_ub : Rabs (`I(P ; V) - `I(P ; W)) <=
  / ln 2 * (INR #|B| + INR #|A| * INR #|B|) * - xlnx (sqrt (2 * D(V || W | P))).
Proof.
rewrite /mut_info.
rewrite (_ : _ - _ = `H(P `o V) - `H(P `o W) + (`H(P , W) - `H(P , V))); last by field.
eapply Rle_trans; first by apply Rabs_triang.
rewrite -mulRA mulRDl mulRDr.
apply Rplus_le_compat.
- by rewrite mulRA; apply out_entropy_dist_ub.
- by rewrite Rabs_minus_sym 2!mulRA; apply joint_entropy_dist_ub.
Qed.

End mutinfo_distance_bound.

Local Open Scope Rb_scope.

Section error_exponent_lower_bound.

Variables A B : finType.
Hypothesis Bnot0 : (0 < #|B|)%nat.
Variable W : `Ch_1(A, B).
Variable cap : R.
Hypothesis W_cap : capacity W cap.
Variable minRate : R.
Hypothesis minRate_cap : minRate > cap.

(** * Error exponent bound *)

Lemma error_exponent_bound : exists Delta, 0 < Delta /\
  forall P : dist A, forall V : `Ch_1(A, B),
    V << W | P ->
    Delta <= D(V || W | P) +  +| minRate - `I(P ; V) |.
Proof.
set gamma := / (INR #|B| + INR #|A| * INR #|B|) * (ln 2 * ((minRate - cap) / 2)).
move: (continue_xlnx 0).
rewrite /continuity_pt /continue_in /limit1_in /limit_in.
move=> /(_ (min(exp (-2), gamma))).
have Htmp : min(exp (-2), gamma) > 0.
  apply Rmin_Rgt_r ; split ; apply Rlt_gt.
  - by apply exp_pos.
  - subst gamma ; apply Rmult_lt_0_compat.
      apply Rinv_0_lt_compat, Rplus_lt_le_0_compat.
      - apply lt_0_INR; by apply/ltP.
      - apply Rmult_le_pos; by apply pos_INR.
    apply Rmult_lt_0_compat; first by apply ln_2_pos.
    apply Rmult_lt_0_compat; last by apply Rinv_0_lt_compat, Rlt_R0_R2.
    rewrite -(Rplus_opp_r cap) /Rminus.
    by apply Rplus_lt_compat_r.
move=> /(_ Htmp) {Htmp} [] /= mu [mu_pos mu_cond].
set x := min(mu / 2, exp (-2)).
move: {mu_cond}(mu_cond x).
have x_pos : 0 < x.
  subst x.
  apply Rmin_pos; last by apply exp_pos.
  apply Rmult_lt_0_compat => //.
  by apply Rinv_0_lt_compat, Rlt_R0_R2.
have Htmp : D_x no_cond 0 x /\ R_dist x 0 < mu.
  split.
  - split => //; by apply Rlt_not_eq.
  - rewrite /R_dist /Rminus Ropp_0 addR0 Rabs_right; last by apply Rle_ge, Rlt_le.
    subst x.
    apply (Rle_lt_trans _ (mu * / 2)); first by apply Rmin_l.
    apply (Rmult_lt_reg_r 2); first by apply Rlt_R0_R2.
    rewrite -mulRA Rinv_l; last by apply not_eq_sym, Rlt_not_eq, Rlt_R0_R2.
    apply Rmult_lt_compat_l => //; fourier.
move=> /(_ Htmp) {Htmp}.
rewrite /R_dist /Rminus {2}/xlnx.
rewrite (_ : 0 <b 0 = false); last by apply/RltP; apply Rlt_irrefl.
rewrite Ropp_0 addR0 Rabs_left; last first.
  apply xlnx_neg.
  split => //; subst x.
  apply (Rle_lt_trans _ (exp (-2))); first by apply Rmin_r.
  by apply exp_opp_2_lt_1.
move=> Hx.
set Delta := min((minRate - cap) / 2, x ^ 2 / 2).
exists Delta; split.
  apply Rmin_case.
    apply Rmult_lt_0_compat; last by apply Rinv_0_lt_compat, Rlt_R0_R2.
    apply (Rplus_lt_reg_r cap).
    by rewrite addRC -addRA Rplus_opp_l 2!addR0.
  apply Rmult_lt_0_compat; last by apply Rinv_0_lt_compat, Rlt_R0_R2.
  by apply pow_gt0.
move=> P V v_dom_by_w.
case/boolP : (Delta <b= D(V || W | P)).
  move/RleP => Hcase.
  apply (Rle_trans _ (D(V || W | P))) => //.
  rewrite -{1}(addR0 (D(V || W | P))).
  by apply Rplus_le_compat_l, Rmax_l.
move/RleP/(Rnot_le_lt _) => Hcase.
suff Htmp : (minRate - cap) / 2 <= minRate - (`I(P; V)).
  clear -Hcase v_dom_by_w Htmp.
  apply (Rle_trans _ +| minRate - `I(P ; V) |); last first.
    rewrite -[X in X <= _]add0R.
    apply Rplus_le_compat_r, leq0cdiv => b Hb ? ?; by apply v_dom_by_w.
  eapply Rle_trans; last by apply Rmax_r.
  eapply Rle_trans; first by apply Rmin_l.
  done.
have Htmp : `I(P ; V) <= cap + / ln 2 * (INR #|B| + INR #|A| * INR #|B|) *
                               (- xlnx (sqrt (2 * D(V || W | P)))).
  apply (Rle_trans _ (`I(P ; W) + / ln 2 * (INR #|B| + INR #|A| * INR #|B|) *
                                  - xlnx (sqrt (2 * D(V || W | P))))); last first.
    apply Rplus_le_compat_r.
    move: W_cap; rewrite /capacity /lub; case; by move/(_ P).
  apply (Rplus_le_reg_l (- `I(P ; W))).
  rewrite addRA Rplus_opp_l add0R addRC.
  apply (Rle_trans _ (Rabs (`I(P ; V) + - `I(P ; W)))); first apply Rle_abs.
  have Htmp : D(V || W | P) <= exp (-2) ^ 2 * / 2.
    clear -Hcase x_pos.
    apply Rlt_le, (Rlt_le_trans _ _ _ Hcase).
    apply (Rle_trans _ (x ^ 2 * / 2)); first by apply Rmin_r.
    apply Rmult_le_compat_r; first by apply Rlt_le, Rinv_0_lt_compat, Rlt_R0_R2.
    apply pow_incr.
    split; by [apply Rlt_le | apply Rmin_r].
  by apply mut_info_dist_ub.
apply Ropp_le_contravar, (Rplus_le_compat_l minRate) in Htmp.
eapply Rle_trans; last by apply Htmp.
clear Htmp.
suff Htmp : - xlnx (sqrt (2 * (D(V || W | P)))) <= gamma.
  rewrite Ropp_plus_distr addRA.
  apply (Rplus_le_reg_l (- (minRate + - cap ))).
  rewrite [X in X <= _](_ : _ = - ((minRate + - cap) / 2)); last by field.
  apply Rge_le.
  rewrite addRA Rplus_opp_l add0R.
  apply Ropp_le_ge_contravar; rewrite -mulRA.
  apply (Rmult_le_reg_l (ln 2)); first by apply ln_2_pos.
  rewrite mulRA Rinv_r; last by apply not_eq_sym, Rlt_not_eq, ln_2_pos.
  rewrite mul1R.
  apply (Rmult_le_reg_l (/ (INR #|B| + INR #|A| * INR #|B|))).
    apply Rinv_0_lt_compat, Rplus_lt_le_0_compat.
    - apply lt_0_INR; by apply/ltP.
    - apply Rmult_le_pos; by apply pos_INR.
  rewrite -/gamma mulRA Rinv_l; last first.
    apply not_eq_sym, Rlt_not_eq, Rplus_lt_le_0_compat.
    - apply lt_0_INR; by apply/ltP.
    - apply Rmult_le_pos; by apply pos_INR.
  by rewrite mul1R.
suff Htmp : xlnx x <= xlnx (sqrt (2 * (D(V || W | P)))).
  clear -Hx Htmp.
  apply Ropp_le_cancel; rewrite Ropp_involutive.
  apply (Rle_trans _ (xlnx x)) => //.
  apply Ropp_le_cancel; rewrite Ropp_involutive.
  apply Rlt_le; apply (Rlt_le_trans _ _ _ Hx).
  subst gamma; by apply Rmin_r.
apply Rlt_le, Rgt_lt.
have Htmp : sqrt (2 * D(V || W | P)) < x.
  apply pow2_Rlt_inv; [by apply sqrt_pos | by apply Rlt_le | ].
  rewrite [in X in X < _]/= mulR1 sqrt_sqrt; last first.
    apply Rmult_le_pos; first by apply Rlt_le, Rlt_R0_R2.
    apply leq0cdiv=> a Ha ? ?; by apply v_dom_by_w.
  apply (Rmult_lt_reg_r (/ 2)); first by apply Rinv_0_lt_compat, Rlt_R0_R2.
  rewrite mulRC mulRA Rinv_l; last by apply not_eq_sym, Rlt_not_eq, Rlt_R0_R2.
  rewrite mul1R; apply (Rlt_le_trans _ _ _ Hcase); by apply Rmin_r.
apply xlnx_sdecreasing_0_Rinv_e => //.
- split; first by apply sqrt_pos.
  apply (Rle_trans _ x); first by apply Rlt_le.
  subst x.
  apply (Rle_trans _ (exp (-2))); first by apply Rmin_r.
  apply Rlt_le, exp_increasing, Ropp_lt_contravar; fourier.
- split; first by apply Rlt_le.
  apply (Rle_trans _ (exp (-2))); first by apply Rmin_r.
  apply Rlt_le, exp_increasing, Ropp_lt_contravar; fourier.
Qed.

End error_exponent_lower_bound.
