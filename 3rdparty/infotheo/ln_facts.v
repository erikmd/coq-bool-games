(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div fintype.
From mathcomp Require Import tuple finfun bigop.
Require Import Reals Fourier.
Require Import Reals_ext Ranalysis_ext Rssr log2.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope Rb_scope.

Section ln_id_sect.

Definition ln_id x := ln x - (x - 1).

Lemma pderivable_ln_id_xle1 : pderivable ln_id (fun x => 0 < x <= 1).
Proof.
rewrite /pderivable => x Hx.
rewrite /ln_id.
apply derivable_pt_plus.
- apply derivable_pt_ln, Hx.
- apply derivable_pt_opp, derivable_pt_minus ; [apply derivable_pt_id | apply derivable_pt_cst].
Defined.

Definition ln_id' x (H : 0 < x <= 1) := derive_pt ln_id x (pderivable_ln_id_xle1 H).

Lemma derive_pt_ln_id_xle1 : forall x (Hx : 0 < x <= 1), (/ x) - 1 = ln_id' Hx.
Proof.
move=> y Hy.
rewrite /ln_id' /pderivable_ln_id_xle1 /ln_id.
rewrite derive_pt_plus derive_pt_opp derive_pt_ln derive_pt_minus derive_pt_id derive_pt_cst.
rewrite Rminus_0_r /Rminus.
reflexivity.
Defined.

Lemma derive_pt_ln_id_xle1_ge0 x (Hx : 0 < x <= 1) : 0 < if x==1 then 1 else ln_id' Hx.
Proof.
case/orP : (orbN (x == 1)) => Hcase ; first by rewrite Hcase; fourier.
move/negbTE in Hcase ; rewrite Hcase.
rewrite -derive_pt_ln_id_xle1.
apply Rgt_lt, Rgt_minus, Rlt_gt.
rewrite -Rinv_1 ; apply Rinv_lt_contravar; first by [rewrite mulR1; apply Hx].
case (Rle_lt_or_eq_dec x 1) ; [apply Hx | done | ].
move/eqP in Hcase ; move => Habs.
rewrite Habs in Hcase ; by contradict Hcase.
Defined.

Lemma ln_idlt0_xlt1 : forall x, 0 < x < 1 -> ln_id x < 0.
Proof.
rewrite {2}(_ : 0 = ln_id 1); last by rewrite /ln_id ln_1 /Rminus Rplus_opp_r Ropp_0 addR0.
move=> x Hx.
have lt01 : 0 < 1 by fourier.
apply (derive_increasing_ad_hoc lt01 derive_pt_ln_id_xle1_ge0).
- by split; [apply Hx | apply Rlt_le, Hx].
- split; by fourier.
- by apply Hx.
Qed.

Lemma ln_idlt0_xgt1 x : 0 < x -> 1 < x -> ln_id x < 0.
Proof.
move=> Hx Hx2.
rewrite /ln_id; apply Rlt_minus, exp_lt_inv.
rewrite exp_ln; last exact Hx.
rewrite -{1}(addR0 x) -(Rplus_opp_l 1) addRA addRC.
apply exp_ineq1, Rgt_minus, Rgt_lt, Hx2.
Qed.

Lemma ln_idgt0 x : 0 < x -> ln_id x <= 0.
Proof.
move=> Hx.
case (total_order_T x 1).
- case => Hx2.
  + by apply Rlt_le, ln_idlt0_xlt1.
  + subst x; rewrite /ln_id ln_1 /Rminus 2!Rplus_opp_r; by apply Rle_refl.
- move=> Hx2; apply Rlt_le, ln_idlt0_xgt1; by [apply Hx | apply Rgt_lt, Hx2].
Qed.

Lemma ln_id_cmp x : 0 < x -> ln x <= x - 1.
Proof. move=> Hx ; apply Rminus_le ; apply ln_idgt0 ; exact Hx. Qed.

Lemma log_id_cmp x : 0 < x -> log x <= (x - 1) * log (exp 1).
Proof.
move=> Hx ; rewrite /log ln_exp /Rdiv mul1R.
apply Rmult_le_compat_r; by
  [apply Rlt_le, Rinv_0_lt_compat, ln_2_pos | apply ln_id_cmp].
Qed.

Lemma ln_id_eq x : 0 < x -> ln x = x - 1 -> x = 1.
Proof.
move=> Hx' Hx.
case (total_order_T x 1) => [ [] // Hx2 | Hx2]; contradict Hx.
- apply Rlt_not_eq, (Rplus_lt_reg_r (- (x - 1))); rewrite (addRC (x - 1)) Rplus_opp_l.
  apply ln_idlt0_xlt1; split; [exact Hx' | exact Hx2].
- apply Rlt_not_eq, (Rplus_lt_reg_r (- (x - 1))); rewrite (addRC (x - 1)) Rplus_opp_l.
  by apply ln_idlt0_xgt1.
Qed.

Lemma log_id_eq x : 0 < x -> log x = (x - 1) * log (exp 1) -> x = 1.
Proof.
move=> Hx' Hx ; rewrite /log ln_exp /Rdiv mul1R in Hx.
apply Rmult_eq_reg_r in Hx; last by apply not_eq_sym, Rlt_not_eq, Rinv_0_lt_compat, ln_2_pos.
apply ln_id_eq; by [apply Hx' | apply Hx].
Qed.

End ln_id_sect.

Section xlnx_sect.

Section xlnx.

Definition xlnx := fun x => if 0 <b x then x * ln x else 0.

Lemma xlnx_0 : xlnx 0 = 0.
Proof. rewrite /xlnx mul0R; by case : ifP. Qed.

Lemma xlnx_1 : xlnx 1 = 0.
Proof. rewrite /xlnx ln_1 mulR0 ; by case : ifP. Qed.

Lemma xlnx_neg x : 0 < x < 1 -> xlnx x < 0.
Proof.
case => lt0x ltx1.
rewrite /xlnx.
have -> : 0 <b x ; first by apply/RltP.
apply Ropp_lt_cancel.
rewrite Ropp_0 -Ropp_mult_distr_r_reverse.
apply Rmult_lt_0_compat => //.
apply Ropp_lt_cancel; rewrite Ropp_involutive Ropp_0.
apply exp_lt_inv.
by rewrite exp_ln // exp_0.
Qed.

Lemma continue_xlnx : continuity xlnx.
Proof.
rewrite /continuity => r.
rewrite /continuity_pt /continue_in /limit1_in /limit_in => eps eps_pos /=.
case (total_order_T 0 r) ; first case ; move=> Hcase.
- have : continuity_pt (fun x => x * ln x) r.
    apply continuity_pt_mult.
      by apply derivable_continuous_pt, derivable_id.
    by apply derivable_continuous_pt, derivable_pt_ln.
  rewrite /continuity_pt /continue_in /limit1_in /limit_in => /(_ eps eps_pos); case => /= k [k_pos Hk].
  exists (Rmin k r); split; first by apply Rlt_gt, Rmin_pos.
  - move=> x ; rewrite /D_x ; move => [[_ Hx1] Hx2].
    rewrite /xlnx.
    have -> : 0 <b x.
      apply/RltP.
      rewrite -(addR0 x) -{2}(Rplus_opp_l r) addRA.
      apply (Rle_lt_trans _ ((x + - r) + Rabs (x + - r))).
        rewrite -(Rplus_opp_r (x + -r)); apply Rplus_le_compat_l.
        rewrite -Rabs_Ropp; by apply Rle_abs.
      apply Rplus_lt_compat_l.
      rewrite /R_dist /Rminus in Hx2.
      apply (Rlt_le_trans _ (Rmin k r)) => //; by apply Rmin_r.
    have -> : 0 <b r by apply/RltP.
    apply Hk.
    split => //.
    by apply (@Rlt_le_trans _ _ _ Hx2), Rmin_l.
- subst r.
  exists (exp (- 2 * / eps)).
  split ; first by apply exp_pos.
  move=> x; rewrite /R_dist /Rminus Ropp_0 addR0; case=> Hx1 Hx2.
  rewrite /xlnx.
  have -> : Rlt_bool 0 0 = false by apply/RltP/Rlt_irrefl.
  case (Rlt_le_dec 0 x) => Hcase.
  + rewrite Rabs_pos_eq in Hx2 ; last by apply Rlt_le.
    have -> : 0 <b x by apply/RltP.
    rewrite /Rminus Ropp_0 addR0 -{1}(exp_ln _ Hcase).
    set X := ln x.
    have X_neg : X < 0.
      apply (Rlt_trans _ (-2 * / eps)).
      by apply exp_lt_inv ; subst X ; rewrite exp_ln.
      rewrite Ropp_mult_distr_l_reverse.
      apply Ropp_0_lt_gt_contravar, Rlt_mult_inv_pos => // ; by apply Rlt_R0_R2.
    apply: (Rlt_le_trans _ (2 * / (- X)) _).
    * rewrite Rabs_left ; last first.
        rewrite -(mulR0 (exp X)).
        apply Rmult_lt_compat_l => // ; by apply exp_pos.
       rewrite -Ropp_mult_distr_r_reverse.
      apply (Rmult_lt_reg_r (/ - X)); first by apply Rinv_0_lt_compat, Ropp_0_gt_lt_contravar.
      rewrite -mulRA Rinv_r; last by apply not_eq_sym, Rlt_not_eq, Ropp_0_gt_lt_contravar.
      rewrite mulR1 -(Rinv_involutive 2); last by apply not_eq_sym, Rlt_not_eq, Rlt_R0_R2.
      rewrite -mulRA ( _ : forall r, r * r = r ^ 2); last by move=> ?; rewrite /pow mulR1.
      rewrite pow_inv; last by apply not_eq_sym, Rlt_not_eq, Ropp_0_gt_lt_contravar.
      rewrite -Rinv_mult_distr; last 2 first.
        by apply Rinv_neq_0_compat, not_eq_sym, Rlt_not_eq, Rlt_R0_R2.
        by apply pow_nonzero, Ropp_neq_0_compat, Rlt_not_eq.
      rewrite -(Rinv_involutive (exp X)); last by apply not_eq_sym, Rlt_not_eq, exp_pos.
      apply Rinv_lt_contravar.
        rewrite -mulRA mulRC; apply Rlt_mult_inv_pos; last fourier.
        apply Rlt_mult_inv_pos; last by apply exp_pos.
        apply pow_gt0; by fourier.
        rewrite -exp_Ropp mulRC (_ : 2 = INR 2`!) //.
        by apply exp_strict_lb, Ropp_0_gt_lt_contravar.
    * apply (Rmult_le_reg_r (/ 2)); first by apply Rinv_0_lt_compat, Rlt_R0_R2.
      rewrite mulRC mulRA Rinv_l; last by apply not_eq_sym, Rlt_not_eq, Rlt_R0_R2.
      rewrite mul1R -(Rinv_involutive eps); last by apply not_eq_sym, Rlt_not_eq.
      rewrite -Rinv_mult_distr ; last 2 first.
        by apply not_eq_sym, Rlt_not_eq, Rinv_0_lt_compat.
        by apply not_eq_sym, Rlt_not_eq, Rlt_R0_R2.
      apply Rle_Rinv.
      - apply Rmult_lt_0_compat; by [apply Rinv_0_lt_compat | apply Rlt_R0_R2].
      - by apply Ropp_0_gt_lt_contravar.
      - rewrite -(Ropp_involutive (/ eps * 2)); apply Ropp_le_contravar.
        rewrite mulRC -Ropp_mult_distr_l_reverse.
        apply exp_le_inv, Rlt_le; subst X; by rewrite exp_ln.
  + have -> : 0 <b x = false by apply/RltP; apply RIneq.Rle_not_lt.
    by rewrite /Rminus Ropp_0 addR0 Rabs_R0.
- exists (- r); split; first by apply Ropp_0_gt_lt_contravar.
  move=> x [[_ Hx1] Hx2].
  rewrite /R_dist /xlnx.
  have -> : 0 <b x = false.
    apply/RltP ; apply Rge_not_lt, Rle_ge.
    rewrite -(addR0 x) -{1}(Rplus_opp_l r) addRA.
    apply (Rle_trans _ ((x + - r) - Rabs (x + - r))).
      apply Rplus_le_compat_l, Rlt_le.
      rewrite -{1}(Ropp_involutive r).
      by apply Ropp_lt_contravar.
    rewrite -(Rplus_opp_r (x + -r)); apply Rplus_le_compat_l.
    by apply Ropp_le_contravar, Rle_abs.
  have -> : Rlt_bool 0 r = false.
    by apply/RltP; apply Rge_not_lt, Rle_ge, Rlt_le.
  rewrite /Rminus Ropp_0 addR0 Rabs_R0; by apply Rgt_lt.
Qed.

(* NB: not used *)
Lemma uniformly_continue_xlnx : uniform_continuity xlnx (fun x => 0 <= x <= 1).
Proof.
apply Heine ; first by apply compact_P3.
move=> x _ ; by apply continue_xlnx.
Qed.

Let xlnx_total := fun y => y * ln y.

Lemma derivable_xlnx_total x : 0 < x -> derivable_pt xlnx_total x.
Proof.
move=> x_pos.
apply derivable_pt_mult.
  by apply derivable_id.
by apply derivable_pt_ln.
Defined.

Lemma xlnx_total_xlnx x : 0 < x -> xlnx x = xlnx_total x.
Proof. by rewrite /xlnx /f => /RltP ->. Qed.

Lemma derivable_pt_xlnx x (x_pos : 0 < x) : derivable_pt xlnx x.
Proof. apply (@derivable_f_eq_g _ _ x 0 xlnx_total_xlnx x_pos (derivable_xlnx_total x_pos)). Defined.

Lemma derive_xlnx_aux1 x (x_pos : 0 < x) :
  derive_pt xlnx x (derivable_pt_xlnx x_pos) =
  derive_pt xlnx_total x (derivable_xlnx_total x_pos).
Proof. by rewrite -derive_pt_f_eq_g. Qed.

Lemma derive_xlnx_aux2 x (x_pos : 0 < x) : derive_pt xlnx x (derivable_pt_xlnx x_pos) = ln x + 1.
Proof.
rewrite derive_xlnx_aux1 /f derive_pt_mult derive_pt_ln.
rewrite Rinv_r; last by apply not_eq_sym, Rlt_not_eq.
rewrite (_ : derive_pt ssrfun.id x (derivable_id x) = 1) ; first by rewrite mul1R.
rewrite -(derive_pt_id x).
by apply proof_derive_irrelevance.
Qed.

Lemma derive_pt_xlnx x (x_pos : 0 < x) (pr : derivable_pt xlnx x) : derive_pt xlnx x pr = ln x + 1.
Proof. rewrite -derive_xlnx_aux2 ; by apply proof_derive_irrelevance. Qed.

Lemma pderivable_Ropp_xlnx : pderivable (fun y => - xlnx y) (fun x => 0 < x <= exp (- 1)).
Proof.
move=> x /= Hx.
apply derivable_pt_opp.
apply derivable_pt_xlnx.
apply Hx.
Defined.

Lemma xlnx_sdecreasing_0_Rinv_e_helper : forall (t : R) (Ht : 0 < t <= exp (-1)),
  0 < (if t == exp (-1) then 1 else derive_pt (fun x => - xlnx x) t (pderivable_Ropp_xlnx Ht)).
Proof.
move=> t [Ht1 Ht2].
case : ifP => [|/negbT] Hcase ; first apply Rlt_0_1.
rewrite derive_pt_opp derive_pt_xlnx //.
apply Ropp_lt_cancel ; rewrite Ropp_involutive Ropp_0.
apply (Rplus_lt_reg_r (- 1)).
rewrite -addRA Rplus_opp_r addR0 add0R.
apply exp_lt_inv.
rewrite exp_ln //.
apply Rlt_le_neq => //.
move/eqP; by apply/negP.
Qed.

Lemma xlnx_sdecreasing_0_Rinv_e x y :
  0 <= x <= exp (-1) -> 0 <= y <= exp (-1) -> x < y -> xlnx x > xlnx y.
Proof.
move=> [Hx1 Hx2] [Hy1 Hy2] xlty.
case/orP : (orbN ( x == 0)).
- move/eqP => -> ; rewrite xlnx_0 ; apply xlnx_neg.
  split ; first by apply (Rle_lt_trans _ x).
  apply (Rle_lt_trans _ (exp (-1)))=> //.
  apply exp_opp_1_lt_1.
move => xnot0.
apply Ropp_lt_cancel.
have x_pos : 0 < x.
  apply Rlt_le_neq => // /eqP.
  rewrite eq_sym ; by apply/negP.
have y_pos : 0 < y by apply (Rlt_trans _ x).
move=> {Hx1 Hy1}.
have aux : 0 < exp(-1) by apply exp_pos.
by apply (derive_increasing_ad_hoc aux xlnx_sdecreasing_0_Rinv_e_helper).
Qed.

Lemma xlnx_decreasing_0_Rinv_e x y :
  0 <= x <= exp (-1) -> 0 <= y <= exp (-1) -> x <= y -> xlnx y <= xlnx x.
Proof.
move=> Hx Hy Hxy.
case/orP : (orbN (x == y)).
- move=> /eqP -> ; by apply Rle_refl.
- move=> H.
  apply Rlt_le, xlnx_sdecreasing_0_Rinv_e => //.
  apply Rlt_le_neq => //.
  move=> /eqP ; by apply/negP.
Qed.

End xlnx.

Section diff_xlnx.

Definition diff_xlnx := fun x => xlnx (1 - x) - xlnx x.

Lemma derivable_pt_diff_xlnx x (Hx : 0 < x < 1) : derivable_pt diff_xlnx x.
Proof.
rewrite /diff_xlnx /Rminus.
apply derivable_pt_plus ; last by apply derivable_pt_opp, derivable_pt_xlnx, Hx.
apply (derivable_pt_comp (fun x => 1 + - x) xlnx).
  apply derivable_pt_plus ; first by apply derivable_pt_const.
  apply derivable_pt_Ropp.
apply derivable_pt_xlnx.
apply (Rplus_lt_reg_r x); rewrite addRC -addRA Rplus_opp_l 2!addR0; by apply Hx.
Defined.

Lemma derive_pt_diff_xlnx x (Hx : 0 < x < 1) :
  derive_pt diff_xlnx x (derivable_pt_diff_xlnx Hx) = -(2 + ln (x * (1-x))).
Proof.
rewrite derive_pt_plus derive_pt_opp derive_pt_xlnx; last by apply Hx.
rewrite derive_pt_comp derive_pt_plus derive_pt_const.
rewrite derive_pt_xlnx /=; last first.
  apply (Rplus_lt_reg_r x); rewrite addRC -addRA Rplus_opp_l 2!addR0; by apply Hx.
rewrite add0R ln_mult; first field.
- by apply Hx.
- apply (Rplus_lt_reg_r x); rewrite addRC -addRA Rplus_opp_l 2!addR0; by apply Hx.
Qed.

Lemma diff_xlnx_0 : diff_xlnx 0 = 0.
Proof. by rewrite /diff_xlnx Rminus_0_r xlnx_0 xlnx_1 Rminus_0_r. Qed.

Lemma diff_xlnx_1 : diff_xlnx 1 = 0.
Proof. by rewrite /diff_xlnx /Rminus Rplus_opp_r xlnx_0 xlnx_1 Rplus_opp_r. Qed.

Lemma derive_diff_xlnx_neg_aux x (Hx : 0 < x < 1) : x < exp (-2) -> 0 < derive_pt diff_xlnx x (derivable_pt_diff_xlnx Hx).
Proof.
rewrite derive_pt_diff_xlnx; case: Hx => Hx1 Hx2 xltexp2.
apply Ropp_lt_cancel; rewrite Ropp_0 Ropp_involutive.
apply (Rplus_lt_reg_r (-2)); rewrite addRC addRA Rplus_opp_l 2!add0R.
apply exp_lt_inv.
rewrite exp_ln ; last first.
  apply Rmult_lt_0_compat => //.
  apply (Rplus_lt_reg_r x); by rewrite addRC -addRA Rplus_opp_l 2!addR0.
apply (Rlt_trans _ ( (exp (-2)) * (1 - x))).
  apply Rmult_lt_compat_r => //.
  apply (Rplus_lt_reg_r x); by rewrite addRC -addRA Rplus_opp_l 2!addR0.
rewrite -{2}(mulR1 (exp (-2))).
apply Rmult_lt_compat_l; first by apply exp_pos.
apply (Rplus_lt_reg_r (-1)).
rewrite /Rminus addRC addRA Rplus_opp_l add0R Rplus_opp_r.
apply Ropp_lt_cancel; by rewrite Ropp_involutive Ropp_0.
Qed.

Lemma derive_diff_xlnx_pos x (Hx : 0 < x < 1) (pr : derivable_pt diff_xlnx x) : x < exp (-2) -> 0 < derive_pt diff_xlnx x pr.
Proof.
rewrite (proof_derive_irrelevance _ (derivable_pt_diff_xlnx Hx)).
apply derive_diff_xlnx_neg_aux.
Qed.

Lemma MVT_cor1_pderivable_new f a b : forall (prd : pderivable f (fun x => a < x < b)) (prc : forall x (Hx : a <= x <= b), continuity_pt f x),
  a < b ->
  exists c (Hc : a < c < b),
    f b - f a = derive_pt f c (prd c Hc) * (b - a) /\ a < c < b.
Proof.
intros prd prc ab.
have H0 : forall c : R, a < c < b -> derivable_pt f c.
  move=> c Hc.
  apply prd.
  case: Hc => ? ?; split; fourier.
have H1 : forall c : R, a < c < b -> derivable_pt id c.
  move=> c _; by apply derivable_pt_id.
have H2 : forall c, a <= c <= b -> continuity_pt f c.
  move=> x Hc.
  by apply prc.
have H3 : forall c, a <= c <= b -> continuity_pt id c.
  move=> x Hc; by apply derivable_continuous_pt, derivable_pt_id.
case: (MVT f id a b H0 H1 ab H2 H3) => c [Hc H'].
exists c.
exists Hc.
split => //.
cut (derive_pt id c (H1 c Hc) = derive_pt id c (derivable_pt_id c));
    [ intro | apply pr_nu ].
rewrite H (derive_pt_id c) mulR1 in H'.
rewrite -H' /= /id mulRC.
f_equal.
by apply pr_nu.
Qed.

Lemma MVT_cor1_pderivable_new_var f a b : forall (prd : pderivable f (fun x => a < x < b)) (prca : continuity_pt f a) (prcb : continuity_pt f b),
  a < b ->
  exists c (Hc : a < c < b),
    f b - f a = derive_pt f c (prd c Hc) * (b - a) /\ a < c < b.
Proof.
intros prd prca prcb ab.
have prc : forall x (Hx : a <= x <= b), continuity_pt f x.
  move=> x Hx.
  case/orP : (orbN (x == a)) ; first by move/eqP => ->.
  move=> xnota.
  case/orP : (orbN (x == b)) ; first by move/eqP => ->.
  move=> xnotb.
  apply derivable_continuous_pt, prd.
  split.
  - apply Rlt_le_neq ; by [apply Hx | move=> /eqP ; apply/negP ; rewrite eq_sym].
  - apply Rlt_le_neq ; by [apply Hx | move=> /eqP ; apply/negP].
have H0 : forall c : R, a < c < b -> derivable_pt f c.
  move=> c Hc.
  apply prd.
  case: Hc => ? ?; split; fourier.
have H1 : forall c : R, a < c < b -> derivable_pt id c.
  move=> c _; by apply derivable_pt_id.
have H2 : forall c, a <= c <= b -> continuity_pt f c.
  move=> x Hc.
  by apply prc.
have H3 : forall c, a <= c <= b -> continuity_pt id c.
  move=> x Hc; by apply derivable_continuous_pt, derivable_pt_id.
case: (MVT f id a b H0 H1 ab H2 H3) => c [Hc H'].
exists c.
exists Hc.
split => //.
cut (derive_pt id c (H1 c Hc) = derive_pt id c (derivable_pt_id c));
    [ intro | apply pr_nu ].
rewrite H (derive_pt_id c) mulR1 in H'.
rewrite -H' /= /id mulRC.
f_equal.
by apply pr_nu.
Qed.

Lemma derive_sincreasing_interv a b (f:R -> R) (pr: pderivable f (fun x => a < x < b)) (prc : forall x (Hx : a <= x <= b), continuity_pt f x) :
    a < b ->
    ((forall t:R, forall (prt : derivable_pt f t), a < t < b -> 0 < derive_pt f t prt) ->
      forall x y:R, a <= x <= b -> a <= y <= b -> x < y -> f x < f y).
Proof.
intros H H0 x y H1 H2 H3.
- apply Rplus_lt_reg_r with (- f x).
  rewrite Rplus_opp_r.
  have prd' : pderivable f (fun z => x < z < y).
    move=> z /= [Hz1 Hz2] ; apply pr.
    split.
    - apply (Rle_lt_trans _ x) => // ; by apply H1.
    - apply (Rlt_le_trans _ y) => // ; by apply H2.
  have H0' : forall t (Ht : x < t < y), 0 < derive_pt f t (prd' t Ht).
    move=> z /= [Hz0 Hz1].
    apply H0.
    split.
    - apply (Rle_lt_trans _ x) => // ; by apply H1.
    - apply (Rlt_le_trans _ y) => // ; by apply H2.
  have prcx : continuity_pt f x.
    apply prc ; split ; by apply H1.
  have prcy : continuity_pt f y.
    apply prc ; split ; by apply H2.
  have aux : a < b.
    apply (Rle_lt_trans _ x) ; first by apply H1.
    apply (Rlt_le_trans _ y) => // ; by apply H2.
  case: (MVT_cor1_pderivable_new_var prd' prcx prcy H3); intros x0 [x1 [H7 H8]].
  unfold Rminus in H7.
  rewrite H7.
  apply Rmult_lt_0_compat.
  by apply H0'.
apply (Rplus_lt_reg_r x).
by rewrite addRC -addRA Rplus_opp_l 2!addR0.
Qed.

Lemma diff_xlnx_sincreasing_0_Rinv_e2 : forall x y : R, 0 <= x <= exp (-2) -> 0 <= y <= exp (-2) -> x < y -> diff_xlnx x < diff_xlnx y.
Proof.
apply derive_sincreasing_interv.
- move=> x /= [Hx1 Hx2].
  apply derivable_pt_diff_xlnx.
  split => //.
  apply: (@Rlt_trans _ _ _ Hx2 _).
  by apply exp_opp_2_lt_1.
- move=> x /= Hx.
  rewrite /diff_xlnx.
  apply continuity_pt_minus ; last by apply continue_xlnx.
  apply (continuity_pt_comp (fun x => 1 - x) xlnx); last by apply continue_xlnx.
  rewrite /Rminus.
  apply continuity_pt_plus ; first by apply continuity_pt_const.
  apply continuity_pt_opp.
  apply derivable_continuous_pt.
  by apply derivable_pt_id.
- by apply exp_pos.
- move => t prt [Ht1 Ht2].
  apply derive_diff_xlnx_pos => //.
  split => // ; apply (Rlt_trans _ (exp (-2))) => //.
  by apply exp_opp_2_lt_1.
Qed.

Lemma xlnx_ineq x : 0 <= x <= exp (-2) -> xlnx x <= xlnx (1-x).
Proof.
move=> [Hx1 Hx2].
apply Rge_le, Rminus_ge, Rle_ge.
rewrite -diff_xlnx_0 -/(diff_xlnx x).
case/orP : (orbN (0 == x)) ; last move=> xnot0 ; first by [move=> /eqP <- ; apply Rle_refl].
apply Rlt_le, diff_xlnx_sincreasing_0_Rinv_e2.
- split ; by [apply Rle_refl | apply Rlt_le, exp_pos].
- by split.
apply Rlt_le_neq => // /eqP ; by apply/negP.
Qed.

End diff_xlnx.

Definition xlnx_delta a := fun x => xlnx (x + a) - xlnx x.

Lemma derivable_xlnx_delta eps (Heps : 0 < eps < 1) x (Hx : 0 < x < 1 - eps) :
  derivable_pt (xlnx_delta eps) x.
Proof.
rewrite /xlnx_delta.
apply derivable_pt_minus.
- apply (derivable_pt_comp (fun x => x + eps) xlnx).
    apply derivable_pt_plus ; first by apply derivable_pt_id.
    by apply derivable_pt_const.
  apply derivable_pt_xlnx.
  apply Rplus_le_lt_0_compat ; by [apply Heps | apply Rlt_le, Hx].
- by apply derivable_pt_xlnx, Hx.
Defined.

Lemma derive_pt_xlnx_delta eps (Heps : 0 < eps < 1) x (Hx : 0 < x < 1 - eps) :
  derive_pt (xlnx_delta eps) x (derivable_xlnx_delta Heps Hx) = ln (x + eps) - ln x.
Proof.
rewrite derive_pt_minus derive_pt_comp derive_pt_plus derive_pt_id derive_pt_const derive_pt_xlnx ; last first.
  apply Rplus_lt_0_compat ; by [apply Hx | apply Heps].
rewrite derive_pt_xlnx ; last by apply Hx.
field.
Qed.

Lemma increasing_xlnx_delta eps (Heps : 0< eps < 1) :
  forall x y : R, 0 <= x <= 1 - eps -> 0 <= y <= 1 - eps -> x < y ->
                  xlnx_delta eps x < xlnx_delta eps y.
Proof.
apply derive_sincreasing_interv.
- move=> x /= [Hx1 Hx2] ; rewrite /xlnx_delta.
  apply derivable_pt_minus.
  - apply (derivable_pt_comp (fun x => x + eps) xlnx).
      apply derivable_pt_plus ; first by apply derivable_pt_id.
      by apply derivable_pt_const.
    apply derivable_pt_xlnx.
    apply Rplus_lt_0_compat => // ; by apply Heps.
  - by apply derivable_pt_xlnx.
- move=> x /= [Hx1 Hx2] ; rewrite /xlnx_delta.
  apply continuity_pt_minus.
  - apply (continuity_pt_comp (fun x => x + eps) xlnx); last by apply continue_xlnx.
      apply continuity_pt_plus ; first by apply derivable_continuous_pt, derivable_pt_id.
      by apply continuity_pt_const.
  - by apply continue_xlnx.
- by apply Rgt_lt, Rgt_minus, Rlt_gt, Heps.
- move=> t prd Ht.
  rewrite (proof_derive_irrelevance _ (derivable_xlnx_delta Heps Ht)) derive_pt_xlnx_delta.
  apply Rgt_lt, Rgt_minus, Rlt_gt, ln_increasing ; first by apply Ht.
  rewrite -{1}(addR0 t).
  by apply Rplus_lt_compat_l, Heps.
Qed.

Lemma xlnx_delta_bound eps : 0 < eps <= exp (-2) ->
  forall x, 0 <= x <= 1 - eps -> Rabs (xlnx_delta eps x) <= - xlnx eps.
Proof.
move=> [Heps1 Heps2] x [Hx1 Hx2].
apply Rabs_Rle.
- apply (Rle_trans _ (xlnx_delta eps (1 - eps))).
    case/orP : (orbN (x == 1 - eps)) ; last move=> xnot0 ; first by [move=> /eqP -> ; apply Rle_refl].
    apply Rlt_le, increasing_xlnx_delta => //.
    - split => //.
      apply (Rle_lt_trans _ (exp (-2))) => //.
      by apply exp_opp_2_lt_1.
    - split ; by [apply (Rle_trans _ x) | apply Rle_refl].
    - apply Rlt_le_neq => // /eqP ; by apply/negP.
  rewrite /xlnx_delta /Rminus -addRA Rplus_opp_l addR0 xlnx_1 add0R.
  apply Ropp_le_cancel ; rewrite 2!Ropp_involutive.
  apply xlnx_ineq.
  split => // ; by apply Rlt_le.
rewrite Ropp_involutive.
rewrite (_ : xlnx eps = xlnx_delta eps 0) ; last first.
  rewrite /xlnx_delta.
  by rewrite add0R xlnx_0 Rminus_0_r.
case/orP : (orbN (0 == x)) ; last move=> xnot0 ; first by [move=> /eqP <- ; apply Rle_refl].
apply Rlt_le, increasing_xlnx_delta => //.
- split => //.
  apply (Rle_lt_trans _ (exp (-2))) => //.
  by apply exp_opp_2_lt_1.
- split ; by [apply (Rle_trans _ x) | apply Rle_refl].
- apply Rlt_le_neq => // /eqP ; by apply/negP.
Qed.

Lemma Rabs_xlnx a (Ha : 0 <= a <= exp(-2)) x y :
  0 <= x <= 1 -> 0 <= y <= 1 -> Rabs (x - y) <= a ->
  Rabs (xlnx x - xlnx y) <= - xlnx a.
Proof.
move=> [Hx1 Hx2] [Hy1 Hy2] H.
case : (Rtotal_order x y) ; last case ; move => Hcase.
- have Haux : y = x + Rabs (x - y).
    rewrite /R_dist -Rabs_Ropp Rabs_pos_eq.
      by rewrite Ropp_plus_distr Ropp_involutive addRA Rplus_opp_r add0R.
    apply Ropp_le_cancel; rewrite Ropp_0 Ropp_involutive.
    by apply Rle_minus, Rlt_le.
  rewrite Haux -Rabs_Ropp Ropp_plus_distr Ropp_involutive addRC.
  apply (Rle_trans _ (- xlnx (Rabs (x - y)))).
    apply xlnx_delta_bound.
    - split.
      - by apply Rabs_pos_lt, Rlt_not_eq, Rlt_minus.
      - apply (Rle_trans _ a) => //; by apply Ha.
    - split => //.
      apply (Rplus_le_reg_r (Rabs (x - y))); by rewrite /Rminus -addRA Rplus_opp_l addR0 -Haux.
  apply Ropp_le_cancel ; rewrite 2!Ropp_involutive.
  apply xlnx_decreasing_0_Rinv_e => //.
  - split; first by apply Rabs_pos.
    apply (Rle_trans _ a) => //.
    apply (Rle_trans _ (exp (- 2))); first by apply Ha.
    apply Rlt_le, exp_increasing, Ropp_lt_contravar; fourier.
  - split; first by apply Ha.
    apply (Rle_trans _ (exp (-2))); first by apply Ha.
    apply Rlt_le, exp_increasing, Ropp_lt_contravar; fourier.
- subst x ; rewrite /Rminus Rplus_opp_r Rabs_R0.
  apply Ropp_le_cancel ; rewrite Ropp_involutive Ropp_0.
  case/orP : (orbN (0 == a)); last move=> anot0.
    by [move=> /eqP <- ; rewrite xlnx_0 ; apply Rle_refl].
  apply Rlt_le, xlnx_neg.
  split.
  - apply Rlt_le_neq; first by apply Ha.
    move/eqP; by apply/negP.
  - apply (Rle_lt_trans _ (exp (-2))); first by apply Ha.
    by apply exp_opp_2_lt_1.
- apply Rgt_lt in Hcase.
  have Haux : x = y + Rabs (x - y).
    rewrite Rabs_pos_eq.
      by rewrite addRC /Rminus -addRA Rplus_opp_l addR0.
    by apply Rge_le, Rge_minus, Rle_ge, Rlt_le.
  rewrite Rabs_minus_sym in H Haux.
  rewrite Haux.
  apply (Rle_trans _ (- xlnx (Rabs (y - x)))).
    apply xlnx_delta_bound.
    - split.
      - by apply Rabs_pos_lt, Rlt_not_eq, Rlt_minus.
      - apply (Rle_trans _ a) => //; by apply Ha.
    - split => //.
      apply (Rplus_le_reg_r (Rabs (y - x))); by rewrite /Rminus -addRA Rplus_opp_l addR0 -Haux.
  apply Ropp_le_cancel ; rewrite 2!Ropp_involutive.
  apply xlnx_decreasing_0_Rinv_e => //.
  + split; first by apply Rabs_pos.
    apply (Rle_trans _ a) => //.
    apply (Rle_trans _ (exp (-2))); first by apply Ha.
    apply Rlt_le, exp_increasing, Ropp_lt_contravar; fourier.
  - split; first by apply Ha.
    apply (Rle_trans _ (exp (-2))); first by apply Ha.
    apply Rlt_le, exp_increasing, Ropp_lt_contravar; fourier.
Qed.

End xlnx_sect.
