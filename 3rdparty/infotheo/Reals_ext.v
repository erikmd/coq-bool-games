(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path div.
From mathcomp Require Import fintype tuple finfun bigop prime finset binomial.
Require Import ProofIrrelevance Reals Fourier.
Require Import Rssr.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Arguments INR : simpl never.

Record pos_fun (T : Type) := mkPosFun {
  pos_f :> T -> R ;
  Rle0f : forall a, 0 <= pos_f a }.

Notation "T '->' 'R+' " := (pos_fun T) (at level 10, format "'[' T  ->  R+ ']'") : reals_ext_scope.

Local Open Scope reals_ext_scope.

Lemma pos_fun_eq {C : Type} (f g : C -> R+) : pos_f f = pos_f g -> f = g.
Proof.
destruct f as [f Hf].
destruct g as [g Hg].
move=> /= ?; subst.
suff : Hf = Hg by move=> ->.
by apply proof_irrelevance.
Qed.

(** Various lemmas about reals *)

Lemma Rlt_ne a b : a < b -> b <> a.
Proof.
move => Hb He.
rewrite He in Hb.
by apply (Rlt_irrefl a).
Qed.

Lemma Rmult_minus_distr_r (r1 r2 r3 : R) : (r2 - r3) * r1 = r2 * r1 - r3 * r1.
Proof. field. Qed.

Lemma Rlt_0_Rmult_inv a b : 0 < a * b -> 0 <= a -> 0 <= b -> 0 < a /\ 0 < b.
Proof.
move=> H Ha Hb.
split.
  apply Rnot_le_lt => abs.
  have : a = 0.
    clear -Ha abs.
    by apply Rle_antisym.
  move=> abs'; rewrite abs' mul0R in H.
  by move/Rlt_irrefl : H.
apply Rnot_le_lt => abs.
have : b = 0.
  clear -Hb abs.
  by apply Rle_antisym.
move=> abs'; rewrite abs' mulR0 in H.
by move/Rlt_irrefl : H.
Qed.

Lemma iter_Rmult_pow x : forall n : nat, ssrnat.iter n (Rmult x) 1 = x ^ n.
Proof. elim => // n Hn ; by rewrite iterS Hn. Qed.

Lemma iter_Rplus_Rmult x : forall n : nat, ssrnat.iter n (Rplus x) 0 = INR n * x.
Proof.
elim; first by rewrite mul0R.
move=> n Hn; by rewrite iterS Hn -{1}(mul1R x) -mulRDl addRC -S_INR.
Qed.

Lemma exp_not_0 l : (exp l <> 0)%R.
Proof. apply not_eq_sym, Rlt_not_eq ; exact (exp_pos l). Qed.

Lemma two_e : 2 <= exp 1.
Proof. apply Rlt_le, exp_ineq1; fourier. Qed.

Lemma exp_opp_1_lt_1 : exp (-1) < 1.
Proof. rewrite -[X in _ < X]exp_0. apply exp_increasing. fourier. Qed.

Lemma exp_opp_2_lt_1 : exp (-2) < 1.
Proof. rewrite -[X in _ < X]exp_0. apply exp_increasing. fourier. Qed.

(* NB: try to use Rltn_neqAle instead? *)
Lemma Rlt_le_neq a b : a <= b -> a <> b -> a < b.
move=> H1 H2.
apply Rnot_le_lt => abs.
by move: (Rle_antisym _ _ H1 abs).
Qed.

Lemma Rle_inv_conv x y : 0 < x -> 0 < y -> / y <= / x -> x <= y.
Proof.
move=> x_pos y_pos H.
rewrite -(Rinv_involutive x); last by apply not_eq_sym, Rlt_not_eq.
rewrite -(Rinv_involutive y); last by apply not_eq_sym, Rlt_not_eq.
apply Rle_Rinv => //; by apply Rinv_0_lt_compat.
Qed.

(* NB: see Rplus_le_lt_reg_pos_r in the standard library *)
Lemma Rplus_le_lt_reg_pos_r r1 r2 r3 : 0 < r2 -> r1 + r2 <= r3 -> r1 < r3.
Proof. move=> *. fourier. Qed.

Lemma INR_Zabs_nat x : (0 <= x)%Z -> INR (Zabs_nat x) = IZR x.
Proof.
move=> Hx.
destruct x => //.
suff : False by done.
suff : ~ (0 <= Zneg p)%Z by contradiction.
by apply Zlt_not_le.
Qed.

Lemma Rmax_Rle_in r1 r2 r : Rmax r1 r2 <= r -> r1 <= r /\ r2 <= r.
Proof.
case: (Rlt_le_dec r1 r2).
- move/Rlt_le => H1.
  rewrite Rmax_right // => H2.
  split; [by apply Rle_trans with r2 | assumption].
- move=> H1.
  rewrite Rmax_left // => H2.
  split; [assumption | by apply Rle_trans with r1].
Qed.

Lemma RmaxA : associative Rmax.
Proof.
move=> a b c.
apply Rmax_case_strong.
- case/Rmax_Rle_in => H1 H2.
  rewrite Rmax_left; last first.
    apply Rmax_Rle; tauto.
  by rewrite Rmax_left.
- case/Rmax_Rle => H.
  by rewrite [in X in _ = Rmax X _]Rmax_right.
  apply Rmax_case_strong => H'.
  rewrite [in X in _ = Rmax X _]Rmax_right; last first.
    by apply Rle_trans with c.
  by rewrite Rmax_left.
  apply Rmax_case_strong => //.
  case/Rmax_Rle => H''.
  have ? : a = c by apply Rle_antisym. subst c.
  by rewrite Rmax_left.
  have ? : b = c by apply Rle_antisym. subst c.
  by rewrite Rmax_right.
Qed.

Definition RmaxC : commutative Rmax := Rmax_comm.

Notation "'min(' x ',' y ')'" := (Rmin x y) : reals_ext_scope.
Notation "'max(' x ',' y ')'" := (Rmax x y) : reals_ext_scope.

Notation "+| r |" := (Rmax 0 r) (at level 0, r at level 99, format "+| r |") : reals_ext_scope.

(** Notation for positive rationals: *)

Record Qplus := mkRrat { num : nat ; den : nat }.

Definition Q2R (q : Qplus) := INR (num q) / INR (den q).+1.

Coercion Q2R : Qplus >-> R.

(** Lemmas about division *)

Lemma neq_Rdiv a b : a <> 0 -> b <> 0 -> b <> 1 -> a <> a / b.
Proof.
move=> Ha Hb Hb' abs.
rewrite -{1}[X in X = _]mulR1 in abs.
apply Rmult_eq_reg_l in abs => //.
apply Hb'.
apply Rmult_eq_reg_r with (/ b); last first.
  by apply Rinv_neq_0_compat.
by rewrite Rinv_r // mul1R.
Qed.

Lemma Rdiv_le a : 0 <= a -> forall r, 1 <= r -> a / r <= a.
Proof.
move=> Ha r Hr.
apply Rmult_le_reg_l with r; first by fourier.
rewrite /Rdiv mulRA Rinv_r_simpl_m; last by move=> *; fourier.
rewrite -{1}(mul1R a).
apply Rmult_le_compat_r => //; fourier.
Qed.

Lemma Rdiv_lt a : 0 < a -> forall r : R, 1 < r -> a / r < a.
Proof.
move=> Ha r0 Hr0.
rewrite -[X in _ < X]mulR1.
apply Rmult_lt_compat_l => //.
rewrite -Rinv_1.
apply Rinv_1_lt_contravar => //.
by apply Rle_refl.
Qed.

(** Lemmas about power *)

Lemma le_sq x : 0 <= x ^ 2.
Proof.
move=> /=; case: (Rle_dec 0 x) => H; rewrite mulR1.
by apply Rmult_le_pos.
rewrite -(Ropp_involutive x) Rmult_opp_opp.
apply Rmult_le_pos; by apply Ropp_0_ge_le_contravar, Rgt_ge, Rnot_le_gt.
Qed.

Lemma pow0_inv : forall n x, x ^ n = 0 -> x = 0.
Proof.
elim => [x /= H | n IH x /= H].
fourier.
case/Rmult_integral : H => //; by move/IH.
Qed.

Lemma sq_incr a b : 0 <= a -> 0 <= b -> a <= b -> a^2 <= b^2.
Proof. move=> Ha Hb H. by apply pow_incr. Qed.

Lemma pow2_Rle_inv a b : 0 <= a -> 0 <= b -> a^2 <= b^2 -> a <= b.
Proof.
move=> Ha Hb H.
apply sqrt_le_1 in H; last 2 first.
  by apply le_sq.
  by apply le_sq.
by rewrite /= !mulR1 !sqrt_square in H.
Qed.

Lemma pow2_Rlt_inv a b : 0 <= a -> 0 <= b -> a^2 < b^2 -> a < b.
Proof.
move=> Ha Hb H.
apply sqrt_lt_1 in H; last 2 first.
  by apply le_sq.
  by apply le_sq.
by rewrite /= !mulR1 !sqrt_square in H.
Qed.

Lemma Rabs_sq x : Rabs x ^ 2 = x ^ 2.
Proof.
move=> /=.
rewrite !mulR1 -Rabs_mult Rabs_pos_eq // (_ : _ * _ = x ^2 ).
apply le_sq.
by rewrite /= mulR1.
Qed.

Lemma Rabs_Rle (x a : R) : x <= a -> - a <= x -> Rabs x <= a.
Proof.
move=> H1 H2.
rewrite /Rabs.
case : Rcase_abs => _ //.
apply Ropp_le_cancel; by rewrite Ropp_involutive.
Qed.

Lemma id_rem a b : (a - b) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2.
Proof. rewrite /= !mulR1 !mulRDr !Rmult_minus_distr_r /=; field. Qed.

Lemma id_rem_plus a b : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2.
Proof. rewrite /= !mulR1 !mulRDl !mul1R !mulRDr /=; field. Qed.

Lemma x_x2_eq q : q * (1 - q) = 1 / 4 - 1 / 4 * (2 * q - 1) ^ 2.
Proof. field. Qed.

Lemma x_x2_max q : q * (1 - q) <= 1 / 4.
Proof.
rewrite x_x2_eq.
have : forall a b, 0 <= b -> a - b <= a. move=>  *; fourier.
apply.
apply Rmult_le_pos.
fourier.
by apply le_sq.
Qed.

(** Lemmas about up / Int_part / frac_part *)

Lemma up_pos r : 0 <= r -> (0 < up r)%Z.
Proof.
move=> Hr.
apply lt_IZR => /=.
move/Rgt_lt : (proj1 (archimed r)) => Hr'.
by apply Rle_lt_trans with r.
Qed.

Lemma Rle_up_pos r : 0 <= r -> r <= IZR (Zabs (up r)).
Proof.
move=> Hr.
rewrite Zabs_eq; last first.
  apply up_pos in Hr.
  by apply Z.lt_le_incl.
case: (base_Int_part r).
rewrite /Int_part minus_IZR (_ : IZR 1 = 1) // => _ ?; fourier.
Qed.

Lemma Rle_up a : a <= IZR (Zabs (up a)).
Proof.
case: (Rlt_le_dec a 0) => Ha; last by apply Rle_up_pos.
apply Rle_trans with 0; first by fourier.
rewrite (_ : 0 = IZR 0) //; by apply IZR_le, Zabs_pos.
Qed.

Lemma up_Int_part r : (up r = Int_part r + 1)%Z.
Proof.
case: (base_Int_part r) => H1 H2.
rewrite -(up_tech r (Int_part r)) // plus_IZR (_ : IZR 1 = 1) //; fourier.
Qed.

Lemma Int_part_pos a : 0 <= a -> (0 <= Int_part a)%Z.
Proof.
move/up_pos => ?.
rewrite /Int_part.
rewrite (_ : 0 = Z.succ 0 - 1)%Z //.
apply Z.sub_le_mono => //.
by apply Zlt_le_succ.
Qed.

Lemma frac_part_INR m : frac_part (INR m) = 0.
Proof.
rewrite /frac_part /Int_part -(up_tech _ (Z_of_nat m)).
rewrite minus_IZR plus_IZR /= -INR_IZR_INZ; by field.
rewrite -INR_IZR_INZ; by apply Rle_refl.
rewrite {1}INR_IZR_INZ; apply IZR_lt.
by apply Z.lt_add_pos_r.
Qed.

Lemma frac_Int_part x : frac_part x = 0 -> IZR (Int_part x) = x.
Proof.
rewrite /frac_part.
set h := IZR _.
move=> H.
by rewrite -(addR0 h) -H Rplus_minus.
Qed.

Lemma frac_part_mult a b : frac_part a = 0 -> frac_part b = 0 ->
  frac_part (a * b) = 0.
Proof.
rewrite /frac_part /Int_part !minus_IZR (_ : IZR 1 = 1) //.
move=> Ha Hb.
have {Ha}Ha : IZR (up a) = a + 1.
  move: Ha.
  set x := IZR (up a).
  move=> Ha.
  rewrite -[X in X = _](add0R _) -Ha.
  by field.
have {Hb}Hb : IZR (up b) = b + 1.
  move: Hb.
  set x := IZR (up b).
  move=> Hb.
  rewrite -[X in X = _](add0R _) -Hb.
  by field.
rewrite -(tech_up _ ((up a - 1) * (up b - 1) + 1)).
  rewrite ?plus_IZR ?minus_IZR ?mult_IZR ?minus_IZR (_ : IZR 1 = 1) // Ha Hb.
  by field.
  rewrite ?plus_IZR ?minus_IZR ?mult_IZR ?minus_IZR (_ : IZR 1 = 1) // Ha Hb.
  rewrite (_ : forall a, a + 1 - 1 = a); last by move=> *; field.
  rewrite (_ : forall a, a + 1 - 1 = a); last by move=> *; field.
  fourier.
  rewrite ?plus_IZR ?minus_IZR ?mult_IZR ?minus_IZR (_ : IZR 1 = 1) // Ha Hb.
  rewrite (_ : forall a, a + 1 - 1 = a); last by move=> *; field.
  rewrite (_ : forall a, a + 1 - 1 = a); last by move=> *; field.
  by apply Rle_refl.
Qed.

Lemma frac_part_pow a : frac_part a = 0 -> forall n, frac_part (a ^ n) = 0.
Proof.
move=> Ha; elim=> /=.
by rewrite /frac_part (_ : 1 = INR 1) // Int_part_INR  Rminus_diag_eq.
move=> n IH; by apply frac_part_mult.
Qed.

Lemma Rabs_eq_0 r : Rabs r = 0 -> r = 0.
Proof.
move=> H.
apply/eqP/negPn/negP => abs; move: H.
apply Rabs_no_R0 => /eqP; by apply/negP.
Qed.

Section dominance.

(** P is dominated by Q: *)

Definition dom_by {A : Type} (P Q : A -> R) := forall a, Q a = 0 -> P a = 0.

Definition dom_byb {A : finType} (P Q : A -> R) := [forall b, (Q b == 0) ==> (P b == 0)].

End dominance.

Notation "P '<<' Q" := (dom_by P Q) (at level 10) : reals_ext_scope.

Notation "P '<<b' Q" := (dom_byb P Q) (at level 10) : reals_ext_scope.

Local Open Scope Rb_scope.

Lemma Rabs_lt a b : Rabs a <b b = (- b <b a <b b).
Proof.
case: (Rlt_le_dec a 0) => h.
  rewrite Rabs_left //.
  rewrite /Rlt_bool.
  move H1 : (Rlt_dec (- a) b) => h1.
  move H2 : (Rlt_dec (- b) a) => h2.
  move H3 : (Rlt_dec a b) => h3.
  rewrite {H1 H2 H3}.
  case: h1; case: h2; case: h3 => h1 h2 h3 //.
  apply Rnot_lt_le in h1.
  fourier.
  apply Rnot_lt_le in h2.
  fourier.
  apply Rnot_lt_le in h1.
  apply Rnot_lt_le in h2.
  fourier.
  apply Rnot_lt_le in h3.
  fourier.
rewrite /Rlt_bool.
rewrite Rabs_pos_eq //.
move H1 : (Rlt_dec a b) => h1.
move H2 : (Rlt_dec (- b) a) => h2.
rewrite {H1 H2}.
case: h1; case: h2 => h1 h2 //.
apply Rnot_lt_le in h1.
fourier.
Qed.

Lemma Rabs_le a b : Rabs a <b= b = (- b <b= a <b= b).
Proof.
case: (Rlt_le_dec a 0) => h.
  rewrite Rabs_left //.
  rewrite /Rle_bool /Rge_bool.
  move H1 : (Rge_dec b (- a)) => h1.
  move H2 : (Rge_dec a (- b)) => h2.
  move H3 : (Rge_dec b a) => h3.
  rewrite {H1 H2 H3}.
  case: h1; case: h2; case: h3 => h1 h2 h3 //.
  apply Rnot_ge_lt in h1.
  fourier.
  apply Rnot_ge_lt in h2.
  fourier.
  apply Rnot_ge_lt in h1.
  apply Rnot_ge_lt in h2.
  fourier.
  apply Rnot_ge_lt in h3.
  fourier.
rewrite /Rle_bool /Rge_bool.
rewrite Rabs_pos_eq //.
move H1 : (Rge_dec b a) => h1.
move H2 : (Rge_dec a (- b)) => h2.
rewrite {H1 H2}.
case: h1; case: h2 => h1 h2 //.
apply Rnot_ge_lt in h1.
fourier.
Qed.

Lemma Rle_mult_div_L k a b : 0 < k -> k * a <b= b = (a <b= b / k).
Proof.
move=> Hk.
move H1 : (_ <b= _ ) => [|] /=.
- move/RleP in H1.
  have H2 : a <= b / k.
    apply Rmult_le_reg_l with k => //.
    rewrite /Rdiv mulRA -(mulRC b) Rinv_r_simpl_l //.
    by apply nesym, Rlt_not_eq.
  by symmetry; apply/RleP.
- move H2 : (_ <b= _ ) => [|] //=.
  move/RleP in H2.
  apply (Rmult_le_compat_l k) in H2; last by fourier.
    rewrite /Rdiv mulRA -(mulRC b) Rinv_r_simpl_l // in H2;
      last by apply nesym, Rlt_not_eq.
  move/RleP in H2.
  by rewrite H2 in H1.
Qed.

Lemma Rle_mult_div_R k b c : 0 < k -> b <b= k * c = (b / k <b= c).
Proof.
move=> Hk.
move H1 : (_ <b= _ ) => [|] /=.
- move/RleP in H1.
  have H2 : b / k <= c.
    apply Rmult_le_reg_l with k => //.
    rewrite /Rdiv mulRA -(mulRC b) Rinv_r_simpl_l //.
    by apply nesym, Rlt_not_eq.
  symmetry; by apply/RleP.
- move H2 : (_ <b= _ ) => [|] //=.
  move/RleP in H2.
  apply (Rmult_le_compat_l k) in H2; last by fourier.
    rewrite /Rdiv mulRA -(mulRC b) Rinv_r_simpl_l // in H2;
      last by apply nesym, Rlt_not_eq.
  move/RleP in H2.
  by rewrite H2 in H1.
Qed.

Lemma Rle2_mult_div k a b c : 0 < k -> k * a <b= b <b= k * c = (a <b= b / k <b= c).
Proof.
move=> Hk.
move H1 : (_ <b= _ ) => [|] /=.
- rewrite Rle_mult_div_L // in H1.
  rewrite H1 /=.
  by apply Rle_mult_div_R.
- rewrite Rle_mult_div_L // in H1.
  by rewrite H1.
Qed.

Lemma Rle_opp a b : a <b= b = (-b <b= -a).
Proof.
move H1 : (_ <b= _ ) => [|] /=.
symmetry; apply/RleP; apply Ropp_le_contravar; by apply/RleP.
move H2 : (_ <b= _ ) => [|] //=.
move/RleP/Ropp_le_contravar/RleP : H2.
by rewrite 2!Ropp_involutive H1.
Qed.

Lemma Rle2_opp a b c : a <b= b <b= c = (- c <b= -b <b= -a).
Proof.
move H1 : (_ <b= _ ) => [|] /=.
- rewrite Rle_opp in H1.
  by rewrite H1 andbC /= Rle_opp.
- move H2 : (_ <b= _ ) => [|] //=.
  by rewrite -Rle_opp.
Qed.

Lemma Rleb_trans_minus k a b : a <b= b = ((a - k) <b= (b - k)).
Proof.
move H1 : (_ <b= _ ) => [|] /=.
- move/RleP in H1.
  apply (Rplus_le_compat_r (-k)) in H1.
  symmetry; apply/RleP; fourier.
- symmetry.
  apply/negP.
  move/negP in H1.
  contradict H1.
  move/RleP in H1.
  apply/RleP; fourier.
Qed.

Lemma Rle2_trans_minus k a b c :  (a <b= b <b= c) = ((a - k) <b= (b - k) <b= (c - k)).
Proof.
rewrite (Rleb_trans_minus k).
move H1 : (_ <b= _ ) => [|] //=.
by rewrite -Rleb_trans_minus.
Qed.

Lemma Rle2P a b c : a <b= b <b= c -> a <= b <= c.
Proof.
move H1 : (_ <b= _) => [|] //=.
move/RleP in H1.
by move/RleP.
Qed.

Section pow_sect.

Lemma INR_pow_expn (r : nat) : forall n, INR r ^ n = INR (expn r n).
Proof.
elim => // n IH.
by rewrite (expnSr r n) mult_INR -addn1 pow_add /= mulR1 IH.
Qed.

Lemma pow_mult x y : forall n, (x * y) ^ n = x ^ n * y ^ n.
Proof.
elim=> /= [|n IH]; first by rewrite mul1R.
rewrite -2!mulRA; f_equal.
rewrite [in X in _ = X]mulRC -mulRA; f_equal.
by rewrite IH mulRC.
Qed.

Lemma pow_gt0 x : 0 < x -> forall n, 0 < x ^ n.
Proof.
move=> x_pos.
elim => [/= | n IH]; by [apply Rlt_0_1 | apply Rmult_lt_0_compat].
Qed.

Lemma pow_ge0 x : 0 <= x -> forall n, 0 <= x ^ n.
Proof.
move=> x_pos.
elim => [/= | n IH]; first by apply Rlt_le, Rlt_0_1.
rewrite -(mulR0 0).
apply Rmult_le_compat => //; by apply Rle_refl.
Qed.

Lemma pow_not0 x : x <> 0 -> forall n, x ^ n <> 0.
Proof.
move=> x_not0.
elim => [/= | n IH]; first by apply not_eq_sym, Rlt_not_eq, Rlt_0_1.
by apply Rmult_integral_contrapositive.
Qed.

Lemma pow_inv x : x <> 0 -> forall n, (/ x) ^ n = / x ^ n.
Proof.
move=> x_not0.
elim=> /= [ | n IH]; first by rewrite Rinv_1.
rewrite Rinv_mult_distr //; by [ rewrite IH | apply pow_not0].
Qed.

Lemma Rmult_pow_inv r a b : r <> 0 -> (b <= a)%nat -> r ^ a * (/ r) ^ b = r ^ (a - b).
Proof.
move=> Hr ab; symmetry.
by rewrite (pow_RN_plus r _ b) // plusE -minusE subnK // pow_inv.
Qed.

End pow_sect.

Section exp_lb_sect.

Let exp_dev n := fun x => exp x - x ^ n * / INR (n`!).

Let derivable_exp_dev n : derivable (exp_dev n).
Proof.
rewrite /exp_dev => x.
apply derivable_pt_minus ; first by apply derivable_pt_exp.
apply derivable_pt_mult ; first by apply derivable_pt_pow.
by apply derivable_pt_const.
Defined.

Let exp_dev_rec n x : derive_pt (exp_dev n.+1) x (derivable_exp_dev n.+1 x) = exp_dev n x.
Proof.
rewrite /exp_dev derive_pt_minus derive_pt_exp ; f_equal.
rewrite derive_pt_mult derive_pt_const mulR0 addR0 derive_pt_pow.
rewrite mulRC mulRA mulRC; f_equal.
rewrite factS mult_INR Rinv_mult_distr ; last 2 first.
- apply not_0_INR => /eqP ; apply/negP ; by rewrite -lt0n.
- apply not_eq_sym, Rlt_not_eq, lt_0_INR.
  apply/ltP ; by apply fact_gt0.
rewrite mulRC mulRA Rinv_r ; first by rewrite mul1R.
apply not_0_INR => /eqP ; apply/negP ; by rewrite -lt0n.
Qed.

Let exp_dev_gt0 : forall n r, 0 < r -> 0 < exp_dev n r.
Proof.
elim => [r rpos | n IH r rpos].
- rewrite /exp_dev /= mul1R Rinv_1 -exp_0.
  by apply Rgt_lt, Rgt_minus, Rlt_gt, exp_increasing.
- apply: (Rlt_trans _ 1) ; first by fourier.
  rewrite (_ : 1 = exp_dev n.+1 0) ; last first.
    rewrite /exp_dev exp_0 pow_i ; last by apply/ltP.
    by rewrite mul0R /Rminus Ropp_0 addR0.
  move: derive_increasing_interv.
  move/(_ 0 r (exp_dev n.+1) (derivable_exp_dev n.+1) rpos).
  have Haux : forall t : R,
     0 < t < r -> 0 < derive_pt (exp_dev n.+1) t (derivable_exp_dev n.+1 t).
    move=>x Hx.
    rewrite exp_dev_rec.
    by apply IH, Hx.
  move/(_ Haux 0 r) => {Haux}.
  apply => //.
  - split; by [apply Rle_refl | apply Rlt_le].
  - split; by [apply Rlt_le | apply Rle_refl].
Qed.

Lemma exp_strict_lb n x : 0 < x -> x ^ n * / INR (n`!) < exp x.
Proof. move=> xpos; by apply Rgt_lt, Rminus_gt, Rlt_gt, exp_dev_gt0. Qed.

Let exp_dev_ge0 n r : 0 <= r -> 0 <= exp_dev n r.
Proof.
move=> Hr.
case/orP : (orbN (r == 0)) ; last first.
- move=> Hr2.
  have {Hr Hr2}R_pos : 0 < r.
    apply/RltP; rewrite Rlt_neqAle eq_sym Hr2 /=; by apply/RleP.
  by apply Rlt_le, exp_dev_gt0.
- move=> /eqP ->.
  move:n ; case.
  - rewrite /exp_dev exp_0 /= Rinv_1 mul1R /Rminus Rplus_opp_r; by apply Rle_refl.
  - move=> n.
    rewrite -(_ : 1 = exp_dev n.+1 0); first by apply Rle_0_1.
    rewrite /exp_dev exp_0 pow_i; last by apply/ltP.
    rewrite mul0R; by ring.
Qed.

Lemma exp_lb n x : 0 <= x -> x ^ n / INR (n`!) <= exp x.
Proof. move=> xpos; by apply Rge_le, Rminus_ge, Rle_ge, exp_dev_ge0. Qed.

End exp_lb_sect.

Lemma fact_Coq_SSR n0 : fact n0 = n0 `!.
Proof. elim: n0 => // n0 IH /=. by rewrite IH factS mulSn -multE. Qed.

Lemma combinaison_Coq_SSR n0 m0 : (m0 <= n0)%nat -> C n0 m0 = INR 'C(n0, m0).
Proof.
move=> ?.
rewrite /C.
apply Rmult_eq_reg_r with (INR (fact m0) * INR (fact (n0 - m0)%coq_nat)).
set tmp := INR (fact m0) * _.
rewrite /Rdiv -mulRA Rinv_l; last first.
  rewrite /tmp.
  apply Rmult_integral_contrapositive.
  split; by apply not_0_INR, fact_neq_0.
by rewrite mulR1 /tmp -!mult_INR !fact_Coq_SSR !multE !minusE bin_fact.
apply Rmult_integral_contrapositive.
split; by apply not_0_INR, fact_neq_0.
Qed.
