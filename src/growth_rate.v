Require Import Reals Psatz.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div choice fintype tuple finfun bigop.
From mathcomp Require Import prime binomial ssralg.
From infotheo Require Import Reals_ext ssrR ssr_ext ssralg_ext Rbigop proba num_occ.
Require Import Rbigop_complements bigop_tactics reals_complements.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope R_scope with Re.
Local Open Scope R_scope.

Lemma Rdiv1E (x : R) : x / 1 = x.
Proof. by rewrite /Rdiv Rinv_1 Rmult_1_r. Qed.

(** The following definition can be used by doing [rewrite !Rsimpl] *)
Definition Rsimpl :=
  (Rplus_0_l, Rplus_0_r, Rmult_1_l, Rmult_1_r, Rmult_0_l, Rmult_0_r,
   pow1, pow_O, pow_1, Rminus_0_r, Rminus_0_l, Rdiv1E).

Module Psatz_helper. (* taken from Drincq (https://gitlab.com/erikmd/drincq) *)
(** Defined a generalized tactic of [simp2] called [simpdiv]. *)

Ltac simpdiv_hyp r Pr H :=
let H' := fresh H in
match type of H with
| ?x = ?y => pose proof @Rmult_eq_compat_r r _ _ H as H'
| Rlt ?x ?y => pose proof @Rmult_lt_compat_r r _ _ Pr H as H'
| Rle ?x ?y =>
  pose proof @Rmult_le_compat_r r _ _ (@Rlt_le _ _ Pr) H as H'
| Rgt ?x ?y =>
  pose proof @Rmult_gt_compat_r r _ _ (@Rlt_gt _ _ Pr) H as H'
| Rge ?x ?y =>
  pose proof @Rmult_ge_compat_r r _ _ (@Rgt_ge _ _ (@Rlt_gt _ _ Pr)) H as H'
end; clear H; field_simplify in H'; rewrite ?Rdiv1E in H'; rename H' into H.

Ltac simpdiv_goal r Pr :=
match goal with
| |- ?x = ?y => refine (@Rmult_eq_reg_r r _ _ _ (@Rgt_not_eq _ _ Pr))
| |- Rlt ?x ?y => apply (@Rmult_lt_reg_r r _ _ Pr)
| |- Rle ?x ?y => apply (@Rmult_le_reg_r r _ _ Pr)
| |- Rgt ?x ?y => apply (@Rmult_lt_reg_r r _ _ Pr)
| |- Rge ?x ?y => (apply Rle_ge; apply (@Rmult_le_reg_r r _ _ Pr))
end; field_simplify; rewrite ?Rdiv1E.

Ltac simpdiv r Pr :=
repeat match goal with
| [H : context[Rinv r] |- _] => simpdiv_hyp r Pr H
| [H : context[Rdiv _ r] |- _] => simpdiv_hyp r Pr H
| |- context[Rinv r] => simpdiv_goal r Pr
| |- context[Rdiv _ r] => simpdiv_goal r Pr
end.

End Psatz_helper.

Ltac simpdiv_cut r :=
  let Pr := fresh "Pr" in
  cut (0 < r)%R; [intro Pr; Psatz_helper.simpdiv r Pr|idtac].

(*
(* Rdiv_eq_reg was taken from Interval.Interval_missing *)
Lemma Rdiv_eq_reg a b c d :
  (a * d = b * c -> b <> 0%Re -> d <> 0%Re -> a / b = c / d)%Re.
Proof.
intros Heq Hb Hd.
apply (Rmult_eq_reg_r (b * d)).
field_simplify; trivial.
now rewrite Heq.
now apply Rmult_integral_contrapositive_currified.
Qed.
 *)

Section Missing.

Lemma bool_ind_and (P : bool -> Prop) : P true /\ P false -> forall b : bool, P b.
Proof. by case => H1 H0; case. Qed.

Lemma INR_bin2 n : INR 'C(n, 2) = INR n * (INR n - 1) / 2.
Proof.
rewrite bin2.
case: n => [|n].
rewrite /= /INR !Rsimpl; lra.
change 1 with (INR 1) at 1; rewrite -minus_INR; last exact/leP.
simpdiv_cut 2; auto with real.
change 2 with (INR 2).
rewrite -!mult_INR.
congr INR.
rewrite multE mul2n -[RHS]odd_double_half minusE subn1.
suff->: odd (n.+1 * n.+1.-1) = false by [].
apply negbTE.
elim: n => [//|n IHn].
rewrite [n.+2.-1]/= mulnC.
rewrite [n.+1.-1]/= in IHn.
rewrite -addn2.
rewrite mulnDr -dvdn2; rewrite -dvdn2 in IHn.
by rewrite dvdn_addl // dvdn_mull.
Qed.

Lemma binSm_div n m : INR 'C(n, m.+1) = INR 'C(n, m) * (INR n - INR m) / (1 + INR m).
Proof.
have := mul_bin_left n m.
move/(congr1 INR).
have [Hle|Hgt] := leqP m n.
{ rewrite !(plus_INR,mult_INR) minus_INR; [move=> H|exact/leP].
  simpdiv_cut (1 + INR m); try lra.
  change 1 with (INR 1); rewrite -plus_INR.
  exact/lt_0_INR/ltP. }
rewrite !(bin_small Hgt) !mult_INR -[INR 0]/(0) /Rdiv !(Rmult_0_r, Rmult_0_l).
by move/eqP; rewrite mulR_eq0 INR_eq0' /=; move/eqP.
Qed.

Lemma Rmult_minus1 r : -1 * r = - r.
Proof. by rewrite Ropp_mult_distr_l_reverse Rmult_1_l. Qed.

Lemma pow_1_dvdn2 a : 2 %| a -> (-1) ^ a = 1.
Proof. by case/dvdnP => m ->; rewrite mulnC pow_1_even. Qed.

Lemma Rlt_pow_l (x y : R) (m : nat) : (0 < m)%N -> 0 <= x -> x < y -> x ^ m < y ^ m.
Proof.
case: m =>[//|m _].
elim: m => [|m IHm] //= Hx Hxy.
by rewrite !Rsimpl.
apply Rmult_le_0_lt_compat; auto with real.
pose proof pow_ge0 Hx m.
exact: Rmult_le_pos.
Qed.

Lemma Rge_pow_leq (x : R) (m n : nat) : (0 < x < 1) -> (m <= n)%N -> x ^ n <= x ^ m.
Proof.
move=> [_x x_] /leP Hmn.
induction Hmn; first by apply Rle_ge, Rle_refl.
simpl.
rewrite -(Rmult_1_l (x ^ m)).
apply Rmult_le_compat =>//; try exact: Rlt_le.
by apply pow_ge0, Rlt_le.
Qed.

End Missing.

Section Growth_rate.

Variables (p : R) (n k : nat).

Definition g s := (1 - (1 - p^(2^(n-k-s)))^(2^k))^(2^s).

Definition phi s := g s - g 0.

Variable (s : nat).

Hypothesis p_bnd : 0 < p < 1.
Hypothesis k_gt0 : (0 < k)%N.
Hypothesis s_n_k : (s <= n - k)%N.

Lemma rsum_abs_le (F : nat -> R) (a b : nat) :
  (a <= b)%N -> (*superfluous*)
  2 %| a ->
  0 <= F a ->
  (forall i, (a <= i <= b)%N -> 0 <= F i.+1 <= F i) ->
  0 <= \rsum_(a <= i < b.+1) (-1) ^ i * F i <= F a.
Proof.
move=> Hab Ha H0.
rewrite -(subnK Hab).
have := leq_subr a b.
rewrite -(odd_double_half (b - a)).
set b0 := odd (b - a).
elim/bool_ind_and: b0.
elim: ((b - a)./2)%N => [|m IHm].
{ split.
  { rewrite double0 addn0.
    move=> /= Hb HF.
    rewrite add1n big_ltn // big_nat1.
    rewrite /= pow_1_dvdn2 ?Rsimpl //.
    rewrite (_: _ + _ = F a - F a.+1); last ring.
    move/(_ a) in HF; rewrite add1n !leqnn /= in HF.
    move/(_ (ltnW (leqnn _))) in HF.
    lra. }
  by rewrite add0n big_nat1 pow_1_dvdn2 ?Rsimpl //; auto with real. }
rewrite add1n add0n addSn big_nat_recr 1?big_nat_recr /= ?leq_addl ?leqW ?leq_addl //.
split => Hb HF.
{ rewrite -doubleE pow_add !pow_1_dvdn2 //; last by rewrite -mul2n ?dvdn_mulr.
  rewrite !Rsimpl -[-1 * -1]Rsqr_neg [Rsqr _]Rsimpl !Rsimpl.
  rewrite /= !(add0n, addn0, add1n, addn1, addSn) in IHm.
  have {IHm} [A B] := IHm.
  have A1 : (m.*2 < b)%N by rewrite doubleS in Hb; do 2![move/ltnW in Hb].
  have A2 : (forall i : nat, (a <= i <= (m.*2 + a).+1)%N -> 0 <= F i.+1 <= F i).
    by move=> i /andP[_i i_]; apply: HF; rewrite _i /= doubleS !addSn 2?ltnW //.
  have {A1 A2} A3 := A A1 A2.
  have B1 : (m.*2 <= b)%N by rewrite doubleS in Hb; do 3![move/ltnW in Hb].
  have B2 : (forall i : nat, (a <= i <= (m.*2 + a))%N -> 0 <= F i.+1 <= F i).
    by move=> i /andP[_i i_]; apply: HF; rewrite _i /= doubleS !addSn 3?ltnW.
  have {B1 B2} B3 := B B1 B2.
  set G := \rsum_(a <= i < (m.+1).*2 + a) (-1) ^ i * F i in A3 *.
  have C1 : (a <= (m.+1).*2 + a <= ((m.+1).*2 + a).+1)%N.
    apply/andP; split; first by rewrite leq_addl.
    by do 1![apply leqW].
  have {C1} C2 := HF _ C1.
  split; try lra; clear A3.
  rewrite {}/G doubleS !addSn big_nat_recr /=; last first.
  { by rewrite leqW // leq_addl. }
  set G := \rsum_(a <= i < (m.*2 + a).+1) (-1) ^ i * F i in B3 *.
  rewrite pow_1_dvdn2; last first.
  by rewrite dvdn_addl // -mul2n dvdn_mulr.
  rewrite !Rmult_minus1.
  apply Rle_trans with G; try lra.
  set ma := (m.*2 + a)%N.
  have D1 : (a <= ma <= ((m.+1).*2 + a).+1)%N.
    apply/andP; split; first by rewrite leq_addl.
    by do 2![apply leqW].
  have D2 : (a <= ma.+1 <= ((m.+1).*2 + a).+1)%N.
    apply/andP; split; first by rewrite leqW ?leq_addl.
    by do 2![apply leqW].
  have D3 : (a <= ma.+2 <= ((m.+1).*2 + a).+1)%N.
    apply/andP; split; first by rewrite 2?leqW ?leq_addl.
    by do 1![apply leqW].
  have {D1} D1 := HF _ D1.
  have {D2} D2 := HF _ D2.
  have {D3} D3 := HF _ D3.
  lra. }
{ rewrite -doubleE pow_add !pow_1_dvdn2 //; last by rewrite -mul2n ?dvdn_mulr.
  rewrite !Rsimpl -[-1 * -1]Rsqr_neg [Rsqr _]Rsimpl !Rsimpl.
  rewrite /= !(add0n, addn0, add1n, addn1, addSn) in IHm.
  have {IHm} [A B] := IHm.
  have A1 : (m.*2 < b)%N by rewrite doubleS in Hb; do 1![move/ltnW in Hb].
  have A2 : (forall i : nat, (a <= i <= (m.*2 + a).+1)%N -> 0 <= F i.+1 <= F i)
    by move=> i /andP[_i i_]; apply: HF; rewrite _i /= doubleS !addSn 1?ltnW.
  have {A1 A2} A3 := A A1 A2.
  have B1 : (m.*2 <= b)%N by rewrite doubleS in Hb; do 2![move/ltnW in Hb].
  have B2 : (forall i : nat, (a <= i <= (m.*2 + a))%N -> 0 <= F i.+1 <= F i)
    by move=> i /andP[_i i_]; apply: HF; rewrite _i /= doubleS !addSn 2?ltnW.
  have {B1 B2} B3 := B B1 B2.
  set G := \rsum_(a <= i < (m.+1).*2 + a) (-1) ^ i * F i in A3 *.
  have C1 : (a <= (m.+1).*2 + a <= ((m.+1).*2 + a))%N.
    by apply/andP; split; first by rewrite leq_addl.
  have {C1} C2 := HF _ C1.
  split; try lra; clear A3.
  rewrite {}/G doubleS !addSn big_nat_recr /=; last first.
  { by rewrite leqW // leq_addl. }
  set G := \rsum_(a <= i < (m.*2 + a).+1) (-1) ^ i * F i in B3 *.
  rewrite pow_1_dvdn2; last first.
  by rewrite dvdn_addl // -mul2n dvdn_mulr.
  rewrite !Rmult_minus1.
  apply Rle_trans with G; try lra.
  set ma := (m.*2 + a)%N.
  have D1 : (a <= ma <= ((m.+1).*2 + a))%N.
    apply/andP; split; first by rewrite leq_addl.
    by do 2![apply leqW].
  have D2 : (a <= ma.+1 <= ((m.+1).*2 + a))%N.
    apply/andP; split; first by rewrite leqW ?leq_addl.
    by do 1![apply leqW].
  have D3 : (a <= ma.+2 <= ((m.+1).*2 + a))%N.
    by apply/andP; split; first by rewrite 2?leqW ?leq_addl.
  have {D1} D1 := HF _ D1.
  have {D2} D2 := HF _ D2.
  have {D3} D3 := HF _ D3.
  lra. }
Qed.

Theorem phi_ineq :
  2^k * p^(2^(n-k-s)) < 1 -> phi s > (2^((k-1) * 2^s) - 2^k) * p^(2^(n-k)).
Proof.
rewrite /phi /g subn0 /= Rmult_1_r.
pose t s := p^(2^(n-k-s)) => H6.
fold (t s).
have Pt : 0 < t s by apply pow_gt0; apply (proj1 p_bnd).
have Pkt : 0 < 2^k * t s.
{ by apply Rmult_lt_0_compat =>//; apply pow_gt0; lra. }
have H9 : forall s,  (1 - (1 - t s) ^ 2 ^ k) =
  2^k * t s - (2^k * t s)^2 *
  \rsum_(2<=i<(2^k).+1) (-1) ^ i * (INR 'C(2^k, i) * t s^(i-2) / 2^(2*k)).
{ move=> s'; rewrite {2}/Rminus RPascal.
  rewrite -(big_mkord predT (fun i => INR 'C(2^k, i) * (1 ^ (2^k - i) * (- t s')^i))) /=.
  rewrite big_ltn // big_ltn; last by rewrite ltnS expn_gt0.
  rewrite bin0 -[INR 1]/R1 bin1 !Rsimpl -INR_pow_expn -[INR 2]/(2%Re).
  rewrite (big_morph _ (morph_mulRDr _) (id1 := R0)) ?Rsimpl //.
  ring_simplify; congr Rminus.
  apply eq_big_nat => i /andP[_i i_].
  simpdiv_cut (2 ^ (2 * k)); [| lra | apply: pow_gt0; lra].
  (* rewrite -Rmult_minus1. *)
  rewrite pow_opp pow1.
  rewrite -[in t s' ^ i](@subnK 2 i) // Rsimpl pow_add.
  (* missing lemma _^_^_ *)
  rewrite Rdef_pow_add /= plusE addn0 Rsimpl.
  ring. }
have H10 : (1 - (1 - t s) ^ 2 ^ k) > 2^(k-1) * t s.
{ apply Rge_gt_trans with (2^k * t s - (2^k * t s)^2 * (1 / 2)); last first.
  { simpdiv_cut 2; auto with real.
    rewrite -Rlt_subl_addr.
    rewrite ![pow _ 2]/=; rewrite !Rsimpl.
    rewrite -!Ropp_mult_distr_l.
    apply ltR_oppr.
    fold (t s) in H6.
    pose proof Rmult_lt_compat_r _ _ _ Pkt H6 as H.
    rewrite Rsimpl in H.
    rewrite tech_pow_Rmult -subSn // subn1 /=.
    lra. }
  rewrite {}H9 /Rminus.
  apply Rplus_ge_compat_l.
  apply Ropp_ge_contravar.
  apply Rmult_ge_compat_l.
  { by apply Rle_ge, pow_ge0, Rlt_le. }
  apply Rge_trans with
    (let i := 2%N in ((-1) ^ i * (INR 'C(2 ^ k, i) * t s ^ (i - 2) / 2 ^ (2 * k)))).
  { rewrite /= !Rsimpl INR_bin2.
    simpdiv_cut 2; auto with real.
    simpdiv_cut (2 ^ (2 * k)); auto with real.
    rewrite -!INR_pow_expn INR_IZR_INZ /=.
    rewrite Rdef_pow_add plusE addn0 /= Rsimpl.
    pose proof pow_gt0 Pr k; lra. }
  (* The sum is less than its first term *)
  cbv zeta; rewrite pow_1_dvdn2 // Rmult_1_l.
  apply Rle_ge, rsum_abs_le =>//.
  { by rewrite -{1}[1%N]/(2 ^ 0)%N ltn_exp2l. }
  { rewrite subnn /= Rsimpl; simpdiv_cut (2 ^ (2 * k)); auto with real. }
  move=> i Hi; rewrite binSm_div.
  have /andP [_i i_] := Hi.
  rewrite subSn //= /Rdiv.
  set i1 := / (1 + INR i).
  set k2 := / 2 ^ (2 * k).
  set num := (INR (2 ^ k) - INR i).
  have Hnum : num < 2 ^ k.
  { rewrite /num; rewrite -minus_INR; last exact/leP.
    have->: 2 ^ k = INR (2 ^ k) by rewrite -INR_pow_expn.
    apply/lt_INR/ltP; rewrite minusE.
    rewrite -subSn // leq_subLR.
    by rewrite -addn1 addnC leq_add // ltnW. }
  have PC : 0 <= INR 'C(2 ^ k, i) by apply pos_INR.
  have Pnum : 0 <= num.
  { rewrite /num; rewrite -minus_INR; last exact/leP.
    exact: pos_INR. }
  have Pi1 : 0 <= i1.
  { apply Rlt_le, Rinv_0_lt_compat; pose proof pos_INR i; lra. }
  have Pk2 : 0 <= k2.
  { by apply Rlt_le, Rinv_0_lt_compat, pow_gt0; auto with real. }
  split.
  { by repeat apply Rmult_le_pos =>//; auto with real. }
  rewrite !Rmult_assoc.
  apply Rmult_le_compat_l =>//.
  have Hi1 : i1 <= 1.
  { have->: 1 = / 1 by auto with real.
    apply Rinv_le_contravar; auto with real; pose proof pos_INR i; lra. }
  have->: num * (i1 * (t s * (t s ^ (i - 2) * k2))) =
    t s ^ (i - 2) * (k2 * ((num * t s) * i1)) by ring.
  apply Rmult_le_compat_l.
  { by apply pow_ge0, Rlt_le. }
  rewrite -{2}(Rmult_1_r k2).
  apply Rmult_le_compat_l =>//.
  (* workaround *) apply Rle_trans with (1 * i1); last by rewrite Rsimpl.
  apply Rmult_le_compat_r =>//.
  apply Rle_trans with (2 ^ k * t s) =>//.
  { apply Rmult_le_compat_r =>//; exact: Rlt_le. }
  exact: Rlt_le. }
have H11 : (1 - (1 - t s) ^ 2 ^ k) ^ 2 ^ s > 2 ^ ((k - 1) * (2 ^ s)) * p ^ 2 ^ (n - k).
{ apply Rlt_gt.
  set lhs := 2 ^ _ * p ^ _.
  suff->: lhs = (2 ^ (k - 1) * t s) ^ 2 ^ s.
  apply: Rlt_pow_l.
  - exact: expn_gt0.
  - apply Rmult_le_pos; last 1 [exact: Rlt_le] || apply: pow_ge0; lra.
  - exact: Rlt_gt.
  rewrite /lhs !(pow_mult,Rpow_mult_distr) /t.
  congr Rmult.
  rewrite -pow_muln.
  congr pow.
  rewrite multE -expnD.
  congr expn.
  by rewrite subnK. }
have H12 : 1 - (1 - p ^ 2 ^ (n - k)) ^ 2 ^ k <= 2 ^ k * p ^ 2 ^ (n - k).
{ have := H9 0%N; rewrite /t subn0 =>->.
  apply/Rle_subr_addl; rewrite Rminus_diag_eq //.
  apply Rge_le, Ropp_0_le_ge_contravar.
  apply Rmult_le_pos.
  have two : 0 <= 2 by lra.
  pose proof pow_ge0 two k as two_k.
  have t0 : 0 <= t 0%N by apply pow_ge0 with (1 := Rlt_le _ _ (proj1 p_bnd)).
  rewrite /t subn0 in t0.
  { rewrite /= ?Rsimpl.
    repeat apply Rmult_le_pos; trivial. }
  apply rsum_abs_le =>//.
  (* The code below looks very much like the proof for arbitrary s *)
  { by rewrite -{1}[1%N]/(2 ^ 0)%N ltn_exp2l. } (* again *)
  { rewrite subnn /= Rsimpl; simpdiv_cut (2 ^ (2 * k)); auto with real. }
  move=> i Hi; rewrite binSm_div.
  have /andP [_i i_] := Hi.
  rewrite subSn //= /Rdiv.
  set i1 := / (1 + INR i).
  set k2 := / 2 ^ (2 * k).
  set num := (INR (2 ^ k) - INR i).
  have Hnum : num < 2 ^ k.
  { rewrite /num; rewrite -minus_INR; last exact/leP.
    have->: 2 ^ k = INR (2 ^ k) by rewrite -INR_pow_expn.
    apply/lt_INR/ltP; rewrite minusE.
    rewrite -subSn // leq_subLR.
    by rewrite -addn1 addnC leq_add // ltnW. }
  have PC : 0 <= INR 'C(2 ^ k, i) by apply pos_INR.
  have Pnum : 0 <= num.
  { rewrite /num; rewrite -minus_INR; last exact/leP.
    exact: pos_INR. }
  have Pi1 : 0 <= i1.
  { apply Rlt_le, Rinv_0_lt_compat; pose proof pos_INR i; lra. }
  have Pk2 : 0 <= k2.
  { by apply Rlt_le, Rinv_0_lt_compat, pow_gt0; auto with real. }
  set t00 := p^2^(n-k).
  have Pt00 : 0 <= t00 by apply pow_ge0; lra.
  have Hi1 : i1 <= 1.
  { have->: 1 = / 1 by auto with real.
     apply Rinv_le_contravar; auto with real; pose proof pos_INR i; lra. }
  split.
  { repeat apply Rmult_lt_pos =>//; auto with real.
    rewrite !Rmult_assoc.
    apply Rmult_le_pos =>//.
    have->: num * (i1 * (t00 * (t00 ^ (i - 2) * k2))) =
      t00 ^ (i - 2) * (k2 * ((num * t00) * i1)) by ring.
    apply Rmult_le_pos.
    { exact: pow_ge0. }
    by repeat apply Rmult_le_pos. }
  rewrite -{2}(Rmult_1_r k2) Rsimpl.
  apply Rmult_le_compat_r =>//.
  rewrite !Rmult_assoc.
  apply Rmult_le_compat_l =>//.
  rewrite -!Rmult_assoc.
  rewrite -{2}(Rmult_1_l ((p ^ 2 ^ (n - k)) ^ (i - 2))).
  apply Rmult_le_compat_r.
  repeat apply pow_ge0; lra.
  apply Rle_trans with (2 ^ k * t 0%N) =>//.
  { rewrite /t subn0.
    apply Rmult_le_compat_r =>//.
    rewrite -(Rmult_1_r (2 ^ k)).
    apply Rmult_le_compat =>//.
    exact: Rlt_le. }
  rewrite /t subn0.
  clear - H6 p_bnd.
  have E1 : (n - k - s <= n - k)%N by rewrite leq_subr.
  rewrite -(@leq_exp2l 2) // in E1.
  set (nks := (n - k - s)%N) in *.
  set (nk := (n - k)%N) in *.
  move/(Rge_pow_leq p_bnd) in E1.
  move/(Rmult_le_compat_l (2 ^ k)) in E1.
  apply Rlt_le, Rle_lt_trans with (2 := H6).
  apply E1, pow_ge0; lra. }
clear H6 H9 H10; rewrite /t in H11 H12 *.
lra.
Qed.

End Growth_rate.
