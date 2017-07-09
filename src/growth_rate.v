Require Import Reals Psatz.
From Coquelicot Require Import Coquelicot.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div choice fintype tuple finfun bigop.
From mathcomp Require Import prime binomial ssralg.
From Infotheo Require Import Reals_ext Rssr ssr_ext ssralg_ext Rbigop proba num_occ.
Require Import Rbigop_complements bigop_tactics reals_complements.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope R_scope with Re.

(** The following definition can be used by doing [rewrite !Rsimpl] *)
Definition Rsimpl :=
  (Rplus_0_l, Rplus_0_r, Rmult_1_l, Rmult_1_r, Rmult_0_l, Rmult_0_r,
   pow1, pow_O, pow_1, Rminus_0_r, Rminus_0_l, Rdiv_1).


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
end; clear H; field_simplify in H'; rewrite ?Rdiv_1 in H'; rename H' into H.

Ltac simpdiv_goal r Pr :=
match goal with
| |- ?x = ?y => refine (@Rmult_eq_reg_r r _ _ _ (@Rgt_not_eq _ _ Pr))
| |- Rlt ?x ?y => apply (@Rmult_lt_reg_r r _ _ Pr)
| |- Rle ?x ?y => apply (@Rmult_le_reg_r r _ _ Pr)
| |- Rgt ?x ?y => apply (@Rmult_lt_reg_r r _ _ Pr)
| |- Rge ?x ?y => (apply Rle_ge; apply (@Rmult_le_reg_r r _ _ Pr))
end; field_simplify; rewrite ?Rdiv_1.

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

Lemma INR_bin2 n : INR 'C(n, 2) = INR n * (INR n - 1) / 2.
Proof.
rewrite bin2.
case: n => [|n].
rewrite /= /INR !Rsimpl; psatzl R.
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

Section Growth_rate.

Variables (p : R) (n k : nat).

Definition g s := (1 - (1 - p^(2^(n-k-s)))^(2^k))^(2^s).

Definition phi s := g s - g 0.

Variable (s : nat).

Hypothesis k_gt0 : (0 < k)%N.
Hypothesis s_n_k : INR s <= INR n - INR k.

Theorem phi_ineq :
  2^k * p^(2^(n-k-s)) < 1 -> phi s > (2^((k-1) * 2^s) - 2^k) * p^(2^(n-k)).
Proof.
rewrite /phi /g subn0 /= Rmult_1_r.
set t := p^(2^(n-k-s)) => H6.
have H9 : (1 - (1 - t) ^ 2 ^ k) =
  2^k * t - (2^k * t)^2 * \rsum_(2<=i<(2^k).+1) INR 'C(2^k, i) * (-1)^i * t^(i-2) / 2^(2*k).
{ rewrite {2}/Rminus RPascal.
  rewrite -(big_mkord predT (fun i => INR 'C(2^k, i) * (1 ^ (2^k - i) * (- t)^i))) /=.
  rewrite big_ltn // big_ltn; last by rewrite ltnS expn_gt0.
  rewrite bin0 -[INR 1]/R1 bin1 !Rsimpl -INR_pow_expn -[INR 2]/(2%Re).
  rewrite (big_morph _ (morph_mulRDr _) (id1 := R0)) ?Rsimpl //.
  ring_simplify; congr Rminus.
  apply eq_bigr => i _.
  (* simpdiv_cut (2 ^ (2 * k)). *)
  admit. (* easy = *) }
have H10 : (1 - (1 - t) ^ 2 ^ k) > 2^(k-1) * t.
{ apply Rge_gt_trans with (2^k * t - (2^k * t)^2 * (1 / 2)); last first.
  { rewrite -Rmult_pow_inv; discrR; trivial.
    simpdiv_cut 2; auto with real.
    rewrite -Rlt_subl_addr.
    ring_simplify.
    rewrite ![pow _ 2]/=; rewrite !Rsimpl.
    rewrite -!Ropp_mult_distr_l.
    apply Ropp_lt_contravar.
    have H0 : 0 < 2^k * t.
    { rewrite /t.
      admit. (* easy 0 < *)}
    pose proof Rmult_lt_compat_r _ _ _ H0 H6 as H1.
    rewrite Rsimpl in H1.
    psatzl R. }
  rewrite {}H9 /Rminus.
  apply Rplus_ge_compat_l.
  apply Ropp_ge_contravar.
  apply Rmult_ge_compat_l.
  { admit. (* easy >= 0 *)}
  apply Rge_trans with
    (let i := 2%N in (INR 'C(2 ^ k, i) * (-1) ^ i * t ^ (i - 2) / 2 ^ (2 * k))).
  { rewrite /= !Rsimpl INR_bin2.
    admit. (* >= / ^ *) }
  (* The sum is less than its first term *)
  admit. }
have H11 : (1 - (1 - p ^ 2 ^ (n - k - s)) ^ 2 ^ k) ^ 2 ^ s >
  2 ^ ((k - 1) * (2 ^ s)) * p ^ 2 ^ (n - k).
{ admit. (* ^ (2^s) *) }
have H12 : 1 - (1 - p ^ 2 ^ (n - k)) ^ 2 ^ k < 2 ^ k * p ^ 2 ^ (n - k).
{ admit. (* trickier *) }
clear H6 H9 H10; rewrite {}/t.
psatzl R.
Admitted.

Notation log2 := log2.log (only parsing).

Theorem phi_ineq_suff :
  INR s <= INR (n - k) - log2 (INR k.+1) + log2 (Rabs (log2 p)) ->
  2^k * p^(2^(n-k-s)) < 1.
Proof.
Admitted. (* todo *)
