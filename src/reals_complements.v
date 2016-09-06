Require Import Reals.
From mathcomp Require Import ssreflect.
From Infotheo Require Import Reals_ext.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope R_scope.

(** Support results to transpose terms with inequalities over reals.
    To this aim, we reuse MathComp naming conventions. *)

Lemma Rle_subl_addr x y z : (x - y <= z) <-> (x <= z + y).
Proof.
split=> H.
  rewrite -(Rplus_0_r x) -(Rplus_opp_l y) -Rplus_assoc.
  by apply Rplus_le_compat_r.
rewrite -(Rplus_0_r z) -(Rplus_opp_r y) -Rplus_assoc.
by apply Rplus_le_compat_r.
Qed.

Lemma Rle_subr_addr x y z : (x <= y - z) <-> (x + z <= y).
Proof.
split=> H.
  rewrite -(Rplus_0_r y) -(Rplus_opp_l z) -Rplus_assoc.
  by apply Rplus_le_compat_r.
rewrite -(Rplus_0_r x) -(Rplus_opp_r z) -Rplus_assoc.
by apply Rplus_le_compat_r.
Qed.

Definition Rle_sub_addr := (Rle_subl_addr, Rle_subr_addr).

Lemma Rle_subl_addl x y z : (x - y <= z) <-> (x <= y + z).
Proof.
split=> H.
  by rewrite Rplus_comm -Rle_sub_addr.
by rewrite -Rle_sub_addr /Rminus Ropp_involutive Rplus_comm.
Qed.

Lemma Rle_subr_addl x y z : (x <= y - z) <-> (z + x <= y).
split=> H.
  by rewrite Rplus_comm -Rle_sub_addr.
by rewrite -Rle_sub_addr /Rminus Ropp_involutive Rplus_comm.
Qed.

Definition Rle_sub_addl := (Rle_subl_addl, Rle_subr_addl).

(** Support results to transpose terms w.r.t equality over reals.
    To this aim, we reuse MathComp naming conventions. *)

Lemma oppRK r : - - r = r.
Proof Ropp_involutive r.

Lemma addRN r : r + - r = 0.
Proof Rplus_opp_r r.

Lemma subRR r : r - r = 0.
Proof addRN r.

Lemma subR0_eq x y : x - y = 0 -> x = y.
Proof Rminus_diag_uniq x y.

Lemma subR_eq x y z : (x - z = y) <-> (x = y + z).
Proof.
split.
{ by move<-; rewrite /Rminus Rplus_assoc (Rplus_comm _ z) addRN Rplus_0_r. }
by move->; rewrite /Rminus Rplus_assoc addRN Rplus_0_r.
Qed.

Lemma subR_eq0 x y : (x - y = 0) <-> (x = y).
Proof. by rewrite subR_eq Rplus_0_l. Qed.

Lemma addR_eq0 x y : (x + y = 0) <-> (x = - y).
Proof. by rewrite -[y in LHS]oppRK subR_eq0. Qed.

Lemma eqR_opp x y : (- x = - y) <-> (x = y).
Proof.
split.
{ by move=> Hopp; rewrite -[LHS]oppRK -[RHS]oppRK Hopp. }
by move->.
Qed.

Lemma eqR_oppLR x y : (- x = y) <-> (x = - y).
Proof.
split.
{ by move<-; rewrite oppRK. }
by move->; rewrite oppRK.
Qed.

(** Support results about [pow] *)

Lemma pow_opp r m : (-r) ^ m = (-1) ^ m * r ^ m.
Proof.
by rewrite -[- r]Rmult_1_l -Ropp_mult_distr_r -pow_mult Ropp_mult_distr_l.
Qed.

Lemma pow_muln r m1 m2 : r ^ (m1 * m2) = (r ^ m1) ^ m2.
Proof (Rfunctions.pow_mult r m1 m2).
