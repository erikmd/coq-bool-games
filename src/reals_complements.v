Require Import Reals.
From mathcomp Require Import ssreflect.

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
