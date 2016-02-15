(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div choice fintype.
From mathcomp Require Import finfun bigop prime binomial ssralg finset fingroup finalg matrix.
Require Import Reals Fourier.
Require Import Reals_ext Rssr log2 Rbigop proba channel.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope proba_scope.
Local Open Scope channel_scope.

(** * Definition of a channel code *)

Section code_definition.

(** A code is an index set
   (or set of codewords) M with an encoding and a decoding function. *)

Variables A B M : finType.
Variable n : nat.

Local Open Scope ring_scope.

Definition encT := {ffun M -> 'rV[A]_n}.
Definition decT := {ffun 'rV[B]_n -> option M}.

Record code := mkCode { enc : encT ; dec : decT }.

Definition CodeRate (c : code) := (log (INR #| M |) / INR n)%R.

(** Probability of error given that the codeword m was sent: *)

Definition ErrRateCond (W : `Ch_1(A, B)) c m :=
  Pr (W ``^ n (| enc c m)) [set tb | dec c tb != Some m].

Local Notation "e( W , c )" := (ErrRateCond W c) (at level 50).

(** Average probability of error: *)

Definition CodeErrRate (W : `Ch_1(A, B)) c :=
  (1 / INR #| M | * \rsum_(m in M) e(W, c) m)%R.

Local Notation "echa( W , c )" := (CodeErrRate W c) (at level 50).

Lemma echa_pos (HM : (0 < #| M |)%nat) W (c : code) : 0 <= echa(W , c).
Proof.
apply Rmult_le_pos.
- apply Rle_mult_inv_pos.
  + fourier.
  + apply lt_0_INR; by apply/ltP.
- apply: Rle_big_0_P_g => j _.
  apply: Rle_big_0_P_g => k Hk /=.
  by apply DMC_nonneg.
Qed.

Lemma echa1 (HM : (0 < #| M |)%nat) W (c : code) : echa(W , c) <= 1.
Proof.
rewrite /CodeErrRate /Rdiv Rmult_1_l.
apply (Rmult_le_reg_l (INR #|M|)); first by apply lt_0_INR; apply/ltP.
rewrite mulRA Rinv_r; last by apply nesym, Rlt_not_eq, lt_0_INR; apply/ltP.
rewrite Rmult_1_l -iter_Rplus_Rmult -big_const.
apply: Rle_big_P_f_g => m _.
apply Pr_1.
Qed.

End code_definition.

Notation "e( W , c )" := (ErrRateCond W c) (at level 50) : channel_code_scope.

Notation "echa( W , c )" := (CodeErrRate W c) (at level 50) : channel_code_scope.

(** Definition of the set of (code) rates (unit: bits per transmission): *)

Record CodeRateType := mkCodeRateType {
  rate :> R ;
  _ : exists n d, (0 < n)%nat /\ (0 < d)%nat /\ rate = log (INR n) / INR d }.
