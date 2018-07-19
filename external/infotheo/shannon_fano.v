From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq.
From mathcomp Require Import finfun choice fintype tuple bigop finset path.
From mathcomp Require Import ssralg fingroup zmodp poly ssrnum.
Require Import Reals Fourier.
Require Import ssrR logb Reals_ext Rbigop ssr_ext proba entropy kraft.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope R_scope.

(* TODO: move? *)
Definition ceil (r : R) : Z := if frac_part r == 0 then Int_part r else up r.

(* TODO: move? *)
Definition floor : R -> Z := Int_part.

(* TODO: move? *)
Lemma floorP (r : R) : r - 1 < IZR (floor r) <= r.
Proof. rewrite /floor; case: (base_Int_part r) => ? ?; split=> //; fourier. Qed.

(* TODO: move? *)
Lemma ceilP (r : R) : r <= IZR (ceil r) < r + 1.
Proof.
rewrite /ceil; case: ifPn => [|] /eqP r0.
  rewrite frac_Int_part //; split; fourier.
case: (floorP r); rewrite /floor => H1 /Rle_lt_or_eq_dec[] H2.
  rewrite up_Int_part plus_IZR; split; fourier.
exfalso; apply/r0/eqP; rewrite subR_eq0; by apply/eqP.
Qed.

(* TODO: move? *)
Lemma leR0ceil x : 0 <= x -> (0 <= ceil x)%Z.
Proof. move=> ?; case: (ceilP x) => K _; exact/le_IZR/(leR_trans _ K). Qed.

(* TODO: move? *)
Lemma leR_wiexpn2l x :
  0 <= x -> x <= 1 -> {homo (pow x) : m n / (n <= m)%nat >-> m <= n}.
Proof.
move/leRP; rewrite le0R => /orP[/eqP -> _ m n|/ltRP x0 x1 m n /leP nm].
  case: n => [|n nm].
    case: m => [_ |m _]; first exact/leRR.
    by rewrite pow_ne_zero.
  rewrite pow_ne_zero; last by case: m nm.
  rewrite pow_ne_zero //; exact/leRR.
apply invR_le => //.
exact/pow_gt0.
exact/pow_gt0.
rewrite -expRV; last exact/eqP/gtR_eqF.
rewrite -expRV; last exact/eqP/gtR_eqF.
apply Rle_pow => //.
rewrite -invR1; apply leR_inv => //; exact/ltRP.
Qed.

(* TODO: move? *)
Lemma leR_weexpn2l x :
  1 <= x -> {homo (pow x) : m n / (m <= n)%nat >-> m <= n}.
Proof. move=> x1 m n /leP nm; exact/Rle_pow. Qed.

(* TODO: move up? *)
Reserved Notation "n %:R" (at level 2, left associativity, format "n %:R").
Local Notation "n %:R" := (INR n).

(* NB(rei): redefine kraft_cond in R instead of with an rcfType *)
(* TODO: use mathcomp.analysis? or build an ad-hoc interface to bridge R and rcfType as a temporary fix? *)
Definition kraft_condR (T : finType) (sizes : seq nat) :=
  let n := size sizes in
  (\rsum_(i < n) #|T|%:R^-(nth O sizes i) <= (1 : R))%R.

Local Open Scope proba_scope.

Module Encoding.
Record t (A T : finType) := mk {
  f :> {ffun A -> seq T};
  f_inj : injective f }.
End Encoding.
Coercion encoding_coercion (A T : finType) (c : Encoding.t A T) : {ffun A -> seq T} :=
 let: @Encoding.mk _ _ f _ := c in f.

Section shannon_fano_def.

Variables (A T : finType) (P : {dist A}).

Definition is_shannon_fano (f : Encoding.t A T) :=
  forall s, size (f s) = Z.abs_nat (ceil (Log (INR #|T|) (1 / P s)%R)).

End shannon_fano_def.

Section shannon_fano_is_kraft.

Variables (A : finType) (P : {dist A}).
Hypothesis Pr_pos : forall s, P s != 0.

Let a : A. by move/card_gt0P: (dist_domain_not_empty P) => /sigW [i]. Qed.

Variable t' : nat.
Let t := t'.+2.
Let T := [finType of 'I_t].
Variable (f : Encoding.t A T).

Let sizes := [seq (size \o f) a| a in A].
Lemma shannon_fano_is_kraft : is_shannon_fano P f -> kraft_condR T sizes.
Proof.
move=> H.
rewrite /kraft_condR -(pmf1 P).
rewrite /sizes size_map.
rewrite (eq_bigr (fun i:'I_(size(enum A)) => #|'I_t|%:R ^- size (f (nth a (enum A) i)))); last first.
  move=> i _; by rewrite /= (nth_map a).
rewrite -(big_mkord xpredT (fun i => #|T|%:R ^- size (f (nth a (enum A) i)))).
rewrite -(big_nth a xpredT (fun i => #|'I_t|%:R ^- size (f i))).
rewrite enumT.
apply ler_rsum => i _.
rewrite H.
have Pi0 : 0 < P i by apply/ltRP; rewrite lt0R Pr_pos; exact/leRP/dist_ge0.
apply (@leR_trans (Exp #|T|%:R (- Log #|T|%:R (1 / P i)))); last first.
  rewrite div1R LogV //.
  rewrite oppRK LogK //; first exact/leRR.
  by apply/ltRP; rewrite (_ : 1 = 1%:R) // ltR_nat card_ord.
rewrite pow_Exp; last by apply ltR0n; rewrite card_ord.
rewrite Exp_Ropp.
apply/leR_inv/Exp_le_increasing => //.
  by apply/ltRP; rewrite (_ : 1 = 1%:R) // ltR_nat card_ord.
rewrite INR_Zabs_nat; last first.
  case/boolP : (P i == 1) => [/eqP ->|Pj1].
    by rewrite divR1 Log_1 /ceil fp_R0 eqxx /=; apply/Int_part_pos/leRR.
  apply/leR0ceil/ltRW/ltR0Log.
  by apply/ltRP; rewrite (_ : 1 = 1%:R) // ltR_nat card_ord.
  rewrite div1R.
  apply/ltRP; rewrite invR_gt1 // ltR_neqAle Pj1 /=; exact/leRP/dist_max.
by set x := Log _ _; case: (ceilP x).
Qed.

End shannon_fano_is_kraft.

Section average_length.

Variables (A T : finType) (P : {dist A}).
Variable f : {ffun A -> seq T}. (* encoding function *)

Definition average := \rsum_(x in A) P x * (size (f x))%:R.

End average_length.

Section shannon_fano_suboptimal.

Variable A : finType.
Variable P : {dist A}.
Hypothesis Pr_pos : forall s, P s != 0.

Let T := [finType of 'I_2].
Variable f : Encoding.t A T.

Local Open Scope entropy_scope.

Lemma shannon_fano_average_entropy : is_shannon_fano P f ->
  average P f < `H P  + 1.
Proof.
move=> H; rewrite /average.
apply (@ltR_leR_trans (\rsum_(x in A) P x * (- Log (INR #|T|) (P x) + 1))).
  apply ltR_rsum; [exact: dist_domain_not_empty|move=> i].
  apply ltR_pmul2l.
    apply/ltRP; rewrite lt0R Pr_pos /=; exact/leRP/dist_ge0.
  rewrite H.
  rewrite (_ : INR #|T| = 2) // ?card_ord // -!/(log _).
  set x := log _; case: (ceilP x) => _ Hx.
  have Pi0 : 0 < P i by apply/ltRP; rewrite lt0R Pr_pos /=; exact/leRP/dist_ge0.
  rewrite INR_Zabs_nat; last first.
    apply/leR0ceil.
    rewrite /x div1R /log LogV //.
    apply oppR_ge0.
    rewrite -(Log_1 2); apply Log_increasing_le => //.
    exact/dist_max.
  case: (ceilP x) => _.
  by rewrite -LogV // -/(log _) -(div1R _) /x.
evar (h : A -> R).
rewrite (eq_bigr h); last first.
  move=> i _; rewrite mulRDr mulR1 mulRN  /h; reflexivity.
rewrite {}/h big_split /=; apply leR_add.
  apply Req_le.
  rewrite /entropy (big_morph _ morph_Ropp oppR0); apply eq_bigr => i _.
  by rewrite card_ord (_ : INR 2 = 2).
rewrite pmf1; exact/leRR.
Qed.

End shannon_fano_suboptimal.

(* wip *)
Section kraft_code_is_shannon_fano.

Variables (A : finType).
Variable P : {dist A}.

Variable (t' : nat).
Let n := #|A|.-1.+1.
Let t := t'.+2.
Let T := [finType of 'I_t].
Variable l : seq nat.
Hypothesis l_n : size l = n.
Hypothesis sorted_l : sorted leq l.

Let C := ACode t' l_n sorted_l.

Lemma f_inj : injective [ffun a : A => nth [::] C (enum_rank a)].
Proof.
move=> x y.
rewrite !ffunE => /eqP xy.
rewrite -(enum_rankK x) -(enum_rankK y); congr enum_val.
apply/ord_inj/eqP.
rewrite -(@nth_uniq _ [::] C (enum_rank x) (enum_rank y)) //; last first.
  rewrite /C /ACode /= /acode map_inj_uniq //.
  exact/enum_uniq.
  exact/injective_sigma.
rewrite /C /ACode /= /acode size_map size_enum_ord prednK //.
exact: (dist_domain_not_empty P).
rewrite /C /ACode /= /acode size_map size_enum_ord prednK //.
exact: (dist_domain_not_empty P).
Qed.

Let f := Encoding.mk f_inj.

End kraft_code_is_shannon_fano.
