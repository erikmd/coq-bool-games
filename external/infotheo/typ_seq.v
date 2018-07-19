(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype finfun bigop prime binomial ssralg.
From mathcomp Require Import finset fingroup finalg matrix.
Require Import Reals Fourier.
Require Import ssrR Reals_ext logb Rbigop.
Require Import proba entropy aep.

(** * Typical Sequences *)

Reserved Notation "'`TS'".

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

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
case/andP. move/leRP => H2. move/leRP => H3.
apply/andP; split; apply/leRP.
- apply/(leR_trans _ H2)/Exp_le_increasing => //.
  rewrite !mulNR.
  rewrite leR_oppr oppRK; apply leR_wpmul2l; first exact/leR0n.
  apply leR_add2l, Rdiv_le => //; fourier.
- eapply Rle_trans; first by apply H3.
  apply Exp_le_increasing => //.
  rewrite !mulNR.
  rewrite leR_oppr oppRK; apply leR_wpmul2l; first exact/leR0n.
  apply leR_add2l; rewrite leR_oppr oppRK; apply Rdiv_le => //; fourier.
Qed.

Section typ_seq_prop.

Variable A : finType.
Variable P : dist A.
Variable epsilon : R.
Variable n : nat.

(** The total number of typical sequences is upper-bounded by 2^(k*(H P + e)): *)

Lemma TS_sup : INR #| `TS P n epsilon | <= exp2 (INR n * (`H P + epsilon)).
Proof.
suff Htmp : INR #| `TS P n epsilon | * exp2 (- INR n * (`H P + epsilon)) <b= 1.
  apply/leRP; rewrite -(mulR1 (exp2 _)) mulRC -leR_pdivr_mulr //.
  by rewrite /Rdiv -exp2_Ropp -mulNR.
rewrite -(pmf1 (P `^ n)).
rewrite (_ : _ * _ = \rsum_(x in `TS P n epsilon) (exp2 (- INR n * (`H P + epsilon)))); last first.
  by rewrite big_const iter_addR.
apply/leRP/ler_rsum_l => //=.
- move=> i; rewrite inE; by case/andP => /leRP.
- move=> a _; exact/dist_ge0.
Qed.

Lemma typ_seq_definition_equiv x : x \in `TS P n epsilon ->
  exp2 (- INR n * (`H P + epsilon)) <= P `^ n x <= exp2 (- INR n * (`H P - epsilon)).
Proof.
rewrite inE /typ_seq.
case/andP => H1 H2; split; by apply/leRP.
Qed.

Lemma typ_seq_definition_equiv2 x : x \in `TS P n.+1 epsilon ->
  `H P - epsilon <= - (1 / INR n.+1) * log (P `^ n.+1 x) <= `H P + epsilon.
Proof.
rewrite inE /typ_seq.
case/andP => H1 H2; split;
  apply/leRP; rewrite -(leR_pmul2l' (INR n.+1)) ?ltR0n' //;
  rewrite div1R mulRA mulRN mulRV ?INR_eq0' // mulN1R; apply/leRP.
- rewrite leR_oppr.
  apply/(@Exp_le_inv 2) => //.
  rewrite LogK //; last by apply/(ltR_leR_trans (exp2_gt0 _)); apply/leRP: H1.
  apply/leRP; by rewrite -mulNR.
- rewrite leR_oppl.
  apply/(@Exp_le_inv 2) => //.
  rewrite LogK //; last by apply/(ltR_leR_trans (exp2_gt0 _)); apply/leRP: H1.
  apply/leRP; by rewrite -mulNR.
Qed.

End typ_seq_prop.

Section typ_seq_more_prop.

Variable A : finType.
Variable P : dist A.
Variable epsilon : R.
Variable n : nat.

Hypothesis He : 0 < epsilon.

Lemma Pr_TS_1 : aep_bound P epsilon <= INR n.+1 -> 1 - epsilon <= Pr (P `^ n.+1) (`TS P n.+1 epsilon).
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
  case/andP : LHS => /leRP LHS _.
  exact/esym/ltRP/(ltR_leR_trans (exp2_gt0 _) LHS).
set p := [set _ | _].
move: (Pr_cplt (P `^ n.+1) p) => Htmp.
rewrite Pr_to_cplt.
suff ? : Pr (P `^ n.+1) (~: p) <= epsilon by apply leR_add2l; rewrite leR_oppl oppRK.
have -> : Pr P `^ n.+1 (~: p) =
  Pr P `^ n.+1 [set x | P `^ n.+1 x == 0]
  +
  Pr P `^ n.+1 [set x | (0 <b P `^ n.+1 x) && (`| - (1 / INR n.+1) * log (P `^ n.+1 x) - `H P | >b epsilon) ].
  have H1 : ~: p =
    [set x | P `^ n.+1 x == 0 ] :|:
    [set x | (0 <b P `^ n.+1 x) &&
               (`| - (1 / INR n.+1) * log (P `^ n.+1 x) - `H P | >b epsilon)].
    apply/setP => i.
    rewrite !inE.
    rewrite negb_and.
    rewrite orbC.
    move LHS : (_ || _) => [|].
    + case/orP : LHS => LHS.
      * apply/esym/orP; left.
        rewrite -leRNgt' in LHS; move/leRP in LHS.
        apply/eqP; rewrite eqR_le; split => //; exact: dist_ge0.
      * rewrite /typ_seq negb_and in LHS.
        case/orP : LHS => LHS.
        - apply/esym.
          case/boolP : (P `^ n.+1 i == 0) => /= H1; first by [].
          rewrite lt0R H1 /=; apply/andP; split; first exact/leRP/dist_ge0.
          rewrite -ltRNge' in LHS; move/ltRP in LHS.
          apply (@Log_increasing 2) in LHS => //; last first.
            apply/ltRP; rewrite lt0R H1 /=; exact/leRP/dist_ge0.
          move/ltRP : LHS.
          rewrite /exp2 ExpK // mulRC mulRN -mulNR -ltR_pdivr_mulr; last exact/ltR0n.
          rewrite /Rdiv mulRC => /ltRP; rewrite ltR_oppr => /ltRP.
          rewrite mulNR -ltR_subRL' => LHS.
          rewrite mul1R geR0_norm //.
          by move/ltRP : LHS; move/(ltR_trans He)/ltRW.
        - rewrite leRNgt' negbK in LHS.
          apply/esym/orP; right.
          move/ltRP in LHS.
          apply/andP; split; first exact/ltRP/(ltR_trans (exp2_gt0 _) LHS).
          apply (@Log_increasing 2) in LHS => //.
          move: LHS; rewrite /exp2 ExpK // => /ltRP.
          rewrite mulRC mulRN -mulNR -ltR_pdivl_mulr; last exact/ltR0n.
          rewrite oppRD oppRK => LHS.
          have H2 : forall a b c, - a + b < c -> - c - a < - b by move=> *; fourier.
          move/ltRP/H2 in LHS.
          rewrite div1R mulRC mulRN -/(Rdiv _ _) leR0_norm.
          + apply/ltRP; by rewrite ltR_oppr.
          + apply: (leR_trans (ltRW LHS)); by fourier.
      * move/negbT : LHS.
        rewrite negb_or 2!negbK /typ_seq => /andP[H1 /andP[/leRP H2 /leRP H3]].
        apply/esym/negbTE.
        rewrite negb_or; apply/andP; split; first exact/eqP/gtR_eqF/ltRP.
        rewrite negb_and H1 /= -leRNgt'.
        apply (@Log_increasing_le 2) in H2 => //.
        rewrite /exp2 ExpK // in H2.
        move/leRP : H2.
        rewrite mulRC mulRN -mulNR -leR_pdivl_mulr ?oppRD; last exact/ltR0n.
        move/leRP => H2.
        have /(_ _ _ _ H2) {H2}H2 : forall a b c, - a + - b <= c -> - c - a <= b.
          by move=> *; fourier.
        apply (@Log_increasing_le 2) in H3 => //; last exact/ltRP.
        rewrite /exp2 ExpK // in H3.
        move/leRP : H3.
        rewrite mulRC mulRN -mulNR -leR_pdivr_mulr; last exact/ltR0n.
        rewrite oppRD oppRK div1R mulRC mulRN => /leRP H3.
        have /(_ _ _ _ H3) {H3}H3 : forall a b c, a <= - c + b -> - b <= - a - c.
          by move=> *; fourier.
        rewrite leR_Rabsl; apply/andP; split; exact/leRP.
  rewrite H1 Pr_union_disj; last first.
    apply disjoint_setI0.
    rewrite disjoints_subset.
    apply/subsetP => i.
    rewrite !inE /= => Hi.
    rewrite negb_and.
    by rewrite (eqP Hi) ltRR'.
  congr (_ + _); apply Pr_ext => i /=; by rewrite !inE.
have -> : Pr P `^ n.+1 [set x | P `^ n.+1 x == 0] = 0.
  rewrite /Pr.
  transitivity (\rsum_(a in 'rV[A]_n.+1 | P `^ n.+1 a == 0) 0).
    apply eq_big => // i.
      by rewrite !inE.
    by rewrite inE => /eqP.
  by rewrite big_const /= iter_addR mulR0.
rewrite add0R.
apply/(leR_trans _ (@aep _ P n _ He k0_k))/Pr_incl/subsetP => /= t.
rewrite inE /=.
case/andP => H2 H3.
rewrite inE H2 /=.
apply/ltRW'; by rewrite mulRN -mulNR.
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
  split; by [apply Pr_TS_1 | apply Pr_1].
have H2 : (forall x, x \in `TS P n.+1 epsilon ->
  exp2 (- INR n.+1 * (`H P + epsilon)) <= P `^ n.+1 x <= exp2 (- INR n.+1 * (`H P - epsilon))).
  by move=> x; rewrite inE /typ_seq => /andP[/leRP ? /leRP].
move: (wolfowitz (exp2_gt0 _) (exp2_gt0 _) H1 H2).
rewrite mulNR exp2_Ropp {1}/Rdiv invRK; last exact/nesym/ltR_eqF.
by case.
Qed.

End typ_seq_more_prop.
