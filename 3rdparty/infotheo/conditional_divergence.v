(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice fintype.
From mathcomp Require Import tuple finfun bigop prime binomial ssralg finset fingroup finalg matrix.
Require Import Reals Fourier Rpower.
Require Import Reals_ext ssr_ext ssralg_ext Rssr log2 Rbigop ln_facts.
Require Import num_occ proba entropy channel divergence types jtypes.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Local Open Scope channel_scope.
Local Open Scope divergence_scope.
Local Open Scope num_occ_scope.
Local Open Scope types_scope.

Section condition_equivalence.

Variables A B : finType.
Variables V W : `Ch_1(A, B).
Variable P : dist A.

Definition cdom_by := forall a, P a != 0 -> (V a) << (W a).

Lemma condition_equivalence : (`J(P , V) << `J(P , W)) <-> cdom_by.
Proof.
rewrite /dom_by; split=> H.
- move=> a p_not_0 b; move: (H (a, b)).
  rewrite /JointDistd /= /JointDist.f /= => H0 H1.
  rewrite H1 mul0R in H0.
  move/(_ (refl_equal _)) in H0.
  case/Rmult_integral : H0 => // H0.
  by rewrite H0 eqxx in p_not_0.
- case=> a p_not_0 b; move: {H}(H a) => H.
  rewrite /JointDistd /= /JointDist.f /=.
  case/boolP : (P a == 0) => [/eqP -> | H1].
    by rewrite mulR0.
  move: {H}(H H1) => ->.
  by rewrite mul0R.
  case/Rmult_integral : b => // b.
  by rewrite b eqxx in H1.
Qed.

End condition_equivalence.

Notation "V '<<' W '|' P" := (cdom_by V W P) (at level 5, P at next level) : channel_scope.

Notation "V '<<b' W '|' P" := ([forall a, (P a != 0) ==> (V a) <<b (W a)])
  (at level 5) : channel_scope.

Section joint_dom_sect.

Variable A B : finType.
Variables V W : `Ch_1(A, B).
Variable P : dist A.

Lemma joint_dom : V << W | P -> dom_by (`J(P, V)) (`J(P, W)) (*NB: notation issue*).
Proof.
move => V_dom_by_W => ab /= Hab.
case: (Rle_lt_or_eq_dec _ _ (Rle0f P ab.1)) => Hab1.
- rewrite /JointDist.f V_dom_by_W.
  + by rewrite mul0R.
  + case/Rmult_integral : Hab => Hab.
    * apply/eqP; by apply nesym, Rlt_not_eq.
    * move: Hab1; rewrite Hab; by move/Rlt_irrefl.
  + case/Rmult_integral : Hab => // Hab.
    move/Rlt_not_eq : Hab1; by rewrite Hab.
- by rewrite /JointDist.f -Hab1 mulR0.
Qed.

End joint_dom_sect.

Section conditional_divergence_def.

Variables A B : finType.
Variables V W : `Ch_1(A, B).
Variable P : dist A.

Definition cdiv := \rsum_(a : A) P a * D(V a || W a).

End conditional_divergence_def.

Notation "'D(' V '||' W '|' P ')'" := (cdiv V W P)
  (at level 50, V, W, P at next level) : divergence_scope.

Section conditional_divergence_prop.

Variables A B : finType.
Variables V W : `Ch_1(A, B).
Variable P : dist A.

Hypothesis V_dom_by_W : V << W | P.

Lemma cdiv_is_div_joint_dist : D(V || W | P) =  D(`J(P , V) || `J(P , W)).
Proof.
rewrite (_ : D(V || W | P) =
  \rsum_(a : A) (\rsum_(b | b \in B) V a b * (log (V a b) - log (W a b)) * P a)); last first.
  apply eq_bigr => a _.
  by rewrite -(big_morph _ (morph_mulRDl _) (mul0R _)) mulRC.
rewrite pair_bigA big_mkcond /=.
apply eq_bigr; case => [] a b /= _.
rewrite /JointDist.f.
case/boolP : (P a == 0) => [/eqP -> | Pneq0]; first by rewrite !mulR0 mul0R.
case/boolP : (V a b == 0) => [/eqP -> | Vneq0]; first by rewrite !mul0R.
case/boolP : (W a b == 0) => [/eqP Weq0| Wneq0].
  contradict Vneq0.
  apply/negP. rewrite negbK. apply/eqP. by apply V_dom_by_W.
rewrite /= !log_mult; first field; apply Rlt_le_neq; by [apply Rle0f | apply/eqP; rewrite eq_sym].
Qed.

Lemma leq0cdiv : 0 <= D(V || W | P).
Proof.
rewrite cdiv_is_div_joint_dist //; apply leq0div.
case=> a b; rewrite /JointDistd /= /JointDist.f /=.
case/boolP : (P a == 0); first by move/eqP => ->; rewrite 2!mulR0.
move=> H1 H2.
apply Rmult_eq_0_compat_r.
apply V_dom_by_W => //.
case (Rmult_integral _ _ H2) => // ?; contradict H1.
by apply/negP/negPn/eqP.
Qed.

Lemma eq0cdiv : D(V || W | P) = 0 <-> `J(P, V) = `J(P, W).
Proof.
rewrite cdiv_is_div_joint_dist.
apply eq0div; case=> a b.
rewrite /JointDistd /= /JointDist.f /= => HW.
apply Rmult_integral in HW; case: HW => Hcase; last by rewrite Hcase mulR0.
case/boolP : (P a == 0) => [/eqP ->|Hcase2]; first by rewrite mulR0.
by apply Rmult_eq_0_compat_r, V_dom_by_W.
Qed.

End conditional_divergence_prop.

Section dmc_cdiv_cond_entropy_sect.

Variable A B : finType.
Variables W : `Ch_1(A, B).
Variable n : nat.
Variable P : P_ n ( A ).
Variable V : P_ n ( A , B ).
Variable ta : 'rV[A]_n.
Variable tb : 'rV[B]_n.

Local Open Scope vec_ext_scope.

Lemma dmc_cdiv_cond_entropy_aux : W ``^ n (tb | ta) =
  \rmul_(a : A) \rmul_(b : B) W a b ^ N(a, b | tuple_of_row ta, tuple_of_row tb).
Proof.
transitivity (\rmul_(a : A) \rmul_(b : B) \rmul_(i < n)
  if (a == ta ``_ i) && (b == tb ``_ i) then W ta ``_ i tb ``_ i else 1).
  rewrite pair_big exchange_big /= /DMC.c; unlock.
  apply eq_bigr => i _.
  rewrite (bigD1 (ta ``_ i, tb ``_ i)) //= 2!eqxx andbT.
  rewrite big1; first by rewrite mulR1.
  case=> a b /=.
  rewrite xpair_eqE negb_and.
  case/orP.
  - by move/negbTE => ->.
  - move/negbTE => ->; by rewrite andbF.
apply eq_bigr => a _; apply eq_bigr => b _.
rewrite num_co_occ_alt -sum1_card.
rewrite (@big_morph _ _ (fun x => W a b ^ x) 1 Rmult O addn) //; last first.
  move=> * /=; by rewrite -pow_add.
rewrite [in RHS]big_mkcond.
apply eq_bigr => i _.
case: ifP.
  case/andP => /eqP Ha /eqP Hb.
  by rewrite inE 2!tnth_mktuple -Ha -Hb 2!eqxx /= mulR1.
move/negbT.
rewrite negb_and inE 2!tnth_mktuple.
case/orP => /negbTE.
  by rewrite eq_sym => ->.
by rewrite andbC eq_sym => ->.
Qed.

Local Close Scope tuple_ext_scope.

Hypothesis W0_V0 : V << W | P.
Hypothesis Hta : tuple_of_row ta \in T_{P}.
Hypothesis HV : V \in \nu^{B}(P).
Hypothesis Htb : tuple_of_row tb \in V.-shell (tuple_of_row ta).
Hypothesis Hn : n != O.

(** Expression of the probability transition matrix of a DMC using
   the conditional divergence and the condition entropy *)

Lemma dmc_cdiv_cond_entropy :
  W ``^ n (tb | ta) = exp2 (- INR n * (D(V || W | P) + `H(V | P))).
Proof.
rewrite dmc_cdiv_cond_entropy_aux cond_entropy_single_sum.
rewrite /cdiv /entropy -big_split /=.
rewrite (big_morph _ (morph_mulRDr _) (mulR0 _)) (big_morph _ morph_exp2_plus exp2_0).
apply eq_bigr => a _.
rewrite (big_morph _ morph_Ropp Ropp_0).
rewrite /div /= -mulRDr mulRA -big_split /=.
rewrite (big_morph _ (morph_mulRDr _) (mulR0 _)) (big_morph _ morph_exp2_plus exp2_0).
apply eq_bigr => b _.
case/boolP : (W a b == 0) => Wab0.
- move/eqP in Wab0; rewrite Wab0.
  case/boolP : (P a == 0) => Pa0.
  - move/eqP in Pa0; rewrite Pa0.
    rewrite mulR0 mul0R exp2_0 -(pow_O 0).
    f_equal.
    move: Htb; rewrite in_set => /forallP/(_ a)/forallP/(_ b)/eqP => ->.
    move: (HV).
    rewrite in_set.
    move/cond_type_equiv/(_ _ Hta a).
    move: Hta; rewrite in_set => /forallP/(_ a)/eqP => Htmp Htmp'.
    rewrite -Htmp' Pa0 in Htmp.
    symmetry in Htmp; case/Rmult_integral : Htmp; last first.
      move=> abs.
      suff : False by done.
      move: abs.
      apply Rinv_neq_0_compat.
      apply not_0_INR; by apply/eqP.
    rewrite (_ : 0 = INR 0) //.
    move/INR_eq.
    move/eqP; rewrite sum_nat_eq0 => /forall_inP/(_ b) => H; apply/eqP; by move: H => ->.
  - move: (W0_V0 Pa0 Wab0) => nullV.
    rewrite nullV.
    suff : N(a, b| tuple_of_row ta, tuple_of_row tb) = 0%nat.
      move=> ->; by rewrite 2!mul0R Ropp_0 addR0 mulR0 exp2_0.
    move: Htb; rewrite in_set => /forallP/(_ a)/forallP/(_ b)/eqP => ->.
    by rewrite jtype_0_jtypef.
- rewrite -{1}(@exp2_log (W a b)); last first.
    apply Rlt_le_neq; first by apply Rle0f.
    move/eqP; apply/negP; by rewrite eqtype.eq_sym.
  rewrite -exp2_pow.
  f_equal.
  rewrite -Ropp_mult_distr_r_reverse -mulRDr mulRA /Rminus addRC addRA Rplus_opp_l add0R Ropp_mult_distr_r_reverse -3!Ropp_mult_distr_l_reverse Ropp_involutive.
  f_equal.
  move: Htb; rewrite in_set => /forallP/(_ a)/forallP/(_ b)/eqP => ->.
  move: (HV).
  rewrite in_set.
  move/cond_type_equiv => /(_ _ Hta a).
  move=> Htmp'.
  move: Hta; rewrite in_set => /forallP/(_ a)/eqP => Htmp.
  rewrite (jtype.c_f V) /=.
  case: ifP.
  - move/eqP => HP.
    rewrite Htmp -Htmp' HP /Rdiv !(mul0R, mulR0).
    move/eqP : HP.
    rewrite sum_nat_eq0.
    move/forallP.
    by move/(_ b)/implyP/(_ Logic.eq_refl)/eqP => ->.
  - move/negP/negP => HP.
    rewrite Htmp Htmp' !mulRA Rinv_r_simpl_m; last by apply not_0_INR; apply/eqP.
    rewrite Rinv_r_simpl_m // -Htmp'.
    apply/eqP.
    move: HP; apply contra.
    move/eqP.
    rewrite (_ : 0 = INR 0) //.
    by move/INR_eq => ->.
Qed.

End dmc_cdiv_cond_entropy_sect.

Section cdiv_spec.

Variables A B : finType.
Variable n : nat.
Variable P : P_ n ( A ).
Variable V : P_ n ( A , B ).
Variable W : `Ch_1*(A, B).
(*Variable ta : n.-tuple A.
Variable tb : n.-tuple B.*)

Definition exp_cdiv :=
  if V <<b W | P
  then exp2 (- INR n * D(V || W | P))
  else 0.

Lemma exp_cdiv_left (H : V << W | P) : exp_cdiv = exp2 (-INR n * D(V || W | P)).
Proof.
rewrite /exp_cdiv.
suff : V <<b W | P by move=> ->.
apply/forallP => a.
apply/implyP => Pa0.
apply/forall_inP => b /eqP Wab.
apply/eqP.
by apply H.
Qed.

End cdiv_spec.

Section dmc_cdiv_cond_entropy_spec_sect.

Variables A B : finType.
Variable W : `Ch_1*(A, B).
Variable n' : nat.
Let n := n'.+1.
Variable P : P_ n ( A ).
Variable V : P_ n ( A , B ).
Variable ta : 'rV[A]_n.
Variable tb : 'rV[B]_n.

Hypothesis Hta : tuple_of_row ta \in T_{P}.
Hypothesis Vctyp : V \in \nu^{B}(P).
Hypothesis Htb : tuple_of_row tb \in V.-shell (tuple_of_row ta).

Lemma dmc_exp_cdiv_cond_entropy :
  W ``^ n (tb | ta) = exp_cdiv P V W * exp2 (- INR n * `H(V | P)).
Proof.
rewrite /exp_cdiv.
case : ifP => Hcase.
- rewrite -exp2_plus -mulRDr.
  apply dmc_cdiv_cond_entropy => // a Pa b /eqP Wab.
  by move: Hcase => /forallP/(_ a)/implyP/(_ Pa)/forallP/(_ b)/implyP/(_ Wab)/eqP.
- rewrite mul0R.
  move: Hcase => /negbT; rewrite negb_forall; case/existsP => a.
  rewrite negb_imply.
  case/andP => Pa.
  rewrite negb_forall_in ; move/existsP ; case => b.
  case/andP=> Wab H.
  rewrite dmc_cdiv_cond_entropy_aux.
  rewrite pair_big /= (bigD1 (a, b)) //=.
  apply Rmult_eq_0_compat_r.
  move/eqP in Wab; rewrite Wab.
  apply pow_i.
  apply/ltP.
  rewrite lt0n.
  move: Htb ; rewrite in_set => /forallP/(_ a)/forallP/(_ b)/eqP ->.
  move: H => /=.
  rewrite (jtype.c_f V) /=.
  move: (Vctyp).
  rewrite in_set.
  move/cond_type_equiv => /(_ _ Hta a) ->.
  move: Hta; rewrite in_set => /forallP/(_ a)/eqP => Htmp.
  case: ifP => Hcase.
    suff : False by done.
    move/eqP : Pa; apply.
    rewrite Htmp.
    move/eqP : Hcase => ->.
    by rewrite /Rdiv mul0R.
  apply contra.
  move/eqP => ->.
  by rewrite /Rdiv mul0R.
Qed.

End dmc_cdiv_cond_entropy_spec_sect.
