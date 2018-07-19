(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq.
From mathcomp Require Import choice fintype finfun bigop finset.
Require Import Reals Fourier.
Require Import ssrR Reals_ext Ranalysis_ext logb ln_facts bigop_ext Rbigop.

(** * The log-sum Inequality *)

Local Open Scope reals_ext_scope.

Local Notation "'\rsum_{' C '}' f" :=
  (\rsum_(a | a \in C) f a) (at level 10, format "\rsum_{ C }  f").

Definition log_sum_stmt {A : finType} (C : {set A}) (f g : A -> R+) :=
  f << g ->
  \rsum_{C} f * log (\rsum_{C} f / \rsum_{C} g) <= \rsum_(a | a \in C) f a * log (f a / g a).

Lemma log_sum1 {A : finType} (C : {set A}) (f g : A -> R+) :
  (forall a, a \in C -> 0 < f a) -> log_sum_stmt C f g.
Proof.
move=> fspos fg.
case/boolP : (C == set0) => [ /eqP -> | Hc].
  rewrite !big_set0 mul0R; exact/leRR.
have gspos : forall a, a \in C -> 0 < g a.
  move=> a a_C.
  case/Rle_lt_or_eq_dec : ((pos_f_ge0 g) a) => // abs; symmetry in abs; apply fg in abs.
  move: (fspos _ a_C); by rewrite abs; move/ltRR.
have Fnot0 : \rsum_{ C } f != 0.
  apply/eqP => /prsumr_eq0P abs.
  case/set0Pn : Hc => a aC.
  move: (fspos _ aC); rewrite abs //; last by move=> b bC; apply/ltRW/fspos.
  by move/ltRR.
have Gnot0 : \rsum_{ C } g != 0.
  apply/eqP => /prsumr_eq0P abs.
  case/set0Pn : Hc => a aC.
  move: (gspos _ aC); rewrite abs //; last by move=> b bC; apply/ltRW/gspos.
  by move/ltRR.
wlog : Fnot0 g Gnot0 fg gspos / \rsum_{ C } f = \rsum_{ C } g.
  move=> Hwlog.
  set k := \rsum_{ C } f / \rsum_{ C } g.
  have Fspos : 0 < \rsum_{ C } f.
    suff Fpos : 0 <= \rsum_{ C } f by apply/ltRP; rewrite lt0R Fnot0; exact/leRP.
    apply: rsumr_ge0 => ? ?; exact/ltRW/fspos.
  have Gspos : 0 < \rsum_{ C } g.
    suff Gpocs : 0 <= \rsum_{ C } g by apply/ltRP; rewrite lt0R Gnot0; exact/leRP.
    apply: rsumr_ge0 => ? ?; exact/ltRW/gspos.
  have kspos : 0 < k by apply Rlt_mult_inv_pos.
  have kg_pos : forall a, 0 <= k * g a.
    move=> a; apply mulR_ge0; by [apply ltRW | apply pos_f_ge0].
  have kabs_con : forall a, k * g a = 0 -> f a = 0.
    move=> a /eqP; rewrite mulR_eq0 => /orP[/eqP Hk| /eqP/fg //].
    rewrite Hk in kspos; by move/ltRR : kspos.
  have kgspos : forall a, a \in C -> 0 < k * g a.
    move=> a a_C; apply mulR_gt0 => //; by apply gspos.
  have Hkg : \rsum_(a | a \in C) k * g a = \rsum_{C} f.
    by rewrite -big_distrr /= /k /Rdiv -mulRA mulRC mulVR // mul1R.
  have Htmp : \rsum_{ C } {| pos_f := fun x : A => k * g x; pos_f_ge0 := kg_pos |} != 0.
    by rewrite /= Hkg.
  symmetry in Hkg.
  move: {Hwlog}(Hwlog Fnot0 (@mkPosFun _ (fun x => (k * g x)) kg_pos) Htmp kabs_con kgspos Hkg) => /= Hwlog.
  rewrite Hkg {1}/Rdiv mulRV // /log Log_1 mulR0 in Hwlog.
  set rhs := \rsum_(_ | _) _ in Hwlog.
  rewrite (_ : rhs = \rsum_(a | a \in C) (f a * log (f a / g a) - f a * log k)) in Hwlog; last first.
    rewrite /rhs.
    apply eq_bigr => a a_C.
    rewrite /Rdiv /log LogM; last 2 first.
      exact/fspos.
      apply/invR_gt0/mulR_gt0 => //; exact/gspos.
    rewrite LogV; last first.
      apply mulR_gt0 => //; exact: gspos.
    rewrite LogM //; last exact: gspos.
    rewrite LogM //; last 2 first.
      exact/fspos.
      apply invR_gt0; by [apply gspos | apply fspos].
    rewrite LogV; by [field | apply gspos].
  rewrite big_split /= -(big_morph _ morph_Ropp oppR0) -big_distrl /= in Hwlog.
  have : forall a b, 0 <= a + - b -> b <= a by move=> *; fourier.
  by apply.
move=> Htmp; rewrite Htmp.
rewrite /Rdiv mulRV; last by rewrite -Htmp.
rewrite /log Log_1 mulR0.
suff : 0 <= \rsum_(a | a \in C) f a * ln (f a / g a).
  move=> H.
  rewrite /log /Rdiv.
  set rhs := \rsum_( _ | _ ) _.
  have -> : rhs = \rsum_(H | H \in C) (f H * (ln (f H / g H))) / ln 2.
    rewrite /rhs.
    apply eq_bigr => a a_C; by rewrite /Rdiv -mulRA.
  rewrite -big_distrl /=.
  apply mulR_ge0 => //; exact/ltRW/invR_gt0.
apply (@leR_trans (\rsum_(a | a \in C) f a * (1 - g a / f a))).
  apply (@leR_trans (\rsum_(a | a \in C) (f a - g a))).
    rewrite big_split /= -(big_morph _ morph_Ropp oppR0); fourier.
  apply Req_le, eq_bigr => a a_C.
  rewrite Rmult_minus_distr_l mulR1.
  case: (Req_EM_T (g a) 0).
    move=> ->; by rewrite div0R mulR0.
  move=> ga_not_0.
  field; exact/gtR_eqF/(fspos _ a_C).
apply: ler_rsum => a C_a.
apply leR_wpmul2l; first exact/ltRW/fspos.
rewrite -[X in _ <= X]oppRK leR_oppr -ln_Rinv; last first.
  apply Rlt_mult_inv_pos; by [apply fspos | apply gspos].
rewrite invRM; last 2 first.
  exact/gtR_eqF/(fspos _ C_a).
  exact/eqP/invR_neq0/eqP/gtR_eqF/(gspos _ C_a).
rewrite invRK; last exact/gtR_eqF/(gspos _ C_a).
rewrite mulRC.
apply: leR_trans.
  apply ln_id_cmp.
  apply Rlt_mult_inv_pos; by [apply gspos | apply fspos].
apply Req_le.
field; exact/gtR_eqF/(fspos _ C_a).
Qed.

Lemma log_sum {A : finType} (C : {set A}) (f g : A -> R+) :
  log_sum_stmt C f g.
Proof.
move=> fg.
set D := [set a | (a \in C) && (f a != 0)].
suff : \rsum_{D} f * log (\rsum_{D} f / \rsum_{D} g) <=
       \rsum_(a | a \in D) f a * log (f a / g a).
  move=> H.
  set D' := [set a in C | f a == 0].
  have DUD' : C = D :|: D'.
    apply/setP => a.
    move Hlhs : (a \in C) => lhs.
    destruct lhs => //.
      symmetry.
      rewrite in_setU /C1 /C1 !in_set Hlhs /=.
      by destruct (f a == 0).
    by rewrite in_setU in_set Hlhs /= /C1 in_set Hlhs.
  have DID' : [disjoint D & D'].
    rewrite -setI_eq0.
    apply/eqP/setP => a.
    rewrite in_set0 /C1 /C1 in_setI !in_set.
    destruct (a \in C) => //=; by rewrite andNb.
  have H1 : \rsum_{C} f = \rsum_{D} f.
    rewrite setUC in DUD'.
    rewrite DUD' (big_union _ f DID') /=.
    rewrite (_ : \rsum_{D'} f = \rsum_(a | a \in D') 0); last first.
      apply eq_bigr => a.
      rewrite /D' in_set.
      by case/andP => _ /eqP.
    by rewrite big_const iter_addR mulR0 add0R.
  rewrite -H1 in H.
  have pos_F : 0 <= \rsum_{C} f.
    apply rsumr_ge0 => ? ?; exact: pos_f_ge0.
  apply (@leR_trans (\rsum_{C} f * log (\rsum_{C} f / \rsum_{D} g))).
    case/Rle_lt_or_eq_dec : pos_F => pos_F; last first.
      rewrite -pos_F !mul0R; exact/leRR.
    have H2 : 0 <= \rsum_(a | a \in D) g a.
      apply: rsumr_ge0 => ? _; exact: pos_f_ge0.
    case/Rle_lt_or_eq_dec : H2 => H2; last first.
      have : 0 = \rsum_{D} f.
        transitivity (\rsum_(a | a \in D) 0).
          by rewrite big_const iter_addR mulR0.
        apply eq_bigr => a a_C1.
        rewrite fg // (proj1 (@prsumr_eq0P _ (mem D) _ _)) // => ? ?; exact/pos_f_ge0.
      move=> abs; rewrite -abs in H1; rewrite H1 in pos_F.
      by move/ltRR : pos_F.
    have H3 : 0 < \rsum_(a | a \in C) g a.
      rewrite setUC in DUD'.
      rewrite DUD' (big_union _ g DID') /=.
      apply addR_gt0wr => //.
      apply: rsumr_ge0 => *; exact/pos_f_ge0.
    apply/(leR_wpmul2l (ltRW pos_F))/Log_increasing_le => //.
      apply Rlt_mult_inv_pos => //; by rewrite -HG.
    apply/(leR_wpmul2l (ltRW pos_F))/leR_inv => //.
    rewrite setUC in DUD'.
    rewrite DUD' (big_union _ g DID') /= -[X in X <= _]add0R; apply leR_add2r.
    apply: rsumr_ge0 => ? ?; exact/pos_f_ge0.
  apply: (leR_trans H).
  rewrite setUC in DUD'.
  rewrite DUD' (big_union _ (fun a => f a * log (f a / g a)) DID') /=.
  rewrite (_ : \rsum_(_ | _ \in D') _ = 0); last first.
    transitivity (\rsum_(a | a \in D') 0).
      apply eq_bigr => a.
      rewrite /D' in_set => /andP[a_C /eqP ->]; by rewrite mul0R.
    by rewrite big_const iter_addR mulR0.
  rewrite add0R; exact/leRR.
apply log_sum1 => // a.
rewrite /C1 in_set.
case/andP => a_C fa_not_0.
case/Rle_lt_or_eq_dec: (pos_f_ge0 f a) => // abs.
by rewrite abs eqxx in fa_not_0.
Qed.
