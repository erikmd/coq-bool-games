Require Import Reals Psatz.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div choice fintype tuple finfun bigop.
From mathcomp Require Import prime binomial ssralg finset ssrint matrix.
From Infotheo Require Import Reals_ext Rssr ssr_ext ssralg_ext Rbigop proba num_occ.
Require Import Rbigop_complements bigop_tactics reals_complements.

(** * A Coq theory of random Boolean games *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope R_scope with Re.

(** ** Preliminary results to simplify goals of the form [x \in enum _] *)

Section Prelim_fintype.

Lemma mem_enumT (T : finType) (x : T) : (x \in enum T).
Proof. by rewrite enumT mem_index_enum. Qed.

Lemma mem_enum_set_seqE (T : finType) (s : seq T) (x : T) :
  (x \in enum [set x0 in s]) = (x \in s).
Proof. by rewrite !mem_filter !inE (mem_index_enum x) andbT. Qed.

Lemma mem_enum_seqE (T : finType) (s : seq T) (x : T) :
  (x \in enum s) = (x \in s).
Proof. by rewrite !mem_filter (mem_index_enum x) andbT. Qed.

Lemma mem_enum_setE (T : finType) (s : {set T}) (x : T) :
  (x \in enum s) = (x \in s).
Proof. by rewrite !mem_filter (mem_index_enum x) andbT. Qed.

End Prelim_fintype.

Lemma if_negb_eq a b : (if a then b else ~~ b) = (a == b).
Proof. by case: a; case: b. Qed.

Section Prelim_finset.

Variable T : finType.

Lemma setDUKr (A B : {set T}) : (A :|: B) :\: B = A :\: B.
Proof. by rewrite setDUl setDv setU0. Qed.

Lemma setDUKl (A B : {set T}) : (A :|: B) :\: A = B :\: A.
Proof. by rewrite setDUl setDv set0U. Qed.

Lemma eq_set (P1 P2 : pred T) :
  P1 =1 P2 -> [set x | P1 x] = [set x | P2 x].
Proof. by move=> H; apply/setP => x; rewrite !inE H. Qed.

Lemma setUDKl (A B : {set T}) : A :\: B :|: B = A :|: B.
Proof. by rewrite setDE setUIl (setUC (setC _)) setUCr setIT. Qed.

Lemma setUDKr (A B : {set T}) : A :|: B :\: A = A :|: B.
Proof. by rewrite setUC setUDKl setUC. Qed.

End Prelim_finset.

(** ** Boolean functions, DNF and (sets of) Boolean vectors *)

Section Def.

Variable n : nat.

Definition bool_vec := (bool ^ n)%type.

Definition bool_fun := {ffun bool_vec -> bool}.

Definition DNF_of (s : {set bool_vec}) : bool_fun :=
  [ffun v : bool_vec => \big[orb/false]_(vs in s)
                        \big[andb/true]_(i < n) (if vs i then v i else ~~ v i)].

(** [{set bool_vec}] is isomorphic to [bool_fun] *)

Definition bool_fun_of_finset (s : {set bool_vec}) : bool_fun :=
  [ffun v => v \in s].

Lemma DNF_ofE s : DNF_of s = bool_fun_of_finset s.
Proof.
apply/ffunP=> /= v; rewrite !ffunE; apply/idP/idP=> H.
- rewrite big_orE in H.
  have {H} /existsP /= [vs /andP [Hi1 Hi2]] := H.
  rewrite big_andE in Hi2.
  have {Hi2} /forallP /= Hi2 := Hi2.
  have Hi3 : forall i : 'I_n, v i = vs i.
    by move=> i; symmetry; apply/eqP; rewrite -if_negb_eq; exact: Hi2.
  by have->: v = vs by apply/ffunP.
- rewrite big_orE; apply/existsP; simpl; exists v; rewrite H /=.
  by rewrite big_andE; apply/forallP; move=> /= i; rewrite if_negb_eq.
Qed.

Definition finset_of_bool_fun (f : bool_fun) : {set bool_vec} :=
  [set w : bool ^ n | f w].

Lemma bool_fun_of_finsetK : cancel bool_fun_of_finset finset_of_bool_fun.
Proof. by move=> s; apply/setP => v; rewrite inE ffunE. Qed.

Lemma finset_of_bool_funK : cancel finset_of_bool_fun bool_fun_of_finset.
Proof. by move=> f; apply/ffunP => v; rewrite ffunE inE. Qed.

Lemma bool_fun_of_finset_bij : bijective bool_fun_of_finset.
Proof.
by exists finset_of_bool_fun; [apply: bool_fun_of_finsetK|apply: finset_of_bool_funK].
Qed.

Lemma finset_of_bool_fun_bij : bijective finset_of_bool_fun.
Proof.
by exists bool_fun_of_finset; [apply: finset_of_bool_funK|apply: bool_fun_of_finsetK].
Qed.

(** Definition 1.
    [w0 ⇒0 w1] := [w1] is true on [w0], i.e. on all elements of [w0] *)
Definition implies0 (w0 w1 : bool_fun) : bool := [forall i, w0 i ==> w1 i].

Infix "⇒0" := implies0 (at level 70).

Lemma implies0E w1 w2 :
  (w1 ⇒0 w2) = (finset_of_bool_fun w1 \subset finset_of_bool_fun w2).
Proof.
apply/idP/idP.
- by move=> H; apply/subsetP => x; move/forallP/(_ x)/implyP: H; rewrite !inE.
- by move/subsetP=> H; apply/forallP => x; move/(_ x)/implyP: H; rewrite !inE.
Qed.

End Def.

Infix "⇒0" := (@implies0 _) (at level 70).

Local Open Scope ring_scope.
Local Open Scope R_scope.
Local Open Scope proba_scope.
Local Open Scope vec_ext_scope.

(** ** A toy example *)

Section Proba_example.

Variable n : nat.

Let Omega := bool_fun n.

Let Omega_set := {set bool_vec n}.

  Check @bool_fun_of_finset n : Omega_set -> Omega.
  Check @finset_of_bool_fun n : Omega -> Omega_set.

Let sigmA := {set Omega}.

Variable P : {dist Omega}.

Lemma example : forall w0, 0 <= Pr P [set w | w0 ⇒0 w].
Proof. move=> *; exact: le_0_Pr. Qed.

End Proba_example.

(** ** An algebraic proof of the formula of inclusion-exclusion *)

Section probability_inclusion_exclusion.
(** In this section we prove the formula of inclusion-exclusion.
    This result is more general than lemma [Pr_bigcup] in Infotheo. *)
Variable A : finType.
Variable P : dist A.

Lemma bigmul_eq0 (C : finType) (p : pred C) (F : C -> R) :
  (exists2 i : C, p i & F i = R0) <-> \big[Rmult/R1]_(i : C | p i) F i = R0.
Proof.
split.
{ by case => [i Hi Hi0]; rewrite (bigD1 i) //= Hi0 Rmult_0_l. }
apply big_ind.
- by move=> K; exfalso; auto with real.
- move=> x y Hx Hy Hxy.
  have [Hx0|Hy0] := Rmult_integral _ _ Hxy; [exact: Hx|exact: Hy].
- move=> i Hi Hi0; by exists i.
Qed.

Lemma Pr_union_eq (E1 E2 : {set A}) :
  Pr P (E1 :|: E2) = Pr P E1 + Pr P E2 - Pr P (E1 :&: E2).
Proof.
rewrite -[E1 :|: E2](setID _ E1) Pr_union_disj; last first.
{ rewrite setDE -setIA [E1 :&: _]setIC -setIA [~: E1 :&: _]setIC setICr.
  by rewrite !setI0. }
rewrite setUK setDUKl -{1}[E2 in RHS](setID _ E1) Pr_union_disj; last first.
{ rewrite setDE -setIA [E1 :&: _]setIC -setIA [~: E1 :&: _]setIC setICr.
  by rewrite !setI0. }
by rewrite setIC; ring.
Qed.

Lemma Rplus_minus_assoc (r1 r2 r3 : R) : r1 + r2 - r3 = r1 + (r2 - r3).
Proof. by rewrite /Rminus Rplus_assoc. Qed.

(** *** A theory of indicator functions from [A : finType] to [R] *)

Definition Ind (s : {set A}) (x : A) : R := if x \in s then R1 else R0.

Lemma Ind_set0 (x : A) : Ind set0 x = R0.
Proof. by rewrite /Ind inE. Qed.

Lemma Ind_inP (s : {set A}) (x : A) : reflect (Ind s x = R1) (x \in s).
Proof.
apply: (iffP idP); rewrite /Ind; first by move->.
by case: ifP =>//; auto with real.
Qed.

Lemma Ind_notinP (s : {set A}) (x : A) : reflect (Ind s x = R0) (x \notin s).
Proof.
apply: (iffP idP); rewrite /Ind => Hmain.
  by rewrite ifF //; exact: negbTE.
by apply: negbT; case: ifP Hmain =>// _ H10; exfalso; auto with real.
Qed.

Lemma Ind_cap (S1 S2 : {set A}) (x : A) :
  Ind (S1 :&: S2) x = Ind S1 x * Ind S2 x.
Proof. by rewrite /Ind inE; case: in_mem; case: in_mem=>/=; auto with real. Qed.

Lemma Ind_bigcap I (e : I -> {set A}) (r : seq I) (p : pred I) x :
  Ind (\bigcap_(j <- r | p j) e j) x = \big[Rmult/R1]_(j <- r | p j) (Ind (e j) x).
Proof.
apply (big_ind2 (R1 := {set A}) (R2 := R)); last done.
- by rewrite /Ind inE.
- by move=> sa a sb b Ha Hb; rewrite -Ha -Hb; apply: Ind_cap.
Qed.

(** *** Extra support results for the expected value *)

(** Remark:

    In Infotheo, random variables [X : rvar A] are defined as a record
    gathering a distribution [P : dist A] and a function [f : A -> R].

    For convenience, we locally define the function [rv] for building
    such random variables, endowed with the ambient distribution [P]. *)

Let rv : (A -> R) -> rvar A := mkRvar P.

Lemma Ex_altE (X : A -> R) : `E (rv X) = \rsum_(a in A) X a * P a.
Proof. done. Qed.

Lemma E_Ind s : `E (rv (Ind s)) = Pr P s.
Proof.
rewrite /Ex_alt /Ind /Pr (bigID (mem s)) /=.
rewrite [X in _ + X = _]big1; last by move=> i /negbTE ->; rewrite Rmult_0_l.
by rewrite Rplus_0_r; apply: eq_bigr => i ->; rewrite Rmult_1_l.
Qed.

Lemma E_ext X2 X1 : X1 =1 X2 -> `E (rv X1) = `E (rv X2).
Proof.
by move=> Heq; rewrite /Ex_alt; apply: eq_bigr => i Hi /=; rewrite Heq.
Qed.

Lemma E_add X1 X2 : `E (rv (fun w => X1 w + X2 w)) = `E (rv X1) + `E (rv X2).
Proof.
rewrite /Ex_alt; set b := LHS; under b ? _ rewrite Rmult_plus_distr_r.
by rewrite big_split.
Qed.

Lemma E_rsum I r p (X : I -> A -> R) :
  `E (rv (fun x => \big[Rplus/R0]_(i <- r | p i) X i x)) =
  \big[Rplus/R0]_(i <- r | p i) (`E (rv (X i))).
Proof.
rewrite /Ex_alt exchange_big /=; apply: eq_bigr => i Hi.
by rewrite big_distrl /=.
Qed.

Lemma E_scaler X1 r2 : `E (rv (fun w => X1 w * r2)) = `E (rv X1) * r2.
Proof.
rewrite /Ex_alt big_distrl /=; apply: eq_bigr => i Hi.
by rewrite !Rmult_assoc; congr Rmult; rewrite Rmult_comm.
Qed.

Lemma E_scalel r1 X2 : `E (rv (fun w => r1 * X2 w)) = r1 * `E (rv X2).
Proof.
rewrite /Ex_alt big_distrr /=; apply: eq_bigr => i Hi.
by rewrite !Rmult_assoc; congr Rmult; rewrite Rmult_comm.
Qed.

(** [bigA_distr] is a specialization of [bigA_distr_bigA] and at the same
    time a generalized version of [GRing.exprDn] for iterated prod. *)
Lemma bigA_distr (R : Type) (zero one : R) (times : Monoid.mul_law zero)
    (plus : Monoid.add_law zero times)
    (I : finType)
    (F1 F2 : I -> R) :
  \big[times/one]_(i in I) plus (F1 i) (F2 i) =
  \big[plus/zero]_(0 <= k < #|I|.+1)
  \big[plus/zero]_(J in {set I} | #|J| == k)
  \big[times/one]_(j in I) (if j \notin J then F1 j else F2 j).
Proof.
pose F12 i (j : bool) := if ~~ j then F1 i else F2 i.
under big i Hi
  rewrite (_: plus (F1 i) (F2 i) = \big[plus/zero]_(j : bool) F12 i j).
rewrite bigA_distr_bigA big_mkord (partition_big
  (fun i : {ffun I -> _} => inord #|[set x | i x]|)
  (fun j : [finType of 'I_#|I|.+1] => true)) //=.
{ eapply eq_big =>// i _.
  rewrite (reindex (fun s : {set I} => [ffun x => x \in s])); last first.
  { apply: onW_bij.
    exists (fun f : {ffun I -> bool} => [set x | f x]).
    by move=> s; apply/setP => v; rewrite inE ffunE.
    by move=> f; apply/ffunP => v; rewrite ffunE inE. }
  eapply eq_big.
  { move=> s; apply/eqP/eqP.
      move<-; rewrite -[#|s|](@inordK #|I|) ?ltnS ?max_card //.
      by congr inord; apply: eq_card => v; rewrite inE ffunE.
    move=> Hi; rewrite -[RHS]inord_val -{}Hi.
    by congr inord; apply: eq_card => v; rewrite inE ffunE. }
  by move=> j Hj; apply: eq_bigr => k Hk; rewrite /F12 ffunE. }
rewrite (reindex (fun x : 'I_2 => (x : nat) == 1%N)); last first.
  { apply: onW_bij.
    exists (fun b : bool => inord (nat_of_bool b)).
    by move=> [x Hx]; rewrite -[RHS]inord_val; case: x Hx =>// x Hx; case: x Hx.
    by case; rewrite inordK. }
rewrite 2!big_ord_recl big_ord0 /F12 /=.
by rewrite Monoid.mulm1.
Qed.

Lemma bigID2 (R : Type) (I : finType) (J : {set I}) (F1 F2 : I -> R)
    (idx : R) (op : Monoid.com_law idx) :
  \big[op/idx]_(j in I) (if j \notin J then F1 j else F2 j) =
  op (\big[op/idx]_(j in ~: J) F1 j) (\big[op/idx]_(j in J) F2 j).
Proof.
rewrite (bigID (mem (setC J)) predT); apply: congr2.
by apply: eq_big =>// i /andP [H1 H2]; rewrite inE in_setC in H2; rewrite H2.
apply: eq_big => [i|i /andP [H1 H2]] /=; first by rewrite inE negbK.
by rewrite ifF //; apply: negbTE; rewrite inE in_setC in H2.
Qed.

(* TODO: to move *)
Lemma bigcap_seq_const I (B : {set A}) (r : seq I) :
  (0 < size r)%N -> \bigcap_(i <- r) B = B.
Proof.
elim: r => [//|a r IHr] _; rewrite big_cons.
case: r IHr => [|b r] IHr; first by rewrite big_nil setIT.
by rewrite IHr // setIid.
Qed.

Lemma bigcap_ord_const n' (B : {set A}) :
  \bigcap_(i < n'.+1) B = B.
Proof. by rewrite bigcap_seq_const // /index_enum -enumT size_enum_ord. Qed.

Lemma bigcap_const (I : eqType) (B : {set A}) (r : seq I) (p : pred I) :
  (exists2 i : I, i \in r & p i) ->
  \bigcap_(i <- r | p i) B = B.
Proof.
case=> i H1 H2; rewrite -big_filter bigcap_seq_const //.
rewrite size_filter- has_count.
by apply/hasP; exists i.
Qed.

Lemma m1powD k : k <> 0%N -> (-1)^(k-1) = - (-1)^k.
Proof.
by case: k => [//|k _]; rewrite subn1 /= Ropp_mult_distr_l oppRK Rmult_1_l.
Qed.

Lemma bigsum_card_constE (I : finType) (B : pred I) x0 :
  \rsum_(i in B) x0 = (INR #|B| * x0)%Re.
Proof. by rewrite big_const iter_Rplus. Qed.

Lemma bigmul_constE (x0 : R) (k : nat) : \rmul_(i < k) x0 = (x0 ^ k)%Re.
Proof.
rewrite big_const cardT size_enum_ord.
elim: k => [//|k IHk].
by rewrite /= IHk /= Rmult_comm.
Qed.

Lemma bigmul_card_constE (I : finType) (B : pred I) x0 : \rmul_(i in B) x0 = x0 ^ #|B|.
Proof.
rewrite big_const.
elim: #|B| => [//|k IHk].
by rewrite /= IHk /= Rmult_comm.
Qed.

(** [bigmul_m1pow] is the Reals counterpart of lemma [GRing.prodrN] *)
Lemma bigmul_m1pow (I : finType) (p : pred I) (F : I -> R) :
  \rmul_(i in p) - F i = (-1) ^ #|p| * \rmul_(i in p) F i.
Proof.
rewrite -bigmul_card_constE.
apply: (big_rec3 (fun a b c => a = b * c)).
{ by rewrite Rmult_1_l. }
move=> i a b c Hi Habc; rewrite Habc; ring.
Qed.

Let SumIndCap (n : nat) (S : 'I_n -> {set A}) (k : nat) (x : A) :=
  \rsum_(J in {set 'I_n} | #|J| == k) (Ind (\bigcap_(j in J) S j) x).

Lemma Ind_bigcup_incl_excl (n : nat) (S : 'I_n -> {set A}) (x : A) :
  Ind (\bigcup_(i < n) S i) x =
  (\rsum_(1 <= k < n.+1) ((-1)^(k-1) * (SumIndCap S k x)))%Re.
Proof.
case: n S => [|n] S; first by rewrite big_ord0 big_geq // Ind_set0.
set Efull := \bigcup_(i < n.+1) S i.
have Halg : \big[Rmult/R1]_(i < n.+1) (Ind Efull x - Ind (S i) x) = 0.
  case Ex : (x \in Efull); last first.
  { have /Ind_notinP Ex0 := Ex.
    under big ? _ rewrite Ex0.
    have Ex00 : forall i : 'I_n.+1, Ind (S i) x = 0.
      move=> i; apply/Ind_notinP.
      by move/negbT: Ex; rewrite -!in_setC setC_bigcup; move/bigcapP; apply.
    under big ? _ rewrite Ex00; rewrite Rminus_0_r.
    by apply/bigmul_eq0; exists ord0. }
  { rewrite /Efull in Ex.
    have /bigcupP [i Hi Hi0] := Ex.
    apply/bigmul_eq0; exists i =>//.
    by rewrite /Efull (Ind_inP _ _ Ex) (Ind_inP _ _ Hi0) /Rminus Rplus_opp_r. }
rewrite (@bigA_distr R R0 R1) in Halg.
under big in Halg k _ under big J _ rewrite bigID2.
rewrite big_ltn //= in Halg.
rewrite -> addR_eq0 in Halg.
rewrite cardT size_enum_ord (big_pred1 set0) in Halg; last first.
  by move=> i; rewrite pred1E [RHS]eq_sym; apply: cards_eq0.
rewrite [in X in _ * X = _]big_pred0 in Halg; last by move=> i; rewrite inE.
underp big in Halg j rewrite !inE /negb /=.
rewrite Rmult_1_r -Ind_bigcap bigcap_ord_const in Halg.
rewrite {}Halg.
rewrite (big_morph Ropp (id1 := R0) (op1 := Rplus)); first last.
  by rewrite Ropp_0.
  by move=> *; rewrite Ropp_plus_distr.
rewrite big_nat [RHS]big_nat.
apply: eq_bigr => i Hi; rewrite /SumIndCap /Efull.
rewrite m1powD; last first.
  by case/andP: Hi => Hi _ K0; rewrite K0 in Hi.
rewrite -Ropp_mult_distr_l.
rewrite [in RHS](big_morph _ (id1 := R0) (op1 := Rplus)); first last.
  by rewrite Rmult_0_r.
  by move=> *; rewrite Rmult_plus_distr_l.
congr Ropp; apply: eq_bigr => j Hj.
rewrite bigmul_m1pow (eqP Hj).
rewrite (_ : ?[a] * ((-1)^i * ?[b]) = (-1)^i * (?a * ?b)); last by ring.
congr Rmult.
have [Hlt|Hn1] := ltnP i n.+1; last first.
{ rewrite big1; last first.
  { move=> k Hk; rewrite inE in Hk.
    rewrite (_: j = [set: 'I_n.+1]) ?inE // in Hk.
    apply/setP/subset_cardP =>//.
    rewrite (eqP Hj) cardsT /= card_ord.
    by apply/anti_leq/andP; split; first by case/andP: Hi =>//. }
  by rewrite Rmult_1_l Ind_bigcap. }
rewrite -!Ind_bigcap bigcap_const; last first.
{ exists (odflt ord0 (pick [pred x | x \notin j])); first exact: mem_index_enum.
  case: pickP; first by move=> y Hy; rewrite !inE -in_setC in Hy.
  move=> /pred0P K; exfalso.
  rewrite /pred0b in K.
  have Hcard := cardsC j.
  rewrite cardsE (eqP K) (eqP Hj) cardT size_enum_ord addn0 in Hcard.
  by rewrite Hcard ltnn in Hlt. }
rewrite -Ind_cap -/Efull.
suff : \bigcap_(j0 in j) S j0 \subset Efull by move/setIidPr->.
rewrite /Efull.
pose i0 := odflt ord0 (pick (mem j)).
have Hi0 : i0 \in j.
{ rewrite /i0; case: pickP =>//.
  move=> /pred0P K; exfalso.
  rewrite /pred0b (eqP Hj) in K.
  by rewrite (eqP K) /= in Hi. }
apply: (subset_trans (bigcap_inf i0 Hi0)).
exact: (bigcup_sup i0).
Qed.

Let SumPrCap (n : nat) (S : 'I_n -> {set A}) (k : nat) :=
  \rsum_(J in {set 'I_n} | #|J| == k) Pr P (\bigcap_(j in J) S j).

Lemma E_SumIndCap n (S : 'I_n -> {set A}) k :
  `E (rv (SumIndCap S k)) = SumPrCap S k.
Proof.
rewrite /SumIndCap /SumPrCap E_rsum; apply: eq_bigr => i Hi.
by rewrite E_Ind.
Qed.

Theorem Pr_bigcup_incl_excl n (S : 'I_n -> {set A}) :
  Pr P (\bigcup_(i < n) S i) =
  \big[Rplus/0]_(1 <= k < n.+1) ((-1)^(k-1) * SumPrCap S k).
Proof.
rewrite -E_Ind.
under big ? _ rewrite /= Ind_bigcup_incl_excl.
rewrite -Ex_altE E_rsum.
apply: eq_bigr => i _.
by rewrite E_scalel E_SumIndCap.
Qed.

End probability_inclusion_exclusion.

(** ** Push-forward distribution w.r.t [X : A -> B] where [A, B : finType] *)

(** Note: [X : A -> B] is necessarily measurable, as both [A] and [B]
    are finite (and thereby endowed with the discrete sigma-algebra). *)

Section Pushforward_distribution.

Lemma dist_img_proof {A B : finType} (X : A -> B) (PA : dist A) :
  \rsum_(a in B)
     {|
     pos_f := fun b : B => Pr PA [set x | X x == b];
     Rle0f := fun c : B => le_0_Pr PA [set x | X x == c] |} a = 1
.
Proof.
rewrite -[RHS](pmf1 PA) (sum_parti'_finType _ _ X).
rewrite [RHS]big_uniq /= ?undup_uniq //.
rewrite (bigID (mem (undup [seq X i | i <- enum A])) predT) /=.
rewrite [X in _ + X = _]big1 ?Rplus_0_r; last first.
  move=> b Hb; rewrite (_: [set x | X x == b] = set0) ?Pr_0 //.
  apply/setP => a; rewrite !inE.
  rewrite mem_undup in Hb.
  apply/negbTE/eqP => K; rewrite -K in Hb.
  have K' := @map_f _ _ X (enum A) a.
  rewrite mem_enumT in K'.
  by rewrite K' in Hb.
by apply: eq_bigr => b Hb; apply: eq_bigl => a; rewrite inE.
Qed.

Definition dist_img {A B : finType} (X : A -> B) (PA : dist A) : dist B.
Proof.
refine (mkDist (pmf := (mkPosFun (pos_f := fun b => Pr PA [set x | X x == b])
  (fun c => le_0_Pr PA [set x | X x == c]))) _).
exact: dist_img_proof.
Defined.

End Pushforward_distribution.


Section Finite_product_structure.

Variables (I : finType) (T_ : I -> finType).

Definition prodn_type := forall i : I, T_ i.

(* Inductive or Record *)
Record prodn : predArgType :=
  { prodn_fun :> {ffun I -> {i : I & T_ i}} ;
    prodn_prop : [forall i : I, projT1 (prodn_fun i) == i] }.

Program Definition prodn_type_of_prodn (f : prodn) : prodn_type :=
  fun i => ecast j (Finite.sort (T_ j)) _ (projT2 (prodn_fun f i)).
Next Obligation.
case: f => f p /=; apply/eqP.
by move/forallP in p.
Defined.
(*
Proof.
move=> i.
assert (fi := (projT2 (prodn_fun f i))).
assert (H : projT1 (f i) = i).
  by apply/eqP; case: (f) => [ff] /= /forallP.
by rewrite -H.
Defined.
 *)

Program Definition prodn_of_prodn_type (f : prodn_type) : prodn :=
  @Build_prodn (finfun (fun i => @existT _ _ i (f i))) _.
Next Obligation.
by apply/forallP => i; rewrite ffunE.
Defined.
(*
Proof.
eapply Build_prodn.
red in f.
Unshelve.
2: apply (finfun (fun i => @existT _ _ i (f i))).
by apply/forallP => i; rewrite ffunE /=.
Defined.
 *)

(* Local Notation enumF T := (Finite.enum T). *)

(*
filter_map:
  forall (T1 T2 : Type) (f : T1 -> T2) (a : pred T2) (s : seq T1),
  [seq x <- [seq f i | i <- s] | a x] = [seq f i | i <- s & (preim f a) i]

filter_map:
  forall (T1 T2 : Type) (f : forall _ : T1, T2) (a : pred T2) (s : list T1),
  eq (filter a (map f s)) (map f (filter (preim f a) s))
*)

(* Canonical prodn_fun_finType := [finType of {ffun I -> {i : I & T_ i}}]. *)
Canonical prodn_subType := Eval hnf in [subType for prodn_fun].
Definition prodn_eqm := Eval hnf in [eqMixin of prodn by <:].
Canonical prodn_eqType := Eval hnf in EqType prodn prodn_eqm.
Definition prodn_chm := [choiceMixin of prodn by <:].
Canonical prodn_choiceType := Eval hnf in ChoiceType prodn prodn_chm.
Definition prodn_cntm := [countMixin of prodn by <:].
Canonical prodn_countType := Eval hnf in CountType prodn prodn_cntm.
Canonical prodn_subCountType := Eval hnf in [subCountType of prodn].
Definition prodn_finm := [finMixin of prodn by <:].
Canonical prodn_finType := Eval hnf in FinType prodn prodn_finm.
Canonical prodn_subFinType := Eval hnf in [subFinType of prodn_finType].
(* Print Canonical Projections.
Print prodn_finm.
Print prodn_cntm. *)

Lemma sigT_eta A (P : A -> Type) (s : {x : A & P x}) :
  s = existT _ (projT1 s) (projT2 s).
Proof. by move: s => [x Q]. Qed.

(* PROVED BUT UNNEEDED

Lemma ecast_trans : forall m n p (s : T_ m)
    (eq_mn : m = n) (eq_np : n = p),
  ecast i (T_ i) (etrans eq_mn eq_np) s =
  ecast i (T_ i) eq_np (ecast j (T_ j) eq_mn s).
Proof.
move=> m n' p' s eq_mn eq_np.
case: n' / eq_mn eq_np.
by case: p' /.
Qed.

Lemma ecast_id (i : I) (erefl_i : i = i) (t : T_ i) :
  ecast i (T_ i) erefl_i t = t.
Proof. by rewrite [erefl_i]eq_axiomK. Qed.
 *)

Lemma prodn_type_of_prodnK : cancel prodn_type_of_prodn prodn_of_prodn_type.
Proof.
move => x.
rewrite /prodn_type_of_prodn /prodn_of_prodn_type.
apply: val_inj =>/=.
apply/ffunP => i; rewrite !ffunE.
case: x => f p /=.
rewrite [RHS]sigT_eta.
(* rewrite -/tag -/tagged -/(Tagged _ _) -/(Tagged _ _) in p *. *)
(* apply/eqP; rewrite eq_sym; rewrite eq_Tagged. *)
set Ei := eqP (elimTF forallP p i).
apply EqdepFacts.eq_dep_eq_sigT.
apply EqdepFacts.eq_dep1_dep.
by apply: EqdepFacts.eq_dep1_intro.
Qed.

(*
Check eq_axiomK.
Check Eqdep_dec.eq_rect_eq_dec.
Check rew_opp_l.
 *)

Check card_partition.
Check (big_seq, big_uniq).
Check card_tagged.

Lemma card_prodn :
  #|prodn| = \big[muln/1%N]_(i : I) #|T_ i|.
Proof.
rewrite card_sub.
(* UNNEEDED
rewrite (eq_card (_ : _ =i [set x : {ffun I -> {i : I & T_ i}} | [forall i, projT1 (x i) == i]])).
2: by move=> i; rewrite inE.
 *)
rewrite -[LHS]/#|family (fun i : I => [pred j : {i : I & T_ i} | projT1 j == i])|.
rewrite card_family.
set lhs := LHS; suff->: lhs = foldr muln 1%N [seq #|T_ i| | i : I]; rewrite {}/lhs.
by rewrite /image_mem foldr_map BigOp.bigopE /reducebig; f_equal; rewrite enumT.
f_equal; apply eq_map => i.
rewrite -sum1_card; (underp big i0 rewrite inE).
pose IT := tag_finType T_.
rewrite -sum1_card.
Admitted.

(*
Check tagged_as.
change i with (tag _ (Tagged _)).
apply eq_big.

(* pose p := fun a : IT => tagged a : T_ (tag a). *)
pose p := fun a : IT => tagged a : [finType of T_ (tag a)].
rewrite (partition_big p).
rewrite sum1dep_card.

set lhs := LHS; have->: lhs = #||; rewrite /lhs.
rewrite cardE.
erewrite <-eq_card_sub.
Check (reindex (@tagged _ _ _)).
rewrite sum1dep_card.

rewrite cardsE /=.
eapply eq_card.
rewrite card1.
apply card_bool.
rewrite card_tagged.
set lhs := LHS; have->: lhs = foldr muln 1%N [seq #|T_ i| | i : I]; rewrite /lhs.
rewrite card1.
rewrite card_tagged.
rewrite -card_map.
rewrite card_sig.
rewrite /foldr.
rewrite foldr_map.

rewrite card1.
rewrite /family_mem.
apply eq_card.
rewrite -[LHS]/(family (fun i => [pred j | projT1 j == i])).

rewrite !cardE size_filter -!enumT /enum_mem -enumT.
rewrite count_map -size_filter enumT -cardE.
rewrite card_preim.
elim: (index_enum I) =>//=.

rewrite card_ffun.
rewrite card_sig.
rewrite card_ffun.
*)

End Finite_product_structure.

(** ** Random Boolean games and characterization of winning strategies *)

Section Proba_games.

Variable n : nat.

(** Let us consider Boolean Games of two players A and B with a random
    Boolean function of [n] variables as the pay function of A, and
    its negation as the pay function for B.

    We shall assume that A controls the first [k] variables, and B the
    remaining [n-k] variables.

    The prefix [bg_] stands for "Boolean Game".
*)

Variable k : nat.

Class leq_class k n := leq_prop : (k <= n)%N.

Context `{!leq_class k n}.

Lemma knk_eqn : (k + (n - k) = n)%N.
Proof. by apply: subnKC. Qed.

Lemma eqn_knk : (n = k + (n - k))%N.
Proof. by rewrite knk_eqn. Qed.

Definition bg_StratA := (bool_vec k)%type.

Definition bg_StratB := (bool_vec (n - k))%type.

(** Outcomes are Booleans, and [true] means player A wins *)
Definition bg_Outc := bool.

Definition bg_strategy := (bg_StratA * bg_StratB)%type.

(** [bg_strategy] is isomorphic to [bool_vec n] *)

Definition bool_vec_of_bg_strategy (s : bg_strategy) : bool_vec n :=
  [ffun i : 'I_n => match split (cast_ord eqn_knk i) with
                    | inl ik => s.1 ik
                    | inr ink => s.2 ink
                    end].

Definition widen_k_n : 'I_k -> 'I_n := widen_ord leq_prop.

Definition bg_strategy_of_bool_vec (v : bool_vec n) : bg_strategy :=
  ([ffun ik : 'I_k => v (widen_k_n ik)],
   [ffun ink : 'I_(n - k) => v (cast_ord knk_eqn (rshift k ink))]).

Lemma bool_vec_of_bg_strategyK :
  cancel bool_vec_of_bg_strategy bg_strategy_of_bool_vec.
Proof.
move=> s; rewrite (surjective_pairing s).
congr pair; apply/ffunP => v; rewrite !ffunE.
- case: splitP => /= j; first by move/ord_inj->.
  case: v => [v Hv] /= => K; exfalso; rewrite K in Hv.
  by rewrite ltnNge leq_addr in Hv.
- case: splitP => /= j.
  + case: j => [j Hv] /= => K; exfalso; rewrite -K in Hv.
    by rewrite ltnNge leq_addr in Hv.
  + by move/eqP; rewrite eqn_add2l; move/eqP/ord_inj->.
Qed.

Lemma bg_strategy_of_bool_vecK :
  cancel bg_strategy_of_bool_vec bool_vec_of_bg_strategy.
Proof.
move=> v; apply/ffunP=> x; rewrite !ffunE.
by case: splitP=>/= j H; rewrite ffunE; apply: congr1; apply/ord_inj; rewrite H.
Qed.

Lemma bool_vec_of_bg_strategy_bij : bijective bool_vec_of_bg_strategy.
Proof.
by exists bg_strategy_of_bool_vec; [apply: bool_vec_of_bg_strategyK|apply: bg_strategy_of_bool_vecK].
Qed.

Lemma bg_strategy_of_bool_vec_bij : bijective bg_strategy_of_bool_vec.
Proof.
by exists bool_vec_of_bg_strategy; [apply: bg_strategy_of_bool_vecK|apply: bool_vec_of_bg_strategyK].
Qed.

Definition bool_game := {ffun bg_strategy -> bg_Outc}.

(** [bool_game] is isomorphic to [bool_fun n] *)

Definition bool_fun_of_bool_game (g : bool_game) : bool_fun n :=
  [ffun i => g (bg_strategy_of_bool_vec i)].

Definition bool_game_of_bool_fun (f : bool_fun n) : bool_game :=
  [ffun s => f (bool_vec_of_bg_strategy s)].

Lemma bool_fun_of_bool_gameK :
  cancel bool_fun_of_bool_game bool_game_of_bool_fun.
Proof.
move=> g; apply/ffunP => x; rewrite !ffunE.
by rewrite bool_vec_of_bg_strategyK.
Qed.

Lemma bool_game_of_bool_funK :
  cancel bool_game_of_bool_fun bool_fun_of_bool_game.
Proof.
move=> f; apply/ffunP => x; rewrite !ffunE.
by rewrite bg_strategy_of_bool_vecK.
Qed.

Lemma bool_fun_of_bool_game_bij : bijective bool_fun_of_bool_game.
Proof.
by exists bool_game_of_bool_fun; [apply: bool_fun_of_bool_gameK|apply: bool_game_of_bool_funK].
Qed.

Lemma bool_game_of_bool_fun_bij : bijective bool_game_of_bool_fun.
Proof.
by exists bool_fun_of_bool_game; [apply: bool_game_of_bool_funK|apply: bool_fun_of_bool_gameK].
Qed.

Definition Omega := bool_fun n.

Variable P : {dist Omega}.

Let sigmA := {set Omega}.

(*
Variable random_f : Omega.
Definition g := bg_game_of random_f.
*)

Definition winA (g : bool_game) (a : bg_StratA) : bool :=
  [forall b : bg_StratB, g (a, b) (** == true *)].

Definition winA_wide (g : bool_game) (s : bg_strategy) : bool :=
  winA g s.1.

Definition w_ (a : bg_StratA) : Omega :=
  [ffun v : bool ^ n => [forall i : 'I_k, v (widen_k_n i) == a i]].

Lemma w_inj a a' : w_ a = w_ a' -> a = a'.
Proof.
rewrite /w_ => /ffunP H.
apply/ffunP => /= i.
pose v := bool_vec_of_bg_strategy (a, [ffun i => false]).
move/(_ v) in H.
rewrite !ffunE in H.
have HT : forall i0, v (widen_k_n i0) = a i0.
{ move=> i'; apply/eqP; rewrite /v /bool_vec_of_bg_strategy ffunE.
  case: splitP => j /=; first by move/ord_inj ->.
  case: i' => [i' Hi'] /= => K; exfalso; rewrite K in Hi'.
  by rewrite ltnNge leq_addr in Hi'. }
symmetry in H; move/forallP in H; rewrite ifT in H; last first.
  apply/forallP => *; exact/eqP.
rewrite -HT.
exact/eqP/H.
Qed.

Definition W_ (a : bg_StratA) : sigmA :=
  [set w : Omega | (w_ a) ⇒0 w].

Fact winA_eq :
  forall (f : Omega) (a : bg_StratA),
  winA (bool_game_of_bool_fun f) a = (f \in W_ a).
Proof.
move=> f a; rewrite /winA /W_.
apply/forallP/idP =>/= H.
- rewrite -(bool_game_of_bool_funK f) inE implies0E.
  rewrite /bool_fun_of_bool_game.
  apply/subsetP => x.
  rewrite !inE 2!ffunE => /forallP H'.
  have->: bg_strategy_of_bool_vec x = (a, (bg_strategy_of_bool_vec x).2).
    rewrite [LHS]surjective_pairing; congr pair.
    apply/ffunP => ik; rewrite !ffunE.
    by apply/eqP; exact: H'.
  exact: H.
- rewrite inE /w_ !implies0E in H.
  move/subsetP in H.
  move=> x; move/(_ (bool_vec_of_bg_strategy (a, x))) in H.
  rewrite !inE in H; rewrite ffunE; apply: H; rewrite ffunE.
  apply/forallP => y; rewrite ffunE.
  case: splitP => j /=; first by move/ord_inj<-.
  case: y => [y Hy] /= => K; exfalso; rewrite K in Hy.
  by rewrite ltnNge leq_addr in Hy.
Qed.

(** To derive [Pr_ex_winA], we need to reindex the bigcup above,
    as [Pr_bigcup_incl_excl] uses integer indices. *)

(** [bg_StratA] is isomorphic to ['I_#|bool_vec k|] *)

Definition ord_of_StratA : bg_StratA -> 'I_#|bool_vec k| := enum_rank.

Definition StratA_of_ord : 'I_#|bool_vec k| -> bg_StratA := enum_val.

Lemma ord_of_StratAK : cancel ord_of_StratA StratA_of_ord.
Proof. exact: enum_rankK. Qed.

Lemma StratA_of_ordK : cancel StratA_of_ord ord_of_StratA.
Proof. exact: enum_valK. Qed.

Lemma ord_of_StratA_bij : bijective ord_of_StratA.
Proof. by exists StratA_of_ord; [apply: ord_of_StratAK|apply: StratA_of_ordK]. Qed.

Lemma StratA_of_ord_bij : bijective StratA_of_ord.
Proof. by exists ord_of_StratA; [apply: StratA_of_ordK|apply: ord_of_StratAK]. Qed.

(** Then we lift these results to the powerset. *)

(** [{set bg_StratA}] is isomorphic to [{set ('I_#|bool_vec k|)}] *)

Definition set_ord_of_StratA (s : {set bg_StratA}) : {set ('I_#|bool_vec k|)} :=
  [set x | x \in [seq enum_rank i | i <- enum s]].

Definition set_StratA_of_ord (s : {set ('I_#|bool_vec k|)}) : {set bg_StratA} :=
  [set x | x \in [seq enum_val i | i <- enum s]].

Lemma map_ord_of_StratAK : cancel (map ord_of_StratA) (map StratA_of_ord).
Proof. apply: mapK; exact: ord_of_StratAK. Qed.

Lemma map_StratA_of_ordK : cancel (map StratA_of_ord) (map ord_of_StratA).
Proof. apply: mapK; exact: StratA_of_ordK. Qed.

Lemma set_ord_of_StratAK : cancel set_ord_of_StratA set_StratA_of_ord.
Proof.
move=> s; rewrite /set_ord_of_StratA /set_StratA_of_ord.
apply/setP =>x; rewrite !inE.
rewrite -{1}(enum_rankK x).
rewrite mem_map /=; last exact: enum_val_inj.
rewrite mem_enum_set_seqE mem_map; last exact: enum_rank_inj.
by rewrite mem_enum_setE.
Qed.

Lemma set_StratA_of_ordK : cancel set_StratA_of_ord set_ord_of_StratA.
Proof.
move=> s; rewrite /set_ord_of_StratA /set_StratA_of_ord.
apply/setP =>x; rewrite !inE.
rewrite -{1}(enum_valK x).
rewrite mem_map /=; last exact: enum_rank_inj.
rewrite mem_enum_set_seqE mem_map; last exact: enum_val_inj.
by rewrite mem_enum_setE.
Qed.

Lemma set_ord_of_StratA_bij : bijective set_ord_of_StratA.
Proof.
by exists set_StratA_of_ord; [apply: set_ord_of_StratAK|apply: set_StratA_of_ordK].
Qed.

Lemma set_StratA_of_ord_bij : bijective set_StratA_of_ord.
Proof.
by exists set_ord_of_StratA; [apply: set_StratA_of_ordK|apply: set_ord_of_StratAK].
Qed.

Theorem Pr_ex_winA :
  Pr P [set F | [exists a : bg_StratA, winA (bool_game_of_bool_fun F) a]] =
  \rsum_(1 <= i < (2^k).+1) (-1)^(i-1) *
  \rsum_(J in {set bg_StratA} | #|J| == i) Pr P (\bigcap_(a in J) W_ a).
Proof.
have->: [set F | [exists a, winA (bool_game_of_bool_fun F) a]] =
  \bigcup_(a in bg_StratA) W_ a.
{ apply/setP => f; rewrite !inE.
  apply/existsP/bigcupP.
  - by case=> a ?; exists a =>//; rewrite -winA_eq.
  - by case=> a *; exists a =>//; rewrite winA_eq. }
rewrite (reindex StratA_of_ord) /=; last first.
  by apply: onW_bij; apply: StratA_of_ord_bij.
underp (\bigcup_(j | _) _) j rewrite enum_valP.
rewrite Pr_bigcup_incl_excl {1}card_ffun /= card_bool card_ord.
apply: eq_bigr => i _.
congr Rmult.
rewrite (reindex set_ord_of_StratA) /=; last first.
  by apply: onW_bij; apply: set_ord_of_StratA_bij.
apply: eq_big.
{ move=> j.
  (* There is no lemma "bijective f -> #|f s| = #|s|"
     but we can use [on_card_preimset] & [card_image] *)
  rewrite on_card_preimset; last by apply: onW_bij; exists id; move=> *.
  f_equal; rewrite card_image //; exact/bij_inj/enum_rank_bij. }
move=> s Hs; f_equal.
rewrite (reindex StratA_of_ord) /=; last first.
  by apply: onW_bij; apply: StratA_of_ord_bij.
apply: eq_bigl.
move=> x; rewrite /set_ord_of_StratA !inE.
rewrite -(mem_map (f := StratA_of_ord)); last exact/bij_inj/StratA_of_ord_bij.
rewrite -map_comp; rewrite (eq_map (f2 := id)); last exact: ord_of_StratAK.
by rewrite map_id mem_enum_setE.
Qed.

End Proba_games.

(*
Section Proba_product.

Variables (I : finType) (T_ : I -> finType).
(* Check #|{: {i : I & T_ i}}|. *)
Variable P_ : forall i, dist (T_ i).

End Proba_product.
 *)

Section Proba_winning.

(** ** Probability of Winning Strategies *)

(** We now consider Boolean functions whose truth-set is built from
    2^n independent Bernoulli trials with probability [p] of success. *)

Variable n : nat.

Variable p : R.

(* If need be:

Hypothesis p_0_1_strict : 0 < p < 1.

Let p_0_1 : 0 <= p <= 1.
Proof. by case: p_0_1_strict => H1 H2; split; apply: Rlt_le. Qed.
*)

Class p_0_1_class p := p_0_1 : 0 <= p <= 1.

Context `{!p_0_1_class p}.

Global Instance q_0_1 : p_0_1_class (1 - p).
Proof. by case: p_0_1 => H1 H2; split; lra. Qed.

(** Bernoulli distribution "B(p)": a distribution over {true, false}
such that [P(true) = p]. *)
Definition distb : {dist bool} := bdist card_bool q_0_1.

Lemma qqE : 1 - (1 - p) = p.
Proof. lra. Qed.

Lemma qpE : 1 - p + p = 1.
Proof. lra. Qed.

Lemma enum_bool : enum bool_finType = [:: true; false].
Proof. by rewrite /enum_mem Finite.EnumDef.enumDef. Qed.

Lemma val0_bool : Two_set.val0 card_bool = true.
Proof.
by rewrite /ssr_ext.Two_set.val0 /= (enum_val_nth true) /= enum_bool.
Qed.

Lemma val1_bool : Two_set.val1 card_bool = false.
Proof.
by rewrite /ssr_ext.Two_set.val1 /= (enum_val_nth true) /= enum_bool.
Qed.

Lemma distbT : distb true = p.
Proof. by rewrite /= ffunE val0_bool qqE. Qed.

Lemma distbF : distb false = 1 - p.
Proof. by rewrite /= ffunE val0_bool. Qed.

Section Bernoulli_process_def.
(** Definition of a Bernoulli process: independent repetition of [m := 2^n]
Bernoulli trials with parameter [p]. *)

Definition bool_row_pow n := 'rV[bool]_(2^n).

Definition dist_Bernoulli_aux : {dist bool_row_pow n} :=
  TupleDist.d distb (2^n).

(** [bool_vec n] is isomorphic to ['I_(2^n)] *)

Lemma card_bool_vec : forall {n}, #|bool_vec n| = (2 ^ n)%N.
Proof. by move=> ?; rewrite /bool_vec card_ffun card_bool card_ord. Qed.

Definition ord_of_bool_vec : bool_vec n -> 'I_(2 ^ n) :=
  cast_ord card_bool_vec \o enum_rank.

Definition bool_vec_of_ord : 'I_(2 ^ n) -> bool_vec n :=
  enum_val \o cast_ord (esym card_bool_vec).

Lemma ord_of_bool_vecK : cancel ord_of_bool_vec bool_vec_of_ord.
Proof.
move=> v; rewrite /ord_of_bool_vec /bool_vec_of_ord /=.
by rewrite cast_ordK enum_rankK.
Qed.

Lemma bool_vec_of_ordK : cancel bool_vec_of_ord ord_of_bool_vec.
Proof.
move=> v; rewrite /ord_of_bool_vec /bool_vec_of_ord /=.
by rewrite enum_valK cast_ordKV.
Qed.

Lemma ord_of_bool_vec_bij : bijective ord_of_bool_vec.
Proof.
by exists bool_vec_of_ord; [apply: ord_of_bool_vecK|apply: bool_vec_of_ordK].
Qed.

Lemma bool_vec_of_ord_bij : bijective bool_vec_of_ord.
Proof.
by exists ord_of_bool_vec; [apply: bool_vec_of_ordK|apply: ord_of_bool_vecK].
Qed.

(** [bool_row_pow n] is isomorphic to [bool_fun n] *)

Definition bool_fun_of_row (g : bool_row_pow n) : bool_fun n :=
  [ffun v => g ``_ (ord_of_bool_vec v)].

Definition row_of_bool_fun (f : bool_fun n) : bool_row_pow n :=
  \matrix_(i, j) f (bool_vec_of_ord j).

Lemma bool_fun_of_rowK : cancel bool_fun_of_row row_of_bool_fun.
Proof.
move=> r; rewrite /bool_fun_of_row /row_of_bool_fun.
by apply/matrixP => i j; rewrite mxE ffunE bool_vec_of_ordK [i]ord1.
Qed.

Lemma row_of_bool_funK : cancel row_of_bool_fun bool_fun_of_row.
Proof.
move=> f; rewrite /bool_fun_of_row /row_of_bool_fun.
by apply/ffunP => v; rewrite ffunE mxE ord_of_bool_vecK.
Qed.

Lemma bool_fun_of_row_bij : bijective bool_fun_of_row.
Proof.
by exists row_of_bool_fun; [apply: bool_fun_of_rowK|apply: row_of_bool_funK].
Qed.

Lemma row_of_bool_fun_bij : bijective row_of_bool_fun.
Proof.
by exists bool_fun_of_row; [apply: row_of_bool_funK|apply: bool_fun_of_rowK].
Qed.

(** Distribution of [2^n] Bernoulli trials with parameter [p],
    in terms of Boolean functions. *)
Definition dist_Bernoulli : {dist bool_fun n} :=
  dist_img bool_fun_of_row dist_Bernoulli_aux.

Definition num_true (f : bool_fun n) := #|finset_of_bool_fun f|.

Definition num_false (f : bool_fun n) := #|~: finset_of_bool_fun f|.

Lemma num_falseE f : num_false f = (2^n - num_true f)%N.
Proof. by rewrite /num_false /num_true cardsCs card_bool_vec setCK. Qed.

Fact dist_BernoulliE f :
  dist_Bernoulli f = p ^ (num_true f) * (1 - p) ^ (num_false f).
Proof.
rewrite /dist_Bernoulli /dist_img /=.
rewrite /dist_Bernoulli_aux /TupleDist.d /Pr /=.
rewrite /TupleDist.f num_falseE.
underp big a rewrite in_set.
rewrite (reindex row_of_bool_fun) /=; last first.
  apply: onW_bij; exact: row_of_bool_fun_bij.
underp big j rewrite row_of_bool_funK.
rewrite big_pred1_eq.
under big i _ rewrite ffunE /row_of_bool_fun mxE.
rewrite (reindex ord_of_bool_vec) /=; last first.
  apply: onW_bij; exact: ord_of_bool_vec_bij.
under big j _ rewrite ord_of_bool_vecK val0_bool.
rewrite (bigID f predT) /=.
under big i Hi rewrite Hi eqxx qqE.
rewrite bigmul_card_constE.
under big i Hi rewrite (negbTE Hi) /=.
rewrite bigmul_card_constE /=.
rewrite /num_true.
congr Rmult; congr pow.
{ by rewrite cardsE. }
rewrite -num_falseE /num_false.
apply: eq_card => i /=.
by rewrite !inE. (* . *)
Qed.

End Bernoulli_process_def.

Let P := dist_Bernoulli.

(** First, assume that the strategy a of A is fixed.
    What is the probability that it is winning? *)

Lemma Pr_set1 (S : {set bool_vec n}) :
  Pr P [set bool_fun_of_finset S] = p ^ #|S| * (1 - p) ^ (2^n - #|S|).
Proof.
rewrite /Pr /P big_set1 dist_BernoulliE num_falseE /num_true.
by rewrite bool_fun_of_finsetK.
Qed.

Variable k : nat.

Context `{Hkn : !leq_class k n}.

Global Instance Hnkn : leq_class (n - k) n | 99.
Proof. exact: leq_subr. Qed.

Section strategy_a_fixed.

Variable a : bg_StratA k.

Let knk_eqn : (k + (n - k) = n)%N.
Proof. by apply: subnKC. Qed.

Let eqn_knk : (n = k + (n - k))%N.
Proof. by rewrite knk_eqn. Qed.

Lemma Pr_implies0_Bern (S : {set bool_vec n}) :
  Pr P [set F | bool_fun_of_finset S ⇒0 F] =
  p ^ #|S|.
Proof.
rewrite /Pr /W_.
rewrite (reindex_onto (@bool_fun_of_finset n) (@finset_of_bool_fun n));
  last by move=> i _; rewrite finset_of_bool_funK.
underp big j rewrite inE bool_fun_of_finsetK eqxx andbT implies0E !bool_fun_of_finsetK.
under big j _ rewrite dist_BernoulliE num_falseE /num_true !bool_fun_of_finsetK.
rewrite (reindex_onto (fun s => s :|: S) (fun s => s :\: S)); last first.
{ by move=> i Hi; rewrite setUDKl; apply/setUidPl. }
have Heq :
  forall j, ((S \subset j :|: S) && ((j :|: S) :\: S == j)) = (j \subset ~: S).
{ move=> j; rewrite setDUKr setDE subsetUr /=; by apply/eqP/idP; move/setIidPl. }
underp big j rewrite Heq.
rewrite (partition_big
           (fun i : {set bool_vec n} => @inord (2^n) #|i|)
           (fun j => (j <= 2^n - #|S|)%N)) /=; last first.
{ move=> i /subset_leq_card Hle; rewrite inordK; last first.
  { by rewrite ltnS -card_bool_vec max_card. }
  by rewrite [#|~: S|]cardsCs setCK card_bool_vec in Hle. }
swap under big j Hj under big i Hi rewrite (_ : #|i :|: S| = j + #|S|)%N.
{ rewrite cardsU.
  have {Hi} /andP [Hic /eqP Hij] := Hi.
  move/(congr1 val) in Hij.
  rewrite /= inordK in Hij.
  2: by rewrite ltnS -card_bool_vec max_card.
  rewrite -disjoints_subset -setI_eq0 in Hic.
  by rewrite Hij (eqP Hic) cards0 subn0. }
under big j Hj rewrite bigsum_card_constE.
swap under big j Hj rewrite (_ : INR _ = INR 'C(#|~: S|, j)).
{ congr INR; rewrite -cards_draws -cardsE.
  apply: eq_card => i; rewrite !inE unfold_in; congr andb.
  apply/eqP/eqP; last move->.
  - move/(congr1 val); rewrite /= inordK //.
    by rewrite ltnS -card_bool_vec max_card.
  - by rewrite inord_val. }
swap under big j _ rewrite [(j + #|S|)%N]addnC subnDA
  (_ : ?[a] * (p ^ (#|S| + j) * ?[b]) = p^#|S| * (?a * (?b * p^j))).
{ by rewrite addnE pow_add; ring. }
rewrite -big_distrr /=.
under big j _ rewrite [#|~: S|]cardsCs setCK card_bool_vec /=.
rewrite (reindex_onto (fun j : 'I_(2^n - #|S|).+1 => @inord (2^n) j)
                      (fun i : 'I_(2^n).+1 => @inord (2^n - #|S|) i)) /=;
  last by move=> i Hi; rewrite inordK ?ltnS // inord_val.
have SC : forall j : 'I_(2 ^ n - #|S|).+1, (j < (2 ^ n).+1)%N.
{ by case => j Hj /=; rewrite ltnS in Hj; rewrite ltnS;
  apply: leq_trans Hj (leq_subr _ _). }
swap under big j _ rewrite inordK //.
underp big j set lhs := LHS; suff->: lhs = true.
{ by rewrite -RPascal qpE pow1 Rmult_1_r. }
rewrite {}/lhs; rewrite inordK //; last first.
rewrite inord_val eqxx andbT.
by case: j.
Qed.

Lemma card_w_a_Bern : #|finset_of_bool_fun (w_ a)| = (2 ^ (n - k))%N.
Proof.
rewrite /w_ /finset_of_bool_fun (eq_set (ffunE _)).
pose f := fun b : bg_StratB n k => bool_vec_of_bg_strategy (a, b).
pose g := fun v : bool_vec n => (bg_strategy_of_bool_vec v).2.
set lhs := LHS; suff ->: lhs = #|[seq (@f Hkn) x | x in predT]|.
{ rewrite card_image /f; first by rewrite card_ffun card_bool card_ord.
  move=> x y /(congr1 (@bg_strategy_of_bool_vec _ _ _)).
  rewrite !bool_vec_of_bg_strategyK.
  by case. }
rewrite /lhs /f.
apply: eq_card => x; rewrite !inE.
apply/forallP/imageP => /=.
- move=> H; exists (bg_strategy_of_bool_vec x).2 =>//.
  rewrite -[LHS]bg_strategy_of_bool_vecK.
  f_equal.
  rewrite [LHS]surjective_pairing.
  f_equal.
  apply/ffunP => /= v; rewrite !ffunE.
  exact/eqP/H.
- case => [x0 _ Hx0]; rewrite Hx0 => i; rewrite /bool_vec_of_bg_strategy ffunE.
  case: splitP; first by move=> j /= /ord_inj ->.
  move=> j /= Hj; exfalso.
  case: i Hj => i Hi /= Hj.
  by rewrite Hj ltnNge leq_addr in Hi.
Qed.

Theorem Pr_winA_Bern :
  Pr P [set F | winA (bool_game_of_bool_fun F) a] =
  p ^ (2 ^ (n - k)).
Proof.
set setF := [set F | _ _ a].
have {setF} ->: setF = (W_ a).
{ by apply/setP => v; rewrite /setF !inE winA_eq /W_ inE. }
by rewrite /W_ -[w_ a]finset_of_bool_funK Pr_implies0_Bern card_w_a_Bern.
Qed.

End strategy_a_fixed.

Lemma big_implies0 (J : {set bg_StratA k}) :
  \bigcap_(a in J) [set w | w_ a ⇒0 w] =
  [set w | bool_fun_of_finset (\bigcup_(a in J) finset_of_bool_fun (w_ a)) ⇒0 w].
Proof.
apply/setP => /= w; rewrite inE; apply/bigcapP/idP.
{ move=> Hw; rewrite implies0E bool_fun_of_finsetK.
  apply/subsetP => y /bigcupP [a Ha Hya].
  move/(_ a Ha) in Hw; rewrite inE implies0E in Hw.
  exact: (subsetP Hw). }
rewrite implies0E bool_fun_of_finsetK => Hw a Ha; rewrite inE implies0E.
by apply subset_trans with (1 := bigcup_sup a Ha) (2 := Hw).
Qed.

Lemma w_trivIset : forall J : {set bg_StratA k},
  trivIset [set finset_of_bool_fun (w_ a) | a in J].
Proof.
move=> J; apply/trivIsetP => A B HA HB HAB.
have {HA} /imsetP [a Ha Hwa] := HA.
have {HB} /imsetP [b Hb Hwb] := HB.
rewrite {}Hwa {}Hwb in HAB *.
rewrite -setI_eq0.
apply/set0Pn; case => [x /setIP [Hxa Hxb]].
move/negP: HAB; apply; apply/eqP.
suff->: a = b by done.
apply/ffunP => v.
move: Hxa Hxb; rewrite /w_ !inE !ffunE.
by do 2![move/forallP/(_ v)/eqP <-].
Qed.

Theorem Pr_ex_winA_Bern :
  Pr P [set F | [exists a : bg_StratA k, winA (bool_game_of_bool_fun F) a]] =
  1 - (1 - p ^ (2 ^ (n - k))) ^ (2 ^ k).
Proof.
rewrite Pr_ex_winA /W_.
have prelim :
  forall J : {set bg_StratA k},
  {in J &, injective (fun i0 : bool ^ k => finset_of_bool_fun (w_ i0))}.
{ move=> J x y Hx Hy /(congr1 (@bool_fun_of_finset n)).
  rewrite !finset_of_bool_funK; exact: w_inj. }
under big i _ under big J _
  rewrite big_implies0 Pr_implies0_Bern -(big_imset id) //=.
rewrite big_nat.
under big i Hi under big J HJ rewrite -(eqP (w_trivIset J)).
rewrite -big_nat.
under big i _ under big J _ rewrite big_imset;
  [under big j _ rewrite card_w_a_Bern|done].
under big i _ under big J HJ rewrite sum_nat_const (eqP (proj2 (andP HJ))).
do [under big i _ rewrite bigsum_card_constE (_ : INR _ = INR 'C(2^k, i))];
  last first.
{ congr INR.
  by rewrite -cardsE card_draws card_bool_vec. }
rewrite [LHS](_ : _ = 1 -
  \rsum_(i<(2^k).+1) INR 'C(2^k, i) * (1 ^ (2^k - i) * (- p ^ (2^(n-k))) ^ i)).
{ by rewrite -RPascal. }
rewrite big_add1 big_mkord /= [in RHS]big_ord_recl /=.
rewrite bin0 pow1 !Rmult_1_r -[INR 1]/R1 /Rminus Ropp_plus_distr -Rplus_assoc.
rewrite Rplus_opp_r Rplus_0_l.
rewrite (big_morph Ropp (id1 := R0) (op1 := Rplus)); first last.
  by rewrite Ropp_0.
  by move=> *; rewrite Ropp_plus_distr.
apply: eq_bigr => i _; rewrite /bump add1n subn1 /=.
rewrite pow1 [(i.+1 * _)%N]mulnC pow_muln [in RHS]pow_opp /=.
ring.
Qed.

Definition winB (g : bool_game n k) (b : bg_StratB n k) : bool :=
  [forall a : bg_StratA k, g (a, b) == false].

(** [bg_StratB n (n - k)] is isomorphic to [bg_StratA k] *)

Definition bg_castAB (s : bg_StratA k) : bg_StratB n (n - k) :=
  ecast i (bg_StratA i) (esym (subKn Hkn)) s.

Definition bg_castBA (s : bg_StratB n (n - k)) : bg_StratA k :=
  ecast i (bg_StratA i) (subKn Hkn) s.

Lemma bg_cast_trans : forall m n p (s : bg_StratA m)
    (eq_mn : m = n) (eq_np : n = p),
  ecast i (bg_StratA i) (etrans eq_mn eq_np) s =
  ecast i (bg_StratA i) eq_np (ecast j (bg_StratA j) eq_mn s).
Proof.
move=> m n' p' s eq_mn eq_np.
case: n' / eq_mn eq_np.
by case: p' /.
Qed.

Lemma bg_castABK : cancel bg_castAB bg_castBA.
Proof.
rewrite /bg_castAB /bg_castBA => s.
rewrite -bg_cast_trans.
by rewrite (eq_axiomK (etrans _ _)).
Qed.

Lemma bg_castBAK : cancel bg_castBA bg_castAB.
Proof.
rewrite /bg_castAB /bg_castBA => s.
rewrite -bg_cast_trans.
by rewrite (eq_axiomK (etrans _ _)).
Qed.

Lemma bg_castAB_bij : bijective bg_castAB.
Proof.
by exists bg_castBA; [apply: bg_castABK|apply: bg_castBAK].
Qed.

Lemma bg_castBA_bij : bijective bg_castBA.
Proof.
by exists bg_castAB; [apply: bg_castBAK|apply: bg_castABK].
Qed.

(** Duality: [bool_game n (n - k)] is isomorphic to [bool_game n k] *)

Definition bool_game_sym (g : bool_game n k) : bool_game n (n - k) :=
  [ffun c => ~~ g (bg_castBA c.2, c.1)].

Definition bool_game_sym' (g : bool_game n (n - k)) : bool_game n k :=
  [ffun c => ~~ g (c.2, bg_castAB c.1)].

Lemma bool_game_symK : cancel bool_game_sym bool_game_sym'.
Proof.
move=> F; apply/ffunP => v; rewrite /bool_game_sym' /bool_game_sym.
rewrite !ffunE negbK /= bg_castABK.
by case: v.
Qed.

Lemma bool_game_sym'K : cancel bool_game_sym' bool_game_sym.
Proof.
move=> F; apply/ffunP => v; rewrite /bool_game_sym' /bool_game_sym.
rewrite !ffunE negbK /= bg_castBAK.
by case: v.
Qed.

Lemma bool_game_sym_bij : bijective bool_game_sym.
Proof.
by exists bool_game_sym'; [apply: bool_game_symK|apply: bool_game_sym'K].
Qed.

Lemma bool_game_sym'_bij : bijective bool_game_sym'.
Proof.
by exists bool_game_sym; [apply: bool_game_sym'K|apply: bool_game_symK].
Qed.

(** We can write [winB] in terms of the dual game [bool_game_sym] *)

Lemma winB_eq (g : bool_game n k) (b : bg_StratB n k) :
  winB g b = @winA n (n - k) (bool_game_sym g) b.
Proof.
rewrite /winB /winA /bool_game_sym.
apply/forallP/forallP => H a.
{ by rewrite ffunE; apply/negbT/eqP/H. }
by move: (H (bg_castAB a)); rewrite ffunE /= bg_castABK; move/negbTE/eqP.
Qed.

(** The dual of a boolean function [F] w.r.t parameter [k] *)

Definition bool_fun_sym (F : bool_fun n) : bool_fun n :=
  bool_fun_of_bool_game (bool_game_sym (@bool_game_of_bool_fun n k Hkn F)).

Definition bool_fun_sym' (F : bool_fun n) : bool_fun n :=
  bool_fun_of_bool_game (bool_game_sym' (@bool_game_of_bool_fun n _ Hnkn F)).

Lemma bool_fun_symK : cancel bool_fun_sym bool_fun_sym'.
Proof.
rewrite /bool_fun_sym /bool_fun_sym' => v.
by rewrite bool_fun_of_bool_gameK bool_game_symK bool_game_of_bool_funK.
Qed.

Lemma bool_fun_sym'K : cancel bool_fun_sym' bool_fun_sym.
Proof.
rewrite /bool_fun_sym /bool_fun_sym' => v.
by rewrite !(bool_fun_of_bool_gameK, bool_game_sym'K, bool_game_of_bool_funK).
Qed.

Lemma bool_fun_sym_bij : bijective bool_fun_sym.
Proof.
by exists bool_fun_sym'; [apply: bool_fun_symK|apply: bool_fun_sym'K].
Qed.

Lemma bool_fun_sym'_bij : bijective bool_fun_sym'.
Proof.
by exists bool_fun_sym; [apply: bool_fun_sym'K|apply: bool_fun_symK].
Qed.

End Proba_winning.

(** For proving [Pr_ex_winB_Bern], we need to close/reopen the section
as we'll use [Pr_ex_winA_Bern] with different values of [p] and [k] *)

Section Proba_winning1.

Variable n : nat.

Variable p : R.

Context `{Hp : !p_0_1_class p}.

Variable k : nat.

Context `{Hkn : !leq_class k n}.

(** The symmetric of a boolean vector [v] w.r.t parameter [k] *)

Definition swap_vec (v : bool_vec n) : bool_vec n :=
  bool_vec_of_bg_strategy
    ([ffun x => (bg_castBA x.2, x.1)] (@bg_strategy_of_bool_vec n (n - k) (Hnkn _ _) v)).

Definition swap_vec' (v : bool_vec n) : bool_vec n :=
  bool_vec_of_bg_strategy
    ([ffun x => (x.2, bg_castAB x.1)] (@bg_strategy_of_bool_vec n k Hkn v)).

Lemma swap_vecK : cancel swap_vec swap_vec'.
Proof.
rewrite /swap_vec /swap_vec' => v.
by rewrite !ffunE bool_vec_of_bg_strategyK bg_castBAK bg_strategy_of_bool_vecK.
Qed.

Lemma swap_vec'K : cancel swap_vec' swap_vec.
Proof.
rewrite /swap_vec /swap_vec' => v.
by rewrite !ffunE bool_vec_of_bg_strategyK bg_castABK bg_strategy_of_bool_vecK.
Qed.

Lemma swap_vec_bij : bijective swap_vec.
Proof.
by exists swap_vec'; [apply: swap_vecK|apply: swap_vec'K].
Qed.

Lemma swap_vec'_bij : bijective swap_vec'.
Proof.
by exists swap_vec; [apply: swap_vec'K|apply: swap_vecK].
Qed.

(** The symmetric of a boolean function [v] w.r.t parameter [k] (no negation) *)

Definition swap_fun (f : bool_fun n) : bool_fun n :=
  [ffun v => f (swap_vec v)].

Definition swap_fun' (f : bool_fun n) : bool_fun n :=
  [ffun v => f (swap_vec' v)].

Lemma swap_funK : cancel swap_fun swap_fun'.
Proof.
rewrite /swap_fun /swap_fun' => f.
by apply/ffunP => v; rewrite !ffunE swap_vec'K.
Qed.

Lemma swap_fun'K : cancel swap_fun' swap_fun.
Proof.
rewrite /swap_fun /swap_fun' => f.
by apply/ffunP => v; rewrite !ffunE swap_vecK.
Qed.

Lemma swap_fun_bij : bijective swap_fun.
Proof.
by exists swap_fun'; [apply: swap_funK|apply: swap_fun'K].
Qed.

Lemma swap_fun'_bij : bijective swap_fun'.
Proof.
by exists swap_fun; [apply: swap_fun'K|apply: swap_funK].
Qed.

Lemma swap_funE (f : bool_fun n) (v : bool_vec n) :
  swap_fun f v = ~~ @bool_fun_sym n k Hkn f v.
Proof. by rewrite /swap_fun /swap_vec /bool_fun_sym !ffunE negbK. Qed.

Lemma swap_fun'E (f : bool_fun n) (v : bool_vec n) :
  swap_fun' f v = ~~ @bool_fun_sym' n k Hkn f v.
Proof. by rewrite /swap_fun' /swap_vec' /bool_fun_sym' !ffunE negbK. Qed.

Lemma card_swap_fun F :
  #|finset_of_bool_fun F| = #|finset_of_bool_fun (swap_fun F)|.
Proof.
set rhs := RHS.
suff->: rhs = #|preimset swap_vec (mem (finset_of_bool_fun F))|.
{ rewrite !on_card_preimset //.
  by apply/onW_bij; exists id.
  exact/onW_bij/swap_vec_bij.
  by apply/onW_bij; exists id. }
apply: eq_card => v.
by rewrite !inE; rewrite /swap_fun ffunE.
Qed.

Lemma card_swap_fun' F :
  #|finset_of_bool_fun F| = #|finset_of_bool_fun (swap_fun' F)|.
Proof.
set rhs := RHS.
suff->: rhs = #|preimset swap_vec' (mem (finset_of_bool_fun F))|.
{ rewrite !on_card_preimset //.
  by apply/onW_bij; exists id.
  exact/onW_bij/swap_vec'_bij.
  by apply/onW_bij; exists id. }
apply: eq_card => v.
by rewrite !inE; rewrite /swap_fun' ffunE.
Qed.

Lemma dist_Bernoulli_symE F :
  @dist_Bernoulli n p Hp (@bool_fun_sym n k Hkn F) =
  @dist_Bernoulli n (1 - p)%Re _ F.
Proof.
rewrite !dist_BernoulliE Rmult_comm.
congr Rmult; congr pow; try by rewrite qqE.
{ rewrite /num_false /num_true card_swap_fun.
  by apply: eq_card => v; rewrite !inE swap_funE. }
rewrite /num_false /num_true card_swap_fun'.
by apply: eq_card => v; rewrite !inE swap_fun'E bool_fun_symK.
Qed.

Lemma dist_Bernoulli_sym'E F :
  @dist_Bernoulli n p Hp (@bool_fun_sym' n k Hkn F) =
  @dist_Bernoulli n (1 - p)%Re _ F.
Proof.
rewrite !dist_BernoulliE Rmult_comm.
congr Rmult; congr pow; try by rewrite qqE.
{ rewrite /num_false /num_true card_swap_fun'.
  by apply: eq_card => v; rewrite !inE swap_fun'E. }
rewrite /num_false /num_true card_swap_fun.
by apply: eq_card => v; rewrite !inE swap_funE bool_fun_sym'K.
Qed.

Let P := @dist_Bernoulli n p Hp.

Corollary Pr_ex_winB_Bern :
  Pr P [set F | [exists b : bg_StratB n k, winB (bool_game_of_bool_fun F) b]] =
  1 - (1 - (1 - p) ^ (2 ^ k)) ^ (2 ^ (n - k)).
Proof.
rewrite /Pr.
set lhs := LHS.
have->: lhs = \rsum_(a in [set F |
    [exists b, @winA n (n - k) (bool_game_of_bool_fun (bool_fun_sym F)) b]]) P a.
rewrite /lhs.
apply: eq_bigl.
{ move=> F; rewrite !in_set !bool_fun_of_bool_gameK.
  apply/existsP/existsP => -[x Hx]; exists x.
  by rewrite -winB_eq.
    by rewrite winB_eq. }
rewrite (reindex (fun F => bool_fun_sym' F)); last exact/onW_bij/bool_fun_sym'_bij.
underp big j rewrite inE bool_fun_sym'K.
under big j _ rewrite dist_Bernoulli_sym'E.
rewrite -{7}[k](subKn Hkn).
have <- := @Pr_ex_winA_Bern n (1 - p)%Re (@q_0_1 p Hp) (n - k) (Hnkn _ _).
by underp big j rewrite inE.
Qed.

(** ** Partial Information on the Opponent's Choices *)

Section parameter_s_fixed.

Variable s : nat.

Context `{Hsnk : !leq_class s (n - k)}.

(** We assume that player A knows the first [s] bits of the [n - k]
variables controlled by player B.

The "possible worlds" compatible with this assumption are represented
by an element [bs : bool_vec s] and all strategy profiles [(a, b)]
such that [b] satisfies [compat_knowing bs b].

Hence the following definitions. *)

Definition bg_known_StratB := bool_vec s.

Definition widen_s_nk : 'I_s -> 'I_(n - k) := widen_ord leq_prop.

Definition compat_knowing (bs : bg_known_StratB) (b : bg_StratB n k) : bool :=
  [forall i : 'I_s, b (widen_s_nk i) == bs i].

Definition winA_knowing
  (g : bool_game n k) (bs : bg_known_StratB) (a : bg_StratA k) : bool :=
  [forall b : bg_StratB n k, compat_knowing bs b ==> g (a, b)].

(*
Compute val (@widen_ord 1 2 erefl ord0).
Compute val (rshift 2 (@ord_max 1)).
*)

Definition rshift_nk_n (i : 'I_(n - k)) : 'I_n :=
  cast_ord (@knk_eqn _ _ Hkn) (rshift k i).

Definition w_knowing (bs : bg_known_StratB) : Omega n :=
  [ffun v : bool ^ n => [forall i : 'I_s, v (rshift_nk_n (widen_s_nk i)) == bs i]].

Local Instance leq_s_nk : leq_class s n.
Proof. apply: (leq_trans (n := n - k)) =>//; exact: Hnkn. Qed.

Local Instance leq_k_sn : leq_class k (n - s).
Proof. red in Hsnk |- *.
case: s Hsnk => [|s'] H'.
{ rewrite subn0; exact: Hkn. }
case: k H'  => [//|k'].
by rewrite !ltn_subRL !addSn addnC.
Qed.

(*
Lemma widen_s_nK x : rshift_nk_n (widen_s_nk x) = @widen_k_n n s _ x.
Proof.
rewrite /widen_k_n /rshift_nk_n /widen_s_nk.
apply/val_inj; rewrite /=.
Abort.
 *)

Definition rshift_s_n (i : 'I_(n - s)) : 'I_n :=
  cast_ord (@knk_eqn _ _ leq_s_nk) (rshift s i).

(* Use [bool_vec_of_bg_strategy] in a different context (refactor?) *)
Definition bool_vec_cat n k `{!leq_class k n} :
  {ffun 'I_k -> bool} * {ffun 'I_(n - k) -> bool} -> bool_vec n
  := @bool_vec_of_bg_strategy n k _.

Definition bool_vec_fst n k `{!leq_class k n} (v : bool_vec n) : bool_vec k :=
  (bg_strategy_of_bool_vec v).1.

Definition bool_vec_snd n k `{!leq_class k n} (v : bool_vec n) : bool_vec (n - k) :=
  (bg_strategy_of_bool_vec v).2.

Definition bool_vec_snd_nks (v : bool_vec n) : bool_vec (n - k - s) :=
  bool_vec_snd (bool_vec_snd v).

(*
(* sam := split and merge *)
Definition bool_vec_sam (v : bool_vec n) : bool_vec (n - s) :=
  @bool_vec_cat (n - s) k _ (bool_vec_fst v, bool_vec_snd v).
*)

Definition subnC : forall m n p, (m - n - p = m - p - n)%N.
Proof. clear=> m n p. by rewrite -!subnDA addnC. Qed.

Definition cast_bool_vecB : forall m n p (v : bool_vec (m - n - p)),
  bool_vec (m - p - n) :=
  fun m n p v =>
  ecast i (bool_vec i) (subnC m n p) v.

Definition bool_game_knowing (g : bool_game n k) (bs : bg_known_StratB) :
  bool_game (n - s) k :=
  [ffun c => g (c.1, (bool_vec_cat (bs, cast_bool_vecB c.2)))].

Lemma bool_vec_cast_trans : forall m n p (v : bool_vec m)
    (eq_mn : m = n) (eq_np : n = p),
  ecast i (bool_vec i) (etrans eq_mn eq_np) v =
  ecast i (bool_vec i) eq_np (ecast j (bg_StratA j) eq_mn v).
Proof.
move=> m n' p' v eq_mn eq_np.
case: n' / eq_mn eq_np.
by case: p' /.
Qed.

Lemma cast_bool_vecB_K :
  forall m n p, cancel (@cast_bool_vecB m n p) (@cast_bool_vecB m p n).
Proof.
clear=> m n p.
move=> x; rewrite /cast_bool_vecB.
rewrite -bool_vec_cast_trans.
by rewrite (eq_axiomK (etrans _ _)).
Qed.

Lemma bool_vec_sndK (bs : bool_vec s) (b : bool_vec (n - k)) :
  compat_knowing bs b ->
  bool_vec_cat (bs, bool_vec_snd b) = b.
Proof.
move/forallP => Hall.
apply/ffunP => i; rewrite !ffunE.
case: splitP => /= j H.
{ suff->: i = widen_s_nk j by symmetry; apply: (eqP (Hall j)).
  exact/ord_inj. }
rewrite ffunE; apply: congr1; exact/ord_inj.
Qed.

Lemma winA_knowingE g bs a :
  winA_knowing g bs a = winA (bool_game_knowing g bs) a.
Proof.
rewrite /winA_knowing /winA /bool_game_knowing.
apply/forallP/forallP => Hall b; rewrite ?ffunE /=.
{ apply (implyP (Hall _)); rewrite /compat_knowing.
  apply/forallP => i; apply/eqP.
  rewrite ffunE; case: splitP => j /=; first by move/ord_inj->.
  case: i => i Hi /= K; rewrite K in Hi *; exfalso.
  by rewrite ltnNge leq_addr in Hi. }
apply/implyP => Hc.
rewrite /compat_knowing in Hc.
pose b2 := cast_bool_vecB (@bool_vec_snd (n - k) s Hsnk b).
move/(_ b2): Hall; rewrite ffunE /=.
by rewrite /b2 cast_bool_vecB_K bool_vec_sndK.
Qed.

(* DRAFT

Definition WK_ (bs : bg_known_StratB) : {set Omega n} :=
  [set w : Omega n | (w_knowing bs) ⇒0 w].

Fact winA_knowing_eq :
  forall (f : Omega n) (a : bg_StratA k) (bs : bg_known_StratB),
  winA_knowing (bool_game_of_bool_fun f) bs a = (f \in WK_ bs).
Proof.
move=> f a bs; rewrite /winA_knowing /WK_ /w_knowing inE implies0E.
apply/forallP/subsetP => H /= x.
rewrite !inE !ffunE.
Show 2.
rewrite inE.
Admitted.

Lemma w_knowingE bs : w_knowing bs = @w_ (n - s) (n - k s) bs

Lemma w_knowingE bs :
  w_knowing bs = @w_ n s _ bs.
Proof.
apply/ffunP => v; rewrite !ffunE.
apply: eq_forallb => x; congr eq_op; apply congr1.
apply: val_inj =>/=.

Definition ex_winA_knowing (g : bool_game n k) (bs : bg_known_StratB) : bool :=
  [exists a : bg_StratA k, forall b : bg_StratB n k, compat_knowing bs b ==> g (a, b)].

*)

Let eqn_ks_nsk : (n = k + (s + (n - s - k)))%N.
Proof.
rewrite -{1}(@subnKC k n) //.
congr addn.
rewrite -{1}(@subnKC s (n - k)) //.
by rewrite subnC.
Qed.

Let k_nsk_eqn : (k + (n - s - k) = n - s)%N.
Proof. by rewrite knk_eqn. Qed.

Definition widen_ns_n : 'I_(n - s) -> 'I_n := widen_ord leq_prop.

(* Definition widen_nsk_ns : 'I_(n - s - k) -> 'I_(n - s) := widen_ord leq_prop. *)

Definition rshift_nsk_ns (i : 'I_(n - s - k)) : 'I_(n - s) :=
  cast_ord k_nsk_eqn (rshift k i).

(* Version 1
Definition bool_fun_knowing (F : bool_fun n) (bs : bg_known_StratB) :=
  bool_fun_of_bool_game (bool_game_knowing (bool_game_of_bool_fun F) bs).
 *)

Definition bool_fun_knowing (F : bool_fun n) (bs : bg_known_StratB)
  : bool_fun (n - s) :=
  [ffun v : bool ^ (n - s) =>
   F [ffun i : 'I_n => match split (cast_ord eqn_ks_nsk i) with
                      | inl ik => v (widen_k_n ik)
                      | inr isn => match split isn with
                                  | inl is0 => bs is0
                                  | inr insk => v (rshift_nsk_ns insk)
                                  end
                      end]].

Lemma bool_game_knowingE F bs :
  (bool_game_knowing (bool_game_of_bool_fun F) bs)
  = @bool_game_of_bool_fun (n - s) k _ (bool_fun_knowing F bs).
Proof.
(* by rewrite /bool_fun_knowing bool_fun_of_bool_gameK. *)
admit. (* TODO *)
Admitted.

Definition knowing_bool_fun (F : bool_fun (n - s) (* depends on bs…*))
  : bool_fun n :=
  [ffun c : bool ^ n => F [ffun i : 'I_(n - s) =>
                       if (val i < k)%N then c (widen_ns_n i)
                       else c (rshift_s_n i)]].

Lemma knowing_bool_funK bs : cancel knowing_bool_fun (bool_fun_knowing ^~ bs).
Proof.
move=> F.
rewrite /knowing_bool_fun.
apply/ffunP => v; rewrite !ffunE; apply congr1.
apply/ffunP => i; rewrite !ffunE.
case: ifP => Hif.
{ case: splitP=> /= j Hj.
  by apply congr1; apply: val_inj; rewrite /= Hj.
  case: splitP => l Hl /=.
  { exfalso; clear - Hif j Hj.
    suff : (k + j < k)%N by rewrite ltnNge leq_addr.
    by rewrite -Hj /= Hif. }
  apply congr1; apply: val_inj; rewrite /= Hj.
  { exfalso; clear - Hif j Hj.
    suff : (k + j < k)%N by rewrite ltnNge leq_addr.
    by rewrite -Hj /= Hif. } }
case: splitP=> j Hj /=.
{ exfalso; clear - Hif j Hj.
  move/negbT in Hif; rewrite -leqNgt in Hif.
  suff : (k < k)%N by rewrite ltnn.
  apply: leq_ltn_trans Hif (leq_ltn_trans _ (ltn_ord j)).
  by rewrite -Hj leq_addl. }
case: splitP => /= l Hl.
{ exfalso; clear - Hif j Hj l Hl.
  simpl in Hj.
  suff : (s + i > k + j)%N by rewrite Hj ltnn.
  rewrite -addnS addnC; apply: leq_add; first by rewrite Hl; exact: ltn_ord.
  by rewrite leqNgt; apply/negbT. }
apply congr1; apply: val_inj; rewrite /=.
simpl in Hj.
by apply/eqP; rewrite -(eqn_add2l s) {}Hj {}Hl !addnA (addnC s k).
Qed.

(*
Lemma bool_fun_knowingK bs : cancel (bool_fun_knowing ^~ bs) knowing_bool_fun.
Proof.
move=> F.
rewrite /bool_fun_knowing.
apply/ffunP => v; rewrite !ffunE; apply congr1.
apply/ffunP => i; rewrite !ffunE.
case: splitP=> /= j Hj.
{ rewrite !ffunE.
  rewrite ifT; first by apply congr1; apply: val_inj; rewrite /= Hj.
  simpl; exact: ltn_ord. }
case: splitP => l Hl /=.
admit.
Abort.
 *)

Definition knowing (bs : bg_known_StratB) (F : bool_fun n) : bool :=
  knowing_bool_fun (bool_fun_knowing F bs) == F.

Lemma Pr_isom_knowing_Bern bs Q :
  Pr P [set F | Q (bool_fun_knowing F bs) (*  && knowing bs F *)] =
  @Pr _ (@dist_Bernoulli (n - s) p Hp) [set F | Q F].
Proof.
rewrite /P /Pr.
under big a _ rewrite dist_BernoulliE.
under big a _ rewrite dist_BernoulliE.
underp big a rewrite in_set.
underp big a rewrite in_set.
simpl.
rewrite (reindex_onto
           (fun a : {ffun bool ^ (n) -> bool} => bool_fun_knowing a bs)
           (fun a : {ffun bool ^ (n - s) -> bool} => knowing_bool_fun a)); last first.
{ by move=> i Hi; rewrite knowing_bool_funK. }
simpl.
(* apply eq_bigr => i Hi.
rewrite /num_true.
admit. *)
Admitted.

Lemma Pr_indep_knowing_Bern Q :
  Pr P [set F | [forall bs, Q (bool_fun_knowing F bs)]] =
  \rmul_(bs in bg_known_StratB) Pr P [set F | Q (bool_fun_knowing F bs)].
Proof.
stepr (Pr P (\bigcap_(bs in bg_known_StratB) [set F | Q (bool_fun_knowing F bs)])).
{ rewrite /Pr.
  apply: eq_bigl => x; rewrite in_set; apply/forallP/bigcapP => H y.
  { rewrite inE => _; apply: H. }
  have := H y; rewrite inE; exact. }
now_show (Pr P (\bigcap_(bs in bg_known_StratB)
            [set F | Q (bool_fun_knowing F bs)]) =
         \rmul_(bs in bg_known_StratB) Pr P
            [set F | Q (bool_fun_knowing F bs)]).

(*
  underp big a rewrite in_set.
stepr \r
underp big a rewrite in_set.
symmetry; (under big bs _ underp big a rewrite in_set); symmetry.
rewrite /= /Pr.
symmetry; (under big bs _ underp big a rewrite in_set); symmetry.
under big bs _ rewrite set1
rewrite /TupleDist.f num_falseE.
underp big a rewrite in_set.
rewrite (reindex row_of_bool_fun) /=; last first.
  apply: onW_bij; exact: row_of_bool_fun_bij.
underp big j rewrite row_of_bool_funK.
rewrite big_pred1_eq.
under big i _ rewrite ffunE /row_of_bool_fun mxE.
rewrite (reindex ord_of_bool_vec) /=; last first.
  apply: onW_bij; exact: ord_of_bool_vec_bij.
under big j _ rewrite ord_of_bool_vecK val0_bool.
rewrite (bigID f predT) /=.
under big i Hi rewrite Hi eqxx qqE.
rewrite bigmul_card_constE.
under big i Hi rewrite (negbTE Hi) /=.
rewrite bigmul_card_constE /=.
rewrite /num_true.
congr Rmult; congr pow.
{ by rewrite cardsE. }
rewrite -num_falseE /num_false.
apply: eq_card => i /=.
by rewrite !inE. (* . *)
*)
Admitted.

Theorem Pr_ex_winA_knowing_Bern :
  Pr P [set F | [forall bs, exists a : bg_StratA k, winA_knowing (bool_game_of_bool_fun F) bs a]] =
  (1 - (1 - p ^ (2 ^ (n - s - k))) ^ (2 ^ k)) ^ 2 ^ s.
Proof.
stepr (Pr P [set F | [forall bs, exists a, winA (bool_game_of_bool_fun (bool_fun_knowing F bs)) a]]).
{ apply: eq_bigl => F; rewrite !inE.
  apply: eq_forallb => bs.
  apply: eq_existsb => a.
    by rewrite winA_knowingE bool_game_knowingE. }
pose Q := (fun F' => [exists a, winA (bool_game_of_bool_fun F') a]).
rewrite (Pr_indep_knowing_Bern (Q _ _ _)).
under big bs _ rewrite (Pr_isom_knowing_Bern bs (Q _ _ _)).
under big bs _ rewrite Pr_ex_winA_Bern.
rewrite bigmul_card_constE.
by rewrite !(card_ffun, card_bool, card_ord).
Qed.

End parameter_s_fixed.

End Proba_winning1.
