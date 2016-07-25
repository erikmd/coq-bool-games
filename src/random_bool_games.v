Require Import Reals.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div choice fintype tuple finfun bigop.
From mathcomp Require Import prime binomial ssralg finset ssrint.
From Infotheo Require Import Reals_ext Rbigop proba.
Require Import bigop_tactics.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope R_scope.
Delimit Scope R_scope with Re.

Section Def.

Variable n : nat.

Definition bool_vec := (bool ^ n)%type.

Definition bool_fun := {ffun bool_vec -> bool}.

Definition ffun_of (s : {set bool_vec}) : bool_fun :=
  [ffun v => v \in s].

Definition DNF_of (s : {set bool_vec}) : bool_fun :=
  [ffun v : bool_vec => \big[orb/false]_(vs in s)
                        \big[andb/true]_(i < n) (if vs i then v i else ~~ v i)].

Lemma if_negb_eq a b : (if a then b else ~~ b) = (a == b).
Proof. by case: a; case: b. Qed.

Lemma DNF_ofE s : DNF_of s = ffun_of s.
Proof.
rewrite /DNF_of /ffun_of; apply/ffunP=> /= v; rewrite !ffunE; apply/idP/idP=> H.
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

Definition finset_of (f : bool_fun) : {set bool_vec} :=
  [set w : bool ^ n | f w].

Lemma finset_ofK : cancel finset_of ffun_of.
Proof.
by move=> f; rewrite /finset_of /ffun_of; apply/ffunP => v; rewrite ffunE inE.
Qed.

Lemma ffun_ofK : cancel ffun_of finset_of.
Proof.
by move=> s; rewrite /finset_of /ffun_of; apply/setP => v; rewrite inE ffunE.
Qed.

(** Definition 1.
    [w0 ⊆0 w1] := [w1] is true on [w0], i.e. on all elements of [w0] *)
Definition subseteq0 (w0 w1 : {set bool_vec}) := w0 \subset w1.

Infix "⊆0" := subseteq0 (at level 70).

Definition implies0 (w0 w1 : bool_fun) : Prop := forall i, w0 i -> w1 i.

Infix "⇒0" := implies0 (at level 70).

Definition subseteq1 (s0 s1 : {set {set bool_vec}}) := s0 \subset s1.

Infix "⊆1" := subseteq1 (at level 70).

Lemma subseteq0P : forall w1 w2, reflect (ffun_of w1 ⇒0 ffun_of w2) (w1 ⊆0 w2).
Proof.
move=> w1 w2.
apply: (iffP idP).
- by move/subsetP => H x; rewrite !ffunE; move: x.
- by move=> H; apply/subsetP => x; move/(_ x) in H; rewrite !ffunE in H.
Qed.

End Def.

Infix "⊆0" := (@subseteq0 _) (at level 70).
Infix "⇒0" := (@implies0 _) (at level 70).
Infix "⊆1" := (@subseteq1 _) (at level 70).

Section Proba_example.

Variable n : nat.

Let Omega_fun := bool_fun n.

Let Omega := {set bool_vec n}.

  Check @ffun_of n : Omega -> Omega_fun.
  Check @finset_of n : Omega_fun -> Omega.

Let sigmA := {set Omega}.

Variable P : dist [finType of Omega].

(* Definition P_of (E : sigmA) := \rsum_(a in E) P a. *)

Lemma example : forall w0, 0 <= Pr P [set w | w0 ⊆0 w].
Proof. move=> *; exact: le_0_Pr. Qed.

End Proba_example.

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

Hypothesis le_k_n : (k <= n)%N.

Let knk_eqn : (k + (n - k) = n)%N.
Proof. by apply: subnKC. Qed.

Let eqn_knk : (n = k + (n - k))%N.
Proof. by rewrite knk_eqn. Qed.

Definition bg_StratA := (bool_vec k)%type.

Definition bg_StratB := (bool_vec (n - k))%type.

Definition bg_Outc := bool.
(* [true] means player A wins *)

Definition bg_strategy := (bg_StratA * bg_StratB)%type.
(* [bg_strategy] is isomorphic to [bool_vec n] *)

Definition bool_vec_of (s : bg_strategy) : bool_vec n :=
  [ffun i : 'I_n => match split (cast_ord eqn_knk i) with
                    | inl ik => s.1 ik
                    | inr ink => s.2 ink
                    end].

(* TODO: name the function [widen_ord le_k_n]... *)
Definition bg_strategy_of (v : bool_vec n) : bg_strategy :=
  ([ffun ik : 'I_k => v (widen_ord le_k_n ik)],
   [ffun ink : 'I_(n - k) => v (cast_ord knk_eqn (rshift k ink))]).

Lemma bool_vec_ofK : cancel bool_vec_of bg_strategy_of.
Proof.
move=> s; rewrite /bool_vec_of /bg_strategy_of (surjective_pairing s).
congr pair; apply/ffunP => v; rewrite !ffunE.
- case: splitP => /= j; first by move/ord_inj->.
  case: v => [v Hv] /= => K; exfalso; rewrite K in Hv.
  by rewrite ltnNge leq_addr in Hv.
- case: splitP => /= j.
  + case: j => [j Hv] /= => K; exfalso; rewrite -K in Hv.
    by rewrite ltnNge leq_addr in Hv.
  + by move/eqP; rewrite eqn_add2l; move/eqP/ord_inj->.
Qed.

Lemma bg_strategy_ofK : cancel bg_strategy_of bool_vec_of.
Proof.
move=> v; rewrite /bg_strategy_of /bool_vec_of; apply/ffunP=> x; rewrite !ffunE.
by case: splitP=>/= j H; rewrite ffunE; apply: congr1; apply/ord_inj; rewrite H.
Qed.

Definition bg_game := {ffun bg_strategy -> bg_Outc}.
(* [bg_game] is isomorphic to [bool_fun n] *)

Definition bool_fun_of (g : bg_game) : bool_fun n :=
  [ffun i => g (bg_strategy_of i)].

Definition bg_game_of (f : bool_fun n) : bg_game :=
  [ffun s => f (bool_vec_of s)].

Lemma bool_fun_ofK : cancel bool_fun_of bg_game_of.
Proof.
move=> g; rewrite /bool_fun_of /bg_game_of; apply/ffunP => x; rewrite !ffunE.
by rewrite bool_vec_ofK.
Qed.

Lemma bg_game_ofK : cancel bg_game_of bool_fun_of.
Proof.
move=> f; rewrite /bool_fun_of /bg_game_of; apply/ffunP => x; rewrite !ffunE.
by rewrite bg_strategy_ofK.
Qed.

Definition Omega := bool_fun n.

Variable P : dist [finType of Omega].

Let sigmA := {set Omega}.

(*
Variable random_f : Omega.
Definition g := bg_game_of random_f.
*)

Definition bg_winA (g : bg_game) (a : bg_StratA) : bool :=
  [forall b : bg_StratB, g (a, b) (* == true *)].

Definition bg_winA_wide (g : bg_game) (s : bg_strategy) : bool :=
  bg_winA g s.1.

Definition w_ (a : bg_StratA) : Omega :=
  ffun_of [set w : bool ^ n | [forall i : 'I_k, w (widen_ord le_k_n i) == a i]].

Definition W_ (a : bg_StratA) : sigmA :=
  [set w : Omega | finset_of (w_ a) ⊆0 finset_of w].

Theorem winA_sigmA :
  forall (f : Omega) (a : bg_StratA),
  bg_winA (bg_game_of f) a = (f \in W_ a).
Proof.
move=> f a; rewrite /bg_winA /W_.
apply/forallP/idP =>/= H.
- rewrite inE /w_; apply/subseteq0P; rewrite !finset_ofK=> x; rewrite ffunE inE.
  move/forallP => H'.
  rewrite -(bg_game_ofK f) /bool_fun_of ffunE.
  have->: bg_strategy_of x = (a, (bg_strategy_of x).2).
    rewrite [LHS]surjective_pairing; congr pair.
    rewrite /bg_strategy_of /=.
    apply/ffunP => ik; rewrite !ffunE.
    by apply/eqP; exact: H'.
  exact: H.
- rewrite inE /w_ in H; move/subseteq0P in H; rewrite !finset_ofK in H.
  move=> x; move/(_ (bool_vec_of (a, x))) in H.
  rewrite ffunE inE in H; rewrite /bg_game_of ffunE; apply: H.
  apply/forallP => y; rewrite /bool_vec_of ffunE.
  case: splitP => j /=; first by move/ord_inj<-.
  case: y => [y Hy] /= => K; exfalso; rewrite K in Hy.
  by rewrite ltnNge leq_addr in Hy.
Qed.

Corollary ex_winA_sigmA :
  forall (f : Omega),
  [exists a : bg_StratA, bg_winA (bg_game_of f) a] =
  (f \in \bigcup_(a in bg_StratA) W_ a).
Proof.
move=> f.
apply/existsP/bigcupP.
- by case=> a Ha; exists a =>//; rewrite -winA_sigmA.
- by case=> a Ha Hb; exists a =>//; rewrite winA_sigmA.
Qed.

End Proba_games.

Section probability_inclusion_exclusion.
(** In this section we prove the formula of inclusion-exclusion.
    This result is more general than lemma [Pr_bigcup] in Infotheo. *)
Variable A : finType.
Variable P : dist A.

Variables (B : finType) (E : nat -> {set A}) (n : nat).

Let Pr_capE (n : nat) (k : nat) := \rsum_(J in {set 'I_n} | #|J| == k) Pr P (\bigcap_(j in J) E j).

Lemma setDUKr (E1 E2 : {set A}) : (E1 :|: E2) :\: E2 = E1 :\: E2.
Proof. by rewrite setDUl setDv setU0. Qed.

Lemma setDUKl (E1 E2 : {set A}) : (E1 :|: E2) :\: E1 = E2 :\: E1.
Proof. by rewrite setDUl setDv set0U. Qed.

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

Lemma predSn (p : nat) : p.+1.-1 = p.
Proof. by []. Qed.

Definition Ind (s : {set A}) (x : A) : R := if x \in s then R1 else R0.

(** Expected value of a random variable [X], in the finite case *)
Definition Exp (X : A -> R) := \rsum_(a in A) X a * P a.

Lemma Exp_Ind s : Exp (Ind s) = Pr P s.
Proof.
rewrite /Exp /Ind /Pr (bigID (mem s)) /=.
rewrite [X in _ + X = _]big1; last by move=> i /negbTE ->; rewrite Rmult_0_l.
by rewrite Rplus_0_r; apply: eq_bigr => i ->; rewrite Rmult_1_l.
Qed.

Lemma Exp_ext X2 X1 : X1 =1 X2 -> Exp X1 = Exp X2.
Proof. by move=> Heq; rewrite /Exp; apply: eq_bigr => i Hi; rewrite Heq. Qed.

Lemma Exp_add X1 X2 : Exp (fun w => X1 w + X2 w) = Exp X1 + Exp X2.
Proof.
by rewrite /Exp; set b := LHS; underbig b rewrite Rmult_plus_distr_r; rewrite big_split.
Qed.

Lemma Exp_rsum I r p (X : I -> A -> R) :
  Exp (fun x => \big[Rplus/R0]_(i <- r | p i) X i x) =
  \big[Rplus/R0]_(i <- r | p i) (Exp (X i)).
Proof.
rewrite /Exp exchange_big /=; apply: eq_bigr => i Hi.
by rewrite big_distrl /=.
Qed.

Lemma Exp_scaler X1 r2 : Exp (fun w => X1 w * r2) = Exp X1 * r2.
Proof.
rewrite /Exp big_distrl /=; apply: eq_bigr => i Hi.
by rewrite !Rmult_assoc; congr Rmult; rewrite Rmult_comm.
Qed.

Lemma Exp_scalel r1 X2 : Exp (fun w => r1 * X2 w) = r1 * Exp X2.
Proof.
rewrite /Exp big_distrr /=; apply: eq_bigr => i Hi.
by rewrite !Rmult_assoc; congr Rmult; rewrite Rmult_comm.
Qed.

Let Ind_capE (n : nat) (k : nat) (x : A) :=
  \rsum_(J in {set 'I_n} | #|J| == k) (Ind (\bigcap_(j in J) E j) x).

Lemma bigcup_incl_excl (x : A) :
  Ind (\bigcup_(i < n) E i) x =
  (\rsum_(1 <= k < n.+1) ((-1)^(k-1) * (Ind_capE n k x)))%Re.
Proof.
Admitted.

Lemma Ind_capE_correct k : Exp (Ind_capE n k) = Pr_capE n k.
rewrite /Ind_capE /Pr_capE Exp_rsum; apply: eq_bigr => i Hi.
by rewrite Exp_Ind.
Qed.

Theorem Pr_bigcup_incl_excl :
  Pr P (\bigcup_(i < n) E i) = \big[Rplus/0]_(1 <= k < n.+1) ((-1)^(k-1) * Pr_capE n k).
Proof.
rewrite -Exp_Ind.
set b := LHS; underbig b rewrite bigcup_incl_excl; clear b.
rewrite -/(Exp _) Exp_rsum.
apply: eq_bigr => i _.
by rewrite Exp_scalel Ind_capE_correct.
Qed.
