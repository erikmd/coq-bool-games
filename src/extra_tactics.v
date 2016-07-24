From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div choice fintype tuple finfun bigop.
From mathcomp Require Import prime binomial ssralg.

(* Erik Martin-Dorel, 2016 *)

(** [under_big] allows one to apply a given tactic under the bigop
    that correspond to the specified arguments. *)
Ltac under_big b R idx op I r P F1 tac :=
  (* erewrite (@eq_bigr R idx op I r P F1 _); (*not robust enough*) *)
  pattern b;
  match goal with
  | [|- ?G b] =>
    refine (@eq_rect_r _ _ G _ _ (@eq_bigr R idx op I r P F1 _ _));
    [|let i := fresh "i" in
      let Hi := fresh "Hi" in
      intros i Hi; (tac || fail 5 "Cannot apply" tac); reflexivity];
    cbv beta
  end.

(* BEGIN 3rdparty *)
(** The following tactic can be used to add support for patterns to
tactic notation:
It will search for the first subterm of the goal matching [pat], and
then call [tac] with that subterm.

Posted by Ralf Jung on 2016-02-25 to the ssreflect mailing list.
*)
Ltac find_pat pat tac :=
  match goal with |- context [?x] =>
                  unify pat x with typeclass_instances;
                  tryif tac x then idtac else fail 2
end.
(* END 3rdparty *)

(** [underbig] allows one to apply a given tactic under the first
    bigop that matches the specified pattern *)
Tactic Notation "underbig" open_constr(pat) tactic(tac) :=
  find_pat pat ltac:(fun b =>
  let b' := eval hnf in b in change b with b';
  match b' with
  | @BigOp.bigop ?R ?I ?idx ?r ?f =>
    match f with
    | fun i => @BigBody ?R ?I i ?op (@?P i) (@?F1 i) =>
    under_big b' R idx op I r P F1 tac
    end
  end).

(* TODO: underbig b in H ... *)

Lemma test1 (n : nat) (R : ringType) (f1 f2 g : nat -> R) :
  (\big[+%R/0%R]_(i < n) ((f1 i + f2 i) * g i) =
  \big[+%R/0%R]_(i < n) (f1 i * g i) + \big[+%R/0%R]_(i < n) (f2 i * g i))%R.
Proof.
set b1 := LHS.
Fail underbig b1 rewrite GRing.mulrDr.
underbig b1 rewrite GRing.mulrDl.
by rewrite big_split.
Qed.
