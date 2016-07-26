From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div choice fintype tuple finfun bigop.
From mathcomp Require Import prime binomial ssralg.

(* Erik Martin-Dorel, 2016 *)

(** * Tactic for rewriting under bigops *)

(** ** When the bigop appears in the goal *)

(** [under_big] allows one to apply a given tactic under the bigop
    that correspond to the specified arguments. *)
Ltac under_big b tac :=
  let b' := eval hnf in b in
  match b' with
  | @BigOp.bigop ?R ?I ?idx ?r ?f =>
    match f with
    | fun i => @BigBody ?R ?I i ?op (@?P i) (@?F1 i) =>
      (* erewrite (@eq_bigr R idx op I r P F1 _); (*not robust enough*) *)
      pattern b;
      match goal with
      | [|- ?G b] =>
        refine (@eq_rect_r _ _ G _ b (@eq_bigr R idx op I r P F1 _ _));
        [|tac;
          try reflexivity (* instead of "; first reflexivity" *) ];
        cbv beta
      end
    end
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

(** [underbig] allows one to apply a given tactic under some bigop:
    if [pat] is a local variable (let-in) that appears in the goal,
    only the occurrences of [pat] will be rewritten;
    otherwise the occurrences of the first bigop that matches [pat]
    will be rewritten. *)
Tactic Notation "underbig" open_constr(pat) tactic(tac) :=
  tryif match goal with [|- context [pat]] => is_var pat end
  then under_big pat tac
  else find_pat pat ltac:(fun b => under_big b tac).

(** ** When the bigop appears in some hypothesis *)

(** [under_big_in] allows one to apply a given tactic under the bigop
    that correspond to the specified arguments, in some hypothesis *)
Ltac under_big_in b H tac :=
  let b' := eval hnf in b in
  match b' with
  | @BigOp.bigop ?R ?I ?idx ?r ?f =>
    match f with
    | fun i => @BigBody ?R ?I i ?op (@?P i) (@?F1 i) =>
      (* erewrite (@eq_bigr R idx op I r P F1 _); (*not robust enough*) *)
      pattern b in H;
      match type of H with
      | ?G b =>
        let e := fresh in
        let new := fresh in
        refine (let e := G _ in _);
        shelve_unifiable;
        suff new : e;
        [ try clear H ; try rename new into H
        | refine (@eq_rect _ _ G H _ (@eq_bigr R idx op I r P F1 _ _));
          tac;
          try reflexivity (* instead of "; first reflexivity" *)
        ]; try unfold e in * |- *; try clear e ; cbv beta
      end
    end
  end.

Ltac find_pat_in pat H tac :=
  match type of H with context [?x] =>
    unify pat x with typeclass_instances;
    tryif tac x then idtac else fail 2
end.

(** [underbig…in] allows one to apply a given tactic under some bigop:
    if [pat] is a local variable (let-in) that appears in H,
    only the occurrences of [pat] will be rewritten;
    otherwise the occurrences of the first bigop that matches [pat]
    will be rewritten. *)
Tactic Notation "underbig" open_constr(pat) "in" hyp(H) tactic(tac) :=
  tryif match type of H with context [pat] => is_var pat end
  then under_big_in pat H tac
  else find_pat_in pat H ltac:(fun b => under_big_in b H tac).

(** ** Tests *)

(* A test lemma covering several testcases. *)
Lemma test1 (n : nat) (R : ringType) (f1 f2 g : nat -> R) :
  (\big[+%R/0%R]_(i < n) ((f1 i + f2 i) * g i) +
  \big[+%R/0%R]_(i < n) ((f1 i + f2 i) * g i) =
  \big[+%R/0%R]_(i < n) ((f1 i + f2 i) * g i) +
  \big[+%R/0%R]_(i < n) (f1 i * g i) + \big[+%R/0%R]_(i < n) (f2 i * g i))%R.
Proof.
set b1 := {2}(bigop _ _ _).
Fail underbig b1 move=> *; rewrite GRing.mulrDr.

underbig b1 move=> *; rewrite GRing.mulrDl. (* only b1 is rewritten *)

Undo 1. rewrite /b1.
underbig b1 move=> *; rewrite GRing.mulrDl. (* 3 occurrences are rewritten *)

rewrite big_split /=.
by rewrite GRing.addrA.
Qed.

(* A test with a side-condition. *)
Lemma test2 (n : nat) (R : fieldType) (f : nat -> R) :
  (forall k : 'I_n, f k != 0%R) ->
  (\big[+%R/0%R]_(i < n) (f i / f i) = n%:R)%R.
Proof.
move=> Hneq0.
underbig (bigop _ _ _) move=> *; rewrite GRing.divff.
2: done.

rewrite big_const cardT /= size_enum_ord /GRing.natmul.
case: {Hneq0} n =>// n.
by rewrite iteropS iterSr GRing.addr0.
Qed.

(* Another test lemma when the bigop appears in some hypothesis *)
Lemma test3 (n : nat) (R : fieldType) (f : nat -> R) :
  (forall k : 'I_n, f k != 0%R) ->
  (\big[+%R/0%R]_(i < n) (f i / f i) +
  \big[+%R/0%R]_(i < n) (f i / f i) = n%:R + n%:R)%R -> True.
Proof.
move=> Hneq0 H.
set b1 := {2}(bigop _ _ _) in H.
underbig b1 in H move=> i Hi; rewrite GRing.divff. (* only b1 is rewritten *)
done.

Undo 2.
move: H.
underbig (bigop _ _ _) move=> *; rewrite GRing.divff.
done.

move=> *; exact: Hneq0.
Qed.