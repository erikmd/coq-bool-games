From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div choice fintype tuple finfun bigop.
From mathcomp Require Import prime binomial ssralg.

(* Erik Martin-Dorel, 2016 *)

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
        [|let i := fresh "i" in
          let Hi := fresh "Hi" in
          move=> i Hi; tac; move: i Hi;
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
Tactic Notation "underbig" open_constr(pat) tactic1(tac) :=
  tryif match goal with [|- context [pat]] => is_var pat end
  then under_big pat tac
  else find_pat pat ltac:(fun b => under_big b tac).

(* TODO: underbig b in H ... *)

(* A test lemma covering several testcases. *)
Lemma test1 (n : nat) (R : ringType) (f1 f2 g : nat -> R) :
  (\big[+%R/0%R]_(i < n) ((f1 i + f2 i) * g i) +
  \big[+%R/0%R]_(i < n) ((f1 i + f2 i) * g i) =
  \big[+%R/0%R]_(i < n) ((f1 i + f2 i) * g i) +
  \big[+%R/0%R]_(i < n) (f1 i * g i) + \big[+%R/0%R]_(i < n) (f2 i * g i))%R.
Proof.
set b1 := {2}(\big[_/_]_(i < n) _).
Fail underbig b1 rewrite GRing.mulrDr.

underbig b1 rewrite GRing.mulrDl. (* only b1 is rewritten *)

Undo 1. rewrite /b1.
underbig b1 rewrite GRing.mulrDl. (* 3 occurrences are rewritten *)

rewrite big_split /=.
by rewrite GRing.addrA.
Qed.

(* A test with a side-condition. *)
Lemma test2 (n : nat) (R : fieldType) (f : nat -> R) :
  (forall k : 'I_n, f k != 0%R) ->
  (\big[+%R/0%R]_(i < n) (f i / f i) = n%:R)%R.
Proof.
move=> Hneq0.
underbig (\big[_/_]_i _) rewrite GRing.divff //.

rewrite big_const cardT /= size_enum_ord /GRing.natmul.
case: {Hneq0} n =>// n.
by rewrite iteropS iterSr GRing.addr0.
Qed.
