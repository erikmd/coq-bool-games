From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div choice fintype tuple finfun bigop.
From mathcomp Require Import prime binomial ssralg finset.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Erik Martin-Dorel, 2016 *)

(** * Tactic for rewriting under bigops *)

(** ** When the bigop appears in the goal *)

(** [under_big] allows one to apply a given tactic under the bigop
    that correspond to the specified arguments. *)
Ltac under_big b x Hx tac :=
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
        [|move=> x Hx; tac;
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
Tactic Notation "under" open_constr(pat) simple_intropattern(x) simple_intropattern(Hx) tactic(tac) :=
  tryif match goal with [|- context [pat]] => is_var pat end
  then under_big pat x Hx tac
  else find_pat pat ltac:(fun b => under_big b x Hx tac).

(** A shortcut when we want to rewrite the first occurrence of [bigop _ _ _] *)
Notation big := (bigop _ _ _) (only parsing).

(** ** When the bigop appears in some hypothesis *)

(** [under_big_in] allows one to apply a given tactic under the bigop
    that correspond to the specified arguments, in some hypothesis *)
Ltac under_big_in H b x Hx tac :=
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
          move=> x Hx; tac;
          try reflexivity (* instead of "; first reflexivity" *)
        ]; try unfold e in * |- *; try clear e ; cbv beta
      end
    end
  end.

Ltac find_pat_in H pat tac :=
  match type of H with context [?x] =>
    unify pat x with typeclass_instances;
    tryif tac x then idtac else fail 2
  end.

(** [underbig…in] allows one to apply a given tactic under some bigop:
    if [pat] is a local variable (let-in) that appears in H,
    only the occurrences of [pat] will be rewritten;
    otherwise the occurrences of the first bigop that matches [pat]
    will be rewritten. *)
Tactic Notation "under" open_constr(pat) "in" hyp(H) simple_intropattern(x) simple_intropattern(Hx) tactic(tac) :=
  tryif match type of H with context [pat] => is_var pat end
  then under_big_in H pat x Hx tac
  else find_pat_in H pat ltac:(fun b => under_big_in H b x Hx tac).

(** * Similar material, for the bigop predicates *)

(** ** When the bigop appears in the goal *)

(** [under_bigp] allows one to apply a given tactic for rewriting the
    predicate of the bigop corresponding to the specified arguments. *)
Ltac under_bigp b x tac :=
  let b' := eval hnf in b in
  match b' with
  | @BigOp.bigop ?R ?I ?idx ?r ?f =>
    match f with
    | fun i => @BigBody ?R ?I i ?op (@?P1 i) (@?F i) =>
      pattern b;
      match goal with
      | [|- ?G b] =>
        refine (@eq_rect_r _ _ G _ b (@eq_bigl R idx op I r P1 _ F _));
        [|move=> x; tac;
          try reflexivity (* instead of "; first reflexivity" *) ];
        cbv beta
      end
    end
  end.

(** [underbigp] allows one to apply a given tactic for rewriting
    some bigop predicate:
    if [pat] is a local variable (let-in) that appears in the goal,
    only the occurrences of [pat] will be rewritten;
    otherwise the occurrences of the first bigop that matches [pat]
    will be rewritten. *)
Tactic Notation "underp" open_constr(pat) simple_intropattern(x) tactic(tac) :=
  tryif match goal with [|- context [pat]] => is_var pat end
  then under_bigp pat x tac
  else find_pat pat ltac:(fun b => under_bigp b x tac).

(** ** When the bigop appears in some hypothesis *)

(** [under_bigp_in] allows one to apply a given tactic for rewriting the
    predicate of the bigop corresponding to the specified arguments,
    in some hypothesis *)
Ltac under_bigp_in H b x tac :=
  let b' := eval hnf in b in
  match b' with
  | @BigOp.bigop ?R ?I ?idx ?r ?f =>
    match f with
    | fun i => @BigBody ?R ?I i ?op (@?P1 i) (@?F i) =>
      pattern b in H;
      match type of H with
      | ?G b =>
        let e := fresh in
        let new := fresh in
        refine (let e := G _ in _);
        shelve_unifiable;
        suff new : e;
        [ try clear H ; try rename new into H
        | refine (@eq_rect _ _ G H _ (@eq_bigl R idx op I r P1 _ F _));
          move=> x; tac;
          try reflexivity (* instead of "; first reflexivity" *)
        ]; try unfold e in * |- *; try clear e ; cbv beta
      end
    end
  end.

(** [underbigp…in] allows one to apply a given tactic for rewriting
    some bigop predicate:
    if [pat] is a local variable (let-in) that appears in H,
    only the occurrences of [pat] will be rewritten;
    otherwise the occurrences of the first bigop that matches [pat]
    will be rewritten. *)
Tactic Notation "underp" open_constr(pat) "in" hyp(H) simple_intropattern(x) tactic(tac) :=
  tryif match type of H with context [pat] => is_var pat end
  then under_bigp_in H pat x tac
  else find_pat_in H pat ltac:(fun b => under_bigp_in H b x tac).

(** * Tests and examples *)

Section Tests.

(* A test lemma covering several testcases. *)
Let test1 (n : nat) (R : ringType) (f1 f2 g : nat -> R) :
  (\big[+%R/0%R]_(i < n) ((f1 i + f2 i) * g i) +
  \big[+%R/0%R]_(i < n) ((f1 i + f2 i) * g i) =
  \big[+%R/0%R]_(i < n) ((f1 i + f2 i) * g i) +
  \big[+%R/0%R]_(i < n) (f1 i * g i) + \big[+%R/0%R]_(i < n) (f2 i * g i))%R.
Proof.
set b1 := {2}(bigop _ _ _).
Fail under b1 ? _ rewrite GRing.mulrDr.

under b1 ? _ rewrite GRing.mulrDl. (* only b1 is rewritten *)

Undo 1. rewrite /b1.
under b1 ? _ rewrite GRing.mulrDl. (* 3 occurrences are rewritten *)

rewrite big_split /=.
by rewrite GRing.addrA.
Qed.

(* A test with a side-condition. *)
Let test2 (n : nat) (R : fieldType) (f : nat -> R) :
  (forall k : 'I_n, f k != 0%R) ->
  (\big[+%R/0%R]_(i < n) (f i / f i) = n%:R)%R.
Proof.
move=> Hneq0.
under big ? _ rewrite GRing.divff.
2: done.

rewrite big_const cardT /= size_enum_ord /GRing.natmul.
case: {Hneq0} n =>// n.
by rewrite iteropS iterSr GRing.addr0.
Qed.

(* Another test lemma when the bigop appears in some hypothesis *)
Let test3 (n : nat) (R : fieldType) (f : nat -> R) :
  (forall k : 'I_n, f k != 0%R) ->
  (\big[+%R/0%R]_(i < n) (f i / f i) +
  \big[+%R/0%R]_(i < n) (f i / f i) = n%:R + n%:R)%R -> True.
Proof.
move=> Hneq0 H.
set b1 := {2}big in H.
under b1 in H ? _ rewrite GRing.divff. (* only b1 is rewritten *)
done.

Undo 2.
move: H.
under b1 ? _ rewrite GRing.divff.
done.

move=> *; exact: Hneq0.
Qed.

(* A test lemma for [underbigp] *)
Let testp1 (A : finType) (n : nat) (F : A -> nat) :
  \big[addn/O]_(0 <= k < n)
  \big[addn/O]_(J in {set A} | #|J :&: [set: A]| == k)
  \big[addn/O]_(j in J) F j >= 0.
Proof.
under big ? _ underp big ? rewrite setIT.
done.
Qed.

(* A test lemma for [underbigp…in] *)
Let testp2 (A : finType) (n : nat) (F : A -> nat) :
  \big[addn/O]_(J in {set A} | #|J :&: [set: A]| == 1)
  \big[addn/O]_(j in J) F j = \big[addn/O]_(j in A) F j -> True.
Proof.
move=> H.
underp big in H ? rewrite setIT.
done.
Qed.

End Tests.
