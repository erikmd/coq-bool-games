(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div fintype tuple.
From mathcomp Require Import finfun bigop fingroup perm ssralg zmodp matrix mxalgebra.
From mathcomp Require Import poly mxpoly.
Require Import num_occ.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section AboutF2.

(** * Finite Field with Two Elements

   Prime finite fields are directly available in SSReflect.

*)

Local Open Scope ring_scope.

Coercion F2_of_bool (b : bool) : 'F_2 := if b then 1 else 0.

Definition bool_of_F2 (x : 'F_2) : bool := x != 0.

Definition negF2 (x : 'F_2) : 'F_2 := (*F2_of_bool*) (x == 0%R).

Lemma F2_0_1 : forall x : 'F_2, x = (x != 0).
Proof. move=> x; rewrite -{1}[x]natr_Zp; case: x; case=> //; by case. Qed.

Lemma F2_0_1' : forall x : 'F_2, ((x == 1)%R = (x != 0)%R).
Proof. move=> x; rewrite -{1}[x]natr_Zp; case: x; case=> //; by case. Qed.

Lemma F2_0_1'' : forall x : 'F_2, ((x == 0)%R = (x != 1)%R).
Proof. move=> x; rewrite -{1}[x]natr_Zp; case: x; case=> //; by case. Qed.

(* TODO: rename *)
Lemma F2_0_1''' : forall x : 'F_2, (bool_of_F2 x) = (x != 0)%R.
Proof. move=> x; rewrite -{1}[x]natr_Zp; case: x; case=> //; by case. Qed.
Lemma F2_0_1'''' : forall x : 'F_2, ~~ (bool_of_F2 x) = (x == 0)%R.
Proof. move=> x; rewrite -{1}[x]natr_Zp; case: x; case=> //; by case. Qed.

CoInductive F2_spec : 'F_2 -> bool -> bool -> Prop :=
| F2_0 : F2_spec 0 true false
| F2_1 : F2_spec 1 false true.

Lemma F2P a : F2_spec a (a == 0) (a == 1).
Proof.
case/boolP : (a == 0).
  move/eqP => ?; subst a.
  rewrite (_ : 0 == 1 = false) //; by constructor.
rewrite F2_0_1'' negbK => /eqP ?; subst a.
rewrite eqxx; by constructor.
Qed.

Lemma F2_opp (x : 'F_2) : - x = x.
Proof.
rewrite (F2_0_1 x) -[x]natr_Zp; case: x.
case; first by rewrite /= oppr0.
by case.
Qed.

Lemma F2_add (x : 'F_2) : x + x = 0.
Proof. by rewrite -{2}(F2_opp x) addrN. Qed.

Lemma F2_of_bool_addr (x  y : 'F_2) :
  (x + F2_of_bool (y == 0) = F2_of_bool ((x + y) == 0))%R.
Proof.
  destruct (F2P x), (F2P y); simpl; try done.
    by rewrite GRing.add0r.
  by rewrite F2_add.
Qed.

Lemma F2_of_bool_0_inv : forall x, F2_of_bool x = 0 -> x = false.
Proof. by case. Qed.

Lemma F2_of_boolK : forall x, bool_of_F2 (F2_of_bool x) = x.
Proof. by case. Qed.

Lemma bool_of_F2K x : F2_of_bool (bool_of_F2 x) = x.
Proof. rewrite (F2_0_1 x); by case Heq : ( _ == _ ). Qed.

Lemma bool_of_F2_add_xor a b :
  bool_of_F2 (a + b) = bool_of_F2 a (+) bool_of_F2 b.
Proof.
rewrite (F2_0_1 a) (F2_0_1 b).
by case Ha : ( a == _ ); case Hb : ( b == _ ).
Qed.

Lemma morph_F2_of_bool : {morph F2_of_bool : x y / x (+) y >-> (x + y) : 'F_2}.
Proof.
move=> x y /=.
rewrite /F2_of_bool.
move: x y; case; case => //=; by rewrite F2_add.
Qed.

Lemma morph_bool_of_F2 : {morph bool_of_F2 : x y / (x + y) : 'F_2 >-> x (+) y}.
Proof. move=> x y /=; by rewrite bool_of_F2_add_xor. Qed.

Local Open Scope nat_scope.

Lemma num_occ_sum : forall (t : seq 'F_2),
  num_occ 1%R t = \sum_(i <- t) i.
Proof.
elim => [ /= | /= h t ->].
  by rewrite big_nil.
rewrite big_cons.
by case/F2P: h.
Qed.

Local Close Scope nat_scope.

(** Properties of %$\mathbb{F}_2$%#F_2# generalize to matrices over
   %$\mathbb{F}_2$%#F_2#: *)

Lemma F2_addmx m n (v : 'M['F_2]_(m, n)) : v + v = 0.
Proof. apply/matrixP => i j; by rewrite !mxE F2_add. Qed.

Lemma F2_mx_opp m n (v : 'M['F_2]_(m, n)) : - v = v.
Proof. apply/matrixP => i j; by rewrite mxE F2_opp. Qed.

Lemma F2_addmx0 m n (a b : 'M['F_2]_(m, n)) : a + b = 0 -> a = b.
Proof.
move/eqP.
rewrite addr_eq0 F2_mx_opp.
by move/eqP.
Qed.

(** Properties of %$\mathbb{F}_2$%#F_2# generalize to polynomials over
   %$\mathbb{F}_2$%#F_2#: *)

Lemma F2_poly_add (p : {poly 'F_2}) : p + p = 0.
Proof.
apply/polyP => i.
by rewrite coef0 coef_add_poly F2_add.
Qed.

(*Lemma poly_rV_scale n (a : 'F_2) (p : { poly 'F_2 }) :
 poly_rV (a%:P * p) = a%:M *m (@poly_rV _ n p).
Proof. by rewrite mul_polyC linearZ /= mul_scalar_mx. Qed.*)

(* TODO: move *)
From mathcomp Require Import polydiv.

(*Lemma scale_modp (p d : {poly 'F_2}) (c : 'F_2) :
  (c%:P * p) %% d = c%:P * (p %% d).
Proof.
rewrite (F2_0_1 c); case: (_ =P _) => /= _.
- by rewrite polyC0 2!mul0r mod0p.
- by rewrite polyC1 2!mul1r.
Qed.*)

(** Furthermore, polynomials over %$\mathbb{F}_2$%#F_2# enjoy special properties
    w.r.t. their coefficients, e.g.: *)

Lemma size_lead_coef_F2 (p : {poly 'F_2}) : size p <> O -> lead_coef p = 1.
Proof.
move=> sz_p.
suff goal : lead_coef p <> 0.
  apply/eqP; rewrite F2_0_1'; by apply/eqP.
rewrite lead_coefE.
contradict sz_p.
case: p sz_p => p /= last_p sz_p.
rewrite (nth_last 0 p) in sz_p.
case: p last_p sz_p => //= last_p sz_p.
by move/negbTE; move/eqP.
Qed.

Lemma size1_polyC_F2 (p : {poly 'F_2}) : size p = 1%nat -> p = 1%:P.
Proof.
move=> sz_1.
have sz_1' : (size p <= 1)%nat by rewrite sz_1.
rewrite (size1_polyC sz_1').
transitivity (lead_coef p)%:P.
by rewrite /lead_coef sz_1.
by rewrite size_lead_coef_F2 // sz_1.
Qed.

Lemma lead_coef_F2 (p q : {poly 'F_2}) : size p = size q -> lead_coef p = lead_coef q.
Proof.
move=> X.
case/orP : (orbN (size p == O)) => [ | Y].
- move/eqP => Y; rewrite Y in X.
  symmetry in X; move/eqP: X; rewrite size_poly_eq0; move/eqP => ->.
  by move/eqP: Y; rewrite size_poly_eq0; move/eqP => ->.
- rewrite size_lead_coef_F2; last by apply/eqP.
  rewrite size_lead_coef_F2 //; by rewrite -X; apply/eqP.
Qed.

Lemma monic_F_2 (p : { poly 'F_2 }) : p != 0 -> p \is monic.
Proof.
move=> Hp; apply negbNE; apply/negP => H.
have {H} : lead_coef p == 0.
  move/monicP/eqP : H; by rewrite F2_0_1' negbK.
rewrite lead_coef_eq0.
by apply/negP.
Qed.

Lemma row_nth n (i j : bitseq) : (size i <= n)%nat -> size j = size i ->
  \row_(i0 < n) F2_of_bool (nth false i i0) =
  \row_(i0 < n) F2_of_bool (nth false j i0) -> i = j.
Proof.
move=> Hi Hj /matrixP Heq.
apply/esym.
apply (@eq_from_nth _ false _ _ Hj) => i0 Hi0.
rewrite Hj in Hi0.
have {Hi0}Hi0 : (i0 < n)%nat.
  apply leq_ltn_trans with ((size i).-1)%nat;
    rewrite -ltnS prednK //; by apply leq_ltn_trans with i0.
move: (Heq 0 (Ordinal Hi0)).
rewrite !mxE /=; by do 2 case: nth.
Qed.

(*Lemma col_nth n (i j : bitseq) : (size i <= n)%nat -> size j = size i ->
  \col_(i0 < n) F2_of_bool (nth false i i0) =
  \col_(i0 < n) F2_of_bool (nth false j i0) -> i = j.
Proof.
move=> Hi Hj /matrixP Heq.
apply/esym.
apply (@eq_from_nth _ false _ _ Hj) => i0 Hi0.
rewrite Hj in Hi0.
have {Hi0}Hi0 : (i0 < n)%nat.
  apply leq_ltn_trans with ((size i).-1)%nat;
    rewrite -ltnS prednK //; by apply leq_ltn_trans with i0.
move: (Heq (Ordinal Hi0) 0).
rewrite !mxE /=; by do 2 case: nth.
Qed.*)

End AboutF2.
