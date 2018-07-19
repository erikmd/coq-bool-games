From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div choice fintype.
From mathcomp Require Import tuple finfun bigop prime binomial ssralg finset fingroup finalg.
From mathcomp Require Import matrix.
Require Import Reals Fourier.
From infotheo Require Import Reals_ext ssrR logb ssr_ext ssralg_ext Rbigop.

Local Open Scope reals_ext_scope.

(** Generalization of section [sum_dom_codom] in [infotheo.Rbigop] *)

Section sum_dom_codom_generalized.

Variable A B : finType. (* B <> R *)

Lemma sum_parti' (p : seq A) (X : A -> B) : forall F, uniq p ->
  \rsum_(i <- p) (F i) =
  \rsum_(r <- undup (map X p)) \big[Rplus/0]_(i <- p | X i == r) (F i).
Proof.
move Hn : (undup (map X (p))) => n.
move: n p X Hn.
elim => [p X HA F Hp | h t IH p X H F Hp].
- rewrite big_nil.
  move/undup_nil in HA.
  suff: p = [::] by move ->; rewrite big_nil.
  by apply size0nil; rewrite -(size_map X) HA.
- rewrite big_cons.
  have [preh [pret [H1 [H2 H3]]]] : exists preh pret,
    perm_eq p (preh ++ pret) /\ undup (map X preh) = [:: h] /\ undup (map X pret) = t.
    by apply undup_perm.
  apply trans_eq with (\big[Rplus/0]_(i <- preh ++ pret) F i).
    by apply: eq_big_perm.
  apply trans_eq with
   (\big[Rplus/0]_(i <- preh ++ pret | X i == h) F i +
   \rsum_(j <- t) \big[Rplus/0]_(i <- preh ++ pret | X i == j) F i); last first.
    f_equal.
    apply: eq_big_perm.
      by rewrite perm_eq_sym.
    apply eq_bigr => i _ /=.
    apply: eq_big_perm.
    by rewrite perm_eq_sym.
  have -> :
    \rsum_(j <- t) \big[Rplus/0]_(i <- (preh ++ pret) | X i == j) F i =
    \rsum_(j <- t) \big[Rplus/0]_(i <- pret | X i == j) F i.
    rewrite big_seq_cond.
    symmetry.
    rewrite big_seq_cond /=.
    apply eq_bigr => i Hi.
    rewrite big_cat /=.
    have -> : \big[Rplus/0]_(i0 <- preh | X i0 == i) F i0 = 0.
      transitivity (\big[Rplus/0]_(i0 <- preh | false) F i0).
      rewrite big_seq_cond.
      apply eq_bigl => /= j.
      apply/negP.
      case/andP; move=> Xj_i; move/eqP=> j_preh.
      subst i.
      have Xj_h : X j \in [:: h].
        have H4 : X j \in map X preh by apply/mapP; exists j.
        have H5 : X j \in undup (map X preh)  by rewrite mem_undup.
        by rewrite H2 in H5.
      have : uniq (h :: t).
        rewrite -H.
        apply undup_uniq.
        rewrite /= in_cons in_nil orbC /= in Xj_h.
        move/eqP : Xj_h => Xj_h.
        subst h.
        rewrite andbC /= in Hi.
        by rewrite /= Hi.
      by rewrite big_pred0.
      by rewrite add0R.
  rewrite -IH //; last first.
    have : uniq (preh ++ pret) by rewrite -(@perm_eq_uniq _ _ _ H1).
    rewrite cat_uniq.
    case/andP => _; by case/andP.
  have -> :  \big[Rplus/0]_(i <- (preh ++ pret) | X i == h) F i =
    \rsum_(i <- preh) F i.
    rewrite big_cat /=.
    have -> : \big[Rplus/0]_(i <- pret | X i == h) F i = 0.
      transitivity (\big[Rplus/0]_(i0 <- pret | false) F i0); last first.
        by rewrite big_pred0.
      rewrite big_seq_cond.
      apply eq_bigl => /= j.
      apply/negP.
      case/andP; move => j_pret; move/eqP => Xj_h.
      subst h.
      have Xj_t : X j \in t.
        have H4 : X j \in map X pret.
        apply/mapP; by exists j.
        have H5 : X j \in undup (map X pret).
        by rewrite mem_undup.
        by rewrite H3 in H5.
      have : uniq (X j :: t).
        rewrite -H.
        by apply undup_uniq.
      by rewrite /= Xj_t.
    rewrite addR0 big_seq_cond /=.
    symmetry.
    rewrite big_seq_cond /=.
    apply congr_big => //= x.
    case/orP : (orbN (x \in preh)) => Y.
    + rewrite Y /=.
      symmetry.
      have : X x \in [:: h].
        rewrite -H2 mem_undup.
        apply/mapP.
        by exists x.
      by rewrite in_cons /= in_nil orbC.
    + by rewrite (negbTE Y) andbC.
  by rewrite big_cat.
Qed.

Lemma sum_parti'_finType (X : A -> B) F :
   \rsum_(i in A) (F i) =
   \rsum_(r <- undup (map X (enum A))) \big[Rplus/0]_(i in A | X i == r) (F i).
Proof.
move: (@sum_parti' (enum A) X F) => /=.
rewrite enum_uniq.
move/(_ (refl_equal _)) => IH.
transitivity (\big[Rplus/0]_(i <- enum A) F i).
  apply congr_big => //.
  by rewrite enumT.
rewrite IH.
apply eq_bigr => i _.
apply congr_big => //.
by rewrite enumT.
Qed.

End sum_dom_codom_generalized.
