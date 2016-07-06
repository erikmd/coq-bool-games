(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div choice fintype.
From mathcomp Require Import tuple finfun bigop prime binomial ssralg finset fingroup finalg.
From mathcomp Require Import matrix.
Require Import Reals Fourier.
Require Import Rssr Reals_ext log2 ssr_ext ssralg_ext tuple_prod.

Local Open Scope reals_ext_scope.

(** * Instantiation of canonical big operators with Coq reals *)

Lemma iter_Rplus : forall n r, ssrnat.iter n (Rplus r) 0 = INR n * r.
Proof.
elim => [r /= | m IHm r]; first by rewrite mul0R.
rewrite iterS IHm S_INR; field.
Qed.

Lemma iter_Rmult : forall n p, ssrnat.iter n (Rmult p) 1 = p ^ n.
Proof. elim => // n0 IH p0 /=; by rewrite IH. Qed.

Lemma morph_Ropp : {morph [eta Ropp] : x y / x + y}.
Proof. by move=> x y /=; field. Qed.

Lemma morph_plus_INR : {morph INR : x y / (x + y)%nat >-> x + y}.
Proof. move=> x y /=; by rewrite plus_INR. Qed.

Lemma morph_mult_INR : {morph INR : x y / (x * y)%nat >-> x * y}.
Proof. move=> x y /=; by rewrite mult_INR. Qed.

Lemma morph_mulRDr a : {morph [eta Rmult a] : x y / x + y}.
Proof. move=> * /=; by rewrite mulRDr. Qed.

Lemma morph_mulRDl a : {morph Rmult^~ a : x y / x + y}.
Proof. move=> x y /=; by rewrite mulRDl. Qed.

Lemma morph_exp2_plus : {morph [eta exp2] : x y / x + y >-> x * y}.
Proof. move=> ? ? /=; by rewrite -exp2_plus. Qed.

Section Abelian.

Variable op : Monoid.com_law 1.

Notation Local "'*%M'" := op (at level 0).
Notation Local "x * y" := (op x y).

Lemma mybig_index_uniq (I : eqType) (i : R) (r : seq I) (E : 'I_(size r) -> R) :
  uniq r ->
  \big[*%M/1]_i E i = \big[*%M/1]_(x <- r) oapp E i (insub (seq.index x r)).
Proof.
move=> Ur.
apply/esym.
rewrite big_tnth.
apply: eq_bigr => j _.
by rewrite index_uniq // valK.
Qed.

End Abelian.

(** Instantiation of big sums for reals *)

Canonical Structure mulR_muloid := Monoid.MulLaw mul0R mulR0.
Canonical Structure addR_monoid := Monoid.Law addRA add0R addR0.
Canonical Structure addR_comoid := Monoid.ComLaw addRC.
Canonical Structure addR_addoid := Monoid.AddLaw mulRDl mulRDr.
Canonical Rmult_monoid := Monoid.Law mulRA mul1R mulR1.
Canonical Structure mulR_comoid := Monoid.ComLaw mulRC.

Notation "\rsum_ ( i <- t ) F" := (\big[Rplus/0%R]_( i <- t) F)
  (at level 41, F at level 41, i at level 50,
    format "'[' \rsum_ ( i <- t ) '/  '  F ']'") : R_scope.
Notation "\rsum_ ( m <= i < n ) F" := (\big[Rplus/0%R]_( m <= i < n ) F)
  (at level 41, F at level 41, i, m, n at level 50,
    format "'[' \rsum_ ( m  <=  i  <  n ) '/  '  F ']'") : R_scope.
Notation "\rsum_ ( i | P ) F" := (\big[Rplus/0%R]_( i | P) F)
  (at level 41, F at level 41, i at level 50,
    format "'[' \rsum_ ( i  |  P ) '/  '  F ']'") : R_scope.
Notation "\rsum_ ( i ':' A | P ) F" := (\big[Rplus/0%R]_( i : A | P ) F)
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \rsum_ ( i  ':'  A  |  P ) '/  '  F ']'") : R_scope.
Notation "\rsum_ ( i : t ) F" := (\big[Rplus/0%R]_( i : t) F)
  (at level 41, F at level 41, i at level 50,
    format "'[' \rsum_ ( i : t ) '/  '  F ']'") : R_scope.
Notation "\rsum_ ( i < n ) F" := (\big[Rplus/0%R]_( i < n ) F)
  (at level 41, F at level 41, i at level 50,
    format "'[' \rsum_ ( i < n ) '/  '  F ']'") : R_scope.
Notation "\rsum_ ( i 'in' A | P ) F" := (\big[Rplus/0%R]_( i in A | P ) F)
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \rsum_ ( i  'in'  A  |  P ) '/  '  F ']'") : R_scope.
Notation "\rsum_ ( a 'in' A ) F" := (\big[Rplus/0%R]_( a in A ) F)
  (at level 41, F at level 41, a, A at level 50,
    format "'[' \rsum_ ( a  'in'  A ) '/  '  F ']'") : R_scope.

(*Notation "\rsum_ ( m <= i < n ) F" := (\big[Rplus/0%R]_( m <= i < n ) F)
  (at level 41, F at level 41, i, m, n at level 50,
    format "'[' \rsum_ ( m  <=  i  <  n ) '/  '  F ']'") : R_scope.
Notation "\rsum_ ( i ':' A | P ) F" := (\big[Rplus/0%R]_( i : A | P ) F)
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \rsum_ ( i  ':'  A  |  P ) '/  '  F ']'") : R_scope.
Notation "\rsum_ ( i : t ) F" := (\big[Rplus/0%R]_( i : t) F)
  (at level 41, F at level 41, i at level 50,
    format "'[' \rsum_ ( i : t ) '/  '  F ']'") : R_scope.
Notation "\rsum_ ( i <- t ) F" := (\big[Rplus/0%R]_( i <- t) F)
  (at level 41, F at level 41, i at level 50,
    format "'[' \rsum_ ( i <- t ) '/  '  F ']'") : R_scope.
Notation "\rsum_ ( i 'in' A | P ) F" := (\big[Rplus/0%R]_( i in A | P ) F)
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \rsum_ ( i  'in'  A  |  P ) '/  '  F ']'") : R_scope.
Notation "\rsum_ ( a 'in' A ) F" := (\big[Rplus/0%R]_( a in A ) F)
  (at level 41, F at level 41, a, A at level 50,
    format "'[' \rsum_ ( a  'in'  A ) '/  '  F ']'") : R_scope.
Notation "\rsum_ ( i | P ) F" := (\big[Rplus/0%R]_( i | P) F)
  (at level 41, F at level 41, i at level 50,
    format "'[' \rsum_ ( i  |  P ) '/  '  F ']'") : R_scope.
Notation "\rsum_ ( i < n ) F" := (\big[Rplus/0%R]_( i < n ) F)
  (at level 41, F at level 41, i, A at level 50,
    format "'[' \rsum_ ( i < n ) '/  '  F ']'") : R_scope.
*)

Lemma big_Rabs {A : finType} F : Rabs (\rsum_ (a : A) F a) <= \rsum_ (a : A) Rabs (F a).
Proof.
elim: (index_enum _) => [| hd tl IH].
  rewrite 2!big_nil Rabs_R0; by apply Rle_refl.
rewrite 2!big_cons.
apply (Rle_trans _ (Rabs (F hd) + Rabs (\rsum_(j <- tl) F j))); first by apply Rabs_triang.
by apply Rplus_le_compat_l.
Qed.

Lemma classify_big {T : finType} k (f : T -> 'I_k) (F : 'I_k -> R) :
  \rsum_(s : T) F (f s) = \rsum_(n : 'I_k) INR #|f @^-1: [set n]| * F n.
Proof.
transitivity (\rsum_(n<k) \rsum_(s | true && (f s == n)) F (f s)).
  by apply partition_big.
apply eq_bigr => i _ /=.
transitivity (\rsum_(s|f s == i) F i).
  by apply eq_bigr => s /eqP ->.
rewrite big_const iter_Rplus.
do 2 f_equal.
apply eq_card => j /=.
by rewrite !inE.
Qed.

(** Rle, Rlt lemmas for big sums of reals *)

Section Rcomparison_rsum.

Variable A : finType.
Variables f g : A -> R.
Variable P Q : pred A.

Lemma Rle_big_P_f_g_X (X : {set A}) : (forall i, i \in X -> P i -> f i <= g i) ->
  \rsum_(i in X | P i) f i <= \rsum_(i in X | P i) g i.
Proof.
move=> H.
elim: (index_enum _) => [| hd tl IH].
- rewrite !big_nil; by apply Rle_refl.
- rewrite !big_cons.
  set cond := _ && _; move Hcond : cond => []; subst cond => //.
  apply Rplus_le_compat => //.
  case/andP : Hcond.
  by apply H.
Qed.

Lemma Rle_big_P_f_g : (forall i, P i -> f i <= g i) ->
  \rsum_(i | P i) f i <= \rsum_(i | P i) g i.
Proof.
move=> H.
elim: (index_enum _) => [| hd tl IH].
- rewrite !big_nil; by apply Rle_refl.
- rewrite !big_cons.
  case: ifP => Hcase //.
  apply Rplus_le_compat => //.
  by apply H.
Qed.

Lemma Rlt_big_f_g_X (X : {set A}) : forall (HA: (0 < #|X|)%nat),
  (forall i, i \in X -> f i < g i) ->
  \rsum_(i in X) f i < \rsum_(i in X) g i.
Proof.
move Ha : #|X| => a.
move: a X Ha.
elim => // a IHa X Ha _ H.
move: (ltn0Sn a). rewrite -Ha card_gt0. case/set0Pn => a0 Ha0.
rewrite (@big_setD1 _ _ _ _ a0 _ f) //= (@big_setD1 _ _ _ _ a0 _ g) //=.
case: a IHa Ha => IHa Ha.
  rewrite (_ : X :\ a0 = set0); last first.
    rewrite (cardsD1 a0) Ha0 /= add1n in Ha.
    case: Ha.
    move/eqP.
    rewrite cards_eq0.
    by move/eqP.
  rewrite !big_set0 2!addR0; by apply H.
move=> HA.
apply Rplus_lt_compat.
  by apply H.
apply Ha => //.
  rewrite (cardsD1 a0) Ha0 /= add1n in HA.
  by case: HA.
move=> i Hi.
rewrite in_setD in Hi.
case/andP : Hi => Hi1 Hi2.
by apply H.
Qed.

Lemma Rle_big_P_Q_f_g : (forall i, P i -> f i <= g i) ->
  (forall i, Q i -> 0 <= g i) ->
  (forall i, P i -> Q i) ->
  \rsum_(i | P i) f i <= \rsum_(i | Q i) g i.
Proof.
move=> f_g Qg H.
elim: (index_enum _) => [| hd tl IH].
- rewrite !big_nil; by apply Rle_refl.
- rewrite !big_cons /=.
  case: ifP => Hcase.
    rewrite (H _ Hcase).
    apply Rplus_le_compat => //.
    by apply f_g.
  case: ifP => // Qhd.
  apply Rle_trans with (\big[Rplus/0]_(j <- tl | Q j) g j).
    by apply IH.
  rewrite -{1}(add0R (\big[Rplus/0]_(j <- tl | Q j) g j)).
  by apply Rplus_le_compat_r, Qg.
Qed.

Lemma Rle_big_P_true_f_g : (forall a, 0 <= g a) ->
  (forall i, i \in P -> f i <= g i) ->
  \rsum_(i in A | P i) f i <= \rsum_(i in A) g i.
Proof.
move=> K H.
elim: (index_enum _) => [| hd tl IH].
- rewrite !big_nil; by apply Rle_refl.
- rewrite !big_cons.
  case/orP : (orbN (hd \in A)) => H1.
    rewrite H1 /=.
    case: ifP => Hif.
      apply Rplus_le_compat => //.
      by apply H.
    rewrite -[X in X <= _]add0R.
    by apply Rplus_le_compat.
  rewrite (negbTE H1) /=; exact IH.
Qed.

Lemma Rle_big_f_X_Y : (forall a, 0 <= f a) ->
  (forall i, i \in P -> i \in Q) ->
  \rsum_(i in P) f i <= \rsum_(i in Q) f i.
Proof.
move=> Hf P'_P.
elim: (index_enum _) => [| hd tl IH].
- rewrite !big_nil; by apply Rle_refl.
- rewrite !big_cons.
  set cond := _ \in _; move Hcond : cond => []; subst cond => //=.
    rewrite (P'_P _ Hcond).
    by apply Rplus_le_compat_l.
  set cond := _ \in _; move Hcond2 : cond => []; subst cond => //=.
  rewrite -[X in X <= _]add0R.
  by apply Rplus_le_compat.
Qed.

Lemma Rle_big_P_Q_f_X (X : pred A) :
  (forall a, 0 <= f a) -> (forall i, P i -> Q i) ->
  \rsum_(i in X | P i) f i <= \rsum_(i in X | Q i) f i.
Proof.
move=> Hf P_Q.
elim: (index_enum _) => [| hd tl IH].
- rewrite !big_nil; by apply Rle_refl.
- rewrite !big_cons.
  set cond := _ \in _; move Hcond : cond => []; subst cond => //=.
  case: ifP => // HP.
  + case: ifP => HQ.
    * by apply Rplus_le_compat_l.
    * by rewrite (P_Q _ HP) in HQ.
  + case: ifP => // HQ.
    rewrite -[X in X <= _]add0R.
    by apply Rplus_le_compat.
Qed.

Lemma Rle_big_predU_f : (forall a, 0 <= f a) ->
  \rsum_(i in A | [predU P & Q] i) f i <=
  \rsum_(i in A | P i) f i + \rsum_(i in A | Q i) f i.
Proof.
move=> Hf.
elim: (index_enum _) => //.
- rewrite !big_nil /=; fourier.
- move=> h t IH /=.
  rewrite !big_cons /=.
  case: ifP => /=.
  + case/orP => [HP1 | HP2].
    * rewrite unfold_in in HP1.
      rewrite HP1.
      case: ifP => // HP2.
      - rewrite -addRA; apply Rplus_le_compat_l.
        eapply Rle_trans; first by apply IH.
        have : forall a b c, 0 <= c -> a + b <= a + (c + b) by move=> *; fourier.
        apply.
        by apply Hf.
      - rewrite -addRA; apply Rplus_le_compat_l.
        eapply Rle_trans; first by apply IH.
        by apply Req_le.
    * rewrite unfold_in in HP2.
      rewrite HP2.
      case: ifP => // HP1.
      - rewrite -addRA; apply Rplus_le_compat_l.
        eapply Rle_trans; first by apply IH.
        have : forall a b c, 0 <= c -> a + b <= a + (c + b) by move=> *; fourier.
        apply.
        by apply Hf.
      - rewrite -(Rplus_comm (f h + _)) -addRA; apply Rplus_le_compat_l.
        eapply Rle_trans; first by apply IH.
        by rewrite Rplus_comm; apply Req_le.
  + move/negbT.
    rewrite negb_or.
    case/andP.
    rewrite unfold_in; move/negbTE => ->.
    rewrite unfold_in; move/negbTE => ->.
    by apply IH.
Qed.

Lemma Rle_big_P_true_f : (forall i : A, 0 <= f i) ->
  \rsum_(i in A | P i) f i <= \rsum_(i in A) f i.
Proof.
move=> H.
elim: (index_enum _) => [| hd tl IH].
- rewrite !big_nil; by apply Rle_refl.
- rewrite !big_cons.
  case/orP : (orbN (P hd)) => P_hd.
  + rewrite P_hd /=.
    apply Rplus_le_compat => //; by apply Rle_refl.
  + rewrite (negbTE P_hd) inE /= -[X in X <= _]add0R; by apply Rplus_le_compat.
Qed.

End Rcomparison_rsum.

Lemma Rlt_big_0_g (A : finType) (g : A -> R) (HA : (0 < #|A|)%nat) :
  (forall i, 0 < g i) -> 0 < \rsum_(i in A) g i.
Proof.
move=> H.
rewrite (_ : \rsum_(i in A) g i = \rsum_(i in [set: A]) g i); last first.
  apply eq_bigl => x /=; by rewrite !inE.
eapply Rle_lt_trans; last first.
  apply Rlt_big_f_g_X with (f := fun x => 0) => //.
  by rewrite cardsT.
rewrite big_const_seq iter_Rplus mulR0; by apply Rle_refl.
Qed.

Lemma Rle_big_0_P_g (A : finType) (P : pred A) (g : A -> R) :
  (forall i, P i -> 0 <= g i) -> 0 <= \rsum_(i in A | P i) g i.
Proof.
move=> H.
apply Rle_trans with (\rsum_(i|(i \in A) && P i) (fun x => 0) i).
rewrite big_const iter_Rplus mulR0 /=; by apply Rle_refl.
by apply Rle_big_P_f_g.
Qed.

Lemma Rle_big_P_Q_f_X_new {A : finType} (f : A -> R) (P Q : pred A) :
  (forall a, 0 <= f a) -> (forall i, P i -> Q i) ->
  \rsum_(i | P i) f i <= \rsum_(i | Q i) f i.
Proof.
move=> Hf R_T.
eapply Rle_trans; last by apply (Rle_big_P_Q_f_X A f P Q xpredT).
by apply Req_le.
Qed.

Lemma Req_0_rmul_inv' {A : finType} (f : A -> R) (P Q : pred A) : (forall i, 0 <= f i) ->
  forall j, P j -> f j <= \rsum_(i | P i) f i.
Proof.
move=> HF j Hj.
rewrite (_ : f j = \rsum_(i | i == j) f i); last by rewrite big_pred1_eq.
apply: Rle_big_P_Q_f_X_new => //.
move=> i /eqP ?; by subst j.
Qed.

Lemma Req_0_rmul_inv {C : finType} (R : pred C) F (HF : forall a, 0 <= F a) :
  0 = \rsum_(i | R i) F i -> (forall i, R i -> 0 = F i).
Proof.
move=> abs i Hi.
case/Rle_lt_or_eq_dec : (HF i) => // Fi.
suff : False by done.
have : F i <= \rsum_(i|R i) F i.
  by apply Req_0_rmul_inv'.
rewrite -abs => ?.
fourier.
Qed.

(* TODO: move, generalize to any idx *)
Lemma Req_0_rmul {C : finType} (R : pred C) F:
  (forall i, R i -> 0 = F i) ->
  0 = \rsum_(i | R i) F i.
Proof.
move=> HF.
elim: (index_enum _) => [| hd tl IH].
by rewrite big_nil.
rewrite big_cons.
case: ifP => Rhd.
by rewrite -IH -HF // addR0.
done.
Qed.

(* TODO: factorize? *)
Lemma eq_0_sum_elements {A : finType} (F : A -> R) : (forall i, 0 <= F i) ->
  0 = \rsum_(i : A) F i -> (forall i, F i = 0).
Proof.
move=> Hf H0 i.
by rewrite (Req_0_rmul_inv _ _ Hf H0 i).
Qed.

(* TODO: factorize? *)
Lemma Rle_big_eq_0 {B : finType} (g : B -> R) (U : pred B) :
  \rsum_(i|U i) g i = 0 ->
  (forall i : B, U i -> 0 <= g i) ->
  (forall i : B, U i -> g i = 0).
Proof.
move=> H2 H1 i Hi.
suff H : g i = 0 /\ (\rsum_(j|(U j && (j != i))) g j) = 0 by case: H.
apply Rplus_eq_R0.
- apply H1 ; exact Hi.
- apply: Rle_big_0_P_g => i0 Hi0; apply H1.
  move/andP in Hi0; by apply Hi0.
- rewrite -bigD1 /=; [exact H2 | exact Hi].
Qed.

Lemma rsum_neq0 {A : finType} (P : {set A}) (g : A -> R) :
  \rsum_(t | t \in P) g t != 0 -> [exists t, (t \in P) && (g t != 0)].
Proof.
move=> H1.
apply negbNE.
rewrite negb_exists.
apply/negP => /forallP abs.
move/negP : H1; apply.
rewrite big_mkcond /=.
apply/eqP.
transitivity (\rsum_(a : A) 0); last by rewrite big_const iter_Rplus mulR0.
apply eq_bigr => a _.
case: ifP => // Hcond.
move: (abs a); by rewrite Hcond /= negbK => /eqP.
Qed.

(* TODO: factorize? *)
Lemma Rle_big_eq (B : finType) (f g : B -> R) (U : pred B) :
   (forall i : B, U i -> f i <= g i) ->
   \rsum_(i|U i) g i = \rsum_(i|U i) f i ->
   (forall i : B, U i -> g i = f i).
Proof.
move=> H1 H2 i Hi.
apply (Rplus_eq_reg_l (- (f i))).
rewrite Rplus_opp_l Rplus_comm.
move: i Hi.
apply Rle_big_eq_0.
- rewrite big_split /= -(big_morph _ morph_Ropp Ropp_0).
  by apply Rminus_diag_eq, H2.
- move=> i Hi.
  apply (Rplus_le_reg_l (f i)).
  rewrite addR0 subRKC; by apply H1.
Qed.

(* TODO: generalize to any bigop *)
Lemma rsum_union {C : finType} (B1 B2 B : {set C}) f :
  [disjoint B2 & B1] ->
  B = B1 :|: B2 ->
  \rsum_(b | b \in B) f b =
  \rsum_(b | b \in B1) f b + \rsum_(b | b \in B2) f b.
Proof.
move=> Hdisj ->.
rewrite (@big_setID _ _ _ _ _ B1) /= setUK setDUl setDv set0U.
suff : B2 :\: B1 = B2 by move=> ->.
by apply/setDidPl.
Qed.

(** Big sums lemmas for products *)

Section big_sums_prods.

Variables A B : finType.

Lemma pair_big_fst : forall (F : {: A * B} -> R) P Q,
  P =1 Q \o (fun x => x.1) ->
  \rsum_(i in A | Q i) \rsum_(j in B) (F (i, j)) = \rsum_(i in {: A * B} | P i) F i.
Proof.
move=> /= F Q' Q Q'Q; rewrite pair_big /=.
apply eq_big.
- case=> /= i1 i2; by rewrite inE andbC Q'Q.
- by case.
Qed.

Lemma pair_big_snd : forall (F : {: A * B} -> R) P Q,
  P =1 Q \o (fun x => x.2) ->
  \rsum_(i in A) \rsum_(j in B | Q j) (F (i, j)) = \rsum_(i in {: A * B} | P i) F i.
Proof.
move=> /= F Q' Q Q'Q; rewrite pair_big /=.
apply eq_big.
- case=> /= i1 i2; by rewrite Q'Q.
- by case.
Qed.

End big_sums_prods.

(** Switching from a sum on the domain to a sum on the image of function *)

Section sum_dom_codom.

Variable A : finType.

Lemma sum_parti (p : seq A) (X : A -> R) : forall F, uniq p ->
  \rsum_(i <- p) (F i) =
  \rsum_(r <- undup (map X p)) \big[Rplus/0]_(i <- p | X i == r) (F i).
Proof.
move Hn : (undup (map X (p))) => n.
move: n p X Hn.
elim => [p X HA F Hp | h t IH p X H F Hp].
- rewrite big_nil.
  move/undup_nil_inv : HA.
  move/map_nil_inv => ->.
  by rewrite big_nil.
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

(* NB: use finset.partition_big_imset? *)
Lemma sum_parti_finType (X : A -> R) F :
   \rsum_(i in A) (F i) =
   \rsum_(r <- undup (map X (enum A))) \big[Rplus/0]_(i in A | X i == r) (F i).
Proof.
move: (@sum_parti (enum A) X F) => /=.
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

End sum_dom_codom.

Local Open Scope R_scope.

Section tmp.

Local Open Scope ring_scope.

(* TODO: rename? *)
Lemma rsum_rV_prod (C D : finType) n f (Q : {set 'rV_n}) :
  \rsum_(a in 'rV[C * D]_n | a \in Q) f a =
  \rsum_(a in {: 'rV[C]_n * 'rV[D]_n} | (prod_tuple a) \in Q) f (prod_tuple a).
Proof.
rewrite (reindex_onto (fun p => tuple_prod p) (fun y => prod_tuple y)) //=; last first.
  move=> i _; by rewrite prod_tupleK.
apply eq_big => /=.
  move=> t /=.
  by rewrite tuple_prodK eqxx andbC.
move=> i _; by rewrite tuple_prodK.
Qed.

(*Lemma rsum_rV_prod (A B : finType) n f P :
  \rsum_(a in 'rV[A * B]_n | P a) f a =
  \rsum_(a in {: 'rV[A]_n * 'rV[B]_n} | P (prod_tuple a)) f (prod_tuple a).
Proof.
rewrite (reindex_onto (fun p => tuple_prod p) (fun y => prod_tuple y)) //=; last first.
  move=> i _; by rewrite prod_tupleK.
apply eq_big => /=.
  move=> t /=.
  by rewrite tuple_prodK eqxx andbC.
move=> i _; by rewrite tuple_prodK.
Qed.*)

End tmp.

(*Lemma rsum_tuple_prod (A B : finType) n f P :
  \rsum_(a in {:n.-tuple (A * B)%type} | P a) f a =
  \rsum_(a in {: n.-tuple A * n.-tuple B} | P (tuple_prod.prod_tuple a)) f (tuple_prod.prod_tuple a).
Proof.
rewrite (reindex_onto (fun p => tuple_prod.tuple_prod p) (fun y => tuple_prod.prod_tuple y)) //=; last first.
  move=> i _; by rewrite tuple_prod.prod_tupleK.
apply eq_big => /=.
  move=> t /=.
  by rewrite tuple_prod.tuple_prodK eqxx andbC.
move=> i _; by rewrite tuple_prod.tuple_prodK.
Qed.

Lemma rsum_tuple_prod_set (A B : finType) n f (P : {set {:n.-tuple (A * B)}}) :
  \rsum_(a in {:n.-tuple (A * B)%type} | a \in P) f a =
  \rsum_(a in {: n.-tuple A * n.-tuple B} | (tuple_prod.prod_tuple a) \in P) f (tuple_prod.prod_tuple a).
Proof.
rewrite (reindex_onto (fun p => tuple_prod.tuple_prod p) (fun y => tuple_prod.prod_tuple y)) //=; last first.
  move=> i _; by rewrite tuple_prod.prod_tupleK.
apply eq_big => /=.
  move=> t /=.
  by rewrite tuple_prod.tuple_prodK eqxx andbC.
move=> i _; by rewrite tuple_prod.tuple_prodK.
Qed.
*)

Section big_sum_rV.

Context {A : finType}.

Local Open Scope vec_ext_scope.
Local Open Scope ring_scope.

Lemma rsum_rV_1 F G P Q :
  (forall i : 'rV[A]_1, F i = G (i /_ ord0)) ->
  (forall i : 'rV[A]_1, P i = Q (i /_ ord0)) ->
  \rsum_(i in 'rV[A]_1 | P i) F i = \rsum_(i in A | Q i) G i.
Proof.
move=> FG PQ.
rewrite (reindex_onto (fun i => \row_(j < 1) i) (fun p => p /_ ord0)) /=; last first.
  move=> m Pm.
  apply/matrixP => a b; rewrite {a}(ord1 a) {b}(ord1 b); by rewrite mxE.
apply eq_big => a.
  by rewrite PQ mxE eqxx andbT.
by rewrite FG !mxE.
Qed.

End big_sum_rV.

Section big_sums_rV.

Variable A : finType.

Lemma rsum_0rV F Q :
  \rsum_( j in 'rV[A]_0 | Q j) F j = if Q (row_of_tuple [tuple]) then F (row_of_tuple [tuple]) else 0.
Proof.
rewrite -big_map /= /index_enum -enumT.
rewrite (_ : enum (matrix_finType A 1 0) = row_of_tuple ([tuple]) :: [::]).
by rewrite /= big_cons big_nil addR0.
apply eq_from_nth with (row_of_tuple [tuple]) => /=.
by rewrite size_tuple card_matrix.
move=> i.
rewrite size_tuple card_matrix expn0.
destruct i => //= _.
set xx := enum _ .
destruct xx => //.
destruct s.
apply val_inj => /=.
apply/ffunP.
case => a.
by case.
Qed.

End big_sums_rV.

Section big_sums_rV2.

Local Open Scope vec_ext_scope.
Local Open Scope ring_scope.

Variable A : finType.

Lemma big_singl_rV (p : A -> R) :
  \rsum_(i in A) p i = 1%R -> \rsum_(i in 'rV[A]_1) p (i /_ ord0) = 1%R.
Proof.
move=> <-.
rewrite (reindex_onto (fun j => \row_(i < 1) j) (fun p => p /_ ord0)) /=.
- apply eq_big => a; first by rewrite mxE eqxx inE.
  move=> _; by rewrite mxE.
- move=> t _; apply/matrixP => a b; by rewrite (ord1 a) (ord1 b) mxE.
Qed.

End big_sums_rV2.

Section big_sums_tuples.

Variable A : finType.

Lemma rsum_1_tuple F G P Q :
  (forall i : tuple_finType 1 A, F i = G (thead i)) ->
  (forall i : tuple_finType 1 A, P i = Q (thead i)) ->
  \rsum_(i in {: 1.-tuple A} | P i) F i = \rsum_(i in A | Q i) G i.
Proof.
move=> FG PQ.
rewrite (reindex_onto (fun i => [tuple of [:: i]]) (fun p => thead p)) /=; last first.
  case/tupleP => h t X; by rewrite theadE (tuple0 t).
apply eq_big => x //.
by rewrite (PQ [tuple x]) /= theadE eqxx andbC.
move=> X; by rewrite FG.
Qed.

(* TODO: useless? *)
Lemma rsum_0tuple F Q :
  \rsum_( j in {:0.-tuple A} | Q j) F j = if Q [tuple] then F [tuple] else 0.
Proof.
rewrite -big_map /= /index_enum -enumT (_ : enum (tuple_finType 0 A) = [tuple] :: [::]).
by rewrite /= big_cons big_nil addR0.
apply eq_from_nth with [tuple] => /=.
by rewrite size_tuple card_tuple.
move=> i.
rewrite size_tuple card_tuple expn0.
destruct i => //= _.
set xx := enum _ .
destruct xx => //.
destruct s.
apply val_inj => /=.
by destruct tval.
Qed.

Lemma big_singl_tuple (p : A -> R) :
  \rsum_(i in A) p i = 1 -> \rsum_(i in {: 1.-tuple A}) p (thead i) = 1.
Proof.
move=> <-.
rewrite (reindex_onto (fun j => [tuple of [:: j]]) (fun p => thead p)) => /=.
- apply eq_bigl => x; by rewrite theadE inE eqxx.
- by move=> i _; apply thead_tuple1.
Qed.

(*Lemma big_head_behead_P n (F : 'rV[A]_n.+1 -> R) (P1 : pred A) (P2 : pred 'rV[A]_n) :
  \rsum_(i in A | P1 i) \rsum_(j in 'rV[A]_n | P2 j) (F (row_mx (\row_(k < 1) i) j))
  =
  \rsum_(p in 'rV[A]_n.+1 | (P1 (p /_ ord0)) && (P2 (tbehead p)) ) (F p).
Proof.
symmetry.
rewrite (@partition_big _ _ _ _ _ _ (fun x : {: n.+1.-tuple A} => thead x)
  (fun x : A => P1 x)) //=.
- apply eq_bigr => i Hi.
  rewrite (reindex_onto (fun j : {: n.-tuple A} => [tuple of (i :: j)])
    (fun p => [tuple of (behead p)])) /=; last first.
    move=> j Hj.
    case/andP : Hj => Hj1 /eqP => <-.
    symmetry.
    by apply tuple_eta.
  apply congr_big => // x /=.
  rewrite !theadE eqxx /= Hi /= -andbA /=.
  set tmp := _ == x.
  have Htmp : tmp = true.
    rewrite /tmp tupleE /behead_tuple /=.
    apply/eqP => /=.
    by apply val_inj.
  rewrite Htmp andbC /=.
  f_equal.
  by apply/eqP.
move=> i; by case/andP.
Qed.

Lemma big_head_behead_P_set n (F : n.+1.-tuple A -> R) (P1 : {set A}) (P2 : {set {: n.-tuple A}}) :
  \rsum_(i in P1) \rsum_(j in P2) (F [tuple of (i :: j)])
  =
  \rsum_(p | (thead p \in P1) && (tbehead p \in P2)) (F p).
Proof.
symmetry.
rewrite (@partition_big _ _ _ _ _ _ (fun x : {: n.+1.-tuple A} => thead x)
  (fun x : A => x \in P1)) //=.
- apply eq_bigr => i Hi.
  rewrite (reindex_onto (fun j : {: n.-tuple A} => [tuple of (i :: j)])
    (fun p => [tuple of (behead p)])) /=; last first.
    move=> j Hj.
    case/andP : Hj => Hj1 /eqP => <-.
    symmetry.
    by apply tuple_eta.
  apply congr_big => // x /=.
  rewrite !theadE eqxx /= Hi /= -andbA /=.
  set tmp := _ == x.
  have Htmp : tmp = true.
    rewrite /tmp tupleE /behead_tuple /=.
    apply/eqP => /=.
    by apply val_inj.
  rewrite Htmp andbC /=.
  f_equal.
  by apply/eqP.
move=> i; by case/andP.
Qed.

Lemma big_head_behead n (F : n.+1.-tuple A -> R) :
  \rsum_(i in A) \rsum_(j in {: n.-tuple A}) (F [tuple of (i :: j)]) =
  \rsum_(p in {: n.+1.-tuple A}) (F p).
Proof. by rewrite big_head_behead_P. Qed.*)

(*Lemma big_cat_tuple m n (F : (m + n)%nat.-tuple A -> R) :
  \rsum_(i in {:m.-tuple A} ) \rsum_(j in {: n.-tuple A})
  F [tuple of (i ++ j)] = \rsum_(p in {: (m + n)%nat.-tuple A}) (F p).
Proof.
move: m n F.
elim.
- move=> m2 F /=.
  transitivity ( \rsum_(i <- [tuple] :: [::])
    \rsum_(j in tuple_finType m2 A) F [tuple of i ++ j] ).
    apply congr_big => //=.
    symmetry.
    rewrite /index_enum /=.
    rewrite Finite.EnumDef.enumDef /=.
    apply eq_from_nth with [tuple] => //=.
    by rewrite FinTuple.size_enum expn0.
    case=> //= _.
    destruct (FinTuple.enum 0 A) => //.
    by rewrite (tuple0 t).
  rewrite big_cons /= big_nil /= addR0.
  apply eq_bigr => // i _.
  f_equal.
  by apply val_inj.
- move=> m IH n F.
  symmetry.
  transitivity (\rsum_(p in tuple_finType (m + n).+1 A) F p); first by apply congr_big.
  rewrite -big_head_behead -big_head_behead.
  apply eq_bigr => i _.
  symmetry.
  move: {IH}(IH n (fun x => F [tuple of i :: x])) => <-.
  apply eq_bigr => i0 _.
  apply eq_bigr => i1 _.
  f_equal.
  by apply val_inj.
Qed.

Lemma big_cat_tuple_seq m n (F : seq A -> R) :
  \rsum_(i in {:m.-tuple A} ) \rsum_(j in {: n.-tuple A}) (F (i ++ j)) =
  \rsum_(p in {: (m + n)%nat.-tuple A}) (F p).
Proof.
move: (@big_cat_tuple m n (fun l => if size l == (m+n)%nat then F l else 0)) => IH.
set lhs := \rsum_(i in _) _ in IH.
apply trans_eq with lhs.
rewrite /lhs.
apply eq_bigr => i _.
apply eq_bigr => j _.
set test := _ == _.
have Htest : test = true by rewrite /test size_tuple eqxx.
case: ifP => // abs.
by rewrite abs in Htest.
rewrite IH.
apply eq_bigr => i _.
by rewrite size_tuple eqxx.
Qed.*)

Local Open Scope vec_ext_scope.
Local Open Scope ring_scope.

Lemma big_head_rbehead n (F : 'rV[A]_n.+1 -> R) (i : A) :
  \rsum_(j in 'rV[A]_n) (F (row_mx (\row_(k < 1) i) j)) =
  \rsum_(p in 'rV[A]_n.+1 | p /_ ord0 == i) (F p).
Proof.
symmetry.
rewrite (reindex_onto (fun j : 'rV[A]_n => (row_mx (\row_(k < 1) i) j))
  (fun p : 'rV[A]_n.+1=> rbehead p)) /=; last first.
  move=> m Hm.
  apply/matrixP => a b; rewrite {a}(ord1 a).
  rewrite row_mx_rbehead //.
  by apply/eqP.
apply eq_bigl => /= x.
by rewrite rbehead_row_mx eqxx andbT row_mx_row_ord0 eqxx.
Qed.

(*Lemma big_behead_head n (F : n.+1.-tuple A -> R) (i : A) :
  \rsum_(j in {: n.-tuple A}) (F [tuple of (i :: j)]) =
  \rsum_(p in {: n.+1.-tuple A} | thead p == i) (F p).
Proof.
symmetry.
rewrite (reindex_onto (fun j : {: n.-tuple A} => [tuple of (i :: j)])
  (fun p => tbehead p)) /=; last first.
  move=> ij /eqP => <-; by rewrite -tuple_eta.
apply eq_bigl => /= x.
rewrite inE /= theadE eqxx /=.
apply/eqP.
rewrite tupleE /behead_tuple /=.
by apply val_inj.
Qed.*)

(* TODO: rename *)
Lemma big_head_big_behead n (F : 'rV[A]_n.+1 -> R) (j : 'rV[A]_n) :
  \rsum_(i in A ) (F (row_mx (\row_(k < 1) i) j)) =
  \rsum_(p in 'rV[A]_n.+1 | rbehead p == j) (F p).
Proof.
apply/esym.
rewrite (reindex_onto (fun p => row_mx (\row_(k < 1) p) j) (fun p => p /_ ord0) ) /=; last first.
  move=> i /eqP <-.
  apply/matrixP => a b; rewrite {a}(ord1 a).
  by rewrite row_mx_rbehead.
apply eq_bigl => /= a.
by rewrite rbehead_row_mx eqxx /= row_mx_row_ord0 eqxx.
Qed.

(*Lemma big_head_big_behead n (F : n.+1.-tuple A -> R) (j : {:n.-tuple A}) :
  \rsum_(i in A ) (F [tuple of (i :: j)]) =
  \rsum_(p in {:n.+1.-tuple A} | behead p == j) (F p).
Proof.
symmetry.
rewrite (reindex_onto (fun p => [tuple of (p :: j)]) (fun p => thead p) ) /=; last first.
  case/tupleP => hd tl /=; move/eqP => tl_i.
  rewrite !tupleE.
  f_equal.
  by apply val_inj.
apply eq_bigl => /= a; by rewrite inE /= theadE eqxx /= eqxx.
Qed.*)

Lemma big_head_rbehead_P_set n (F : 'rV[A]_n.+1 -> R) (P1 : {set A}) (P2 : {set {: 'rV[A]_n}}) :
  \rsum_(i in P1) \rsum_(j in P2) (F (row_mx (\row_(k < 1) i) j))
  =
  \rsum_(p in 'rV[A]_n.+1 | (p /_ ord0 \in P1) && (rbehead p \in P2)) (F p).
Proof.
apply/esym.
rewrite (@partition_big _ _ _ _ _ _ (fun x : 'rV[A]_n.+1 => x /_ ord0)
  (fun x : A => x \in P1)) //=.
- apply eq_bigr => i Hi.
  rewrite (reindex_onto (fun j : 'rV[A]_n => row_mx (\row_(k < 1) i) j) rbehead) /=; last first.
    move=> j Hj.
    case/andP : Hj => Hj1 /eqP => <-.
    apply/matrixP => a b; rewrite {a}(ord1 a).
    by rewrite row_mx_rbehead.
  apply congr_big => // x /=.
  by rewrite rbehead_row_mx eqxx andbT row_mx_row_ord0 eqxx Hi andbT.
move=> i; by case/andP.
Qed.

Lemma big_head_behead_P n (F : 'rV[A]_n.+1 -> R) (P1 : pred A) (P2 : pred 'rV[A]_n) :
  \rsum_(i in A | P1 i) \rsum_(j in 'rV[A]_n | P2 j) (F (row_mx (\row_(k < 1) i) j))
  =
  \rsum_(p in 'rV[A]_n.+1 | (P1 (p /_ ord0)) && (P2 (rbehead p)) ) (F p).
Proof.
symmetry.
rewrite (@partition_big _ _ _ _ _ _ (fun x : 'rV[A]_n.+1 => x /_ ord0)
  (fun x : A => P1 x)) //=.
- apply eq_bigr => i Hi.
  rewrite (reindex_onto (fun j : 'rV[A]_n => row_mx (\row_(k < 1) i) j) rbehead) /=; last first.
    move=> j Hj.
    case/andP : Hj => Hj1 /eqP => <-.
    apply/matrixP => a b; rewrite {a}(ord1 a).
    by rewrite row_mx_rbehead.
  apply congr_big => // x /=.
  by rewrite row_mx_row_ord0 rbehead_row_mx 2!eqxx Hi !andbT.
move=> i; by case/andP.
Qed.

Lemma big_head_behead n (F : 'rV[A]_n.+1 -> R) :
  \rsum_(i in A) \rsum_(j in 'rV[A]_n) (F (row_mx (\row_(k < 1) i) j)) =
  \rsum_(p in 'rV[A]_n.+1) (F p).
Proof. by rewrite big_head_behead_P. Qed.

Lemma big_tcast n (F : n.-tuple A -> R) (P : pred {: n.-tuple A}) m
  (n_m : m = n) :
  \rsum_(p in {: n.-tuple A} | P p) (F p) =
  \rsum_(p in {: m.-tuple A} | P (tcast n_m p)) (F (tcast n_m p)).
Proof.
subst m.
apply eq_bigr => ta.
case/andP => _ H.
by rewrite tcast_id.
Qed.

Local Open Scope tuple_ext_scope.

(* TODO: remove? *)
Lemma rsum_tuple_tnth n i (f : n.+1.-tuple A -> R):
  \rsum_(t | t \in {: n.+1.-tuple A}) f t =
  \rsum_(a | a \in A) \rsum_(t | t \_ i == a) f t.
Proof.
by rewrite (partition_big (fun x : n.+1.-tuple A => x \_ i) xpredT).
Qed.

Local Close Scope tuple_ext_scope.

End big_sums_tuples.

Section sum_tuple_ffun.

Import Monoid.Theory.

Variable R : Type.
Variable times : Monoid.mul_law 0.
Notation Local "*%M" := times (at level 0).
Variable plus : Monoid.add_law 0 *%M.
Notation Local "+%M" := plus (at level 0).

Lemma sum_tuple_ffun (I J : finType) (F : {ffun I -> J} -> R)
  (G : _ -> _ -> _) (jdef : J) (idef : I) :
  \big[+%M/0]_(j : #|I|.-tuple J) G (F (Finfun j)) (nth jdef j 0)
    = \big[+%M/0]_(f : {ffun I -> J}) G (F f) (f (nth idef (enum I) 0)).
Proof.
rewrite (reindex_onto (fun y => fgraph y) (fun p => Finfun p)) //.
apply eq_big; first by case => t /=; by rewrite eqxx.
move=> i _.
f_equal.
  by destruct i.
destruct i as [ [tval Htval] ].
rewrite [fgraph _]/= -(nth_map idef jdef); last first.
  rewrite -cardE.
  apply/card_gt0P.
  by exists idef.
by rewrite -codomE codom_ffun.
Qed.

End sum_tuple_ffun.

Lemma sum_f_R0_rsum : forall k (f : nat -> R),
  sum_f_R0 f k = \rsum_(i<k.+1) f i.
Proof.
elim => [f|] /=.
  by rewrite big_ord_recl /= big_ord0 addR0.
move=> k IH f.
by rewrite big_ord_recr /= IH.
Qed.

Theorem RPascal k (a b : R) :
  (a + b) ^ k = \rsum_(i < k.+1) INR ('C(k, i))* (a ^ (k - i) * b ^ i).
Proof.
rewrite addRC Binomial.binomial sum_f_R0_rsum.
apply eq_bigr => i _.
rewrite combinaison_Coq_SSR; last by rewrite -ltnS.
rewrite -minusE; field.
Qed.

(** Rle, Rlt lemmas for big-mult of reals *)

Reserved Notation "\rmul_ ( i : A | P ) F"
  (at level 41, F at level 41, i, A at level 50,
     format "'[' \rmul_ ( i  :  A  |  P ) '/  '  F ']'").
Reserved Notation "\rmul_ ( i : t ) F"
  (at level 41, F at level 41, i at level 50, only parsing).
Reserved Notation "\rmul_ ( i 'in' A ) F"
  (at level 41, F at level 41, i, A at level 50,
    format "'[' \rmul_ ( i  'in'  A ) '/  '  F ']'").
Notation "\rmul_ ( i | P ) F" := (\big[Rmult/1%R]_( i | P) F)
  (at level 41, F at level 41, i at level 50,
    format "'[' \rmul_ ( i | P ) '/  '  F ']'") : R_scope.
Reserved Notation "\rmul_ ( i < A | P ) F"
  (at level 41, F at level 41, i, A at level 50,
     format "'[' \rmul_ ( i  <  A  |  P ) '/  '  F ']'").
Reserved Notation "\rmul_ ( i < t ) F"
  (at level 41, F at level 41, i, t at level 50,
    format "'[' \rmul_ ( i < t ) '/  '  F ']'").

Notation "\rmul_ ( i : A | P ) F" := (\big[Rmult/R1]_( i : A | P ) F): R_scope.
Notation "\rmul_ ( i : t ) F" := (\big[Rmult/R1]_( i : t ) F) : R_scope.
Notation "\rmul_ ( i 'in' A ) F" := (\big[Rmult/R1]_( i in A ) F) : R_scope.
Notation "\rmul_ ( i < A | P ) F" := (\big[Rmult/R1]_( i < A | P ) F): R_scope.
Notation "\rmul_ ( i < t ) F" := (\big[Rmult/R1]_( i < t ) F) : R_scope.

Section compare_big_mult.

Lemma Rlt_0_big_mult {A : finType} F : (forall i, 0 < F i) ->
  0 < \rmul_(i : A) F i.
Proof.
move=> H.
elim: (index_enum _) => [| hd tl IH].
rewrite big_nil; fourier.
rewrite big_cons; apply Rmult_lt_0_compat => //; by apply H.
Qed.

Lemma Rle_0_big_mult {A : finType} F : (forall i, 0 <= F i) ->
  0 <= \rmul_(i : A) F i.
Proof.
move=> H.
elim: (index_enum _) => [| hd tl IH].
rewrite big_nil; fourier.
rewrite big_cons; apply Rmult_le_pos => //; by apply H.
Qed.

Local Open Scope vec_ext_scope.
Local Open Scope ring_scope.

Lemma Rlt_0_rmul_inv {B : finType} F (HF: forall a, 0 <= F a) :
  forall n (x : 'rV[B]_n.+1),
  0 < \rmul_(i < n.+1) F (x /_ i) -> forall i, 0 < F (x /_ i).
Proof.
elim => [x | n IH].
  rewrite big_ord_recr /= big_ord0 mul1R => Hi i.
  suff : i = ord_max by move=> ->.
  rewrite (ord1 i).
  by apply/val_inj.
move=> x.
set t := \row_(i < n.+1) (x /_ (lift ord0 i)).
rewrite big_ord_recl /= => H.
apply Rlt_0_Rmult_inv in H; last 2 first.
  by apply HF.
  apply Rle_0_big_mult => i; by apply HF.
case.
case=> [Hi | i Hi].
  rewrite (_ : Ordinal _ = ord0); last by apply val_inj.
  by case: H.
case: H => _ H.
have : 0 < \rmul_(i0 < n.+1) F (t /_ i0).
  suff : \rmul_(i < n.+1) F (x /_ (lift ord0 i)) =
    \rmul_(i0 < n.+1) F (t /_ i0).
    by move=> <-.
  apply eq_bigr => j _.
  by rewrite mxE.
have Hi' : (i < n.+1)%nat.
  clear -Hi; by rewrite ltnS in Hi.
move/IH.
move/(_ (Ordinal Hi')).
set o1 := Ordinal _.
set o2 := Ordinal _.
suff : lift ord0 o1 = o2.
  move=> <-.
  by rewrite mxE.
by apply val_inj.
Qed.

(*
Lemma Rlt_0_rmul_inv {B : finType} F (HF: forall a, 0 <= F a) :
  forall n (x : n.+1.-tuple B),
  0 < \rmul_(i < n.+1) F (tnth x i) -> forall i, 0 < F (tnth x i).
Proof.
elim => [x | n IH].
  rewrite big_ord_recr /= big_ord0 mul1R => Hi i.
  suff : i = ord_max by move=> ->.
  rewrite (ord1 i).
  by apply/val_inj.
case/tupleP => h t.
rewrite big_ord_recl /= => H.
apply Rlt_0_Rmult_inv in H; last 2 first.
  by apply HF.
  apply Rle_0_big_mult => i; by apply HF.
case.
case=> [Hi | i Hi].
  by case: H.
case: H => _ H.
have : 0 < \rmul_(i0<n.+1) F (tnth t i0).
  suff : \rmul_(i<n.+1) F (tnth [tuple of h :: t] (lift ord0 i)) =
    \rmul_(i0<n.+1) F (tnth t i0).
    by move=> <-.
  apply eq_bigr => j _.
  f_equal.
have Ht : t = [tuple of behead (h :: t)].
  rewrite (tuple_eta t) /=.
  by apply/val_inj.
rewrite Ht /=.
rewrite tnth_behead /=.
f_equal.
by apply val_inj.
rewrite -(lift0 j).
by rewrite inord_val.
have Hi' : (i < n.+1)%nat.
  clear -Hi; by rewrite ltnS in Hi.
move/IH.
move/(_ (Ordinal Hi')).
suff : (tnth t (Ordinal Hi')) = (tnth [tuple of h :: t] (Ordinal Hi)).
  by move=> ->.
have Ht : t = [tuple of behead (h :: t)].
  rewrite (tuple_eta t) /=.
  by apply/val_inj.
rewrite Ht /= tnth_behead /=.
f_equal.
  by apply val_inj.
apply val_inj => /=; by rewrite inordK.
Qed.
*)

Lemma Rle_1_big_mult {A : finType}  f : (forall i, 1 <= f i) ->
  1 <= \rmul_(i : A) f i.
Proof.
move=> Hf.
elim: (index_enum _) => [| hd tl IH].
- rewrite big_nil; by apply Rle_refl.
- rewrite big_cons -{1}(mulR1 1%R).
  apply Rmult_le_compat => // ; fourier.
Qed.

Local Open Scope R_scope.

Lemma Rle_big_mult {A : finType} f g : (forall i, 0 <= f i <= g i) ->
  \rmul_(i : A) f i <= \rmul_(i : A) g i.
Proof.
move=> Hfg.
case/orP : (orbN [forall i, f i != 0%R]) ; last first.
- rewrite negb_forall => /existsP Hf.
  case: Hf => i0 /negPn/eqP Hi0.
  rewrite (bigD1 i0) //= Hi0 mul0R; apply Rle_0_big_mult.
  move=> i ; move: (Hfg i) => [Hi1 Hi2] ; by apply (Rle_trans _ _ _ Hi1 Hi2).
- move=> /forallP Hf.
  have Hprodf : 0 < \rmul_(i:A) f i.
    apply Rlt_0_big_mult => i.
    move: (Hf i) (Hfg i) => {Hf}Hf {Hfg}[Hf2 _].
    apply/RltP; rewrite Rlt_neqAle eq_sym Hf /=; by apply/RleP.
  apply (Rmult_le_reg_r (1 * / \rmul_(i : A) f i) _ _).
    apply Rlt_mult_inv_pos => //; fourier.
  rewrite mul1R Rinv_r; last by apply not_eq_sym, Rlt_not_eq.
  set inv_spec := fun r => if r == 0 then 0 else / r.
  rewrite (_ : / (\rmul_(a : A) f a) = inv_spec (\rmul_(a : A) f a)) ; last first.
    rewrite /inv_spec (_ : \rmul_(a : A) f a == 0 = false) //.
    apply/eqP ; by apply not_eq_sym, Rlt_not_eq.
  rewrite (@big_morph _ _ (inv_spec) R1 Rmult R1 Rmult _); last 2 first.
  - move=> a b /=.
    case/boolP : ((a != 0) && (b != 0)).
    - move=> /andP [/negbTE Ha /negbTE Hb] ; rewrite /inv_spec Ha Hb.
      move/negbT in Ha ; move/negbT in Hb.
      have : (a * b)%R == 0 = false ; last move=> ->.
      apply/negP => /eqP Habs.
        apply (Rmult_eq_compat_r (/ b)) in Habs ; move: Habs.
        rewrite -mulRA mul0R Rinv_r ?mulR1; move/eqP; by apply/negP.
      apply Rinv_mult_distr; move/eqP; by apply/negP.
    - rewrite negb_and => Hab.
      case/orP : (orbN (a != 0)) => Ha.
      - rewrite Ha /= in Hab; move/negPn/eqP in Hab; rewrite Hab mulR0 /inv_spec.
        by rewrite (_ : 0 == 0 ) // mulR0.
      - move/negPn/eqP in Ha ; rewrite Ha mul0R /inv_spec.
        by rewrite (_ : 0 == 0 ) // mul0R.
  - rewrite /inv_spec.
    have : ~~ (1 == 0).
      apply/eqP => H01; symmetry in H01; move: H01; apply Rlt_not_eq; fourier.
    move/negbTE => -> ; by rewrite Rinv_1.
  rewrite -big_split /=.
  apply Rle_1_big_mult => i.
  move/(_ i) in Hf.
  move: Hfg => /(_ i) [Hf2 Hfg].
  rewrite /inv_spec.
  move/negbTE in Hf ; rewrite Hf ; move/negbT in Hf.
  rewrite -(Rinv_r (f i)); last by move/eqP; apply/negP.
  apply Rmult_le_compat_r => //.
  rewrite -(mul1R (/ f i)).
  apply Rle_mult_inv_pos; first fourier.
  apply/RltP; rewrite Rlt_neqAle eq_sym Hf /=; by apply/RleP.
Qed.

Local Close Scope R_scope.

End compare_big_mult.

Local Open Scope vec_ext_scope.
Local Open Scope ring_scope.

Lemma log_rmul_rsum_mlog {A : finType} (f : A -> R+) : forall n (ta : 'rV[A]_n.+1),
  (forall i, 0 < f ta /_ i) ->
  (- log (\rmul_(i < n.+1) f ta /_ i) = \rsum_(i < n.+1) - log (f ta /_ i))%R.
Proof.
elim => [i Hi | n IH].
  by rewrite big_ord_recl big_ord0 mulR1 big_ord_recl big_ord0 addR0.
move=> ta Hi.
rewrite big_ord_recl /= log_mult; last 2 first.
  by apply Hi.
  apply Rlt_0_big_mult => i; by apply Hi.
set tl := \row_(i < n.+1) ta /_ (lift ord0 i).
have Htmp : forall i0 : 'I_n.+1, 0 < f tl /_ i0.
  move=> i.
  rewrite mxE.
  by apply Hi.
move: {IH Htmp}(IH _ Htmp) => IH.
have -> : \rmul_(i < n.+1) f ta /_ (lift ord0 i) = \rmul_(i0<n.+1) f tl /_ i0.
  apply eq_bigr => i _.
  congr (f _).
  by rewrite /tl mxE.
rewrite Ropp_plus_distr [X in _ = X]big_ord_recl IH.
congr (_ + _)%R.
apply eq_bigr => i _.
by rewrite /tl mxE.
Qed.

(*Lemma log_rmul_rsum_mlog {A : finType} (f : A -> R+) : forall n (ta : n.+1.-tuple A),
  (forall i, 0 < f ta \_ i) ->
  - log (\rmul_(i < n.+1) f ta \_ i) = \rsum_(i < n.+1) - log (f ta \_ i).
Proof.
elim => [i Hi | n IH].
  by rewrite big_ord_recl big_ord0 mulR1 big_ord_recl big_ord0 addR0.
case/tupleP => hd tl Hi.
rewrite big_ord_recl /= log_mult; last 2 first.
  by apply Hi.
  apply Rlt_0_big_mult => i; by apply Hi.
have Htmp : forall i0 : 'I_n.+1, 0 < f tl \_ i0.
  move=> i.
  move: {Hi}(Hi (inord i.+1)) => Hi.
  set rhs := _ \_ _ in Hi.
  suff : tl \_ i = rhs by move=> ->.
  rewrite /rhs -tnth_behead /=.
  f_equal.
  by apply val_inj.
move: {IH Htmp}(IH tl Htmp) => IH.
have -> : \rmul_(i < n.+1) f [tuple of hd :: tl] \_ (lift ord0 i) = \rmul_(i0<n.+1) f tl \_ i0.
  apply eq_bigr => i _.
  f_equal.
  rewrite (_ : lift _ _ = inord i.+1); last by rewrite -lift0 inord_val.
  rewrite -tnth_behead /=.
  f_equal.
  by apply val_inj.
rewrite Ropp_plus_distr [X in _ = X]big_ord_recl IH.
f_equal.
apply eq_bigr => i _.
do 3 f_equal.
rewrite (_ : lift _ _ = inord i.+1); last by rewrite -lift0 inord_val.
rewrite -tnth_behead /=.
f_equal.
by apply val_inj.
Qed.*)

Local Close Scope tuple_ext_scope.
