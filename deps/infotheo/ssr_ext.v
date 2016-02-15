(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice fintype.
From mathcomp Require Import tuple div path bigop prime finset fingroup perm.
Require Import Reals.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** Some additional lemmas about ssrnat, seq, finset, tuple *)

Section ssrnat_ext.

Lemma leq_lt_predn : forall a b : nat, a < b -> a <= b.-1.
Proof. move=> a ; case ; first by rewrite ltn0.
move=> b Hab ; rewrite -ltnS prednK //. Qed.

Lemma mul2_inj a b : a.*2 = b.*2 -> a = b.
Proof. rewrite -!muln2; move/eqP; rewrite eqn_pmul2r //; by move/eqP. Qed.

Lemma nat_of_pos_not_0 : forall p, nat_of_pos p <> O.
Proof.
elim => // p H.
contradict H.
rewrite /= NatTrec.doubleE in H.
apply/eqP; rewrite -double_eq0; by apply/eqP.
Qed.

Lemma nat_of_pos_inj : forall i j, nat_of_pos i = nat_of_pos j -> i = j.
Proof.
elim=> [i Hi [] | i Hi [] | j /=].
- move=> j /= [].
  rewrite !NatTrec.doubleE => Hj; f_equal.
  by apply Hi, mul2_inj.
- move=> j /=.
  rewrite !NatTrec.doubleE => Hj.
  have absurd : odd ((nat_of_pos j).*2) by rewrite -Hj /= odd_double.
  by rewrite odd_double in absurd.
- rewrite /= NatTrec.doubleE.
  case => Habsurd.
  suff : False by done.
  move: (@nat_of_pos_not_0 i).
  by destruct (nat_of_pos i).
- move=> j /=.
  rewrite !NatTrec.doubleE => Hj.
  have absurd : odd ((nat_of_pos i).*2) by rewrite Hj /= odd_double.
  by rewrite odd_double in absurd.
- move=> j /= [].
  rewrite !NatTrec.doubleE => Hj; f_equal.
  by apply Hi, mul2_inj.
- rewrite /= NatTrec.doubleE => absurd.
  suff : False by done.
  move: (@nat_of_pos_not_0 i).
  by destruct (nat_of_pos i).
  destruct j => //=;
    rewrite NatTrec.doubleE => absurd ;
      have [//] : False ;
        move: (@nat_of_pos_not_0 j) => H' ;
          by destruct (nat_of_pos j).
Qed.

Lemma bin_of_nat_inj : forall a b, bin_of_nat a = bin_of_nat b -> a = b.
Proof.
move=> a b X.
have : nat_of_bin (bin_of_nat a) = nat_of_bin (bin_of_nat b) by rewrite X.
by rewrite 2!bin_of_natK.
Qed.

Lemma bin_of_nat_nat_of_pos_not_0 : forall i, bin_of_nat (nat_of_pos i) <> 0%num.
Proof.
elim=> // a Ha /=.
rewrite NatTrec.doubleE.
contradict Ha.
by destruct (nat_of_pos a).
Qed.

Lemma expn_2 : forall r, r <= (expn 2 r).-1.
Proof.
case=> // r; rewrite -subn1 ltn_subRL addnC addn1; by apply ltn_expl.
Qed.

End ssrnat_ext.

Section seq_ext.

Variables A B : Type.

Lemma behead_zip : forall n (a : seq A) (b : seq B),
  size a = n.+1 -> size b = n.+1 ->
  zip (behead a) (behead b) = behead (zip a b).
Proof.
elim.
by case=> // h1 [] // [].
by move=> m IH [|h1 t1] // [|h2 t2].
Qed.

Lemma zip_swap : forall (a : seq A) (b : seq B),
  zip a b = map (fun x => (x.2, x.1)) (zip b a).
Proof. elim => [ [] // | h t IH [|hd tl] //=]; by rewrite IH. Qed.

Lemma sumn_big_addn s : sumn s = \sum_ ( i <- s ) i.
Proof.
elim s => [|a l HR] /= ; first by rewrite big_nil.
by rewrite -cat1s big_cat /= big_seq1 HR.
Qed.

Lemma filter_flatten T u (s : seq (seq T)) : filter u (flatten s) = flatten (map (filter u) s).
Proof.
elim s => // hd tl HR.
rewrite -cat1s map_cat !flatten_cat filter_cat -HR.
f_equal ; by rewrite /flatten /= 2!cats0.
Qed.

Lemma drop_take_iota a b c : a <= b <= c ->
  drop a (take b (iota 0 c)) = filter (fun n => a <= n < b) (iota 0 c).
Proof.
move=> /andP [Hab Hbc].
set f := fun n => a <= n < b.
rewrite -(subnKC Hbc) iota_add take_cat size_iota subnn take0 add0n (ltnn b) cats0 filter_cat.
rewrite (_ : filter f (iota b (c-b)) = [::]) ; last first.
  apply/eqP/negPn ; rewrite -has_filter ; apply/hasPn => l.
  rewrite mem_iota (subnKC Hbc) /f negb_and => /andP [H _].
  by rewrite -leqNgt H orbT.
rewrite cats0 -(subnKC Hab) iota_add drop_cat size_iota subnn drop0 add0n (ltnn a) filter_cat.
rewrite (_ : filter f (iota 0 a) = [::]) ; last first.
  apply/eqP/negPn ; rewrite -has_filter ; apply/hasPn => l.
  rewrite mem_iota /f negb_and add0n => /andP [_ H].
  by rewrite -ltnNge H orTb.
rewrite cat0s.
symmetry ; apply/all_filterP/allP.
move=> l.
by rewrite mem_iota /f (subnKC Hab).
Qed.

Lemma take_take : forall (n m :nat) (s : seq A), take n (take (n + m) s) = take n s.
Proof.
elim=> [* | n0 IH m0 z0].
- by rewrite !take0.
- destruct z0 => //=; by rewrite IH.
Qed.

Lemma take_drop_take : forall m n (z : seq A),
  m + n <= size z -> take n (drop m (take (m + n) z)) = (drop m (take (m + n) z)).
Proof.
elim=> [n0 z Hsz | m IH n1 [|hd tl] //=].
- rewrite drop0 add0n take_oversize // size_take.
  case: ifP => // {Hsz}.
  move/negbT; by rewrite -leqNgt.
rewrite addnC addnS => ?; by rewrite IH // addnC.
Qed.

Lemma zip_mask : forall bs (al : seq A) (bl : seq B),
  zip (mask bs al) (mask bs bl) = mask bs (zip al bl).
Proof.
elim=> // h t IH [|a1 a2] [|b1 b2] //=.
- destruct h => //=; by case: mask.
- destruct h => //=; by case: mask.
- destruct h => /=; by rewrite IH.
Qed.

Lemma nseq_add : forall n (a : A) m, nseq (n + m) a = nseq n a ++ nseq m a.
Proof. elim=> // n0 IH a m; by rewrite addSn /= IH. Qed.

Variable def : A.

Lemma nseq_S : forall n, nseq n.+1 def = nseq n def ++ [:: def].
Proof. by elim=> //= n <-. Qed.

Lemma rev_nseq : forall n, rev (nseq n def) = nseq n def.
Proof. elim=> // n H; by rewrite nseq_S rev_cat H /= -nseq_S. Qed.

Lemma nseq_cat : forall (l1 l2 : seq A) n n1, size l1 = n1 ->
  l1 ++ l2 = nseq n def ->
  l1 = nseq n1 def /\ l2 = nseq (n - n1) def.
Proof.
elim/last_ind => [l2 n [] // _ /= ? | h1 t1 IH l2 n []].
- by rewrite subn0.
- by rewrite size_rcons.
- move=> n1; rewrite size_rcons; move=> [] Hh1.
  rewrite cat_rcons => X.
  destruct n.
  * by destruct h1.
  * have [i Hi] : exists i, n.+1 - n1 = i.+1.
      rewrite subSn; last first.
        match goal with | X : ?a = ?b |- _ =>
          have {X}X : (size a = size b) by rewrite X
        end.
        rewrite size_nseq size_cat /= addnS Hh1 in X.
        move/eqP : X; rewrite eqSS; move/eqP => <-.
        by apply leq_addr.
      by exists (n - n1).
   case: (IH (t1 :: l2) _ _ Hh1 X) => IH1.
   rewrite Hi; case=> IH2 IH3; subst t1.
   rewrite nseq_S IH1 -cat_rcons cats0 subSS.
   split; first by done.
   rewrite subSn in Hi; last first.
     have -> : n = (size (nseq n.+1 def)).-1.
       by rewrite size_nseq.
     rewrite -X size_cat /= addnS /= Hh1; by apply leq_addr.
   by case: Hi => ->.
Qed.

Lemma map_nil_inv : forall (f : A -> B) (l : seq A), map f l = [::] -> l = [::].
Proof. by move=> f; case. Qed.

End seq_ext.

Section seq_eqType_ext.

Variables A B : eqType.

Lemma mem_nseq (l : A) k (i : A) : l \in nseq k i -> (l == i).
Proof.
have : nseq k i = nseq (size (nseq k i)) i by rewrite size_nseq.
by move/all_pred1P/allP/(_ l).
Qed.

Lemma in_cat (s : seq A) x : x \in s -> exists hd tl, s = hd ++ x :: tl.
Proof.
elim: s => // h t IH; rewrite in_cons; case/orP.
- move/eqP => ?; subst h.
  by exists [::], t.
- case/IH => h1 [] t1 ht1.
  exists (h ::h1), t1 => /=.
  congruence.
Qed.

Lemma rev_inj : forall (a b : seq A), rev a = rev b -> a = b.
Proof.
elim => [ [] // hb tb | ta ha IH [| hb tb] //].
- rewrite rev_cons -cats1; by destruct (rev tb).
- rewrite rev_cons -cats1; by destruct (rev ha).
- rewrite !rev_cons.
  move/eqseqP; rewrite eqseqE eqseq_rcons.
  case/andP; move/eqP; move/IH => ->; by move/eqP => ->.
Qed.

Lemma sorted_cat (l1 l2 : seq A) (Rel : @rel A) :
  sorted Rel l1 -> sorted Rel l2 ->
  (forall a, a \in l1 -> forall b, b \in l2 -> Rel a b) ->
  sorted Rel (l1 ++ l2).
Proof.
move=> Hl1 Hl2 H.
destruct l1 => //.
rewrite /sorted /= cat_path.
rewrite /sorted in Hl1.
apply/andP; split => //.
destruct l2 => //.
rewrite /sorted in Hl2.
rewrite /= Hl2 andbC /=.
apply H.
by rewrite mem_last.
by rewrite in_cons eqxx.
Qed.

Lemma sorted_is_flattened leT (Htrans : transitive leT) (Hanti : antisymmetric leT) (Hrefl : reflexive leT) : forall n (lst v : seq A),
  n = size lst -> uniq lst -> sorted leT lst ->
  sorted leT v -> (forall i, i \in v -> i \in lst) ->
  v = flatten (map (fun elt => filter (pred1 elt) v) lst).
Proof.
elim=> /=.
  case=> //.
  move=> v _ _ _ Hv H.
  destruct v => //.
  suff : false by done.
  move: (H s).
  rewrite in_cons eqxx /= in_nil.
  by apply.
move=> n0 IH [|hd tl] // v [lst_sz] lst_uniq lst_sorted v_sorted Hincl.
have X1 : v = filter (pred1 hd) v ++ filter (predC (pred1 hd)) v.
  apply eq_sorted with leT => //.
  - apply: sorted_cat.
    + by apply sorted_filter.
    + by apply sorted_filter.
    + move=> a.
      rewrite mem_filter.
      case/andP => /= /eqP ?; subst hd => av b.
      rewrite mem_filter.
      case/andP => /= ba bv.
      apply Hincl in bv.
      rewrite in_cons in bv.
      case/orP : bv.
      * move/eqP => ?; by subst b.
      * move=> btl.
        rewrite /sorted in lst_sorted.
        move: (@subseq_order_path _ _ (Htrans) a [:: b] tl).
        rewrite /= andbC /=.
        apply => //; by rewrite sub1seq.
  - rewrite perm_eq_sym; by apply perm_eqlE, perm_filterC.
rewrite {1}X1 {X1} /=.
f_equal.
simpl in lst_uniq. case/andP : lst_uniq => hdtl tl_uniq.
rewrite (IH tl (filter (predC (pred1 hd)) v) lst_sz tl_uniq).
- f_equal.
  apply eq_in_map => i i_tl.
  rewrite -filter_predI.
  apply eq_in_filter => j j_v /=.
  case/orP : (orbN ( j == i)) => ij.
  + rewrite ij /=.
    apply/negP.
    move/eqP => ?; subst j.
    move/eqP : ij => ?; subst i.
    by rewrite i_tl in hdtl.
  + move/negbTE in ij;  by rewrite ij.
- destruct tl => //=.
  rewrite /= in lst_sorted.
  by case/andP : lst_sorted.
- apply sorted_filter => //.
- move=> i.
  rewrite mem_filter.
  case/andP => /= Hi.
  move/Hincl.
  rewrite in_cons.
  case/orP => // /eqP.
  move=> ?; subst i.
  by rewrite eqxx in Hi.
Qed.

Lemma filter_zip_L m (al : seq A) (bl : seq B) a :
  size al = m -> size bl = m ->
  filter (fun x => x.1 == a) (zip al bl) =
  zip (filter (pred1 a) al) (mask (map (pred1 a) al) bl).
Proof.
move=> mal mbl.
rewrite filter_mask.
symmetry. rewrite filter_mask zip_mask. symmetry.
f_equal.
elim: m al bl mal mbl a.
  case=> //; by case.
move=> m IHm [|a1 a2] // [|b1 b2] // [sza2] [szb2] a /=; by rewrite IHm.
Qed.

Lemma filter_zip_R m (al : seq A) (bl : seq B) b :
  size al = m -> size bl = m ->
  filter (fun x => x.2 == b) (zip al bl) =
  zip (mask (map (pred1 b) bl) al)
     (filter (pred1 b) bl).
Proof.
move=> mal mbl.
rewrite filter_mask.
symmetry. rewrite filter_mask zip_mask. symmetry.
f_equal.
elim: m al bl mal mbl b.
  case=> //; by case.
move=> m IHm [|a1 a2] // [|b1 b2] // [sza2] [szb2] b /=; by rewrite IHm.
Qed.

Lemma undup_nil_inv : forall (l : seq A), undup l = [::] -> l = [::].
Proof.
elim=> // h t IH /=.
case/orP : (orbN (h \in t)) => X.
rewrite X; move/IH => ?; by subst t.
by rewrite (negbTE X).
Qed.

Lemma undup_filter : forall (P : pred B) x, undup (filter P x) = filter P (undup x).
move=> P; elim=> // h t IH /=.
case/orP : (orbN (P h)) => X.
- rewrite X /=.
  case/orP : (orbN (h \in t)) => Y.
  + rewrite Y /=.
    have -> : h \in filter P t by rewrite mem_filter X Y.
    done.
  + rewrite (negbTE Y).
    have -> : h \in filter P t = false by rewrite mem_filter (negbTE Y) andbC.
    by rewrite IH /= X.
- rewrite (negbTE X) IH.
  case/orP : (orbN (h \in t)) => Y.
  + by rewrite Y.
  + by rewrite (negbTE Y) /= (negbTE X).
Qed.

Lemma undup_perm : forall (f : A -> B) p h t, undup (map f p) = h :: t ->
  exists preh : seq A,
    exists pret : seq A,
      perm_eq p (preh ++ pret) /\
      undup (map f preh) = [:: h] /\ undup (map f pret) = t.
Proof.
move=> f p h t p_t.
exists (filter (preim f [pred x | x == h]) p), (filter (preim f [pred x | x \in t]) p).
split.
- apply/perm_eqlP => x.
  rewrite -(@perm_filterC A (preim f [pred x | (x == h)]) p).
  move: x.
  apply/perm_eqlP.
  rewrite perm_cat2l (@eq_in_filter _ _ [pred x | (f x \in t)]) //.
  move=> x X /=.
  case/orP : (orbN (f x == h)) => Y.
  + rewrite Y /=.
    symmetry.
    apply/negP => abs.
    move/eqP : Y => Y; subst h.
    have : uniq (f x :: t).
      rewrite -p_t; by apply undup_uniq.
    by rewrite /= abs.
  - rewrite Y.
    symmetry.
    have Htmp : f x \in map f p by apply/mapP; exists x.
    have {Htmp}Htmp : f x \in h :: t by rewrite -p_t mem_undup.
    rewrite in_cons in Htmp.
    case/orP : Htmp => [Htmp|->//].
    by rewrite Htmp in Y.
- split.
  + rewrite -filter_map undup_filter p_t /= eqxx.
    have -> : filter [pred x | x == h] t = [::]; last by done.
    apply trans_eq with (filter pred0 t); last by apply filter_pred0.
    apply eq_in_filter => i Hi /=.
    apply/negP => X.
    move/eqP : X => X; subst h.
    have : uniq (i :: t).
      rewrite -p_t; by apply undup_uniq.
    rewrite /=.
    case/andP => H1 H2.
    by rewrite Hi in H1.
  + rewrite -filter_map undup_filter p_t /=.
    have -> : h \in t = false.
      apply/negP => X.
      have : uniq (h :: t).
        rewrite -p_t.
        by apply undup_uniq.
      by rewrite /= X.
    apply trans_eq with (filter predT t); last by apply filter_predT.
    by apply eq_in_filter.
Qed.

End seq_eqType_ext.

Section ordered_ranks.

Variable X : finType.

Definition le_rank (x y : X) := enum_rank x <= enum_rank y.

Definition lt_rank x y := le_rank x y && (x != y).

Lemma lt_rank_alt x0 x1 : lt_rank x0 x1 = (enum_rank x0 < enum_rank x1).
Proof.
rewrite /lt_rank /le_rank ltn_neqAle andbC.
apply andb_id2r => _.
case/orP : (orbN (x0 != x1)) => Hcase.
- rewrite Hcase.
  symmetry ; apply/eqP => abs ; move: Hcase.
  apply/negP/negPn/eqP.
  apply: enum_rank_inj => /=.
  by apply ord_inj.
- move/negbTE in Hcase ; rewrite Hcase ; move/negbT/negPn/eqP in Hcase.
  symmetry ; apply/eqP ; by subst.
Qed.

Definition sort_le_rank : seq X -> seq X := sort le_rank.

Variable n : nat.

Definition sort_le_rank_tuple (y : n.-tuple X) : n.-tuple X.
apply Tuple with (sort_le_rank y).
by rewrite size_sort size_tuple.
Defined.

Lemma transitive_le_rank : transitive le_rank.
Proof. rewrite /le_rank /transitive => a b c /leq_trans; by apply. Qed.

Lemma reflexive_le_rank : reflexive le_rank.
Proof. by rewrite /le_rank /reflexive => a. Qed.

Lemma antisymmetric_le_rank : antisymmetric le_rank.
Proof.
rewrite /le_rank /antisymmetric => a b H ; apply enum_rank_inj.
rewrite -eqn_leq in H ; by apply/eqP.
Qed.

Lemma total_le_rank : total le_rank.
Proof.
rewrite /total /le_rank => a b.
case/orP : (orbN (enum_rank a <= enum_rank b)) ; move=> Hcase ; first by rewrite Hcase /=.
move/negbTE in Hcase ; rewrite Hcase /= ; move/negbT in Hcase ; rewrite -ltnNge in Hcase ; by apply ltnW.
Qed.

Lemma lt_le_rank_trans (u v w : X) : lt_rank u v -> le_rank v w -> lt_rank u w.
Proof.
rewrite /lt_rank.
move=> /andP [Huv Diffuv] Hvw.
case/orP : (orbN (u != w)) => Hcase.
- rewrite Hcase andbT.
  apply (transitive_le_rank Huv Hvw).
- move/negPn/eqP in Hcase.
  subst w.
  contradict Diffuv.
  apply/negP/negPn/eqP.
  apply antisymmetric_le_rank.
  by rewrite Huv Hvw.
Qed.

Lemma le_lt_rank_trans (u v w : X) : le_rank u v -> lt_rank v w -> lt_rank u w.
Proof.
rewrite /lt_rank.
move=> Huv /andP [Hvw Diffvw].
case/orP : (orbN (u != w)) => Hcase.
- rewrite Hcase andbT.
  apply (transitive_le_rank Huv Hvw).
- move/negPn/eqP in Hcase.
  subst w.
  contradict Diffvw.
  apply/negP/negPn/eqP.
  apply antisymmetric_le_rank.
  by rewrite Huv Hvw.
Qed.

Lemma lt_le_rank_weak (u v : X) : lt_rank u v -> le_rank u v.
Proof. by rewrite /lt_rank => /andP [H _]. Qed.

Lemma lt_neq_rank (u v : X) : lt_rank u v -> u != v.
Proof. by rewrite /lt_rank => /andP [_ H]. Qed.

End ordered_ranks.

Section finset_ext.

Variable A : finType.

Lemma seq_index_enum_card : forall l (Y : {set A}) i,
  l =i enum Y -> uniq l ->
  i \in Y -> (seq.index i l < #| Y |)%nat.
Proof.
elim => [Y i Hl Hl' Hi | h t IH Y i Hl Hl' Hi /= ].
  have {Hi}Hi : i \in enum Y by rewrite mem_enum.
  by rewrite -Hl in Hi.
case: ifP => // Hif.
  rewrite card_gt0.
  apply/negP.
  move/eqP => Habs.
  by rewrite Habs inE in Hi.
apply leq_ltn_trans with (#|Y :\ h|); last first.
  rewrite (cardsD1 h Y).
  suff : h \in Y by move=> ->; rewrite addnC addn1.
  by rewrite -mem_enum -Hl in_cons eqxx.
apply IH.
- move=> j.
  move H1 : (j \in (enum (Y :\ h))) => [].
    rewrite mem_enum in_setD1 in H1.
    case/andP : H1 => H1.
    rewrite -mem_enum -Hl in_cons.
    case/orP => H1' //.
    by rewrite H1' in H1.
  move: H1.
  rewrite mem_enum in_setD1.
  move/negbT.
  rewrite negb_and.
  case/orP => [|H1].
  - move/negPn/eqP => ?; subst j.
      apply/negP => Habs'.
      rewrite /= in Hl'.
      by rewrite Habs' in Hl'.
  - rewrite -mem_enum -Hl in H1.
    apply/negP/negP.
    move: H1; apply: contra.
    rewrite in_cons.
    move=> ->; by rewrite orbC.
- rewrite /= in Hl'; by case/andP: Hl'.
- apply/setD1P.
  move/negbT in Hif.
  split; last by done.
  move: Hif.
  apply contra.
  by move/eqP => ->.
Qed.

Lemma sorted_enum : sorted (@le_rank A) (enum A).
Proof.
rewrite /sorted.
move HA : (enum A) => Alst.
destruct Alst => //.
apply/(pathP s) => i Hi.
rewrite /le_rank -HA.
destruct Alst => //.
have Hi' : (i < #|A|)%nat.
  rewrite cardE HA.
  by apply (ltn_trans Hi).
rewrite -(@enum_val_nth A (xpredT) s (Ordinal Hi')).
have Hi'' : (i.+1 < #|A|)%nat.
  rewrite cardE HA.
  by apply (leq_ltn_trans Hi).
have -> : (nth s (s0 :: Alst) i) = (nth s (enum A) i.+1).
  by rewrite /= HA.
rewrite -(@enum_val_nth A (xpredT) s (Ordinal Hi'')).
rewrite 2!enum_valK.
by apply leqnSn.
Qed.

Lemma cardsltn1P (s : {set A}) :
  (1 < #| s |) = [exists a, exists b, (a \in s) && (b \in s) && (a != b)].
Proof.
case/boolP : (s == set0) => [ /eqP -> | /set0Pn [] /= a Ha ].
  rewrite cards0 /=.
  apply/esym/negbTE.
  rewrite negb_exists.
  apply/forallP => a.
  rewrite negb_exists.
  apply/forallP => b.
  by rewrite !inE.
case/boolP : (s :\ a == set0) => [sa | ].
  have Hs : s == [set a].
    apply/eqP/setP => /= a'.
    move/eqP/setP/(_ a') in sa.
    rewrite !inE in sa.
    move/negbT in sa.
    rewrite negb_and negbK in sa.
    case/orP : sa => sa.
      move/eqP in sa; subst a'.
      by rewrite inE eqxx.
    rewrite (negbTE sa) inE.
    apply/esym/negbTE.
    apply/eqP => ?; subst a'.
    by rewrite Ha in sa.
  rewrite (eqP Hs) cards1.
  apply/esym/negbTE.
  rewrite negb_exists.
  apply/forallP => b.
  rewrite negb_exists.
  apply/forallP => c.
  rewrite 2!in_set1.
  case/boolP : (b == c).
    move/eqP => ?; subst c; by rewrite /= andbC.
  rewrite /= andbT negb_and => bc.
  case/boolP : (b == a) => // /eqP ?; subst b => /=; by rewrite eq_sym.
case/set0Pn => b Hb.
have -> : 1 < #| s |.
  by rewrite (cardsD1 a s) Ha /= (cardsD1 b (s :\ a)) Hb.
apply/esym; apply/existsP; exists a; apply/existsP; exists b.
rewrite !inE eq_sym in Hb.
case/andP : Hb => -> ->; by rewrite Ha.
Qed.

End finset_ext.

Lemma ord0_false : forall i : 'I_0, False.
Proof. by case=> [] []. Qed.

Lemma ord1 : forall i : 'I_1, i = ord0. Proof. case=> [[]] // ?; exact/eqP. Qed.

Module Two_set.

Section two_set.

Variable X : finType.

Hypothesis HX : #|X| = 2%nat.

Definition val0 := enum_val (cast_ord (sym_eq HX) ord0).

Definition val1 := enum_val (cast_ord (sym_eq HX) (lift ord0 ord0)).

Lemma enum : enum X = val0 :: val1 :: [::].
Proof.
apply (@eq_from_nth _ val0); first by rewrite -cardE HX.
move=> i Hi.
destruct i.
  by rewrite [X in _ = X]/= {2}/val0 (enum_val_nth val0).
destruct i; last first.
  rewrite -cardE HX in Hi.
  by destruct i.
by rewrite [X in _ = X]/= {1}/val1 (enum_val_nth val0).
Qed.

Lemma val0_neq_val1 : val0 != val1.
Proof. rewrite /val0 /val1. apply/eqP. by move/enum_val_inj. Qed.

Lemma neq_val0_val1 : forall x, x != val0 -> x == val1.
Proof.
move=> x xi.
have : x \in X by done.
rewrite -mem_enum enum !inE.
case/orP => // abs.
by rewrite abs in xi.
Qed.

End two_set.

End Two_set.

Notation "t '\_' i" := (tnth t i) (at level 9) : tuple_ext_scope.

Local Open Scope tuple_ext_scope.

Section tuple_ext.

Variable A : Type.

Lemma tcast_take_simpl n m k (H : minn n k = m) (nk : n = k) (t v : k.-tuple A) :
  tcast H [tuple of take n t] = tcast H [tuple of take n v] -> t = v.
Proof.
subst m => /=.
subst n; case => /= Htv.
apply eq_from_tnth => i.
by rewrite (tnth_nth t\_i) [in X in _ = X](tnth_nth t\_i) -(@nth_take k) // -[in X in _ = X](@nth_take k) // Htv.
Qed.

End tuple_ext.

Section tuple_ext_finType.

Variables A B : finType.
Variable n : nat.

Lemma tnth_zip_1 (x1 : n.-tuple A) (x2 : n.-tuple B) i:
  (tnth [tuple of zip x1 x2] i).1 = tnth x1 i.
Proof.
rewrite /tnth.
set def := tnth_default _ _.
destruct def as [def1 def2].
rewrite nth_zip /=; last by rewrite !size_tuple.
apply set_nth_default.
by rewrite size_tuple.
Qed.

Lemma tnth_zip_2 (x1 : n.-tuple A) (x2 : n.-tuple B) i:
  (tnth [tuple of zip x1 x2] i).2 = tnth x2 i.
Proof.
rewrite /tnth.
set def := tnth_default _ _.
destruct def as [def1 def2].
rewrite nth_zip /=; last by rewrite !size_tuple.
apply set_nth_default.
by rewrite size_tuple.
Qed.

Lemma thead_tuple1 : forall (i : 1.-tuple A), [tuple thead i] = i.
Proof. move=> [ [|h []] H] //. by apply val_inj. Qed.

Lemma eq_tcast (t : {:n.-tuple A}) m (t' : {:m.-tuple A}) (H' : m = n) :
  tval t = tval t' -> t = tcast H' t'.
Proof.
subst m.
rewrite tcast_id.
move=> tt'.
by apply val_inj.
Qed.

Lemma eq_tcast2 (t : seq A) m (t' : {:m.-tuple A}) (H : m = n) :
  t = tval t' -> t = tval (tcast H t').
Proof. subst m. by rewrite tcast_id. Qed.

End tuple_ext_finType.

Definition tbehead (n : nat) (T : Type) (t : (n.+1).-tuple T) : n.-tuple T :=
  [tuple of behead t].

Section perm_tuples.

Local Open Scope nat_scope.
Local Open Scope group_scope.

Variables A : finType.
Variable n : nat.
Variable s : 'S_n.

Definition perm_tuple (t : n.-tuple A) : n.-tuple A := [tuple (t \_ (s i)) | i < n].
Definition perm_tuple_set (E : {set n.-tuple A}) := perm_tuple @: E.

End perm_tuples.

Section perm_tuples_facts.

Variable A : finType.

Local Open Scope group_scope.

Lemma perm_tuple_id {m} (b : m.-tuple A) : perm_tuple 1 b = b.
Proof.
apply eq_from_tnth => i.
by rewrite /perm_tuple /= tnth_map /= perm1 tnth_ord_tuple.
Qed.

Variable n : nat.

Lemma perm_tuple_comp (s1 s2 : 'S_n) (b : n.-tuple A) :
  perm_tuple s1 (perm_tuple s2 b) = perm_tuple (s1 * s2) b.
Proof.
apply eq_from_tnth => i.
by rewrite /perm_tuple !tnth_map /= tnth_ord_tuple permM.
Qed.

Lemma perm_tuple_inj (s : 'S_n) : injective (@perm_tuple A n s).
Proof.
rewrite /injective.
move=> a b H.
have H2 : perm_tuple 1 a = perm_tuple 1 b.
- rewrite -(mulVg s).
  rewrite -!perm_tuple_comp.
  f_equal ; apply H.
rewrite !perm_tuple_id in H2 ; apply H2.
Qed.

Lemma perm_tuple0 : forall (u : 'S_0) (t : 0.-tuple A), perm_tuple u t = t.
Proof.
move=> u t.
rewrite (tuple0 t).
have -> : u = 1%g.
  apply/permP => /= x.
  suff : False by done.
  by move/ord0_false in x.
by rewrite perm_tuple_id.
Qed.

Variable B : finType.

Lemma zip_perm_tuple (ta : n.-tuple A) (tb : n.-tuple B) (s : 'S_n) :
  zip_tuple (perm_tuple s ta) (perm_tuple s tb) = perm_tuple s (zip_tuple ta tb).
Proof.
apply eq_from_tnth.
case.
destruct n => //.
case=> [Hi | i Hi].
  rewrite (tnth_nth (thead ta, thead tb)) (tnth_nth (thead (zip_tuple ta tb))).
  rewrite /= enum_ordS /= (tnth_nth (thead ta, thead tb)) /= nth_zip; last
    by rewrite (size_tuple ta) (size_tuple tb).
  by rewrite (tnth_nth (thead ta)) /= (tnth_nth (thead tb)) /=.
rewrite (tnth_nth (thead ta, thead tb)) (tnth_nth (thead (zip_tuple ta tb))) /= enum_ordS /=.
rewrite ltnS in Hi.
rewrite nth_zip; last by rewrite 4!size_map size_enum_ord.
symmetry.
rewrite (nth_map ord0); last by rewrite size_map size_enum_ord.
rewrite (tnth_nth (thead ta, thead tb)) /zip_tuple /=.
rewrite nth_zip; last by rewrite (size_tuple ta) (size_tuple tb).
symmetry.
rewrite (nth_map ord0); last by rewrite size_map size_enum_ord.
rewrite (nth_map ord0); last by rewrite size_map size_enum_ord.
by rewrite (tnth_nth (thead ta)) (tnth_nth (thead tb)).
Qed.

End perm_tuples_facts.

Lemma tcast2tval (T : Type) (m n0 : nat) (H : m = n0) : forall (v : m.-tuple T) w,
  tcast H v = w -> tval v = tval w.
Proof. subst n0. by move=> [v Hv] [w Hw] <- /=. Qed.
