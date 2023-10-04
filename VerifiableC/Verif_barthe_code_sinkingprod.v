(* ================================================================= *)
(* antonoupoulous_sa_simple.c - no array for this*)

Require VC.Preface. 
Require Import Setoid.
From Coq Require Import ZArith.Int.
Require Import VST.floyd.proofauto.
Require Import Coq.Classes.RelationClasses.

Require Import VC.barthe_code_sinking.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

(*max - fixedpoint to def. using fold*)
Search fold_right.
Definition sum_max : Z -> list Z ->  Z := fold_right Z.max.


Lemma summax_correct: forall l : list Z,
 Forall (fun x  => 0 <= x <= Int.max_unsigned) l ->
 Forall (fun x => 0 <= x <= sum_max 0 l) l.
Proof.
  intros. induction l.
  apply Forall_nil. apply Forall_cons.
  unfold sum_max. simpl. 
  (*Z.le_max_l*)
  split. rewrite Forall_forall in H by lia.
  specialize H with a. apply H. apply in_eq.
  apply Z.le_max_l. rewrite Forall_forall.
  intros. autorewrite with sublist. unfold sum_max. 
  rewrite fold_right_cons.
  apply Forall_inv_tail in H. apply IHl in H.
  rewrite Forall_forall in H. specialize H with x.
  apply H in H0. unfold sum_max in H0. 
  split. lia. lia.
Qed.

Lemma summax_range: forall l : list Z,
 Forall (fun x  => 0 <= x <= Int.max_unsigned) l ->
 0 <= sum_max 0 l <= Int.max_unsigned.
Proof.
  induction l. intros.
  simpl. compute. split.
  try congruence. try congruence.
  intros.  simpl. 
  destruct (a =? (sum_max 0 l)) eqn:HDz.
  apply Z.eqb_eq in HDz.
  rewrite <- HDz. rewrite Z.max_id.
  rewrite Forall_forall in H. specialize H with a. apply H.
  apply in_eq. apply Z.eqb_neq in HDz.
  apply not_Zeq in HDz.
  destruct HDz as [? | ?]. 
  apply Z.lt_le_incl in H0.
  apply Z.max_r in H0. rewrite H0. apply IHl.
  apply Forall_inv_tail in H.
  assumption. apply Z.lt_le_incl in H0. apply Z.max_r in H0.
  rewrite Z.max_comm in H0. rewrite H0.
  rewrite Forall_forall in H. specialize H with a.
  apply H. apply in_eq.
Qed.

Lemma summax_one: forall (l_i : Z) (l : list Z),
 0 <= l_i < Zlength l ->
 Forall (fun x  => 0 <= x <= Int.max_unsigned) l ->
 0 <= Znth l_i l <= Int.max_unsigned.
Proof.
  intros. rewrite Forall_forall in H0.
  rewrite <- nth_Znth by lia. 
  specialize H0 with (nth (Z.to_nat l_i) l Inhabitant_Z).
  apply H0. simpl. rewrite nth_Znth by lia. apply Znth_In. lia.
Qed.

Lemma summax_app: forall (x : Z) (l: list Z),
 0 <= x <= Int.max_unsigned ->
 sum_max 0 (l ++ [x]) = Z.max (sum_max 0 l) x. 
Proof.
 induction l; intros; simpl. Search Z.max. rewrite Z.max_comm.
 reflexivity.
 rewrite IHl. list_simplify.  assumption.
Qed.

Lemma entailment_swap: forall {cs: compspecs} sh contents li a,
 0 <= li <= 10 ->
 Zlength contents = 11 ->

 data_at sh (tarray tuint 11)
  (upd_Znth li
     (upd_Znth 10
        (map Vint (map Int.repr contents))
        (Vint (Int.repr (Znth li contents))))
     (Vint (Int.repr (Znth 10 contents)))) a
|-- (if Z.eq_dec li 10
     then
      data_at sh (tarray tuint 11)
        (map Vint (map Int.repr contents)) a
     else
      if Z.eq_dec li 0
      then
       data_at sh (tarray tuint 11)
         (Vint (Int.repr (Znth 10 contents))
          :: map Vint
               (map Int.repr
                  (sublist 1 10 contents ++
                   [Znth 0 contents]))) a
      else
       data_at sh (tarray tuint 11)
         (map Vint
            (map Int.repr
               (sublist 0 li contents ++
                Znth 10 contents
                :: sublist (li + 1) 10 contents ++
                   [Znth li contents]))) a).
 Proof.
  intros.
  (*rind =? 10*)
  destruct (Z.eq_dec li 10) eqn:He.
  rewrite e. apply derives_refl'.
  f_equal. rewrite !upd_Znth_map. f_equal. f_equal.  
  pattern (upd_Znth 10 contents (Znth 10 contents)) at 1.
  rewrite upd_Znth_unfold at 1. replace (10 + 1) with 11 by lia.
  rewrite H0.  rewrite sublist_nil. simpl. rewrite upd_Znth_app2.
  rewrite Zlength_sublist by lia. replace (10 - (10 - 0)) with 0 by lia.
  rewrite upd_Znth0. rewrite <- sublist_last_1 by lia. simpl.
  rewrite sublist_same by lia. reflexivity. rewrite !Zlength_sublist by lia. simpl. lia. lia.
  (*second case rind < 10*)
  clear He. apply not_Zeq_inf in n. destruct n.
  (*rind and 0*)
  destruct (li =? 0) eqn:Hi0. apply Z.eqb_eq in Hi0.
  rewrite Hi0. simpl. apply derives_refl'. f_equal.
  rewrite !upd_Znth_map. 
  pattern (upd_Znth 10 contents (Znth 0 contents)) at 1.
  rewrite upd_Znth_unfold at 1.  replace (10 + 1) with 11 by lia.
  rewrite H0. rewrite sublist_nil. simpl. 
  rewrite sublist_next by lia. 
  rewrite upd_Znth_app1. rewrite upd_Znth0. simpl. reflexivity.
  simpl. rewrite Zlength_cons.
  rewrite Zlength_sublist by lia. simpl. lia. lia.
  (*rind is not 0*)
  rewrite Z.eqb_neq in Hi0.
  simpl. destruct (Z.eq_dec li 0) eqn:HeqDec. contradiction.
  apply derives_refl'. f_equal. rewrite !upd_Znth_map.
  f_equal. f_equal. 
  pattern (upd_Znth 10 contents (Znth li contents)) at 1.
  rewrite upd_Znth_unfold at 1.  replace (10 + 1) with 11 by lia.
  rewrite H0. rewrite sublist_nil. simpl. rewrite upd_Znth_app1.
  rewrite upd_Znth_unfold. rewrite Zlength_sublist by lia. simpl.
  rewrite sublist_sublist00 by lia. rewrite <- sublist_parts1 by lia. try list_solve.
  rewrite Zlength_sublist by lia. lia. rewrite Zlength_sublist by lia. lia. lia.
  destruct H. apply Z.lt_gt in l. contradiction.
Qed.
            


(*Functional Model: empty for kestrel*)
(*API spec => verifyfunc spec; left and right are equal *)
Definition verifyfunc_spec : ident * funspec :=
DECLARE _verifyfunc
  WITH l_a : val, r_a : val, sh1 : share, sh2 : share,
  contents_la : list Z, contents_ra : list Z
  PRE [tptr tuint, tptr tuint]  
    (*ensure variables left and right are equal*)
    PROP (
    writable_share sh1; writable_share sh2;
    Forall (fun x => 0 <= x <= Int.max_unsigned) contents_la;
    Forall (fun x => 0 <= x <= Int.max_unsigned) contents_ra;
    Forall2 (fun x y => x = y) contents_la contents_ra)
  PARAMS (l_a;r_a)
    SEP (data_at sh1 (tarray tuint 11) (map Vint (map Int.repr contents_la)) l_a;
    data_at sh2 (tarray tuint 11) (map Vint (map Int.repr contents_ra)) r_a)
  POST [ tvoid ]
    EX lnd : Z, EX rnd : Z, 
    PROP (0 <= lnd < 11; 0 <= rnd < 11; Znth lnd contents_la = Znth rnd contents_ra;
    Forall2 (fun x y => x = y) contents_la contents_ra
    )
    RETURN () (*void*)
    SEP (if Z.eq_dec lnd 10 then (data_at sh1 (tarray tuint 11) (map Vint (map Int.repr contents_la)) l_a)
    else if Z.eq_dec lnd 0 then (data_at sh1 (tarray tuint 11) (map Vint (map Int.repr ([Znth 10 contents_la] ++ sublist 1 10 contents_la ++
    [Znth 0 contents_la]))) l_a)
    else (data_at sh1 (tarray tuint 11) (map Vint (map Int.repr (sublist 0 lnd contents_la ++ [Znth 10 contents_la] ++ sublist (lnd + 1) 10 contents_la ++
    [Znth lnd contents_la])))) l_a;
    if Z.eq_dec rnd 10 then (data_at sh2 (tarray tuint 11) (map Vint (map Int.repr contents_ra)) r_a)
    else if Z.eq_dec rnd 0 then (data_at sh2 (tarray tuint 11) (map Vint (map Int.repr ([Znth 10 contents_ra] ++ sublist 1 10 contents_ra ++
    [Znth 0 contents_ra]))) r_a)
    else (data_at sh2 (tarray tuint 11) (map Vint (map Int.repr (sublist 0 rnd contents_ra ++ [Znth 10 contents_ra] ++ sublist (rnd + 1) 10 contents_ra ++
    [Znth rnd contents_ra])))) r_a).


 Lemma Znth0sublist: forall l: list Z,
    Zlength l = 11 ->
    Forall (fun x : Z => 0 <= x <= Int.max_unsigned) l ->
    Znth 0 l = sum_max 0 (sublist 0 1 l).
  Proof.
    intros l H1 H.
    rewrite sublist_len_1 by lia.
    simpl. apply summax_one with 0 l in H.
    destruct H. apply Z.max_l in H.
    rewrite H. reflexivity. lia.
  Qed.

Lemma eqmaxlist: forall l1 l2: list Z,
  Zlength l1 = Zlength l2 ->
  Forall (fun x : Z => 0 <= x <= Int.max_unsigned) l1 ->
  Forall (fun x : Z => 0 <= x <= Int.max_unsigned) l2 ->
  Forall2 (fun x y : Z => x = y) l1 l2 ->
  sum_max 0 l1 = sum_max 0 l2.
Proof.
  intros. destruct l1,l2.
  reflexivity. rewrite Zlength_nil in H. 
  rewrite Zlength_cons in H.
  unfold Z.succ in H. destruct (Zlength l2) eqn:Zll2. simpl in H.
  discriminate H. discriminate H. 
  assert (Zlength l2 >= 0). {
     apply Z.le_ge. apply Zlength_nonneg.
  }
  rewrite Zll2 in H3. 
  assert (Z.neg p < 0). {
    apply Pos2Z.neg_is_neg.
  }
  contradiction.  
  rewrite Zlength_nil in H. rewrite Zlength_cons in H. 
  destruct (Zlength l1) eqn:Zll1. simpl in H.
  discriminate H. discriminate H. 
  assert (Zlength l1 >= 0). {
     apply Z.le_ge. apply Zlength_nonneg.
  }
  rewrite Zll1 in H3. 
  assert (Z.neg p < 0). {
    apply Pos2Z.neg_is_neg.
  }
  contradiction.  eapply Forall2_cons_iff in H2. 
  destruct H2 as [? ?]. rewrite H2. unfold sum_max. 
  rewrite <- H2. rewrite !fold_right_cons. f_equal. rewrite <- H2 in H,H1.
  rewrite !Zlength_cons in H. apply Z.succ_inj in H. apply Forall_inv_tail in H0,H1.
  induction H3. reflexivity. rewrite H3. rewrite !fold_right_cons. f_equal. 
  rewrite !Zlength_cons in H.  apply Z.succ_inj in H.
  apply IHForall2.  assumption. apply Forall_inv_tail in H0.
  assumption. apply Forall_inv_tail in H1.  assumption.  
Qed.

(*Pack APIs together*)
Definition Gprog := [verifyfunc_spec].

(*verify fun_spec - from here*)
Lemma body_verifyfunc: semax_body Vprog Gprog f_verifyfunc verifyfunc_spec.
Proof. 
 start_function. 
 (*a1 length is M*)
 assert_PROP (Zlength contents_la = 11). {
  entailer!. rewrite <- H3. do 2 rewrite Zlength_map. reflexivity.
 }
 assert_PROP (Zlength contents_ra = 11). {
  entailer!. rewrite <- H7. do 2 rewrite Zlength_map. reflexivity.
 }
 fastforward. 
forward_loop 
  (EX l_i:Z, EX r_i:Z, EX li:Z, EX ri:Z, 
    PROP (0 <= l_i <= 11; 0 <= r_i <= 11; 
    l_i = r_i; 0 <= li < l_i; 0 <= ri < r_i;
    Znth li contents_la = (sum_max 0 (sublist 0 l_i contents_la));
    Znth ri contents_ra = (sum_max 0 (sublist 0 r_i contents_ra)))
   LOCAL (
    temp _r_i (Vint (Int.repr r_i)); 
    temp _rind (Vint (Int.repr ri)); 
    temp _r_max (Vint (Int.repr (sum_max 0 (sublist 0 r_i contents_ra))));  
    temp _l_i (Vint (Int.repr l_i)); 
    temp _lind (Vint (Int.repr li)); 
    temp _l_max (Vint (Int.repr (sum_max 0 (sublist 0 l_i contents_la)))); 
    temp _l_a l_a; temp _r_a r_a)
   SEP (data_at sh1 (tarray tuint 11) 
   (map Vint (map Int.repr contents_la)) l_a;
   if Z_lt_le_dec r_i 11 then (data_at sh2 (tarray tuint 11) (map Vint (map Int.repr contents_ra)) r_a)
   else if Z.eq_dec ri 10 then (data_at sh2 (tarray tuint 11) (map Vint (map Int.repr contents_ra)) r_a)
   else if Z.eq_dec ri 0 then (data_at sh2 (tarray tuint 11) (map Vint (map Int.repr ([Znth 10 contents_ra] ++ sublist 1 10 contents_ra ++
   [Znth 0 contents_ra]))) r_a)
   else (data_at sh2 (tarray tuint 11) (map Vint (map Int.repr (sublist 0 ri contents_ra ++ [Znth 10 contents_ra] ++ sublist (ri + 1) 10 contents_ra ++
   [Znth ri contents_ra])))) r_a)
   )%assert
   break: 
   (EX l_i:Z, EX r_i:Z, EX li:Z, EX ri:Z,
   PROP (0 <= l_i <= 11; 0 <= r_i <= 11; l_i = 11; r_i = 11;
   l_i = r_i; 0 <= li < l_i; 0 <= ri < r_i;
   Znth li contents_la = (sum_max 0 (sublist 0 l_i contents_la));
   Znth ri contents_ra = (sum_max 0 (sublist 0 r_i contents_ra)))
   LOCAL (
    temp _r_i (Vint (Int.repr r_i)); 
    temp _rind (Vint (Int.repr ri)); 
    temp _r_max (Vint (Int.repr (sum_max 0 (sublist 0 r_i contents_ra))));  
    temp _l_i (Vint (Int.repr l_i)); 
    temp _lind (Vint (Int.repr li)); 
    temp _l_max (Vint (Int.repr (sum_max 0 (sublist 0 l_i contents_la)))); 
    temp _l_a l_a; temp _r_a r_a)
   SEP (data_at sh1 (tarray tuint 11) 
   (map Vint (map Int.repr contents_la)) l_a;
   if Z_lt_le_dec r_i 11 then (data_at sh2 (tarray tuint 11) (map Vint (map Int.repr contents_ra)) r_a)
   else if Z.eq_dec ri 10 then (data_at sh2 (tarray tuint 11) (map Vint (map Int.repr contents_ra)) r_a)
   else if Z.eq_dec ri 0 then (data_at sh2 (tarray tuint 11) (map Vint (map Int.repr ([Znth 10 contents_ra] ++ sublist 1 10 contents_ra ++
   [Znth 0 contents_ra]))) r_a)
   else (data_at sh2 (tarray tuint 11) (map Vint (map Int.repr (sublist 0 ri contents_ra ++ [Znth 10 contents_ra] ++ sublist (ri + 1) 10 contents_ra ++
   [Znth ri contents_ra])))) r_a
   ))%assert.
 (*first existential - outermost if*)      
 Exists 1. Exists 1. Exists 0. Exists 0. entailer!.
 {(*prove entailment*)
    split. apply Znth0sublist. assumption. assumption.
    split. apply Znth0sublist. assumption. assumption.
    split. f_equal. f_equal. symmetry. apply Znth0sublist.
    assumption. assumption. f_equal. f_equal. symmetry.
    apply Znth0sublist. assumption. assumption.
 }
 Intros l_i r_i li ri. forward_if. forward. 
 Exists l_i. Exists r_i. Exists li. Exists ri. entailer!.
 forward_if. forward. Exists l_i. Exists r_i. Exists li. Exists ri. entailer!.
 forward. 
 forward_if (
  EX lj : Z, EX lind: Z, 
  PROP(0 <= lind <= l_i; if  Z_lt_ge_dec (sum_max 0 (sublist 0 l_i contents_la))(Znth l_i contents_la) then
   lj = Znth l_i contents_la else lj = sum_max 0 (sublist 0 l_i contents_la);
   if  Z_lt_ge_dec (sum_max 0 (sublist 0 l_i contents_la))(Znth l_i contents_la) then
   lind = l_i else lind = li
   )
  LOCAL (temp _t'7 (Vint (Int.repr (Znth l_i contents_la)));
   temp _r_i (Vint (Int.repr r_i));
   temp _rind (Vint (Int.repr ri));
   temp _r_max (Vint (Int.repr (sum_max 0 (sublist 0 r_i contents_ra))));
   temp _l_i (Vint (Int.repr l_i));
   temp _lind (Vint (Int.repr lind));
   temp _l_max (Vint (Int.repr lj));
   temp _l_a l_a; temp _r_a r_a)
   SEP (data_at sh1 (tarray tuint 11) (map Vint (map Int.repr contents_la)) l_a;
   data_at sh2 (tarray tuint 11) (map Vint (map Int.repr contents_ra)) r_a) 
   ). 
 forward. forward. rewrite !Int.unsigned_repr in H13. Exists (Znth l_i contents_la).
 Exists l_i. entailer!. 
 (*right*)
 unfold Z_lt_ge_dec. 
 destruct (Z_lt_dec (sum_max 0 (sublist 0 r_i contents_la))(Znth r_i contents_la)) eqn:HDe.
 split; reflexivity. contradiction. destruct (Z_lt_le_dec r_i 11) eqn:Hltler.
 entailer!. clear Hltler. apply Z.le_ge in l. contradiction. 
 apply summax_one. lia. assumption.
 eapply summax_range. eapply Forall_sublist in H. eassumption.
 forward.
 (*other way*)
 rewrite !Int.unsigned_repr in H13. Exists (sum_max 0 (sublist 0 l_i contents_la)). 
 Exists li. entailer!.
 unfold Z_lt_ge_dec. 
 destruct (Z_lt_dec (sum_max 0 (sublist 0 r_i contents_la))(Znth r_i contents_la)) eqn:HDe. 
 contradiction. split; reflexivity. destruct (Z_lt_le_dec r_i 11) eqn:Hltler.
 entailer!. clear Hltler. apply Z.le_ge in l. contradiction. 
 apply summax_one. lia. assumption.
 eapply summax_range. eapply Forall_sublist in H. eassumption.
 Intros lj lind. forward.  
 forward_if (
  EX rj : Z, EX rind: Z,
  PROP(0 <= rind <= r_i; if  Z_lt_ge_dec (sum_max 0 (sublist 0 r_i contents_ra))(Znth r_i contents_ra) then
   rj = Znth r_i contents_ra else rj = sum_max 0 (sublist 0 r_i contents_ra);
   if  Z_lt_ge_dec (sum_max 0 (sublist 0 r_i contents_ra))(Znth r_i contents_ra) then
   rind = r_i else rind = ri
   )
  LOCAL (temp _t'6 (Vint (Int.repr (Znth r_i contents_ra)));
   temp _t'7 (Vint (Int.repr (Znth l_i contents_la)));
   temp _r_i (Vint (Int.repr r_i));
   temp _rind (Vint (Int.repr rind));
   temp _r_max (Vint (Int.repr rj));
   temp _l_i (Vint (Int.repr l_i));
   temp _lind (Vint (Int.repr lind));
   temp _l_max (Vint (Int.repr lj));
   temp _l_a l_a; temp _r_a r_a)
   SEP (data_at sh1 (tarray tuint 11) (map Vint (map Int.repr contents_la)) l_a;
   data_at sh2 (tarray tuint 11) (map Vint (map Int.repr contents_ra)) r_a) 
   ).
  forward. forward. 
  rewrite !Int.unsigned_repr in H16. Exists (Znth r_i contents_ra).
  Exists r_i. entailer!. 
 (*right*)
 unfold Z_lt_ge_dec. 
 destruct (Z_lt_dec (sum_max 0 (sublist 0 r_i contents_ra))(Znth r_i contents_ra)) eqn:HDe.
 split; reflexivity. contradiction. 
 apply summax_one. lia. assumption.
 eapply summax_range. eapply Forall_sublist in H0. eassumption.
 forward.
 (*other way*)
 rewrite !Int.unsigned_repr in H16. Exists (sum_max 0 (sublist 0 r_i contents_ra)). 
 Exists ri. entailer!.
 unfold Z_lt_ge_dec. 
 destruct (Z_lt_dec (sum_max 0 (sublist 0 r_i contents_ra))(Znth r_i contents_ra)) eqn:HDe. 
 contradiction. split; reflexivity.  apply summax_one. lia.
 assumption. eapply summax_range. eapply Forall_sublist in H0. eassumption.
 (*forward_if - rind - max index*)
 Intros rj rind. 
 forward_if (
  PROP()
  LOCAL (temp _t'6 (Vint (Int.repr (Znth r_i contents_ra)));
   temp _t'7 (Vint (Int.repr (Znth l_i contents_la)));
   temp _r_i (Vint (Int.repr r_i));
   temp _rind (Vint (Int.repr rind));
   temp _r_max (Vint (Int.repr rj));
   temp _l_i (Vint (Int.repr l_i));
   temp _lind (Vint (Int.repr lind));
   temp _l_max (Vint (Int.repr lj));
   temp _l_a l_a; temp _r_a r_a)
   SEP (data_at sh1 (tarray tuint 11) (map Vint (map Int.repr contents_la)) l_a;
   if Z_lt_le_dec r_i 10 then (data_at sh2 (tarray tuint 11) (map Vint (map Int.repr contents_ra)) r_a)
   else if Z.eq_dec rind 10 then (data_at sh2 (tarray tuint 11) (map Vint (map Int.repr contents_ra)) r_a)
   else if Z.eq_dec rind 0 then (data_at sh2 (tarray tuint 11) (map Vint (map Int.repr ([Znth 10 contents_ra] ++ sublist 1 10 contents_ra ++
   [Znth 0 contents_ra]))) r_a)
   else (data_at sh2 (tarray tuint 11) (map Vint (map Int.repr (sublist 0 rind contents_ra ++ [Znth 10 contents_ra] ++ sublist (rind + 1) 10 contents_ra ++
   [Znth rind contents_ra])))) r_a
   )).
  fastforward. entailer!. simpl. eapply entailment_swap; assumption.
  forward. entailer!.  apply not_Zeq_inf in H19. destruct H19 as [? | ?].
  destruct (Z_lt_le_dec r_i 10) eqn:Hltledec. entailer!.  apply Z.lt_gt in l.
  contradiction. (*contradiction - successor case*)  replace 11 with (Z.succ 10) in H11 by lia.  
  apply Zlt_succ_le in H11. apply Z.lt_gt in l. contradiction. forward. forward.
  (*plus 1*)
  Exists (l_i + 1). Exists (r_i + 1). Exists lind. Exists rind. entailer!.
 (*same proof all over - destruct both?*)
 destruct (Z_lt_ge_dec (sum_max 0 (sublist 0 r_i contents_la))(Znth r_i contents_la)) eqn:HDe1.
 destruct (Z_lt_ge_dec (sum_max 0 (sublist 0 r_i contents_ra))(Znth r_i contents_ra)) eqn:HDe2.
 rewrite H14,H17.  
 assert (Z.max (Znth r_i contents_la) 0 = Znth r_i contents_la). {
  apply summax_one with r_i contents_la in H. 
  destruct H. apply Z.max_r in H. rewrite Z.max_comm in H.
  rewrite H. reflexivity. lia.
 }
 assert (Z.max (Znth r_i contents_ra) 0 = Znth r_i contents_ra). {
  apply summax_one with r_i contents_ra in H0. 
  destruct H0. apply Z.max_r in H0. rewrite Z.max_comm in H0.
  rewrite H0. reflexivity. lia.
 }
 rewrite !(sublist_split 0 r_i (r_i + 1)) by lia. rewrite !sublist_len_1 by lia.
 rewrite !summax_app. clear HDe1. clear HDe2. apply Z.lt_le_incl in l,l0.
 apply Z.max_r in l,l0. rewrite l,l0. rewrite H15. split; try reflexivity.
 rewrite H18. split; try reflexivity. split; reflexivity.
 apply summax_one. lia. assumption. apply summax_one. lia. assumption.
 rewrite !(sublist_split 0 r_i (r_i + 1)) by lia. rewrite !sublist_len_1 by lia.
 rewrite !summax_app. clear HDe1. apply Z.lt_le_incl in l.  apply Z.max_r in l.
 rewrite l. rewrite H15. 
 (*other side*)
 clear HDe2. apply Z.ge_le in g. apply Z.max_r in g.
 rewrite Z.max_comm in g. rewrite g. rewrite H18. split. reflexivity.
 split. assumption. rewrite H17, H14; split; reflexivity.
 apply summax_one. lia. assumption. apply summax_one. lia. assumption.
 destruct (Z_lt_ge_dec (sum_max 0 (sublist 0 r_i contents_ra))(Znth r_i contents_ra)) eqn:HDe2.
 (*opposite treatment*)
 rewrite !(sublist_split 0 r_i (r_i + 1)) by lia. rewrite !sublist_len_1 by lia.
 rewrite !summax_app. clear HDe2. apply Z.lt_le_incl in l.  apply Z.max_r in l.
 rewrite l. rewrite H18.  
 (*other side*)
 clear HDe1. apply Z.ge_le in g. apply Z.max_r in g.
 rewrite Z.max_comm in g. rewrite g. rewrite H15, H9. split. reflexivity.
 split. reflexivity. rewrite H17, H14; split; reflexivity.
 apply summax_one. lia. assumption. apply summax_one. lia. assumption.
 (*both >=*)
 rewrite !(sublist_split 0 r_i (r_i + 1)) by lia. rewrite !sublist_len_1 by lia.
 rewrite !summax_app. clear HDe1. clear HDe2. apply Z.ge_le in g0,g. apply Z.max_r in g0,g.
 rewrite Z.max_comm in g0,g. rewrite g0,g. rewrite H15. rewrite <- H9.
 rewrite H18, <- H10, H17, <- H10, H14, <- H9.
 split. reflexivity. split. reflexivity. split. reflexivity. reflexivity.
 apply summax_one. lia. assumption. apply summax_one. lia. assumption. entailer!.
 destruct (Z_lt_le_dec r_i 10) eqn:Hfin1. destruct (Z_lt_le_dec (r_i + 1) 11) eqn:Hfin2. 
 entailer!. clear Hfin2. replace (r_i + 1) with (Z.succ r_i) in l0 by lia.
 apply Z.le_pred_lt_succ in l0. apply Z.le_ge in l0. replace (Z.pred 11) with 10 in l0 by lia.
 contradiction.
 destruct (Z_lt_le_dec (r_i + 1) 11) eqn:Hfin2. clear Hfin2. replace (r_i + 1) with (Z.succ r_i) in l0 by lia.
 apply Z.lt_succ_lt_pred in l0. replace (Z.pred 11) with 10 in l0 by lia. 
 apply Z.lt_gt in l0. contradiction. entailer!.
 (*next loop*)
 Intros l_i r_i li ri.
 forward_loop 
  (EX l_i:Z, EX r_i:Z, EX li:Z, EX ri:Z, 
    PROP (0 <= l_i <= 11; 0 <= r_i <= 11; l_i = 11; r_i = 11;
    l_i = r_i; 0 <= li < l_i; 0 <= ri < r_i;
    Znth li contents_la = (sum_max 0 (sublist 0 l_i contents_la));
    Znth ri contents_ra = (sum_max 0 (sublist 0 r_i contents_ra)))
   LOCAL (
    temp _r_i (Vint (Int.repr r_i)); 
    temp _rind (Vint (Int.repr ri)); 
    temp _r_max (Vint (Int.repr (sum_max 0 (sublist 0 r_i contents_ra))));  
    temp _l_i (Vint (Int.repr l_i)); 
    temp _lind (Vint (Int.repr li)); 
    temp _l_max (Vint (Int.repr (sum_max 0 (sublist 0 l_i contents_la)))); 
    temp _l_a l_a; temp _r_a r_a)
   SEP (data_at sh1 (tarray tuint 11) 
   (map Vint (map Int.repr contents_la)) l_a;
   if Z_lt_le_dec r_i 11 then (data_at sh2 (tarray tuint 11) (map Vint (map Int.repr contents_ra)) r_a)
   else if Z.eq_dec ri 10 then (data_at sh2 (tarray tuint 11) (map Vint (map Int.repr contents_ra)) r_a)
   else if Z.eq_dec ri 0 then (data_at sh2 (tarray tuint 11) (map Vint (map Int.repr ([Znth 10 contents_ra] ++ sublist 1 10 contents_ra ++
   [Znth 0 contents_ra]))) r_a)
   else (data_at sh2 (tarray tuint 11) (map Vint (map Int.repr (sublist 0 ri contents_ra ++ [Znth 10 contents_ra] ++ sublist (ri + 1) 10 contents_ra ++
   [Znth ri contents_ra])))) r_a)
   )%assert
   break: 
   (EX l_i:Z, EX r_i:Z, EX li:Z, EX ri:Z,
   PROP (0 <= l_i <= 11; 0 <= r_i <= 11; l_i = 11; r_i = 11;
   l_i = r_i; 0 <= li < l_i; 0 <= ri < r_i;
   Znth li contents_la = (sum_max 0 (sublist 0 l_i contents_la));
   Znth ri contents_ra = (sum_max 0 (sublist 0 r_i contents_ra)))
   LOCAL (
    temp _r_i (Vint (Int.repr r_i)); 
    temp _rind (Vint (Int.repr ri)); 
    temp _r_max (Vint (Int.repr (sum_max 0 (sublist 0 r_i contents_ra))));  
    temp _l_i (Vint (Int.repr l_i)); 
    temp _lind (Vint (Int.repr li)); 
    temp _l_max (Vint (Int.repr (sum_max 0 (sublist 0 l_i contents_la)))); 
    temp _l_a l_a; temp _r_a r_a)
   SEP (data_at sh1 (tarray tuint 11) 
   (map Vint (map Int.repr contents_la)) l_a;
   if Z_lt_le_dec r_i 11 then (data_at sh2 (tarray tuint 11) (map Vint (map Int.repr contents_ra)) r_a)
   else if Z.eq_dec ri 10 then (data_at sh2 (tarray tuint 11) (map Vint (map Int.repr contents_ra)) r_a)
   else if Z.eq_dec ri 0 then (data_at sh2 (tarray tuint 11) (map Vint (map Int.repr ([Znth 10 contents_ra] ++ sublist 1 10 contents_ra ++
   [Znth 0 contents_ra]))) r_a)
   else (data_at sh2 (tarray tuint 11) (map Vint (map Int.repr (sublist 0 ri contents_ra ++ [Znth 10 contents_ra] ++ sublist (ri + 1) 10 contents_ra ++
   [Znth ri contents_ra])))) r_a
   ))%assert.
   Exists l_i. Exists r_i. Exists li. Exists ri. entailer!. Intros l_i0 r_i0 li0 ri0.
   rewrite H15,H16. forward_if. forward. 
   (*other side*)
   Exists l_i0. Exists r_i0. Exists li0. Exists ri0. entailer!. discriminate H22.
   (*r loop*)   
   Intros l_i0 r_i0 li0 ri0.
   forward_loop 
   (EX l_i0:Z, EX r_i0:Z, EX li0:Z, EX ri0:Z, 
    PROP (0 <= l_i0 <= 11; 0 <= r_i0 <= 11; l_i0 = 11; r_i0 = 11;
    l_i0 = r_i0; 0 <= li0 < l_i0; 0 <= ri0 < r_i0;
    Znth li0 contents_la = (sum_max 0 (sublist 0 l_i0 contents_la));
    Znth ri0 contents_ra = (sum_max 0 (sublist 0 r_i0 contents_ra)))
   LOCAL (
    temp _r_i (Vint (Int.repr r_i0)); 
    temp _rind (Vint (Int.repr ri0)); 
    temp _r_max (Vint (Int.repr (sum_max 0 (sublist 0 r_i0 contents_ra))));  
    temp _l_i (Vint (Int.repr l_i0)); 
    temp _lind (Vint (Int.repr li0)); 
    temp _l_max (Vint (Int.repr (sum_max 0 (sublist 0 l_i0 contents_la)))); 
    temp _l_a l_a; temp _r_a r_a)
   SEP (data_at sh1 (tarray tuint 11) 
   (map Vint (map Int.repr contents_la)) l_a;
   if Z_lt_le_dec r_i0 11 then (data_at sh2 (tarray tuint 11) (map Vint (map Int.repr contents_ra)) r_a)
   else if Z.eq_dec ri0 10 then (data_at sh2 (tarray tuint 11) (map Vint (map Int.repr contents_ra)) r_a)
   else if Z.eq_dec ri0 0 then (data_at sh2 (tarray tuint 11) (map Vint (map Int.repr ([Znth 10 contents_ra] ++ sublist 1 10 contents_ra ++
   [Znth 0 contents_ra]))) r_a)
   else (data_at sh2 (tarray tuint 11) (map Vint (map Int.repr (sublist 0 ri0 contents_ra ++ [Znth 10 contents_ra] ++ sublist (ri0 + 1) 10 contents_ra ++
   [Znth ri0 contents_ra])))) r_a)
   )%assert
   break: 
   (EX l_i0:Z, EX r_i0:Z, EX li0:Z, EX ri0:Z,
   PROP (0 <= l_i0 <= 11; 0 <= r_i0 <= 11; l_i0 = 11; r_i0 = 11;
   l_i0 = r_i0; 0 <= li0 < l_i0; 0 <= ri0 < r_i0;
   Znth li0 contents_la = (sum_max 0 (sublist 0 l_i0 contents_la));
   Znth ri0 contents_ra = (sum_max 0 (sublist 0 r_i0 contents_ra)))
   LOCAL (
    temp _r_i (Vint (Int.repr r_i0)); 
    temp _rind (Vint (Int.repr ri0)); 
    temp _r_max (Vint (Int.repr (sum_max 0 (sublist 0 r_i0 contents_ra))));  
    temp _l_i (Vint (Int.repr l_i0)); 
    temp _lind (Vint (Int.repr li0)); 
    temp _l_max (Vint (Int.repr (sum_max 0 (sublist 0 l_i0 contents_la)))); 
    temp _l_a l_a; temp _r_a r_a)
   SEP (data_at sh1 (tarray tuint 11) 
   (map Vint (map Int.repr contents_la)) l_a;
   if Z_lt_le_dec r_i0 11 then (data_at sh2 (tarray tuint 11) (map Vint (map Int.repr contents_ra)) r_a)
   else if Z.eq_dec ri0 10 then (data_at sh2 (tarray tuint 11) (map Vint (map Int.repr contents_ra)) r_a)
   else if Z.eq_dec ri0 0 then (data_at sh2 (tarray tuint 11) (map Vint (map Int.repr ([Znth 10 contents_ra] ++ sublist 1 10 contents_ra ++
   [Znth 0 contents_ra]))) r_a)
   else (data_at sh2 (tarray tuint 11) (map Vint (map Int.repr (sublist 0 ri0 contents_ra ++ [Znth 10 contents_ra] ++ sublist (ri0 + 1) 10 contents_ra ++
   [Znth ri0 contents_ra])))) r_a
   ))%assert.
   Exists l_i0. Exists r_i0. Exists li0. Exists ri0. entailer!. Intros l_i1 r_i1 li1 ri1.
   rewrite H24,H25. forward_if. forward. 
   (*other side*)
   Exists l_i1. Exists r_i1. Exists li1. Exists ri1. entailer!. discriminate H31.
   fastforward. Exists li1. Exists ri1.
   entailer!. rewrite H29,H30. apply eqmaxlist. rewrite !Zlength_sublist by lia.
   reflexivity. Search Forall sublist. eapply Forall_sublist in H.
   eassumption. eapply Forall_sublist in H0. eassumption. Search Forall2 sublist.
   eapply Forall2_sublist in H1. eassumption. lia.   
   apply sepcon_derives. eapply entailment_swap. destruct H27. split. assumption.
   replace 11 with (Z.succ 10) in H7 by lia.  apply Zlt_succ_le in H7.
   assumption. assumption. simpl. entailer!.
Qed.
 



