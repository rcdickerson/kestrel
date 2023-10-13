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
            
(*Lemma basic_mathp1eq: forall x: Z,
 x >= 0 -> x < (x + 1).
Proof. intros. lia. Qed.

Lemma basic_mathp2eq: forall x y: Z,
 x >= 0 -> y >= 0 -> y < (y + x + 1).
Proof. intros. lia. Qed.

Lemma basic_mathp3eq: forall x y z: Z,
 x >= 0 -> y >= 0 -> z >= 0 -> z < (z + y + x + 1).
Proof. intros. lia. Qed.*)
 
(*Functional Model: empty for kestrel*)
(*API spec => verifyfunc spec; left and right are equal *)
Definition verifyfunc_spec : ident * funspec :=
DECLARE _verifyfunc
  WITH l_a : val, r_a : val, sh1 : share, sh2 : share,
  contents_lai : list Z, contents_rai : list Z
  PRE [tptr tuint, tptr tuint]  
    (*ensure variables left and right are equal*)
    PROP (
    writable_share sh1; writable_share sh2;
    Zlength contents_lai = 11; Zlength contents_rai = 11;
    Forall (fun x => 0 <= x <= Int.max_unsigned) contents_lai;
    Forall (fun x => 0 <= x <= Int.max_unsigned) contents_rai;
    Forall2 eq contents_lai contents_rai)
  PARAMS (l_a;r_a)
    SEP (data_at sh1 (tarray tuint 11) (map Vint (map Int.repr contents_lai)) l_a;
    data_at sh2 (tarray tuint 11) (map Vint (map Int.repr contents_rai)) r_a)
  POST [ tvoid ]
    EX contents_lao:list Z, EX contents_rao :list Z, 
    PROP (Forall2 eq contents_lao contents_rao)
    RETURN () (*void*)
    SEP (data_at sh1 (tarray tuint 11) (map Vint (map Int.repr contents_lao)) l_a;
    data_at sh2 (tarray tuint 11) (map Vint (map Int.repr contents_rao)) r_a).


(*Pack APIs together*)
Definition Gprog := [verifyfunc_spec].

(*verify fun_spec - from here*)
Lemma body_verifyfunc: semax_body Vprog Gprog f_verifyfunc verifyfunc_spec.
Proof. 
 start_function. 
 fastforward. 
 forward_loop 
 ( 
    EX l_i:Z, EX r_i:Z, EX lmax:Z, EX rmax:Z, EX li:Z, EX ri:Z, 
    EX contents_lao:list Z, EX contents_rao: list Z, 
    PROP 
    (
      Forall (fun x => 0 <= x <= Int.max_unsigned) contents_lao;
      Forall (fun x => 0 <= x <= Int.max_unsigned) contents_rao;
      (*In lmax contents_lao; In rmax contents_rao;*)
      (r_i <= 10) -> Forall2 eq contents_lao contents_rao;
      (r_i = 11) -> Forall2 eq (sublist 0 ri contents_lao) (sublist 0 ri contents_rao);
      (r_i = 11) -> Forall2 eq (sublist (ri + 1) 10 contents_lao) (sublist (ri + 1) 10 contents_rao); 
      0 <= l_i <= 11; 0 <= r_i <= 11; l_i = r_i; 
      0 <= li < l_i; 0 <= ri < r_i; lmax = rmax; li = ri;
      lmax = Znth li contents_lao; (r_i <= 10) -> rmax = Znth ri contents_rao;
      (r_i = 11) -> rmax = Znth 10 contents_rao;
      (r_i = 11) -> (Znth ri contents_lao = Znth 10 contents_rao);
      (r_i = 11) -> (Znth 10 contents_lao = Znth ri contents_rao)
    )
    LOCAL 
    (
      temp _r_i (Vint (Int.repr r_i)); 
      temp _rind (Vint (Int.repr ri)); 
      temp _r_max (Vint (Int.repr rmax));  
      temp _l_i (Vint (Int.repr l_i)); 
      temp _lind (Vint (Int.repr li)); 
      temp _l_max (Vint (Int.repr lmax)); 
      temp _l_a l_a; temp _r_a r_a
    )
    SEP 
    (
      data_at sh1 (tarray tuint 11) (map Vint (map Int.repr contents_lao)) l_a;
      data_at sh2 (tarray tuint 11) (map Vint (map Int.repr contents_rao)) r_a
    )
)%assert
break:
( 
   EX l_i:Z, EX r_i:Z, EX lmax:Z, EX rmax:Z, EX li:Z, EX ri:Z, 
   EX contents_lao:list Z, EX contents_rao: list Z, 
   PROP 
   (
     Forall (fun x => 0 <= x <= Int.max_unsigned) contents_lao;
     Forall (fun x => 0 <= x <= Int.max_unsigned) contents_rao;
     l_i = 11; r_i = 11; 
     Forall2 eq (sublist 0 ri contents_lao) (sublist 0 ri contents_rao);
     Forall2 eq (sublist (ri + 1) 10 contents_lao) (sublist (ri + 1) 10 contents_rao); 
     0 <= li < l_i; 0 <= ri < r_i; lmax = rmax; li = ri;
     Znth ri contents_lao = Znth 10 contents_rao; Znth 10 contents_lao = Znth ri contents_rao; 
     lmax = Znth li contents_lao; rmax = Znth 10 contents_rao
   )
   LOCAL 
   (
     temp _r_i (Vint (Int.repr r_i)); 
     temp _rind (Vint (Int.repr ri)); 
     temp _r_max (Vint (Int.repr rmax));  
     temp _l_i (Vint (Int.repr l_i)); 
     temp _lind (Vint (Int.repr li)); 
     temp _l_max (Vint (Int.repr lmax)); 
     temp _l_a l_a; temp _r_a r_a
   )
   SEP 
   (
     data_at sh1 (tarray tuint 11) (map Vint (map Int.repr contents_lao)) l_a;
     data_at sh2 (tarray tuint 11) (map Vint (map Int.repr contents_rao)) r_a
   )
 )%assert.
 (*first existential - outermost if*)      
 Exists 1. Exists 1. Exists (Znth 0 contents_lai). Exists (Znth 0 contents_rai). 
 Exists 0. Exists 0. Exists contents_lai. Exists contents_rai. entailer!.
 apply Forall2_Znth. assumption. lia. 
 Intros l_i r_i lmax rmax li ri contents_lao contents_rao. 
 assert_PROP (Zlength contents_lao = 11). {
  entailer!. rewrite <- H22. do 2 rewrite Zlength_map. reflexivity.
 }
 assert_PROP (Zlength contents_rao = 11). {
  entailer!. rewrite <- H26. do 2 rewrite Zlength_map. reflexivity.
 }
 forward_if. forward. 
 Exists l_i. Exists r_i. Exists lmax. Exists rmax. 
 Exists li. Exists ri. Exists contents_lao. Exists contents_rao. entailer!.
 assert (r_i = 11) by lia. split. apply H7 in H11. assumption. 
 apply H8 in H11. assumption. 
 forward_if. forward.
 Exists l_i. Exists r_i. Exists lmax. Exists rmax. 
 Exists li. Exists ri. Exists contents_lao. Exists contents_rao. entailer!.
 forward. 
 forward_if 
 (
    EX lmaxn:Z,EX lin:Z,
    PROP
    (
      lmaxn = Z.max lmax (Znth l_i contents_lao); 
      0 <= lin <= l_i; if Z_lt_ge_dec lmax (Znth l_i contents_lao) then lin = l_i 
      else lin = li
    )
    LOCAL 
    (
      temp _t'4 (Vint (Int.repr (Znth l_i contents_lao)));
      temp _r_i (Vint (Int.repr r_i));
      temp _rind (Vint (Int.repr ri));
      temp _r_max (Vint (Int.repr rmax));
      temp _l_i (Vint (Int.repr l_i));
      temp _lind (Vint (Int.repr lin));
      temp _l_max (Vint (Int.repr lmaxn));
      temp _l_a l_a; temp _r_a r_a
    )
    SEP 
    (
      data_at sh1 (tarray tuint 11) (map Vint (map Int.repr contents_lao)) l_a;
      data_at sh2 (tarray tuint 11) (map Vint (map Int.repr contents_rao)) r_a
    ) 
 ). 
 forward. forward. Exists (Znth l_i contents_lao). Exists l_i. rewrite !Int.unsigned_repr in H25.
 destruct (Z_lt_ge_dec lmax (Znth l_i contents_lao)) eqn:Hltgedec. 
 entailer!. contradiction.  
 apply summax_one. lia. assumption. rewrite H16. apply summax_one. lia. assumption. forward. 
 (*second case*)
 Exists lmax. Exists li. rewrite !Int.unsigned_repr in H25.
 destruct (Z_lt_ge_dec lmax (Znth l_i contents_lao)) eqn:Hltgedec. contradiction. entailer!. 
 apply summax_one. lia. assumption. rewrite H16.
 apply summax_one. lia. assumption.
 (*next if*)
 Intros lmaxn lin. forward. 
 (*right if*)
 forward_if 
 (
    EX rmaxn:Z,EX rin:Z,
    PROP
    (
      rmaxn = Z.max rmax (Znth r_i contents_rao); 
      0 <= rin <= r_i; if Z_lt_ge_dec rmax (Znth r_i contents_rao) then rin = r_i 
      else rin = ri
    )
    LOCAL 
    (
      temp _t'3 (Vint (Int.repr (Znth r_i contents_rao)));
      temp _t'4 (Vint (Int.repr (Znth l_i contents_lao)));
      temp _r_i (Vint (Int.repr r_i));
      temp _rind (Vint (Int.repr rin));
      temp _r_max (Vint (Int.repr rmaxn));
      temp _l_i (Vint (Int.repr l_i));
      temp _lind (Vint (Int.repr lin));
      temp _l_max (Vint (Int.repr lmaxn));
      temp _l_a l_a; temp _r_a r_a
    )
    SEP 
    (
      data_at sh1 (tarray tuint 11) (map Vint (map Int.repr contents_lao)) l_a;
      data_at sh2 (tarray tuint 11) (map Vint (map Int.repr contents_rao)) r_a
    ) 
 ).
 forward. forward. Exists (Znth r_i contents_rao). Exists r_i. 
 rewrite !Int.unsigned_repr in H28. 
 destruct (Z_lt_ge_dec rmax (Znth r_i contents_rao)) eqn:Hltgedec. entailer!. 
 (*apply Z.max_r in H22. rewrite !H22. entailer!. *)
 contradiction. apply summax_one. lia. assumption. rewrite H14 in H16. rewrite H16. 
 apply summax_one. lia. assumption. forward.
 (*second case*)
 Exists rmax. Exists ri. rewrite !Int.unsigned_repr in H28. 
 destruct (Z_lt_ge_dec rmax (Znth r_i contents_rao)) eqn:Hltgedec.
 entailer!. entailer!. 
 apply summax_one. lia. assumption. rewrite <- H14, H16. apply summax_one. lia. assumption.
 Intros rmaxn rin.
 (*last if*)
 forward_if 
 (
    PROP
    ()
    LOCAL 
    (
      temp _t'3 (Vint (Int.repr (Znth r_i contents_rao)));
      temp _t'4 (Vint (Int.repr (Znth l_i contents_lao)));
      temp _r_i (Vint (Int.repr r_i));
      temp _rind (Vint (Int.repr rin));
      temp _r_max (Vint (Int.repr rmaxn));
      temp _l_i (Vint (Int.repr l_i));
      temp _lind (Vint (Int.repr lin));
      temp _l_max (Vint (Int.repr lmaxn));
      temp _l_a l_a; temp _r_a r_a
    )
    SEP 
    (
      data_at sh1 (tarray tuint 11) (map Vint (map Int.repr contents_lao)) l_a;
      if Z_lt_le_dec r_i 10 then data_at sh2 (tarray tuint 11) (map Vint (map Int.repr contents_rao)) r_a
      else if Z.eq_dec rin 10  then
      data_at sh2 (tarray tuint 11) (map Vint (map Int.repr contents_rao)) r_a
      else data_at sh2 (tarray tuint 11) (map Vint (map Int.repr ((sublist 0 rin contents_rao) ++ [Znth 10 contents_rao] ++ (sublist (rin + 1) 10 contents_rao) ++ [rmaxn]))) r_a

    ) 
 ).
 fastforward. destruct (Z_lt_le_dec r_i 10) eqn:Hlelt. clear Hlelt.
 rewrite H31 in l. discriminate l. destruct (Z.eq_dec rin 10) eqn:Hrin. subst.
 entailer!.
 (*prove a*)
 rewrite !upd_Znth_map. rewrite upd_Znth_twice by lia. rewrite upd_Znth_unfold.
 rewrite H22. simpl. rewrite sublist_nil. rewrite <- sublist_last_1 by lia. simpl. 
 rewrite sublist_same by lia. entailer!. lia.
(*second case*) assert (rin < 10) by lia. entailer!.
 apply derives_refl'. rewrite !upd_Znth_map. f_equal. f_equal. f_equal.
 set (x := Z.max (Znth ri contents_lao) (Znth 10 contents_rao)). 
 pattern (upd_Znth 10 contents_rao x) at 1. rewrite upd_Znth_unfold at 1.
 rewrite H22. simpl. rewrite sublist_nil. simpl. rewrite upd_Znth_app1 by list_solve.
 rewrite upd_Znth_unfold. rewrite !Zlength_sublist by lia. simpl. rewrite <- sublist_parts1 by lia.
 rewrite sublist_prefix. replace (Z.min rin 10) with rin by lia. list_solve. list_solve. lia. forward.
 destruct (Z_lt_le_dec r_i 10) eqn:Hlelt. entailer!. assert (r_i = 10) by lia.
 rewrite H32 in H31. contradiction. 
 fastforward. Exists (l_i + 1). Exists (r_i + 1). Exists lmaxn. Exists rmaxn. 
 Exists lin. Exists rin. Exists contents_lao.
 (*destruct on r_i value*) 
 destruct (Z_lt_le_dec r_i 10) eqn:Hlelt. (* < 10*) Exists contents_rao. entailer!.
 split. intros. apply H6. lia. clear Hlelt. apply Z.lt_le_incl in l.
 apply H6 in l. move l at bottom. eapply Forall2_Znth with (i := r_i) in l.
 rewrite l. split. reflexivity. rewrite l in H27. destruct (Z_lt_ge_dec (Znth ri contents_lao)
 (Znth r_i contents_rao)) eqn:Heq. rewrite <- H30 in H27. split. assumption. split.
 rewrite Z.max_r. rewrite <- H27 in H30. rewrite H30. symmetry. assumption.
 lia. intros. rewrite Z.max_r by lia. rewrite H30. reflexivity.
 split. rewrite H27,H30. reflexivity. split. rewrite Z.max_l by lia. rewrite H27. reflexivity.
 intros. rewrite Z.max_l by lia. rewrite H30. assert (r_i <= 10) by lia.
 apply H6 in H14. eapply Forall2_forall_Znth with (i := ri) in H14. assumption. lia. lia. 
 destruct (Z.eq_dec rin 10) eqn:Hrin. Exists contents_rao.
 entailer!. (*break case*) split. intros. apply Forall2_sublist. apply H6. lia. lia.
 split. intros. simpl. rewrite !sublist_nil_gen by lia. apply Forall2_nil.
 split. assert (r_i <= 10) by lia. apply H6 in H11. eapply Forall2_Znth with (i := r_i) in H11. rewrite H11. reflexivity.
 lia. assert (r_i <= 10) by lia. apply H6 in H11. eapply Forall2_forall_Znth with (i := r_i) in H11.
 rewrite H11 in H27.
 destruct (Z_lt_ge_dec (Znth ri contents_lao)(Znth r_i contents_rao)) eqn:Hltledec. assert (r_i = 10) by lia.
 split. rewrite H14 in H27. assumption. split. clear Hltledec. rewrite <- H11 in l0. rewrite Z.max_r by lia.
 rewrite H27. reflexivity. split. intros. rewrite Z.max_r by lia. rewrite H14. reflexivity.
 assert (r_i <= 10) by lia. apply H6 in H15. eapply Forall2_forall_Znth with (i := 10) in H15.
 split. intros. assumption. intros. assumption. lia. split. rewrite <- H30 in H27. assumption.
 split. rewrite Z.max_l by lia. rewrite H27. reflexivity. rewrite Z.max_l by lia.
 rewrite <- H30. assert (r_i <= 10) by lia. apply H6 in H14. eapply Forall2_forall_Znth with (i := 10) in H14.
 split. intros. assumption. split. intros. assumption. intros. assumption. lia. lia. 
 Exists (sublist 0 rin contents_rao ++ [Znth 10 contents_rao] ++
 sublist (rin + 1) 10 contents_rao ++ [rmaxn]). entailer!.
 (*final set of clauses - for range*)
 split. try list_solve. split. intros. replace (sublist 0 rin (sublist 0 rin contents_rao ++
  [Znth 10 contents_rao] ++ sublist (rin + 1) 10 contents_rao ++
  [Z.max (Znth ri contents_lao) (Znth r_i contents_rao)])) with (sublist 0 rin contents_rao) by list_solve.
  assert (r_i <= 10) by lia. apply Forall2_sublist. apply H6. lia. lia.
  split. intros. replace (sublist (rin + 1) 10 (sublist 0 rin contents_rao ++
   [Znth 10 contents_rao] ++ sublist (rin + 1) 10 contents_rao ++
   [Z.max (Znth ri contents_lao) (Znth r_i contents_rao)])) with (sublist (rin + 1) 10 contents_rao) by list_solve.
   assert (r_i <= 10) by lia. apply Forall2_sublist. apply H6. lia. lia.
  split. assert (r_i <= 10) by lia. apply H6 in H11. eapply Forall2_Znth with (i := r_i) in H11.
  rewrite H11. reflexivity. lia. assert (r_i <= 10) by lia. apply H6 in H11. eapply Forall2_forall_Znth with (i := r_i) in H11.
  rewrite H11 in H27. destruct (Z_lt_ge_dec (Znth ri contents_lao)(Znth r_i contents_rao)) eqn:Hs. split. rewrite <- H30 in H27.
  assumption. split. rewrite Z.max_r by lia. rewrite H27. reflexivity.
  split. intros. replace (Znth 10 (sublist 0 rin contents_rao ++
   [Znth 10 contents_rao] ++ sublist (rin + 1) 10 contents_rao ++
   [Z.max (Znth ri contents_lao) (Znth r_i contents_rao)])) with (Z.max (Znth ri contents_lao) (Znth r_i contents_rao)) by list_solve. reflexivity.
  split. intros. replace (Znth 10 (sublist 0 rin contents_rao ++
   [Znth 10 contents_rao] ++ sublist (rin + 1) 10 contents_rao ++
   [Z.max (Znth ri contents_lao) (Znth r_i contents_rao)])) with (Z.max (Znth ri contents_lao)
   (Znth r_i contents_rao)) by list_solve. rewrite Z.max_r by lia. rewrite H30. assumption.
   intros. replace (Znth rin (sublist 0 rin contents_rao ++ [Znth 10 contents_rao] ++
    sublist (rin + 1) 10 contents_rao ++ [Z.max (Znth ri contents_lao)(Znth r_i contents_rao)])) with (Znth 10 contents_rao) by list_solve.
  assert (r_i <= 10) by lia. apply H6 in H15. eapply Forall2_Znth with (i := 10) in H15. assumption. lia.
  split. rewrite H27,H30. reflexivity. split. rewrite Z.max_l by lia. rewrite H27. reflexivity.
  split. intros. replace (Znth 10 (sublist 0 rin contents_rao ++
   [Znth 10 contents_rao] ++ sublist (rin + 1) 10 contents_rao ++
   [Z.max (Znth ri contents_lao) (Znth r_i contents_rao)])) with (Z.max (Znth ri contents_lao) (Znth r_i contents_rao)) by list_solve.
   reflexivity. split. intros. replace (Znth 10 (sublist 0 rin contents_rao ++
    [Znth 10 contents_rao] ++ sublist (rin + 1) 10 contents_rao ++ [Z.max (Znth ri contents_lao)(Znth r_i contents_rao)])) with (Z.max (Znth ri contents_lao)
    (Znth r_i contents_rao)) by list_solve. rewrite Z.max_l by lia. rewrite H30. reflexivity.
    intros.  replace (Znth rin (sublist 0 rin contents_rao ++ [Znth 10 contents_rao] ++
     sublist (rin + 1) 10 contents_rao ++ [Z.max (Znth ri contents_lao)(Znth r_i contents_rao)])) with (Znth 10 contents_rao) by list_solve. 
     assert (r_i <= 10) by lia. apply H6 in H15. eapply Forall2_Znth with (i := 10) in H15. assumption. lia. lia.
  (*individual loops*)
  Intros l_i r_i lmax rmax li ri contents_lao contents_rao.
  forward_loop 
  ( 
     EX l_i:Z, EX r_i:Z, EX lmax:Z, EX rmax:Z, EX li:Z, EX ri:Z, 
     EX contents_lao:list Z, EX contents_rao: list Z, 
     PROP 
     (
       Forall (fun x => 0 <= x <= Int.max_unsigned) contents_lao;
       Forall (fun x => 0 <= x <= Int.max_unsigned) contents_rao;
       (*In lmax contents_lao; In rmax contents_rao;*)
       (r_i <= 10) -> Forall2 eq contents_lao contents_rao;
       (r_i = 11) -> Forall2 eq (sublist 0 ri contents_lao) (sublist 0 ri contents_rao);
       (r_i = 11) -> Forall2 eq (sublist (ri + 1) 10 contents_lao) (sublist (ri + 1) 10 contents_rao); 
       0 <= l_i <= 11; 0 <= r_i <= 11; l_i = 11; r_i = 11; l_i = r_i; 
       0 <= li < l_i; 0 <= ri < r_i; lmax = rmax; li = ri;
       lmax = Znth li contents_lao; (r_i <= 10) -> rmax = Znth ri contents_rao;
       (r_i = 11) -> rmax = Znth 10 contents_rao;
       (r_i = 11) -> (Znth ri contents_lao = Znth 10 contents_rao);
       (r_i = 11) -> (Znth 10 contents_lao = Znth ri contents_rao)
     )
     LOCAL 
     (
       temp _r_i (Vint (Int.repr r_i)); 
       temp _rind (Vint (Int.repr ri)); 
       temp _r_max (Vint (Int.repr rmax));  
       temp _l_i (Vint (Int.repr l_i)); 
       temp _lind (Vint (Int.repr li)); 
       temp _l_max (Vint (Int.repr lmax)); 
       temp _l_a l_a; temp _r_a r_a
     )
     SEP 
     (
       data_at sh1 (tarray tuint 11) (map Vint (map Int.repr contents_lao)) l_a;
       data_at sh2 (tarray tuint 11) (map Vint (map Int.repr contents_rao)) r_a
     )
 )%assert
 break:
 ( 
    EX l_i:Z, EX r_i:Z, EX lmax:Z, EX rmax:Z, EX li:Z, EX ri:Z, 
    EX contents_lao:list Z, EX contents_rao: list Z, 
    PROP 
    (
      Forall (fun x => 0 <= x <= Int.max_unsigned) contents_lao;
      Forall (fun x => 0 <= x <= Int.max_unsigned) contents_rao;
      l_i = 11; r_i = 11; 
      Forall2 eq (sublist 0 ri contents_lao) (sublist 0 ri contents_rao);
      Forall2 eq (sublist (ri + 1) 10 contents_lao) (sublist (ri + 1) 10 contents_rao); 
      0 <= li < l_i; 0 <= ri < r_i; lmax = rmax; li = ri;
      Znth ri contents_lao = Znth 10 contents_rao; Znth 10 contents_lao = Znth ri contents_rao; 
      lmax = Znth li contents_lao; rmax = Znth 10 contents_rao
    )
    LOCAL 
    (
      temp _r_i (Vint (Int.repr r_i)); 
      temp _rind (Vint (Int.repr ri)); 
      temp _r_max (Vint (Int.repr rmax));  
      temp _l_i (Vint (Int.repr l_i)); 
      temp _lind (Vint (Int.repr li)); 
      temp _l_max (Vint (Int.repr lmax)); 
      temp _l_a l_a; temp _r_a r_a
    )
    SEP 
    (
      data_at sh1 (tarray tuint 11) (map Vint (map Int.repr contents_lao)) l_a;
      data_at sh2 (tarray tuint 11) (map Vint (map Int.repr contents_rao)) r_a
    )
  )%assert.
  Exists l_i. Exists r_i. Exists lmax. Exists rmax. Exists li. Exists ri. 
  Exists contents_lao. Exists contents_rao. entailer!.
  Intros l_i1 r_i1 lmax1 rmax1 li1 ri1 contents_la1 contents_ra1.
  forward_if. forward.
  Exists l_i1. Exists r_i1. Exists lmax1. Exists rmax1. Exists li1. Exists ri1. 
  Exists contents_la1. Exists contents_ra1. entailer!. rewrite H25 in H37. discriminate H37.
  (*right side discriminate*)
  Intros l_i1 r_i1 lmax1 rmax1 li1 ri1 contents_la1 contents_ra1.
  forward_loop 
  ( 
     EX l_i:Z, EX r_i:Z, EX lmax:Z, EX rmax:Z, EX li:Z, EX ri:Z, 
     EX contents_lao:list Z, EX contents_rao: list Z, 
     PROP 
     (
       Forall (fun x => 0 <= x <= Int.max_unsigned) contents_lao;
       Forall (fun x => 0 <= x <= Int.max_unsigned) contents_rao;
       (*In lmax contents_lao; In rmax contents_rao;*)
       (r_i <= 10) -> Forall2 eq contents_lao contents_rao;
       (r_i = 11) -> Forall2 eq (sublist 0 ri contents_lao) (sublist 0 ri contents_rao);
       (r_i = 11) -> Forall2 eq (sublist (ri + 1) 10 contents_lao) (sublist (ri + 1) 10 contents_rao); 
       0 <= l_i <= 11; 0 <= r_i <= 11; l_i = 11; r_i = 11; l_i = r_i; 
       0 <= li < l_i; 0 <= ri < r_i; lmax = rmax; li = ri;
       lmax = Znth li contents_lao; (r_i <= 10) -> rmax = Znth ri contents_rao;
       (r_i = 11) -> rmax = Znth 10 contents_rao;
       (r_i = 11) -> (Znth ri contents_lao = Znth 10 contents_rao);
       (r_i = 11) -> (Znth 10 contents_lao = Znth ri contents_rao)
     )
     LOCAL 
     (
       temp _r_i (Vint (Int.repr r_i)); 
       temp _rind (Vint (Int.repr ri)); 
       temp _r_max (Vint (Int.repr rmax));  
       temp _l_i (Vint (Int.repr l_i)); 
       temp _lind (Vint (Int.repr li)); 
       temp _l_max (Vint (Int.repr lmax)); 
       temp _l_a l_a; temp _r_a r_a
     )
     SEP 
     (
       data_at sh1 (tarray tuint 11) (map Vint (map Int.repr contents_lao)) l_a;
       data_at sh2 (tarray tuint 11) (map Vint (map Int.repr contents_rao)) r_a
     )
 )%assert
 break:
 ( 
    EX l_i:Z, EX r_i:Z, EX lmax:Z, EX rmax:Z, EX li:Z, EX ri:Z, 
    EX contents_lao:list Z, EX contents_rao: list Z, 
    PROP 
    (
      Forall (fun x => 0 <= x <= Int.max_unsigned) contents_lao;
      Forall (fun x => 0 <= x <= Int.max_unsigned) contents_rao;
      l_i = 11; r_i = 11; 
      Forall2 eq (sublist 0 ri contents_lao) (sublist 0 ri contents_rao);
      Forall2 eq (sublist (ri + 1) 10 contents_lao) (sublist (ri + 1) 10 contents_rao); 
      0 <= li < l_i; 0 <= ri < r_i; lmax = rmax; li = ri;
      Znth ri contents_lao = Znth 10 contents_rao; Znth 10 contents_lao = Znth ri contents_rao; 
      lmax = Znth li contents_lao; rmax = Znth 10 contents_rao
    )
    LOCAL 
    (
      temp _r_i (Vint (Int.repr r_i)); 
      temp _rind (Vint (Int.repr ri)); 
      temp _r_max (Vint (Int.repr rmax));  
      temp _l_i (Vint (Int.repr l_i)); 
      temp _lind (Vint (Int.repr li)); 
      temp _l_max (Vint (Int.repr lmax)); 
      temp _l_a l_a; temp _r_a r_a
    )
    SEP 
    (
      data_at sh1 (tarray tuint 11) (map Vint (map Int.repr contents_lao)) l_a;
      data_at sh2 (tarray tuint 11) (map Vint (map Int.repr contents_rao)) r_a
    )
  )%assert.
  Exists l_i1. Exists r_i1. Exists lmax1. Exists rmax1. Exists li1. Exists ri1. 
  Exists contents_la1. Exists contents_ra1. entailer!.
  Intros l_i2 r_i2 lmax2 rmax2 li2 ri2 contents_la2 contents_ra2.
  forward_if. forward.
  Exists l_i2. Exists r_i2. Exists lmax2. Exists rmax2. Exists li2. Exists ri2. 
  Exists contents_la2. Exists contents_ra2. entailer!. rewrite H40 in H51. discriminate H51.
  Intros l_i2 r_i2 lmax2 rmax2 li2 ri2 contents_la2 contents_ra2. 
  assert_PROP (Zlength contents_la2 = 11). {
    entailer!. rewrite <- H47. do 2 rewrite Zlength_map. reflexivity.
   }
   assert_PROP (Zlength contents_ra2 = 11). {
    entailer!. rewrite <- H51. do 2 rewrite Zlength_map. reflexivity.
   }
  fastforward.
  (*very last*)
  (*destruct first*)
  destruct (ri2 =? 10) eqn:Hrin2. apply Z.eqb_eq in Hrin2.
  (*first case*)
  Exists contents_la2. Exists contents_ra2. entailer!. rewrite <- sublist_same with 0 11 contents_la2 by lia.
  rewrite <- sublist_same with 0 11 contents_ra2 by lia.
  rewrite sublist_split with 0 10 11 contents_la2 by lia. rewrite sublist_split with 0 10 11 contents_ra2 by lia.
  apply Forall2_app. assumption. rewrite !sublist_len_1 by lia.  Search Forall2 cons. apply Forall2_cons.
  assumption. apply Forall2_nil.
  (*entailment*) Search upd_Znth. rewrite upd_Znth_twice by list_solve. rewrite !upd_Znth_map by lia.
  rewrite upd_Znth_unfold by lia. simpl. rewrite H46. rewrite sublist_nil. Search sublist.
  rewrite <- sublist_last_1 by lia. simpl. rewrite sublist_same by lia. entailer!.
  (*second case*) assert (ri2 < 10) by lia.
  Exists (sublist 0 li2 contents_la2 ++ [Znth 10 contents_la2] ++ (sublist (li2 + 1) 10 contents_la2) ++ [lmax2]).
  Exists contents_ra2.
  entailer!. rewrite <- sublist_same with 0 11 contents_ra2 by lia.   
  rewrite sublist_split with 0 ri2 11 contents_ra2 by list_solve.  rewrite sublist_split with ri2 (ri2 + 1) 11 contents_ra2 by list_solve.
  rewrite sublist_len_1 by list_solve. rewrite sublist_split with (ri2 + 1) 10 11 contents_ra2 by lia. rewrite sublist_len_1 by list_solve.
  apply Forall2_app. assumption. apply Forall2_app. apply Forall2_cons_iff. split. assumption. apply Forall2_nil.
  apply Forall2_app. assumption. apply Forall2_cons_iff. split. assumption. apply Forall2_nil.
  (*last equality entailment*)
  rewrite !upd_Znth_map by lia. apply derives_refl'. f_equal. f_equal. f_equal. 
  pattern (upd_Znth 10 contents_la2 (Znth ri2 contents_la2)) at 1. rewrite upd_Znth_unfold at 1 by lia.
  rewrite H46. replace (10 + 1) with 11 by lia. rewrite sublist_nil. Search app nil. rewrite app_nil_r.
  rewrite upd_Znth_unfold by list_solve. rewrite Zlength_app. rewrite !Zlength_sublist by lia.
  Search Zlength. rewrite Zlength_cons. rewrite Zlength_nil.
  replace (10 - 0 + Z.succ 0) with 11 by lia. list_solve.
Qed.


