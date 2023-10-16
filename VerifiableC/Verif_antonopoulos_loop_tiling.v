(* ================================================================= *)
(* antonoupoulous_sa_simple.c - no array for this*)

Require VC.Preface. 
Require Import Setoid.
Require Import VST.floyd.proofauto.
Require Import Coq.Classes.RelationClasses.

Require Import VC.antonopoulos_loop_tiling.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.
Print Int.repr. Print Vint. Print map. Search concat map.
Print flat_map. Print map.
(*Functional Model: empty for kestrel*)
(*API spec => verifyfunc spec *)
Definition verifyfunc_spec : ident * funspec :=
DECLARE _verifyfunc
  WITH a_1 : val, sh1 : share, contents_a1 : list Z,
  a_2 : val, sh2 : share, contents_a2 : list (list Z), 
  f : val, shf : share, contents_f : list Z
  PRE [ tptr tuint, tptr (tarray tuint 10), tptr tuint ]  
    (*ensure variables left and right are equal*)
    PROP 
    (
      writable_share sh1; writable_share sh2; readable_share shf;
      Zlength contents_a1 = 100; Zlength contents_a2 = 10; 
      Zlength (concat contents_a2) = 100; Zlength contents_f = 100
    )
    PARAMS (a_1; a_2; f)
    SEP 
    (
      data_at sh1 (tarray tuint 100) (map Vint (map Int.repr contents_a1)) a_1;
      data_at sh2 (tarray (tarray tuint 10) 10) (map (map Vint)(map (map Int.repr) contents_a2)) a_2;
      data_at shf (tarray tuint 100) (map Vint (map Int.repr contents_f)) f
    ) 
  POST [ tvoid ]
    EX contents_a1o : list Z, EX contents_a2o : list (list Z), 
    PROP 
    (
      Forall2 eq contents_a1o (concat contents_a2o)

    )
    RETURN () (*void*)
    SEP 
    (
      data_at sh1 (tarray tuint 100) (map Vint (map Int.repr contents_a1o)) a_1;
      data_at sh2 (tarray (tarray tuint 10) 10) (map (map Vint)(map (map Int.repr) contents_a2o)) a_2;
      data_at shf (tarray tuint 100) (map Vint (map Int.repr contents_f)) f
    ).



(*Pack APIs together*)
Definition Gprog := [verifyfunc_spec].

(*verify fun_spec - from here*)

(*verify fun_spec - from here*)
Lemma body_verifyfunc: semax_body Vprog Gprog f_verifyfunc verifyfunc_spec.
Proof. 
 start_function. 
 fastforward.
 forward_loop 
 (
   EX l_x:Z, EX r_i:Z, EX contents_a1o: list Z, EX contents_a2o: list (list Z), 
    PROP 
    (
      0 <= l_x <= 100; 0 <= r_i <= 10; r_i = Z.add l_x l_x;
      Forall2 eq (sublist 0 l_x contents_a1o) (sublist 0 l_x (concat contents_a2o));
      Forall2 eq (sublist 0 l_x contents_a1o) (sublist 0 l_x contents_f);
      Forall2 eq (sublist 0 (r_i * 10) (concat contents_a2o)) (sublist 0 (r_i * 10) contents_f)
    )
   LOCAL 
   (
      temp _l_x (Vint (Int.repr l_x)); 
      temp _r_i (Vint (Int.repr r_i)); 
      temp _a_1 a_1; temp _a_2 a_2; temp _f f
   )
   SEP 
   (
      data_at sh1 (tarray tuint 100) (map Vint (map Int.repr contents_a1o)) a_1;
      data_at sh2 (tarray (tarray tuint 10) 10) (map (map Vint)(map (map Int.repr) contents_a2o)) a_2;
      data_at shf (tarray tuint 100) (map Vint (map Int.repr contents_f)) f

   ))%assert
   break: 
   (
    EX l_x:Z, EX r_i:Z, EX contents_a1o: list Z, EX contents_a2o: list (list Z), 
    PROP 
    (
      0 <= l_x <= 100; 0 <= r_i <= 10; r_i = Z.add l_x l_x; l_x = 5; r_i = 10;
      Forall2 eq (sublist 0 l_x contents_a1o) (sublist 0 l_x (concat contents_a2o));
      Forall2 eq (sublist 0 l_x contents_a1o) (sublist 0 l_x contents_f);
      Forall2 eq (sublist 0 (r_i * 10) (concat contents_a2o)) (sublist 0 (r_i * 10) contents_f)
    )
   LOCAL 
   (
      temp _l_x (Vint (Int.repr l_x)); 
      temp _r_i (Vint (Int.repr r_i)); 
      temp _a_1 a_1; temp _a_2 a_2; temp _f f
   )
   SEP 
   (
      data_at sh1 (tarray tuint 100) (map Vint (map Int.repr contents_a1o)) a_1;
      data_at sh2 (tarray (tarray tuint 10) 10) (map (map Vint)(map (map Int.repr) contents_a2o)) a_2;
      data_at shf (tarray tuint 100) (map Vint (map Int.repr contents_f)) f

   )
  )%assert.

 (*first existential - outermost if*)      
 Exists 0. Exists 0. Exists contents_a1. Exists contents_a2. entailer!. 
 Intros l_x r_i contents_a1o contents_a2o. 
 assert_PROP (Zlength contents_a1o = 100). {
  entailer!. rewrite <- H10. rewrite !Zlength_map. reflexivity.
 }
 assert_PROP (Zlength contents_a2o = 10). {
  entailer!. rewrite <- H14. rewrite !Zlength_map. reflexivity.
 }
 assert_PROP (Zlength (concat contents_a2o) = 100). {
  entailer!. rewrite Zlength_concat' with 10 10 contents_a2o.
  lia. lia. apply Forall_forall_Znth. intros. 
  rewrite Forall_forall in H16.
  specialize (H16 (map Vint (map Int.repr (Znth i contents_a2o)))).
  spec H16. apply in_map_iff.
  exists (map Int.repr (Znth i contents_a2o)). split; auto. Print spec.
  Search In app.
  apply in_map. apply Znth_In. list_solve.
  simplify_value_fits in H16. destruct H16. list_solve.
 }
 forward_if. forward. 
 (*second if - entailer contradiction*)
 assert (l_x = 100) by lia. rewrite H13 in H5. simpl in H5. rewrite H5 in H4.
 destruct H4 as [? ?]. contradiction. forward_if. forward.
 (*existential - else*)
 Exists l_x. Exists r_i. Exists contents_a1o. Exists contents_a2o.
 entailer!. fastforward. 
 forward_while 
 (
    EX r_j:Z, EX contents_a1in: list Z, EX contents_a2in: list (list Z),
    PROP 
    (
      0 <= r_j <= 10; Zlength contents_a1in = 100;
      Zlength contents_a2in = 10; Zlength (concat contents_a2in) = 100;
      (r_i = 0 /\ r_j = 0) -> Forall2 eq (sublist 0 r_i contents_a1in) (sublist 0 r_i (concat contents_a2in));
      ~(r_i = 0 /\ r_j = 0) -> Forall2 eq (sublist 0 (l_x + 1) contents_a1in) (sublist 0 (l_x + 1)  (concat contents_a2in));
      Forall2 eq (sublist 0 (l_x + 1) contents_a1in) (sublist 0 (l_x + 1) contents_f);
      Forall2 eq (sublist 0 (r_i * 10 + r_j) (concat contents_a2in)) (sublist 0 (r_i * 10 + r_j) contents_f)
    )
    LOCAL 
    (
      temp _r_j (Vint (Int.repr r_j));
      temp _l_x (Vint (Int.repr (l_x + 1)));
      temp _t'5 (Vint (Int.repr (Znth l_x contents_f)));
      temp _r_i (Vint (Int.repr r_i));
      temp _a_1 a_1; temp _a_2 a_2; 
      temp _f f
    )
    SEP 
    (
      data_at sh1 (tarray tuint 100)(map Vint (map Int.repr contents_a1in)) a_1;
      data_at sh2 (tarray (tarray tuint 10) 10) (map (map Vint)(map (map Int.repr) contents_a2in)) a_2;
      data_at shf (tarray tuint 100) (map Vint (map Int.repr contents_f)) f
    )
 ).
 Exists 0. Exists (sublist 0 l_x contents_a1o ++ [Znth l_x contents_f] ++ sublist (l_x + 1) 100 contents_a1o).
 Exists contents_a2o. entailer!.
 (*prove base case: *)
 split. list_solve. split. intros. destruct H5 as [? ?].
 rewrite H5. rewrite !sublist_nil. list_solve. split. intros. assert (l_x + l_x > 0) by lia.
 assert (l_x + 1 <= l_x + l_x) by lia. rewrite app_assoc.
 rewrite sublist0_app1 by list_solve. replace (sublist 0 (l_x + 1)
 (sublist 0 l_x contents_a1o ++ [Znth l_x contents_f])) with (sublist 0 l_x contents_a1o ++ [Znth l_x contents_f]) by list_solve.
 rewrite sublist_split with 0 l_x (l_x + 1) (concat contents_a2o) by list_solve. rewrite sublist_len_1 by lia.
 apply Forall2_app. assumption. move H8 at bottom. 
 eapply Forall2_Znth with (i := l_x) in H8. rewrite !Znth_sublist in H8 by lia.
 replace (l_x + 0) with l_x in H8 by lia. rewrite H8. apply Forall2_cons. reflexivity. list_solve. list_solve.
 rewrite app_assoc. rewrite sublist0_app1. replace (sublist 0 (l_x + 1)
 (sublist 0 l_x contents_a1o ++ [Znth l_x contents_f])) with (sublist 0 l_x contents_a1o ++
 [Znth l_x contents_f]) by list_solve. rewrite sublist_split with 0 l_x (l_x + 1) contents_f by lia.
 apply Forall2_app. assumption. rewrite sublist_len_1. apply Forall2_cons. reflexivity. list_solve. lia.
 rewrite Zlength_app. rewrite Zlength_sublist by lia. rewrite Zlength_cons. rewrite Zlength_nil. lia.
 rewrite !upd_Znth_map. apply derives_refl'. f_equal. f_equal. f_equal.
 rewrite upd_Znth_unfold by lia. rewrite H9. reflexivity.
 entailer!.
 assert_PROP (forall i:Z, 0 <= i < 10 -> Zlength (Znth i contents_a2in) = 10).
 {
    entailer!. intros.
    rewrite Forall_forall in H27.
    specialize (H27 (map Vint (map Int.repr (Znth i contents_a2in)))).
    spec H27. apply in_map_iff.
    exists (map Int.repr (Znth i contents_a2in)). split; auto.
    apply in_map. apply Znth_In. list_solve.
    simplify_value_fits in H27. destruct H27. list_solve.
 }
 fastforward.
 (*plus 1*)
 Exists ((r_j + 1), contents_a1in,
 sublist 0 r_i contents_a2in ++ [sublist 0 r_j (Znth r_i contents_a2in) ++ [Znth (r_i*10 + r_j) contents_f] ++ sublist (r_j + 1) 10 (Znth r_i contents_a2in)] ++ sublist (r_i + 1) 10 contents_a2in).
 entailer!.
 split. lia. split. list_solve. split. (*list_solve. split.*)
 rewrite !concat_app.  rewrite !Zlength_app. 
 rewrite Zlength_concat' with (l_x + l_x) 10 (sublist 0 (l_x + l_x) contents_a2in).
 rewrite Zlength_concat' with (9 - (l_x + l_x)) 10 (sublist (l_x + l_x + 1) 10 contents_a2in).
 rewrite concat_cons. rewrite concat_nil. rewrite app_nil_r.
 rewrite !Zlength_app. rewrite !Zlength_sublist. replace (Zlength
 [Znth ((l_x + l_x) * 10 + r_j) contents_f]) with 1 by list_solve. lia. lia.
 move H22 at bottom. rewrite H22 by lia. lia. lia. rewrite H22 by lia. lia.  
 rewrite Zlength_sublist by lia. lia. apply Forall_sublist.
 apply Forall_forall_Znth. rewrite H16. assumption. 
 rewrite Zlength_sublist by lia. lia. apply Forall_sublist.
 apply Forall_forall_Znth. rewrite H16. assumption.
 (*next part:*)
 split. intros. destruct H5 as [? ?]. assert (r_j + 1 > 0) by lia. rewrite H32 in H33.
 inversion H33.
 split. intros. assert (r_j + 1 > 0) by lia.
 destruct (l_x + l_x =? 0) eqn:Hlx. assert (l_x = 0) by lia. rewrite H33.
 simpl. destruct (r_j =? 0) eqn:Hrj. assert (r_j = 0) by lia. rewrite H34. simpl. 
 rewrite !Znth_cons_sublist by lia. replace (0 + 1) with 1 by lia. 
 rewrite !sublist0_app1 by list_solve. rewrite !sublist_sublist00 by lia.
 move H20 at bottom. rewrite H33 in H20. replace (0 + 1) with 1 in H20 by lia. assumption.
 assert (r_j > 0) by lia. simpl. replace (0 + r_j) with r_j by lia.
 assert (Zlength (Znth 0 contents_a2in) = 10). {
  move H22 at bottom. specialize H22 with 0. rewrite H22 by lia. reflexivity.
 }
 simpl. rewrite sublist0_app1. rewrite sublist0_app1. rewrite sublist_split with 0 1 r_j (Znth 0 contents_a2in) by lia.
 rewrite sublist0_app1. rewrite <- sublist_parts1 by lia.
 move H20 at bottom. move H21 at bottom. rewrite sublist_len_1. rewrite sublist_split with 0 1 (l_x + 1) contents_a1in in H20 by lia.
 rewrite sublist_split with 0 1 (l_x + 1) contents_f in H20 by lia. rewrite !sublist_len_1 in H20.
 apply Forall2_app_inv in H20. destruct H20 as [? ?]. rewrite sublist_len_1.
 rewrite sublist_split with 0 1 ((l_x + l_x) * 10 + r_j) (concat contents_a2in) in H21.
 rewrite sublist_split with 0 1 ((l_x + l_x) * 10 + r_j) contents_f in H21 by lia.
 apply Forall2_app_inv in H21. destruct H21 as [? ?]. rewrite <- sublist_same with 0 10 contents_a2in in H21 by lia.
 rewrite sublist_split with 0 1 10 contents_a2in in H21 by lia. rewrite concat_app in H21.
 rewrite sublist0_app1 in H21. rewrite !sublist_len_1 in H21. simpl in H21. rewrite app_nil_r in H21.
 move H20 at bottom. move H21 at bottom. eapply Forall2_Znth with (i := 0) in H20.
 rewrite !Znth_0_cons in H20. rewrite H20. eapply Forall2_Znth with (i := 0) in H21.
 rewrite !Znth_0_cons in H21. rewrite H21. apply Forall2_cons. reflexivity. list_solve.
 rewrite Zlength_cons. rewrite Zlength_nil. lia. rewrite Zlength_cons. rewrite Zlength_nil. lia.
 lia. lia. rewrite sublist_len_1. simpl. rewrite app_nil_r. rewrite H35. lia. lia.
 rewrite sublist_len_1. simpl. rewrite app_nil_r. rewrite H35. lia. lia.
 rewrite <- !ZtoNat_Zlength. f_equal. rewrite !Zlength_sublist by lia. lia. lia. lia.
 rewrite H35. lia. rewrite <- !ZtoNat_Zlength. f_equal. lia. lia. lia. 
 rewrite Zlength_sublist. lia. lia. rewrite H35. lia. rewrite Zlength_sublist. lia.
 lia. rewrite H35. lia. rewrite Zlength_app. rewrite Zlength_cons. rewrite !Zlength_sublist.
 lia. lia. rewrite H35. lia. lia. lia. 
 assert (l_x + l_x > 0) by lia. assert (l_x + 1 <= l_x + l_x) by lia.
 rewrite sublist_split with 0 l_x (l_x + 1) contents_a1in by lia.
 simpl. rewrite concat_app. rewrite sublist0_app1. 
 rewrite sublist_split with 0 (l_x + 1) (l_x + l_x) contents_a2in by lia. rewrite concat_app.
 rewrite sublist0_app1. move H19 at bottom. move H20 at bottom. spec H19. lia.
 (*eapply Forall2_Znth with (i := l_x) in H19.*) 
 rewrite sublist_split with 0 l_x (l_x + 1) (concat (sublist 0 (l_x + 1) contents_a2in)).
 rewrite sublist_len_1. apply Forall2_app. 
 rewrite sublist_split with 0 l_x (l_x + 1) contents_a1in in H19 by lia.
 rewrite sublist_split with 0 l_x (l_x + 1) (concat contents_a2in) in H19 by lia.
 apply Forall2_app_inv in H19. destruct H19 as [? ?].
 rewrite <- sublist_same with 0 10 contents_a2in in H19 by lia.
 rewrite sublist_split with 0 l_x 10 contents_a2in in H19 by lia.
 rewrite concat_app in H19. rewrite sublist0_app1 in H19.
 rewrite sublist_split with 0 l_x (l_x + 1) contents_a2in by lia. rewrite concat_app.
 rewrite sublist0_app1. assumption.
 rewrite Zlength_concat' with l_x 10 (sublist 0 l_x contents_a2in).
 lia. rewrite Zlength_sublist by lia. lia. apply Forall_sublist.
 apply Forall_Znth. rewrite H16. assumption.
 rewrite Zlength_concat' with l_x 10 (sublist 0 l_x contents_a2in). lia.
 rewrite Zlength_sublist by lia. lia. apply Forall_sublist. apply Forall_Znth. rewrite H16. assumption.
 rewrite <- !ZtoNat_Zlength. f_equal. rewrite Zlength_sublist by lia.
 rewrite Zlength_sublist. lia. lia. lia. rewrite sublist_len_1. rewrite sublist_split with 0 l_x (l_x + 1) contents_a2in by lia.
 rewrite sublist_len_1. rewrite concat_app. simpl. rewrite app_nil_r.
 assert (Zlength (concat (sublist 0 l_x contents_a2in)) = l_x * 10). {
  rewrite Zlength_concat' with l_x 10 (sublist 0 l_x contents_a2in). 
  reflexivity. rewrite Zlength_sublist by lia. lia. apply Forall_sublist.
  apply Forall_Znth. rewrite H16. assumption.
 }
 rewrite app_Znth1. rewrite sublist_split with 0 (l_x + 1) (l_x + 1) contents_a1in in H19 by lia.
 rewrite sublist_split with 0 (l_x + 1) (l_x + 1) (concat contents_a2in) in H19. rewrite !sublist_nil in H19.
 rewrite !app_nil_r in H19. eapply Forall2_Znth with (i := l_x) in H19.
 rewrite sublist_split with 0 l_x (l_x + 1) contents_a1in in H19 by lia. rewrite sublist_len_1 in H19 by lia.
 rewrite app_Znth2 in H19. rewrite Zlength_sublist in H19 by lia. replace (l_x - (l_x - 0)) with 0 in H19 by lia.
 rewrite Znth_0_cons in H19. rewrite <- sublist_same with 0 10 contents_a2in in H19 by lia.
 rewrite sublist_split with 0 l_x 10 contents_a2in in H19 by lia. rewrite concat_app in H19.
 rewrite sublist0_app1 in H19. rewrite Znth_sublist in H19 by lia.
 replace (l_x + 0) with l_x in H19 by lia. rewrite <- H19. apply Forall2_cons. reflexivity. list_solve.
 rewrite Zlength_concat' with l_x 10 (sublist 0 l_x contents_a2in). lia. rewrite Zlength_sublist by lia. lia.
 apply Forall_sublist. apply Forall_Znth. rewrite H16. assumption.
 rewrite Zlength_sublist by lia. lia. rewrite Zlength_sublist by lia. lia. lia. lia. lia. lia.
 rewrite Zlength_concat' with (l_x + 1) 10 (sublist 0 (l_x + 1) contents_a2in). lia.
 rewrite Zlength_sublist by lia. lia. apply Forall_sublist. apply Forall_Znth. rewrite H16. assumption. lia. lia.
 rewrite Zlength_concat' with (l_x + 1) 10 (sublist 0 (l_x + 1) contents_a2in). lia.
 rewrite Zlength_sublist by lia. lia. apply Forall_sublist. apply Forall_Znth. rewrite H16. assumption. 
 rewrite Zlength_concat' with (l_x + 1) 10 (sublist 0 (l_x + 1) contents_a2in). lia.
 rewrite Zlength_sublist by lia. lia. apply Forall_sublist. apply Forall_Znth. rewrite H16. assumption.
 rewrite Zlength_concat' with (l_x + l_x) 10 (sublist 0 (l_x + l_x) contents_a2in). lia.
 rewrite Zlength_sublist by lia. lia. apply Forall_sublist. apply Forall_Znth. rewrite H16. assumption.
 move H21 at bottom. destruct ((l_x + l_x) =? 0) eqn:Hlx. assert (l_x + l_x = 0) by lia.
 rewrite H5. simpl. replace (0 + (r_j + 1)) with (r_j + 1) by lia. replace (0 + r_j) with r_j by lia.
 assert (Zlength (Znth 0 contents_a2in) = 10). {
  move H22 at bottom. specialize (H22 0). rewrite H22 by lia. reflexivity.
 }
 rewrite Znth_cons_sublist by lia. rewrite app_assoc. rewrite sublist0_app1. rewrite sublist0_app1.
 rewrite sublist_len_1 by lia. rewrite sublist_split with 0 r_j (r_j + 1) contents_f by lia.
 rewrite sublist_len_1 by lia. rewrite H5 in H21. replace (0 * 10 + r_j) with r_j in H21 by lia.
 rewrite <- sublist_same with 0 10 contents_a2in in H21 by lia. rewrite sublist_split with 0 1 10 contents_a2in in H21 by lia.
 rewrite sublist_len_1 in H21 by lia. rewrite concat_app in H21. simpl in H21. rewrite app_nil_r in H21.
 rewrite sublist0_app1 in H21. rewrite sublist_split with 0 r_j (r_j + 1) (sublist 0 r_j (Znth 0 contents_a2in) ++
 [Znth r_j contents_f]). apply Forall2_app. rewrite sublist0_app1. rewrite sublist_prefix by lia.
 replace (Z.min r_j r_j) with r_j by lia. assumption.  rewrite Zlength_sublist by lia. lia.
 rewrite sublist_app2. rewrite !Zlength_sublist by lia. replace (r_j - (r_j - 0)) with 0 by lia. replace (r_j + 1 - (r_j - 0)) with 1 by lia.
 rewrite sublist_len_1. rewrite Znth_0_cons. apply Forall2_cons. reflexivity. list_solve. 
 rewrite Zlength_cons. rewrite Zlength_nil. lia. rewrite Zlength_sublist by lia. lia. lia.
 rewrite Zlength_app. rewrite Zlength_sublist by lia. rewrite Zlength_cons. rewrite Zlength_nil. lia.
 lia. rewrite sublist_len_1 by lia. rewrite Zlength_app. rewrite Zlength_sublist by lia. 
 rewrite Zlength_cons. rewrite Zlength_nil. lia. rewrite sublist_len_1 by lia. rewrite !Zlength_app.
 rewrite !Zlength_sublist by lia. rewrite Zlength_cons. rewrite Zlength_nil. lia.   
 assert (l_x + l_x > 0) by lia. assert (l_x + 1 <= l_x + l_x) by lia.
 move H21 at bottom. move H22 at bottom.
 assert (Zlength (Znth (l_x + l_x) contents_a2in) = 10). {
  specialize H22 with (l_x + l_x). rewrite H22 by lia. reflexivity.
 }
 rewrite app_assoc. rewrite concat_app. rewrite sublist0_app1.
 rewrite concat_app. rewrite sublist_split with 0 ((l_x + l_x) * 10 + r_j) ((l_x + l_x) * 10 + (r_j + 1)) (concat (sublist 0 (l_x + l_x) contents_a2in) ++
 concat[sublist 0 r_j (Znth (l_x + l_x) contents_a2in) ++ [Znth ((l_x + l_x) * 10 + r_j) contents_f] ++
    sublist (r_j + 1) 10 (Znth (l_x + l_x) contents_a2in)]). 
 rewrite sublist_split with 0 ((l_x + l_x) * 10 + r_j) ((l_x + l_x) * 10 + (r_j + 1)) contents_f by lia.
 apply Forall2_app. simpl. rewrite app_nil_r. rewrite app_assoc. rewrite sublist0_app1.
 rewrite <- sublist_same with 0 10 contents_a2in in H21 by lia.
 rewrite sublist_split with 0 (l_x + l_x) 10 contents_a2in in H21 by lia. 
 rewrite sublist_split with (l_x + l_x) (l_x + l_x + 1) 10 contents_a2in in H21 by lia.  
 rewrite sublist_len_1 in H21. rewrite app_assoc in H21. rewrite concat_app in H21.
 rewrite sublist0_app1 in H21. rewrite concat_app in H21. simpl in H21. rewrite app_nil_r in H21. 
 rewrite <- sublist_same with 0 10 (Znth (l_x + l_x) contents_a2in) in H21 by lia. rewrite sublist_split with 0 r_j 10 (Znth (l_x + l_x) contents_a2in) in H21 by lia.
 rewrite app_assoc in H21. rewrite sublist0_app1 in H21. assumption.
 rewrite Zlength_app. rewrite Zlength_concat' with (l_x + l_x) 10 (sublist 0 (l_x + l_x) contents_a2in).
 rewrite Zlength_sublist by lia. lia. rewrite Zlength_sublist by lia. lia.
 apply Forall_sublist. apply Forall_Znth. rewrite H16. assumption. rewrite concat_app.
 simpl. rewrite app_nil_r. rewrite Zlength_app. rewrite Zlength_concat' with (l_x + l_x) 10 (sublist 0 (l_x + l_x) contents_a2in).
 lia. rewrite Zlength_sublist by lia. lia. apply Forall_sublist. apply Forall_Znth. rewrite H16.
 assumption. lia. rewrite Zlength_app. rewrite Zlength_concat' with (l_x + l_x) 10 (sublist 0 (l_x + l_x) contents_a2in).
 rewrite Zlength_sublist by lia. lia. rewrite Zlength_sublist by lia. lia. 
 apply Forall_sublist. apply Forall_Znth. rewrite H16. assumption.
 assert (Zlength (Znth (l_x + l_x) contents_a2in) = 10). {
  specialize H22 with (l_x + l_x). rewrite H22 by lia. reflexivity.
 }
 replace ((l_x + l_x) * 10 + (r_j + 1)) with ((l_x + l_x) * 10 + r_j + 1) by lia.
 rewrite !sublist_len_1. simpl. rewrite app_nil_r. rewrite app_assoc. 
 assert (Zlength (concat (sublist 0 (l_x + l_x) contents_a2in) ++ sublist 0 r_j
    (Znth (l_x + l_x) contents_a2in)) = (l_x + l_x)*10 + r_j). {
      rewrite Zlength_app. rewrite Zlength_concat' with (l_x + l_x) 10 (sublist 0 (l_x + l_x) contents_a2in).
      rewrite Zlength_sublist by lia. lia. rewrite Zlength_sublist by lia. lia.
      apply Forall_sublist. apply Forall_Znth. rewrite H16. assumption.
    } 
 rewrite app_Znth2. rewrite H35. replace ((l_x + l_x) * 10 + r_j - ((l_x + l_x) * 10 + r_j)) with 0 by lia.
 rewrite Znth_0_cons. apply Forall2_cons. reflexivity. list_solve. rewrite H35. lia.
 lia. simpl. rewrite app_nil_r. rewrite !Zlength_app. rewrite Zlength_cons.
 rewrite !Zlength_sublist by lia. replace (r_j - 0 + Z.succ (10 - (r_j + 1))) with 10 by lia.
 rewrite Zlength_concat' with (l_x + l_x) 10 (sublist 0 (l_x + l_x) contents_a2in).
 lia. rewrite Zlength_sublist by lia. lia. apply Forall_sublist. apply Forall_Znth. rewrite H16. assumption.
 lia. simpl. rewrite app_nil_r. rewrite !Zlength_app. rewrite !Zlength_sublist by lia. rewrite Zlength_cons.
 rewrite Zlength_sublist by lia. 
 replace (r_j - 0 + Z.succ (10 - (r_j + 1))) with 10 by lia.
 rewrite Zlength_concat' with (l_x + l_x) 10 (sublist 0 (l_x + l_x) contents_a2in).
 lia. rewrite Zlength_sublist by lia. lia. apply Forall_sublist. apply Forall_Znth. rewrite H16. assumption.
 rewrite concat_app. simpl. rewrite app_nil_r. rewrite !Zlength_app. rewrite Zlength_cons. rewrite !Zlength_sublist by lia. 
 replace (r_j - 0 + Z.succ (10 - (r_j + 1))) with 10 by lia.
 rewrite Zlength_concat' with (l_x + l_x) 10 (sublist 0 (l_x + l_x) contents_a2in).
 lia. rewrite Zlength_sublist by lia. lia. apply Forall_sublist. apply Forall_Znth. rewrite H16. assumption.
 (*prove a2in*)
 rewrite !Znth_map. rewrite !upd_Znth_map. apply derives_refl'. f_equal. f_equal. f_equal.
 pattern (upd_Znth r_j (Znth (l_x + l_x) contents_a2in)
 (Znth ((l_x + l_x) * 10 + r_j) contents_f)) at 1. rewrite upd_Znth_unfold.
 assert (Zlength (Znth (l_x + l_x) contents_a2in) = 10). {
  specialize H22 with (l_x + l_x). rewrite H22 by lia. reflexivity.
 }
 rewrite H5. rewrite <- sublist_same with 0 10 contents_a2in by lia. 
 rewrite sublist_split with 0 (l_x + l_x) 10 contents_a2in by lia.
 rewrite upd_Znth_app2. rewrite Zlength_sublist by lia. simpl.
 replace (l_x + l_x - (l_x + l_x - 0)) with 0 by lia. 
 rewrite sublist_split with  (l_x + l_x) (l_x + l_x + 1) 10 contents_a2in.
 rewrite upd_Znth_app1. rewrite sublist_len_1. rewrite upd_Znth_unfold. simpl.
 rewrite sublist0_app1. rewrite sublist_prefix. 
 replace (Z.min (l_x + l_x) (l_x + l_x)) with (l_x + l_x) by lia.
 f_equal. try list_solve.  rewrite Zlength_sublist by lia. lia. rewrite Zlength_cons.
 rewrite Zlength_nil. lia. lia. rewrite Zlength_sublist by lia. lia. lia. lia.
 rewrite !Zlength_sublist by lia. lia. 
 assert (Zlength (Znth (l_x + l_x) contents_a2in) = 10). {
  specialize H22 with (l_x + l_x). rewrite H22 by lia. reflexivity.
 }
 lia. lia. rewrite !Zlength_map. lia.
 forward. forward_if. forward.
 forward_while 
 (
    EX r_j1:Z, EX contents_a1in1: list Z, EX contents_a2in1: list (list Z),
    PROP 
    (
      0 <= r_j1 <= 10; Zlength contents_a1in1 = 100;
      Zlength contents_a2in1 = 10; Zlength (concat contents_a2in1) = 100;
      Forall2 eq (sublist 0 (l_x + 1) contents_a1in1) (sublist 0 (l_x + 1)  (concat contents_a2in1));
      Forall2 eq (sublist 0 (l_x + 1) contents_a1in1) (sublist 0 (l_x + 1) contents_f);
      Forall2 eq (sublist 0 ((r_i + 1) * 10 + r_j1) (concat contents_a2in1)) (sublist 0 ((r_i + 1) * 10 + r_j1) contents_f)
    )
    LOCAL 
    (
      temp _r_j__1 (Vint (Int.repr r_j1));
      temp _l_x (Vint (Int.repr (l_x + 1)));
      temp _t'5 (Vint (Int.repr (Znth l_x contents_f)));
      temp _r_i (Vint (Int.repr (r_i + 1)));
      temp _a_1 a_1; temp _a_2 a_2; 
      temp _f f
    )
    SEP 
    (
      data_at sh1 (tarray tuint 100)(map Vint (map Int.repr contents_a1in1)) a_1;
      data_at sh2 (tarray (tarray tuint 10) 10) (map (map Vint)(map (map Int.repr) contents_a2in1)) a_2;
      data_at shf (tarray tuint 100) (map Vint (map Int.repr contents_f)) f
    )
 ).
 Exists 0. Exists contents_a1in. (*Exists (sublist 0 l_x contents_a1o ++ [Znth l_x contents_f] ++ sublist (l_x + 1) 100 contents_a1o).*)
 Exists contents_a2in. entailer!.
 (*prove base case: *)
 split. spec H19. lia. assumption. move H21 at bottom. assert (r_j = 10) by lia.
 rewrite H5 in H21. replace ((l_x + l_x + 1) * 10) with ((l_x + l_x) * 10 + 10) by lia.
 assumption. entailer!.
 assert_PROP (forall i:Z, 0 <= i < 10 -> Zlength (Znth i contents_a2in1) = 10).
 {
    entailer!. intros.
    rewrite Forall_forall in H35.
    specialize (H35 (map Vint (map Int.repr (Znth i contents_a2in1)))).
    spec H35. apply in_map_iff.
    exists (map Int.repr (Znth i contents_a2in1)). split; auto.
    apply in_map. apply Znth_In. list_solve.
    simplify_value_fits in H35. destruct H35. list_solve.
 }
 fastforward.
 (*plus 1*)
 Exists ((r_j1 + 1), contents_a1in1,
 sublist 0 (r_i + 1) contents_a2in1 ++ [sublist 0 r_j1 (Znth (r_i + 1) contents_a2in1) ++ [Znth ((r_i + 1)*10 + r_j1) contents_f] ++ sublist (r_j1 + 1) 10 (Znth (r_i + 1) contents_a2in1)] ++ sublist (r_i + 2) 10 contents_a2in1).
 entailer!.
 split. lia. split. list_solve. 
 assert (Zlength (Znth (l_x + l_x + 1) contents_a2in1) = 10). {
  move H30 at bottom. specialize H30 with (l_x + l_x + 1). 
  rewrite H30 by lia. reflexivity.
 }
 split. (*list_solve. split.*)
 rewrite !concat_app.  rewrite !Zlength_app. 
 rewrite Zlength_concat' with (l_x + l_x + 1) 10 (sublist 0 (l_x + l_x + 1) contents_a2in1).
 rewrite Zlength_concat' with (8 - (l_x + l_x)) 10 (sublist (l_x + l_x + 2) 10 contents_a2in1).
 rewrite concat_cons. rewrite concat_nil. rewrite app_nil_r.
 rewrite !Zlength_app. rewrite !Zlength_sublist. rewrite Zlength_cons.  
 rewrite Zlength_nil. lia. lia. lia. lia. lia. rewrite Zlength_sublist by lia.
 lia. apply Forall_sublist.
 apply Forall_forall_Znth. rewrite H25. assumption. 
 rewrite Zlength_sublist by lia. lia. apply Forall_sublist.
 apply Forall_forall_Znth. rewrite H25. assumption.
 (*next part:*)
 split. assert (l_x + 1 <= l_x + l_x + 1) by lia.
 move H27 at bottom. move H28 at bottom.
 rewrite sublist_split with 0 l_x (l_x + 1) contents_a1in1 by lia.
 simpl. rewrite concat_app. rewrite sublist0_app1. 
 rewrite sublist_split with 0 (l_x + 1) (l_x + l_x + 1) contents_a2in1 by lia. rewrite concat_app.
 rewrite sublist0_app1.
 (*eapply Forall2_Znth with (i := l_x) in H19.*) 
 rewrite sublist_split with 0 l_x (l_x + 1) (concat (sublist 0 (l_x + 1) contents_a2in1)).
 rewrite sublist_len_1. apply Forall2_app. 
 rewrite sublist_split with 0 l_x (l_x + 1) contents_a1in1 in H27 by lia.
 rewrite sublist_split with 0 l_x (l_x + 1) (concat contents_a2in1) in H27 by lia.
 apply Forall2_app_inv in H27. destruct H27 as [? ?].
 rewrite <- sublist_same with 0 10 contents_a2in1 in H27 by lia.
 rewrite sublist_split with 0 l_x 10 contents_a2in1 in H27 by lia.
 rewrite concat_app in H27. rewrite sublist0_app1 in H27.
 rewrite sublist_split with 0 l_x (l_x + 1) contents_a2in1 by lia. rewrite concat_app.
 rewrite sublist0_app1. assumption.
 rewrite Zlength_concat' with l_x 10 (sublist 0 l_x contents_a2in1). lia.
 rewrite Zlength_sublist by lia. lia. apply Forall_sublist.
 apply Forall_Znth. rewrite H25. assumption.
 rewrite Zlength_concat' with l_x 10 (sublist 0 l_x contents_a2in1). lia.
 rewrite Zlength_sublist by lia. lia. apply Forall_sublist. apply Forall_Znth. rewrite H25. assumption.
 rewrite <- !ZtoNat_Zlength. f_equal. rewrite !Zlength_sublist by lia.
 lia. rewrite sublist_len_1. rewrite sublist_split with 0 l_x (l_x + 1) contents_a2in1 by lia.
 rewrite sublist_len_1. rewrite concat_app. simpl. rewrite app_nil_r.
 assert (Zlength (concat (sublist 0 l_x contents_a2in1)) = l_x * 10). {
  rewrite Zlength_concat' with l_x 10 (sublist 0 l_x contents_a2in1). 
  reflexivity. rewrite Zlength_sublist by lia. lia. apply Forall_sublist.
  apply Forall_Znth. rewrite H25. assumption.
 }
 destruct (l_x =? 0) eqn: Hlx. assert (l_x = 0) by lia. rewrite H42. rewrite sublist_nil. rewrite concat_nil.
 rewrite app_nil_l. rewrite H42 in H27. replace (0 + 1) with 1 in H27 by lia.
 rewrite !sublist_len_1 in H27 by lia. rewrite <- sublist_same with 0 10 contents_a2in1 in H27 by lia.
 rewrite sublist_split with 0 1 10 contents_a2in1 in H27 by lia. rewrite sublist_len_1 in H27 by lia.
 rewrite concat_app in H27. simpl in H27. rewrite app_nil_r in H27. rewrite app_Znth1 in H27.
 assumption. move H30 at bottom. specialize H30 with 0. rewrite H30 by lia. lia.
 assert (l_x > 0) by lia.
 rewrite app_Znth1. rewrite sublist_split with 0 (l_x + 1) (l_x + 1) contents_a1in1 in H27 by lia.
 rewrite sublist_split with 0 (l_x + 1) (l_x + 1) (concat contents_a2in1) in H27. rewrite !sublist_nil in H27.
 rewrite !app_nil_r in H27. eapply Forall2_Znth with (i := l_x) in H27.
 rewrite sublist_split with 0 l_x (l_x + 1) contents_a1in1 in H27 by lia. rewrite sublist_len_1 in H27 by lia.
 rewrite app_Znth2 in H27. rewrite Zlength_sublist in H27 by lia. replace (l_x - (l_x - 0)) with 0 in H27 by lia.
 rewrite Znth_0_cons in H27. rewrite <- sublist_same with 0 10 contents_a2in1 in H27 by lia.
 rewrite sublist_split with 0 l_x 10 contents_a2in1 in H27 by lia. rewrite concat_app in H27. 
 rewrite sublist_split with l_x (l_x + 1) 10 contents_a2in1 in H27 by lia. rewrite concat_app in H27.
 rewrite sublist_len_1 in H27. simpl in H27. rewrite app_nil_r in H27. 
 rewrite sublist0_app1 in H27. rewrite Znth_sublist in H27 by lia.
 replace (l_x + 0) with l_x in H27 by lia. rewrite <- H27. apply Forall2_cons. reflexivity. list_solve.
 rewrite Zlength_concat' with l_x 10 (sublist 0 l_x contents_a2in1). lia. rewrite Zlength_sublist by lia. lia.
 apply Forall_sublist. apply Forall_Znth. rewrite H25. assumption. lia.
 rewrite Zlength_sublist by lia. lia. rewrite Zlength_sublist by lia. lia. lia. lia. lia. lia.
 rewrite Zlength_concat' with (l_x + 1) 10 (sublist 0 (l_x + 1) contents_a2in1). lia.
 rewrite Zlength_sublist by lia. lia. apply Forall_sublist. apply Forall_Znth. rewrite H25. assumption. lia. lia.
 rewrite Zlength_concat' with (l_x + 1) 10 (sublist 0 (l_x + 1) contents_a2in1). lia.
 rewrite Zlength_sublist by lia. lia. apply Forall_sublist. apply Forall_Znth. rewrite H25. assumption. 
 rewrite Zlength_concat' with (l_x + 1) 10 (sublist 0 (l_x + 1) contents_a2in1). lia.
 rewrite Zlength_sublist by lia. lia. apply Forall_sublist. apply Forall_Znth. rewrite H25. assumption.
 rewrite Zlength_concat' with (l_x + l_x + 1) 10 (sublist 0 (l_x + l_x + 1) contents_a2in1). lia.
 rewrite Zlength_sublist by lia. lia. apply Forall_sublist. apply Forall_Znth. rewrite H25. assumption.
 move H28 at bottom. move H29 at bottom.
  assert (Zlength (Znth (l_x + l_x + 1) contents_a2in1) = 10). {
  specialize H30 with (l_x + l_x + 1). rewrite H30 by lia. reflexivity.
 }
 rewrite app_assoc. rewrite concat_app. rewrite sublist0_app1.
 2:{
   rewrite concat_app. simpl. rewrite app_nil_r. rewrite !Zlength_app. 
   rewrite Zlength_cons. rewrite !Zlength_sublist by lia. replace (r_j1 - 0 + Z.succ (10 - (r_j1 + 1))) with 10 by lia.
   rewrite Zlength_concat' with (l_x + l_x + 1) 10 (sublist 0 (l_x + l_x + 1) contents_a2in1).
   lia. rewrite Zlength_sublist by lia. lia. apply Forall_sublist. apply Forall_Znth.
   rewrite H25. assumption.
 }
 rewrite concat_app. rewrite sublist_split with 0 ((l_x + l_x + 1) * 10 + r_j1) ((l_x + l_x + 1) * 10 + (r_j1 + 1)) (concat (sublist 0 (l_x + l_x + 1) contents_a2in1) ++
 concat[sublist 0 r_j1 (Znth (l_x + l_x + 1) contents_a2in1) ++ [Znth ((l_x + l_x + 1) * 10 + r_j1) contents_f] ++
    sublist (r_j1 + 1) 10 (Znth (l_x + l_x + 1) contents_a2in1)]). 
 rewrite sublist_split with 0 ((l_x + l_x + 1) * 10 + r_j1) ((l_x + l_x + 1) * 10 + (r_j1 + 1)) contents_f by lia.
 apply Forall2_app. simpl. rewrite app_nil_r. rewrite app_assoc. rewrite sublist0_app1.
 rewrite <- sublist_same with 0 10 contents_a2in1 in H29 by lia.
 rewrite sublist_split with 0 (l_x + l_x + 1) 10 contents_a2in1 in H29 by lia. 
 rewrite sublist_split with (l_x + l_x + 1) (l_x + l_x + 1 + 1) 10 contents_a2in1 in H29 by lia.  
 rewrite sublist_len_1 in H29. rewrite app_assoc in H29. rewrite concat_app in H29.
 rewrite sublist0_app1 in H29. rewrite concat_app in H29. simpl in H29. rewrite app_nil_r in H29. 
 rewrite <- sublist_same with 0 10 (Znth (l_x + l_x + 1) contents_a2in1) in H29 by lia. rewrite sublist_split with 0 r_j1 10 (Znth (l_x + l_x + 1) contents_a2in1) in H29 by lia.
 rewrite app_assoc in H29. rewrite sublist0_app1 in H29. assumption.
 rewrite Zlength_app. rewrite Zlength_concat' with (l_x + l_x + 1) 10 (sublist 0 (l_x + l_x + 1) contents_a2in1).
 rewrite Zlength_sublist by lia. lia. rewrite Zlength_sublist by lia. lia.
 apply Forall_sublist. apply Forall_Znth. rewrite H25. assumption. rewrite concat_app.
 simpl. rewrite app_nil_r. rewrite Zlength_app. rewrite Zlength_concat' with (l_x + l_x + 1) 10 (sublist 0 (l_x + l_x + 1) contents_a2in1).
 lia. rewrite Zlength_sublist by lia. lia. apply Forall_sublist. apply Forall_Znth. rewrite H25.
 assumption. lia. rewrite Zlength_app. rewrite Zlength_concat' with (l_x + l_x + 1) 10 (sublist 0 (l_x + l_x + 1) contents_a2in1).
 rewrite Zlength_sublist by lia. lia. rewrite Zlength_sublist by lia. lia. 
 apply Forall_sublist. apply Forall_Znth. rewrite H25. assumption.
 assert (Zlength (Znth (l_x + l_x + 1) contents_a2in1) = 10). {
  specialize H30 with (l_x + l_x + 1). rewrite H30 by lia. reflexivity.
 }
 replace ((l_x + l_x + 1) * 10 + (r_j1 + 1)) with ((l_x + l_x + 1) * 10 + r_j1 + 1) by lia.
 rewrite !sublist_len_1. simpl. rewrite app_nil_r. rewrite app_assoc. 
 assert (Zlength (concat (sublist 0 (l_x + l_x + 1) contents_a2in1) ++ sublist 0 r_j1
    (Znth (l_x + l_x + 1) contents_a2in1)) = (l_x + l_x + 1)*10 + r_j1). {
      rewrite Zlength_app. rewrite Zlength_concat' with (l_x + l_x + 1) 10 (sublist 0 (l_x + l_x + 1) contents_a2in1).
      rewrite Zlength_sublist by lia. lia. rewrite Zlength_sublist by lia. lia.
      apply Forall_sublist. apply Forall_Znth. rewrite H25. assumption.
    } 
 rewrite app_Znth2. rewrite H42. replace ((l_x + l_x + 1) * 10 + r_j1 - ((l_x + l_x + 1) * 10 + r_j1)) with 0 by lia.
 rewrite Znth_0_cons. apply Forall2_cons. reflexivity. list_solve. rewrite H42. lia.
 lia. simpl. rewrite app_nil_r. rewrite !Zlength_app. rewrite Zlength_cons.
 rewrite !Zlength_sublist by lia. replace (r_j1 - 0 + Z.succ (10 - (r_j1 + 1))) with 10 by lia.
 rewrite Zlength_concat' with (l_x + l_x + 1) 10 (sublist 0 (l_x + l_x + 1) contents_a2in1).
 lia. rewrite Zlength_sublist by lia. lia. apply Forall_sublist. apply Forall_Znth. rewrite H25. assumption.
 lia. simpl. rewrite app_nil_r. rewrite !Zlength_app. rewrite !Zlength_sublist by lia. rewrite Zlength_cons.
 rewrite Zlength_sublist by lia. 
 replace (r_j1 - 0 + Z.succ (10 - (r_j1 + 1))) with 10 by lia.
 rewrite Zlength_concat' with (l_x + l_x + 1) 10 (sublist 0 (l_x + l_x + 1) contents_a2in1).
 lia. rewrite Zlength_sublist by lia. lia. apply Forall_sublist. apply Forall_Znth. rewrite H25. assumption.
 rewrite !Znth_map. rewrite !upd_Znth_map. apply derives_refl'. f_equal. f_equal. f_equal.
 pattern (upd_Znth r_j1 (Znth (l_x + l_x + 1) contents_a2in1)
 (Znth ((l_x + l_x + 1) * 10 + r_j1) contents_f)) at 1. rewrite upd_Znth_unfold.
 assert (Zlength (Znth (l_x + l_x + 1) contents_a2in1) = 10). {
  specialize H30 with (l_x + l_x + 1). rewrite H30 by lia. reflexivity.
 }
 rewrite H5. rewrite <- sublist_same with 0 10 contents_a2in1 by lia. 
 rewrite sublist_split with 0 (l_x + l_x + 1) 10 contents_a2in1 by lia.
 rewrite upd_Znth_app2. rewrite Zlength_sublist by lia. simpl.
 replace (l_x + l_x + 1 - (l_x + l_x + 1 - 0)) with 0 by lia. 
 rewrite sublist_split with  (l_x + l_x + 1) (l_x + l_x + 1 + 1) 10 contents_a2in1.
 rewrite upd_Znth_app1. rewrite sublist_len_1. rewrite upd_Znth_unfold. simpl.
 rewrite sublist0_app1. rewrite sublist_prefix. 
 replace (Z.min (l_x + l_x + 1) (l_x + l_x + 1)) with (l_x + l_x + 1) by lia.
 f_equal. try list_solve. rewrite Zlength_sublist by lia. lia. rewrite Zlength_cons.
 rewrite Zlength_nil. lia. lia. rewrite Zlength_sublist by lia. lia. lia. lia.
 rewrite !Zlength_sublist by lia. lia. 
 assert (Zlength (Znth (l_x + l_x + 1) contents_a2in1) = 10). {
  specialize H30 with (l_x + l_x + 1). rewrite H30 by lia. reflexivity.
 }
 lia. lia. rewrite !Zlength_map. lia.
 forward.
 Exists (l_x + 1). Exists (r_i + 2). Exists contents_a1in1. Exists contents_a2in1. entailer!.
 split. move H29 at bottom. assert (r_j1 = 10) by lia. rewrite H5 in H29.
 replace ((l_x + l_x + 2) * 10) with ((l_x + l_x + 1) * 10 + 10) by lia.
 assumption. f_equal. f_equal. lia. forward.
 Exists (l_x + 1). Exists (r_i + 1). Exists contents_a1in. Exists contents_a2in. entailer!.
 (*last running loop*)
 Intros l_x r_i contents_a1o contents_a2o. 
 assert_PROP (Zlength contents_a1o = 100). {
  entailer!. rewrite <- H12. rewrite !Zlength_map. reflexivity.
 }
 assert_PROP (Zlength contents_a2o = 10). {
  entailer!. rewrite <- H16. rewrite !Zlength_map. reflexivity.
 }
 assert_PROP (Zlength (concat contents_a2o) = 100). {
  entailer!. rewrite Zlength_concat' with 10 10 contents_a2o.
  lia. lia. apply Forall_forall_Znth. intros. 
  rewrite Forall_forall in H18.
  specialize (H18 (map Vint (map Int.repr (Znth i contents_a2o)))).
  spec H18. apply in_map_iff.
  exists (map Int.repr (Znth i contents_a2o)). split; auto. 
  apply in_map. apply Znth_In. list_solve.
  simplify_value_fits in H18. destruct H18. list_solve.
 }
 rewrite H7 in H10.
 replace (10 * 10) with 100 in H10 by lia. rewrite !sublist_same in H10 by lia.
 forward_loop 
 (
   EX l_x:Z, EX contents_a1o1: list Z, 
    PROP 
    (
      5 <= l_x <= 100; Zlength contents_a1o1 = 100;
      Forall2 eq (sublist 0 l_x contents_a1o1) (sublist 0 l_x (concat contents_a2o));
      Forall2 eq (sublist 0 l_x contents_a1o1) (sublist 0 l_x contents_f)
      (*Forall2 eq (concat contents_a2o) contents_f*)
    )
   LOCAL 
   (
      temp _l_x (Vint (Int.repr l_x)); 
      temp _r_i (Vint (Int.repr r_i)); 
      temp _a_1 a_1; temp _a_2 a_2; temp _f f
   )
   SEP 
   (
      data_at sh1 (tarray tuint 100) (map Vint (map Int.repr contents_a1o1)) a_1;
      data_at sh2 (tarray (tarray tuint 10) 10) (map (map Vint)(map (map Int.repr) contents_a2o)) a_2;
      data_at shf (tarray tuint 100) (map Vint (map Int.repr contents_f)) f

   ))%assert
   break: 
   (
    EX l_x:Z, EX contents_a1o1: list Z,
    PROP 
    (
      0 <= l_x <= 100; l_x = 100; Zlength contents_a1o1 = 100;
      Forall2 eq (sublist 0 l_x contents_a1o1) (sublist 0 l_x (concat contents_a2o));
      Forall2 eq (sublist 0 l_x contents_a1o1) (sublist 0 l_x contents_f)
      (*Forall2 eq (sublist 0 (r_i * 10) (concat contents_a2o)) (sublist 0 (r_i * 10) contents_f)*)
    )
   LOCAL 
   (
      temp _l_x (Vint (Int.repr l_x)); 
      temp _r_i (Vint (Int.repr r_i)); 
      temp _a_1 a_1; temp _a_2 a_2; temp _f f
   )
   SEP 
   (
      data_at sh1 (tarray tuint 100) (map Vint (map Int.repr contents_a1o1)) a_1;
      data_at sh2 (tarray (tarray tuint 10) 10) (map (map Vint)(map (map Int.repr) contents_a2o)) a_2;
      data_at shf (tarray tuint 100) (map Vint (map Int.repr contents_f)) f

   )
  )%assert.
  Exists l_x. Exists contents_a1o. entailer!.
  Intros l_x0 contents_a1o1. forward_if. forward.
  Exists l_x0. Exists contents_a1o1. entailer!.
  forward_if. rewrite H7 in H19. inversion H19.
  fastforward.
  (*next step*)
  Exists (l_x0 + 1). Exists (sublist 0 l_x0 contents_a1o1 ++ [Znth l_x0 contents_f] ++ sublist (l_x0 + 1) 100 contents_a1o1).
  entailer!. split. rewrite !Zlength_app. rewrite Zlength_cons. rewrite Zlength_nil. rewrite !Zlength_sublist by lia. lia. split.
  move H16 at bottom. rewrite sublist_split with 0 l_x0 (l_x0 + 1) (concat contents_a2o) by lia.
  replace (sublist 0 (l_x0 + 1)
  (sublist 0 l_x0 contents_a1o1 ++ [Znth l_x0 contents_f] ++
   sublist (l_x0 + 1) 100 contents_a1o1)) with (sublist 0 l_x0 contents_a1o1 ++ [Znth l_x0 contents_f]) by list_solve.
  apply Forall2_app. assumption. move H10 at bottom. rewrite sublist_len_1 by lia.
  eapply Forall2_Znth with (i := l_x0) in H10. rewrite H10. apply Forall2_cons. reflexivity. list_solve. lia.
  replace (sublist 0 (l_x0 + 1)
  (sublist 0 l_x0 contents_a1o1 ++ [Znth l_x0 contents_f] ++
   sublist (l_x0 + 1) 100 contents_a1o1)) with (sublist 0 l_x0 contents_a1o1 ++ [Znth l_x0 contents_f]) by list_solve.
  move H16 at bottom. rewrite sublist_split with 0 l_x0 (l_x0 + 1) contents_f by lia. 
  rewrite sublist_len_1 by lia. apply Forall2_app. assumption. apply Forall2_cons. reflexivity. list_solve.
  (*prove update entailment*)
  rewrite !upd_Znth_map. apply derives_refl'. f_equal. f_equal. f_equal.
  rewrite <- H15. rewrite <- upd_Znth_unfold by lia. reflexivity.
  Intros l_x0 contents_a1o1. rewrite H15 in H17 ,H18. rewrite !sublist_same in H17 by lia.
  rewrite !sublist_same in H18 by lia.
  forward_loop 
  (
    PROP 
    ()
   LOCAL 
   (
      temp _l_x (Vint (Int.repr l_x0)); 
      temp _r_i (Vint (Int.repr r_i)); 
      temp _a_1 a_1; temp _a_2 a_2; temp _f f
   )
   SEP 
   (
      data_at sh1 (tarray tuint 100) (map Vint (map Int.repr contents_a1o1)) a_1;
      data_at sh2 (tarray (tarray tuint 10) 10) (map (map Vint)(map (map Int.repr) contents_a2o)) a_2;
      data_at shf (tarray tuint 100) (map Vint (map Int.repr contents_f)) f

   ))%assert
   break: 
   (
    PROP ()
   LOCAL 
   (
      temp _l_x (Vint (Int.repr l_x0)); 
      temp _r_i (Vint (Int.repr r_i)); 
      temp _a_1 a_1; temp _a_2 a_2; temp _f f
   )
   SEP 
   (
      data_at sh1 (tarray tuint 100) (map Vint (map Int.repr contents_a1o1)) a_1;
      data_at sh2 (tarray (tarray tuint 10) 10) (map (map Vint)(map (map Int.repr) contents_a2o)) a_2;
      data_at shf (tarray tuint 100) (map Vint (map Int.repr contents_f)) f

   )
  )%assert.
  entailer!. forward_if. rewrite H15 in H19. inversion H19.
  forward_if. forward. entailer!. rewrite H7 in H20. inversion H20.
  Exists contents_a1o1. Exists contents_a2o. entailer!.
Qed.


