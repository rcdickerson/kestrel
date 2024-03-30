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
  contents_lai : list Z, contents_rai : list Z, N : Z
  PRE [tptr tuint, tptr tuint, tuint]  
    (*ensure variables left and right are equal*)
    PROP (
    writable_share sh1; writable_share sh2;
    Zlength contents_lai = Z.add N 1; Zlength contents_rai = Z.add N 1;
    Forall (fun x => 0 <= x <= Int.max_unsigned) contents_lai;
    Forall (fun x => 0 <= x <= Int.max_unsigned) contents_rai;
    2 <= Z.add N 1 <= Int.max_unsigned; Forall2 eq contents_lai contents_rai)
  PARAMS (l_a;r_a; Vint (Int.repr N))
    SEP (data_at sh1 (tarray tuint (Z.add N 1)) (map Vint (map Int.repr contents_lai)) l_a;
    data_at sh2 (tarray tuint (Z.add N 1)) (map Vint (map Int.repr contents_rai)) r_a)
  POST [ tvoid ]
    EX contents_lao:list Z, EX contents_rao :list Z, 
    PROP (Forall2 eq contents_lao contents_rao)
    RETURN () (*void*)
    SEP (data_at sh1 (tarray tuint (Z.add N 1)) (map Vint (map Int.repr contents_lao)) l_a;
    data_at sh2 (tarray tuint (Z.add N 1)) (map Vint (map Int.repr contents_rao)) r_a).


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
      (r_i <= N) -> Forall2 eq contents_lao contents_rao;
      (r_i = (Z.add N 1)) -> Forall2 eq (sublist 0 ri contents_lao) (sublist 0 ri contents_rao);
      (r_i = (Z.add N 1)) -> Forall2 eq (sublist (ri + 1) N contents_lao) (sublist (ri + 1) N contents_rao); 
      0 <= l_i <= (Z.add N 1); 0 <= r_i <= (Z.add N 1); l_i = r_i; 0 <= lmax <= Int.max_unsigned;
      0 <= rmax <= Int.max_unsigned; 0 <= li <= l_i; 0 <= ri <= r_i;  0 <= li <= N; 0 <= ri <= N; 
      (l_i > 0) -> lmax = rmax; li = ri; lmax = Znth li contents_lao; 
      (0 < r_i <= N) -> rmax = Znth ri contents_rao;
      (r_i = (Z.add N 1)) -> rmax = Znth N contents_rao;
      (r_i = (Z.add N 1)) -> (Znth ri contents_lao = Znth N contents_rao);
      (r_i = Z.add N 1) -> (Znth N contents_lao = Znth ri contents_rao)
    )
    LOCAL 
    (
      temp _r_i (Vint (Int.repr r_i)); 
      temp _rind (Vint (Int.repr ri)); 
      temp _r_max (Vint (Int.repr rmax));  
      temp _l_i (Vint (Int.repr l_i)); 
      temp _lind (Vint (Int.repr li)); 
      temp _l_max (Vint (Int.repr lmax));
      temp _N (Vint (Int.repr N)); 
      temp _l_a l_a; temp _r_a r_a
    )
    SEP 
    (
      data_at sh1 (tarray tuint (Z.add N 1)) (map Vint (map Int.repr contents_lao)) l_a;
      data_at sh2 (tarray tuint (Z.add N 1)) (map Vint (map Int.repr contents_rao)) r_a
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
     l_i = (Z.add N 1); r_i = (Z.add N 1); 
     Forall2 eq (sublist 0 ri contents_lao) (sublist 0 ri contents_rao);
     Forall2 eq (sublist (ri + 1) N contents_lao) (sublist (ri + 1) N contents_rao); 
     0 <= li <= l_i; 0 <= ri <= r_i; lmax = rmax; li = ri; 0 <= li <= N; 0 <= ri <= N; 
     0 <= lmax <= Int.max_unsigned; 0 <= rmax <= Int.max_unsigned;
     Znth ri contents_lao = Znth N contents_rao; Znth N contents_lao = Znth ri contents_rao; 
     lmax = Znth li contents_lao; rmax = Znth N contents_rao
   )
   LOCAL 
   (
     temp _r_i (Vint (Int.repr r_i)); 
     temp _rind (Vint (Int.repr ri)); 
     temp _r_max (Vint (Int.repr rmax));  
     temp _l_i (Vint (Int.repr l_i)); 
     temp _lind (Vint (Int.repr li)); 
     temp _l_max (Vint (Int.repr lmax)); 
     temp _N (Vint (Int.repr N)); 
     temp _l_a l_a; temp _r_a r_a
   )
   SEP 
   (
     data_at sh1 (tarray tuint (Z.add N 1)) (map Vint (map Int.repr contents_lao)) l_a;
     data_at sh2 (tarray tuint (Z.add N 1)) (map Vint (map Int.repr contents_rao)) r_a
   )
 )%assert.
 (*first existential - outermost if*)      
 Exists 0. Exists 0. Exists (Znth 0 contents_lai). Exists 0. 
 Exists 0. Exists 0. Exists contents_lai. Exists contents_rai. entailer!.
 rewrite Forall_forall in H1. apply H1. apply Znth_In. lia. 
 (*apply Forall2_Znth. assumption. lia.*) 
 Intros l_i r_i lmax rmax li ri contents_lao contents_rao. 
 assert_PROP (Zlength contents_lao = Z.add N 1). {
  entailer!. rewrite <- H27. do 2 rewrite Zlength_map. reflexivity.
 }
 assert_PROP (Zlength contents_rao = Z.add N 1). {
  entailer!. rewrite <- H31. do 2 rewrite Zlength_map. reflexivity.
 }
 forward_if. forward. 
 Exists l_i. Exists r_i. Exists lmax. Exists rmax. 
 Exists li. Exists ri. Exists contents_lao. Exists contents_rao. entailer!. split. 
 apply H8. lia. apply H9. lia. 
 forward_if. forward.
 Exists l_i. Exists r_i. Exists lmax. Exists rmax. 
 Exists li. Exists ri. Exists contents_lao. Exists contents_rao. entailer!.
 forward. apply semax_if_seq. forward_if. fastforward. apply semax_if_seq. forward_if. 
 fastforward. apply semax_if_seq. forward_if. fastforward. apply semax_if_seq. forward_if.
 fastforward. assert (N >= 1) by lia. rewrite H33 in H31. rewrite H31 in H34. contradiction. 
 fastforward. rewrite Int.unsigned_repr in H30. do 2 rewrite Int.unsigned_repr in H32.
 assert (r_i < N) by lia. Exists (l_i + 1) (r_i + 1) (Znth l_i contents_lao) (Znth r_i contents_rao) l_i r_i 
 contents_lao contents_rao. entailer!. rewrite Forall_forall in H6. apply H6. apply Znth_In. lia. 
 rewrite Forall_forall in H6. apply H6. apply Znth_In. lia. rewrite Forall_forall in H6. apply H6. apply Znth_In. lia. 
 rewrite Forall_forall in H5. apply H5. apply Znth_In. lia. apply semax_if_seq. forward_if. fastforward. 
 rewrite H33 in H31. assert (N >= 1) by lia. rewrite H31 in H34. contradiction. assert (r_i < N) by lia.
 fastforward. Exists (l_i + 1) (r_i + 1) (Znth l_i contents_lao) (Znth 0 contents_rao) l_i 0 contents_lao contents_rao.
 entailer!. split. intros. apply H7. lia. split. rewrite Forall_forall in H5. apply H5. apply Znth_In. lia. split.
 rewrite Forall_forall in H6. apply H6. apply Znth_In. lia. intros. assert (0 <= N) by lia. apply H7 in H20. 
 apply Forall2_Znth with (i := 0) in H20. assumption. lia. forward. apply semax_if_seq. forward_if.
 fastforward. apply semax_if_seq. forward_if. fastforward. 
 Exists (l_i + 1) (r_i + 1) (Znth l_i contents_lao) (Znth r_i contents_lao) l_i r_i contents_lao contents_rao.
 entailer!. split. intros. apply Forall2_sublist. apply H7. lia. lia. split. intros. do 2 rewrite sublist_nil_gen by lia.
 apply Forall2_nil. split.  rewrite Forall_forall in H5. apply H5. apply Znth_In. lia. split.
 rewrite Forall_forall in H5. apply H5. apply Znth_In. lia. assert (N <= N) by lia. 
 apply H7 in H12. apply Forall2_Znth with (i := N) in H12; try lia. rewrite H12. auto. 
 rewrite upd_Znth_twice. apply derives_refl'. f_equal. rewrite upd_Znth_map. f_equal. rewrite upd_Znth_map. f_equal. 
 list_solve. do 2 rewrite Zlength_map. lia.
 fastforward. Exists (l_i + 1) (r_i + 1) (Znth l_i contents_lao) (Znth r_i contents_rao) l_i r_i contents_lao contents_rao.  entailer!. 
 assert (0 < r_i < N) by lia. move H7 at bottom. assert (r_i <= N) by lia. apply H7 in H20. 
 split. intros. assumption. split. rewrite Forall_forall in H5. apply H5. apply Znth_In. lia. split. 
 rewrite Forall_forall in H6. apply H6. apply Znth_In. lia. intros.
 apply Forall2_Znth with (i := r_i) in H20; try lia. apply semax_if_seq. forward_if. fastforward. subst. assert (N > 0) by lia.
 apply H19 in H12. subst. destruct (ri =? N) eqn:Hrin. assert (ri = N) by lia. subst. rewrite Int.unsigned_repr in H30. 
 assert (Znth N contents_lao <? Znth N contents_lao = false) by lia. apply Zaux.Zlt_bool_true in H30. rewrite H12 in H30. 
 discriminate H30. rewrite Forall_forall in H5. apply H5. apply Znth_In. lia. assert (ri < N) by lia. assert (N <= N) by lia. apply H7 in H20.
 apply Forall2_Znth with (i := N) in H20. rewrite <- H20 in H32. contradiction. lia. forward. assert (0 < r_i < N) by lia.
 Exists (l_i + 1) (r_i + 1) (Znth l_i contents_lao) rmax l_i ri contents_lao contents_rao. entailer!. split. intros. apply H7. lia. split.
 rewrite Forall_forall in H5. apply H5. apply Znth_In. lia. assert (r_i > 0) by lia. apply H19 in H12. rewrite <- H12 in H32.
 assert (r_i <= N) by lia. apply H7 in H20. apply Forall2_Znth with (i := r_i) in H20. rewrite H20 in H30. contradiction. lia. fastforward.
 apply semax_if_seq. forward_if. fastforward. apply semax_if_seq. forward_if. fastforward. apply semax_if_seq. forward_if. fastforward.
 subst. rewrite !Int.unsigned_repr in H32. assert (Znth 0 contents_rao <? Znth 0 contents_rao = false) by lia. apply Zaux.Zlt_bool_true in H32.
 rewrite H12 in H32. discriminate H32. rewrite Forall_forall in H6. apply H6. apply Znth_In. lia. subst. rewrite !Int.unsigned_repr in H32. 
 assert (Znth 0 contents_rao <? Znth 0 contents_rao = false) by lia. apply Zaux.Zlt_bool_true in H32.
 rewrite H12 in H32. discriminate H32. rewrite Forall_forall in H6. apply H6. apply Znth_In. lia. subst. assert (ri = 0) by lia. subst. 
 apply semax_if_seq. forward_if. assert (N > 0) by lia. rewrite H12 in H20. apply Z.gt_lt in H20. assert (N <? N = false) by lia.
 apply Zaux.Zlt_bool_true in H20. rewrite H20 in H21. discriminate H21. forward.
 Exists 1 1 (Znth 0 contents_lao) (Znth 0 contents_rao) 0 0 contents_lao contents_rao.  entailer!.  assert (0 <= N) by lia.
 apply H7 in H36. split. intros. assumption. split. rewrite Forall_forall in H6. apply H6. apply Znth_In. lia. intros.
 apply Forall2_Znth with (i := 0) in H36. assumption. lia. forward. apply semax_if_seq. forward_if. assert (r_i > 0) by lia.
 assert (r_i <= N) by lia. rewrite H12 in H19. apply H19 in H33. subst. apply H7 in H34. apply Forall2_Znth with (i := r_i) in H34; subst.
 rewrite H34 in H30. contradiction. lia. apply semax_if_seq. forward_if. fastforward. subst. destruct (ri =? N) eqn:Hrn. assert (ri = N) by lia.
 subst. Exists (N + 1) (N + 1) (Znth N contents_lao) rmax N N contents_lao contents_rao. entailer!. split. intros. apply Forall2_sublist.
 apply H7. lia. lia. rewrite !sublist_nil_gen by lia. auto. apply derives_refl'. f_equal. rewrite upd_Znth_twice. rewrite !upd_Znth_map. f_equal.
 f_equal. list_solve. rewrite !Zlength_map. lia. assert (ri < N) by lia.
 Exists (N + 1) (N + 1) (Znth ri contents_lao) rmax ri ri contents_lao ((sublist 0 ri contents_rao) ++ [Znth N contents_rao] ++ (sublist(ri + 1) N contents_rao) ++ [Znth ri contents_rao]).
 entailer!. split. apply Forall_app. split. apply Forall_sublist. assumption. apply Forall_app. split. apply Forall_cons. 
 rewrite Forall_forall in H6. apply H6. apply Znth_In. lia. auto. apply Forall_app. split. apply Forall_sublist. assumption.
 apply Forall_cons. rewrite Forall_forall in H6. apply H6. apply Znth_In. lia.  auto. split. intros. rewrite app_assoc. rewrite sublist0_app1.
 rewrite sublist0_app1. replace (sublist 0 ri (sublist 0 ri contents_rao)) with (sublist 0 ri contents_rao) by list_solve. apply Forall2_sublist.
 apply H7. lia. lia. rewrite Zlength_sublist by lia. lia. rewrite Zlength_app. rewrite Zlength_sublist by lia. replace (Zlength [Znth N contents_rao]) with 1 by list_solve. lia. 
 split. intros. rewrite app_assoc. rewrite sublist_app2. rewrite !Zlength_app. rewrite !Zlength_sublist by lia. rewrite !Zlength_cons by lia. simpl. 
 replace (ri + 1 - (ri - 0 + 1)) with 0 by lia. replace (N - (ri - 0 + 1)) with (N - ri - 1) by lia. rewrite sublist0_app1. rewrite sublist_sublist by lia.
 replace (0 + (ri + 1)) with (ri + 1) by lia. replace (N - ri - 1 + (ri + 1)) with N by lia. apply Forall2_sublist. apply H7. lia. lia. 
 rewrite Zlength_sublist by lia. lia. rewrite Zlength_app. rewrite Zlength_sublist by lia. replace (Zlength [Znth N contents_rao]) with 1 by list_solve. lia.
 split. intros. rewrite app_assoc. rewrite Znth_app2 by list_solve. rewrite Zlength_app. rewrite Zlength_sublist by lia. 
 replace (Zlength [Znth N contents_rao]) with 1 by list_solve. replace (N - (ri - 0 + 1)) with (N - ri - 1) by lia.  rewrite Znth_app2 by list_solve. 
 rewrite Zlength_sublist by lia. replace (N - ri - 1 - (N - (ri + 1))) with 0 by lia. rewrite Znth_0_cons. apply H22. lia. assert (N <= N) by lia. apply H7 in H37.
 split; intros. rewrite app_assoc. rewrite Znth_app2 by list_solve. rewrite Zlength_app. rewrite Zlength_sublist by lia. 
 replace (Zlength [Znth N contents_rao]) with 1 by list_solve. replace (N - (ri - 0 + 1)) with (N - ri - 1) by lia.  rewrite Znth_app2 by list_solve. 
 rewrite Zlength_sublist by lia. replace (N - ri - 1 - (N - (ri + 1))) with 0 by lia. rewrite Znth_0_cons.  apply Forall2_Znth with (i := ri) in H37. assumption. lia. 
 rewrite app_assoc. rewrite Znth_app1 by list_solve. rewrite Znth_app2 by list_solve. rewrite Zlength_sublist by lia. replace (ri - (ri - 0)) with 0 by lia.
 rewrite Znth_0_cons. apply Forall2_Znth with (i := N) in H37. assumption. lia.  apply derives_refl'. f_equal. rewrite !upd_Znth_map. f_equal. f_equal. 
 list_solve. forward. Exists (l_i + 1) (r_i + 1) lmax rmax li ri contents_lao contents_rao. entailer!. apply H7. lia. 
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
     l_i = (Z.add N 1); r_i = (Z.add N 1); 
     Forall2 eq (sublist 0 ri contents_lao) (sublist 0 ri contents_rao);
     Forall2 eq (sublist (ri + 1) N contents_lao) (sublist (ri + 1) N contents_rao); 
     0 <= li <= l_i; 0 <= ri <= r_i; 0 <= li <= N; 0 <= ri <= N; lmax = rmax; li = ri;
     0 <= lmax <= Int.max_unsigned; 0 <= rmax <= Int.max_unsigned;
     Znth ri contents_lao = Znth N contents_rao; Znth N contents_lao = Znth ri contents_rao; 
     lmax = Znth li contents_lao; rmax = Znth N contents_rao
    )
    LOCAL 
    (
      temp _r_i (Vint (Int.repr r_i)); 
      temp _rind (Vint (Int.repr ri)); 
      temp _r_max (Vint (Int.repr rmax));  
      temp _l_i (Vint (Int.repr l_i)); 
      temp _lind (Vint (Int.repr li)); 
      temp _l_max (Vint (Int.repr lmax));
      temp _N (Vint (Int.repr N)); 
      temp _l_a l_a; temp _r_a r_a
    )
    SEP 
    (
      data_at sh1 (tarray tuint (Z.add N 1)) (map Vint (map Int.repr contents_lao)) l_a;
      data_at sh2 (tarray tuint (Z.add N 1)) (map Vint (map Int.repr contents_rao)) r_a
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
     l_i = (Z.add N 1); r_i = (Z.add N 1); 
     Forall2 eq (sublist 0 ri contents_lao) (sublist 0 ri contents_rao);
     Forall2 eq (sublist (ri + 1) N contents_lao) (sublist (ri + 1) N contents_rao); 
     0 <= li <= l_i; 0 <= ri <= r_i; lmax = rmax; li = ri; 0 <= li <= N; 0 <= ri <= N; 
     0 <= lmax <= Int.max_unsigned; 0 <= rmax <= Int.max_unsigned;
     Znth ri contents_lao = Znth N contents_rao; Znth N contents_lao = Znth ri contents_rao; 
     lmax = Znth li contents_lao; rmax = Znth N contents_rao
   )
   LOCAL 
   (
     temp _r_i (Vint (Int.repr r_i)); 
     temp _rind (Vint (Int.repr ri)); 
     temp _r_max (Vint (Int.repr rmax));  
     temp _l_i (Vint (Int.repr l_i)); 
     temp _lind (Vint (Int.repr li)); 
     temp _l_max (Vint (Int.repr lmax)); 
     temp _N (Vint (Int.repr N)); 
     temp _l_a l_a; temp _r_a r_a
   )
   SEP 
   (
     data_at sh1 (tarray tuint (Z.add N 1)) (map Vint (map Int.repr contents_lao)) l_a;
     data_at sh2 (tarray tuint (Z.add N 1)) (map Vint (map Int.repr contents_rao)) r_a
   )
 )%assert.
  Exists l_i. Exists r_i. Exists lmax. Exists rmax. Exists li. Exists ri. 
  Exists contents_lao. Exists contents_rao. entailer!.
  Intros l_i1 r_i1 lmax1 rmax1 li1 ri1 contents_la1 contents_ra1.
  forward_if. forward.
  Exists l_i1 r_i1 lmax1 rmax1 li1 ri1 contents_la1 contents_ra1. entailer!. rewrite <- H25 in H41. assert (l_i1 <? l_i1 = false) by lia.
  apply Zaux.Zlt_bool_true in H41. rewrite H41 in H42.  discriminate H42.
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
      l_i = (Z.add N 1); r_i = (Z.add N 1); 
      Forall2 eq (sublist 0 ri contents_lao) (sublist 0 ri contents_rao);
      Forall2 eq (sublist (ri + 1) N contents_lao) (sublist (ri + 1) N contents_rao); 
      0 <= li <= l_i; 0 <= ri <= r_i; lmax = rmax; li = ri; 0 <= li <= N; 0 <= ri <= N; 
      0 <= lmax <= Int.max_unsigned; 0 <= rmax <= Int.max_unsigned;
      Znth ri contents_lao = Znth N contents_rao; Znth N contents_lao = Znth ri contents_rao; 
      lmax = Znth li contents_lao; rmax = Znth N contents_rao
     )
     LOCAL 
     (
       temp _r_i (Vint (Int.repr r_i)); 
       temp _rind (Vint (Int.repr ri)); 
       temp _r_max (Vint (Int.repr rmax));  
       temp _l_i (Vint (Int.repr l_i)); 
       temp _lind (Vint (Int.repr li)); 
       temp _l_max (Vint (Int.repr lmax));
       temp _N (Vint (Int.repr N)); 
       temp _l_a l_a; temp _r_a r_a
     )
     SEP 
     (
       data_at sh1 (tarray tuint (Z.add N 1)) (map Vint (map Int.repr contents_lao)) l_a;
       data_at sh2 (tarray tuint (Z.add N 1)) (map Vint (map Int.repr contents_rao)) r_a
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
      l_i = (Z.add N 1); r_i = (Z.add N 1); 
      Forall2 eq (sublist 0 ri contents_lao) (sublist 0 ri contents_rao);
      Forall2 eq (sublist (ri + 1) N contents_lao) (sublist (ri + 1) N contents_rao); 
      0 <= li <= l_i; 0 <= ri <= r_i; lmax = rmax; li = ri; 0 <= li <= N; 0 <= ri <= N; 
      0 <= lmax <= Int.max_unsigned; 0 <= rmax <= Int.max_unsigned;
      Znth ri contents_lao = Znth N contents_rao; Znth N contents_lao = Znth ri contents_rao; 
      lmax = Znth li contents_lao; rmax = Znth N contents_rao
    )
    LOCAL 
    (
      temp _r_i (Vint (Int.repr r_i)); 
      temp _rind (Vint (Int.repr ri)); 
      temp _r_max (Vint (Int.repr rmax));  
      temp _l_i (Vint (Int.repr l_i)); 
      temp _lind (Vint (Int.repr li)); 
      temp _l_max (Vint (Int.repr lmax)); 
      temp _N (Vint (Int.repr N)); 
      temp _l_a l_a; temp _r_a r_a
    )
    SEP 
    (
      data_at sh1 (tarray tuint (Z.add N 1)) (map Vint (map Int.repr contents_lao)) l_a;
      data_at sh2 (tarray tuint (Z.add N 1)) (map Vint (map Int.repr contents_rao)) r_a
    )
  )%assert.
  Exists l_i1 r_i1 lmax1 rmax1 li1 ri1 contents_la1 contents_ra1. entailer!.
  Intros l_i2 r_i2 lmax2 rmax2 li2 ri2 contents_la2 contents_ra2.
  forward_if. forward.
  Exists l_i2 r_i2 lmax2 rmax2 li2 ri2 contents_la2 contents_ra2. entailer!. rewrite <- H44 in H59. assert (r_i2 <? r_i2 = false) by lia.
  apply Zaux.Zlt_bool_true in H59. rewrite H59 in H60. discriminate H60.
  Intros l_i2 r_i2 lmax2 rmax2 li2 ri2 contents_la2 contents_ra2. 
  assert_PROP (Zlength contents_la2 = (Z.add N 1)). {
    entailer!. rewrite <- H60. do 2 rewrite Zlength_map. reflexivity.
   }
   assert_PROP (Zlength contents_ra2 = (Z.add N 1)). {
    entailer!. rewrite <- H64. do 2 rewrite Zlength_map. reflexivity.
   }
  fastforward. destruct (ri2 <? N) eqn:Hri2. assert (ri2 < N) by lia.
  Exists (sublist 0 li2 contents_la2 ++ [Znth N contents_la2] ++ (sublist (li2 + 1) N contents_la2) ++ [lmax2]) contents_ra2.
  entailer!. rewrite <- sublist_same with 0 (N + 1) contents_ra2. 
  rewrite sublist_split with 0 ri2 (N + 1) contents_ra2 by list_solve. rewrite sublist_split with ri2 (ri2 + 1) (N + 1) contents_ra2 by list_solve.
  rewrite sublist_len_1 by lia. rewrite sublist_split with (ri2 + 1) N (N + 1) contents_ra2 by list_solve. rewrite sublist_len_1 by lia. rewrite <- H55, <- H56.
  apply Forall2_app. assumption. apply Forall2_app. apply Forall2_cons; auto. apply Forall2_app. assumption. apply Forall2_cons; auto. lia.  lia. apply derives_refl'.
  try f_equal. rewrite !upd_Znth_map. f_equal. f_equal. list_solve.
  assert(ri2 = N) by lia. subst. Exists contents_la2 contents_ra2. entailer!. rewrite <- sublist_same with 0 (N + 1) contents_la2 by list_solve. 
  rewrite <- sublist_same with 0 (N + 1) contents_ra2 by list_solve. rewrite sublist_split with 0 N (N + 1) contents_la2 by list_solve.
  rewrite sublist_split with 0 N (N + 1) contents_ra2 by list_solve. apply Forall2_app. assumption. rewrite !sublist_len_1 by list_solve. 
  apply Forall2_cons; auto. apply derives_refl'. f_equal. rewrite !upd_Znth_map. f_equal. f_equal. list_solve.
Qed.


