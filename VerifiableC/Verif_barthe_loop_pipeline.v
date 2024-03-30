(* ================================================================= *)
(* antonoupoulous_sa_simple.c - no array for this*)

Require VC.Preface. 
Require Import Setoid.
From Coq Require Import ZArith.Int.
Require Import VST.floyd.proofauto.
Require Import Coq.Classes.RelationClasses.

Require Import VC.barthe_loop_pipeline.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

(*API spec => verifyfunc spec; left and right are equal *)
Definition verifyfunc_spec : ident * funspec :=
DECLARE _verifyfunc
  WITH l_a : val, l_b : val, l_c : val,
  r_a : val, r_b : val, r_c : val, 
  shla : share, shlb : share, shlc : share, shra: share, shrb: share, shrc: share,
  contents_lai : list Z, contents_lbi : list Z, contents_lci : list Z,
  contents_rai : list Z, contents_rbi : list Z, contents_rci : list Z, N : Z
  PRE [tptr tuint, tptr tuint, tptr tuint,tptr tuint, tptr tuint, tptr tuint, tuint]
    (*ensure variables left and right are equal*)
    PROP 
    (
      writable_share shla; writable_share shlb; writable_share shlc; 
      writable_share shra; writable_share shrb; writable_share shrc; 
      Zlength contents_lai = N; Zlength contents_lbi = N; Zlength contents_lci = N;
      Zlength contents_rai = N; Zlength contents_rbi = N; Zlength contents_rci = N;
      2 <= N <= Int.max_unsigned;
      Forall2 (fun x y => x = y) contents_lai contents_rai;
      Forall2 (fun x y => x = y) contents_lbi contents_rbi;
      Forall2 (fun x y => x = y) contents_lci contents_rci
    )
  PARAMS (l_a; l_b; l_c; r_a; r_b; r_c; Vint (Int.repr N))
    SEP 
    (
      data_at shla (tarray tuint N) (map Vint (map Int.repr contents_lai)) l_a;
      data_at shlb (tarray tuint N) (map Vint (map Int.repr contents_lbi)) l_b;
      data_at shlc (tarray tuint N) (map Vint (map Int.repr contents_lci)) l_c;
      data_at shra (tarray tuint N) (map Vint (map Int.repr contents_rai)) r_a;
      data_at shrb (tarray tuint N) (map Vint (map Int.repr contents_rbi)) r_b;
      data_at shrc (tarray tuint N) (map Vint (map Int.repr contents_rci)) r_c
    )
  POST [ tvoid ]
    EX contents_lao:list Z, EX contents_lbo: list Z, EX contents_lco: list Z,
    EX contents_rao:list Z, EX contents_rbo: list Z, EX contents_rco: list Z,
    PROP 
    ( 
      Forall2 (fun x y => x = y) contents_lao contents_rao;
      Forall2 (fun x y => x = y) contents_lbo contents_rbo;
      Forall2 (fun x y => x = y) contents_lco contents_rco
    )
    RETURN () (*void*)
    SEP 
    (
      data_at shla (tarray tuint N) (map Vint (map Int.repr contents_lao)) l_a;
      data_at shlb (tarray tuint N) (map Vint (map Int.repr contents_lbo)) l_b;
      data_at shlc (tarray tuint N) (map Vint (map Int.repr contents_lco)) l_c;
      data_at shra (tarray tuint N) (map Vint (map Int.repr contents_rao)) r_a;
      data_at shrb (tarray tuint N) (map Vint (map Int.repr contents_rbo)) r_b;
      data_at shrc (tarray tuint N) (map Vint (map Int.repr contents_rco)) r_c
    ).

(*Pack APIs together*)
Definition Gprog := [verifyfunc_spec].

(*verify fun_spec - from here*)
Lemma body_verifyfunc: semax_body Vprog Gprog f_verifyfunc verifyfunc_spec.
Proof. 
 start_function. fastforward; try list_solve. 
 forward_if (
  PROP()
  LOCAL (
    temp _l_i (Vint (Int.repr 1));
    temp _r_j (Vint (Int.repr 0)); 
    temp _l_a l_a; temp _l_b l_b; temp _l_c l_c;
    temp _r_a r_a; temp _r_b r_b; temp _r_c r_c; temp _N (Vint (Int.repr N))
  )
   SEP (
    data_at shla (tarray tuint N) (map Vint (map Int.repr ([Znth 0 contents_lai + 1] ++ (sublist 1 N contents_lai)))) l_a;
    data_at shlb (tarray tuint N) (map Vint (map Int.repr ([Znth 0 contents_lbi + Znth 0 contents_lai + 1] ++ (sublist 1 N contents_lbi)))) l_b;
    data_at shlc (tarray tuint N) (map Vint (map Int.repr ([Znth 0 contents_lci + Znth 0 contents_lbi + Znth 0 contents_lai + 1] ++ (sublist 1 N contents_lci)))) l_c;
    data_at shra (tarray tuint N) (map Vint (map Int.repr ([Znth 0 contents_rai + 1] ++ [Znth 1 contents_rai + 1] ++ (sublist 2 N contents_rai)))) r_a;
    data_at shrb (tarray tuint N) (map Vint (map Int.repr ([Znth 0 contents_rbi + Znth 0 contents_rai + 1] ++ (sublist 1 N contents_rbi)))) r_b;
    data_at shrc (tarray tuint N) (map Vint (map Int.repr contents_rci)) r_c
  )
 ).
 fastforward; try list_solve. entailer!. repeat apply sepcon_derives. 
 (*la*) 
  apply derives_refl'. f_equal. rewrite !upd_Znth_map. f_equal. f_equal. list_solve.
  (*lb*)
  apply derives_refl'. f_equal.
  rewrite !sem_cast_i2i_correct_range. 
  2:{ simpl. list_simplify. }
  rewrite force_val_e. unfold both_int. simpl.
  rewrite !sem_cast_i2i_correct_range.
  2:{ simpl. list_simplify. }
  simpl. try list_solve. list_simplify. rewrite force_val_e. 
  rewrite add_repr. rewrite Z.add_assoc. reflexivity. 
  (*for lc*)
  apply derives_refl'. f_equal. rewrite !sem_cast_i2i_correct_range. 
  2:{ simpl. list_simplify. }
  rewrite force_val_e. unfold both_int. simpl. 
  rewrite !sem_cast_i2i_correct_range.
  2:{ simpl. list_simplify. }
  simpl. try list_solve. list_simplify. rewrite !force_val_e.
  rewrite !add_repr. rewrite !Z.add_assoc. reflexivity. list_solve. list_solve. 
  (*for ra*)
  apply derives_refl'. f_equal. rewrite !sem_cast_i2i_correct_range. 
  2:{ simpl. list_simplify. }
  rewrite !force_val_e; try list_solve. f_equal. unfold both_int. simpl. rewrite !upd_Znth_map. list_simplify.
  rewrite !add_repr. reflexivity. 
  (*for shrb*)
  apply derives_refl'. f_equal.
  rewrite !sem_cast_i2i_correct_range. 
  2:{ simpl. list_simplify. }
  rewrite force_val_e. unfold both_int. simpl.
  rewrite !sem_cast_i2i_correct_range.
  2:{ simpl. list_simplify. }
  simpl. try list_solve. list_simplify. rewrite force_val_e. 
  rewrite !add_repr. rewrite Z.add_assoc. reflexivity. apply Z.ge_le in H9. destruct H5. apply Z.le_ge in H5. Search (_ <= _).
  Check Z.le_lt_trans. apply Z.le_lt_trans with N 0 2 in H9. contradiction. lia.  
  (*second if*)
  forward_if (
  PROP()
  LOCAL (
    temp _l_i (Vint (Int.repr 2));
    temp _r_j (Vint (Int.repr 0)); 
    temp _l_a l_a; temp _l_b l_b; temp _l_c l_c;
    temp _r_a r_a; temp _r_b r_b; temp _r_c r_c; temp _N (Vint (Int.repr N))
  )
   SEP (
    data_at shla (tarray tuint N) (map Vint (map Int.repr ([Znth 0 contents_lai + 1] ++ [Znth 1 contents_lai + 1] ++ (sublist 2 N contents_lai)))) l_a;
    data_at shlb (tarray tuint N) (map Vint (map Int.repr ([Znth 0 contents_lbi + Znth 0 contents_lai + 1] ++ [Znth 1 contents_lbi + Znth 1 contents_lai + 1] ++ (sublist 2 N contents_lbi)))) l_b;
    data_at shlc (tarray tuint N) (map Vint (map Int.repr ([Znth 0 contents_lci + Znth 0 contents_lbi + Znth 0 contents_lai + 1] ++ [Znth 1 contents_lci + Znth 1 contents_lbi + Znth 1 contents_lai + 1] ++ (sublist 2 N contents_lci)))) l_c;
    data_at shra (tarray tuint N) (map Vint (map Int.repr ([Znth 0 contents_rai + 1] ++ [Znth 1 contents_rai + 1] ++ (sublist 2 N contents_rai)))) r_a;
    data_at shrb (tarray tuint N) (map Vint (map Int.repr ([Znth 0 contents_rbi + Znth 0 contents_rai + 1] ++ (sublist 1 N contents_rbi)))) r_b;
    data_at shrc (tarray tuint N) (map Vint (map Int.repr contents_rci)) r_c
  )
 ).
 fastforward; try list_solve. entailer!. repeat apply sepcon_derives. 
 (*la*) 
  apply derives_refl'. f_equal. rewrite !upd_Znth_map. f_equal. f_equal. list_solve.
  (*lb*)
  apply derives_refl'. f_equal.
  rewrite !sem_cast_i2i_correct_range. 
  2:{ simpl. list_simplify. }
  rewrite force_val_e. unfold both_int. simpl.
  rewrite !sem_cast_i2i_correct_range.
  2:{ simpl. list_simplify. }
  simpl. try list_solve. list_simplify. rewrite force_val_e. 
  rewrite add_repr. rewrite Z.add_assoc. reflexivity. 
  (*for lc*)
  apply derives_refl'. f_equal. rewrite !sem_cast_i2i_correct_range. 
  2:{ simpl. list_simplify. }
  rewrite force_val_e. unfold both_int. simpl. 
  rewrite !sem_cast_i2i_correct_range.
  2:{ simpl. list_simplify. }
  simpl. try list_solve. list_simplify. rewrite !force_val_e.
  rewrite !add_repr. rewrite !Z.add_assoc. reflexivity. list_solve. list_solve. 
  apply Z.ge_le in H9. destruct H5. apply Z.le_ge in H5. apply Z.le_lt_trans with N 1 2 in H9. contradiction. lia.
 forward_loop 
 (
  EX l_i:Z, EX r_j:Z, 
  EX contents_lao :list Z, EX contents_lbo:list Z, EX contents_lco:list Z,
  EX contents_rao :list Z, EX contents_rbo:list Z, EX contents_rco:list Z,
    PROP
    (
      0 <= l_i <= N; 0 <= r_j <= (N - 2);  l_i = Z.add r_j 2;
      Zlength contents_lao = N; Zlength contents_lbo = N; Zlength contents_lco = N;
      Zlength contents_rao = N; Zlength contents_rbo = N; Zlength contents_rco = N;
      (*for a*)
      Forall2 eq contents_lao contents_rao;
      (*for b*)
      Forall2 eq (sublist 0 (Z.add r_j 1) contents_lbo)(sublist 0 (Z.add r_j 1) contents_rbo);
      Znth (Z.add r_j 1) contents_lbo = Z.add (Znth (Z.add r_j 1) contents_rbo)  (Znth (Z.add r_j 1) contents_lao);
      Forall2 eq (sublist (Z.add r_j 2) N contents_lbo)(sublist (Z.add r_j 2) N contents_rbo);
      (*for c*)
      Forall2 eq (sublist 0 r_j contents_lco)(sublist 0 r_j contents_rco);
      Znth r_j contents_lco = Z.add (Znth r_j contents_rco) (Znth r_j contents_lbo);
      Znth (Z.add r_j 1) contents_lco = Z.add (Znth (Z.add r_j 1) contents_rco)  (Znth (Z.add r_j 1) contents_lbo);
      Forall2 eq (sublist (Z.add r_j 2) N contents_lco)(sublist (Z.add r_j 2) N contents_rco)
     
      
    )
    LOCAL
    (
      temp _l_i (Vint (Int.repr l_i));
      temp _r_j (Vint (Int.repr r_j)); 
      temp _l_a l_a; temp _l_b l_b; temp _l_c l_c;
      temp _r_a r_a; temp _r_b r_b; temp _r_c r_c; temp _N (Vint (Int.repr N))
      
    )
    SEP
    (
      data_at shla (tarray tuint N) (map Vint (map Int.repr contents_lao)) l_a;
      data_at shlb (tarray tuint N) (map Vint (map Int.repr contents_lbo)) l_b;
      data_at shlc (tarray tuint N) (map Vint (map Int.repr contents_lco)) l_c;
      data_at shra (tarray tuint N) (map Vint (map Int.repr contents_rao)) r_a;
      data_at shrb (tarray tuint N) (map Vint (map Int.repr contents_rbo)) r_b;
      data_at shrc (tarray tuint N) (map Vint (map Int.repr contents_rco)) r_c
    )
  )%assert
  break:
  (
    EX l_i:Z, EX r_j:Z, 
    EX contents_lao :list Z, EX contents_lbo:list Z, EX contents_lco:list Z,
    EX contents_rao :list Z, EX contents_rbo:list Z, EX contents_rco:list Z,
    PROP
    (
      l_i = N; r_j = Z.sub N 2;
      Zlength contents_lao = N; Zlength contents_lbo = N; Zlength contents_lco = N;
      Zlength contents_rao = N; Zlength contents_rbo = N; Zlength contents_rco = N;
      (*for a*)
      Forall2 eq contents_lao contents_rao;
      (*for b*)
      Forall2 eq (sublist 0 (Z.add r_j 1) contents_lbo)(sublist 0 (Z.add r_j 1) contents_rbo);
      Znth (Z.add r_j 1) contents_lbo = Z.add (Znth (Z.add r_j 1) contents_rbo)  (Znth (Z.add r_j 1) contents_lao);
      Forall2 eq (sublist (Z.add r_j 2) N contents_lbo)(sublist (Z.add r_j 2) N contents_rbo);
      (*for c*)
      Forall2 eq (sublist 0 r_j contents_lco)(sublist 0 r_j contents_rco);
      Znth r_j contents_lco = Z.add (Znth r_j contents_rco) (Znth r_j contents_lbo);
      Znth (Z.add r_j 1) contents_lco = Z.add (Znth (Z.add r_j 1) contents_rco)  (Znth (Z.add r_j 1) contents_lbo);
      Forall2 eq (sublist (Z.add r_j 2) N contents_lco)(sublist (Z.add r_j 2) N contents_rco)

    )
    LOCAL
    (
      temp _l_i (Vint (Int.repr l_i));
      temp _r_j (Vint (Int.repr r_j)); 
      temp _l_a l_a; temp _l_b l_b; temp _l_c l_c;
      temp _r_a r_a; temp _r_b r_b; temp _r_c r_c; temp _N (Vint (Int.repr N))
    )
    SEP
    (
      data_at shla (tarray tuint N) (map Vint (map Int.repr contents_lao)) l_a;
      data_at shlb (tarray tuint N) (map Vint (map Int.repr contents_lbo)) l_b;
      data_at shlc (tarray tuint N) (map Vint (map Int.repr contents_lco)) l_c;
      data_at shra (tarray tuint N) (map Vint (map Int.repr contents_rao)) r_a;
      data_at shrb (tarray tuint N) (map Vint (map Int.repr contents_rbo)) r_b;
      data_at shrc (tarray tuint N) (map Vint (map Int.repr contents_rco)) r_c
    )
  )%assert.
  Exists 2  0. 
  Exists ([Znth 0 contents_lai + 1] ++ [Znth 1 contents_lai + 1] ++ (sublist 2 N contents_lai)). 
  Exists ([Znth 0 contents_lbi + Znth 0 contents_lai + 1] ++ [Znth 1 contents_lbi + Znth 1 contents_lai + 1] ++ (sublist 2 N contents_lbi)). 
  Exists ([Znth 0 contents_lci + Znth 0 contents_lbi + Znth 0 contents_lai + 1] ++ [Znth 1 contents_lci + Znth 1 contents_lbi + Znth 1 contents_lai + 1] ++ (sublist 2 N contents_lci)). 
  Exists ([Znth 0 contents_rai + 1] ++ [Znth 1 contents_rai + 1] ++ (sublist 2 N contents_rai)).
  Exists ([Znth 0 contents_rbi + Znth 0 contents_rai + 1] ++ (sublist 1 N contents_rbi)). Exists contents_rci.
  entailer!. 
  split. list_solve. split. list_solve.  split. list_solve. split. list_solve. split. list_solve. split.
  apply Forall2_app. apply Forall2_cons; auto. f_equal. move H6 at bottom.
  apply Forall2_Znth with (i := 0) in H6; try lia. apply Forall2_app. apply Forall2_cons; auto. f_equal. move H6 at bottom.
  apply Forall2_Znth with (i := 1) in H6; try lia. apply Forall2_sublist; try lia. assumption. split. replace (sublist 0 1
  ([Znth 0 contents_lbi + Znth 0 contents_lai + 1] ++ [Znth 1 contents_lbi + Znth 1 contents_lai + 1] ++ sublist 2 (Zlength contents_lai) contents_rbi)) with [Znth 0 contents_lbi + Znth 0 contents_lai + 1] by list_solve.
  replace (sublist 0 1 ([Znth 0 contents_rbi + Znth 0 contents_rai + 1] ++ sublist 1 (Zlength contents_lai) contents_rbi)) with [Znth 0 contents_rbi + Znth 0 contents_rai + 1] by list_solve. 
  apply Forall2_cons. f_equal. apply Forall2_Znth with (i := 0) in H6, H7; try lia. auto. 
  split. simpl. rewrite Znth_pos_cons by lia. replace (1 - 1) with 0 by lia. rewrite Znth_0_cons. rewrite Znth_pos_cons by lia. replace (1 - 1) with 0 by lia. 
  rewrite Znth_pos_cons by lia. replace (1 - 1) with 0 by lia.  rewrite Znth_0_cons. rewrite sublist_split with 1 2 (Zlength contents_lai) contents_rbi by lia. 
  rewrite sublist_len_1 by lia. simpl. rewrite Znth_0_cons. rewrite Z.add_assoc. f_equal. f_equal. apply Forall2_Znth with (i := 1) in H7; try lia. auto. 
  split. replace (sublist 2 (Zlength contents_lai) ([Znth 0 contents_lbi + Znth 0 contents_lai + 1] ++ [Znth 1 contents_lbi + Znth 1 contents_lai + 1] ++
   sublist 2 (Zlength contents_lai) contents_lbi)) with (sublist 2 (Zlength contents_lai) contents_lbi) by list_solve.
   rewrite sublist_split with 1 2 (Zlength contents_lai) contents_rbi by lia. rewrite sublist_len_1 by lia. replace (sublist 2 (Zlength contents_lai)
   ([Znth 0 contents_rbi + Znth 0 contents_rai + 1] ++ [Znth 1 contents_rbi] ++ sublist 2 (Zlength contents_lai) contents_rbi)) with (sublist 2 (Zlength contents_lai) contents_rbi) by list_solve.
   apply Forall2_sublist; try lia. assumption. split. simpl. rewrite Znth_0_cons. rewrite Znth_0_cons. do 2  rewrite Z.add_assoc.  f_equal. f_equal. f_equal. 
   apply Forall2_Znth with (i := 0) in H8; try lia. auto. split. simpl. rewrite Znth_pos_cons by lia. replace (1 - 1) with 0 by lia. rewrite Znth_0_cons.
   rewrite Znth_pos_cons by lia. replace (1 - 1) with 0 by lia.  rewrite Znth_0_cons. do 2 rewrite Z.add_assoc. f_equal. f_equal. f_equal.
   apply Forall2_Znth with (i := 1) in H8; try lia. auto. replace (sublist 2 (Zlength contents_lai) ([Znth 0 contents_lci + Znth 0 contents_lbi + Znth 0 contents_lai + 1] ++
    [Znth 1 contents_lci + Znth 1 contents_lbi + Znth 1 contents_lai + 1] ++ sublist 2 (Zlength contents_lai) contents_lci)) with (sublist 2 (Zlength contents_lai) contents_lci) by list_solve.
    apply Forall2_sublist; try lia. assumption.  
  Intros l_i r_j contents_lao contents_lbo contents_lco contents_rao contents_rbo contents_rco.
  forward_if. forward.
  Exists l_i. Exists r_j. 
  Exists contents_lao. Exists contents_lbo. Exists contents_lco.
  Exists contents_rao. Exists contents_rbo. Exists contents_rco. entailer!.
  (*next forward if*)
  forward_if. forward.
  Exists l_i. Exists r_j. 
  Exists contents_lao. Exists contents_lbo. Exists contents_lco.
  Exists contents_rao. Exists contents_rbo. Exists contents_rco. entailer!.
  (*assert all lengths*)
  fastforward; try list_solve. Exists (l_i + 1) (r_j + 1).
  Exists ((sublist 0 l_i contents_lao) ++ [Znth l_i contents_lao + 1] ++ (sublist (l_i + 1) N contents_lao)). 
  Exists ((sublist 0 l_i contents_lbo) ++ [Znth l_i contents_lbo + Znth l_i contents_lao + 1] ++ (sublist (l_i + 1) N contents_lbo)). 
  Exists ((sublist 0 l_i contents_lco) ++ [Znth l_i contents_lco + Znth l_i contents_lbo + Znth l_i contents_lao + 1] ++ (sublist (l_i + 1) N contents_lco)). 
  Exists ((sublist 0 (r_j + 2) contents_rao) ++ [Znth (r_j + 2) contents_rao + 1] ++ (sublist (r_j + 3) N contents_rao)). 
  Exists ((sublist 0 (r_j + 1) contents_rbo) ++ [Znth (r_j + 1) contents_rbo + Znth (r_j + 1) contents_lao] ++ (sublist (r_j + 2) N contents_rbo)). 
  Exists ((sublist 0 r_j contents_rco) ++ [Znth r_j contents_rco + Znth r_j contents_lbo] ++ (sublist (r_j + 1) N contents_rco)). 
  entailer!. split; try list_solve. split. list_solve. split. list_solve. split. list_solve. split. list_solve. split. list_solve.
  split. replace (r_j + 2 + 1) with (r_j + 3) by lia. apply Forall2_app. apply Forall2_sublist; try assumption. lia. apply Forall2_app.
  apply Forall2_cons; auto. f_equal. apply Forall2_Znth with (i := (r_j + 2)) in H18.  assumption. lia. apply Forall2_sublist. assumption. lia.
  split. replace (r_j + 1 + 1) with (r_j + 2) by lia. replace (r_j + 2 + 1) with (r_j + 3) by lia. rewrite app_assoc. rewrite app_assoc. 
  rewrite sublist0_app1 by list_solve. rewrite sublist0_app1 by list_solve. rewrite sublist0_app1 by list_solve. replace (sublist 0 (r_j + 2)
  (sublist 0 (r_j + 1) contents_rbo ++ [Znth (r_j + 1) contents_rbo + Znth (r_j + 1) contents_lao])) with (sublist 0 (r_j + 1) contents_rbo ++ [Znth (r_j + 1) contents_rbo + Znth (r_j + 1) contents_lao]) by list_solve.
  replace (sublist 0 (r_j + 2) (sublist 0 (r_j + 2) contents_lbo)) with (sublist 0 (r_j + 2) contents_lbo) by list_solve. 
  rewrite sublist_split with 0 (r_j + 1) (r_j + 2) contents_lbo by lia. replace (r_j + 2) with (r_j + 1 + 1) by lia. apply Forall2_app. 
  assumption. rewrite sublist_len_1 by lia. move H20 at bottom. rewrite H20. apply Forall2_cons; auto. split. replace (r_j + 1 + 1) with (r_j + 2) by lia. replace (r_j + 2 + 1) with (r_j + 3) by lia. simpl. 
  do 3 rewrite Znth_app2 by list_solve.  rewrite !Zlength_sublist by lia. replace (r_j + 2 - (r_j + 2 - 0)) with 0 by lia. replace (r_j + 2 - (r_j + 1 - 0)) with 1 by lia. 
  rewrite Znth_0_cons. rewrite Znth_0_cons. rewrite Znth_pos_cons by lia. replace (1 - 1) with 0 by lia. rewrite sublist_split with (r_j + 2) (r_j + 2 + 1) (Zlength contents_lai) contents_rbo by lia. 
  rewrite sublist_len_1 by lia. simpl. rewrite Znth_0_cons.  rewrite Z.add_assoc. f_equal. f_equal. move H21 at bottom. apply Forall2_Znth with (i := 0) in H21; try lia. 
  rewrite sublist_split with (r_j + 2) (r_j + 2 + 1) (Zlength contents_lai) contents_lbo in H21 by lia. rewrite sublist_split with (r_j + 2) (r_j + 2 + 1) (Zlength contents_lai) contents_rbo in H21 by lia.
  rewrite !sublist_len_1 in H21 by lia. simpl in H21. do 2 rewrite Znth_0_cons in H21. assumption. rewrite Zlength_sublist by lia. lia. split. 
  replace (r_j + 1 + 2) with (r_j + 3) by lia. replace (r_j + 2 + 1) with (r_j + 3) by lia. replace (sublist (r_j + 3) (Zlength contents_lai)
  (sublist 0 (r_j + 2) contents_lbo ++ [Znth (r_j + 2) contents_lbo + Znth (r_j + 2) contents_lao + 1] ++ sublist (r_j + 3) (Zlength contents_lai) contents_lbo)) with (sublist (r_j + 3) (Zlength contents_lai) contents_lbo) by list_solve.
  rewrite sublist_split with (r_j + 2) (r_j + 3) (Zlength contents_lai) contents_rbo by list_solve. replace (sublist (r_j + 3) (Zlength contents_lai)
  (sublist 0 (r_j + 1) contents_rbo ++ [Znth (r_j + 1) contents_rbo + Znth (r_j + 1) contents_lao] ++ sublist (r_j + 2) (r_j + 3) contents_rbo ++
   sublist (r_j + 3) (Zlength contents_lai) contents_rbo)) with (sublist (r_j + 3) (Zlength contents_lai) contents_rbo) by list_solve.
   move H21 at bottom. rewrite sublist_split with (r_j + 2) (r_j + 3) (Zlength contents_lai) contents_lbo in H21 by lia. 
   rewrite sublist_split with (r_j + 2) (r_j + 3) (Zlength contents_lai) contents_rbo in H21 by lia. apply Forall2_app_inv in H21. destruct H21 as [? ?]. assumption.
  apply invariants.Zlength_eq. rewrite !Zlength_sublist by lia.  lia. split. replace (sublist 0 (r_j + 1)
   (sublist 0 r_j contents_rco ++ [Znth r_j contents_rco + Znth r_j contents_lbo] ++ sublist (r_j + 1) (Zlength contents_lai) contents_rco)) with (sublist 0 r_j contents_rco ++
   [Znth r_j contents_rco + Znth r_j contents_lbo]) by list_solve. rewrite sublist_split with 0 (r_j + 1) (r_j + 2) contents_lco by list_solve.
   replace (sublist 0 (r_j + 1) ((sublist 0 (r_j + 1) contents_lco ++ sublist (r_j + 1) (r_j + 2) contents_lco) ++ [Znth (r_j + 2) contents_lco + Znth (r_j + 2) contents_lbo + Znth (r_j + 2) contents_lao + 1] ++
    sublist (r_j + 2 + 1) (Zlength contents_lai) contents_lco)) with (sublist 0 (r_j + 1) contents_lco) by list_solve. rewrite sublist_split with 0 r_j (r_j + 1) contents_lco by list_solve.
    rewrite sublist_len_1 by lia. apply Forall2_app. assumption. rewrite H23. apply Forall2_cons; try auto. split.  replace (Znth (r_j + 1)
    (sublist 0 (r_j + 2) contents_lco ++ [Znth (r_j + 2) contents_lco + Znth (r_j + 2) contents_lbo + Znth (r_j + 2) contents_lao + 1] ++ sublist (r_j + 2 + 1) (Zlength contents_lai) contents_lco)) with (Znth (r_j + 1) contents_lco) by list_solve.
   replace (Znth (r_j + 1) (sublist 0 r_j contents_rco ++ [Znth r_j contents_rco + Znth r_j contents_lbo] ++ sublist (r_j + 1) (Zlength contents_lai) contents_rco)) with (Znth (r_j + 1) contents_rco) by list_solve.
   replace (Znth (r_j + 1) (sublist 0 (r_j + 2) contents_lbo ++ [Znth (r_j + 2) contents_lbo + Znth (r_j + 2) contents_lao + 1] ++
    sublist (r_j + 2 + 1) (Zlength contents_lai) contents_lbo)) with (Znth (r_j + 1) contents_lbo) by list_solve. rewrite H24. reflexivity.
    split. replace (r_j + 1 + 1) with (r_j + 2) by lia. replace (r_j + 2 + 1) with (r_j + 3) by lia. replace (Znth (r_j + 2)
    (sublist 0 (r_j + 2) contents_lco ++ [Znth (r_j + 2) contents_lco + Znth (r_j + 2) contents_lbo + Znth (r_j + 2) contents_lao + 1] ++ sublist (r_j + 3) (Zlength contents_lai) contents_lco))
    with (Znth (r_j + 2) contents_lco + Znth (r_j + 2) contents_lbo + Znth (r_j + 2) contents_lao + 1) by list_solve. replace (Znth (r_j + 2)
    (sublist 0 r_j contents_rco ++ [Znth r_j contents_rco + Znth r_j contents_lbo] ++ sublist (r_j + 1) (Zlength contents_lai) contents_rco)) with (Znth (r_j + 2) contents_rco) by list_solve.
    replace (Znth (r_j + 2) (sublist 0 (r_j + 2) contents_lbo ++ [Znth (r_j + 2) contents_lbo + Znth (r_j + 2) contents_lao + 1] ++ sublist (r_j + 3) (Zlength contents_lai) contents_lbo))
    with (Znth (r_j + 2) contents_lbo + Znth (r_j + 2) contents_lao + 1) by list_solve. do 2 rewrite Z.add_assoc. f_equal. f_equal. f_equal. 
    move H25 at bottom. apply Forall2_Znth with (i := 0) in H25. replace (Znth 0 (sublist (r_j + 2) (Zlength contents_lai) contents_lco)) with (Znth (r_j + 2) contents_lco) in H25 by list_solve.
    replace (Znth 0 (sublist (r_j + 2) (Zlength contents_lai) contents_rco)) with (Znth (r_j + 2) contents_rco) in H25 by list_solve. assumption. 
    rewrite Zlength_sublist by lia. lia. replace (r_j + 1 + 2) with (r_j + 3) by lia. replace (r_j + 2 + 1) with (r_j + 3) by lia. 
    replace (sublist (r_j + 3) (Zlength contents_lai) (sublist 0 (r_j + 2) contents_lco ++ [Znth (r_j + 2) contents_lco + Znth (r_j + 2) contents_lbo + Znth (r_j + 2) contents_lao + 1] ++ sublist (r_j + 3) (Zlength contents_lai) contents_lco))
    with (sublist (r_j + 3) (Zlength contents_lai) contents_lco) by list_solve. replace (sublist (r_j + 3) (Zlength contents_lai)
    (sublist 0 r_j contents_rco ++ [Znth r_j contents_rco + Znth r_j contents_lbo] ++ sublist (r_j + 1) (Zlength contents_lai) contents_rco)) with (sublist (r_j + 3) (Zlength contents_lai) contents_rco) by list_solve. 
    move H25 at bottom. rewrite sublist_split with (r_j + 2) (r_j + 3) (Zlength contents_lai) contents_lco in H25 by list_solve. rewrite sublist_split with (r_j + 2) (r_j + 3) (Zlength contents_lai) contents_rco in H25 by list_solve.
    apply Forall2_app_inv in H25. destruct H25 as [? ?]. assumption. apply invariants.Zlength_eq. rewrite !Zlength_sublist by lia. lia. 
    repeat apply sepcon_derives.
    (*la*)
    apply derives_refl'. f_equal. rewrite !upd_Znth_map. f_equal. f_equal. list_solve.
    (*lb*)
    apply derives_refl'. f_equal. rewrite !sem_cast_i2i_correct_range. 
    2:{ simpl. list_simplify. }
    rewrite force_val_e. unfold both_int. simpl. 
    rewrite !sem_cast_i2i_correct_range.
    2:{ simpl. list_simplify. }
    simpl. try list_solve. list_simplify. rewrite force_val_e.
    rewrite add_repr. rewrite Z.add_assoc. reflexivity.  
    (*lc*)
    apply derives_refl'. f_equal. rewrite !sem_cast_i2i_correct_range. 
    2:{ simpl. list_simplify. }
    rewrite force_val_e. unfold both_int. simpl. 
    rewrite !sem_cast_i2i_correct_range.
    2:{ simpl. list_simplify. }
    simpl. try list_solve. list_simplify. rewrite !force_val_e.
    rewrite !add_repr. rewrite !Z.add_assoc. reflexivity. simpl. list_solve. list_solve.
    (*ra*)
    apply derives_refl'. f_equal. rewrite !upd_Znth_map. f_equal. f_equal. list_solve.
    (*rb*)
    apply derives_refl'. f_equal. rewrite !sem_cast_i2i_correct_range. 
    2:{ simpl. list_simplify. }
    rewrite force_val_e. unfold both_int. simpl. 
    rewrite !sem_cast_i2i_correct_range.
    2:{ simpl. list_simplify. }
    simpl. try list_solve. list_simplify. rewrite force_val_e.
    rewrite add_repr. move H18 at bottom. apply Forall2_Znth with (i := (r_j + 1)) in H18; try lia. rewrite H18. reflexivity.
    (*rc*)
    apply derives_refl'. f_equal. rewrite !sem_cast_i2i_correct_range. 
    2:{ simpl. list_simplify. }
    rewrite force_val_e. unfold both_int. simpl. 
    rewrite !sem_cast_i2i_correct_range.
    2:{ simpl. list_simplify. }
    simpl. try list_solve. list_simplify. rewrite !force_val_e.
    rewrite !add_repr.  move H19 at bottom. apply Forall2_Znth with (i := r_j) in H19; try lia. 
    replace (Znth r_j (sublist 0 (r_j + 1) contents_lbo)) with (Znth r_j contents_lbo) in H19 by list_solve. replace (Znth r_j (sublist 0 (r_j + 1) contents_rbo)) with (Znth r_j contents_rbo) in H19 by list_solve.
    rewrite H19. reflexivity. rewrite Zlength_sublist by list_solve. lia. list_solve. list_solve.
    (*break condition*)
    Intros l_i r_j contents_lao contents_lbo contents_lco contents_rao contents_rbo contents_rco.  
    forward_loop 
    (
      EX l_i:Z, EX r_j:Z, 
      EX contents_lao :list Z, EX contents_lbo:list Z, EX contents_lco:list Z,
      EX contents_rao :list Z, EX contents_rbo:list Z, EX contents_rco:list Z,
      PROP
      (
         l_i = N; r_j = Z.sub N 2;  l_i = Z.add r_j 2;
      Zlength contents_lao = N; Zlength contents_lbo = N; Zlength contents_lco = N;
      Zlength contents_rao = N; Zlength contents_rbo = N; Zlength contents_rco = N;
      (*for a*)
      Forall2 eq contents_lao contents_rao;
      (*for b*)
      Forall2 eq (sublist 0 (Z.add r_j 1) contents_lbo)(sublist 0 (Z.add r_j 1) contents_rbo);
      Znth (Z.add r_j 1) contents_lbo = Z.add (Znth (Z.add r_j 1) contents_rbo)  (Znth (Z.add r_j 1) contents_lao);
      Forall2 eq (sublist (Z.add r_j 2) N contents_lbo)(sublist (Z.add r_j 2) N contents_rbo);
      (*for c*)
      Forall2 eq (sublist 0 r_j contents_lco)(sublist 0 r_j contents_rco);
      Znth r_j contents_lco = Z.add (Znth r_j contents_rco) (Znth r_j contents_lbo);
      Znth (Z.add r_j 1) contents_lco = Z.add (Znth (Z.add r_j 1) contents_rco)  (Znth (Z.add r_j 1) contents_lbo);
      Forall2 eq (sublist (Z.add r_j 2) N contents_lco)(sublist (Z.add r_j 2) N contents_rco)
    )
    LOCAL
    (
      temp _l_i (Vint (Int.repr l_i));
      temp _r_j (Vint (Int.repr r_j)); 
      temp _l_a l_a; temp _l_b l_b; temp _l_c l_c;
      temp _r_a r_a; temp _r_b r_b; temp _r_c r_c; temp _N (Vint (Int.repr N))
      
    )
    SEP
    (
      data_at shla (tarray tuint N) (map Vint (map Int.repr contents_lao)) l_a;
      data_at shlb (tarray tuint N) (map Vint (map Int.repr contents_lbo)) l_b;
      data_at shlc (tarray tuint N) (map Vint (map Int.repr contents_lco)) l_c;
      data_at shra (tarray tuint N) (map Vint (map Int.repr contents_rao)) r_a;
      data_at shrb (tarray tuint N) (map Vint (map Int.repr contents_rbo)) r_b;
      data_at shrc (tarray tuint N) (map Vint (map Int.repr contents_rco)) r_c
    )
  )%assert
  break:
  (
    EX l_i:Z, EX r_j:Z, 
    EX contents_lao :list Z, EX contents_lbo:list Z, EX contents_lco:list Z,
    EX contents_rao :list Z, EX contents_rbo:list Z, EX contents_rco:list Z,
    PROP
    (
      l_i = N; r_j = Z.sub N 2;
      Zlength contents_lao = N; Zlength contents_lbo = N; Zlength contents_lco = N;
      Zlength contents_rao = N; Zlength contents_rbo = N; Zlength contents_rco = N;
      (*for a*)
      Forall2 eq contents_lao contents_rao;
      (*for b*)
      Forall2 eq (sublist 0 (Z.add r_j 1) contents_lbo)(sublist 0 (Z.add r_j 1) contents_rbo);
      Znth (Z.add r_j 1) contents_lbo = Z.add (Znth (Z.add r_j 1) contents_rbo)  (Znth (Z.add r_j 1) contents_lao);
      Forall2 eq (sublist (Z.add r_j 2) N contents_lbo)(sublist (Z.add r_j 2) N contents_rbo);
      (*for c*)
      Forall2 eq (sublist 0 r_j contents_lco)(sublist 0 r_j contents_rco);
      Znth r_j contents_lco = Z.add (Znth r_j contents_rco) (Znth r_j contents_lbo);
      Znth (Z.add r_j 1) contents_lco = Z.add (Znth (Z.add r_j 1) contents_rco)  (Znth (Z.add r_j 1) contents_lbo);
      Forall2 eq (sublist (Z.add r_j 2) N contents_lco)(sublist (Z.add r_j 2) N contents_rco)

    )
    LOCAL
    (
      temp _l_i (Vint (Int.repr l_i));
      temp _r_j (Vint (Int.repr r_j)); 
      temp _l_a l_a; temp _l_b l_b; temp _l_c l_c;
      temp _r_a r_a; temp _r_b r_b; temp _r_c r_c; temp _N (Vint (Int.repr N))
    )
    SEP
    (
      data_at shla (tarray tuint N) (map Vint (map Int.repr contents_lao)) l_a;
      data_at shlb (tarray tuint N) (map Vint (map Int.repr contents_lbo)) l_b;
      data_at shlc (tarray tuint N) (map Vint (map Int.repr contents_lco)) l_c;
      data_at shra (tarray tuint N) (map Vint (map Int.repr contents_rao)) r_a;
      data_at shrb (tarray tuint N) (map Vint (map Int.repr contents_rbo)) r_b;
      data_at shrc (tarray tuint N) (map Vint (map Int.repr contents_rco)) r_c
    )
  )%assert.
  Exists N (N - 2) contents_lao contents_lbo contents_lco contents_rao contents_rbo contents_rco. entailer!.
  Intros l_i0 r_j0 contents_lao0 contents_lbo0 contents_lco0 contents_rao0 contents_rbo0 contents_rco0.
  forward_if. forward.  Exists l_i0 r_j0 contents_lao0 contents_lbo0 contents_lco0 contents_rao0 contents_rbo0 contents_rco0. entailer!.
  rewrite H25 in H42. Search (_ <? _). apply Zlt_is_lt_bool in H42. rewrite Z.ltb_irrefl in H42. discriminate H42.
  Intros l_i0 r_j0 contents_lao0 contents_lbo0 contents_lco0 contents_rao0 contents_rbo0 contents_rco0.  
  (*loop again*)
  forward_loop 
  (
    EX l_i:Z, EX r_j:Z, 
    EX contents_lao :list Z, EX contents_lbo:list Z, EX contents_lco:list Z,
    EX contents_rao :list Z, EX contents_rbo:list Z, EX contents_rco:list Z,
    PROP
    (
       l_i = N; r_j = Z.sub N 2;  l_i = Z.add r_j 2;
    Zlength contents_lao = N; Zlength contents_lbo = N; Zlength contents_lco = N;
    Zlength contents_rao = N; Zlength contents_rbo = N; Zlength contents_rco = N;
    (*for a*)
    Forall2 eq contents_lao contents_rao;
    (*for b*)
    Forall2 eq (sublist 0 (Z.add r_j 1) contents_lbo)(sublist 0 (Z.add r_j 1) contents_rbo);
    Znth (Z.add r_j 1) contents_lbo = Z.add (Znth (Z.add r_j 1) contents_rbo)  (Znth (Z.add r_j 1) contents_lao);
    Forall2 eq (sublist (Z.add r_j 2) N contents_lbo)(sublist (Z.add r_j 2) N contents_rbo);
    (*for c*)
    Forall2 eq (sublist 0 r_j contents_lco)(sublist 0 r_j contents_rco);
    Znth r_j contents_lco = Z.add (Znth r_j contents_rco) (Znth r_j contents_lbo);
    Znth (Z.add r_j 1) contents_lco = Z.add (Znth (Z.add r_j 1) contents_rco)  (Znth (Z.add r_j 1) contents_lbo);
    Forall2 eq (sublist (Z.add r_j 2) N contents_lco)(sublist (Z.add r_j 2) N contents_rco)
  )
  LOCAL
  (
    temp _l_i (Vint (Int.repr l_i));
    temp _r_j (Vint (Int.repr r_j)); 
    temp _l_a l_a; temp _l_b l_b; temp _l_c l_c;
    temp _r_a r_a; temp _r_b r_b; temp _r_c r_c; temp _N (Vint (Int.repr N))
    
  )
  SEP
  (
    data_at shla (tarray tuint N) (map Vint (map Int.repr contents_lao)) l_a;
    data_at shlb (tarray tuint N) (map Vint (map Int.repr contents_lbo)) l_b;
    data_at shlc (tarray tuint N) (map Vint (map Int.repr contents_lco)) l_c;
    data_at shra (tarray tuint N) (map Vint (map Int.repr contents_rao)) r_a;
    data_at shrb (tarray tuint N) (map Vint (map Int.repr contents_rbo)) r_b;
    data_at shrc (tarray tuint N) (map Vint (map Int.repr contents_rco)) r_c
  )
)%assert
break:
(
  EX l_i:Z, EX r_j:Z, 
  EX contents_lao :list Z, EX contents_lbo:list Z, EX contents_lco:list Z,
  EX contents_rao :list Z, EX contents_rbo:list Z, EX contents_rco:list Z,
  PROP
  (
    l_i = N; r_j = Z.sub N 2;
    Zlength contents_lao = N; Zlength contents_lbo = N; Zlength contents_lco = N;
    Zlength contents_rao = N; Zlength contents_rbo = N; Zlength contents_rco = N;
    (*for a*)
    Forall2 eq contents_lao contents_rao;
    (*for b*)
    Forall2 eq (sublist 0 (Z.add r_j 1) contents_lbo)(sublist 0 (Z.add r_j 1) contents_rbo);
    Znth (Z.add r_j 1) contents_lbo = Z.add (Znth (Z.add r_j 1) contents_rbo)  (Znth (Z.add r_j 1) contents_lao);
    Forall2 eq (sublist (Z.add r_j 2) N contents_lbo)(sublist (Z.add r_j 2) N contents_rbo);
    (*for c*)
    Forall2 eq (sublist 0 r_j contents_lco)(sublist 0 r_j contents_rco);
    Znth r_j contents_lco = Z.add (Znth r_j contents_rco) (Znth r_j contents_lbo);
    Znth (Z.add r_j 1) contents_lco = Z.add (Znth (Z.add r_j 1) contents_rco)  (Znth (Z.add r_j 1) contents_lbo);
    Forall2 eq (sublist (Z.add r_j 2) N contents_lco)(sublist (Z.add r_j 2) N contents_rco)

  )
  LOCAL
  (
    temp _l_i (Vint (Int.repr l_i));
    temp _r_j (Vint (Int.repr r_j)); 
    temp _l_a l_a; temp _l_b l_b; temp _l_c l_c;
    temp _r_a r_a; temp _r_b r_b; temp _r_c r_c; temp _N (Vint (Int.repr N))
  )
  SEP
  (
    data_at shla (tarray tuint N) (map Vint (map Int.repr contents_lao)) l_a;
    data_at shlb (tarray tuint N) (map Vint (map Int.repr contents_lbo)) l_b;
    data_at shlc (tarray tuint N) (map Vint (map Int.repr contents_lco)) l_c;
    data_at shra (tarray tuint N) (map Vint (map Int.repr contents_rao)) r_a;
    data_at shrb (tarray tuint N) (map Vint (map Int.repr contents_rbo)) r_b;
    data_at shrc (tarray tuint N) (map Vint (map Int.repr contents_rco)) r_c
  )
)%assert.
Exists N (N - 2) contents_lao0 contents_lbo0 contents_lco0 contents_rao0 contents_rbo0 contents_rco0. entailer!.
Intros l_i1 r_j1 contents_lao1 contents_lbo1 contents_lco1 contents_rao1 contents_rbo1 contents_rco1. forward_if. forward.
Exists l_i1 r_j1 contents_lao1 contents_lbo1 contents_lco1 contents_rao1 contents_rbo1 contents_rco1. entailer!.
forward_if.  forward. Exists l_i1 r_j1 contents_lao1 contents_lbo1 contents_lco1 contents_rao1 contents_rbo1 contents_rco1. entailer!.
rewrite H42 in H59. apply Zlt_is_lt_bool in H59. rewrite Z.ltb_irrefl in H59. discriminate H59. 
Intros l_i1 r_j1 contents_lao1 contents_lbo1 contents_lco1 contents_rao1 contents_rbo1 contents_rco1.  fastforward; try list_solve.
Exists contents_lao1 contents_lbo1 contents_lco1 contents_rao1.
Exists ((sublist 0 (r_j + 1) contents_rbo1) ++ [Znth (r_j + 1) contents_rbo1 + Znth (r_j + 1) contents_lao1]). 
Exists ((sublist 0 r_j contents_rco1) ++ [Znth r_j contents_rco1 + Znth r_j contents_lbo1] ++ [Znth (r_j + 1) contents_rco1 + Znth (r_j + 1) contents_lbo1]).
entailer!. replace (Zlength contents_lai - 2 + 1) with (Zlength contents_lai - 1) by lia. split. Search sublist. rewrite <- sublist_same with 0 (Zlength contents_lai) contents_lbo1 by list_solve. 
rewrite sublist_split with 0 (Zlength contents_lai - 1) (Zlength contents_lai) contents_lbo1 by list_solve. apply Forall2_app. move H50 at bottom.
replace (Zlength contents_lai - 2 + 1) with (Zlength contents_lai - 1) in H50 by lia. assumption. replace (sublist (Zlength contents_lai - 1) (Zlength contents_lai) contents_lbo1) with [Znth (Zlength contents_lai - 1) contents_lbo1] by list_solve. 
apply Forall2_cons; auto. move H51 at bottom. replace (Zlength contents_lai - 2 + 1) with (Zlength contents_lai - 1) in H51 by lia. assumption. 
rewrite <- sublist_same with 0 (Zlength contents_lai) contents_lco1 by list_solve. rewrite sublist_split with 0 (Zlength contents_lai - 2) (Zlength contents_lai) contents_lco1 by list_solve.
rewrite sublist_split with (Zlength contents_lai - 2) (Zlength contents_lai - 1) (Zlength contents_lai) contents_lco1 by list_solve. 
apply Forall2_app.  assumption. apply Forall2_app. replace (Zlength contents_lai - 1) with (Zlength contents_lai - 2 + 1) by lia. rewrite sublist_len_1 by lia. 
apply Forall2_cons; auto. replace (sublist (Zlength contents_lai - 1) (Zlength contents_lai) contents_lco1) with [Znth (Zlength contents_lai - 1) contents_lco1] by list_solve.
apply Forall2_cons; auto. move H55 at bottom. replace (Zlength contents_lai - 2 + 1) with (Zlength contents_lai - 1) in H55 by lia. assumption.
replace (Zlength contents_lai - 2 + 1) with (Zlength contents_lai - 1) by lia. apply sepcon_derives.
(*b*)
apply derives_refl'. f_equal. rewrite !upd_Znth_map. f_equal. f_equal. list_simplify. f_equal. move H49 at bottom. 
eapply Forall2_Znth with (i := (Zlength contents_lai - 1)) in H49; try lia.
(*c*)
apply derives_refl'. f_equal. rewrite !sem_cast_i2i_correct_range. 
    2:{ simpl. list_simplify. }
    rewrite force_val_e. unfold both_int. simpl. 
    rewrite !sem_cast_i2i_correct_range.
    2:{ simpl. list_simplify. }
    simpl. try list_solve. list_simplify. move H50 at bottom. replace (Zlength contents_lai - 2 + 1) with (Zlength contents_lai - 1) in H50 by lia.
    apply Forall2_Znth with (i := (Zlength contents_lai - 2)) in H50. replace (Znth (Zlength contents_lai - 2) (sublist 0 (Zlength contents_lai - 1) contents_lbo1)) with (Znth (Zlength contents_lai - 2) contents_lbo1) in H50 by list_solve.
    replace (Znth (Zlength contents_lai - 2) (sublist 0 (Zlength contents_lai - 1) contents_rbo1)) with (Znth (Zlength contents_lai - 2) contents_rbo1) in H50 by list_solve. rewrite H50. reflexivity.
    rewrite Zlength_sublist by lia. lia. rewrite force_val_e. 
    rewrite !add_repr. rewrite !Z.add_assoc. f_equal. f_equal. move H51 at bottom. replace (Zlength contents_lai - 2 + 1) with (Zlength contents_lai - 1) in H51 by lia. 
    rewrite H51. rewrite Z.add_assoc. move H49 at bottom. eapply Forall2_Znth with (i := (Zlength contents_lai - 1)) in H49; try lia.
    list_solve.
 Qed.


























  