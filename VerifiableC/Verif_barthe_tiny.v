(* ================================================================= *)
(* antonoupoulous_sa_simple.c - no array for this*)

Require VC.Preface. 
Require Import Setoid.
From Coq Require Import ZArith.Int.
Require Import VST.floyd.proofauto.
Require Import Coq.Classes.RelationClasses.

Require Import VC.barthe_tiny.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Definition sum_lZ : list Z -> list Z := map Z.succ.

Definition sum_aZ (a b: list Z): list Z := map (fun '(x, y) => (x + y)%Z) (combine a b).

Lemma add_entailment:  forall {cs: compspecs} sh contents_a l_i a,

0 <= l_i < 100 ->
Zlength contents_a = 100 ->

data_at sh (tarray tuint 100)
  (map Vint
     (map Int.repr
        (upd_Znth l_i
           (sum_lZ (sublist 0 l_i contents_a) ++ sublist l_i (l_i + 1) contents_a ++ sublist (l_i + 1) 100 contents_a)
           (Znth l_i
              (sum_lZ (sublist 0 l_i contents_a) ++
               sublist l_i (l_i + 1) contents_a ++ sublist (l_i + 1) 100 contents_a)
              + 1)))) a
|-- data_at sh (tarray tuint 100)
      (map Vint
         (map Int.repr
            (sum_lZ (sublist 0 l_i contents_a ++ sublist l_i (l_i + 1) contents_a) ++ sublist (l_i + 1) 100 contents_a)))
      a.

Proof.
intros.
apply derives_refl'.
f_equal.
f_equal.
f_equal.

unfold sum_lZ.
list_simplify.
assert (i=l_i) by lia.
subst l_i.
list_simplify.
Qed.


Lemma samea_listLength : forall (l1 l2 : list Z),
Zlength l1 = Zlength l2 ->
Zlength l1 = Zlength (sum_aZ l1 l2).
Proof.
  induction l1,l2; simpl; unfold sum_aZ; try list_solve.
  list_simplify. Search (1 + _). rewrite !Z.add_1_l in H.
  apply Z.succ_inj in H.
  rewrite Zlength_combine.  
  rewrite <- !cons_Zrepeat_1_app.
  rewrite !Zlength_cons. rewrite H. 
  rewrite Z.min_id. rewrite Z.add_1_l.
  reflexivity.
Qed.

Lemma same_listLength : forall (l: list Z),
Zlength l = Zlength (sum_lZ l).
Proof.
 intros. induction l.
 simpl. reflexivity. Search Zlength(_ :: _). 
 rewrite Zlength_cons. simpl. rewrite Zlength_cons.
 f_equal. assumption.
Qed.

(*Functional Model: empty for kestrel*)
(*API spec => verifyfunc spec *)
Definition verifyfunc_spec : ident * funspec :=
DECLARE _verifyfunc
  WITH l_a : val, l_b : val, sh1 : share, sh2 : share,
  contents_la : list Z, contents_lb : list Z
  PRE [tptr tuint, tptr tuint]  
    (*ensure variables left and right are equal*)
    PROP (
    writable_share sh1;
    writable_share sh2;
    Forall (fun x => 0 <= x + 1 <= Int.max_unsigned) contents_la;
    Forall (fun x => 0 <= x <= Int.max_unsigned) contents_lb;
    Forall2 (fun x y => 0 <= x + y + 1 <= Int.max_unsigned) contents_la contents_lb)
  PARAMS (l_a; l_b)
    SEP (data_at sh1 (tarray tuint 100) (map Vint (map Int.repr contents_la)) l_a;
    data_at sh2 (tarray tuint 100) (map Vint (map Int.repr contents_lb)) l_b)
  POST [ tvoid ]
    PROP ()
    RETURN () (*void*)
    SEP (data_at sh1 (tarray tuint 100) (map Vint (map Int.repr (sum_lZ (sublist 0 100 contents_la)))) l_a;
    data_at sh2 (tarray tuint 100) (map Vint (map Int.repr (sum_aZ (sublist 0 100 contents_lb) (sublist 0 100 contents_la)))) l_b). 


 (*Functional Model: empty for kestrel*)
(*API spec => verifyfunc spec *)
Definition verifyfunca_spec : ident * funspec :=
  DECLARE _verifyfunca
    WITH l_a : val, l_b : val, sh1 : share, sh2 : share,
    contents_la : list Z, contents_lb : list Z
    PRE [tptr tuint, tptr tuint]  
      (*ensure variables left and right are equal*)
      PROP (
      writable_share sh1;
      writable_share sh2;
      Forall (fun x => 0 <= x + 1 <= Int.max_unsigned) contents_la;
      Forall (fun x => 0 <= x <= Int.max_unsigned) contents_lb;
      Forall2 (fun x y => 0 <= x + y + 1 <= Int.max_unsigned) contents_la contents_lb)
    PARAMS (l_a; l_b)
      SEP (data_at sh1 (tarray tuint 100) (map Vint (map Int.repr contents_la)) l_a;
      data_at sh2 (tarray tuint 100) (map Vint (map Int.repr contents_lb)) l_b)
    POST [ tvoid ]
      PROP ()
      RETURN () (*void*)
      SEP (data_at sh1 (tarray tuint 100) (map Vint (map Int.repr (sum_lZ (sublist 0 100 contents_la)))) l_a;
      data_at sh2 (tarray tuint 100) (map Vint (map Int.repr (sum_aZ (sublist 0 100 contents_lb) (sublist 0 100 contents_la)))) l_b).    


(*Pack APIs together*)
Definition Gprog := [verifyfunc_spec; verifyfunca_spec].

(*verify fun_spec - from here*)

(*verify fun_spec - from here*)
Lemma body_verifyfunc: semax_body Vprog Gprog f_verifyfunc verifyfunc_spec.
Proof. 
 start_function. 
 (*a1 length is M*)
 assert_PROP (Zlength contents_la = 100). {
  entailer!. rewrite <- H3. do 2 rewrite Zlength_map. reflexivity.
 }
 assert_PROP (Zlength contents_lb = 100). {
  entailer!. rewrite <- H7. do 2 rewrite Zlength_map. reflexivity.
 }
 forward.
forward_loop 
  (EX l_i:Z,  
    PROP (0 <= l_i <= 100)
   LOCAL (
    temp _l_i (Vint (Int.repr l_i)); 
    temp _l_a l_a; temp _l_b l_b
    )(*map.Vint (map Int.repr (sublist 0 l_x contents_f ++ sublist l_x (N * M) contents a_1)) a_1*)
   SEP (data_at sh1 (tarray tuint 100) 
   (map Vint (map Int.repr ((sum_lZ (sublist 0 l_i contents_la)) ++ (sublist l_i 100 contents_la)))) l_a;
   data_at sh2 (tarray tuint 100) 
   (map Vint (map Int.repr ((sum_aZ (sublist 0 l_i contents_lb) (sublist 0 l_i contents_la)) ++ (sublist l_i 100 contents_lb)))) l_b))%assert
   break: 
   (EX l_i:Z, 
   PROP (0 <= l_i <= 100; l_i = 100)
   LOCAL (
    temp _l_i (Vint (Int.repr l_i)); 
    temp _l_a l_a; temp _l_b l_b)
    SEP (data_at sh1 (tarray tuint 100) 
    (map Vint (map Int.repr ((sum_lZ (sublist 0 l_i contents_la)) ++ (sublist l_i 100 contents_la)))) l_a;
    data_at sh2 (tarray tuint 100) 
    (map Vint (map Int.repr ((sum_aZ (sublist 0 l_i contents_lb) (sublist 0 l_i contents_la)) ++ (sublist l_i 100 contents_lb)))) l_b))%assert.
 (*first existential - outermost if*)      
 Exists 0.  entailer!. simpl. rewrite !sublist_same_gen.
 entailer!. reflexivity. rewrite H3. lia. reflexivity. lia.
 Intros l_i. forward_if. forward. 
 (*second if - entailer*)
 Exists l_i.  entailer!. (*entailer!.*) 
 assert_PROP (Zlength (map Int.repr ((sum_lZ (sublist 0 l_i contents_la)) ++
 sublist l_i 100 contents_la)) = 100). {
  entailer!. rewrite Zlength_map.
  rewrite Zlength_app. rewrite <- same_listLength.
  rewrite <- Zlength_app. rewrite sublist_rejoin with 0 l_i 100 contents_la.
  rewrite sublist_same_gen. assumption. reflexivity. 
  lia. lia. lia.
  }
  assert_PROP (0 <= l_i < Zlength (map Int.repr ((sum_lZ (sublist 0 l_i contents_la)) ++
 sublist l_i 100 contents_la))). {
  entailer!. 
  }
  assert_PROP (0 <= l_i < Zlength ((sum_lZ (sublist 0 l_i contents_la)) ++
 sublist l_i 100 contents_la)). {
  entailer!. rewrite Zlength_map in H7. assumption.
  }
  (*for sublist b*)
  assert_PROP (Zlength (map Int.repr ((sum_aZ (sublist 0 l_i contents_lb)(sublist 0 l_i contents_la)) ++
 sublist l_i 100 contents_lb)) = 100). {
  entailer!. rewrite Zlength_map.
  rewrite Zlength_app. rewrite <- samea_listLength.
  rewrite <- Zlength_app. rewrite sublist_rejoin with 0 l_i 100 contents_lb.
  rewrite sublist_same_gen. assumption. reflexivity. 
  lia. lia. lia. Search Zlength sublist 0. 
  rewrite Zlength_sublist with 0 l_i contents_lb. rewrite Zlength_sublist with 0 l_i contents_la.
  reflexivity. lia. lia. lia. lia.
  }
  assert_PROP (0 <= l_i < Zlength (map Int.repr ((sum_aZ (sublist 0 l_i contents_lb)(sublist 0 l_i contents_la)) ++
  sublist l_i 100 contents_lb))). {
  entailer!. 
  }
  assert_PROP (0 <= l_i < Zlength ((sum_aZ (sublist 0 l_i contents_lb)(sublist 0 l_i contents_la)) ++
  sublist l_i 100 contents_lb)). {
  entailer!. rewrite Zlength_map in H10. assumption.
  }
  forward. forward. forward. forward. forward. forward. Exists (l_i + 1).
  entailer!. apply sepcon_derives. do 2 rewrite upd_Znth_map.  
  rewrite (sublist_split 0 l_i (l_i+1)). rewrite (sublist_split l_i (l_i+1) 100).
  eapply add_entailment. lia. lia. lia. lia. lia. lia.
  do 2 rewrite upd_Znth_map.
  apply derives_refl'.
  f_equal. f_equal. f_equal. rewrite !Znth_app2. rewrite !upd_Znth_app2. 
  rewrite <- !samea_listLength. rewrite <- !same_listLength.
  rewrite !Zlength_sublist. 
  replace (l_i - (l_i - 0)) with 0 by lia.  Print sublist_split.
  rewrite (sublist_split l_i (l_i+1) 100). rewrite sublist_len_1. 
  rewrite (sublist_split l_i (l_i+1) 100). rewrite sublist_len_1. simpl.
  Search Znth cons. rewrite !Znth_0_cons. Print upd_Znth0.    
  rewrite upd_Znth0. rewrite app_cons_assoc. f_equal.
  rewrite !(sublist_split 0 l_i (l_i+1)). Search sublist. 
  rewrite !sublist_len_1. unfold sum_aZ at 2.
  Search combine app. rewrite combine_app'. simpl.
  Search map app. rewrite map_app. simpl. reflexivity.
  rewrite !Zlength_sublist. reflexivity.
  lia. lia. lia. lia. lia. lia. lia. lia. lia. lia. lia.
  lia. lia. lia. lia. lia. lia. lia. lia. lia.
  rewrite !Zlength_sublist. reflexivity. lia. lia. lia.
  lia. rewrite <- !samea_listLength. rewrite !Zlength_sublist.
  replace (l_i - 0) with l_i by lia. replace (l_i + (100 - l_i)) with 100 by lia.
  lia. lia. lia. lia. lia. rewrite !Zlength_sublist.
  reflexivity. lia. lia. lia. lia. rewrite <- same_listLength.
  rewrite Zlength_sublist. replace (l_i - 0) with l_i by lia.
  lia. lia. lia. rewrite <- !samea_listLength. rewrite !Zlength_sublist.
  replace (l_i - 0) with l_i by lia. lia. lia. lia.
  rewrite !Zlength_sublist. reflexivity. lia. lia. lia. lia.
  Intros l_i. rewrite H5. entailer!. Search sublist.
  rewrite !sublist_nil. simpl. Search app.
  rewrite <- !app_nil_end. entailer!.
Qed.


(*verify fun_spec - from here*)
Lemma body_verifyfunca: semax_body Vprog Gprog f_verifyfunca verifyfunca_spec.
Proof. 
 start_function. 
 (*a1 length is M*)
 assert_PROP (Zlength contents_la = 100). {
  entailer!. rewrite <- H3. do 2 rewrite Zlength_map. reflexivity.
 }
 assert_PROP (Zlength contents_lb = 100). {
  entailer!. rewrite <- H7. do 2 rewrite Zlength_map. reflexivity.
 }
 forward.
forward_loop 
  (EX l_i:Z,  
    PROP (0 <= l_i <= 100)
   LOCAL (
    temp _l_i (Vint (Int.repr l_i)); 
    temp _l_a l_a; temp _l_b l_b
    )(*map.Vint (map Int.repr (sublist 0 l_x contents_f ++ sublist l_x (N * M) contents a_1)) a_1*)
   SEP (data_at sh1 (tarray tuint 100) 
   (map Vint (map Int.repr ((sum_lZ (sublist 0 l_i contents_la)) ++ (sublist l_i 100 contents_la)))) l_a;
   data_at sh2 (tarray tuint 100) 
   (map Vint (map Int.repr ((sum_aZ (sublist 0 l_i contents_lb) (sublist 0 l_i contents_la)) ++ (sublist l_i 100 contents_lb)))) l_b))%assert
   break: 
   (EX l_i:Z, 
   PROP (0 <= l_i <= 100; l_i = 100)
   LOCAL (
    temp _l_i (Vint (Int.repr l_i)); 
    temp _l_a l_a; temp _l_b l_b)
    SEP (data_at sh1 (tarray tuint 100) 
    (map Vint (map Int.repr ((sum_lZ (sublist 0 l_i contents_la)) ++ (sublist l_i 100 contents_la)))) l_a;
    data_at sh2 (tarray tuint 100) 
    (map Vint (map Int.repr ((sum_aZ (sublist 0 l_i contents_lb) (sublist 0 l_i contents_la)) ++ (sublist l_i 100 contents_lb)))) l_b))%assert.
 (*first existential - outermost if*)      
 Exists 0.  entailer!. simpl. rewrite !sublist_same_gen.
 entailer!. reflexivity. rewrite H3. lia. reflexivity. lia.
 Intros l_i. forward_if. forward. 
 (*second if - entailer*)
 Exists l_i.  entailer!. (*entailer!.*) 
 assert_PROP (Zlength (map Int.repr ((sum_lZ (sublist 0 l_i contents_la)) ++
 sublist l_i 100 contents_la)) = 100). {
  entailer!. rewrite Zlength_map.
  rewrite Zlength_app. rewrite <- same_listLength.
  rewrite <- Zlength_app. rewrite sublist_rejoin with 0 l_i 100 contents_la.
  rewrite sublist_same_gen. assumption. reflexivity. 
  lia. lia. lia.
  }
  assert_PROP (0 <= l_i < Zlength (map Int.repr ((sum_lZ (sublist 0 l_i contents_la)) ++
 sublist l_i 100 contents_la))). {
  entailer!. 
  }
  assert_PROP (0 <= l_i < Zlength ((sum_lZ (sublist 0 l_i contents_la)) ++
 sublist l_i 100 contents_la)). {
  entailer!. rewrite Zlength_map in H7. assumption.
  }
  (*for sublist b*)
  assert_PROP (Zlength (map Int.repr ((sum_aZ (sublist 0 l_i contents_lb)(sublist 0 l_i contents_la)) ++
 sublist l_i 100 contents_lb)) = 100). {
  entailer!. rewrite Zlength_map.
  rewrite Zlength_app. rewrite <- samea_listLength.
  rewrite <- Zlength_app. rewrite sublist_rejoin with 0 l_i 100 contents_lb.
  rewrite sublist_same_gen. assumption. reflexivity. 
  lia. lia. lia. Search Zlength sublist 0. 
  rewrite Zlength_sublist with 0 l_i contents_lb. rewrite Zlength_sublist with 0 l_i contents_la.
  reflexivity. lia. lia. lia. lia.
  }
  assert_PROP (0 <= l_i < Zlength (map Int.repr ((sum_aZ (sublist 0 l_i contents_lb)(sublist 0 l_i contents_la)) ++
  sublist l_i 100 contents_lb))). {
  entailer!. 
  }
  assert_PROP (0 <= l_i < Zlength ((sum_aZ (sublist 0 l_i contents_lb)(sublist 0 l_i contents_la)) ++
  sublist l_i 100 contents_lb)). {
  entailer!. rewrite Zlength_map in H10. assumption.
  }
  forward. forward. forward. forward. Print local. Print mpred.
  Print environ. Print tc_val.
  
  Print Vint. Print liftx.
  Print Lift.  list_simplify. forward. forward. Exists (l_i + 1).
  entailer!. apply sepcon_derives.  do 2 rewrite upd_Znth_map.  
  rewrite (sublist_split 0 l_i (l_i+1)). rewrite (sublist_split l_i (l_i+1) 100).
  eapply add_entailment. lia. assumption. lia. lia. lia. lia.
  apply derives_refl'. f_equal.
  rewrite sem_cast_i2i_correct_range. 
  2:{ simpl. list_simplify. }
  Search force_val Some. rewrite force_val_e.
  Print both_int. unfold both_int. simpl.
  rewrite sem_cast_i2i_correct_range. 2:{ list_simplify. } 
  simpl. list_simplify. rewrite force_val_e. rewrite <- !samea_listLength.
  rewrite <- !same_listLength.  rewrite !Zlength_sublist. 
  replace (l_i - 0) with l_i by lia. replace (l_i - l_i + l_i) with l_i by lia.
  rewrite !upd_Znth_map. f_equal. 
  rewrite add_repr.
  rewrite !upd_Znth_map. f_equal. 
  rewrite !upd_Znth_app2. 
  rewrite <- !samea_listLength. rewrite !Zlength_sublist. 
  replace (l_i - (l_i - 0)) with 0 by lia. 
  rewrite (sublist_split l_i (l_i+1) 100). rewrite sublist_len_1. simpl.   
  rewrite upd_Znth0. rewrite app_cons_assoc. f_equal.
  rewrite !(sublist_split 0 l_i (l_i+1)). Search sublist. 
  rewrite !sublist_len_1. unfold sum_aZ at 2.
  Search combine app. rewrite combine_app'. simpl.
  Search map app. rewrite map_app. simpl. reflexivity.
  
Admitted.