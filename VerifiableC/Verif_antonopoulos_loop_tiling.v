(* ================================================================= *)
(* antonoupoulous_sa_simple.c - no array for this*)

Require VC.Preface. 
Require Import Setoid.
From Coq Require Import ZArith.Int.
Require Import VST.floyd.proofauto.
Require Import Coq.Classes.RelationClasses.

Require Import VC.antonopoulos_loop_tiling.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

(*Functional Model: empty for kestrel*)
(*API spec => verifyfunc spec *)
Definition verifyfunc_spec : ident * funspec :=
DECLARE _verifyfunc
  WITH l_x : Z, r_x : Z, M : Z,
  a_1 : val, sh1 : share, contents_a1 : list Z,
  a_2 : val, sh2 : share, contents_a2 : list Z, 
  f : val, shf : share, contents_f : list Z
  PRE [ tuint, tuint, tuint, tptr tuint, tptr tuint, tptr tuint ]  
    (*ensure variables left and right are equal*)
    PROP ( l_x = 0; r_x = 0; M = 100;
    0 <= l_x <= Int.max_unsigned; 0 <= r_x <= Int.max_unsigned; 
    0 <= M <= Int.max_unsigned;
    writable_share sh1; writable_share sh2; readable_share shf;
    Forall (fun x => 0 <= x <= Int.max_unsigned) contents_a1;
    Forall (fun x => 0 <= x <= Int.max_unsigned) contents_a2;
    Forall (fun x => 0 <= x <= Int.max_unsigned) contents_f)
  PARAMS (Vint (Int.repr l_x); Vint (Int.repr r_x); Vint (Int.repr M); a_1; a_2; f)
    SEP (data_at sh1 (tarray tuint M) (map Vint (map Int.repr contents_a1)) a_1;
    data_at sh2 (tarray tuint M) (map Vint (map Int.repr contents_a2)) a_2;
    data_at shf (tarray tuint M) (map Vint (map Int.repr contents_f)) f) (*non-empty: array range*)
  POST [ tvoid ]
    PROP ()
    RETURN () (*void*)
    SEP (data_at sh1 (tarray tuint M) (map Vint (map Int.repr contents_f)) a_1;
    data_at sh2 (tarray tuint M) (map Vint (map Int.repr contents_f)) a_2;
    data_at shf (tarray tuint M) (map Vint (map Int.repr contents_f)) f) (*non-empty: array*).


(*API spec =>main*)
Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre prog tt gv
  POST [ tint ]
    PROP() 
    RETURN(Vint (Int.repr 0))
    SEP(TT).

(*Pack APIs together*)
Definition Gprog := [verifyfunc_spec; main_spec].

(*verify fun_spec - from here*)

(*verify fun_spec - from here*)
Lemma body_verifyfunc: semax_body Vprog Gprog f_verifyfunc verifyfunc_spec.
Proof. 
 start_function. 
 (*a1 length is M*)
 assert_PROP (Zlength contents_a1 = M). {
  entailer!. rewrite <- H9. do 2 rewrite Zlength_map. reflexivity.
 }
 (*a2 length is M*)
 assert_PROP (Zlength contents_a2 = M). {
  entailer!. rewrite <- H12. do 2 rewrite Zlength_map. reflexivity.
 }
 (*f length is M*)
 assert_PROP (Zlength contents_f = M). {
  entailer!. rewrite <- H16. do 2 rewrite Zlength_map. reflexivity.
 }
forward_loop 
  (EX l_x:Z, EX r_x:Z,  
    PROP (0 <= l_x <= M; 0 <= r_x <= M; l_x = r_x)
   LOCAL (
    temp _l_x (Vint (Int.repr l_x)); temp _r_x (Vint (Int.repr r_x));
    temp _M (Vint (Int.repr M)); 
    temp _a_1__1 a_1; temp _a_2__1 a_2; temp _f__1 f
    )(*map.Vint (map Int.repr (sublist 0 l_x contents_f ++ sublist l_x (N * M) contents a_1)) a_1*)
   SEP (data_at sh1 (tarray tuint M) 
   (map Vint (map Int.repr (sublist 0 l_x contents_f ++ sublist l_x M contents_a1))) a_1;
   data_at sh2 (tarray tuint M) 
   (map Vint (map Int.repr (sublist 0 r_x contents_f ++ sublist r_x M contents_a2))) a_2;
   data_at shf (tarray tuint M) (map Vint (map Int.repr contents_f)) f))%assert
   break: 
   (EX l_x:Z, EX r_x:Z,
   PROP (0 <= l_x <= M; 0 <= r_x <= M; l_x = M; r_x = M; l_x = r_x)
   LOCAL (
    temp _l_x (Vint (Int.repr l_x)); temp _r_x (Vint (Int.repr r_x));
    temp _M (Vint (Int.repr M));
    temp _a_1__1 a_1; temp _a_2__1 a_2; temp _f__1 f
   )
  SEP (data_at sh1 (tarray tuint M)
  (map Vint (map Int.repr (sublist 0 l_x contents_f ++ sublist l_x M contents_a1))) a_1; 
  data_at sh2 (tarray tuint M)
  (map Vint (map Int.repr (sublist 0 r_x contents_f ++ sublist r_x M contents_a2))) a_2; 
  data_at shf (tarray tuint M) (map Vint (map Int.repr contents_f)) f))%assert.
 (*first existential - outermost if*)      
 Exists l_x. Exists r_x.  entailer!. simpl.
 repeat rewrite sublist_same. entailer!. reflexivity.  
 rewrite H9. reflexivity. reflexivity. rewrite H8. reflexivity.
 Intros l_x0 r_x0. forward_if. forward. 
 (*second if - entailer*)
 Exists l_x0. Exists r_x0. entailer!. forward_if. forward.
 (*last - else*)
 Exists l_x0. Exists r_x0. entailer!. 
 forward. forward. forward. forward. forward. forward. 
 Exists (l_x0 + 1). Exists (r_x0 + 1). entailer!. 
 do 4 rewrite upd_Znth_map. 
 pattern (sublist r_x0 100 contents_a1) at 1. rewrite <- H8 at 1.
 pattern (sublist r_x0 100 contents_a2) at 1. rewrite <- H9 at 1.
 pattern (sublist (r_x0 + 1) 100 contents_a1) at 1. rewrite <- H8 at 1.
 pattern (sublist (r_x0 + 1) 100 contents_a2) at 1. rewrite <- H9 at 1.
 (*list_simplify. Znth_solve_rec. autorewrite with Znth. *)
 Search upd_Znth app. rewrite !upd_Znth_app2. 
 rewrite !Zlength_sublist. replace (r_x0 - (r_x0 - 0)) with 0 by lia.
 rewrite (sublist_split r_x0 (r_x0 + 1) (Zlength contents_a1)).
 rewrite (sublist_split r_x0 (r_x0 + 1) (Zlength contents_a2)).
 rewrite !sublist_len_1. simpl.
 rewrite !upd_Znth0. rewrite app_cons_assoc. rewrite <- sublist_last_1.
 rewrite app_cons_assoc. rewrite <- sublist_last_1. entailer!.
 lia. lia. lia. lia. lia. lia. lia. lia. lia.
 lia. lia. lia. Print Zlength_sublist.
 rewrite !Zlength_sublist. replace (r_x0 - 0) with r_x0 by lia.
 replace (r_x0 + (Zlength contents_a2 - r_x0)) with (Zlength contents_a2) by lia.
 lia. lia. lia. lia. lia. 
 (*a_1 now*)
 rewrite !Zlength_sublist. replace (r_x0 - 0) with r_x0 by lia.
 replace (r_x0 + (Zlength contents_a1 - r_x0)) with (Zlength contents_a1) by lia.
 lia. lia. lia. lia. lia. 
 (*Second loop*)
 Intros l_x0 r_x0. 
 forward_loop 
  (EX l_x:Z,  
    PROP (0 <= l_x <= M; l_x = r_x0)
   LOCAL (
    temp _l_x (Vint (Int.repr l_x)); temp _r_x (Vint (Int.repr r_x0));
    temp _M (Vint (Int.repr M));
    temp _a_1__1 a_1; temp _a_2__1 a_2; temp _f__1 f
    )(*map.Vint (map Int.repr (sublist 0 l_x contents_f ++ sublist l_x (N * M) contents a_1)) a_1*)
   SEP (data_at sh1 (tarray tuint M) 
   (map Vint (map Int.repr (sublist 0 l_x contents_f ++ sublist l_x M contents_a1))) a_1;
   data_at sh2 (tarray tuint M) 
   (map Vint (map Int.repr (sublist 0 r_x0 contents_f ++ sublist r_x0 M contents_a2))) a_2;
   data_at shf (tarray tuint M) (map Vint (map Int.repr contents_f)) f))%assert
   break: 
   (EX l_x:Z, 
   PROP (0 <= l_x <= M; l_x = M)
   LOCAL (
    temp _l_x (Vint (Int.repr l_x)); temp _r_x (Vint (Int.repr r_x0));
    temp _M (Vint (Int.repr M)); 
    temp _a_1__1 a_1; temp _a_2__1 a_2; temp _f__1 f
   )
  SEP (data_at sh1 (tarray tuint M)
  (map Vint (map Int.repr (sublist 0 l_x contents_f ++ sublist l_x M contents_a1))) a_1; 
  data_at sh2 (tarray tuint M)
  (map Vint (map Int.repr (sublist 0 r_x0 contents_f ++ sublist r_x0 M contents_a2))) a_2; 
  data_at shf (tarray tuint M) (map Vint (map Int.repr contents_f)) f))%assert.
  (*first if*)
  Exists l_x0. entailer!. Intros l_x1. forward_if. forward.
  (*second if*)
  Exists l_x1. entailer!. forward_if. forward.
  (*else*)
  Exists l_x1. entailer!. forward. forward. forward.
  Exists (l_x1 + 1). entailer!.
  (*last loop*)
  Intros l_x1.  
  forward_loop 
  (EX r_x:Z,  
    PROP (0 <= r_x <= M; l_x1 = r_x)
   LOCAL (
    temp _l_x (Vint (Int.repr l_x1)); temp _r_x (Vint (Int.repr r_x));
    temp _M (Vint (Int.repr M));
    temp _a_1__1 a_1; temp _a_2__1 a_2; temp _f__1 f
    )(*map.Vint (map Int.repr (sublist 0 l_x contents_f ++ sublist l_x (N * M) contents a_1)) a_1*)
   SEP (data_at sh1 (tarray tuint M) 
   (map Vint (map Int.repr (sublist 0 l_x1 contents_f ++ sublist l_x1 M contents_a1))) a_1;
   data_at sh2 (tarray tuint M) 
   (map Vint (map Int.repr (sublist 0 r_x contents_f ++ sublist r_x M contents_a2))) a_2;
   data_at shf (tarray tuint M) (map Vint (map Int.repr contents_f)) f))%assert
   break: 
   (EX r_x:Z, 
   PROP (r_x = M)
   LOCAL (
    temp _l_x (Vint (Int.repr l_x1)); temp _r_x (Vint (Int.repr r_x));
    temp _M (Vint (Int.repr M)); 
    temp _a_1__1 a_1; temp _a_2__1 a_2; temp _f__1 f
   )
  SEP (data_at sh1 (tarray tuint M)
  (map Vint (map Int.repr (sublist 0 l_x1 contents_f ++ sublist l_x1 M contents_a1))) a_1; 
  data_at sh2 (tarray tuint M)
  (map Vint (map Int.repr (sublist 0 r_x contents_f ++ sublist r_x M contents_a2))) a_2; 
  data_at shf (tarray tuint M) (map Vint (map Int.repr contents_f)) f))%assert.
  (*first if*)
  Exists r_x0. entailer!. Intros r_x1. forward_if. forward.
  (*second if*)
  Exists r_x1. entailer!. forward_if. forward.
  (*else*)
  Exists r_x1. entailer!. forward. forward. forward.
  Exists (r_x1 + 1). entailer!.
  Intros r_x1. rewrite H18. rewrite H17. 
  rewrite sublist_nil. rewrite sublist_nil.
  rewrite app_nil_r. rewrite sublist_same.
  entailer!. reflexivity. rewrite H10. reflexivity.
Qed.
