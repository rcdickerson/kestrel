(* ================================================================= *)
(* antonoupoulous_sa_simple.c - no array for this*)

Require VC.Preface. 
From Coq Require Import ZArith.Int.
Require Import VST.floyd.proofauto.
Require Import Coq.Classes.RelationClasses.

Require Import VC.antonopoulos_sa_simple.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

(*Functional Model: empty for kestrel*)
(*API spec => verifyfunc spec *)
Definition verifyfunc_spec : ident * funspec :=
DECLARE _verifyfunc
  WITH l_n : Z, r_n : Z, l_x : Z, r_x : Z, l_i : Z, r_i : Z
  PRE [ tint, tint, tint, tint, tint, tint ]  
    (*ensure variables left and right are equal*)
    PROP ( l_n = r_n; l_x = r_x; l_i = r_i; l_x = 0; r_x = 0; l_i = 0; r_i = 0;
    Int.min_signed <= l_n < Int.max_signed;  Int.min_signed <= r_n < Int.max_signed)
    PARAMS (Vint (Int.repr l_n); Vint (Int.repr r_n); Vint (Int.repr l_x);
      Vint (Int.repr r_x); Vint (Int.repr l_i); Vint (Int.repr r_i))
    SEP (TT) (*empty*)
  POST [ tvoid ]
    PROP ( l_n = r_n; l_x = r_x; l_i = r_i  ) (* same as pre*)
    RETURN () (*void*)
    SEP (TT) (*empty*).


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
forward_loop 
   (EX l_i:Z, EX r_i:Z,
    PROP (l_x = r_x;
    (l_i = 0 \/ 0 <= l_i <= l_n + 1); 
    (r_i = 0 \/ 0 <= r_i <= r_n + 1))
   LOCAL (
    temp _r_i (Vint (Int.repr r_i));
    temp _l_i (Vint (Int.repr l_i));
    temp _r_x (Vint (Int.repr r_i));
    temp _l_x (Vint (Int.repr l_i));
    temp _l_n (Vint (Int.repr l_n));
    temp _r_n (Vint (Int.repr r_n))
    )
   SEP (TT))%assert
   break: 
   (EX l_i:Z, EX r_i:Z,
     PROP (l_x = r_x;
     (l_i = 0 \/ 0 <= l_i <= l_n + 1); 
     (r_i = 0 \/ 0 <= r_i <= r_n + 1))
     LOCAL (
      temp _r_i (Vint (Int.repr r_i));
      temp _l_i (Vint (Int.repr l_i));
      temp _r_x (Vint (Int.repr r_i));
      temp _l_x (Vint (Int.repr l_i));
      temp _l_n (Vint (Int.repr l_n));
      temp _r_n (Vint (Int.repr r_n)
     ))
      SEP (TT))%assert.
 (*first existential - outermost*)     
 Exists 0. Exists 0. entailer!.
 Intros l_i0 r_i0. forward_if. forward. 
 (*first if*)
 Exists l_i0. Exists r_i0. entailer!. forward_if.
 forward. 
 (*second if*)
 Exists l_i0. Exists r_i0. entailer!. 
 forward. forward. forward. forward.
 (*plus 1*)
 Exists (l_i0 + 1). Exists (r_i0 + 1). entailer!.
 (*next loop*)
 Intros l_i0. Intros r_i0.
 forward_loop 
 (EX l_i:Z, EX r_i:Z,
    PROP (l_x = r_x;
    (l_i = 0 \/ 0 <= l_i <= l_n + 1); 
    (r_i = 0 \/ 0 <= r_i <= r_n + 1))
   LOCAL (
    temp _r_i (Vint (Int.repr r_i));
    temp _l_i (Vint (Int.repr l_i));
    temp _r_x (Vint (Int.repr r_i));
    temp _l_x (Vint (Int.repr l_i));
    temp _l_n (Vint (Int.repr l_n));
    temp _r_n (Vint (Int.repr r_n))
    )
   SEP (TT))%assert
   break: 
   (EX l_i:Z, EX r_i:Z,
     PROP (l_x = r_x;
     (l_i = 0 \/ 0 <= l_i <= l_n + 1); 
     (r_i = 0 \/ 0 <= r_i <= r_n + 1))
     LOCAL (
      temp _r_i (Vint (Int.repr r_i));
      temp _l_i (Vint (Int.repr l_i));
      temp _r_x (Vint (Int.repr r_i));
      temp _l_x (Vint (Int.repr l_i));
      temp _l_n (Vint (Int.repr l_n));
      temp _r_n (Vint (Int.repr r_n)
     ))
      SEP (TT))%assert.
  (*first exists - 2nd loop*)
  Exists l_i0. Exists r_i0. entailer!.
  Intros l_i1 r_i1. forward_if. forward.
  (*first if - break*)
  Exists l_i1. Exists r_i1. entailer!.
  forward_if. forward. 
  (*Rest*)
  Exists l_i1. Exists r_i1. entailer!. forward.
  forward. 
  (*plus 1*)
  Exists (l_i1 + 1). Exists r_i1. entailer!. 
  (*last for*)
  Intros l_i1 r_i1.
  forward_loop 
 (EX l_i:Z, EX r_i:Z,
    PROP (l_x = r_x;
    (l_i = 0 \/ 0 <= l_i <= l_n + 1); 
    (r_i = 0 \/ 0 <= r_i <= r_n + 1))
   LOCAL (
    temp _r_i (Vint (Int.repr r_i));
    temp _l_i (Vint (Int.repr l_i));
    temp _r_x (Vint (Int.repr r_i));
    temp _l_x (Vint (Int.repr l_i));
    temp _l_n (Vint (Int.repr l_n));
    temp _r_n (Vint (Int.repr r_n))
    )
   SEP (TT))%assert
   break: 
   (EX l_i:Z, EX r_i:Z,
     PROP (l_x = r_x;
     (l_i = 0 \/ 0 <= l_i <= l_n + 1); 
     (r_i = 0 \/ 0 <= r_i <= r_n + 1))
     LOCAL (
      temp _r_i (Vint (Int.repr r_i));
      temp _l_i (Vint (Int.repr l_i));
      temp _r_x (Vint (Int.repr r_i));
      temp _l_x (Vint (Int.repr l_i));
      temp _l_n (Vint (Int.repr l_n));
      temp _r_n (Vint (Int.repr r_n)
     ))
      SEP (TT))%assert.
    (*first exists*)
    Exists l_i1. Exists r_i1. entailer!.
    Intros l_i2 r_i2. forward_if. forward.
    (*first if - break*)
    Exists l_i2. Exists r_i2. entailer!. forward_if.
    forward. 
    (*rest*)
    Exists l_i2. Exists r_i2. entailer!. forward. forward.
    (*plus 1*)
    Exists l_i2. Exists (r_i2 + 1). entailer!. 
    Intros l_i2. Intros r_i2.  entailer!.
Qed.
  
(*verify main*)
Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  forward.
  forward.
  forward.
  forward.
  forward.
  forward.
  forward_call. entailer!. forward.
 Qed.

 #[export] Existing Instance NullExtension.Espec.

Print prog.
Print varspecs.
Print semax_prog.
Lemma prog_correct: semax_prog prog tt Vprog Gprog.
Proof.
prove_semax_prog.

semax_func_cons body_verifyfunc.
semax_func_cons body_main.
Qed.