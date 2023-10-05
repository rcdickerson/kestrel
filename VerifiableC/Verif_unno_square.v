(* ================================================================= *)
(* antonoupoulous_sa_simple.c - no array for this*)

Require VC.Preface. 
From Coq Require Import ZArith.Int.
Require Import VST.floyd.proofauto.
Require Import Coq.Classes.RelationClasses.

Require Import VC.unno_square_sum.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

(*Functional Model: empty for kestrel*)
(*API spec => verifyfunc spec *)
Definition verifyfunc_spec : ident * funspec :=
DECLARE _verifyfunc
  WITH l_a : Z, l_b : Z, l_c : Z, r_a : Z, r_b : Z, r_c : Z
  PRE [ tuint, tuint, tuint, tuint, tuint, tuint ]  
    (*ensure variables left and right are equal*)
    PROP ( l_a = r_a; l_b = r_b; l_c = r_c; l_c = 0; r_c = 0;
    0 <= l_c <= Int.max_signed; 0 <= r_c <= Int.max_signed; 
   0 <= l_b <= Int.max_signed; 0 <= r_b <= Int.max_signed;
   0 <= l_a <= Int.max_signed; 0 <= r_a <= Int.max_signed;
   0 <= l_a * l_a <= Int.max_signed; 0 <= r_a * r_a <= Int.max_signed)
    PARAMS (Vint (Int.repr l_a); Vint (Int.repr l_b); Vint (Int.repr l_c);
      Vint (Int.repr r_a); Vint (Int.repr r_b); Vint (Int.repr r_c))
    SEP (TT) (*empty*)
  POST [ tvoid ]
    PROP ( l_a = r_a; l_b = r_b; l_c = r_c  ) (* same as pre*)
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
  (EX l_a:Z, EX l_c:Z, EX r_a: Z, EX r_c: Z, 
    PROP ()
   LOCAL (
    temp _l_a (Vint (Int.repr l_a));
    temp _l_b (Vint (Int.repr l_b));
    temp _l_c (Vint (Int.repr l_c));
    temp _r_a (Vint (Int.repr r_a));
    temp _r_b (Vint (Int.repr r_b));
    temp _r_c (Vint (Int.repr r_c))
    )
   SEP (TT))%assert
   break: 
   (EX l_a:Z, EX l_c:Z, EX r_a: Z, EX r_c: Z, 
   PROP ()
  LOCAL (
   temp _l_a (Vint (Int.repr l_a));
   temp _l_b (Vint (Int.repr l_b));
   temp _l_c (Vint (Int.repr l_c));
   temp _r_a (Vint (Int.repr r_a));
   temp _r_b (Vint (Int.repr r_b));
   temp _r_c (Vint (Int.repr r_c))
   )
  SEP (TT))%assert.
 (*first existential - outermost*)     
 Exists l_a. Exists l_c. Exists r_a. Exists r_c.  entailer!. 
 Intros l_a0 l_c0 r_a0 r_c0. forward_if. forward. 
 (*first if*)
 Exists l_a0. Exists l_c0. Exists r_a0. Exists r_c0. entailer!. forward_if.
 forward. 
 Exists l_a0. Exists l_c0. Exists r_a0. Exists r_c0. entailer!. 
 forward. forward. forward. forward. 
 Exists (l_a0 + 1). Exists (l_c0 + l_a0 * l_a0). Exists (r_a0 + 1). Exists (r_c0 + r_a0 * r_a0).
 entailer!.
 (*second loop*)
 Intros l_a0 l_c0 r_a0 r_c0.
 forward_loop 
  (EX l_a:Z, EX l_c:Z, EX r_a: Z, EX r_c: Z, 
    PROP ()
   LOCAL (
    temp _l_a (Vint (Int.repr l_a));
    temp _l_b (Vint (Int.repr l_b));
    temp _l_c (Vint (Int.repr l_c));
    temp _r_a (Vint (Int.repr r_a));
    temp _r_b (Vint (Int.repr r_b));
    temp _r_c (Vint (Int.repr r_c))
    )
   SEP (TT))%assert
   break: 
   (EX l_a:Z, EX l_c:Z, EX r_a: Z, EX r_c: Z, 
   PROP ()
  LOCAL (
   temp _l_a (Vint (Int.repr l_a));
   temp _l_b (Vint (Int.repr l_b));
   temp _l_c (Vint (Int.repr l_c));
   temp _r_a (Vint (Int.repr r_a));
   temp _r_b (Vint (Int.repr r_b));
   temp _r_c (Vint (Int.repr r_c))
   )
  SEP (TT))%assert.
  (*existential*)
  Exists l_a0. Exists l_c0. Exists r_a0. Exists r_c0. entailer!.
  Intros l_a1 l_c1 r_a1 r_c1. forward_if. forward. 
  (*Existential*) Exists l_a1. Exists l_c1. Exists r_a1. Exists r_c1.
  entailer!. forward_if. forward. 
  Exists l_a1. Exists l_c1. Exists r_a1. Exists r_c1. entailer!. forward.
  forward. 
  (*increment*)
  Exists (l_a1 + 1). Exists (l_c1 + l_a1 * l_a1). Exists r_a1. Exists r_c1.
  entailer!. 
  (*third loop*)
  Intros l_a1 l_c1 r_a1 r_c1.  
  forward_loop 
  (EX l_a:Z, EX l_c:Z, EX r_a: Z, EX r_c: Z, 
    PROP ()
   LOCAL (
    temp _l_a (Vint (Int.repr l_a));
    temp _l_b (Vint (Int.repr l_b));
    temp _l_c (Vint (Int.repr l_c));
    temp _r_a (Vint (Int.repr r_a));
    temp _r_b (Vint (Int.repr r_b));
    temp _r_c (Vint (Int.repr r_c))
    )
   SEP (TT))%assert
   break: 
   (EX l_a:Z, EX l_c:Z, EX r_a: Z, EX r_c: Z, 
   PROP ()
  LOCAL (
   temp _l_a (Vint (Int.repr l_a));
   temp _l_b (Vint (Int.repr l_b));
   temp _l_c (Vint (Int.repr l_c));
   temp _r_a (Vint (Int.repr r_a));
   temp _r_b (Vint (Int.repr r_b));
   temp _r_c (Vint (Int.repr r_c))
   )
  SEP (TT))%assert.
  Exists l_a1. Exists l_c1. Exists r_a1. Exists r_c1. entailer!.
  Intros l_a2 l_c2 r_a2 r_c2. forward_if. forward.
  (*Existential*) Exists l_a2. Exists l_c2. Exists r_a2. Exists r_c2.
  entailer!. forward_if. forward.
  (*last - else part*)
  Exists l_a2. Exists l_c2. Exists r_a2. Exists r_c2. entailer!.
  forward. forward.
  (*increment part*)
  Exists l_a2. Exists l_c2. Exists (r_a2 + 1). Exists (r_c2 + r_a2 * r_a2).
  entailer!. Intros l_a2 l_c2 r_a2 r_c2. entailer!.
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