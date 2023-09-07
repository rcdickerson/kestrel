(* ================================================================= *)
(* antonoupoulous_sa_simple.c - no array for this*)

Require VC.Preface. 
From Coq Require Import ZArith.Int.
Require Import VST.floyd.proofauto.
Require Import Coq.Classes.RelationClasses.

Require Import VC.barthe_strength_reduction_unsigned.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

(*Functional Model: empty for kestrel*)
(*API spec => verifyfunc spec *)
Definition verifyfunc_spec : ident * funspec :=
DECLARE _verifyfunc
  WITH l_B : Z, l_C : Z, l_N : Z, l_x : Z, r_B : Z, r_C : Z, r_N : Z,
  r_x : Z, l_i : Z, l_j : Z, r_i : Z, r_j : Z 
  PRE [ tuint, tuint, tuint, tuint, tuint, tuint, tuint, tuint, tuint, tuint, tuint, tuint ]  
    (*ensure variables left and right are equal*)
    PROP ( l_B = r_B; l_C = r_C; l_N = r_N; l_x = r_x; 
    0 <= l_B <= Int.max_signed; 0 <= l_C <= Int.max_signed; 
   0 <= l_N <= Int.max_signed; 0 <= l_x <= Int.max_signed;
   0 <= r_B <= Int.max_signed; 0 <= r_C <= Int.max_signed;
   0 <= r_N <= Int.max_signed; 0 <= r_x <= Int.max_signed;
   0 <= l_i <= Int.max_signed; 0 <= l_j <= Int.max_signed;
   0 <= r_i <= Int.max_signed; 0 <= r_j <= Int.max_signed;
   0 <= (l_N * l_B) + l_C < Int.max_signed;
   l_i = 0; r_i = 0; l_j = 0; r_j = r_C )
  PARAMS (Vint (Int.repr l_B); Vint (Int.repr l_C); Vint (Int.repr l_N);
      Vint (Int.repr l_x); Vint (Int.repr r_B); Vint (Int.repr r_C);
      Vint (Int.repr r_N); Vint (Int.repr r_x); Vint (Int.repr l_i);
      Vint (Int.repr l_j); Vint (Int.repr r_i); Vint (Int.repr r_j))
    SEP (TT) (*empty*)
  POST [ tvoid ]
    PROP ( l_B = r_B; l_C = r_C; l_N = r_N; l_x = r_x  ) (* same as pre*)
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
  (EX l_i:Z, EX l_j:Z, EX l_x:Z, EX r_i: Z, EX r_j: Z, EX r_x : Z, 
    PROP ()
   LOCAL (
    temp _l_B (Vint (Int.repr l_B));
    temp _l_C (Vint (Int.repr l_C)); temp _l_N (Vint (Int.repr l_N));
    temp _l_x (Vint (Int.repr l_x)); temp _r_B (Vint (Int.repr r_B));
    temp _r_C (Vint (Int.repr r_C)); temp _r_N (Vint (Int.repr r_N));
    temp _r_x (Vint (Int.repr r_x)); temp _l_i (Vint (Int.repr l_i));
    temp _l_j (Vint (Int.repr l_j)); temp _r_i (Vint (Int.repr r_i));
    temp _r_j (Vint (Int.repr r_j))
    )
   SEP (TT))%assert
   break: 
   (EX l_i:Z, EX l_j: Z, EX l_x:Z, EX r_i: Z, EX r_j: Z, EX r_x : Z, 
   PROP ()
  LOCAL (
   temp _l_B (Vint (Int.repr l_B));
   temp _l_C (Vint (Int.repr l_C)); temp _l_N (Vint (Int.repr l_N));
   temp _l_x (Vint (Int.repr l_x)); temp _r_B (Vint (Int.repr r_B));
   temp _r_C (Vint (Int.repr r_C)); temp _r_N (Vint (Int.repr r_N));
   temp _r_x (Vint (Int.repr r_x)); temp _l_i (Vint (Int.repr l_i));
   temp _l_j (Vint (Int.repr l_j)); temp _r_i (Vint (Int.repr r_i));
   temp _r_j (Vint (Int.repr r_j))
   )
  SEP (TT))%assert.
 (*first existential - outermost*)     
 Exists l_i. Exists l_j. Exists l_x. Exists r_i. Exists r_j. Exists r_x.
 entailer!. Intros l_i0 l_j0 l_x0 r_i0 r_j0 r_x0. forward_if. 
 forward. 
 (*second if - entailer*)
 Exists l_i0. Exists l_j0. Exists l_x0. Exists r_i0. Exists r_j0. Exists r_x0. 
 entailer!. forward_if. forward.
 (*last - else*)
 Exists l_i0. Exists l_j0. Exists l_x0. Exists r_i0. Exists r_j0. Exists r_x0. 
 entailer!. forward. forward. forward. forward. forward. forward. 
 Exists (l_i0 + 1). Exists (l_i0 * l_B + l_C). Exists (l_x0 + ((l_i0 * l_B) + l_C)). Exists (r_i0 + 1). 
 Exists (r_j0 + r_B). Exists (r_x0 + r_j0). entailer!.
 (*second loop*)
 Intros l_i0 l_j0 l_x0 r_i0 r_j0 r_x0.
 forward_loop 
 (EX l_i:Z, EX l_j:Z, EX l_x:Z, EX r_i: Z, EX r_j: Z, EX r_x : Z, 
   PROP ()
  LOCAL (
   temp _l_B (Vint (Int.repr l_B));
   temp _l_C (Vint (Int.repr l_C)); temp _l_N (Vint (Int.repr l_N));
   temp _l_x (Vint (Int.repr l_x)); temp _r_B (Vint (Int.repr r_B));
   temp _r_C (Vint (Int.repr r_C)); temp _r_N (Vint (Int.repr r_N));
   temp _r_x (Vint (Int.repr r_x)); temp _l_i (Vint (Int.repr l_i));
   temp _l_j (Vint (Int.repr l_j)); temp _r_i (Vint (Int.repr r_i));
   temp _r_j (Vint (Int.repr r_j))
   )
  SEP (TT))%assert
  break: 
  (EX l_i:Z, EX l_j: Z, EX l_x:Z, EX r_i: Z, EX r_j: Z, EX r_x : Z, 
  PROP ()
 LOCAL (
  temp _l_B (Vint (Int.repr l_B));
  temp _l_C (Vint (Int.repr l_C)); temp _l_N (Vint (Int.repr l_N));
  temp _l_x (Vint (Int.repr l_x)); temp _r_B (Vint (Int.repr r_B));
  temp _r_C (Vint (Int.repr r_C)); temp _r_N (Vint (Int.repr r_N));
  temp _r_x (Vint (Int.repr r_x)); temp _l_i (Vint (Int.repr l_i));
  temp _l_j (Vint (Int.repr l_j)); temp _r_i (Vint (Int.repr r_i));
  temp _r_j (Vint (Int.repr r_j))
  )
 SEP (TT))%assert.
  (*existential - entailment*)
 Exists l_i0. Exists l_j0. Exists l_x0. Exists r_i0. Exists r_j0. Exists r_x0.
 entailer!.
 Intros l_i1 l_j1 l_x1 r_i1 r_j1 r_x1. forward_if. forward. 
  (*Existential*) Exists l_i1. Exists l_j1. Exists l_x1. 
  Exists r_i1. Exists r_j1. Exists r_x1. entailer!.
  (*second - if*)
  forward_if. forward.
  (*else - existential*) 
  Exists l_i1. Exists l_j1. Exists l_x1. Exists r_i1. Exists r_j1. Exists r_x1.
  entailer!. forward. forward. forward. 
  (*increment*)
  Exists (l_i1 + 1). Exists (l_i1 * l_B + l_C). Exists (l_x1 + ((l_i1 * l_B) + l_C)). 
  Exists r_i1. Exists r_j1. Exists r_x1. entailer!.
  (*third loop*)
  Intros l_i1 l_j1 l_x1 r_i1 r_j1 r_x1.
  forward_loop 
  (EX l_i:Z, EX l_j:Z, EX l_x:Z, EX r_i: Z, EX r_j: Z, EX r_x : Z, 
    PROP ()
   LOCAL (
    temp _l_B (Vint (Int.repr l_B));
    temp _l_C (Vint (Int.repr l_C)); temp _l_N (Vint (Int.repr l_N));
    temp _l_x (Vint (Int.repr l_x)); temp _r_B (Vint (Int.repr r_B));
    temp _r_C (Vint (Int.repr r_C)); temp _r_N (Vint (Int.repr r_N));
    temp _r_x (Vint (Int.repr r_x)); temp _l_i (Vint (Int.repr l_i));
    temp _l_j (Vint (Int.repr l_j)); temp _r_i (Vint (Int.repr r_i));
    temp _r_j (Vint (Int.repr r_j))
    )
   SEP (TT))%assert
   break: 
   (EX l_i:Z, EX l_j: Z, EX l_x:Z, EX r_i: Z, EX r_j: Z, EX r_x : Z, 
   PROP ()
  LOCAL (
   temp _l_B (Vint (Int.repr l_B));
   temp _l_C (Vint (Int.repr l_C)); temp _l_N (Vint (Int.repr l_N));
   temp _l_x (Vint (Int.repr l_x)); temp _r_B (Vint (Int.repr r_B));
   temp _r_C (Vint (Int.repr r_C)); temp _r_N (Vint (Int.repr r_N));
   temp _r_x (Vint (Int.repr r_x)); temp _l_i (Vint (Int.repr l_i));
   temp _l_j (Vint (Int.repr l_j)); temp _r_i (Vint (Int.repr r_i));
   temp _r_j (Vint (Int.repr r_j))
   )
  SEP (TT))%assert.
  (*existential - entailment*)
  Exists l_i1. Exists l_j1. Exists l_x1. Exists r_i1. 
  Exists r_j1. Exists r_x1. entailer!.
  (*first if*)
  Intros l_i2 l_j2 l_x2 r_i2 r_j2 r_x2. forward_if. forward. 
   (*Existential - entailment*) Exists l_i2. Exists l_j2. Exists l_x2. 
   Exists r_i2. Exists r_j2. Exists r_x2. entailer!.
   (*second - if*)
   forward_if. forward.
   (*else - existential*) 
   Exists l_i2. Exists l_j2. Exists l_x2. Exists r_i2. 
   Exists r_j2. Exists r_x2. entailer!. forward. forward. forward. 
   (*increment*)
   Exists l_i2. Exists l_j2. Exists l_x2. Exists (r_i2 + 1). 
   Exists (r_j2 + l_B). Exists (r_x2 + r_j2). entailer!.
   Intros l_i3 l_j3 l_x3 r_i3 r_j3 r_x3. entailer!. 
  Qed.
(*verify main*)
Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  forward. forward. forward. forward. forward. forward.
  forward. forward. forward. forward. forward. forward.
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