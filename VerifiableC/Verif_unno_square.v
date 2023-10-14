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
  WITH l_a : Z, l_b : Z, r_a : Z, r_b : Z
  PRE [ tuint, tuint, tuint, tuint ]  
    (*ensure variables left and right are equal*)
    PROP 
    ( 
      0 <= l_a <= Int.max_unsigned;  0 <= r_a <= Int.max_unsigned;
      0 <= l_b <= Int.max_unsigned;  0 <= r_b <= Int.max_unsigned;
      l_a = r_a; l_b = r_b
    )
    PARAMS 
    (
      Vint (Int.repr l_a); Vint (Int.repr l_b);
      Vint (Int.repr r_a); Vint (Int.repr r_b)
    )
    SEP (TT) (*empty*)
  POST [ tvoid ]
    EX l_c:Z, EX r_c:Z,
    PROP ( l_c = r_c  ) (* same as pre*)
    RETURN () (*void*)
    SEP (TT) (*empty*).


(*Pack APIs together*)
Definition Gprog := [verifyfunc_spec].

(*verify fun_spec - from here*)
Lemma body_verifyfunc: semax_body Vprog Gprog f_verifyfunc verifyfunc_spec.
Proof. 
  start_function. fastforward.
  forward_loop 
  (
    EX l_a:Z, EX l_c:Z, EX r_a: Z, EX r_c: Z, 
    PROP 
    (
      0 <= l_a <= Int.max_unsigned;  0 <= r_a <= Int.max_unsigned;
      0 <= l_b <= Int.max_unsigned;  0 <= r_b <= Int.max_unsigned;
      l_a = r_a; l_c = r_c
    )
    LOCAL 
    (
      temp _l_a (Vint (Int.repr l_a));
      temp _l_b (Vint (Int.repr l_b));
      temp _l_c (Vint (Int.repr l_c));
      temp _r_a (Vint (Int.repr r_a));
      temp _r_b (Vint (Int.repr r_b));
      temp _r_c (Vint (Int.repr r_c))
    )
   SEP (TT))%assert
   break: 
   (
    EX l_a:Z, EX l_c:Z, EX r_a: Z, EX r_c: Z, 
    PROP 
    (
      0 <= l_a <= Int.max_unsigned;  0 <= r_a <= Int.max_unsigned;
      0 <= l_b <= Int.max_unsigned;  0 <= r_b <= Int.max_unsigned; 
      l_a = r_a; l_c = r_c; l_a >= l_b; r_a >= r_b
    )
    LOCAL
    (
      temp _l_a (Vint (Int.repr l_a));
      temp _l_b (Vint (Int.repr l_b));
      temp _l_c (Vint (Int.repr l_c));
      temp _r_a (Vint (Int.repr r_a));
      temp _r_b (Vint (Int.repr r_b));
      temp _r_c (Vint (Int.repr r_c))
    )
  SEP (TT))%assert.
 (*first existential - outermost*)     
 Exists l_a. Exists 0. Exists r_a. Exists 0.  entailer!. 
 Intros l_a0 l_c0 r_a0 r_c0. forward_if. forward. 
 (*first if*)
 Exists l_a0. Exists l_c0. Exists r_a0. Exists r_c0. entailer!. 
 forward_if. forward. 
 Exists l_a0. Exists l_c0. Exists r_a0. Exists r_c0. entailer!. fastforward.
 Exists (l_a0 + 1). Exists (l_c0 + l_a0 * l_a0). Exists (r_a0 + 1). Exists (r_c0 + r_a0 * r_a0).
 entailer!.
 (*second loop*)
 Intros l_a0 l_c r_a0 r_c.
 forward_loop 
  (
    EX l_a:Z, EX l_c:Z, EX r_a: Z, EX r_c: Z, 
    PROP 
    (
      0 <= l_a <= Int.max_unsigned;  0 <= r_a <= Int.max_unsigned;
      0 <= l_b <= Int.max_unsigned;  0 <= r_b <= Int.max_unsigned; 
      l_a = r_a; l_c = r_c; l_a >= l_b; r_a >= r_b
    )
    LOCAL 
    (
      temp _l_a (Vint (Int.repr l_a));
      temp _l_b (Vint (Int.repr l_b));
      temp _l_c (Vint (Int.repr l_c));
      temp _r_a (Vint (Int.repr r_a));
      temp _r_b (Vint (Int.repr r_b));
      temp _r_c (Vint (Int.repr r_c))
    )
    SEP (TT)
  )%assert
  break: 
  (
    EX l_a:Z, EX l_c:Z, EX r_a: Z, EX r_c: Z, 
    PROP 
    (
      0 <= l_a <= Int.max_unsigned;  0 <= r_a <= Int.max_unsigned;
      0 <= l_b <= Int.max_unsigned;  0 <= r_b <= Int.max_unsigned; 
      l_a = r_a; l_c = r_c; l_a >= l_b; r_a >= r_b
    )
    LOCAL 
    (
      temp _l_a (Vint (Int.repr l_a));
      temp _l_b (Vint (Int.repr l_b));
      temp _l_c (Vint (Int.repr l_c));
      temp _r_a (Vint (Int.repr r_a));
      temp _r_b (Vint (Int.repr r_b));
      temp _r_c (Vint (Int.repr r_c))
    )
    SEP (TT))%assert.
  (*existential*)
  Exists l_a0. Exists l_c. Exists r_a0. Exists r_c. entailer!.
  Intros l_a1 l_c1 r_a1 r_c1. forward_if. forward. 
  (*Existential*) Exists l_a1. Exists l_c1. Exists r_a1. Exists r_c1.
  entailer!. forward_if. forward. contradiction.  contradiction.
  (*third loop*)
  Intros l_a1 l_c1 r_a1 r_c1.  
  forward_loop 
  (
    EX l_a:Z, EX l_c:Z, EX r_a: Z, EX r_c: Z, 
    PROP 
    (
      0 <= l_a <= Int.max_unsigned;  0 <= r_a <= Int.max_unsigned;
      0 <= l_b <= Int.max_unsigned;  0 <= r_b <= Int.max_unsigned; 
      l_a = r_a; l_c = r_c; l_a >= l_b; r_a >= r_b
    )
    LOCAL 
    (
      temp _l_a (Vint (Int.repr l_a));
      temp _l_b (Vint (Int.repr l_b));
      temp _l_c (Vint (Int.repr l_c));
      temp _r_a (Vint (Int.repr r_a));
      temp _r_b (Vint (Int.repr r_b));
      temp _r_c (Vint (Int.repr r_c))
    )
    SEP (TT))%assert
   break: 
   (
    EX l_a:Z, EX l_c:Z, EX r_a: Z, EX r_c: Z, 
    PROP 
    (
      0 <= l_a <= Int.max_unsigned;  0 <= r_a <= Int.max_unsigned;
      0 <= l_b <= Int.max_unsigned;  0 <= r_b <= Int.max_unsigned; 
      l_a = r_a; l_c = r_c; l_a >= l_b; r_a >= r_b
    )
    LOCAL 
    (
      temp _l_a (Vint (Int.repr l_a));
      temp _l_b (Vint (Int.repr l_b));
      temp _l_c (Vint (Int.repr l_c));
      temp _r_a (Vint (Int.repr r_a));
      temp _r_b (Vint (Int.repr r_b));
      temp _r_c (Vint (Int.repr r_c))
    )
    SEP (TT)
  )%assert.
  Exists l_a1. Exists l_c1. Exists r_a1. Exists r_c1. entailer!.
  Intros l_a2 l_c2 r_a2 r_c2. forward_if. forward.
  (*Existential*) Exists l_a2. Exists l_c2. Exists r_a2. Exists r_c2.
  entailer!. contradiction.
  (*last - else part*)
  Intros l_a2 l_c2 r_a2 r_c2. Exists l_c2. Exists r_c2. entailer!.
  Qed.

