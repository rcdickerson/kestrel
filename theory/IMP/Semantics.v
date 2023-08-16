(** * Imp: Simple Imperative Programs *)

(* This definition is largely identical to the one in Programming
   Language Foundations, except that the definitions are now
   parametric in the set of variable identifiers. *)

Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lia.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
Import ListNotations.

From Common Require Import Id Fixpoints.

From stdpp Require Export prelude fin_maps fin_map_dom.
From Imp Require Import Syntax.

Section Semantics.

  (* The type of variables identifiers. *)
  Context {I : Type}.
  Context {M : Type -> Type}.
  Context {id : Id I M}.

  Import Syntax.notations.

  (* ================================================================= *)
  (** ** States *)

  (** In contrast to PLF, we're going to use stdpp's finite map library
      to represent states.

    A _machine state_ (or just _state_) represents the current values
    of _all_ variables at some point in the execution of a program. *)
 
  Definition state := M nat.

  Inductive result : Type :=
    | RNormal : state -> result
    | RError : result.


  Fixpoint aeval (st : state) (a : aexp) : nat :=
    match a with
    | ANum n => n
    | AId x => st !!! x
    | <{a1 + a2}> => (aeval st a1) + (aeval st a2)
    | <{a1 - a2}> => (aeval st a1) - (aeval st a2)
    | <{a1 * a2}> => (aeval st a1) * (aeval st a2)
    end.

  Fixpoint beval (st : state) (b : bexp) : bool :=
    match b with
    | <{true}>      => true
    | <{false}>     => false
    | <{a1 = a2}>   => (aeval st a1) =? (aeval st a2)
    | <{a1 <= a2}>  => (aeval st a1) <=? (aeval st a2)
    | <{~ b1}>      => negb (beval st b1)
    | <{b1 && b2}>  => andb (beval st b1) (beval st b2)
    end.

(* ################################################################# *)
(** * Evaluating Commands *)

(** Next we need to define what it means to evaluate an Imp command.
    The fact that [while] loops don't necessarily terminate makes
    defining an evaluation function tricky... *)

(* ----------------------------------------------------------------- *)
(** *** Operational Semantics - including result *)

(** Here is an informal definition of evaluation, presented as inference
    rules for readability:

                           -----------------                            (E_Skip)
                           st =[ skip ]=> RNormal st

                           aeval st a = n
                   -------------------------------                      (E_Ass)
                   st =[ x := a ]=> RNormal (x !-> n ; st)

                           st  =[ c1 ]=> RNormal st'
                           st' =[ c2 ]=> r
                         ---------------------                           (E_SeqNormal)
                         st =[ c1;c2 ]=> r


                           st  =[ c1 ]=> RError
                         ---------------------                           (E_SeqError)
                         st =[ c1;c2 ]=> RError

                          beval st b = true
                           st =[ c1 ]=> r
                --------------------------------------               (E_IfTrue)
                st =[ if b then c1 else c2 end ]=> r

                         beval st b = false
                           st =[ c2 ]=> r
                --------------------------------------              (E_IfFalse)
                st =[ if b then c1 else c2 end ]=> r

                         beval st b = false
                    -----------------------------                 (E_WhileFalse)
                    st =[ while b do c end ]=> RNormal st

                          beval st b = true
                           st =[ c ]=> RNormal st'
                  st' =[ while b do c end ]=> r
                  --------------------------------                 (E_WhileTrueNormal)
                  st  =[ while b do c end ]=> r

                           beval st b = true
                          st =[ c ]=> RError
                  --------------------------------                 (E_WhileTrueError)
                  st  =[ while b do c end ]=> RError

                            beval st b = true
                --------------------------------------              (E_AssertNormal)
                     st =[ assert b ]=> RNormal st


                          beval st b = false
                --------------------------------------              (E_AssertError)
                     st =[ assert b ]=> RError
*)

Reserved Notation
         "st '=[' c ']=>' r"
         (at level 40, c custom com at level 99,
          st constr, r constr at next level).

Inductive cevalr : com -> state -> result -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> RNormal st
  | E_Ass  : forall st a n x,
      aeval st a = n ->
      st =[ x := a ]=> RNormal (<[x := n]> st)
  | E_SeqNormal : forall c1 c2 st st' r,
      st  =[ c1 ]=> RNormal st'  ->
      st' =[ c2 ]=> r ->
      st  =[ c1 ; c2 ]=> r
  | E_SeqError : forall c1 c2 st,
      st  =[ c1 ]=> RError ->
      st  =[ c1 ; c2 ]=> RError
  | E_IfTrue : forall st r b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> r ->
      st =[ if b then c1 else c2 end]=> r
  | E_IfFalse : forall st r b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> r ->
      st =[ if b then c1 else c2 end]=> r
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> RNormal st
  | E_WhileTrueNormal : forall st st' r b c,
      beval st b = true ->
      st  =[ c ]=> RNormal st' ->
      st' =[ while b do c end ]=> r ->
      st  =[ while b do c end ]=> r
  | E_WhileTrueError : forall st b c,
      beval st b = true ->
      st  =[ c ]=> RError ->
      st =[ while b do c end ]=> RError
  | E_AssertNormal : forall st b,
      beval st b = true ->
      st =[ assert b ]=> RNormal st
  | E_AssertError : forall st b,
      beval st b = false ->
      st =[ assert b]=> RError

  where "st =[ c ]=> r" := (cevalr c st r).


(* ================================================================= *)
(** ** Determinism of Evaluation *)

Theorem ceval_deterministic: forall c st r1 r2,
     st =[ c ]=> r1  ->
     st =[ c ]=> r2 ->
     r1 = r2.
Proof.
  intros c st r1 r2 E1 E2.
  generalize dependent r2.
  induction E1; intros r2 E2; inversion E2; subst.
  - (* E_Skip *) reflexivity.
  - (* E_Ass *) reflexivity.
  - (* E_Seq *) 
    specialize IHE1_1 with (RNormal st'0). apply IHE1_1 in H1. inversion H1; subst.
    apply IHE1_2. assumption.
  - (* E_IfTrue, b evaluates to true *)
     specialize IHE1_1 with RError. apply IHE1_1 in H3. discriminate H3.
  - specialize IHE1 with (RNormal st'). apply IHE1 in H1. discriminate H1.
  - reflexivity.
  - apply IHE1. assumption.
  - (* E_IfTrue,  b evaluates to false (contradiction) *)
      rewrite H in H5. discriminate.
  - (* E_IfFalse, b evaluates to true (contradiction) *)
      rewrite H in H5. discriminate.
  - (* E_IfFalse, b evaluates to false *)
      apply IHE1. assumption.
  - (* E_WhileFalse, b evaluates to false *)
    reflexivity.
  - (* E_WhileFalse, b evaluates to true (contradiction) *)
    rewrite H in H2. discriminate.
  - (* E_WhileTrue Error*)
    rewrite H in H2. discriminate.
  - (* E_WhileTrueNormal, contradiction *)
    rewrite H in H4. discriminate H4.
  - specialize IHE1_1 with (RNormal st'0). apply IHE1_1 in H3.
    inversion H3; subst. apply IHE1_2. assumption.
  - apply IHE1_1 with RError in H5. discriminate H5.
  - rewrite H in H4. discriminate H4.
  - apply IHE1 with (RNormal st') in H3. discriminate H3.
  - reflexivity.
  - reflexivity.
  - rewrite H in H1. discriminate H1.
  - rewrite H in H1. discriminate H1.
  - reflexivity.
Qed.

Definition AExpDom := PSet (nat * state)%type.
Definition BExpDom := PSet (bool * state)%type.
Definition ComDom := PSet (state * result)%type.

Reserved Notation "'[[' a ']]A'" (at level 40).
Reserved Notation "'[[' b ']]B'" (at level 40).
Reserved Notation "'[[' c ']]'" (at level 40).

Declare Scope denote_scope.

Notation "{{ v | P }}" := (fun v => P) (v pattern) : denote_scope.

Open Scope denote_scope.

(* ====== Denotational Semantics of Arithmetic Expressions ======= *)

(* The semantic domain for arithmetic expressions is pairs of states
   and numbers: *)

(* ⟦n⟧A ≡ {(σ, n)}
   ⟦x⟧A ≡ {(σ, σ(x))}
   ⟦a1+a2⟧A ≡ {(σ, n + m) | (σ, n) ∈ ⟦a1⟧A ∧ (σ, m) ∈ ⟦a2⟧A}
   ⟦a1-a2⟧A ≡ {(σ, n - m) | (σ, n) ∈ ⟦a1⟧A  ∧ (σ, m) ∈ ⟦a2⟧A}
   ⟦a1*a2⟧A ≡ {(σ, n * m) | (σ, n) ∈ ⟦a1⟧A  ∧ (σ, m) ∈ ⟦a2⟧A} *)
Fixpoint denote_A (a : aexp) : AExpDom :=
  match a with
  | ANum n => {{ ( m, st ) | m = n }}

  (* ⟦x⟧A ≡ {(σ, σ(x))} *)
  | AId x  => {{ ( m, st ) |  m = st !!! x }}

  (* ⟦a1+a2⟧A ≡ {(σ, n + m) | (σ, n) ∈ ⟦a1⟧A ∧ (σ, m) ∈ ⟦a2⟧A} *)
  | <{a1 + a2}> => {{ (n', st) |
                      exists v1 v2,
                      (v1, st) ∈ [[ a1 ]]A
                      /\ (v2, st) ∈ [[ a2 ]]A
                      /\ n' = v1 + v2 }}

  (* ⟦a1-a2⟧A ≡ {(σ, n - m) | (σ, n) ∈ ⟦a1⟧A  ∧ (σ, m) ∈ ⟦a2⟧A} *)
  | <{a1 - a2}> => {{ (n', st) |
                      exists v1 v2,
                      (v1, st) ∈ [[ a1 ]]A
                      /\ (v2, st) ∈ [[ a2 ]]A
                      /\ n' = v1 - v2 }}

  (* ⟦a1*a2⟧A ≡ {(σ, n * m) | (σ, n) ∈ ⟦a1⟧A  ∧ (σ, m) ∈ ⟦a2⟧A} *)
  | <{a1 * a2}> => {{ (n', st) |
                      exists v1 v2,
                      (v1, st) ∈ [[ a1 ]]A
                      /\ (v2, st) ∈ [[ a2 ]]A
                      /\ n' = v1 * v2 }}
  end
where "'[[' a ']]A'" := (denote_A a).

(* We can already state and prove some interesting properties about
   our denotation function!

   Firstly, there exists (at most) one corresponding value for each
   state in the denotation of an expression. This captures a notion of
   determinism for an expression. *)

Theorem aexp_eqv_unique :
  forall (a : aexp)
         (m n : nat)
         (st : state),
    (m, st) ∈ ([[a ]]A) ->
    (n, st) ∈ ([[a ]]A) ->
    m = n.
Proof.
  induction a; simpl; intros;
    In_inversion; eauto; congruence.
Qed.


(* Secondly, there exists exactly one corresponding value for each
   state in the denotation of an expression. *)
Theorem denote_aexp_defined :
  forall (a : aexp) (st : state),
  exists n, (n, st) ∈ [[a]]A.
Proof.
  intros; induction a; destruct_ex.
  - eexists _; set_solver.
  - eexists _; set_solver.
  - eexists _; simpl; In_intro; set_solver.
  - eexists _; simpl; In_intro; set_solver.
  - eexists _; simpl; In_intro; set_solver.
Qed.

(* ====== Denotational Semantics of Boolean Expressions ======= *)

(* The semantic domain for boolean expressions is pairs of states
   and booleans:

   ⟦true⟧B ≡ {(σ, true)}
   ⟦false⟧B ≡ {(σ, false)}
   ⟦a1 == a2⟧B ≡ {(σ, n =? m) | (σ, n) ∈ ⟦a1⟧B ∧ (σ, m) ∈ ⟦a2⟧B}
   ⟦a1 <= a2⟧B ≡ {(σ, n <=? m) | (σ, n) ∈ ⟦a1⟧B  ∧ (σ, m) ∈ ⟦a2⟧B}
   ⟦b1 && b2⟧B ≡ {(σ, v1 && v2) | (σ, v1) ∈ ⟦b1⟧B  ∧ (σ, v2) ∈ ⟦b2⟧B} *)
Fixpoint denote_B (b : bexp) : BExpDom :=
  match b with
  | <{true}> => {{ (v, st) | v = true }}

  | <{false}> => {{ (v, st) | v = false }}

  | <{a1 = a2}> => {{ (v, st) |
    exists v1 v2,
    (v1, st) ∈ [[ a1 ]]A /\ (v2, st) ∈ [[ a2 ]]A
    /\ (v1 = v2 <-> v = true)}}

  | <{ a1 <= a2}> => {{ (v, st) |
    exists v1 v2,
    (v1, st) ∈ [[ a1 ]]A /\ (v2, st) ∈ [[ a2 ]]A
    /\ (v1 <= v2 <-> v = true) }}

  | <{~ b1}> => {{ (v, st) |  (negb v, st) ∈ [[ b1 ]]B }}

  | <{b1 && b2}> => {{ (v, st) |
    exists v1 v2,
    (v1, st) ∈ [[ b1 ]]B /\ (v2, st) ∈ [[ b2 ]]B
    /\ v = (andb v1 v2) }}

  (* Uncomment to account for larger set of boolean expressions in SF. *)

  (* | <{a1 <> a2}> => {{ (v, st) |
    exists v1 v2,
    (v1, st) ∈ [[ a1 ]]A /\ (v2, st) ∈ [[ a2 ]]A
    /\ (v1 = v2 <-> v = false) }}

  | <{ a1 > a2}> => {{ (v, st) |
    exists v1 v2,
    (v1, st) ∈ [[ a1 ]]A /\ (v2, st) ∈ [[ a2 ]]A
    /\ (v1 > v2 <-> v = true) }} *)
  end
where "'[[' b ']]B'" := (denote_B b).


Lemma bexp_denote : forall (b : bexp) (v : bool) st,
    [[b ]]B (v, st) → (v, st) ∈ [[b ]]B.
Proof.
 induction b; simpl; intros; firstorder.
Qed.



Lemma bexp_eqv_unique : forall (b : bexp) (v1 v2 : bool) st,
    (v1, st) ∈ [[b ]]B → (v2, st) ∈ [[b ]]B → v1 = v2.
Proof.
  induction b; simpl; intros;
    In_inversion; eauto; simpl in *;
    try (generalize (aexp_eqv_unique _ _ _ _ H H0);
         generalize (aexp_eqv_unique _ _ _ _ H1 H3);
         intros; subst).
  - destruct (Nat.eq_dec v0 v5); intros; subst;
      firstorder; simpl in *;
      destruct v1; destruct v2;
      first [congruence | tauto].
  - destruct (Nat.le_dec v0 v5); intros; subst;
            firstorder; simpl in *;
      destruct v1; destruct v2;
      first [congruence | tauto].
  - destruct v1; destruct v2; simpl in *; eauto.
  - rewrite (IHb2 _ _ _ H1 H3),
      (IHb1 _ _ _ H H0); reflexivity.
Qed.

(* ======== Denotational Semantics of Imp Commands ========= *)

(* The semantic domain for commands is pairs of initial and final
   states: *)

(*⟦skip⟧C ≡ {(σ, σ)}
  ⟦x:=a⟧C ≡ {(σ, [x↦v]σ) | (σ, v) ∈ ⟦a⟧A }
  ⟦c1;c2⟧C ≡ {(σ1, σ3) | ∃σ2.    (σ1, σ2) ∈ ⟦c1⟧c
                                     ⋀ (σ2, σ3) ∈ ⟦c2⟧c}
  ⟦if b then ct else ce⟧C ≡
     {(σ1, σ2) | (σ1, true) ∈ ⟦eB⟧B ⋀ (σ1, σ2) ∈ ⟦ct⟧C }
   ∪ {(σ1, σ2) | (σ1, false) ∈ ⟦eB⟧B ⋀ (σ1, σ2) ∈ ⟦ce⟧C}

  ⟦while b do c end⟧C ≡ LFP F

  where
  F(rec) = {(σ, σ) | (σ, false) ∈ ⟦b⟧B}
           ∪ {(σ1, σ3) | (σ1, true) ∈ ⟦b⟧B
                              ∧ ∃σ2. (σ1, σ2) ∈ ⟦c⟧c
                                      ⋀ (σ2, σ3) ∈ rec} *)

(*The denotation of while loops uses the least fixed point [LFP]
  combinator defined in FixpointsJ.v. *)

Fixpoint denote_Com (c : com)
  : ComDom :=
  match c with
  | <{ skip }> =>
    {{ (st, st')| st' = RNormal st }}
  | <{x := a1}> => {{ (st, st') | exists v,
                               (v, st) ∈ [[a1]]A
                               /\ st' = RNormal (<[x := v]>st) }}

  | <{c1; c2}> => {{ (st, st') |
                   (exists st'',
                   (st, RNormal st'') ∈ [[c1]] /\ (st'', st') ∈ [[c2]]) 
                 \/ ((st, RError) ∈ [[c1]] /\ st' = RError)}}
 
  | <{ if b then c1 else c2 end }> =>
    {{ (st, st') |
      ((true, st) ∈ [[b]]B /\ (st, st') ∈ [[c1]])
      \/ ((false, st) ∈ [[b]]B /\ (st, st') ∈ [[c2]]) }}

  | <{ while b do c end }> =>
    LFP (fun (phi : PSet _) =>
           {{ (st, st') |
              ((false, st) ∈ [[b]]B /\ st' = RNormal st)
               \/ (exists st'', (*TrueNormal*)
                      (true, st) ∈ [[b]]B /\
                      (st, RNormal st'') ∈ [[c]]
                      /\  (st'', st') ∈ phi)
               \/ ((true, st) ∈ [[b]]B /\ (*True *)
                      (st, RError) ∈ [[c]]
                      /\  st' = RError)}})
  | <{ assert b }> => {{ (st, st') | ((true, st) ∈ [[b]]B /\ st' = RNormal st)
     \/ ((false, st) ∈ [[b]]B /\ st' = RError )}}


  end
where "'[[' c ']]'" := (denote_Com c). 


(*Fixpoint denote_Com (c : com)
  : ComDom :=
  match c with
  | <{ skip }> =>
    {{ (st, st')| st' = RNormal st }}
  | <{x := a1}> => {{ (st, st') | exists v,
                               (v, st) ∈ [[a1]]A
                               /\ st' = RNormal (<[x := v]>st) }}

  | <{c1; c2}> => {{ (st, st') |
                   (exists st'' st''',
                   (st, RNormal st'') ∈ [[c1]] /\ (st'', RNormal st''') ∈ [[c2]]
                   /\ st' = RNormal st''') }}
 
  | <{ if b then c1 else c2 end }> =>
    {{ (st, st') |
      (exists st'', (true, st) ∈ [[b]]B /\ (st, RNormal st'') ∈ [[c1]] /\ st' = RNormal st'')
      \/ (exists st'', (false, st) ∈ [[b]]B /\ (st, RNormal st'') ∈ [[c2]] /\ st' = RNormal st'')}}

  | <{ while b do c end }> =>
    LFP (fun (phi : PSet _) =>
           {{ (st, st') |
              ((false, st) ∈ [[b]]B /\ st' = RNormal st)
               \/ (exists st'' st''', (*TrueNormal*)
                      (true, st) ∈ [[b]]B /\
                      (st, RNormal st'') ∈ [[c]]
                      /\  (st'', RNormal st''') ∈ phi /\ st' = RNormal st''')
              }})
  | <{ assert b }> => {{ (st, st') | ((true, st) ∈ [[b]]B /\ st' = RNormal st)}}


  end
where "'[[' c ']]'" := (denote_Com c). *)


(* To show that LFP is a proper fixed point in subsequent proofs, we
   need to show that if is applied to a monotone function. *)
Lemma while_body_monotone :
  forall b c,
    Monotone (fun (phi : PSet _) =>
           {{ (st, st') |
              ((false, st) ∈ [[b]]B /\ st' = RNormal st)
               \/ (exists st'', (*TrueNormal*)
                      (true, st) ∈ [[b]]B /\
                      (st, RNormal st'') ∈ [[c]]
                      /\  (st'', st') ∈ phi)
                \/ ((true, st) ∈ [[b]]B /\ (*Error *)
                      (st, RError) ∈ [[c]]
                      /\  st' = RError)
                }}).
Proof.
  unfold Monotone, subseteq, set_subseteq_instance; intros.
  destruct x; unfold elem_of in *; In_inversion.
  - subst; left; split; try assumption; reflexivity.
  - right. left. eexists. intuition eauto.     
  - subst. right. right. split. eassumption. split.
    eassumption. reflexivity. 
Qed.

(* Finally, we can show that the denotational and big-step operational
   semantics of Imp are equivalent:

   - Our big-step operational semantics is /sound/ with respect to the
     denotational semantics-- if a command or expression only evaluate
     to elements of their denotation. *)
Lemma Denotational_A_BigStep_Sound :
  forall a st,
    (aeval st a, st) ∈ [[a]]A.
Proof.
  intros;
    induction a; simpl; try solve [constructor]; In_intro;
    repeat split; try eassumption.
Qed.

Lemma Denotational_B_BigStep_Sound :
  forall b st,
    (beval st b, st) ∈ [[b]]B.
Proof.
  induction b; simpl; intros; In_inversion; In_intro; simpl; eauto;
    try apply Denotational_A_BigStep_Sound.
  - split; intros.
    + rewrite H; eapply PeanoNat.Nat.eqb_refl.
    + eapply PeanoNat.Nat.eqb_eq; assumption.
  - split; intros.
    + apply Nat.leb_le; auto.
    + apply Nat.leb_le; auto.
  - rewrite negb_involutive; eapply IHb.
Qed.

Lemma BigStep_Denotational_Sound :
  forall c st st',
    st =[c]=> st' -> (st, st') ∈ [[c]].
Proof.
  intros. induction H.
  (*skip*)
  constructor. rewrite <- H. econstructor.
  (*Assignment*)
  split. eapply Denotational_A_BigStep_Sound. reflexivity.
  (*Sequence - Normal*)
  econstructor. eexists. split. eassumption. eauto.
  (*Sequence - Error*)
  simpl. right. split. assumption. reflexivity.
  (*If - true*)
  left. split. rewrite <- H. apply Denotational_B_BigStep_Sound. assumption.
  (*if - false*)
  right. split. rewrite <- H. apply Denotational_B_BigStep_Sound. assumption.
  (*while - false*)
  simpl. intros. apply LFP_unfold.  apply while_body_monotone. left. split.
  rewrite <- H. apply Denotational_B_BigStep_Sound. reflexivity.
  (*while - true normal*)
  simpl. apply LFP_unfold. apply while_body_monotone. right. left.
  eexists. split. rewrite <- H. apply Denotational_B_BigStep_Sound.
  split. eassumption. eassumption.
  (*while - true error*)
  simpl. apply LFP_unfold. apply while_body_monotone. right. right.
  split. rewrite <- H. apply Denotational_B_BigStep_Sound. split.
  assumption. reflexivity.
  (*assert : true*)
  left. split. rewrite <- H.  apply Denotational_B_BigStep_Sound. reflexivity.
  (*assert : false*)
  right. split. rewrite <- H.  apply Denotational_B_BigStep_Sound. reflexivity.
Qed.

(* Similarly, our denotational semantics is adequate with respect to
   our big-step semantics-- when executed in an initial state included
   in the denotation of an expression or command, that expression or
   command will evaluate to the corresponding final state in the
   denotation. *)

Lemma BigStep_A_Denotational_Adequate :
  forall a st v,
    (v, st) ∈ [[a]]A
    -> v = aeval st a.
Proof.
  induction a; simpl; intros st v H;
    try eassumption; In_inversion.
  - erewrite <- IHa1, <- IHa2; eauto.
  - erewrite <- IHa1, <- IHa2; eauto.
  - erewrite <- IHa1, <- IHa2; eauto.
Qed.

Lemma BigStep_B_Denotational_Adequate :
  forall b st v,
    (v, st) ∈ [[b]]B
    -> beval st b = v.
Proof.
  induction b; simpl; intros st v H; In_inversion; auto.
  - apply BigStep_A_Denotational_Adequate in H.
    apply BigStep_A_Denotational_Adequate in H0.
    simpl in *; subst.
    destruct (Nat.eqb (aeval st a1) (aeval st a2)) eqn: ?; intuition.
    + apply PeanoNat.Nat.eqb_eq in Heqb; rewrite Heqb in H1; firstorder.
    + apply PeanoNat.Nat.eqb_neq in Heqb; firstorder.
      destruct v; eauto.
  (* Uncomment to account for larger set of boolean expressions in SF. *)
  (* - destruct H as [v1 [v2 [denote_a1 [denote_a2 v_eq] ] ] ]; subst; simpl.
    apply BigStep_A_Denotational_Adequate in denote_a1.
    apply BigStep_A_Denotational_Adequate in denote_a2.
    subst.
    destruct (Nat.eqb (aeval st a1) (aeval st a2)) eqn: ?; intuition.
    + rewrite H; try reflexivity.
      apply Nat.leb_le.
      apply Nat.eqb_eq in Heqb; subst.
      apply H0; apply H.

      apply PeanoNat.Nat.eqb_eq.
      assumption.
    + apply PeanoNat.Nat.eqb_neq in Heqb.
      destruct v; eauto; intuition.
  - destruct H as [v1 [v2 [denote_a1 [denote_a2 v_eq] ] ] ]; subst; simpl.
    apply BigStep_A_Denotational_Adequate in denote_a1.
    apply BigStep_A_Denotational_Adequate in denote_a2.
    subst. intuition.
    destruct (Nat.leb (aeval st a1) (aeval st a2)) eqn: ?; intuition.
    + destruct v; eauto; intuition.
      apply Compare_dec.leb_complete in Heqb; lia.
    + destruct v; eauto; intuition.
      apply Compare_dec.leb_complete_conv in Heqb; lia. *)
  - apply BigStep_A_Denotational_Adequate in H.
    apply BigStep_A_Denotational_Adequate in H0.
    simpl in *; subst. firstorder; simpl in *.
    destruct v; eauto; intuition.
    + apply Nat.leb_le; eauto.
    + apply leb_iff_conv.
      destruct (Nat.leb (aeval st a1) (aeval st a2)) eqn: ?; intuition.
      * apply Nat.leb_le in Heqb; lia.
      * apply leb_iff_conv in Heqb; auto.
  - simpl in H; In_inversion.
    simpl; rewrite IHb with (v := negb v).
    + apply Bool.negb_involutive.
    + apply H.
  - erewrite IHb1, IHb2 by eassumption; eauto.
Qed.

Lemma Denotational_BigStep_Adequate :
  forall c st st',
    (st, st') ∈ [[c]] -> st =[c]=> st'.
Proof.
  induction c; intros.
  (*skip*)
  inversion H; subst. constructor.
  (*assign*)
  inversion H; subst. destruct H0 as [H1 H2]. rewrite H2. constructor.
  symmetry. apply BigStep_A_Denotational_Adequate. assumption.
  (*sequence c1; c2 - Normal*)
  inversion H; subst. inversion H0. destruct H1 as [H11 H12].
  eapply E_SeqNormal. eapply IHc1. eassumption. eapply IHc2. assumption.
  (*sequence c1; c2 - Error*)
  destruct H0 as [H01 H02]. rewrite H02. eapply E_SeqError.
  eapply IHc1. assumption.
  (*If - true*)
  inversion H; subst. destruct H0 as [H01 H02].
  econstructor. apply BigStep_B_Denotational_Adequate. assumption.
  apply IHc1. assumption.
  (*If - false*)
   destruct H0 as [H01 H02]. apply E_IfFalse. apply BigStep_B_Denotational_Adequate. 
   assumption. apply IHc2. assumption.
  (*while - false *)
  simpl. simpl in H. apply LFP_unfold in H. unfold elem_of in *. In_inversion.
  rewrite H0. constructor. apply BigStep_B_Denotational_Adequate. assumption.
 (*while - true Normal*)
  eapply E_WhileTrueNormal. apply BigStep_B_Denotational_Adequate. apply H.
  eapply IHc. eassumption. replace x with (fst (x, st')) by reflexivity. 
  replace st' with (snd (x, st')) at 2 by reflexivity. pattern (x, st').
  eapply Ind; try eassumption. generalize IHc. clear.

   intros IHc [st'' st']
              [ [denote_b st_eq]
             | [ [st''0 [denote_b [denote_c ? ] ] ] | [denote_b [denote_c ?] ] ] ].
  subst. econstructor. erewrite BigStep_B_Denotational_Adequate; try reflexivity; assumption.
  econstructor. erewrite BigStep_B_Denotational_Adequate; try reflexivity; assumption.
  apply IHc. eassumption. assumption.
  (*while - True Error*)
  subst. eapply E_WhileTrueError. simpl. erewrite BigStep_B_Denotational_Adequate.
  try reflexivity. assumption.
  simpl. apply IHc. eassumption.
  (*while - True Error*)
  subst. apply E_WhileTrueError. erewrite BigStep_B_Denotational_Adequate; try reflexivity; assumption.
  apply IHc. assumption.
  apply while_body_monotone.
  (*assert*)
  inversion H; subst. destruct H0 as [H01 H02]. subst. apply E_AssertNormal.
  apply BigStep_B_Denotational_Adequate. assumption.
  (*assert - Error*)
  destruct H0 as [H01 H02]. subst. constructor. apply BigStep_B_Denotational_Adequate.
  assumption.

Qed.

(* We can encode the idea of 'is a subterm' using contexts-- these are
   programs with a single hole representing where a command can be
   plugged in:*)

End Semantics.

Module notations.

  Declare Scope denote_scope.

  Notation "'[[' a ']]A'" := (denote_A a) : denote_scope.
  Notation "'[[' b ']]B'" := (denote_B b) : denote_scope.
  Notation "'[[' c ']]'" := (denote_Com c) : denote_scope.

  Notation "st =[ c ]=> st'" := (cevalr c st st')
                                  (at level 40, c custom com at level 99,
                                    st constr, st' constr at next level).

  Notation "{{ v | P }}" := (fun v => P) (v pattern) : denote_scope.

  Open Scope denote_scope.

End notations.
