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
(** *** Operational Semantics *)

(** Here is an informal definition of evaluation, presented as inference
    rules for readability:

                           -----------------                            (E_Skip)
                           st =[ skip ]=> st

                           aeval st a = n
                   -------------------------------                      (E_Ass)
                   st =[ x := a ]=> (x !-> n ; st)

                           st  =[ c1 ]=> st'
                           st' =[ c2 ]=> st''
                         ---------------------                           (E_Seq)
                         st =[ c1;c2 ]=> st''

                          beval st b = true
                           st =[ c1 ]=> st'
                --------------------------------------               (E_IfTrue)
                st =[ if b then c1 else c2 end ]=> st'

                         beval st b = false
                           st =[ c2 ]=> st'
                --------------------------------------              (E_IfFalse)
                st =[ if b then c1 else c2 end ]=> st'

                         beval st b = false
                    -----------------------------                 (E_WhileFalse)
                    st =[ while b do c end ]=> st

                          beval st b = true
                           st =[ c ]=> st'
                  st' =[ while b do c end ]=> st''
                  --------------------------------                 (E_WhileTrue)
                  st  =[ while b do c end ]=> st''
*)

Reserved Notation
         "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 99,
          st constr, st' constr at next level).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Ass  : forall st a n x,
      aeval st a = n ->
      st =[ x := a ]=> (<[x := n]> st)
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st  =[ while b do c end ]=> st''

  where "st =[ c ]=> st'" := (ceval c st st').

(** The cost of defining evaluation as a relation instead of a
    function is that we now need to construct _proofs_ that some
    program evaluates to some result state, rather than just letting
    Coq's computation mechanism do it for us. *)


(* ================================================================= *)
(** ** Determinism of Evaluation *)

Theorem ceval_deterministic: forall c st st1 st2,
     st =[ c ]=> st1  ->
     st =[ c ]=> st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  induction E1; intros st2 E2; inversion E2; subst.
  - (* E_Skip *) reflexivity.
  - (* E_Ass *) reflexivity.
  - (* E_Seq *)
    rewrite (IHE1_1 st'0 H1) in *.
    apply IHE1_2. assumption.
  - (* E_IfTrue, b evaluates to true *)
      apply IHE1. assumption.
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
  - (* E_WhileTrue, b evaluates to false (contradiction) *)
    rewrite H in H4. discriminate.
  - (* E_WhileTrue, b evaluates to true *)
    rewrite (IHE1_1 st'0 H3) in *.
    apply IHE1_2. assumption.  Qed.


Definition AExpDom := PSet (nat * state)%type.
Definition BExpDom := PSet (bool * state)%type.
Definition ComDom := PSet (state * state)%type.

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
  combinator defined in Fixpoints.v. *)
Fixpoint denote_Com (c : com)
  : ComDom :=
  match c with
  | <{ skip }> =>
    {{ (st, st') | st = st' }}
  | <{x := a1}> => {{ (st, st') | exists v,
                               (v, st) ∈ [[a1]]A
                               /\ st' = <[x := v]>st }}

  | <{c1; c2}> => {{ (st, st') |
                   exists st'',
                   (st, st'') ∈ [[c1]] /\
                   (st'', st') ∈ [[c2]] }}

  | <{ if b then c1 else c2 end }> =>
    {{ (st, st') |
      ((true, st) ∈ [[b]]B /\ (st, st') ∈ [[c1]])
      \/ ((false, st) ∈ [[b]]B /\ (st, st') ∈ [[c2]]) }}

  | <{ while b do c end }> =>
    LFP (fun (phi : PSet _) =>
           {{ (st, st') |
              ((false, st) ∈ [[b]]B /\ st' = st)
               \/ (exists st'',
                      (true, st) ∈ [[b]]B /\
                      (st, st'') ∈ [[c]]
                      /\  (st'', st') ∈ phi) }})


  end
where "'[[' c ']]'" := (denote_Com c).

(* To show that LFP is a proper fixed point in subsequent proofs, we
   need to show that if is applied to a monotone function. *)
Lemma while_body_monotone :
  forall b c,
    Monotone (fun (phi : PSet _) =>
           {{ (st, st') |
              ((false, st) ∈ [[b]]B /\ st' = st)
               \/ (exists st'',
                      (true, st) ∈ [[b]]B /\
                      (st, st'') ∈ [[c]]
                      /\  (st'', st') ∈ phi) }}).
Proof.
  unfold Monotone, subseteq, set_subseteq_instance; intros.
  destruct x; unfold elem_of in *; In_inversion.
  - subst; left; split; try assumption; reflexivity.
  - right; eexists _; intuition; try eassumption.
    apply H; eassumption.
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
  intros.
  induction H; simpl; try solve [econstructor]; In_intro;
    try reflexivity; try eassumption.
  - (* E_Ass *)
    rewrite <- H; eapply Denotational_A_BigStep_Sound.
  - (* E_IfTrue *)
    left; subst; split; try eassumption.
    rewrite <- H; eapply Denotational_B_BigStep_Sound.
  - (* E_IfFalse *)
    right; subst; split; try eassumption.
    rewrite <- H; eapply Denotational_B_BigStep_Sound.
  - (* E_WhileEnd *)
    apply LFP_unfold.
    apply while_body_monotone.
    left.
    intuition.
    rewrite <- H; apply Denotational_B_BigStep_Sound.
  - (* E_WhileLoop *)
    apply LFP_unfold.
    apply while_body_monotone.
    right.
    eexists; repeat split; try eassumption.
    rewrite <- H; apply Denotational_B_BigStep_Sound.
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
  induction c; simpl; intros st st' denote_c; In_inversion.
  - (* skip *)
    econstructor.
  - (* Assignment *)
    econstructor.
    erewrite BigStep_A_Denotational_Adequate; try reflexivity; assumption.
  - (* Sequence *)
    subst; econstructor.
    + apply IHc1; eassumption.
    + apply IHc2; eassumption.
  - (* Conditional *)
    constructor.
    erewrite BigStep_B_Denotational_Adequate; try reflexivity; assumption.
    apply IHc1; eassumption.
  - apply E_IfFalse.
      erewrite BigStep_B_Denotational_Adequate; try reflexivity; assumption.
      apply IHc2; eassumption.
  - apply LFP_unfold in denote_c; try apply while_body_monotone.
    unfold elem_of in *; In_inversion.
    + rewrite H0; econstructor.
      erewrite BigStep_B_Denotational_Adequate; try reflexivity; assumption.
    + eapply E_WhileTrue.
      erewrite BigStep_B_Denotational_Adequate; try reflexivity; assumption.
      apply IHc; eassumption.
      replace x with (fst (x, st')) by reflexivity.
      replace st' with (snd (x, st')) at 2 by reflexivity.
      pattern (x, st').
      (* Hmmmm... we're (almost) back to where we started! *)
      (* Why can't we apply the Inductive Hypothesis? *)
      eapply Ind; try eassumption.
      generalize IHc; clear.
      intros IHc [st'' st']
             [ [denote_b st_eq]
             | [st''0 [denote_b [denote_c ? ] ] ] ].
      * subst; econstructor.
        erewrite BigStep_B_Denotational_Adequate; try reflexivity; assumption.
      * econstructor.
        erewrite BigStep_B_Denotational_Adequate; try reflexivity; assumption.
        apply IHc; eassumption.
        apply H.
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

  Notation "st =[ c ]=> st'" := (ceval c st st')
                                  (at level 40, c custom com at level 99,
                                    st constr, st' constr at next level).

  Notation "{{ v | P }}" := (fun v => P) (v pattern) : denote_scope.

  Open Scope denote_scope.

End notations.
