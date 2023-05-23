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
From Imp Require Import Syntax Semantics.

Section Equiv.

  (* The type of variables identifiers. *)
  Context {I : Type}.
  Context {M : Type -> Type}.
  Context {id : Id I M}.

  Import Syntax.notations.
  Import Semantics.notations.

(* Two aithmetic expressions are semantically equivalent if their denotation is
   the same set of states and values. *)
Definition aexp_eqv (a a' : aexp) : Prop :=
  Same_set ([[ a ]]A) ([[ a' ]]A).

Notation "a1 '==A' a2 " := (aexp_eqv a1 a2) (at level 40).

(* Since expression equivalence is defined in terms of set
   equivalence, we can obtain proofs that it is reflexive,
   transititve, and symmetric for 'free'. *)
Lemma aexp_eqv_refl : forall (a : aexp),
    a ==A a.
Proof. intro; apply Same_set_refl. Qed.

Lemma aexp_eqv_sym : forall (a1 a2 : aexp),
    a1 ==A a2 -> a2 ==A a1.
Proof. intros; apply Same_set_sym; assumption. Qed.

Lemma aexp_eqv_trans : forall (a1 a2 a3 : aexp),
    a1 ==A a2 -> a2 ==A a3 -> a1 ==A a3.
Proof. intros; eapply Same_set_trans; eassumption. Qed.

(* We can use the following command to register the fact that our
   notion of equivalence for arithmetic expressions is actually an
   equivalence relation. This allows us to use the [reflexivity],
   [symmetry], and [transitivity] tactics with goals and assumptions
   about arithmetic equivalence, just as we can with regular
   equality. *)
#[global]
Add Parametric Relation : aexp aexp_eqv
    reflexivity  proved by aexp_eqv_refl
    symmetry proved by aexp_eqv_sym
    transitivity proved by aexp_eqv_trans
    as eqv_aexp_eqv.

Example aexp_tactic_ex : forall (a1 a2 a3 : aexp),
    a1 ==A a2 -> a3 ==A a2 -> a1 ==A a3.
Proof.
  intros.
  symmetry in H.
  symmetry.
  transitivity a2.
  assumption.
  assumption.
Qed.

(* Equivalence of boolean expressions is defined similarly. *)

Definition bexp_eqv (b b' : bexp) : Prop :=
  Same_set ([[ b ]]B) ([[ b' ]]B).

Notation "b1 '==B' b2 " := (bexp_eqv b1 b2) (at level 40).

Lemma bexp_eqv_refl : forall (b : bexp),
    b ==B b.
Proof. intro; apply Same_set_refl. Qed.

Lemma bexp_eqv_sym : forall (b1 b2 : bexp),
    b1 ==B b2 -> b2 ==B b1.
Proof. intros; apply Same_set_sym; assumption. Qed.

Lemma bexp_eqv_trans : forall (b1 b2 b3 : bexp),
    b1 ==B b2 -> b2 ==B b3 -> b1 ==B b3.
Proof. intros; eapply Same_set_trans; eassumption. Qed.

Add Parametric Relation : bexp bexp_eqv
    reflexivity proved by bexp_eqv_refl
    symmetry proved by bexp_eqv_sym
    transitivity proved by bexp_eqv_trans
    as eqv_bexp_eqv.

Theorem beq_eqv_example : forall a, <{ a = a }> ==B <{ true }>.
Proof.
  split; simpl; intros (n, st) In_st.
  - In_inversion.
    erewrite aexp_eqv_unique with (m := x) (n := x0) in H1 by eassumption.
    rewrite <- H1.
    reflexivity.
  - In_inversion.
    In_intro.
    destruct (denote_aexp_defined a st) as [m denote_a].
    exists m, m; repeat split; try assumption.
    subst; reflexivity.
Qed.

(* We can once again prove some congrence facts about the
   compositionality of equivalence of boolean expressions: *)

(*Lemma beq_eqv_cong : forall a1 a2 a1' a2',
    a1 ==A a1' ->
    a2 ==A a2' ->
    <{a1 = a2}> ==B <{a1' = a2'}>. *)
Add Parametric Morphism : BEq
    with signature aexp_eqv ==> aexp_eqv ==> bexp_eqv
      as beq_eqv_cong.
Proof.
  intros a1 a1' a1_eqv a2 a2' a2_eqv.
  split; intros (b, st) v_In.
  - simpl in *; In_inversion; In_intro.
    exists x, x0.
    repeat split; try tauto.
    + apply a1_eqv; assumption.
    + apply a2_eqv; assumption.
  - simpl in *; In_inversion; In_intro.
    exists x, x0.
    repeat split; try tauto.
    + apply a1_eqv; assumption.
    + apply a2_eqv; assumption.
Qed.

(* Lemma ble_eqv_cong : forall a1 a2 a1' a2',
    a1 ==A a1' ->
    a2 ==A a2' ->
    <{a1 <= a2}> ==B <{a1' <= a2'}>. *)
Add Parametric Morphism : BLe
    with signature aexp_eqv ==> aexp_eqv ==> bexp_eqv
      as ble_eqv_cong.
Proof.
  intros a1 a1' a1_eqv a2 a2' a2_eqv; split;
    simpl; intros (b, st) v_In; In_inversion.
  - In_intro.
    exists x, x0.
    repeat split; try tauto.
    + apply a1_eqv; assumption.
    + apply a2_eqv; assumption.
  - In_intro.
    exists x, x0.
    repeat split; try tauto.
    + apply a1_eqv; assumption.
    + apply a2_eqv; assumption.
Qed.

(* Lemma bnot_eqv_cong : forall b1 b1',
    b1 ==B b1' ->
    <{~ b1}> ==B <{~ b1'}>. *)
Add Parametric Morphism : BNot
    with signature bexp_eqv ==> bexp_eqv
      as bnot_eqv_cong.
Proof.
  intros b1 b1' b1_eqv; split;
    simpl; intros (b, st) v_In; In_inversion.
  - In_intro. apply b1_eqv; assumption.
  - In_intro. apply b1_eqv; assumption.
Qed.

(* Lemma band_eqv_cong : forall b1 b2 b1' b2',
    b1 ==B b1' ->
    b2 ==B b2' ->
    <{b1 && b2}> ==B <{b1' && b2'}>. *)
Add Parametric Morphism : BAnd
    with signature bexp_eqv ==> bexp_eqv ==> bexp_eqv
      as band_eqv_cong.
Proof.
  intros b1 b1' b1_eqv b2 b2' b2_eqv; split;
    simpl; intros (b, st) v_In; In_inversion.
  - In_intro.
    exists x, x0; repeat split; try assumption.
    apply b1_eqv; assumption.
    apply b2_eqv; assumption.
  - In_intro.
    exists x, x0; repeat split; try assumption.
    apply b1_eqv; assumption.
    apply b2_eqv; assumption.
Qed.

(* As expected, two commands are semantically equivalent if their
   denotation is the same set of starting and final states. *)

Definition com_eqv (c c' : com) : Prop :=
  Same_set ([[ c ]]) ([[c']]).

Notation "c1 '==C' c2 " := (com_eqv c1 c2) (at level 40).

Lemma com_eqv_refl : forall (c : com),
    c ==C c.
Proof. intro; apply Same_set_refl. Qed.

Lemma com_eqv_sym : forall (c1 c2 : com),
    c1 ==C c2 -> c2 ==C c1.
Proof. intros; apply Same_set_sym; assumption. Qed.

Lemma com_eqv_trans : forall (c1 c2 c3 : com),
    c1 ==C c2 -> c2 ==C c3 -> c1 ==C c3.
Proof. intros; eapply Same_set_trans; eassumption. Qed.

#[global]
Add Parametric Relation : com com_eqv
    reflexivity proved by com_eqv_refl
    symmetry proved by com_eqv_sym
    transitivity proved by com_eqv_trans
    as eqv_com_eqv.

(* We can again show that command equivalence is a /congruence/: that two
   programs are equivalent if their subterms are equivalent.

   The first step is to show this holds for individual commands.

Lemma seq_eq_cong : forall c1 c2 c1' c2',
    c1 ==C c1' ->
    c2 ==C c2' ->
    <{c1; c2}> ==C <{c1'; c2'}>. *)
Add Parametric Morphism : CSeq
    with signature com_eqv ==> com_eqv ==> com_eqv
      as seq_eq_cong.
Proof.
  intros; split; simpl; intros (st, st') X_In; In_inversion.
  - exists x1; split.
    + apply H; assumption.
    + apply H0; assumption.
  - exists x1; split.
    + apply H; assumption.
    + apply H0; assumption.
Qed.

(* Lemma if_eq_cong : forall b c1 c2 c1' c2',
    c1 ==C c1' ->
    c2 ==C c2' ->
    <{if b then c1 else c2 end}> ==C <{if b then c1' else c2' end}>. *)
Add Parametric Morphism : CIf
    with signature bexp_eqv ==> com_eqv ==> com_eqv ==> com_eqv
      as if_eq_cong.
Proof.
  intros; split; simpl; intros [? ?] X_In; In_inversion.
  - unfold elem_of, PSet_In_ElemOf, Fixpoints.In.
    left; intuition.
    + apply H. assumption.
    + apply H0. assumption.
  - right; intuition.
    + apply H. assumption.
    + apply H1. assumption.
  - left; intuition.
    + apply H. assumption.
    + apply H0. assumption.
  - right; intuition.
    + apply H. assumption.
    + apply H1. assumption.
Qed.

(* Lemma while_eq_cong : forall b c1 c1',
    c1 ==C c1' ->
    <{while b do c1 end}> ==C <{while b do c1' end}>. *)
Add Parametric Morphism : CWhile
    with signature bexp_eqv ==> com_eqv ==> com_eqv
      as while_eq_cong.
Proof.
  intros; split; simpl; intros ? X_In; In_inversion.
  - intuition.
    + eapply Ind in X_In.
      apply X_In.
      unfold FClosed.
      intros [? ?] ?.
      In_inversion.
      intuition; subst.
      * apply LFP_fold.
        apply while_body_monotone.
        In_intro.
        left; intuition.
        apply H; assumption.
      * apply LFP_fold.
        apply while_body_monotone.
        right. exists x1; intuition.
        -- apply H; assumption.
        -- apply H0; assumption.
  - intuition.
    + eapply Ind in X_In.
      apply X_In.
      unfold FClosed.
      intros [? ?] ?.
      In_inversion.
      intuition; subst.
      * apply LFP_fold.
        apply while_body_monotone.
        left; intuition.
        apply H; assumption.
      * apply LFP_fold.
        apply while_body_monotone.
        right.
        exists x1; intuition.
        -- apply H; assumption.
        -- apply H0; assumption.
Qed.

(* Using the denotational semantics of commands, we can prove that
   programs have the same meaning: *)
Lemma seq_skip_opt :
  forall c,
    <{skip; c}> ==C c.
Proof.
  intros c; split; intros (st, st') In_st.
  - (* (st, st') ∈ [[skip; c]] -> (st, st') ∈ [[c]] *)
    simpl in *; In_inversion.
    subst.
    In_intro; assumption.
  - (* (st, st') ∈ [[c]] -> (st, st') ∈ [[skip; c]] *)
    (* In this case, we need to show that (st, st') ∈ [[skip; c]] by
       giving an intermediate state [st''], such that (st, st'') ∈
       [[skip]] and (st'', st') ∈ [[c]]. Since [[skip]] only contains
       pairs of the same state, the state [st] fits the bill.  *)
    simpl in *. In_intro.
    exists st; split.
    + reflexivity.
    + assumption.
Qed.

(* Using the denotational semantics of commands, we can show that if
   the condition of an if expression is equivalent to true, the entire
   expression is semantically equivalent to the then branch: *)
Theorem if_true: forall b c1 c2,
    b ==B <{true}>  ->
    <{ if b then c1 else c2 end }> ==C  c1.
Proof.
  intros b c1 c2 Hb.
  split; intros (st, st') st_In.
  - (* We need to show that (st, st') ∈ [[<{ if b then c1 else c2 end }>]]
       implies (st, st') ∈ [[c1]] *)
    (* By simplifying [[<{ if b then c1 else c2 end }>]], we can do
       case analysis on what must be true of (st, st') if it is a
       member of that set. *)
    simpl in st_In; In_inversion.
    + (* In particular, either ([[b ]]B) ∈ (true, st) or ([[b ]]B) ∈ (false, st). *)
      (* The first case follows trivially. *)
      assumption.
    + (* In the second case, [[b ]]B ∈ (false, st) contradicts our assumption that
         [[b]]B ⊆ [[<{ true }>]]B  *)
      destruct Hb.
      simpl in H1.
      apply H1 in H.
      In_inversion.
  - (* In the other direction, We need to show that (st, st') ∈ [[c1]] implies
       (st, st') ∈ [[<{ if b then c1 else c2 end }>]].

      Here, it suffices to show that
      (st, st') ∈ {{(st0, st'0) | (true, st0) ∈ [[b ]]B /\ (st0, st'0) ∈ [[c1]]}},
      which follows immediately from the assumption that (st, st') ∈ [[c1]] and
      [[<{ true }>]]B ⊆ [[b]]B.*)
    simpl. left; split.
    + destruct Hb as [b_sub_tre true_sub_b].
      apply true_sub_b. simpl. In_intro.
    + apply st_In.
Qed.

Lemma If_while_eq :
  forall b c,
    <{while b do c end}> ==C <{if b then (c; while b do c end) else skip end }>.
Proof.
  unfold com_eqv; intros.
  eapply Same_set_trans.
  simpl; apply LFP_unfold.
  apply while_body_monotone.
  simpl.
  split; intros x In_x.
  - destruct x; In_inversion.
    (* The denotation of [if] is built from the denotations of each branch *)
    + right. intuition. subst.
      reflexivity.
    + left. intuition.
      eexists; intuition; eassumption.
  - destruct x; In_inversion.
    + right. eexists. intuition. eassumption.
      apply H1.
    + left. intuition.
Qed.

End Equiv.

Module notations.

  Notation "a1 '==A' a2 " := (aexp_eqv a1 a2) (at level 40).
  Notation "b1 '==B' b2 " := (bexp_eqv b1 b2) (at level 40).
  Notation "c1 '==C' c2 " := (com_eqv c1 c2) (at level 40).

End notations.
