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
  [[ a ]]A ≡ [[ a' ]]A.

Notation "a1 '==A' a2 " := (aexp_eqv a1 a2) (at level 40).

(* Since expression equivalence is defined in terms of set
   equivalence, we can obtain proofs that it is reflexive,
   transititve, and symmetric for 'free'. *)
Lemma aexp_eqv_refl : forall (a : aexp),
    a ==A a.
Proof. set_solver. Qed.

Lemma aexp_eqv_sym : forall (a1 a2 : aexp),
    a1 ==A a2 -> a2 ==A a1.
Proof. set_solver.  Qed.

Lemma aexp_eqv_trans : forall (a1 a2 a3 : aexp),
    a1 ==A a2 -> a2 ==A a3 -> a1 ==A a3.
Proof. set_solver. Qed.

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
  set_solver.
Qed.

Lemma BigStep_aexp_eqv :
  forall a1 a2,
    a1 ==A a2 ->
    forall st, aeval st a1 = aeval st a2.
Proof.

  intros; unfold aexp_eqv in H.
  apply BigStep_A_Denotational_Adequate.
  apply H.
  apply Denotational_A_BigStep_Sound.
Qed.

(* Equivalence of boolean expressions is defined similarly. *)

Definition bexp_eqv (b b' : bexp) : Prop :=
  [[ b ]]B ≡ [[ b' ]]B.

Notation "b1 '==B' b2 " := (bexp_eqv b1 b2) (at level 40).

Lemma bexp_eqv_refl : forall (b : bexp),
    b ==B b.
Proof. set_solver. Qed.

Lemma bexp_eqv_sym : forall (b1 b2 : bexp),
    b1 ==B b2 -> b2 ==B b1.
Proof. set_solver. Qed.

Lemma bexp_eqv_trans : forall (b1 b2 b3 : bexp),
    b1 ==B b2 -> b2 ==B b3 -> b1 ==B b3.
Proof. set_solver. Qed.

#[global]
Add Parametric Relation : bexp bexp_eqv
    reflexivity proved by bexp_eqv_refl
    symmetry proved by bexp_eqv_sym
    transitivity proved by bexp_eqv_trans
    as eqv_bexp_eqv.

Theorem beq_eqv_example : forall a, <{ a = a }> ==B <{ true }>.
Proof.
  intros. intros (n, st); split; simpl; intros In_st.
  - In_inversion.
    erewrite aexp_eqv_unique with (m := v1) (n := v2) in H1 by eassumption.
    unfold elem_of at 1, PSet_In_ElemOf, Fixpoints.In in H1.
    rewrite <- H1.
    reflexivity.
  - In_inversion.
    In_intro.
    + apply Denotational_A_BigStep_Sound.
    + apply Denotational_A_BigStep_Sound.
    + firstorder.
Qed.

Lemma BigStep_bexp_eqv :
  forall b1 b2,
    b1 ==B b2 ->
    forall st, beval st b1 = beval st b2.
Proof.
  intros; unfold bexp_eqv in H.
  apply BigStep_B_Denotational_Adequate.
  apply H.
  apply Denotational_B_BigStep_Sound.
Qed.

(* We can once again prove some congrence facts about the
   compositionality of equivalence of boolean expressions: *)

(*Lemma beq_eqv_cong : forall a1 a2 a1' a2',
    a1 ==A a1' ->
    a2 ==A a2' ->
    <{a1 = a2}> ==B <{a1' = a2'}>. *)
#[global]
Add Parametric Morphism : BEq
    with signature aexp_eqv ==> aexp_eqv ==> bexp_eqv
      as beq_eqv_cong.
Proof.
  intros a1 a1' a1_eqv a2 a2' a2_eqv.
  unfold bexp_eqv.
  intros (b, st); split; intros v_In.
  - simpl in *; In_inversion; In_intro.
    apply a1_eqv; apply H.
    apply a2_eqv; apply H0.
    set_solver.
  - simpl in *; In_inversion; In_intro.
    apply a1_eqv; apply H.
    apply a2_eqv; apply H0.
    set_solver.
Qed.

(* Lemma ble_eqv_cong : forall a1 a2 a1' a2',
    a1 ==A a1' ->
    a2 ==A a2' ->
    <{a1 <= a2}> ==B <{a1' <= a2'}>. *)
#[global]
Add Parametric Morphism : BLe
    with signature aexp_eqv ==> aexp_eqv ==> bexp_eqv
      as ble_eqv_cong.
Proof.
  intros a1 a1' a1_eqv a2 a2' a2_eqv;
    intros (b, st); split; intros v_In.
  - simpl in *; In_inversion; In_intro.
    apply a1_eqv; apply H.
    apply a2_eqv; apply H0.
    set_solver.
  - simpl in *; In_inversion; In_intro.
    apply a1_eqv; apply H.
    apply a2_eqv; apply H0.
    set_solver.
Qed.

(* Lemma bnot_eqv_cong : forall b1 b1',
    b1 ==B b1' ->
    <{~ b1}> ==B <{~ b1'}>. *)
#[global]
Add Parametric Morphism : BNot
    with signature bexp_eqv ==> bexp_eqv
      as bnot_eqv_cong.
Proof.
  intros b1 b1' b1_eqv (b, st); split; set_solver.
Qed.

(* Lemma band_eqv_cong : forall b1 b2 b1' b2',
    b1 ==B b1' ->
    b2 ==B b2' ->
    <{b1 && b2}> ==B <{b1' && b2'}>. *)
#[global]
Add Parametric Morphism : BAnd
    with signature bexp_eqv ==> bexp_eqv ==> bexp_eqv
      as band_eqv_cong.
Proof.
  intros b1 b1' b1_eqv b2 b2' b2_eqv (b, st); split;
    simpl; intros  v_In; In_inversion; In_intro;
    first [apply b1_eqv; eassumption
          | apply b2_eqv; eassumption
          | reflexivity].
Qed.

(* As expected, two commands are semantically equivalent if their
   denotation is the same set of starting and final states. *)

Definition com_eqv (c c' : com) : Prop := [[ c ]] ≡ [[c']].

Notation "c1 '==C' c2 " := (com_eqv c1 c2) (at level 40).

Lemma com_eqv_refl : forall (c : com),
    c ==C c.
Proof. set_solver. Qed.

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
#[global]
Add Parametric Morphism : CSeq
    with signature com_eqv ==> com_eqv ==> com_eqv
      as seq_eq_cong.
Proof.
  intros c1 c1' c1_eqv c2 c2' c2_eqv (st, st'); split; simpl;
    intros; In_inversion; In_intro;
    first [ apply c1_eqv; eauto
          | apply c2_eqv; eauto].
Qed.

(* Lemma if_eq_cong : forall b c1 c2 c1' c2',
    c1 ==C c1' ->
    c2 ==C c2' ->
    <{if b then c1 else c2 end}> ==C <{if b then c1' else c2' end}>. *)
#[global]
Add Parametric Morphism : CIf
    with signature bexp_eqv ==> com_eqv ==> com_eqv ==> com_eqv
      as if_eq_cong.
Proof.
  intros b b' b_eqv c1 c1' c1_eqv c2 c2' c2_eqv (st, st'); split; simpl;
    intros; In_inversion; In_intro; firstorder.
Qed.

(* Lemma while_eq_cong : forall b c1 c1',
    c1 ==C c1' ->
    <{while b do c1 end}> ==C <{while b do c1' end}>. *)
#[global]
Add Parametric Morphism : CWhile
    with signature bexp_eqv ==> com_eqv ==> com_eqv
      as while_eq_cong.
Proof.
  intros b b' b_eqv c1 c1' c1_eqv (st, st'); split; simpl;
    intros; In_inversion; In_intro.
  - eapply Ind in H.
    apply H.
    unfold FClosed.
    intros [? ?] ?.
    In_inversion.
    + apply LFP_fold.
      * apply while_body_monotone.
      * firstorder.
    + apply LFP_fold.
      apply while_body_monotone.
      firstorder.
  - eapply Ind in H.
    apply H.
    unfold FClosed.
    intros [? ?] ?.
    In_inversion.
    + apply LFP_fold.
      * apply while_body_monotone.
      * firstorder.
    + apply LFP_fold.
      * apply while_body_monotone.
      * firstorder.
Qed.

(* Using the denotational semantics of commands, we can prove that
   programs have the same meaning: *)
Lemma seq_skip_opt :
  forall c,
    <{skip; c}> ==C c.
Proof.
  intros c (st, st'); split; intros In_st.
  - (* (st, st') ∈ [[skip; c]] -> (st, st') ∈ [[c]] *)
    simpl in *; In_inversion; firstorder.
  - (* (st, st') ∈ [[c]] -> (st, st') ∈ [[skip; c]] *)
    (* In this case, we need to show that (st, st') ∈ [[skip; c]] by
       giving an intermediate state [st''], such that (st, st'') ∈
       [[skip]] and (st'', st') ∈ [[c]]. Since [[skip]] only contains
       pairs of the same state, the state [st] fits the bill.  *)
    simpl in *. In_intro.
    + reflexivity.
    + assumption.
Qed.

Lemma seq_opt_skip :
  forall c,
    <{c; skip}> ==C c.
Proof.
  intros c (st, st'); split; intros In_st.
  - (* (st, st') ∈ [[c; skip]] -> (st, st') ∈ [[c]] *)
    simpl in *; In_inversion; firstorder.
  - (* (st, st') ∈ [[c]] -> (st, st') ∈ [[c; skip]] *)
    simpl in *. In_intro.
    + eassumption.
    + reflexivity.
Qed.

(* Using the denotational semantics of commands, we can show that if
   the condition of an if expression is equivalent to true, the entire
   expression is semantically equivalent to the then branch: *)
Theorem if_true: forall b c1 c2,
    b ==B <{true}>  ->
    <{ if b then c1 else c2 end }> ==C  c1.
Proof.
  intros b c1 c2 Hb (st, st'); split; intros st_In.
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
      apply Hb in H; simpl in H; In_inversion.
  - (* In the other direction, We need to show that (st, st') ∈ [[c1]] implies
       (st, st') ∈ [[<{ if b then c1 else c2 end }>]].

      Here, it suffices to show that
      (st, st') ∈ {{(st0, st'0) | (true, st0) ∈ [[b ]]B /\ (st0, st'0) ∈ [[c1]]}},
      which follows immediately from the assumption that (st, st') ∈ [[c1]] and
      [[<{ true }>]]B ⊆ [[b]]B.*)
    left; split.
    + firstorder.
    + assumption.
Qed.

Theorem seq_assoc :
  forall c1 c2 c3,
    <{ (c1; c2); c3 }> ==C <{ c1; c2; c3 }>.
Proof.
  intros c1 c2 c3 (st, st'); simpl; split.
  - firstorder.
  - firstorder.
Qed.

Theorem if_seq_eqv :
  forall b c1 c2 c3,
    <{ if b then c1 else c2 end; c3 }> ==C <{if b then c1; c3 else c2; c3 end}> .
Proof.
  intros b c1 c2 c3 (st, st'); firstorder.
Qed.

Lemma while_unroll_eq :
  forall b c,
    <{while b do c end}> ==C <{if b then (c; while b do c end) else skip end }>.
Proof.
  unfold com_eqv; intros.
  etransitivity.
  - simpl; apply LFP_unfold.
    apply while_body_monotone.
  - simpl; intros (st, st'); split; In_intro; intros;
      In_inversion; firstorder.
Qed.

Lemma while_unroll_n_eq :
  forall n b c,
    <{while b do c end}> ==C <{repeat_c n <{if b then c else skip end }>; while b do c end }>.
Proof.
  induction n; simpl; intros.
  - rewrite seq_skip_opt; reflexivity.
  - rewrite while_unroll_eq at 1.
    rewrite IHn at 1.
    rewrite !if_seq_eqv, !seq_assoc.
    intros (st, st'); split; intros;
      eapply BigStep_Denotational_Sound;
      eapply Denotational_BigStep_Adequate in H.
    + inversion H; subst.
      * econstructor; eauto.
      * eapply E_IfFalse; eauto.
        inversion H6; subst; econstructor; eauto.
        inversion H; subst; try congruence.
        econstructor.
        -- instantiate (1 := st').
           revert H5; clear; induction n; intros; simpl; eauto.
           econstructor.
           econstructor.
           eapply E_IfFalse; eauto.
           econstructor.
           eauto.
        -- econstructor; eauto.
    + inversion H; subst.
      * econstructor; eauto.
      * inversion H6; subst; inversion H2; subst.
        eapply E_IfFalse; eauto.
        inversion H7; subst.
        eapply ceval_repeat_cond_false in H3; eauto; subst.
        inversion H9; subst; try congruence.
Qed.

Lemma while_body_while_eq :
  forall b c,
    <{while b do c end}> ==C <{while b do (while b do c end) end }>.
Proof.
  unfold com_eqv; intros.
  intros (st, st'); split; intros;
    eapply BigStep_Denotational_Sound;
    eapply Denotational_BigStep_Adequate in H.
  - remember <{while b do c end}>; induction H; try congruence.
    + injection Heqc0; intros; subst;
        econstructor; eauto.
    + clear IHceval1.
      injection Heqc0; intros; subst.
      specialize (IHceval2 (eq_refl _)).
      econstructor.
      eauto.
      eapply E_WhileTrue; eauto.
      econstructor; eauto using ceval_while_cond_false.
  - remember <{while b do (while b do c end) end}>; induction H; try congruence.
    + injection Heqc0; intros; subst;
        econstructor; eauto.
    + clear IHceval1.
      injection Heqc0; intros; subst.
      specialize (IHceval2 (eq_refl _)).
      replace st'' with st'; eauto.
      apply ceval_while_cond_false in H0.
      inversion IHceval2; subst; try congruence.
Qed.

Lemma while_body_if_eq :
  forall b c,
    <{while b do c end}> ==C <{while b do (if b then c else skip end) end }>.
Proof.
  unfold com_eqv; intros.
  intros (st, st'); split; intros;
    eapply BigStep_Denotational_Sound;
    eapply Denotational_BigStep_Adequate in H.
  - remember <{while b do c end}>; induction H; try congruence.
    + injection Heqc0; intros; subst;
        econstructor; eauto.
    + clear IHceval1.
      injection Heqc0; intros; subst.
      specialize (IHceval2 (eq_refl _)).
      econstructor; eauto.
      econstructor; eauto.
  - remember <{while b do (if b then c else skip end) end}>; induction H; try congruence.
    + injection Heqc0; intros; subst;
        econstructor; eauto.
    + clear IHceval1.
      injection Heqc0; intros; subst.
      specialize (IHceval2 (eq_refl _)).
      econstructor; eauto.
      inversion H0; subst; try congruence.
Qed.

Lemma repeat_c_plus :
  forall m n c,
      repeat_c (m + n) c ==C <{repeat_c m c; repeat_c n c}>.
Proof.
  induction m; intros.
  - simpl; rewrite seq_skip_opt; reflexivity.
  - simpl; rewrite IHm, seq_assoc; reflexivity.
Qed.

Lemma repeat_c_mult :
  forall m n c,
      repeat_c (m * n) c ==C <{repeat_c m (repeat_c n c)}>.
Proof.
  induction m; intros.
  - simpl; reflexivity.
  - simpl; rewrite repeat_c_plus, IHm; reflexivity.
Qed.

Lemma eqv_step
  : forall c c' st st',
    c ==C c' ->
    st =[ c]=> st' -> st =[c']=> st'.
Proof.
  intros.
  eapply Denotational_BigStep_Adequate.
  apply H.
  eapply BigStep_Denotational_Sound; eassumption.
Qed.

Lemma guarded_repeat
  : forall n st st' b c,
    st =[ if b then (repeat_c n <{ if b then c else skip end }>) else skip end ]=> st'
    -> st =[ repeat_c n <{ if b then c else skip end }> ]=> st'.
Proof.
  induction n; simpl; intros.
  - inversion H; subst; eauto.
  - inversion H; subst; eauto.
    inversion H; subst.
    + inversion H6; inversion H8; subst.
      econstructor; eauto.
    + econstructor.
      eapply E_IfFalse; eauto.
      inversion H6; subst.
      eapply IHn; eapply E_IfFalse; eauto.
Qed.

Lemma guarded_repeat'
  : forall n st st' b c,
    st =[ repeat_c n <{ if b then c else skip end }> ]=> st'
    -> st =[ if b then (repeat_c n <{ if b then c else skip end }>) else skip end ]=> st'.
Proof.
  induction n; simpl; intros.
  - inversion H; subst.
    destruct (beval st' b) eqn: ?.
    + econstructor; eauto.
    + eapply E_IfFalse; eauto.
  - inversion H; subst; eauto.
    inversion H2; subst.
    + econstructor; eauto.
    + inversion H8; subst.
      eapply E_IfFalse; eauto.
      eapply ceval_repeat_cond_false in H5; eauto; subst; econstructor.
Qed.

Lemma repeat_c_refine_body
  : forall n st st' c c',
    (forall st st', st =[c]=> st' -> st =[c']=> st')
    -> st =[ repeat_c n c ]=> st'
    -> st =[ repeat_c n c' ]=> st'.
Proof.
  induction n; simpl; intros.
  - eauto.
  - inversion H0; subst; econstructor; eauto.
Qed.

Lemma repeat_c_eqv_body
  : forall n st st' c c',
    (c ==C c')
    -> st =[ repeat_c n c ]=> st'
    -> st =[ repeat_c n c' ]=> st'.
Proof.
  induction n; simpl; intros.
  - eauto.
  - inversion H0; subst; econstructor; eauto.
    eapply Denotational_BigStep_Adequate.
    apply H.
    eapply BigStep_Denotational_Sound; assumption.
Qed.

Lemma while_body_dup_n_eq :
  forall m n,
    0 < n ->
    forall b c,
      <{while b do (repeat_c n <{if b then c else skip end}>) end }> ==C <{while b do (repeat_c (m + n) <{if b then c else skip end}>) end }>.
Proof.
  intros.
  unfold com_eqv; intros.
  intros (st, st'); split; intros.
  - eapply BigStep_Denotational_Sound.
    eapply Denotational_BigStep_Adequate in H0.
    generalize (ceval_while_cond_false _ _ _ _ H0); intros.
    eapply finite_while_repeat in H0; destruct H0 as [n' repeatc].
    eapply (while_body_finite n'); eauto.
    eapply repeat_c_refine_body with (c' := (repeat_c n <{ if b then c else skip end }>)) in repeatc;
      eauto using guarded_repeat.
    eapply repeat_c_refine_body; [intros; apply guarded_repeat'; apply H0 | ].
    eapply eqv_step.
    apply repeat_c_mult.
    eapply eqv_step in repeatc; [ | symmetry; apply repeat_c_mult].
    replace (n' * (m + n)) with ((n' * n) + (n' * m)) by lia.
    eapply repeat_finite_more; eauto.
  - eapply BigStep_Denotational_Sound.
    eapply Denotational_BigStep_Adequate in H0.
    generalize (ceval_while_cond_false _ _ _ _ H0); intros.
    eapply finite_while_repeat in H0; destruct H0 as [n' repeatc].
    eapply repeat_c_refine_body with (c' := (repeat_c (m + n) <{ if b then c else skip end }>)) in repeatc;
      eauto using guarded_repeat.
    eapply eqv_step in repeatc; [ | symmetry; apply repeat_c_mult].
    replace (n' * (m + n)) with ((n' * n) + (n' * m)) in repeatc by lia.
    eapply (while_body_finite (n' + m * n')); eauto.
    eapply repeat_c_refine_body; [intros; apply guarded_repeat'; apply H0 | ].
    eapply eqv_step.
    apply repeat_c_mult.
    destruct n.
    inversion H.
    rewrite !PeanoNat.Nat.mul_succ_r, !Nat.mul_add_distr_r.
    rewrite PeanoNat.Nat.mul_succ_r in repeatc.
    replace (n' * n + m * n' * n + (n' + m * n')) with (n' * n + n' + n' * m + (m * n' * n)) by lia.
    eapply repeat_finite_more in repeatc; eauto.
Qed.

Corollary while_body_repeat_eq :
  forall n,
    0 < n ->
    forall b c,
      <{while b do c end}> ==C <{while b do (repeat_c n <{if b then c else skip end}>) end }>.
Proof.
  intros; rewrite while_body_if_eq.
  generalize (fun H => while_body_dup_n_eq n 1 H b c).
  simpl; intro.
  rewrite seq_opt_skip in H0.
  rewrite H0 by lia.
  symmetry.
  rewrite (while_body_dup_n_eq 1 n H), PeanoNat.Nat.add_1_r; reflexivity.
Qed.

Lemma while_body_dup_2_eq :
  forall b c,
    <{while b do c end}> ==C <{while b do (if b then c else skip end; if b then c else skip end) end }>.
Proof.
  intros.
  rewrite (while_body_repeat_eq 2) by lia.
  simpl.
  rewrite seq_opt_skip.
  reflexivity.
Qed.

End Equiv.

Module notations.

  Notation "a1 '==A' a2 " := (aexp_eqv a1 a2) (at level 40).
  Notation "b1 '==B' b2 " := (bexp_eqv b1 b2) (at level 40).
  Notation "c1 '==C' c2 " := (com_eqv c1 c2) (at level 40).

End notations.
