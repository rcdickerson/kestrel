From Imp Require Import Syntax Semantics Equiv.
From CR Require Import Syntax Semantics.
From Common Require Import Id Fixpoints.

Reserved Notation " r1 '==R' r2 " (at level 40).

Section Equiv.

  Import Imp.Syntax.notations.
  Import Imp.Semantics.notations.
  Import CR.Syntax.notations.
  Import CR.Semantics.notations.

  (* The type of variable identifiers. *)
  Context {I : Type}.
  Context {M : Type -> Type}.
  Context {id : Id I M}.

  (* Our notion of equivalence for aligned programs is defined via
     CoreRel's denotational semantics. *)
  Definition align_eqv (r1 r2 : algn_com) : Prop :=
    [[ r1 ]]R ≡ [[ r2 ]]R.

  Notation "r1 '==R' r2 " := (align_eqv r1 r2) (at level 40).

  Lemma align_com_eqv_refl : forall (r : algn_com),
      r ==R r.
  Proof. set_solver. Qed.

  Lemma align_com_eqv_sym : forall (r1 r2 : algn_com),
      r1 ==R r2 -> r2 ==R r1.
  Proof. set_solver. Qed.

  Lemma align_com_eqv_trans : forall (r1 r2 r3 : algn_com),
      r1 ==R r2 -> r2 ==R r3 -> r1 ==R r3.
  Proof. set_solver. Qed.

  #[global]
   Add Parametric Relation : algn_com align_eqv
  reflexivity proved by align_com_eqv_refl
  symmetry proved by align_com_eqv_sym
  transitivity proved by align_com_eqv_trans
  as align_eqv_com_eqv.

(* Aligned command equivalence is again a /congruence/: two
   alignments are equivalent if their subterms are equivalent.

   The first step is to show this holds for individual alignments commands. *)
  #[global]
  Add Parametric Morphism : ACBlock
    with signature com_eqv ==> com_eqv ==> align_eqv
      as block_eqv_cong.
  Proof.
    intros c1 c1' c1_eqv c2 c2' c2_eqv ((st1, st2), (st1', st2')); firstorder.
  Qed.

  #[global]
  Add Parametric Morphism : ACSeq
    with signature align_eqv ==> align_eqv ==> align_eqv
      as ACSeq_eqv_cong.
  Proof.
    intros r1 r1' r1_eqv c2 c2' c2_eqv ((st1, st2), (st1', st2')); simpl; split;
      intros; In_inversion; simpl in *; In_intro.
    - apply r1_eqv; eauto.
    - apply c2_eqv; eauto.
    - apply r1_eqv; eauto.
    - apply c2_eqv; eauto.
  Qed.

  #[global]
  Add Parametric Morphism : ACIf
    with signature bexp_eqv ==> bexp_eqv ==> align_eqv ==> align_eqv ==> align_eqv
      as ACIf_eqv_cong.
  Proof.
    intros b1 b1' b1_eqv b2 b2' b2_eqv r1 r1' r1_eqv r2 r2' r2_eqv
           ((st1, st2), (st1', st2')); simpl; split; intros;
      In_inversion; simpl in *.
    - firstorder.
    - firstorder.
    - firstorder.
    - firstorder.
    - firstorder.
    - firstorder.
  Qed.

  #[global]
  Add Parametric Morphism : ACWhile
    with signature bexp_eqv ==> bexp_eqv ==> align_eqv ==> align_eqv
      as ACWhile_eqv_cong.
  Proof.
    intros b1 b1' b1_eqv b2 b2' b2_eqv r1 r1' r1_eqv
           ((st1, st2), (st1', st2')); simpl; split; intros;
      In_inversion; simpl in *.
    - eapply Ind in H.
      + apply H.
      + unfold FClosed.
        intros ((stL, stR), (stL', stR')) ?.
        In_inversion.
        compute in H1, H2; simpl in H0; subst.
        * apply LFP_fold.
          apply while_body_monotone.
          firstorder.
        * apply LFP_fold.
          apply while_body_monotone.
          firstorder.
        * apply LFP_fold.
          apply while_body_monotone.
          firstorder.
    - eapply Ind in H.
      + apply H.
      + unfold FClosed.
        intros ((stL, stR), (stL', stR')) ?.
        In_inversion.
        compute in H1, H2; simpl in H0; subst.
        * apply LFP_fold.
          apply while_body_monotone.
          firstorder.
        * apply LFP_fold.
          apply while_body_monotone.
          firstorder.
        * apply LFP_fold.
          apply while_body_monotone.
          firstorder.
  Qed.

  (* More interestingly, we can prove analogues of algebraic
     equivalences from the BiKAT paper: *)

  Lemma rel_def : forall s1 s2,
      <{ <|s1 | s2|> }> ==R <{ <| s1 | skip|>;; <|skip | s2 |> }>.
  Proof.
    intros s1 s2 ((st1, st2), (st1', st2')); firstorder;
      simpl in *; In_inversion;
      firstorder.
  Qed.

  Lemma rel_comm : forall s1 s2,
      <{ <| skip | s2 |>;; <|s1 | skip |> }> ==R <{ <| s1 | skip|>;; <|skip | s2 |> }>.
  Proof.
    intros s1 s2 ((st1, st2), (st1', st2')); firstorder;
      simpl in *; In_inversion;
      firstorder.
  Qed.

  Lemma prod_hom_l : forall s1 s2,
      <{ <|s1; s2 | skip|> }> ==R <{ <| s1 | skip|>;; <|s2 | skip |> }>.
  Proof.
    intros s1 s2 ((st1, st2), (st1', st2')); firstorder;
      simpl in *; In_inversion;
      firstorder.
  Qed.

  Lemma prod_hom_r : forall s1 s2,
      <{ <| skip | s1; s2|> }> ==R <{ <| skip | s1 |>;; <|skip | s2 |> }>.
  Proof.
    intros s1 s2 ((st1, st2), (st1', st2')); firstorder;
      simpl in *; In_inversion;
      firstorder.
  Qed.

  Lemma prod_seq_assoc : forall r1 r2 r3,
      <{ (r1 ;; r2);; r3  }> ==R <{ r1;; r2;; r3 }>.
  Proof.
    intros r1 r2 r3 ((st1, st2), (st1', st2')); firstorder;
      simpl in *; In_inversion; In_intro; eauto; firstorder.
  Qed.

  Lemma if_align : forall b1 b2 c1 c2 c3 c4,
      <{ <| if b1 then c1 else c2 end | if b2 then c3 else c4 end |> }>
      ==R <{ifR <|b1 | b2|> then <|c1 | c3|> else ifR <|b1 | BNot b2|> then <|c1 | c4|>
            else ifR <|BNot b1 | b2|> then <|c2 | c3|> else <|c2 | c4|> end end end}> .
  Proof.
    intros b1 b2 c1 c2 c3 c4 ((st1, st2), (st1', st2')). split.
    intros. In_inversion. firstorder.
    intros. simpl in H. In_inversion; firstorder. simpl in H,H0,H1,H2,H3.
    apply bexp_eqv_unique with b1 false true st1 in H. discriminate H. assumption.
    simpl in H, H0, H1, H2, H3. apply bexp_eqv_unique with b1 false true st1 in H.
    discriminate H. assumption. simpl in H, H0, H1, H2, H3.
    apply bexp_eqv_unique with b2 false true st2 in H. discriminate H.
    assumption. simpl in H,H0,H1,H2,H3. apply bexp_eqv_unique with b2 false true st2 in H.
    discriminate H. assumption.
  Qed.

  Lemma whileR_false_L : forall b1 b2 r,
      bexp_eqv b1 <{false}> ->
      <{ whileR <|b1 | b2|> do r end  }> ==R <{ <|skip|skip|> }> .
  Proof.
    intros b1 b2 r b1_eqv ((st1, st2), (st1', st2')); split;
      intros; In_inversion; firstorder;
      apply Denotational_BigStep_Adequate in H.
    - eapply BigStep_bexp_eqv with (st := st1) in b1_eqv.
      inversion H; simpl in *; try congruence.
    - eapply BigStep_bexp_eqv with (st := st1) in b1_eqv.
      inversion H; simpl in *; try congruence.
  Qed.

  Lemma whileR_false_R : forall b1 b2 r,
      bexp_eqv b2 <{false}> ->
      <{ whileR <|b1 | b2|> do r end  }> ==R <{ <|skip|skip|> }> .
  Proof.
    intros b1 b2 r b2_eqv ((st1, st2), (st1', st2')); split;
      intros; In_inversion; firstorder.
    - simpl in H; apply LFP_fold in H; try apply while_body_monotone.
      In_inversion.
      + compute in H0, H1; subst; firstorder.
      + compute in H0, H1; subst; firstorder.
      + simpl in *.
        apply b2_eqv in H0; compute in H0; discriminate.
    - simpl in H; apply LFP_fold in H; try apply while_body_monotone.
      In_inversion.
      + compute in H0, H1; subst; firstorder.
      + compute in H0, H1; subst; firstorder.
      + simpl in *.
        apply b2_eqv in H0; compute in H0; discriminate.
  Qed.

  Lemma whileR_false_L' : forall b1 b2 r st1 st2,
      (denote_B b1) (false, st1) ->
      [[<{ whileR <|b1 | b2|> do r end  }>]]R (st1, st2, (st1, st2)).
  Proof.
    firstorder.
  Qed.

  Lemma whileR_false_R' : forall b1 b2 r st1 st2,
      (denote_B b2) (false, st2) ->
      [[<{ whileR <|b1 | b2|> do r end  }>]]R (st1, st2, (st1, st2)).
  Proof.
    firstorder.
  Qed.

  Lemma whileR_false_L'' : forall b1 b2 r st1 st2 st1' st2',
      (denote_B b1) (false, st1) ->
      [[<{ whileR <|b1 | b2|> do r end  }>]]R (st1, st2, (st1', st2')) ->
      st1 = st1' /\ st2 = st2'.
  Proof.
    simpl; intros.
    apply LFP_fold in H0; try apply while_body_monotone.
    In_inversion.
    - compute in H0, H1; subst; firstorder.
    - compute in H0, H1; subst; firstorder.
    - apply BigStep_B_Denotational_Adequate in H;
        apply BigStep_B_Denotational_Adequate in H0; simpl in *; congruence.
  Qed.

  Lemma whileR_false_R'' : forall b1 b2 r st1 st2 st1' st2',
      (denote_B b2) (false, st2) ->
      [[<{ whileR <|b1 | b2|> do r end  }>]]R (st1, st2, (st1', st2')) ->
      st1 = st1' /\ st2 = st2'.
  Proof.
    simpl; intros.
    apply LFP_fold in H0; try apply while_body_monotone.
    In_inversion.
    - compute in H0, H1; subst; firstorder.
    - compute in H0, H1; subst; firstorder.
    - apply BigStep_B_Denotational_Adequate in H;
        apply BigStep_B_Denotational_Adequate in H1; simpl in *; congruence.
  Qed.

  Lemma whileR_unroll : forall b1 b2 r,
      <{ whileR <|b1 | b2|> do r end  }>
      ==R <{ifR <|b1 | b2|> then r else <|skip|skip|> end;; whileR <|b1 | b2|> do r end}> .
  Proof.
    intros b1 b2 r((st1, st2), (st1', st2')); simpl; split; intros;
      In_inversion; simpl in *; try firstorder.
    apply LFP_fold in H; try apply while_body_monotone.
    In_inversion.
    - compute in H0, H1; subst; firstorder.
      In_intro.
      + firstorder.
      + eapply whileR_false_L'; eauto.
    - compute in H0, H1; subst; firstorder.
      In_intro.
      + firstorder.
      + eapply whileR_false_R'; eauto.
    - simpl in *; firstorder.
  Qed.

  Lemma whileR_lockstep : forall b1 b2 s1 s2,
      <{ <| while b1 do s1 end | while b2 do s2 end |>  }>
      ==R <{whileR <|b1 | b2|> do <|s1 | s2|> end;;
          <| while b1 do s1 end | while b2 do s2 end |> }>.
  Proof.
    intros b1 b2 s1 s2 ((st1, st2), (st1', st2')); split; intros X_In.
    - eapply CR.Semantics.BigStep_Denotational_Sound.
      eapply CR.Semantics.Denotational_BigStep_Adequate in X_In.
      inversion X_In; subst; simpl in *; clear X_In.
      remember <{ while b1 do s1 end}>.
      revert st2 st2' s2 Heqc H5; induction H3; intros; subst;
        intros; first [discriminate | injection Heqc; intros; subst; clear Heqc].
      + econstructor.
        * eapply E_ACWhileFalseL; simpl; eauto.
        * econstructor; simpl; eauto.
          apply E_WhileFalse; eauto.
      + clear IHceval1.
        inversion H5; subst; intros.
        * econstructor.
          -- eapply E_ACWhileFalseR; simpl; eauto.
          -- econstructor; eauto.
             eapply E_WhileTrue; eauto.
        * eapply CR.Semantics.Denotational_BigStep_Adequate.
          eapply ACSeq_eqv_cong.
          eapply whileR_unroll.
          reflexivity.
          eapply prod_seq_assoc.
          eapply CR.Semantics.BigStep_Denotational_Sound.
          econstructor.
          econstructor; eauto.
          econstructor; eauto.
          eapply IHceval2; eauto.
    - eapply CR.Semantics.Denotational_BigStep_Adequate in X_In;
        inversion X_In; subst; clear X_In.
      remember <{whileR <| b1 | b2 |> do <| s1 | s2 |> end}> as r eqn:Heqr;
        revert  st1' st2' Heqr H4; induction H1;
        intros; first [discriminate | injection Heqr; intros; subst; clear Heqr].
      + clear IHaceval1; specialize (IHaceval2 _ _ eq_refl H4).
        eapply block_eqv_cong.
        eapply If_while_eq.
        eapply If_while_eq.
        eapply CR.Semantics.BigStep_Denotational_Sound.
        eapply CR.Semantics.Denotational_BigStep_Adequate in IHaceval2.
        revert H H0 H1_ IHaceval2.
        econstructor.
        * econstructor; eauto.
          inversion H1_; subst.
          econstructor; eauto.
          inversion IHaceval2; subst; intros; eauto.
        * econstructor; eauto.
          inversion H1_; subst.
          econstructor; eauto.
          inversion IHaceval2; subst; intros; eauto.
      + eapply CR.Semantics.BigStep_Denotational_Sound; eauto.
      + eapply CR.Semantics.BigStep_Denotational_Sound; eauto.
  Qed.

End Equiv.

Module notations.

  Notation "r1 '==R' r2 " := (align_eqv r1 r2) (at level 40).

End notations.
