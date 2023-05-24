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
    Same_set ([[ r1 ]]R) ([[ r2 ]]R).

  Notation "r1 '==R' r2 " := (align_eqv r1 r2) (at level 40).

  Lemma align_com_eqv_refl : forall (r : algn_com),
      r ==R r.
  Proof. intro; apply Same_set_refl. Qed.

  Lemma align_com_eqv_sym : forall (r1 r2 : algn_com),
      r1 ==R r2 -> r2 ==R r1.
  Proof. intros; apply Same_set_sym; assumption. Qed.

  Lemma align_com_eqv_trans : forall (r1 r2 r3 : algn_com),
      r1 ==R r2 -> r2 ==R r3 -> r1 ==R r3.
  Proof. intros; eapply Same_set_trans; eassumption. Qed.

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
    intros; split; simpl; intros ((st1, st2), (st1', st2')) X_In; In_inversion;
      simpl in *.
    - apply H in H1; apply H0 in H2.
      In_intro; eauto.
    - apply H in H1; apply H0 in H2.
      In_intro; eauto.
  Qed.

  #[global]
  Add Parametric Morphism : ACSeq
    with signature align_eqv ==> align_eqv ==> align_eqv
      as ACSeq_eqv_cong.
  Proof.
    intros; split; simpl; intros ((st1, st2), (st1', st2')) X_In; In_inversion;
      simpl in *.
    - apply H in H1; apply H0 in H2.
      In_intro; eauto.
    - apply H in H1; apply H0 in H2.
      In_intro; eauto.
  Qed.

  #[global]
  Add Parametric Morphism : ACIf
    with signature bexp_eqv ==> bexp_eqv ==> align_eqv ==> align_eqv ==> align_eqv
      as ACIf_eqv_cong.
  Proof.
    intros; split; simpl; intros ((st1, st2), (st1', st2')) X_In; In_inversion;
      simpl in *; In_intro.
    - apply H in H3; apply H0 in H4; apply H1 in H5.
      left; left; In_intro; intuition.
    - apply H in H3; apply H2 in H4.
      left; right; In_intro; intuition.
    - apply H0 in H3; apply H2 in H4.
      right; In_intro; intuition.
    - apply H in H3; apply H0 in H4; apply H1 in H5.
      left; left; In_intro; intuition.
    - apply H in H3; apply H2 in H4.
      left; right; In_intro; intuition.
    - apply H0 in H3; apply H2 in H4.
      right; In_intro; intuition.
  Qed.

  #[global]
  Add Parametric Morphism : ACWhile
    with signature bexp_eqv ==> bexp_eqv ==> align_eqv ==> align_eqv
      as ACWhile_eqv_cong.
  Proof.
    intros; split; simpl; intros ((st1, st2), (st1', st2')) X_In; In_inversion;
      simpl in *; In_intro.
    - eapply Ind in X_In.
      apply X_In.
      unfold FClosed.
      intros ((stL, stR), (stL', stR')) ?.
      In_inversion.
      intuition; subst.
      * apply LFP_fold.
        apply while_body_monotone.
        In_intro.
        left; left; In_intro; intuition eauto.
        apply H; eauto.
      * apply LFP_fold.
        apply while_body_monotone.
        In_intro.
        left; right; In_intro; intuition eauto.
        apply H0; eauto.
      * apply LFP_fold.
        apply while_body_monotone.
        right. In_intro; intuition.
        -- apply H; assumption.
        -- apply H0; assumption.
        -- eexists _, _; split; eauto.
           apply H1; assumption.
    - eapply Ind in X_In.
      apply X_In.
      unfold FClosed.
      intros ((stL, stR), (stL', stR')) ?.
      In_inversion.
      intuition; subst.
      * apply LFP_fold.
        apply while_body_monotone.
        In_intro.
        left; left; In_intro; intuition eauto.
        apply H; eauto.
      * apply LFP_fold.
        apply while_body_monotone.
        In_intro.
        left; right; In_intro; intuition eauto.
        apply H0; eauto.
      * apply LFP_fold.
        apply while_body_monotone.
        right. In_intro; intuition.
        -- apply H; assumption.
        -- apply H0; assumption.
        -- eexists _, _; split; eauto.
           apply H1; assumption.
  Qed.

  (* More interestingly, we can prove analogues of algebraic
     equivalences from the BiKAT paper: *)

  Lemma rel_def : forall s1 s2,
      <{ <|s1 | s2|> }> ==R <{ <| s1 | skip|>;; <|skip | s2 |> }>.
  Proof.
    intros; split; simpl; intros ((st1, st2), (st1', st2')) X_In; In_inversion;
      simpl in *; In_intro; subst; intuition eauto.
    eexists _, _; intuition eauto.
  Qed.

  Lemma rel_comm : forall s1 s2,
      <{ <| skip | s2 |>;; <|s1 | skip |> }> ==R <{ <| s1 | skip|>;; <|skip | s2 |> }>.
  Proof.
    intros; split; simpl; intros ((st1, st2), (st1', st2')) X_In; In_inversion;
      simpl in *; In_intro; subst; intuition eauto.
    eexists _, _; intuition eauto.
    eexists _, _; intuition eauto.
  Qed.

  Lemma prod_hom_l : forall s1 s2,
      <{ <|s1; s2 | skip|> }> ==R <{ <| s1 | skip|>;; <|s2 | skip |> }>.
  Proof.
    intros; split; simpl; intros ((st1, st2), (st1', st2')) X_In; In_inversion;
      simpl in *; In_intro; subst; intuition eauto.
    eexists _, _; intuition eauto.
  Qed.

  Lemma prod_hom_r : forall s1 s2,
      <{ <| skip | s1; s2|> }> ==R <{ <| skip | s1 |>;; <|skip | s2 |> }>.
  Proof.
    intros; split; simpl; intros ((st1, st2), (st1', st2')) X_In; In_inversion;
      simpl in *; In_intro; subst; intuition eauto.
    eexists _, _; intuition eauto.
  Qed.

  Lemma prod_seq_assoc : forall r1 r2 r3,
      <{ (r1 ;; r2);; r3  }> ==R <{ r1;; r2;; r3 }>.
  Proof.
    intros; split; simpl; intros ((st1, st2), (st1', st2')) X_In; In_inversion;
      simpl in *; In_intro; subst; intuition eauto.
    eexists _, _; intuition eauto.
    eexists _, _; intuition eauto.
  Qed.

  Lemma whileR_false_L : forall b1 b2 r,
      bexp_eqv b1 <{false}> ->
      <{ whileR <|b1 | b2|> do r end  }> ==R <{ <|skip|skip|> }> .
  Proof.
    intros.
    rewrite H; clear H.
    intros; split; simpl; intros ((st1, st2), (st1', st2')) X_In; In_inversion;
      simpl in *; In_intro; subst; intuition eauto.
    + apply LFP_fold in X_In; try apply while_body_monotone.
      In_inversion.
      * eauto.
      * eauto.
      *   unfold Monotone, subseteq, set_subseteq_instance, rel_state; intros.
          destruct x as ((?, ?), (?, ?)).
          In_inversion.
            -- simpl in *; left; left; In_intro; intuition.
            -- left; right; In_intro; intuition.
      + apply LFP_fold in X_In; try apply while_body_monotone.
        In_inversion.
        * eauto.
        * eauto.
        *   unfold Monotone, subseteq, set_subseteq_instance, rel_state; intros.
            destruct x as ((?, ?), (?, ?)).
            In_inversion.
            -- simpl in *; left; left; In_intro; intuition.
            -- left; right; In_intro; intuition.
      + eapply Ind with (F := fun rec st => st = ((st1', st2'), (st1', st2'))).
        unfold FClosed, subseteq, set_subseteq_instance; simpl.
        intros ((?, ?), (?, ?)) ?; In_inversion; injection H; intros; subst.
        apply LFP_fold.
        -- unfold Monotone, subseteq, set_subseteq_instance, rel_state; intros.
           destruct x as ((?, ?), (?, ?)).
           In_inversion.
           ++ simpl in *; left; left; In_intro; intuition.
           ++ left; right; In_intro; intuition.
        -- left; left; In_intro; intuition.
        -- apply LFP_fold.
           ++ unfold Monotone, subseteq, set_subseteq_instance, rel_state; eauto.
           ++ In_intro.
  Qed.

  Lemma whileR_false_R : forall b1 b2 r,
      bexp_eqv b2 <{false}> ->
      <{ whileR <|b1 | b2|> do r end  }> ==R <{ <|skip|skip|> }> .
  Proof.
    intros.
    rewrite H; clear H.
    intros; split; simpl; intros ((st1, st2), (st1', st2')) X_In; In_inversion;
      simpl in *; In_intro; subst; intuition eauto.
    + apply LFP_fold in X_In; try apply while_body_monotone.
      In_inversion.
      * eauto.
      * eauto.
      *   unfold Monotone, subseteq, set_subseteq_instance, rel_state; intros.
          destruct x as ((?, ?), (?, ?)).
          In_inversion.
          -- simpl in *; left; left; In_intro; intuition.
          -- left; right; In_intro; intuition.
    + apply LFP_fold in X_In; try apply while_body_monotone.
      In_inversion.
      * eauto.
      * eauto.
      *   unfold Monotone, subseteq, set_subseteq_instance, rel_state; intros.
          destruct x as ((?, ?), (?, ?)).
          In_inversion.
          -- simpl in *; left; left; In_intro; intuition.
          -- left; right; In_intro; intuition.
    + eapply Ind with (F := fun rec st => st = ((st1', st2'), (st1', st2'))).
      unfold FClosed, subseteq, set_subseteq_instance; simpl.
      intros ((?, ?), (?, ?)) ?; In_inversion; injection H; intros; subst.
      apply LFP_fold.
      -- unfold Monotone, subseteq, set_subseteq_instance, rel_state; intros.
         destruct x as ((?, ?), (?, ?)).
         In_inversion.
         ++ simpl in *; left; left; In_intro; intuition.
         ++ left; right; In_intro; intuition.
      -- left; right; In_intro; intuition.
      -- apply LFP_fold.
         ++ unfold Monotone, subseteq, set_subseteq_instance, rel_state; eauto.
         ++ In_intro.
  Qed.

  Lemma whileR_false_L' : forall b1 b2 r st1 st2,
      (denote_B b1) (false, st1) ->
      [[<{ whileR <|b1 | b2|> do r end  }>]]R (st1, st2, (st1, st2)).
  Proof.
    simpl; intros.
    apply LFP_fold.
    - unfold Monotone, subseteq, set_subseteq_instance, rel_state; intros.
      destruct x as ((?, ?), (?, ?)).
      In_inversion.
      -- simpl in *; left; left; In_intro; intuition.
      -- left; right; In_intro; intuition.
      -- right; In_intro; intuition.
         eexists _, _; eauto.
    - left; left; In_intro; intuition.
  Qed.

  Lemma whileR_false_R' : forall b1 b2 r st1 st2,
      (denote_B b2) (false, st2) ->
      [[<{ whileR <|b1 | b2|> do r end  }>]]R (st1, st2, (st1, st2)).
  Proof.
    simpl; intros.
    apply LFP_fold.
    - unfold Monotone, subseteq, set_subseteq_instance, rel_state; intros.
      destruct x as ((?, ?), (?, ?)).
      In_inversion.
      -- simpl in *; left; left; In_intro; intuition.
      -- left; right; In_intro; intuition.
      -- right; In_intro; intuition.
         eexists _, _; eauto.
    - left; right; In_intro; intuition.
  Qed.

  Lemma whileR_false_L'' : forall b1 b2 r st1 st2 st1' st2',
      (denote_B b1) (false, st1) ->
      [[<{ whileR <|b1 | b2|> do r end  }>]]R (st1, st2, (st1', st2')) ->
      st1 = st1' /\ st2 = st2'.
  Proof.
    simpl; intros.
    apply LFP_fold in H0.
    - In_inversion.
      + subst; intuition.
      + subst; intuition.
      + apply BigStep_B_Denotational_Adequate in H;
          apply BigStep_B_Denotational_Adequate in H0;
          congruence.
    - unfold Monotone, subseteq, set_subseteq_instance, rel_state; intros.
      destruct x as ((?, ?), (?, ?)).
      In_inversion.
      -- simpl in *; left; left; In_intro; intuition.
      -- left; right; In_intro; intuition.
      -- right; In_intro; intuition.
         eexists _, _; eauto.
  Qed.

  Lemma whileR_false_R'' : forall b1 b2 r st1 st2 st1' st2',
      (denote_B b2) (false, st2) ->
      [[<{ whileR <|b1 | b2|> do r end  }>]]R (st1, st2, (st1', st2')) ->
      st1 = st1' /\ st2 = st2'.
  Proof.
    simpl; intros.
    apply LFP_fold in H0.
    - In_inversion.
      + subst; intuition.
      + subst; intuition.
      + apply BigStep_B_Denotational_Adequate in H;
          apply BigStep_B_Denotational_Adequate in H1;
          congruence.
    - unfold Monotone, subseteq, set_subseteq_instance, rel_state; intros.
      destruct x as ((?, ?), (?, ?)).
      In_inversion.
      -- simpl in *; left; left; In_intro; intuition.
      -- left; right; In_intro; intuition.
      -- right; In_intro; intuition.
         eexists _, _; eauto.
  Qed.

  Lemma whileR_unroll : forall b1 b2 r,
      <{ whileR <|b1 | b2|> do r end  }>
      ==R <{ifR <|b1 | b2|> then r else <|skip|skip|> end;; whileR <|b1 | b2|> do r end}> .
  Proof.
    intros; split; simpl; intros ((st1, st2), (st1', st2')) X_In; In_inversion;
      simpl in *; In_intro; subst; intuition eauto.
    - apply LFP_fold in X_In; try apply while_body_monotone.
      In_inversion.
      + eexists _, _; split.
        * left; right; In_intro; intuition eauto.
        * subst; eapply whileR_false_L'; eauto.
      + eexists _, _; split.
        * right; In_intro; intuition eauto.
        * subst; eapply whileR_false_R'; eauto.
      + eexists x, x0; split; eauto.
        left; left; In_intro; intuition eauto.
    - apply LFP_fold; try apply while_body_monotone.
      destruct H as [ [? |? ] | ?]; In_inversion; In_intro.
      + right; In_intro; intuition eauto.
      + subst; left; left.
        In_intro.
        apply whileR_false_L'' in H0; intuition.
      + subst; left; right.
        In_intro.
        apply whileR_false_R'' in H0; intuition.
  Qed.

  Lemma whileR_lockstep : forall b1 b2 s1 s2,
      <{ <| while b1 do s1 end | while b2 do s2 end |>  }>
      ==R <{whileR <|b1 | b2|> do <|s1 | s2|> end;;
          <| while b1 do s1 end | while b2 do s2 end |> }>.
  Proof.
    intros; split. intros ((st1, st2), (st1', st2')) X_In.
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
    - intros (rst, (st1', st2')) ?.
      eapply CR.Semantics.Denotational_BigStep_Adequate in H;
        inversion H; subst; clear H.
      remember <{whileR <| b1 | b2 |> do <| s1 | s2 |> end}> as r eqn:Heqr;
        revert  st1' st2' Heqr H5; induction H2;
        intros; first [discriminate | injection Heqr; intros; subst; clear Heqr].
      + clear IHaceval1; specialize (IHaceval2 _ _ eq_refl H5).
        eapply block_eqv_cong.
        eapply If_while_eq.
        eapply If_while_eq.
        eapply CR.Semantics.BigStep_Denotational_Sound.
        eapply CR.Semantics.Denotational_BigStep_Adequate in IHaceval2.
        revert H H0 H2_ IHaceval2.
        econstructor.
        * econstructor; eauto.
          inversion H2_; subst.
          econstructor; eauto.
          inversion IHaceval2; subst; intros; eauto.
        * econstructor; eauto.
          inversion H2_; subst.
          econstructor; eauto.
          inversion IHaceval2; subst; intros; eauto.
      + eapply CR.Semantics.BigStep_Denotational_Sound; eauto.
      + eapply CR.Semantics.BigStep_Denotational_Sound; eauto.
  Qed.

End Equiv.

Module notations.

  Notation "r1 '==R' r2 " := (align_eqv r1 r2) (at level 40).

End notations.
