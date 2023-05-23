From Imp Require Import Syntax Semantics.
From CR Require Import Syntax.
From Common Require Import Id Fixpoints.

Reserved Notation
         "st '=<[' c ']>=>' st'"
         (at level 40, c custom com at level 99,
          st constr, st' constr at next level).

Reserved Notation "'[[' r ']]R'" (at level 40).

Section Semantics.

  Import Imp.Syntax.notations.
  Import Imp.Semantics.notations.
  Import CR.Syntax.notations.

  (* The type of variable identifiers. *)
  Context {I : Type}.
  Context {M : Type -> Type}.
  Context {id : Id I M}.

  (* First, a completely standard operational semantics for CoreRel: *)

  (* The operational semantics relate a pair of (disjoint) initial
   s tates to a pair of (disjoint) final state. *)

  Definition state := @state M.

  Definition rel_state := (state * state)%type.

  Inductive aceval : algn_com -> rel_state -> rel_state -> Prop :=
  | E_ACBlock : forall s1 s2 rst st1' st2',
      fst rst =[ s1 ]=> st1' ->
    snd rst =[ s2 ]=> st2' ->
      rst =<[ <| s1 | s2 |> ]>=> (st1', st2')

| E_ACSeq : forall r1 r2 rst rst'' rst',
    rst =<[ r1 ]>=> rst'' ->
    rst'' =<[ r2 ]>=> rst' ->
    rst =<[ r1 ;; r2 ]>=> rst'

| E_ACIfTrue : forall b1 b2 r1 r2 rst rst',
    beval (fst rst) b1 = true ->
    beval (snd rst) b2 = true ->
    rst =<[ r1 ]>=> rst' ->
    rst =<[ ifR <| b1 | b2 |> then r1 else r2 end ]>=> rst'

| E_ACIfFalseL : forall b1 b2 r1 r2 rst rst',
    beval (fst rst) b1 = false ->
    rst =<[ r2 ]>=> rst' ->
    rst =<[ ifR <| b1 | b2 |> then r1 else r2 end ]>=> rst'

| E_ACIfFalseR : forall b1 b2 r1 r2 rst rst',
    beval (snd rst) b2 = false ->
    rst =<[ r2 ]>=> rst' ->
    rst =<[ ifR <| b1 | b2 |> then r1 else r2 end ]>=> rst'

| E_ACWhileTrue : forall b1 b2 r rst rst' rst'',
    beval (fst rst) b1 = true ->
    beval (snd rst) b2 = true ->
    rst =<[ r ]>=> rst'' ->
    rst'' =<[ whileR <| b1 | b2 |> do r end ]>=> rst' ->
    rst =<[ whileR <| b1 | b2 |> do r end ]>=> rst'

| E_ACWhileFalseL : forall b1 b2 r rst,
    beval (fst rst) b1 = false ->
    rst =<[ whileR <| b1 | b2 |> do r end ]>=> rst

| E_ACWhileFalseR : forall b1 b2 r rst,
    beval (snd rst) b2 = false ->
    rst =<[ whileR <| b1 | b2 |> do r end ]>=> rst

where "st =<[ r ]>=> st'" := (aceval r st st').

(* Second, a denotational semantics for CoreRel: *)
(* The semantic domain for commands is pairs of initial and final
   relational states: *)

Definition algn_com_dom := PSet (rel_state * rel_state)%type.

(*⟦<s1 | s2> ⟧RC ≡ {( σL, σL', σR, σR') |
                      (σL, σL') ∈ ⟦s1⟧C ⋀ (σR, σR') ∈ ⟦s2⟧C  }
  ⟦r1;r2⟧RC ≡ {(σL1, σL3, σR1, σR3) |
                      ∃ σL2 σR2.   (σL1, σL2, σR1, σR2) ∈ ⟦r1⟧RC
                                 ⋀ (σL2, σL3, σR2, σR3) ∈ ⟦r2⟧RC}

  ⟦ifR <b1 | b2> then r1 else r2⟧RC ≡
     {(σL1, σL2, σR1, σR2) | (σL1, true) ∈ ⟦b1⟧B ⋀
                             (σR1, true) ∈ ⟦b2⟧B ⋀
                             (σL1, σR1, σL2, σR2) ∈ ⟦r1⟧RC }
   ∪ {(σL1, σL2, σR1, σR2) | (σL1, false) ∈ ⟦b1⟧B
                             (σL1, σL2, σR1, σR2) ∈ ⟦r2⟧RC }
   ∪ {(σL1, σL2, σR1, σR2) | (σR1, false) ∈ ⟦b2⟧B
                             (σL1, σL2, σR1, σR2) ∈ ⟦r2⟧RC }

  ⟦while <b1 | b2> do r end⟧C ≡ LFP F

  where
  F(rec) = {(σL1, σL1, σR1, σR1) | (σL1, false) ∈ ⟦b1⟧B}
         ∪ {(σL1, σL1, σR1, σR1) | (σL2, false) ∈ ⟦b1⟧B}
         ∪ {(σL1, σL3, σR1, σR3) | (σL1, true) ∈ ⟦b1⟧B ∧ (σL2, true) ∈ ⟦b2⟧B
                         ∧ ∃σL2 σR2. (σL1, σL2, σR1, σR2) ∈ ⟦r⟧RC
                                      ⋀ (σL2, σL3, σR2, σR3) ∈ rec} *)

(*The denotation of while loops uses the least fixed point [LFP]
  combinator defined in Fixpoints.v. *)

Fixpoint denote_algn_com (r : algn_com) : algn_com_dom :=
  match r with
  | <{ <| s1 | s2 |> }> =>
      {{ ((stL, stR), (stL', stR')) |
         (stL, stL') ∈ denote_Com s1 /\ (stR, stR') ∈ denote_Com s2 }}

  | <{ r1;; r2 }> =>
      {{ ((stL, stR), (stL', stR')) |
         exists stL'' stR'',
         ((stL, stR), (stL'', stR'')) ∈ [[ r1 ]]R /\
           ((stL'', stR''), (stL', stR')) ∈ [[r2]]R }}

  | <{ ifR <| b1 | b2 |> then r1 else r2 end }> =>
      {{ ((stL, stR), (stL', stR')) |
             (true, stL) ∈ denote_B b1
          /\ (true, stR) ∈ (denote_B b2)
          /\ ((stL, stR), (stL', stR')) ∈ [[r1]]R }}
   ∪ {{ ((stL, stR), (stL', stR')) |
             (false, stL) ∈ (denote_B b1)
             /\ ((stL, stR), (stL', stR')) ∈ [[r2]]R }}
   ∪ {{ ((stL, stR), (stL', stR')) |
             (false, stR) ∈ (denote_B b2)
             /\ ((stL, stR), (stL', stR')) ∈ [[r2]]R }}

  | <{ whileR <| b1 | b2 |> do r end }> =>
      LFP (fun (phi : algn_com_dom) =>
             {{ ((stL, stR), (stL', stR')) |
                ((false, stL) ∈ denote_B b1 /\ stL' = stL /\ stR' = stR) }}
           ∪ {{ ((stL, stR), (stL', stR')) |
                ((false, stR) ∈ denote_B b2 /\ stL' = stL /\ stR' = stR) }}
           ∪ {{ ((stL, stR), (stL', stR')) |
                (true, stL) ∈ denote_B b1 /\
                (true, stR) ∈ denote_B b2 /\
                exists stL'' stR'',
                ((stL, stR), (stL'', stR'')) ∈ [[r]]R /\
                  ((stL'', stR''), (stL', stR')) ∈ phi }})
  end
where "'[[' r ']]R'" := (denote_algn_com r) : denote_scope.

(* We now show that the two semantics above are equivalent, i.e. that
   our denotational semantics is both sound and adequate with respect
   to the operational semantics. *)

(* To show that LFP is a proper fixed point in subsequent proofs, we
   need to show that if is applied to a monotone function. *)
Lemma while_body_monotone :
  forall b1 b2 r,
    Monotone
      (fun (phi : algn_com_dom) =>
             {{ ((stL, stR), (stL', stR')) |
                ((false, stL) ∈ denote_B b1 /\ stL' = stL /\ stR' = stR) }}
           ∪ {{ ((stL, stR), (stL', stR')) |
                ((false, stR) ∈ denote_B b2 /\ stL' = stL /\ stR' = stR) }}
           ∪ {{ ((stL, stR), (stL', stR')) |
                (true, stL) ∈ denote_B b1 /\
                (true, stR) ∈ denote_B b2 /\
                exists stL'' stR'',
                ((stL, stR), (stL'', stR'')) ∈ [[r]]R /\
                  ((stL'', stR''), (stL', stR')) ∈ phi }}).
Proof.
  unfold Monotone, subseteq, set_subseteq_instance, rel_state; intros.
  In_inversion; destruct x0, x1.
  - left; left; In_intro; intuition.
  - left; right; In_intro; intuition.
  - right; In_intro; intuition.
    destruct H3 as [? [? ?] ]; intuition.
    eexists _, _; split; try eassumption.
    eapply H; eauto.
Qed.

(* Now, soundness: *)
Lemma BigStep_Denotational_Sound :
  forall r rst rst',
    rst =<[r]>=> rst' -> (rst, rst') ∈ [[r]]R.
Proof.
  intros.
  induction H;
    try destruct rst as [stL stR];
    try destruct rst' as [stL' stR'];
    try destruct rst'' as [stL'' stR''];
    simpl in *; try solve [econstructor]; unfold In.
  - (* EAC_Block *)
    split; eapply BigStep_Denotational_Sound; eauto.
  - (* E_ACSeq *)
    eexists _, _; intuition eauto.
  - (* E_ACIfTrue *)
    left; left; subst; repeat split; try eassumption.
    rewrite <- H; eapply Denotational_B_BigStep_Sound.
    rewrite <- H0; eapply Denotational_B_BigStep_Sound.
  - (* E_ACIfFalseL *)
    left; right; subst; split; try eassumption.
    rewrite <- H; eapply Denotational_B_BigStep_Sound.
  - (* E_ACIfFalseR *)
    right; subst; split; try eassumption.
    rewrite <- H; eapply Denotational_B_BigStep_Sound.
  - (* E_ACWhileTrue *)
    apply LFP_unfold.
    apply while_body_monotone.
    right.
    In_inversion. In_intro. intuition.
    + rewrite <- H; apply Denotational_B_BigStep_Sound.
    + rewrite <- H0; apply Denotational_B_BigStep_Sound.
    + eexists _, _; intuition eauto.
  - (* E_ACWhileFalseL *)
    apply LFP_unfold; try apply while_body_monotone.
    left; left.
    In_intro. intuition.
    rewrite <- H; apply Denotational_B_BigStep_Sound.
  - (* E_ACWhileFalseR *)
      apply LFP_unfold; try apply while_body_monotone.
      left; right.
      In_intro. intuition.
      rewrite <- H; apply Denotational_B_BigStep_Sound.
Qed.

(* Finally, adequacy: *)
Lemma Denotational_BigStep_Adequate :
  forall r rst rst',
    (rst, rst') ∈ [[r]]R -> rst =<[r]>=> rst'.
Proof.
  induction r; intros;
    destruct rst as [stL stR];
    destruct rst' as [stL' stR'];
    simpl in *; try solve [econstructor]; In_inversion.
  - econstructor; simpl; eapply Denotational_BigStep_Adequate; eauto.
  - econstructor; eauto.
  - eapply E_ACIfTrue; eauto using BigStep_B_Denotational_Adequate; eauto.
  - eapply E_ACIfFalseL; eauto using BigStep_B_Denotational_Adequate; eauto.
  - eapply E_ACIfFalseR; eauto using BigStep_B_Denotational_Adequate; eauto.
  - replace (stL, stR) with (fst ((stL, stR), (stL', stR'))) by reflexivity.
    replace (stL', stR') with (snd ((stL, stR), (stL', stR'))) by reflexivity.
    remember (stL, stR, (stL', stR')).
    replace (fst (stL, stR, snd p)) with (fst p) by (subst; reflexivity).
    rewrite Heqp.
    revert IHr.
    pattern (stL, stR, (stL', stR')).
    eapply Ind; try eassumption; clear.
    intros[ [stL stR] [stL' stR'] ] ?.
    In_intro.
    simpl; In_inversion; intros.
    + subst; eapply E_ACWhileFalseL.
      erewrite BigStep_B_Denotational_Adequate; try reflexivity; assumption.
    + subst; eapply E_ACWhileFalseR.
      erewrite BigStep_B_Denotational_Adequate; try reflexivity; assumption.
    + eapply E_ACWhileTrue.
      * erewrite BigStep_B_Denotational_Adequate; try reflexivity; assumption.
      * erewrite BigStep_B_Denotational_Adequate; try reflexivity; assumption.
      * apply IHr; eassumption.
      * simpl in *; eauto.
Qed.

End Semantics.

Module notations.

  Notation "'[[' r ']]R'" := (denote_algn_com r) : denote_scope.

  Notation "rst =<[ r ]>=> rst'" := (aceval r rst rst').

End notations.
