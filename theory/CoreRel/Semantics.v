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
  Definition result := @result M. 


  Definition rel_state := (state * state)%type.
  Definition rel_result := (result * result)%type.

  (*If one errors -> both error*)

  Inductive aceval : algn_com -> rel_state -> rel_result -> Prop :=

  | E_ACBlockNormal : forall s1 s2 rst st1' st2',
      fst rst =[ s1 ]=> RNormal st1' ->
      snd rst =[ s2 ]=> RNormal st2' ->
      rst =<[ <| s1 | s2 |> ]>=> (RNormal st1', RNormal st2')

  | E_ACBlockErrorP1 : forall s1 s2 rst,
      fst rst =[ s1 ]=> RError ->
      rst =<[ <| s1 | s2 |> ]>=> (RError, RError) (*add P2*)

  | E_ACBlockErrorP2 : forall s1 s2 st rst,
      fst rst =[ s1 ]=> RNormal st ->
      snd rst =[ s2 ]=> RError ->
      rst =<[ <| s1 | s2 |> ]>=> (RError, RError) 

  | E_ACSeqNormal : forall r1 r2 rst st st' rst',
    rst =<[ r1 ]>=> (RNormal st, RNormal st') ->
    (st, st') =<[ r2 ]>=> rst' ->
    rst =<[ r1 ;; r2 ]>=> rst'
 
  | E_ACSeqError : forall r1 r2 rst,
    rst =<[ r1 ]>=> (RError, RError) ->
    rst =<[ r1 ;; r2 ]>=> (RError, RError)

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

  | E_ACWhileTrueNormal : forall b1 b2 r rst st st' rst',
    beval (fst rst) b1 = true ->
    beval (snd rst) b2 = true ->
    rst =<[ r ]>=> (RNormal st, RNormal st') ->
    (st, st') =<[ whileR <| b1 | b2 |> do r end ]>=> rst' ->
    rst =<[ whileR <| b1 | b2 |> do r end ]>=> rst'

  | E_ACWhileTrueError : forall b1 b2 r rst,
    beval (fst rst) b1 = true ->
    beval (snd rst) b2 = true ->
    rst =<[ r ]>=> (RError, RError) ->
    rst =<[ whileR <| b1 | b2 |> do r end ]>=> (RError, RError)

  | E_ACWhileFalseL : forall b1 b2 r st1 st2,
    beval st1 b1 = false ->
    (st1, st2) =<[ whileR <| b1 | b2 |> do r end ]>=> (RNormal st1, RNormal st2)

  | E_ACWhileFalseR : forall b1 b2 r st1 st2,
    beval st2 b2 = false ->
    (st1, st2) =<[ whileR <| b1 | b2 |> do r end ]>=> (RNormal st1, RNormal st2)

where "st =<[ r ]>=> st'" := (aceval r st st').

(* Second, a denotational semantics for CoreRel: *)
(* The semantic domain for commands is pairs of initial and final
   relational states: *)

Definition algn_com_dom := PSet (rel_state * rel_result)%type.

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
  combinator defined in Fixpoints.v. 


    <{c1; c2}> => {{ (st, st') |
                   (exists st'',
                   (st, RNormal st'') ∈ [[c1]] /\ (st'', st') ∈ [[c2]]) 
                 \/ ((st, RError) ∈ [[c1]] /\ st' = RError)}}

*)

(*Fixpoint denote_algn_com (r : algn_com) : algn_com_dom :=
  match r with
  | <{ <| s1 | s2 |> }> =>
      {{ ((stL, stR), (stL', stR')) |
         (exists st st', (stL, RNormal st) ∈ denote_Com s1 /\ (stR, RNormal st') ∈ denote_Com s2 
          /\ stL' = RNormal st /\ stR' = RNormal st') \/ ((stL, RError) ∈ denote_Com s1 
          /\ stL' = RError /\ stR' = RError) \/ (exists st, (stL, RNormal st) ∈ denote_Com s1 /\ 
          (stR, RError) ∈ denote_Com s2  /\ stL' = RError /\ stR' = RError) }}

  | <{ r1;; r2 }> =>
      {{ ((stL, stR), (stL', stR')) |
         (exists stL'' stR'',
         ((stL, stR), (RNormal stL'', RNormal stR'')) ∈ [[ r1 ]]R /\
           ((stL'', stR''), (stL', stR')) ∈ [[r2]]R ) \/ (((stL, stR), (RError, RError)) ∈ [[ r1 ]]R /\ stL' = RError /\ stR' = RError) }}

  | <{ ifR <| b1 | b2 |> then r1 else r2 end }> =>
      {{ ((stL, stR), (stL', stR')) |
          (   (true, stL) ∈ denote_B b1
          /\ (true, stR) ∈ (denote_B b2)
          /\ ((stL, stR), (stL', stR')) ∈ [[r1]]R)
      \/ ((false, stL) ∈ (denote_B b1)
             /\ ((stL, stR), (stL', stR')) ∈ [[r2]]R)
          \/ (false, stR) ∈ (denote_B b2)
             /\ ((stL, stR), (stL', stR')) ∈ [[r2]]R }}

  | <{ whileR <| b1 | b2 |> do r end }> =>
      LFP (fun (phi : algn_com_dom) =>
             {{ ((stL, stR), (stL', stR')) |
                ((false, stL) ∈ denote_B b1 /\ stL' = RNormal stL /\ stR' = RNormal stR)
                \/ ((false, stR) ∈ denote_B b2 /\ stL' = RNormal stL /\ stR' = RNormal stR)
                \/((true, stL) ∈ denote_B b1 /\
                    (true, stR) ∈ denote_B b2 /\
                      ((stL, stR), (RError, RError)) ∈ [[r]]R /\
                        stL' = RError /\ stR' = RError)
                \/((true, stL) ∈ denote_B b1 /\
                    (true, stR) ∈ denote_B b2 /\
                    exists stL'' stR'',
                      ((stL, stR), (RNormal stL'', RNormal stR'')) ∈ [[r]]R /\
                        ((stL'', stR''), (stL', stR')) ∈ phi) }})
  end
where "'[[' r ']]R'" := (denote_algn_com r) : denote_scope. *)


Fixpoint denote_algn_com (r : algn_com) : algn_com_dom :=
  match r with
  | <{ <| s1 | s2 |> }> =>
      {{ ((stL, stR), (stL', stR')) |
         (exists st st', (stL, RNormal st) ∈ denote_Com s1 /\ (stR, RNormal st') ∈ denote_Com s2 
          /\ stL' = RNormal st /\ stR' = RNormal st') }}

  | <{ r1;; r2 }> =>
      {{ ((stL, stR), (stL', stR')) |
         (exists stL'' stR'' stL''' stR''',
         ((stL, stR), (RNormal stL'', RNormal stR'')) ∈ [[ r1 ]]R /\
           ((stL'', stR''), (RNormal stL''', RNormal stR''')) ∈ [[r2]]R /\ stL' = RNormal stL''' /\ stR' = RNormal stR''') }}

  | <{ ifR <| b1 | b2 |> then r1 else r2 end }> =>
      {{ ((stL, stR), (stL', stR')) |
          (exists stL'' stR'', (true, stL) ∈ denote_B b1
          /\ (true, stR) ∈ (denote_B b2)
          /\ ((stL, stR), (RNormal stL'', RNormal stR'')) ∈ [[r1]]R /\ stL' = RNormal stL'' /\ stR' = RNormal stR'')
      \/ (exists stL'' stR'', (false, stL) ∈ (denote_B b1)
             /\ ((stL, stR), (RNormal stL'', RNormal stR'')) ∈ [[r2]]R /\ stL' = RNormal stL'' /\ stR' = RNormal stR'')
          \/ (exists stL'' stR'', (false, stR) ∈ (denote_B b2)
             /\ ((stL, stR), (RNormal stL'', RNormal stR'')) ∈ [[r2]]R /\ stL' = RNormal stL'' /\ stR' = RNormal stR'')}}

(*  rst =<[ r ]>=> (RNormal st, RNormal st') ->
    (st, st') =<[ whileR <| b1 | b2 |> do r end ]>=> rst' ->
    rst =<[ whileR <| b1 | b2 |> do r end ]>=> rst'*)

  | <{ whileR <| b1 | b2 |> do r end }> =>
      LFP (fun (phi : algn_com_dom) =>
             {{ ((stL, stR), (stL', stR')) |
                ((false, stL) ∈ denote_B b1 /\ stL' = RNormal stL /\ stR' = RNormal stR)
                \/ ((false, stR) ∈ denote_B b2 /\ stL' = RNormal stL /\ stR' = RNormal stR)
                \/((true, stL) ∈ denote_B b1 /\
                    (true, stR) ∈ denote_B b2 /\
                    exists stL'' stR'' stL''' stR''',
                      ((stL, stR), (RNormal stL'', RNormal stR'')) ∈ [[r]]R /\
                        ((stL'', stR''), (RNormal stL''', RNormal stR''')) ∈ phi /\ stL' = RNormal stL''' /\ stR' = RNormal stR''')}})
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
                ((false, stL) ∈ denote_B b1 /\ stL' = RNormal stL /\ stR' = RNormal stR)
                \/ ((false, stR) ∈ denote_B b2 /\ stL' = RNormal stL /\ stR' = RNormal stR)
                \/((true, stL) ∈ denote_B b1 /\
                    (true, stR) ∈ denote_B b2 /\
                    exists stL'' stR'' stL''' stR''',
                      ((stL, stR), (RNormal stL'', RNormal stR'')) ∈ [[r]]R /\
                        ((stL'', stR''), (RNormal stL''', RNormal stR''')) ∈ phi /\ stL' = RNormal stL''' /\ stR' = RNormal stR''') }}).
Proof.
  unfold Monotone, subseteq, set_subseteq_instance, rel_state.
  intros ? ? ? ? ? ? ((st1, st2), (st1', st2')) ?.
  In_inversion; In_intro.
  - firstorder.
  - firstorder.
  - right. firstorder. simpl in *. right.  firstorder. eexists _,_,_,_.
    simpl. split. eassumption. split. eapply H. eassumption.
    firstorder.
Qed. 

(* Now, soundness: *)
Lemma BigStep_Denotational_Sound :
  forall r rst st st',
    rst =<[r]>=> (RNormal st, RNormal st') -> (rst, (RNormal st, RNormal st')) ∈ [[r]]R.
Proof.
  intros. remember (RNormal st, RNormal st') as re eqn:Heqr.
  (*remember (rst =<[ r ]>=> (RNormal rst', RNormal rst'')) as re.*)
  (*rewrite Heqre in H. *)
    generalize dependent st. revert st'. induction H;
    try destruct rst as [stL stR]; 
    try destruct rst' as [stL' stR'];
    (*try destruct rst'' as [stL'' stR''];*)
    simpl in *; try solve [econstructor].
  - (* <s1 | s2> none errors *)
    intros. injection Heqr; intros; subst; clear Heqr. eexists _,_. split.
    eapply Imp.Semantics.BigStep_Denotational_Sound in H. eassumption.  
    split. eapply Imp.Semantics.BigStep_Denotational_Sound in H0.
    eassumption. auto.
  - (* <s1 | s2|>: s1 Error *)
     intros. discriminate.
  -  (*<s1 | s2>: s2 errors*)
    intros. discriminate.
  - (*<r1 ;; r2> none error*)
    intros. inversion Heqr. clear Heqr. subst. eexists _,_,_,_. split.
    specialize IHaceval1 with st' st. eapply IHaceval1. reflexivity.
    split. eapply IHaceval2. eauto. eauto.
  - (* <r1 ;; r2> : r1 error *)
    intros. discriminate. 
  - (*If - both true*)
    intros. inversion Heqr; clear Heqr; subst. left. eexists _,_. firstorder.
    rewrite <- H. eapply Denotational_B_BigStep_Sound. rewrite <- H0.
    eapply Denotational_B_BigStep_Sound. specialize IHaceval with st' st.
    apply IHaceval. reflexivity.
  - (*If - H b1 false *)
    intros. right. left. eexists _,_. split. rewrite <- H.
    eapply Denotational_B_BigStep_Sound. split. specialize IHaceval with st' st.
    rewrite Heqr in *. eapply IHaceval. reflexivity. inversion Heqr; clear Heqr; subst.
    eauto.
  - (*If - H b2 false *)
    intros. right. right. eexists _,_. split. rewrite <- H. eapply Denotational_B_BigStep_Sound.
    inversion Heqr; clear Heqr; subst. split. specialize IHaceval with st' st. eapply IHaceval.
    reflexivity. auto.
  - (* while - both true and normal *)
    intros. apply LFP_fold. try apply while_body_monotone. right. right. 
    split. rewrite <- H. apply Denotational_B_BigStep_Sound.
    split. rewrite <- H0. apply Denotational_B_BigStep_Sound. 
    eexists _,_,_,_. split. eapply IHaceval1 with st' st. reflexivity. 
    split. rewrite Heqr in *. clear Heqr. eapply IHaceval2 with st'0 st0.
    reflexivity. inversion Heqr; clear Heqr; subst. auto.
  - (*while error*)
    intros. discriminate.
  - (*while b1 is false*) 
    intros.  apply LFP_unfold. apply while_body_monotone. left.
    split. rewrite <- H. apply Denotational_B_BigStep_Sound. 
    inversion Heqr; clear Heqr; subst. auto.
  - (*while b2 is false*)
    intros. apply LFP_unfold. apply while_body_monotone. right. left. split.
    rewrite <- H. apply Denotational_B_BigStep_Sound. auto.
Qed.
    

(* Finally, adequacy: *)
Lemma Denotational_BigStep_Adequate :
  forall r rst st st',
    (rst, (RNormal st, RNormal st')) ∈ [[r]]R -> rst =<[r]>=> (RNormal st, RNormal st').
Proof.
  induction r; intros;
    destruct rst as [stL stR];
    simpl in *; try solve [econstructor]; In_inversion. 
  - (*<s1 | s2>*)
    simpl in *. inversion H1. inversion H2. econstructor.
    simpl. eapply Denotational_BigStep_Adequate. assumption.
    simpl. eapply Denotational_BigStep_Adequate. assumption.
  - (*<r1 ;; r2>*)
    simpl in *. inversion H1. inversion H2. econstructor.
    subst. eapply IHr1. eassumption. subst. eapply IHr2. assumption.
  - (*if - both true*)
    simpl in *. eapply E_ACIfTrue. simpl. eapply BigStep_B_Denotational_Adequate.
    assumption. simpl. eapply BigStep_B_Denotational_Adequate. assumption.
    specialize IHr1 with (stL, stR) st st'. apply IHr1. inversion H2; subst.
    inversion H3; subst. assumption.
  - (*if - b1 false*)
    simpl in *. eapply E_ACIfFalseL. simpl. eapply BigStep_B_Denotational_Adequate.
    assumption. specialize IHr2 with (stL, stR) st st'. apply IHr2. 
    inversion H1; subst. inversion H2; subst. assumption.
  - (*if - b2 is false*)
    simpl in *. eapply E_ACIfFalseR. simpl. eapply BigStep_B_Denotational_Adequate.
    assumption. specialize IHr2 with (stL, stR) st st'. apply IHr2. 
    inversion H1; subst. inversion H2; subst. assumption.
  - (*while*)
    replace (stL, stR) with (fst ((stL, stR), (RNormal st, RNormal st'))) by reflexivity.
    replace (RNormal st, RNormal st') with (snd ((stL, stR), (RNormal st, RNormal st'))) by reflexivity.
    remember (stL, stR, (RNormal st, RNormal st')).
    replace (fst (stL, stR, snd p)) with (fst p) by (subst; reflexivity).
    rewrite Heqp.
    revert IHr.
    pattern (stL, stR, (RNormal st, RNormal st')).
    eapply Ind; try eassumption; clear.
    intros[ [stL stR] [stL' stR'] ] ? ?.
    simpl; In_inversion; intros.
    + compute in H0, H1. subst; eapply E_ACWhileFalseL.
      erewrite BigStep_B_Denotational_Adequate; try reflexivity; assumption.
    + simpl in *; compute in H0, H1; subst. eapply E_ACWhileFalseR.
      erewrite BigStep_B_Denotational_Adequate; try reflexivity; assumption.
    + eapply E_ACWhileTrueNormal.
      * erewrite BigStep_B_Denotational_Adequate; try reflexivity; assumption.
      * erewrite BigStep_B_Denotational_Adequate; try reflexivity; assumption.
      * apply IHr; eassumption.
      * simpl in *. inversion H3; subst. inversion H4; subst. eauto. 
Qed.

End Semantics.

Module notations.

  Notation "'[[' r ']]R'" := (denote_algn_com r) : denote_scope.

  Notation "rst =<[ r ]>=> rst'" := (aceval r rst rst').

End notations.
