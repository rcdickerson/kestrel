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
   intros r1 r1' r1_eqv c2 c2' c2_eqv ((st1, st2), (st1', st2')). simpl. split.
   intros. In_inversion. simpl in *. eexists _,_,_,_. split. eapply r1_eqv.
   eassumption. split. eapply c2_eqv. eassumption. inversion H1; subst.
   inversion H2; subst. auto.
   intros. In_inversion. simpl in *. eexists _,_,_,_. split. 
   eapply r1_eqv. eassumption. split.
   apply c2_eqv. eassumption. inversion H1; subst. inversion H2; subst.
   auto.
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
          apply while_body_monotone. simpl in *. right. right.
          split. apply b1_eqv. assumption. split. apply b2_eqv.
          assumption. eexists _,_,_,_. split. apply r1_eqv.
          eassumption. split. eassumption. firstorder.
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
          apply while_body_monotone. simpl in *. right. right.
          split. apply b1_eqv. assumption. split. apply b2_eqv.
          assumption. eexists _,_,_,_. split. apply r1_eqv. 
          eassumption. split. eassumption. firstorder.
  Qed.

  (* More interestingly, we can prove analogues of algebraic
     equivalences from the BiKAT paper: - Prove from here*)

  Lemma rel_def : forall s1 s2,
      <{ <|s1 | s2|> }> ==R <{ <| s1 | skip|>;; <|skip | s2 |> }>.
  Proof.
   intros s1 s2 ((st1, st2), (st1', st2')); firstorder;
   simpl in *; In_inversion; subst. firstorder.
   (*Normal, Normal*)
   eexists _,_,_,_. split. eexists _,_. split. eassumption.
   split. firstorder. eauto. split. eexists _,_. split. 
   firstorder. split. eassumption. eauto. auto. 
   eexists _,_. split. eassumption. split. rewrite <- H6 in H8.
   inversion H8; subst. eassumption. rewrite H0 in H7.
   rewrite H7 in H4. auto.
 Qed.
   
 Lemma rel_comm : forall s1 s2,
      <{ <| skip | s2 |>;; <|s1 | skip |> }> ==R <{ <| s1 | skip|>;; <|skip | s2 |> }>.
 Proof.
   intros s1 s2 ((st1, st2), (st1', st2')); firstorder;
   simpl in *; In_inversion; firstorder. 
   (*Normal, Normal*)
   eexists _,_,_,_. split. eexists _,_. split. rewrite <- H7 in H.
   inversion H; subst. eassumption. firstorder. 
   split. eexists _,_. firstorder. eassumption. rewrite H8 in H3.
   rewrite <- H3 in H5. auto.
   (*Normal, Normal*)
   eexists _,_,_,_. split. eexists _,_. split. firstorder.
   split. rewrite <- H6 in H8. inversion H8; subst. eassumption. eauto.
   (*Normal, Normal*)
   split. eexists _,_. split. eassumption. firstorder. 
   rewrite <- H0 in H4. rewrite <- H4 in H7. auto.
 Qed.

  Lemma prod_hom_l : forall s1 s2,
      <{ <|s1; s2 | skip|> }> ==R <{ <| s1 | skip|>;; <|s2 | skip |> }>.
  Proof.
    intros s1 s2 ((st1, st2), (st1', st2')); firstorder;
    simpl in *; In_inversion; firstorder. 
    eexists _,_,_,_. split. eexists _,_. firstorder. eassumption.
    split. eexists _,_. firstorder. eassumption. auto.
    eexists _,_. split. left. eexists. split. eassumption.
    inversion H7; subst. eassumption.
    firstorder. rewrite <- H5 in H3. rewrite H3 in H8. 
    rewrite <- H8 in H6. symmetry. assumption.
  Qed.    

  Lemma prod_hom_r : forall s1 s2,
      <{ <| skip | s1; s2|> }> ==R <{ <| skip | s1 |>;; <|skip | s2 |> }>.
  Proof.
    intros s1 s2 ((st1, st2), (st1', st2')); firstorder;
    simpl in *; In_inversion; firstorder.
    eexists _,_,_,_. split. eexists _,_. firstorder. eassumption.
    split. eexists _,_. firstorder. eassumption. auto.
    eexists _,_. firstorder. left. eexists. split. 
    eassumption. inversion H5; subst. inversion H8; subst.
    assumption. rewrite <- H0 in H4. rewrite <- H7 in H.
    rewrite <- H in H4. assumption.   
  Qed.

  Lemma prod_seq_assoc : forall r1 r2 r3,
      <{ (r1 ;; r2);; r3  }> ==R <{ r1;; r2;; r3 }>.
  Proof.
    intros r1 r2 r3 ((st1, st2), (st1', st2')); firstorder;
    simpl in *; In_inversion; firstorder. 
    eexists _,_,_,_. split. eassumption. split. 
    eexists _,_,_,_. firstorder. eassumption. inversion H4; subst.
    inversion H5; subst. eassumption. auto.
    eexists _,_,_,_. split. eexists _,_,_,_. firstorder. 
    eassumption. eassumption. firstorder. eassumption. 
    rewrite H4 in H1. assumption. rewrite H5 in H2. assumption.
  Qed.

(*problem*)
  Lemma if_align : forall b1 b2 c1 c2 c3 c4,
      <{ <| if b1 then c1 else c2 end | if b2 then c3 else c4 end |> }>
      ==R <{ifR <|b1 | b2|> then <|c1 | c3|> else ifR <|b1 | BNot b2|> then <|c1 | c4|>
            else ifR <|BNot b1 | b2|> then <|c2 | c3|> else <|c2 | c4|> end end end}> .
  Proof.
   intros b1 b2 c1 c2 c3 c4 ((st1, st2), (st1', st2')); firstorder;
   simpl in *; In_inversion; firstorder.
   (*true, true*)
   left. eexists _,_. firstorder. eexists _,_. firstorder.
   eassumption. eassumption. assumption. assumption.
   (*false true*)
   right. left. eexists _,_. split. assumption. split. right.
   left. eexists _,_. split. assumption. split. left.
   eexists _,_. firstorder. eexists _,_. firstorder. 
   eassumption. eassumption. eauto. auto.
   (*true false*)
   right. right. eexists _,_. firstorder. left. eexists _,_.
   firstorder. eexists _,_. firstorder. eassumption. eassumption.
   assumption. assumption.
   (*false false*)
   right. right. eexists _,_. split. assumption. split. right.
   left. eexists _,_. split. assumption. split. right. right.
   eexists _,_. firstorder. eexists _,_. firstorder. eassumption.
   eassumption. eauto. auto.
   (*true true*) 
   eexists _,_. split. left. firstorder. eassumption.
   split. left. firstorder. eassumption. rewrite H5 in H2.
   rewrite H6 in H3. auto.
   (*discriminate*)
   apply bexp_eqv_unique with b1 false true st1 in H.
   discriminate H. assumption.
   (*false true*)
   simpl in H3. eexists _,_. split. right. firstorder.
   eassumption. split. left. firstorder. eassumption. 
   rewrite H11 in H8. rewrite H8 in H4. rewrite H4 in H1.
   rewrite H12 in H9. rewrite H9 in H5. rewrite H5 in H2. auto.
   (*discriminate*)
   simpl in H3. apply bexp_eqv_unique with b1 false true st1 in H.
   discriminate H. assumption.
   (*false false*)
   eexists _,_. split. right. firstorder. eassumption. split.
   right. firstorder. eassumption. rewrite H10 in H7.
   rewrite H7 in H4. rewrite H4 in H1. rewrite H11 in H8.
   rewrite H8 in H5. rewrite H5 in H2. auto.
   (*false true*)
   simpl in H0,H3. eexists _,_. split. right. firstorder.
   eassumption. split. left. firstorder. eassumption. 
   (*H11 -> H8 -> H4 -> H1*)
   rewrite H11 in H8. rewrite H8 in H4. rewrite H4 in H1.
   (*H12 -> H9 -> H5 -> H2*)
   rewrite H12 in H9. rewrite H9 in H5. rewrite H5 in H2. auto.
   (*discriminate*)
   simpl in H0, H3. apply bexp_eqv_unique with b1 false true st1 in H.
   discriminate H. assumption.
   (*dicriminate*)
   simpl in H0. apply bexp_eqv_unique with b2 true false st2 in H0.
   discriminate H0. assumption.
   (*true false*)
   simpl in H3. eexists _,_. split. left. firstorder. eassumption.
   split. right. firstorder. eassumption. 
   (*H8 -> H5 -> H1*) rewrite H8 in H5. rewrite H5 in H1.
   (*H9 -> H6 -> H2*) rewrite H9 in H6. rewrite H6 in H2. auto.
   (*discriminate*)
   simpl in *. apply bexp_eqv_unique with b2 false true st2 in H.
   discriminate H. assumption.
   (*discriminate*)
   simpl in *. apply bexp_eqv_unique with b1 true false st1 in H3.
   discriminate H3. assumption.
   (*false false*)
   eexists _,_. split. right. firstorder. eassumption. split.
   right. firstorder. eassumption. 
   (*H10 -> H7 -> H4 -> H1*) rewrite H10 in H7. rewrite H7 in H4.
   rewrite H4 in H1.
   (*H11 -> H8 -> H5 -> H2*) rewrite H11 in H8. rewrite H8 in H5.
   rewrite H5 in H2. auto.
   (*discriminate*)
   simpl in *. apply bexp_eqv_unique with b2 true false st2 in H0.
   discriminate H0. assumption. 
   (*discriminate*)
   simpl in *. apply bexp_eqv_unique with b2 true false st2 in H0.
   discriminate H0. assumption. 
   (*discriminate*)
   simpl in *. apply bexp_eqv_unique with b2 true false st2 in H0.
   discriminate H0. assumption.
 Qed. 

   
  (*From here*)
 Lemma whileR_false_L : forall b1 b2 r,
      bexp_eqv b1 <{false}> ->
      <{ whileR <|b1 | b2|> do r end  }> ==R <{ <|skip|skip|> }> .
  Proof.
   
    intros b1 b2 r b1_eqv ((st1, st2), (st1', st2')); 
      simpl in *; split; intros; In_inversion. 
      apply LFP_fold in H. In_inversion; subst.
      (*b1 is false*)
      simpl in *. eexists _,_. firstorder.
      simpl in *. eexists _,_. firstorder.
      simpl in *. apply b1_eqv in H. discriminate H.
      apply while_body_monotone. apply LFP_unfold.
      apply while_body_monotone. left. firstorder. 
      inversion H; subst. inversion H0; subst. 
      inversion H1; subst. inversion H2; subst. reflexivity.
      inversion H2; subst. symmetry. assumption.
  Qed.


  Lemma whileR_false_R : forall b1 b2 r,
      bexp_eqv b2 <{false}> ->
      <{ whileR <|b1 | b2|> do r end  }> ==R <{ <|skip|skip|> }> .
  Proof.
      intros b1 b2 r b1_eqv ((st1, st2), (st1', st2')); 
      simpl in *; split; intros; In_inversion. 
      apply LFP_fold in H. In_inversion; subst.
      (*b1 is false*)
      simpl in *. eexists _,_. firstorder.
      simpl in *. eexists _,_. firstorder.
      simpl in *. apply b1_eqv in H0. discriminate H0.
      apply while_body_monotone. apply LFP_unfold.
      apply while_body_monotone. right. left. firstorder. 
      inversion H; subst. inversion H0; subst.  
      inversion H1; subst. inversion H2; subst. reflexivity.
      inversion H2; subst. symmetry. assumption.
  Qed.

  (*Normal -> Normal*)
  Lemma whileI_false_L : forall b r st,
     (denote_B b) (false, st)->
      denote_Com <{ while b do r end }> (st, RNormal st).
  Proof.
    firstorder.
  Qed.

 (*Normal -> Normal*)
  Lemma whileR_false_L' : forall b1 b2 r st1 st2,
      (denote_B b1) (false, st1) ->
      [[<{ whileR <|b1 | b2|> do r end  }>]]R (st1, st2, (RNormal st1, RNormal st2)).
  Proof.
    firstorder.
  Qed.

  Lemma whileR_false_R' : forall b1 b2 r st1 st2,
      (denote_B b2) (false, st2) ->
      [[<{ whileR <|b1 | b2|> do r end  }>]]R (st1, st2, (RNormal st1, RNormal st2)).
  Proof.
    firstorder.
  Qed.

  Lemma whileR_false_L'' : forall b1 b2 r st1 st2 st1' st2',
      (denote_B b1) (false, st1) ->
      [[<{ whileR <|b1 | b2|> do r end  }>]]R (st1, st2, (RNormal st1', RNormal st2')) ->
      st1 = st1' /\ st2 = st2'.
  Proof.
    simpl; intros.
    apply LFP_fold in H0; try apply while_body_monotone.
    In_inversion.
    - compute in H0, H1; subst; firstorder. inversion H1; subst. reflexivity.
      inversion H2. reflexivity.
    - compute in H0, H1; subst; firstorder. inversion H1; subst. reflexivity.
      inversion H2. reflexivity.
    - apply BigStep_B_Denotational_Adequate in H;
        apply BigStep_B_Denotational_Adequate in H0; simpl in *; congruence.
  Qed.

  Lemma whileR_false_R'' : forall b1 b2 r st1 st2 st1' st2',
      (denote_B b2) (false, st2) ->
      [[<{ whileR <|b1 | b2|> do r end  }>]]R (st1, st2, (RNormal st1', RNormal st2')) ->
      st1 = st1' /\ st2 = st2'.
  Proof.
    simpl; intros.
    apply LFP_fold in H0; try apply while_body_monotone.
    In_inversion.
    - compute in H0, H1; subst; firstorder. inversion H1; subst. reflexivity.
      inversion H2. reflexivity.
    - compute in H0, H1; subst; firstorder. inversion H1; subst. reflexivity.
      inversion H2. reflexivity.
    - simpl in *. apply BigStep_B_Denotational_Adequate in H.
      apply BigStep_B_Denotational_Adequate in H1. rewrite H1 in H.
      discriminate H.
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
      + firstorder. simpl in H. eapply whileR_false_L'. eauto.      
        unfold FClosed.
        intros ((stL, stR), (stL', stR')) ?.
        In_inversion; subst.
        simpl in *. eexists _,_,_,_. split. right. left.
        eexists _,_. firstorder. eexists _,_. firstorder.
        split. apply LFP_fold. apply while_body_monotone. 
        left. firstorder. inversion H1; subst. inversion H2; subst.
        simpl. auto. simpl in H0.
        eexists _,_,_,_. split. right. right. eexists _,_.
        firstorder. eassumption.  eexists _,_. firstorder.
        split. apply LFP_unfold. apply while_body_monotone.
        right. left. firstorder. inversion H1; subst. inversion H2; subst.
        simpl. auto.
        simpl in *. (*true, true*) eexists _,_,_,_. split. left. eexists _,_.
        firstorder. eassumption. split. apply LFP_unfold. apply while_body_monotone.
        (*true true*) right. right. firstorder. eexists _,_,_,_. split.
        eassumption. split. inversion H11; subst. inversion H12; subst. eassumption.
        eauto. inversion H4; subst. inversion H5; subst. auto.
        simpl in *. (*true true*) 
        apply LFP_fold in H6. In_inversion; subst. 
        compute in H4,H5,H7,H8,H10,H11,H13,H14,H15,H16. simpl in H6.
        eexists _,_,_,_. split. left. eexists _,_. firstorder. eassumption.
        firstorder. rewrite H4. rewrite <- H9 in H13. rewrite H13 in H10.
        rewrite H10 in H15. rewrite H15 in H7. assumption.
        rewrite H5. rewrite <- H12 in H14. rewrite H14 in H11. rewrite H11 in H16.
        rewrite H16 in H8. assumption.
        simpl in H6. compute in H4,H5,H7,H8,H10,H11,H13,H14,H15,H16. eexists _,_,_,_.
        split. left. eexists _,_. firstorder. eassumption. firstorder.
        rewrite H4. rewrite <- H9 in H13. rewrite H13 in H10.
        rewrite H10 in H15. rewrite H15 in H7. assumption. 
        rewrite H5. rewrite <- H12 in H14. rewrite H14 in H11. rewrite H11 in H16.
        rewrite H16 in H8. assumption.
        simpl in *.
        compute in  H4,H5,H7,H8,H10,H11,H13,H14, H18, H19. rewrite H13 in H10.
        rewrite <- H9 in H10. inversion H10; subst. apply bexp_eqv_unique with b1 false true stL'' in H3.
        discriminate H3. assumption. apply while_body_monotone.
        simpl in H0,H1,H2,H3. compute in H4,H5,H7,H8,H10,H11,H13,H14.
        eexists _,_,_,_. split. left. eexists _,_. firstorder. eassumption. split.
        rewrite <- H9 in H13. rewrite H13 in H10. inversion H10; subst.
        rewrite <- H12 in H14. rewrite H14 in H11. inversion H11; subst. eassumption.
        rewrite H4. rewrite H5. auto.
      - (*b2 is false*) simpl in H. compute in H0, H1. subst. eexists _,_,_,_. split. right.
        right. eexists _,_. firstorder. eexists _,_. firstorder. split.
        firstorder. auto.
      - (*true, true*) simpl in H,H0,H1. compute in H3, H4. subst. eexists _,_,_,_.
        split. left. eexists _,_. firstorder. eassumption. split. eassumption. auto.
      - (*true, true*) compute in H1,H2,H5,H6. subst. apply LFP_fold. apply while_body_monotone.
        right. right. firstorder. eexists _,_,_,_. split. eassumption. inversion H5; subst. 
        inversion H6; subst. split. eassumption. auto.
      - (*b1 is false*) compute in H1,H2,H4,H5,H7,H8. subst. rewrite <- H3 in H7.
        rewrite H7 in H4. rewrite <- H6 in H8. rewrite H8 in H5. inversion H4; subst. inversion H5; subst.
        assumption.
     - (*b2 is false*) compute in H1,H2,H4,H5,H7,H8. subst. rewrite <- H3 in H7. rewrite H7 in H4.
        rewrite <- H6 in H8. rewrite H8 in H5. inversion H4; subst. inversion H5; subst.
        assumption.
  Qed.


  Lemma whileR_lockstep : forall b1 b2 s1 s2,
      <{ <| while b1 do s1 end | while b2 do s2 end |>  }>
      ==R <{whileR <|b1 | b2|> do <|s1 | s2|> end;;
          <| while b1 do s1 end | while b2 do s2 end |> }>.
  Proof.
    intros b1 b2 s1 s2 ((st1, st2), (st1', st2')); split; intros. inversion H; subst.
    inversion H0; subst. destruct H1 as [H11 H12]. destruct H12 as [H121 H122].
    destruct H122 as [? ?]. subst. 
    (*bring it to form suitable for induction*)
    eapply Imp.Semantics.Denotational_BigStep_Adequate in H11. 
    eapply Imp.Semantics.Denotational_BigStep_Adequate in H121.
    eapply CR.Semantics.BigStep_Denotational_Sound. clear H. clear H0.
    remember <{ while b1 do s1 end}>. remember (RNormal x).  
    generalize dependent st2. generalize dependent s2. generalize dependent b2.
    induction H11. discriminate. discriminate. discriminate. discriminate.
    discriminate. discriminate. injection Heqc; intros; subst; clear Heqc.
    (*sequence: normal, normal*)
    eapply E_ACSeqNormal. 
    (*L - false*) eapply E_ACWhileFalseL; simpl; eauto.
    (*<| s1 | s2 |> Normal*) eapply E_ACBlockNormal; simpl; eauto.
    (*L - false Imp: Normal*) eapply E_WhileFalse; eauto. 
    (*while*) intros. clear IHcevalr1. inversion H121; subst; intros.
    econstructor. eapply E_ACWhileFalseR; simpl; eauto. 
    econstructor; eauto. simpl. eapply E_WhileTrueNormal; eauto.
    (*b2 is true*) injection Heqc; intros; subst; clear Heqc. 
    eapply CR.Semantics.Denotational_BigStep_Adequate.
    eapply ACSeq_eqv_cong. eapply whileR_unroll. reflexivity. eapply prod_seq_assoc.
    eapply CR.Semantics.BigStep_Denotational_Sound. econstructor. econstructor; eauto.
    econstructor; eauto. eapply IHcevalr2; eauto.
    (*error - discriminate*) discriminate.
    (*no match - discriminate*) discriminate.
    (*error - discriminate*) discriminate.
    (*OTHER SIDE*)
    inversion H; subst. inversion H0; subst. inversion H1; subst. inversion H2; subst.
    clear H0. clear H1. clear H2. clear H. destruct H3 as [? ?]. destruct H0 as [? ?].
    destruct H1 as [? ?]. subst. eapply CR.Semantics.Denotational_BigStep_Adequate in H, H0.
    remember <{whileR <| b1 | b2 |> do <| s1 | s2 |> end}> as r eqn:Heqr. 
    remember (RNormal x, RNormal x0). generalize dependent x1. generalize dependent x2.
    induction H. discriminate. discriminate. discriminate. discriminate. discriminate.
    discriminate. discriminate. discriminate.
    (*while - while*) injection Heqr; intros; subst; clear Heqr. 
    clear IHaceval1. firstorder. eapply block_eqv_cong.
    eapply If_while_eq. eapply If_while_eq. eapply CR.Semantics.BigStep_Denotational_Sound.
    specialize H3 with x2 x1. apply H3 in H6. 
    eapply CR.Semantics.Denotational_BigStep_Adequate in H6. 
    econstructor; eauto. econstructor; eauto.
    econstructor; eauto. inversion H1; subst. eassumption.
    inversion H6; subst. eauto. econstructor; eauto.
    econstructor; eauto. inversion H1; subst. eauto. inversion H6; subst; eauto.
    (*Error, Normal*) discriminate.
    (*while, Normal*) injection Heqr; subst; clear Heqr. injection Heqp; subst; clear Heqp.
    intros. subst.  eapply CR.Semantics.BigStep_Denotational_Sound; eauto.
    (*while, Normal*) injection Heqr; subst; clear Heqr. injection Heqp; subst; clear Heqp.
    intros. subst.  eapply CR.Semantics.BigStep_Denotational_Sound; eauto.
   
  Qed.

Check <{ <| skip | skip|> }>.

 Lemma bnegb_equiv: forall b st, negb (beval st b) = (beval st (BNot b)).
 Proof.
   intros. simpl. reflexivity. Qed.


(*This is potentially problemmatic as it requires inverting the safe lemmas into comm. form
  - Inverting over ∉ lemmas aren't there. I tried to write them, but proving is problemmatic. *)
 Lemma whileR_lockstep_ : forall b1 b2 s1 s2,
    (*put safety assumption here: 
       Safe p is equivalent to error not in denotation of p
       Safe p1 /\ Safe p2 => (p1 eqv. p2)*)
     forall (r_safe1: forall stl str, 
     ~((stl, str) =<[<{whileR <|b1 | b2|> do <|s1 | s2|> end;;<| assert ~b1 | assert ~b2|>}>]>=> (RError,RError))),
     <{ <| while b1 do s1 end | while b2 do s2 end |>  }> ==R 
     <{whileR <|b1 | b2|> do <|s1 | s2|> end;;<| assert ~b1 | assert ~b2|>}> .
  Proof. 
   intros b1 b2 s1 s2 H1 H2. destruct H2 as ((stl, str), (stl', str')); split; intros. 
   inversion H; subst. inversion H0; subst. destruct H2 as [H31 H32]. destruct H32 as [H321 H322]. destruct H322 as [? ?]; subst.
   eapply Imp.Semantics.Denotational_BigStep_Adequate in H31, H321.
   eapply CR.Semantics.BigStep_Denotational_Sound. clear H. clear H0.
   remember <{ while b1 do s1 end}>. remember (RNormal x).  
   generalize dependent str. generalize dependent s2. generalize dependent b2.
   induction H31; try discriminate.
   injection Heqc; intros; subst; clear Heqc. 
   (*apply constructor*) eapply E_ACSeqNormal. eapply E_ACWhileFalseL; simpl; eauto.
   (*< | s1 | s2 |> - Normal*) eapply E_ACBlockNormal; simpl; eauto. 
   (*assert - Normal will go through*) eapply E_AssertNormal. simpl.
   rewrite H. simpl. reflexivity.
   (*induction on H321*) remember <{ while b2 do s2 end}>. remember (RNormal x0).
   generalize dependent s1. generalize dependent b1. generalize dependent Heqr.
   generalize dependent x. generalize dependent st. induction H321; try discriminate.
   injection Heqc; intros; subst; clear Heqc. (*assert Normal will go through*) eapply E_AssertNormal.
   simpl. rewrite H. simpl. reflexivity.
   (*true or ~b false case - error case*) injection Heqc; intros; subst; clear Heqc. 
   clear IHcevalr1. clear IHcevalr2. Search negb. eapply negb_false_iff in H.
   rewrite bnegb_equiv in H. (*assert Error - discriminate*) eapply E_AssertError in H.
   eapply Imp.Semantics.BigStep_Denotational_Sound in H.
   specialize H3 with st0 st. unfold not in H3. destruct H3. econstructor.
   eapply E_ACWhileFalseL. assumption. (*assert Normal : ~b1*) eapply negb_true_iff in H2.
   rewrite bnegb_equiv in H2. eapply E_AssertNormal in H2. 
   (*denotation to operational in H*) eapply Imp.Semantics.Denotational_BigStep_Adequate in H.
   eapply E_ACBlockErrorP2. simpl. eassumption. simpl. assumption.
   intros. clear IHcevalr1. injection Heqc; intros; subst; clear Heqc. subst. 
   inversion H321; subst; intros.
   econstructor. eapply E_ACWhileFalseR; simpl; eauto. 
   specialize H1 with st x0. unfold not in H1. destruct H1. econstructor.
   eapply E_ACWhileFalseR. assumption. eapply negb_true_iff in H4.
   rewrite bnegb_equiv in H4. eapply E_AssertNormal in H4. eapply negb_false_iff in H.
   rewrite bnegb_equiv in H. eapply E_AssertError in H. eapply E_ACBlockErrorP1.
   simpl. eassumption.
   (*b2 is true*) 
   eapply CR.Semantics.Denotational_BigStep_Adequate.
   eapply ACSeq_eqv_cong. eapply whileR_unroll. reflexivity. eapply prod_seq_assoc.
   eapply CR.Semantics.BigStep_Denotational_Sound. econstructor. econstructor; eauto.
   econstructor; eauto. eapply IHcevalr2; eauto.
   (*other side*)
   inversion H; subst. inversion H0; subst. inversion H2; subst. inversion H3; subst.
   clear H0. clear H2. clear H3. clear H. destruct H4 as [? ?]. destruct H0 as [? ?].
   destruct H2 as [? ?]; subst. eapply CR.Semantics.Denotational_BigStep_Adequate in H, H0.
   remember <{whileR <| b1 | b2 |> do <| s1 | s2 |> end}> as r eqn:Heqr. 
   remember (RNormal x, RNormal x0). generalize dependent x1. generalize dependent x2.
   induction H; try discriminate. 
   (*while - while*) injection Heqr; intros; subst; clear Heqr.
   clear IHaceval1. firstorder. eapply block_eqv_cong.
   eapply If_while_eq. eapply If_while_eq. eapply CR.Semantics.BigStep_Denotational_Sound. 
   specialize H4 with x2 x1. apply H4 in H7. 
   eapply CR.Semantics.Denotational_BigStep_Adequate in H7.
   econstructor; eauto. econstructor; eauto. econstructor; eauto. 
   inversion H2; subst. eassumption. inversion H7; subst. eauto. econstructor; eauto.
   econstructor; eauto. inversion H2; subst. eauto. inversion H7; subst; eauto. 
   (*second last*)
   injection Heqr; subst; clear Heqr. injection Heqp; subst; clear Heqp.
   intros; subst. eapply CR.Semantics.BigStep_Denotational_Sound. 
   inversion H6; subst. simpl in H5,H8. 
   inversion H5; subst. inversion H8; subst. simpl in H4,H7. eapply negb_true_iff in H7.
   constructor; simpl. eapply E_WhileFalse. assumption. eapply E_WhileFalse. assumption.
   (*last*) 
   injection Heqr; subst; clear Heqr. injection Heqp; intros; subst; clear Heqp.
   eapply CR.Semantics.BigStep_Denotational_Sound; eauto.
   (*Block - assert Error*) inversion H6; subst. simpl in H5,H8. eapply negb_true_iff in H. 
   rewrite bnegb_equiv in H. eapply E_AssertNormal in H. subst. 
   inversion H5; subst.  (*<| s1 | s2 | >*) eapply E_ACBlockNormal; simpl; eauto.
   simpl in H4. eapply negb_true_iff in H4. eapply E_WhileFalse. assumption.
   inversion H8; subst. simpl in H7. eapply negb_true_iff in H7. eapply E_WhileFalse. assumption.
 Qed.

  (*ifR <|b1 | BNot b2|> then <| while b1 do s1 end | skip|> else ifR <|BNot b1 | b2|> then <|skip | while b2 do s2 end|>
     else < skip | skip > end end end*)  
 Lemma whileR_lockstep2: forall b1 b2 s1 s2, 
     forall (r_safe2: forall stl str, (stl,RError) ∉ denote_Com <{  assert (~ b1) }> /\ (str,RError) ∉ denote_Com <{  assert (~ b2) }>),
     <{ <| while b1 do s1 end | while b2 do s2 end |>  }> ==R 
     <{whileR <|b1 | b2|> do <|s1 | s2|> end;;<| assert ~b1 | assert ~b2|>}> .
  Proof. 
   intros b1 b2 s1 s2 H1 H2. destruct H2 as ((stl, str), (stl', str')); split; intros. 
   inversion H; subst. inversion H0; subst. destruct H2 as [H31 H32]. destruct H32 as [H321 H322]. destruct H322 as [? ?]; subst.
   eapply Imp.Semantics.Denotational_BigStep_Adequate in H31, H321.
   eapply CR.Semantics.BigStep_Denotational_Sound. clear H. clear H0.
   remember <{ while b1 do s1 end}>. remember (RNormal x).  
   generalize dependent str. generalize dependent s2. generalize dependent b2.
   induction H31; try discriminate.
   injection Heqc; intros; subst; clear Heqc. 
   (*apply constructor*) eapply E_ACSeqNormal. eapply E_ACWhileFalseL; simpl; eauto.
   (*< | s1 | s2 |> - Normal*) eapply E_ACBlockNormal; simpl; eauto. 
   (*assert - Normal will go through*) eapply E_AssertNormal. simpl.
   rewrite H. simpl. reflexivity.
   (*induction on H321*) remember <{ while b2 do s2 end}>. remember (RNormal x0).
   generalize dependent s1. generalize dependent b1. generalize dependent Heqr.
   generalize dependent x. generalize dependent st. induction H321; try discriminate.
   injection Heqc; intros; subst; clear Heqc. (*assert Normal will go through*) eapply E_AssertNormal.
   simpl. rewrite H. simpl. reflexivity.
   (*true or ~b false case - error case*) injection Heqc; intros; subst; clear Heqc. 
   clear IHcevalr1. clear IHcevalr2. Search negb. eapply negb_false_iff in H.
   rewrite bnegb_equiv in H. (*assert Error - discriminate*) eapply E_AssertError in H.
   eapply Imp.Semantics.BigStep_Denotational_Sound in H.
   specialize H3 with st0 st. destruct H3 as [H31 H32]. contradiction. intros. 
   injection Heqc; intros; subst; clear Heqc. clear IHcevalr1. clear IHcevalr2.
   (*b1 to negb - Error - contradiction*) eapply negb_false_iff in H. rewrite bnegb_equiv in H.
   eapply E_AssertError in H. eapply Imp.Semantics.BigStep_Denotational_Sound in H. 
   specialize H1 with st str. destruct H1 as [? ?]. contradiction. 
   (*second case*) 
    inversion H; subst. inversion H0; subst. inversion H2; subst. inversion H3; subst. 
   clear H0. clear H2. clear H3. clear H. destruct H4 as [? ?]. destruct H0 as [? ?].
   destruct H2 as [? ?]; subst. eapply CR.Semantics.Denotational_BigStep_Adequate in H, H0.
   remember <{whileR <| b1 | b2 |> do <| s1 | s2 |> end}> as r eqn:Heqr. 
   remember (RNormal x, RNormal x0). generalize dependent x1. generalize dependent x2.
   generalize dependent H1. induction H; try discriminate.
   injection Heqr; intros; subst; clear Heqr. clear IHaceval1. clear IHaceval2.
   (*b1 to negb - Error - contradiction*) eapply negb_false_iff in H. rewrite bnegb_equiv in H.
   eapply E_AssertError in H. eapply Imp.Semantics.BigStep_Denotational_Sound in H.
   specialize H6 with rst.1 rst.2. destruct H6 as [? ?]. contradiction.
   injection Heqr; subst; clear Heqr. injection Heqp; intros; subst; clear Heqp.
   eapply CR.Semantics.BigStep_Denotational_Sound; eauto.
   (*Block - assert Error*) inversion H6. simpl in H4. eapply negb_true_iff in H. 
   rewrite bnegb_equiv in H. eapply E_AssertNormal in H. subst. simpl in H8.
   inversion H4; subst.  (*<| s1 | s2 | >*) eapply E_ACBlockNormal; simpl; eauto.
   eapply Imp.Semantics.Denotational_BigStep_Adequate. eapply whileI_false_L.
   eapply bexp_denoterev. rewrite <- bnegb_equiv in H3. apply negb_true_iff in H3.
   rewrite <- H3. apply Denotational_B_BigStep_Sound. clear H3.
   inversion H8; subst. eapply Imp.Semantics.Denotational_BigStep_Adequate.
   eapply whileI_false_L. eapply bexp_denoterev.  rewrite <- bnegb_equiv in H3.
   apply negb_true_iff in H3. rewrite <- H3. apply Denotational_B_BigStep_Sound.
   (*last case*)
   injection Heqr; subst; clear Heqr. injection Heqp; intros; subst; clear Heqp.
   eapply CR.Semantics.BigStep_Denotational_Sound; eauto.
   (*Block - assert Error*) inversion H6. simpl in H4,H8. eapply negb_true_iff in H. 
   rewrite bnegb_equiv in H. eapply E_AssertNormal in H. subst. 
   inversion H4; subst.  (*<| s1 | s2 | >*) eapply E_ACBlockNormal; simpl; eauto.
   eapply Imp.Semantics.Denotational_BigStep_Adequate. eapply whileI_false_L.
   eapply bexp_denoterev. rewrite <- bnegb_equiv in H3. apply negb_true_iff in H3.
   rewrite <- H3. apply Denotational_B_BigStep_Sound. clear H3.
   inversion H8; subst. eapply Imp.Semantics.Denotational_BigStep_Adequate.
   eapply whileI_false_L. eapply bexp_denoterev.  rewrite <- bnegb_equiv in H3.
   apply negb_true_iff in H3. rewrite <- H3. apply Denotational_B_BigStep_Sound.
Qed.

Lemma whileR_lockstep3: forall b1 b2 s1 s2, 
     <{ <| while b1 do s1 end | while b2 do s2 end |>  }> ==R 
     <{whileR <|b1 | b2|> do <|s1 | s2|> end;; ifR <|b1 | BNot b2|> then <| while b1 do s1 end | skip|> else ifR <|BNot b1 | b2|> then <|skip | while b2 do s2 end|>
     else <|skip | skip|> end end}> .
Proof.
   intros b1 b2 s1 s2 ((st1, st2), (st1', st2')); split; intros. inversion H; subst.
   inversion H0; subst. destruct H1 as [H11 H12]. destruct H12 as [H121 H122].
   destruct H122 as [? ?]. subst. 
   (*bring it to form suitable for induction*)
   eapply Imp.Semantics.Denotational_BigStep_Adequate in H11. 
   eapply Imp.Semantics.Denotational_BigStep_Adequate in H121.
   eapply CR.Semantics.BigStep_Denotational_Sound. clear H. clear H0.
   remember <{ while b1 do s1 end}>. remember (RNormal x).
   generalize dependent st2. generalize dependent s2. generalize dependent b2.
   induction H11; try discriminate. inversion Heqc; subst. inversion Heqr; subst.
   clear Heqc; clear Heqr; intros. 
   econstructor. (*while - b1 false*) eapply E_ACWhileFalseL. assumption.
   eapply E_ACIfFalseL. simpl. assumption. inversion H121; subst.
   (*b2 is false*) apply E_ACIfFalseR. simpl; assumption.
   constructor; constructor; constructor.
   (*b1 - true, b2 - true*) eapply negb_true_iff in H. rewrite bnegb_equiv in H.
   apply E_ACIfTrue; simpl; try assumption. 
   constructor; try constructor; try assumption.
   (*complicated case*) clear IHcevalr1. injection Heqc; intros; subst; clear Heqc. 
   intros. inversion H121; subst; intros.
   econstructor. (*b2 is false*) eapply E_ACWhileFalseR; simpl; eauto. (*if - both true*)
   eapply negb_true_iff in H3. rewrite bnegb_equiv in H3. eapply E_ACIfTrue; simpl; try assumption.
   constructor; simpl; try constructor. eapply E_WhileTrueNormal; eauto. 
   (*both true*)
   eapply CR.Semantics.Denotational_BigStep_Adequate.
   eapply ACSeq_eqv_cong. eapply whileR_unroll. reflexivity. eapply prod_seq_assoc.
   eapply CR.Semantics.BigStep_Denotational_Sound. econstructor. econstructor; eauto.
   econstructor; eauto. eapply IHcevalr2; eauto.
   (*Other side*)
   inversion H; subst. inversion H0; subst. inversion H1; subst. inversion H2; subst.
   clear H0. clear H1. clear H2. clear H. destruct H3 as [? ?]. destruct H0 as [? ?].
   destruct H1 as [? ?]. subst. eapply CR.Semantics.Denotational_BigStep_Adequate in H, H0.
   remember <{whileR <| b1 | b2 |> do <| s1 | s2 |> end}> as r eqn:Heqr. 
   remember (RNormal x, RNormal x0). generalize dependent x1. generalize dependent x2.
   induction H; try discriminate.
   (*while - while*) inversion Heqr; subst.
   clear IHaceval1. firstorder. eapply block_eqv_cong.
   eapply If_while_eq. eapply If_while_eq. eapply CR.Semantics.BigStep_Denotational_Sound.
   clear Heqr. specialize H4 with x2 x1. apply H4 in H3. 
   eapply CR.Semantics.Denotational_BigStep_Adequate in H3. 
   econstructor; eauto. econstructor; eauto.
   econstructor; eauto. inversion H1; subst. eassumption.
   inversion H3; subst. eauto. econstructor; eauto. 
   econstructor; eauto. inversion H1; subst. eauto. inversion H3; subst; eauto.
   (*while, Normal*) injection Heqr; subst; clear Heqr. injection Heqp; subst; clear Heqp.
   intros. subst.  eapply CR.Semantics.BigStep_Denotational_Sound. 
   inversion H5; subst. simpl in H7,H8. Search negb. apply negb_true_iff in H8.
   (*apply E_ACIfFalseL with b1 b2 <{ <| while b1 do s1 end | skip |> }> <{ ifR <| ~ b1 | b2 |> then <| skip | while b2 do s2 end |>
          else <| skip | skip |> end }> (x,x0) (RNormal x1, RNormal x2) in H.*)
   (*<{ <| while b1 do s1 end | skip |> }> <{ ifR <| ~ b1 | b2 |> then <| skip | while b2 do s2 end |>
          else <| skip | skip |> end }>*)
    inversion H9; subst. simpl in H4,H10. inversion H10; subst. constructor; simpl. assumption. 
    eapply E_WhileFalse. assumption. simpl in H7. inversion H8; subst. simpl in H9,H10.
    apply negb_true_iff in H9. inversion H11; subst. simpl in H4,H12. inversion H4; subst.
    constructor; simpl. eapply E_WhileFalse; assumption. assumption. simpl in H9.
    rewrite H7 in H9. simpl in H9. discriminate H9. simpl in H9.
    (*invert H10 to get equality*) inversion H10; subst. simpl in H4,H11.
    inversion H4; subst; inversion H11; subst. constructor; eapply E_WhileFalse; assumption.
    inversion H8; subst. simpl in H9,H10. inversion H11; subst. simpl in H4,H12.
    inversion H4; subst. constructor; simpl. apply E_WhileFalse; assumption.
    assumption. simpl in H9. rewrite H in H9. simpl in H9. discriminate H9.
    simpl in H7,H9. rewrite H9 in H7. simpl in H7; discriminate H7.
    (*Last*)
    injection Heqr; subst; clear Heqr. injection Heqp; subst; clear Heqp.
    intros; subst. eapply CR.Semantics.BigStep_Denotational_Sound. 
    inversion H5; subst. simpl in H7,H8. apply negb_true_iff in H8.
    inversion H9; subst. simpl in H4,H10. inversion H10; subst. constructor; simpl. assumption. 
    eapply E_WhileFalse. assumption. simpl in H7. inversion H8; subst. simpl in H9,H10.
    apply negb_true_iff in H9. inversion H11; subst. simpl in H4,H12. inversion H4; subst.
    constructor; simpl. eapply E_WhileFalse; assumption. assumption. simpl in H9.
    rewrite H7 in H9. simpl in H9. discriminate H9. simpl in H9.
    (*invert H10 to get equality*) inversion H10; subst. simpl in H4,H11.
    inversion H4; subst; inversion H11; subst. constructor; eapply E_WhileFalse; assumption.
    inversion H8; subst. simpl in H9,H10. inversion H11; subst. simpl in H4,H12.
    inversion H4; subst. constructor; simpl. apply negb_true_iff in H9.
    apply E_WhileFalse; assumption. assumption.
    simpl in H9. apply negb_false_iff in H9. simpl in H7. rewrite H in H7. 
    simpl in H7. discriminate H7. 
    simpl in H7,H9. rewrite H9 in H7. simpl in H7; discriminate H7.
Qed.


End Equiv.

Module notations.

  Notation "r1 '==R' r2 " := (align_eqv r1 r2) (at level 40).

End notations.
