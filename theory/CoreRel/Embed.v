From Common Require Import Id Fixpoints.
From Imp Require Import Syntax Semantics Equiv.
From CR Require Import Syntax Semantics Equiv.
From Coq Require Import Strings.String.

(* We now show how to convert from a pair of Imp programs to a CoreRel
   program and back. *)

Section Embed.

  Import Imp.Syntax.notations.
  Import Imp.Semantics.notations.
  Import CR.Syntax.notations.
  Import CR.Semantics.notations.

  (* The type of variable identifiers. *)
  Context {I : Type}.
  Context {M : Type -> Type}.
  Context {id : Id I M}.


  (*Definition result := @result M. *)

  (* A pair of product programs is embedded into a aligned
     representation largely as expected. - Pair of programs into product program? *)

  Definition embed_com (s1 s2 : @com I) : @algn_com I :=
    <{<| s1 | s2 |> }>.

  Definition algn_eqv_pair (s1 s2 : @com I) (r : @algn_com I) : Prop :=
    forall st1 st2 st1' st2',
      ((st1 =[ s1 ]=> RNormal st1' /\ st2 =[ s2 ]=> RNormal st2') <->
        (st1, st2) =<[ r ]>=> (RNormal st1', RNormal st2')).

  Theorem embed_is_iso :
    forall s1 s2, algn_eqv_pair s1 s2 (embed_com s1 s2).
  Proof. intros. unfold algn_eqv_pair. intros. split.
   intros. destruct H as [? ?]. unfold embed_com. constructor. 
   simpl. assumption. simpl. assumption.
   intros. unfold embed_com in H. inversion H; subst. 
   simpl in H4,H6. split. assumption. assumption. 
  Qed.

  (* Variable renaming functions. There are, of course, more elegant
     ways to do this, but no need to overengineer these intermediate
     functions. *)
  Fixpoint inj_id_aexp_l (a : @aexp I ) : @aexp (I + I) :=
    match a with
    | ANum n => <{ n }>
    | AId x => <{ AId (inl x) }>
    | <{a1 + a2}> => <{ (inj_id_aexp_l a1) + (inj_id_aexp_l a2) }>
    | <{a1 - a2}> => <{ (inj_id_aexp_l a1) - (inj_id_aexp_l a2) }>
    | <{a1 * a2}> => <{ (inj_id_aexp_l a1) * (inj_id_aexp_l a2) }>
    end.

  Fixpoint inj_id_aexp_r (a : @aexp I ) : @aexp (I + I) :=
    match a with
    | ANum n => <{ n }>
    | AId x => <{ AId (inr x) }>
    | <{a1 + a2}> => <{ (inj_id_aexp_r a1) + (inj_id_aexp_r a2) }>
    | <{a1 - a2}> => <{ (inj_id_aexp_r a1) - (inj_id_aexp_r a2) }>
    | <{a1 * a2}> => <{ (inj_id_aexp_r a1) * (inj_id_aexp_r a2) }>
    end.

  Fixpoint inj_id_bexp_l (b : @bexp I ) : @bexp (I + I) :=
    match b with
    | <{true}>      => <{true}>
    | <{false}>     => <{false}>
    | <{a1 = a2}>   => <{inj_id_aexp_l a1 = inj_id_aexp_l a2}>
    | <{a1 <= a2}>  => <{inj_id_aexp_l a1 <= inj_id_aexp_l a2}>
    | <{~ b1}>      => <{~ (inj_id_bexp_l b1) }>
    | <{b1 && b2}>  => <{(inj_id_bexp_l b1) && (inj_id_bexp_l b2)}>
    end.

  Fixpoint inj_id_bexp_r (b : @bexp I ) : @bexp (I + I) :=
    match b with
    | <{true}>      => <{true}>
    | <{false}>     => <{false}>
    | <{a1 = a2}>   => <{inj_id_aexp_r a1 = inj_id_aexp_r a2}>
    | <{a1 <= a2}>  => <{inj_id_aexp_r a1 <= inj_id_aexp_r a2}>
    | <{~ b1}>      => <{~ (inj_id_bexp_r b1) }>
    | <{b1 && b2}>  => <{(inj_id_bexp_r b1) && (inj_id_bexp_r b2)}>
    end.

  Fixpoint inj_id_com_l (c : @com I) : @com (I + I) :=
  match c with
  | <{ skip }> => <{ skip }>

  | <{x := a1}> => <{CAss (inl x) (inj_id_aexp_l a1) }>

  | <{c1; c2}> => <{inj_id_com_l c1; inj_id_com_l c2}>

  | <{ if b then c1 else c2 end }> =>
      <{ if inj_id_bexp_l b then inj_id_com_l c1 else inj_id_com_l c2 end }>

  | <{ while b do c end }> =>
      <{ while inj_id_bexp_l b do inj_id_com_l c end }>

  | <{ assert b }> => <{ assert inj_id_bexp_l b }>
  end.

  Fixpoint inj_id_com_r (c : @com I) : @com (I + I) :=
  match c with
  | <{ skip }> => <{ skip }>

  | <{x := a1}> => <{CAss (inr x) (inj_id_aexp_r a1) }>

  | <{c1; c2}> => <{inj_id_com_r c1; inj_id_com_r c2}>

  | <{ if b then c1 else c2 end }> =>
      <{ if inj_id_bexp_r b then inj_id_com_r c1 else inj_id_com_r c2 end }>

  | <{ while b do c end }> =>
      <{ while inj_id_bexp_r b do inj_id_com_r c end }>

  | <{ assert b }> => <{ assert inj_id_bexp_r b }>
  end.

Print Imp.Semantics.state.


  (* All these lifting functions are semantics preserving, as
     expected: *)
  Lemma inj_id_aexp_l_aeval :
    forall st1 st2 a,
      aeval st1 a = aeval (M := (@prod_M M)) (st1, st2) (inj_id_aexp_l a).
  Proof.
    induction a; simpl; eauto.
  Qed.

  Lemma inj_id_aexp_r_aeval :
    forall st1 st2 a,
      aeval st2 a = aeval (M := (@prod_M M)) (st1, st2) (inj_id_aexp_r a).
  Proof.
    induction a; simpl; eauto.
  Qed.

  Lemma inj_id_bexp_l_beval :
    forall st1 st2 b,
      beval st1 b = beval (M := (@prod_M M)) (st1, st2) (inj_id_bexp_l b).
  Proof.
    induction b; simpl; eauto;
      try erewrite !inj_id_aexp_l_aeval;
      rewrite ?IHb;
      rewrite ?IHb1;
      rewrite ?IHb2; reflexivity.
  Qed.

  Lemma inj_id_bexp_r_beval :
    forall st1 st2 b,
      beval st2 b = beval (M := (@prod_M M)) (st1, st2) (inj_id_bexp_r b).
  Proof.
    induction b; simpl; eauto;
      try erewrite !inj_id_aexp_r_aeval;
      rewrite ?IHb;
      rewrite ?IHb1;
      rewrite ?IHb2; reflexivity.
  Qed.


 (*From here*)
 Lemma inj_id_com_l_ceval :
    forall s (rst rst' : @state (@prod_M M)),
      rst =[ (inj_id_com_l s) ]=> RNormal rst' ->
      fst rst =[ s ]=> RNormal (fst rst') /\ snd rst = snd rst'.
  Proof.
    intros. remember (inj_id_com_l s). remember (RNormal rst'). 
    generalize dependent rst'. generalize dependent s.
    induction H; simpl; intros; destruct s; simpl in *;
    try discriminate; try injection Heqc; intros; 
    try destruct st as [st1 st2] ; try destruct st' as [st1' st2'] ; subst.
    inversion Heqr; subst. split. constructor. reflexivity.
    inversion Heqr; subst. simpl. split. constructor. 
    rewrite <- inj_id_aexp_l_aeval. reflexivity. reflexivity.
    (*s1; s2*) simpl. specialize (IHcevalr1 _ eq_refl); 
    specialize (IHcevalr2 _ eq_refl). simpl in IHcevalr1, IHcevalr2.
    specialize IHcevalr1 with (st1', st2'). specialize IHcevalr2 with rst'.
    firstorder. simpl in H3,H4. eapply E_SeqNormal. eassumption.
    assumption. simpl in H4. rewrite H4. assumption.
    (*if beval true*) simpl. split. eapply E_IfTrue. 
    rewrite <- inj_id_bexp_l_beval in H. assumption. 
    specialize IHcevalr with s1 rst'. firstorder.
    specialize IHcevalr with s1 rst'. firstorder.
    (*if beval false*) simpl. split. eapply E_IfFalse. 
    rewrite <- inj_id_bexp_l_beval in H. assumption. 
    specialize IHcevalr with s2 rst'. firstorder.
    specialize IHcevalr with s2 rst'. firstorder.
    (*while - false*) inversion Heqr; subst. clear Heqr. simpl. split. 
    eapply E_WhileFalse. rewrite <- inj_id_bexp_l_beval in H. assumption.
    reflexivity. simpl.
    (*while - true*) 
    specialize IHcevalr1 with s (st1', st2'). firstorder.
    simpl in H2, H3. eapply E_WhileTrueNormal. rewrite <- inj_id_bexp_l_beval in H.
    assumption. eassumption. simpl in IHcevalr2. eapply IHcevalr2. eauto.
    reflexivity. simpl in H2,H3.  simpl in IHcevalr2. rewrite H3.
    eapply IHcevalr2 with (s := CWhile _ _). eauto. reflexivity.
    (*assert*) simpl. inversion Heqr; subst. clear Heqr. simpl.
    split. constructor. rewrite <- inj_id_bexp_l_beval in H. 
    assumption. reflexivity.
  Qed.

  Lemma inj_id_com_r_ceval :
    forall s (rst rst' : @state (@prod_M M)),
      rst =[ (inj_id_com_r s) ]=> RNormal rst' ->
      snd rst =[ s ]=> RNormal (snd rst') /\ fst rst = fst rst'.
  Proof.
    intros. remember (inj_id_com_r s). remember (RNormal rst'). 
    generalize dependent rst'. generalize dependent s.
    induction H; simpl; intros; destruct s; simpl in *;
    try discriminate; try injection Heqc; intros; 
    try destruct st as [st1 st2] ; try destruct st' as [st1' st2'] ; subst.
    inversion Heqr; subst. split. constructor. reflexivity.
    inversion Heqr; subst. simpl. split. constructor. 
    rewrite <- inj_id_aexp_r_aeval. reflexivity. reflexivity.
    (*s1; s2*) simpl. specialize (IHcevalr1 _ eq_refl); 
    specialize (IHcevalr2 _ eq_refl). simpl in IHcevalr1, IHcevalr2.
    specialize IHcevalr1 with (st1', st2'). specialize IHcevalr2 with rst'.
    firstorder. simpl in H3,H4. eapply E_SeqNormal. eassumption.
    assumption. simpl in H4. rewrite H4. assumption.
    (*if beval true*) simpl. split. eapply E_IfTrue. 
    rewrite <- inj_id_bexp_r_beval in H. assumption. 
    specialize IHcevalr with s1 rst'. firstorder.
    specialize IHcevalr with s1 rst'. firstorder.
    (*if beval false*) simpl. split. eapply E_IfFalse. 
    rewrite <- inj_id_bexp_r_beval in H. assumption. 
    specialize IHcevalr with s2 rst'. firstorder.
    specialize IHcevalr with s2 rst'. firstorder.
    (*while - false*) inversion Heqr; subst. clear Heqr. simpl. split. 
    eapply E_WhileFalse. rewrite <- inj_id_bexp_r_beval in H. assumption.
    reflexivity. simpl.
    (*while - true*) 
    specialize IHcevalr1 with s (st1', st2'). firstorder.
    simpl in H2, H3. eapply E_WhileTrueNormal. rewrite <- inj_id_bexp_r_beval in H.
    assumption. eassumption. simpl in IHcevalr2. eapply IHcevalr2. eauto.
    reflexivity. simpl in H2,H3.  simpl in IHcevalr2. rewrite H3.
    eapply IHcevalr2 with (s := CWhile _ _). eauto. reflexivity.
    (*assert*) simpl. inversion Heqr; subst. clear Heqr. simpl.
    split. constructor. rewrite <- inj_id_bexp_r_beval in H. 
    assumption. reflexivity.
  Qed. 

  Lemma inj_id_com_l_ceval' :
    forall s (st1 st1' : @state M),
      st1 =[ s ]=> RNormal st1' ->
      forall (st2 : @state M),
        (st1, st2) =[ (inj_id_com_l s) ]=> RNormal (st1', st2).
  Proof.
    intros. remember (RNormal st1'). generalize dependent st2.
    generalize dependent st1'.
    induction H; simpl; intros; 
    try solve [econstructor; eauto];
    try rewrite <- inj_id_aexp_l_aeval;
    try rewrite <- inj_id_bexp_l_beval.
   (*Skip*) inversion Heqr; subst; clear Heqr; constructor.
   (*Assignment*) inversion Heqr; subst; clear Heqr. 
    specialize (E_Ass (st, st2) (inj_id_aexp_l a) (aeval st a) (inl x)).
    simpl; intro H0; apply H0. rewrite <- inj_id_aexp_l_aeval. reflexivity.
    (*sequence*) discriminate.
    (*if - true*) econstructor; try rewrite <- inj_id_bexp_l_beval; eauto.
    (*if - false*) eapply E_IfFalse; try rewrite <- inj_id_bexp_l_beval; eauto.
    (*while - false*) inversion Heqr; subst. clear Heqr.
    eapply E_WhileFalse; try rewrite <- inj_id_bexp_l_beval; eauto.
    (*while - true*) eapply E_WhileTrueNormal; try rewrite <- inj_id_bexp_l_beval; eauto.
    (*while - error*) discriminate.
    (*assert - normal*) inversion Heqr; subst. constructor.
    rewrite <- inj_id_bexp_l_beval. assumption.
    (*assert - Error*) discriminate. 
  Qed.

  Lemma inj_id_com_r_ceval' :
    forall s (st2 st2' : @state M),
      st2 =[ s ]=> RNormal st2' ->
      forall (st1 : @state M),
        (st1, st2) =[ (inj_id_com_r s) ]=> RNormal (st1, st2').
  Proof.
    intros. remember (RNormal st2'). generalize dependent st1.
    generalize dependent st2'.
    induction H; simpl; intros; 
    try solve [econstructor; eauto];
    try rewrite <- inj_id_aexp_r_aeval;
    try rewrite <- inj_id_bexp_r_beval.
   (*Skip*) inversion Heqr; subst; clear Heqr; constructor.
   (*Assignment*) inversion Heqr; subst; clear Heqr. 
    specialize (E_Ass (st1, st) (inj_id_aexp_r a) (aeval st a) (inr x)).
    simpl; intro H0; apply H0. rewrite <- inj_id_aexp_r_aeval. reflexivity.
    (*sequence*) discriminate.
    (*if - true*) econstructor; try rewrite <- inj_id_bexp_r_beval; eauto.
    (*if - false*) eapply E_IfFalse; try rewrite <- inj_id_bexp_r_beval; eauto.
    (*while - false*) inversion Heqr; subst. clear Heqr.
    eapply E_WhileFalse; try rewrite <- inj_id_bexp_r_beval; eauto.
    (*while - true*) eapply E_WhileTrueNormal; try rewrite <- inj_id_bexp_r_beval; eauto.
    (*while - error*) discriminate.
    (*assert - normal*) inversion Heqr; subst. constructor.
    rewrite <- inj_id_bexp_r_beval. assumption.
    (*assert - Error*) discriminate. 
  Qed.

  Fixpoint reify_com (r : @algn_com I) : (@com (I + I)) :=
    match r with
    | <{ <| s1 | s2 |> }> =>
        <{ inj_id_com_l s1; inj_id_com_r s2}>

    | <{ r1;; r2 }> =>
        <{ reify_com r1; reify_com r2}>

    | <{ ifR <| b1 | b2 |> then r1 else r2 end }> =>
        <{ if (inj_id_bexp_l b1 && inj_id_bexp_r b2) then reify_com r1 else reify_com r2 end}>

    | <{ whileR <| b1 | b2 |> do r end }> =>
        <{ while (inj_id_bexp_l b1 && inj_id_bexp_r b2) do reify_com r end}>
    end.


  (* We define a different notion of equivalence between aligned
     programs and a single program with variables drawn from two
     distinct domains: *)

  Definition lift_state (st1 st2 : @state M) : (@state (@prod_M M)) := (st1, st2). 



 Definition algn_eqv_single (r : @algn_com I) (s : @com (I + I)) : Prop :=
    forall rst rst',
      (rst =[ s ]=> RNormal rst') <->
        rst =<[ r ]>=> (RNormal (fst rst'), RNormal (snd rst')).

  Theorem reify_is_iso :
    forall r, algn_eqv_single r (reify_com r).
  Proof.
    split; simpl; intros. remember (reify_com r) as rc eqn:Hrc;
    remember (RNormal rst') as rt eqn:Hrt; revert r Hrc Hrt; 
    induction H. (*∀ r : algn_com, <{ c1; c2 }> = reify_com r → st =<[ r ]>=> st''*) intros;
    intros. simpl in Hrc. destruct r. discriminate. discriminate. discriminate.
    discriminate.
    intros. destruct r. discriminate. discriminate. discriminate. discriminate.
    intros. destruct r0. simpl in Hrc. inversion Hrc; subst. 
    econstructor; simpl in *;  eapply inj_id_com_l_ceval in H;
    eapply inj_id_com_r_ceval in H0; simpl in *; intuition eauto; subst; eauto.
    rewrite H3 in H1. assumption. rewrite <- H2 in H. assumption.
    (*sequence: *) destruct r0_1, r0_2.
  
  Admitted.
    
   

  Definition eqv_single_prod (s1 s2 : @com I) (s12 : @com (I + I)) : Prop :=
    forall st1 st2 st1' st2',
      (st1 =[ s1 ]=> RNormal st1' /\ st2 =[ s2 ]=> RNormal st2') <->
        (st1, st2) =[ s12 ]=> RNormal (st1', st2').

  Lemma eqv_single_prod_respect_eqv
    : forall (s1 s2 s1' s2' : @com I)
             (s12 s12' : @com (I + I)),
      com_eqv s1 s1' -> com_eqv s2 s2' -> com_eqv s12 s12' ->
      eqv_single_prod s1 s2 s12 ->
      eqv_single_prod s1' s2' s12'.
  Proof.
    unfold com_eqv, eqv_single_prod; intros.
    split; intros.
    - eapply Imp.Semantics.Denotational_BigStep_Adequate.
      eapply H1.
      eapply Imp.Semantics.BigStep_Denotational_Sound.
      eapply H2; intuition.
      + eapply Imp.Semantics.Denotational_BigStep_Adequate.
        eapply H.
        eapply Imp.Semantics.BigStep_Denotational_Sound.
        eassumption.
      + eapply Imp.Semantics.Denotational_BigStep_Adequate.
        eapply H0.
        eapply Imp.Semantics.BigStep_Denotational_Sound.
        eassumption.
    - eapply Imp.Semantics.BigStep_Denotational_Sound in H3.
      eapply H1 in H3.
      eapply Imp.Semantics.Denotational_BigStep_Adequate in H3.
      eapply H2 in H3; intuition.
      + eapply Imp.Semantics.Denotational_BigStep_Adequate.
        eapply H.
        eapply Imp.Semantics.BigStep_Denotational_Sound.
        eassumption.
      + eapply Imp.Semantics.Denotational_BigStep_Adequate.
        eapply H0.
        eapply Imp.Semantics.BigStep_Denotational_Sound.
        eassumption.
  Qed.

  (* Key theorem: a product program constructed from any alignment
     that is semantically equivalent to the naive construction of a
     pair of programs s1 and s2 is also equivalent to s1 and s2. *)

  Theorem embed_reify_sound :
    forall s1 s2 r,
      align_eqv (embed_com s1 s2) r ->
      eqv_single_prod s1 s2 (reify_com r).
  Proof.
    unfold align_eqv, eqv_single_prod.
    intros s1 s2 r H st1 st2 st1' st2'.
    split; intros.
    - apply reify_is_iso.
      eapply CR.Semantics.Denotational_BigStep_Adequate.
      apply H.
      eapply CR.Semantics.BigStep_Denotational_Sound.
      apply embed_is_iso.
      intuition.
    - apply embed_is_iso.
      eapply CR.Semantics.Denotational_BigStep_Adequate.
      apply H.
      eapply CR.Semantics.BigStep_Denotational_Sound.
      apply reify_is_iso in H0. simpl in H0. assumption.
  Qed.

  (* As a consequence, we can reduce relational reasoning of 2-safety
     properties to reasoning about properties of a product program
     built from *some* alignment. *)

  Corollary product_program_sound :
    forall (s1 s2 : @com I)
           (P : (@state M) -> (@state M) -> Prop)
           (Q : (@state M) -> (@state M) -> Prop),
    forall (r : @algn_com I)
           (r_eqv : align_eqv (embed_com s1 s2) r)
           (r_safe : forall (st1 st2 st1' st2' : @state M),
               P st1 st2 ->
               (st1, st2) =[reify_com r]=> RNormal (st1', st2') ->
                                           Q st1' st2'),
    forall (st1 st2 st1' st2' : @state M),
      P st1 st2 ->
      st1 =[s1]=> RNormal st1' ->
      st2 =[s2]=> RNormal st2' ->
      Q st1' st2'.
  Proof.
    intros.
    eapply r_safe; try eassumption.
    eapply embed_reify_sound; eauto.
  Qed.

End Embed.
