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

  (* A pair of product programs is embedded into a aligned
     representation largely as expected. - Pair of programs into product program? *)

  Definition embed_com (s1 s2 : @com I) : @algn_com I :=
    <{<| s1 | s2 |> }>.

  Definition algn_eqv_pair (s1 s2 : @com I) (r : @algn_com I) : Prop :=
    forall st1 st2 st1' st2',
      (st1 =[ s1 ]=> st1' /\ st2 =[ s2 ]=> st2') <->
        (st1, st2) =<[ r ]>=> (st1', st2').

  Theorem embed_is_iso :
    forall s1 s2, algn_eqv_pair s1 s2 (embed_com s1 s2).
  Proof.
    split; simpl; intros.
    - econstructor; tauto.
    - inversion H; subst ; tauto.
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
  end.

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

  Lemma inj_id_com_l_ceval :
    forall s (rst rst' : @state (@prod_M M)),
      rst =[ (inj_id_com_l s) ]=> rst' ->
      fst rst =[ s ]=> fst rst' /\ snd rst = snd rst'.
  Proof.
    intros.
    remember (inj_id_com_l s) as s' eqn: Heqs; revert s Heqs.
    induction H; simpl; intros; destruct s; simpl in *;
      try discriminate; try injection Heqs; intros; subst;
      try destruct st as [st1 st2];
      try destruct st' as [st1' st2'];
      try destruct st'' as [st1'' st2''];
      simpl in *;
      try specialize (IHceval _ eq_refl);
      try rewrite <- !inj_id_bexp_l_beval in *;
      intuition eauto; subst.
    - econstructor.
    - constructor; auto using inj_id_aexp_l_aeval.
    - specialize (IHceval1 _ eq_refl);
        specialize (IHceval2 _ eq_refl);
        intuition eauto;
        first [econstructor; eauto | congruence].
    - specialize (IHceval1 _ eq_refl);
        specialize (IHceval2 _ eq_refl);
        intuition eauto; congruence.
    - econstructor; eauto.
    - eapply E_IfFalse; eauto.
    - eapply E_WhileFalse; eauto.
    - specialize (IHceval1 _ eq_refl);
        intuition eauto; subst.
      eapply E_WhileTrue; eauto.
      eapply IHceval2; reflexivity.
    - specialize (IHceval1 _ eq_refl);
        intuition eauto; subst.
      eapply IHceval2 with (s := CWhile _ _); reflexivity.
  Qed.

  Lemma inj_id_com_r_ceval :
    forall s (rst rst' : @state (@prod_M M)),
      rst =[ (inj_id_com_r s) ]=> rst' ->
      snd rst =[ s ]=> snd rst' /\ fst rst = fst rst'.
  Proof.
    intros.
    remember (inj_id_com_r s) as s' eqn: Heqs; revert s Heqs.
    induction H; simpl; intros; destruct s; simpl in *;
      try discriminate; try injection Heqs; intros; subst;
      try destruct st as [st1 st2];
      try destruct st' as [st1' st2'];
      try destruct st'' as [st1'' st2''];
      simpl in *;
      try specialize (IHceval _ eq_refl);
      try rewrite <- !inj_id_bexp_r_beval in *;
      intuition eauto; subst.
    - econstructor.
    - constructor; auto using inj_id_aexp_r_aeval.
    - specialize (IHceval1 _ eq_refl);
        specialize (IHceval2 _ eq_refl);
        intuition eauto;
        first [econstructor; eauto | congruence].
    - specialize (IHceval1 _ eq_refl);
        specialize (IHceval2 _ eq_refl);
        intuition eauto; congruence.
    - econstructor; eauto.
    - eapply E_IfFalse; eauto.
    - eapply E_WhileFalse; eauto.
    - specialize (IHceval1 _ eq_refl);
        intuition eauto; subst.
      eapply E_WhileTrue; eauto.
      eapply IHceval2; reflexivity.
    - specialize (IHceval1 _ eq_refl);
        intuition eauto; subst.
      eapply IHceval2 with (s := CWhile _ _); reflexivity.
  Qed.

  Lemma inj_id_com_l_ceval' :
    forall s (st1 st1' : @state M),
      st1 =[ s ]=> st1' ->
      forall (st2 : @state M),
        (st1, st2) =[ (inj_id_com_l s) ]=> (st1', st2).
  Proof.
    intros.
    induction H; simpl; intros; try solve [econstructor; eauto];
      try rewrite <- inj_id_aexp_l_aeval;
      try rewrite <- inj_id_bexp_l_beval.
    - specialize (E_Ass (st, st2) (inj_id_aexp_l a) n (inl x));
        simpl; intro H0; apply H0.
      rewrite <- inj_id_aexp_l_aeval; assumption.
    -
    econstructor;
        try rewrite <- inj_id_bexp_l_beval; eauto.
    - eapply E_IfFalse;
        try rewrite <- inj_id_bexp_l_beval; eauto.
    - eapply E_WhileFalse;
        try rewrite <- inj_id_bexp_l_beval; eauto.
    - eapply E_WhileTrue;
        try rewrite <- inj_id_bexp_l_beval; eauto.
  Qed.

  Lemma inj_id_com_r_ceval' :
    forall s (st2 st2' : @state M),
      st2 =[ s ]=> st2' ->
      forall (st1 : @state M),
        (st1, st2) =[ (inj_id_com_r s) ]=> (st1, st2').
  Proof.
    intros.
    induction H; simpl; intros; try solve [econstructor; eauto];
      try rewrite <- inj_id_aexp_r_aeval;
      try rewrite <- inj_id_bexp_r_beval.
    - specialize (E_Ass (st1, st) (inj_id_aexp_r a) n (inr x));
        simpl; intro H0; apply H0.
      rewrite <- inj_id_aexp_r_aeval; assumption.
    - econstructor;
        try rewrite <- inj_id_bexp_r_beval; eauto.
    - eapply E_IfFalse;
        try rewrite <- inj_id_bexp_r_beval; eauto.
    - eapply E_WhileFalse;
        try rewrite <- inj_id_bexp_r_beval; eauto.
    - eapply E_WhileTrue;
        try rewrite <- inj_id_bexp_r_beval; eauto.
  Qed.

  (* We build a product program by reifying an aligned program into
     the standard IMP syntax. - ? *)

  Fixpoint reify_com (r : @algn_com I) : (@com prod_I) :=
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

Compute reify_com <{ <| CSkip | CSkip |> }>.

  (* We define a different notion of equivalence between aligned
     programs and a single program with variables drawn from two
.     distinct domains: *)

  Definition lift_state (st1 st2 : @state M) : (@state (@prod_M M)) := (st1, st2).


  Definition algn_eqv_single (r : @algn_com I) (s : @com prod_I) : Prop :=
    forall rst rst',
      (rst =[ s ]=> rst') <->
        rst =<[ r ]>=> rst'.

  Theorem reify_is_iso :
    forall r, algn_eqv_single r (reify_com r).
  Proof.
    split; simpl; intros.
    - remember (reify_com r) as rc eqn:Hrc;
        revert r Hrc; induction H; subst;
        simpl; intros;
        try destruct st as [st1 st2];
        try destruct st' as [st1' st2'];
        try destruct st'' as [st1'' st2''];
        destruct r; simpl in Hrc;
        first [discriminate
                 | injection Hrc; intros; subst; clear Hrc].
      + econstructor; simpl in *;
        eapply inj_id_com_l_ceval in H;
          eapply inj_id_com_r_ceval in H0;
          simpl in *; intuition eauto; subst; eauto.
      + specialize (IHceval1 _ eq_refl);
          specialize (IHceval2 _ eq_refl);
          econstructor; eauto.
      + specialize (IHceval _ eq_refl).
        simpl in H; apply andb_prop in H;
          rewrite <- inj_id_bexp_l_beval in H;
          rewrite <- inj_id_bexp_r_beval in H;
          econstructor; simpl in *; intuition eauto.
      + simpl in H; apply andb_false_iff in H;
          rewrite <- inj_id_bexp_l_beval in H;
          rewrite <- inj_id_bexp_r_beval in H;
          specialize (IHceval _ eq_refl);
          intuition.
        * apply E_ACIfFalseL; eauto.
        * apply E_ACIfFalseR; eauto.
      + simpl in H; apply andb_false_iff in H;
          rewrite <- inj_id_bexp_l_beval in H;
          rewrite <- inj_id_bexp_r_beval in H;
          intuition.
        * apply E_ACWhileFalseL; eauto.
        * apply E_ACWhileFalseR; eauto.
      + specialize (IHceval1 _ eq_refl);
          simpl in H; apply andb_prop in H;
          rewrite <- inj_id_bexp_l_beval in H;
          rewrite <- inj_id_bexp_r_beval in H;
          econstructor; intuition eauto.
    - induction H; try destruct rst as [st1 st2];
        try destruct rst' as [st'1 st'2];
        try destruct rst'' as [st''1 st''2];
        simpl in *.
      + econstructor; eauto using inj_id_com_l_ceval', inj_id_com_r_ceval'.
      + econstructor; eauto using inj_id_com_l_ceval', inj_id_com_r_ceval'.
      + econstructor; eauto using inj_id_com_l_ceval', inj_id_com_r_ceval'.
        simpl; rewrite <- inj_id_bexp_l_beval, <- inj_id_bexp_r_beval, H, H0; auto.
      + apply E_IfFalse; simpl; eauto.
        simpl; rewrite <- inj_id_bexp_l_beval, <- inj_id_bexp_r_beval, ?H, ?H0; auto.
      + apply E_IfFalse; simpl; eauto.
        simpl; rewrite <- inj_id_bexp_l_beval, <- inj_id_bexp_r_beval, ?H, ?H0; auto using andb_false_r.
      + eapply E_WhileTrue; try eauto.
        simpl; rewrite <- inj_id_bexp_l_beval, <- inj_id_bexp_r_beval, ?H, ?H0; auto.
      + apply E_WhileFalse; simpl; eauto.
        simpl; rewrite <- inj_id_bexp_l_beval, <- inj_id_bexp_r_beval, ?H, ?H0; auto using andb_false_r.
      + apply E_WhileFalse; simpl; eauto.
        simpl; rewrite <- inj_id_bexp_l_beval, <- inj_id_bexp_r_beval, ?H, ?H0; auto using andb_false_r.
  Qed.

  Definition eqv_single_prod (s1 s2 : @com I) (s12 : @com prod_I) : Prop :=
    forall st1 st2 st1' st2',
      (st1 =[ s1 ]=> st1' /\ st2 =[ s2 ]=> st2') <->
        (st1, st2) =[ s12 ]=> (st1', st2').


  Lemma eqv_single_prod_respect_eqv
    : forall (s1 s2 s1' s2' : @com I)
             (s12 s12' : @com prod_I),
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

  (* Key theorem: equivalent aligned programs produce equivalent
     product program. *)
  Theorem reify_preserves_eqv :
    forall r1 r2,
      align_eqv r1 r2 ->
      com_eqv (reify_com r1) (reify_com r2).
  Proof.
    unfold align_eqv, com_eqv.
    intros r1 r2 H (st1, st2); split; intro.
    - eapply Imp.Semantics.BigStep_Denotational_Sound.
      apply reify_is_iso.
      eapply CR.Semantics.Denotational_BigStep_Adequate.
      apply H.
      eapply Imp.Semantics.Denotational_BigStep_Adequate in H0.
      apply reify_is_iso in H0.
      eapply CR.Semantics.BigStep_Denotational_Sound in H0.
      assumption.
    - eapply Imp.Semantics.BigStep_Denotational_Sound.
      apply reify_is_iso.
      eapply CR.Semantics.Denotational_BigStep_Adequate.
      apply H.
      eapply Imp.Semantics.Denotational_BigStep_Adequate in H0.
      apply reify_is_iso in H0.
      eapply CR.Semantics.BigStep_Denotational_Sound in H0.
      assumption.
  Qed.

  Lemma embed_reify_sound :
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
      apply reify_is_iso. assumption.
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
               (st1, st2) =[reify_com r]=> (st1', st2') ->
                                           Q st1' st2'),
    forall (st1 st2 st1' st2' : @state M),
      P st1 st2 ->
      st1 =[s1]=> st1' ->
      st2 =[s2]=> st2' ->
      Q st1' st2'.
  Proof.
    intros.
    eapply r_safe; try eassumption.
    eapply Imp.Semantics.Denotational_BigStep_Adequate.
    eapply reify_preserves_eqv.
    - symmetry; eassumption.
    - eapply Imp.Semantics.BigStep_Denotational_Sound.
      eapply reify_is_iso.
      unfold embed_com.
      econstructor; simpl; eassumption.
  Qed.

End Embed.

From CR Require Import Hoare.

Section rel_verification.
    Definition I := @prod_I string.
    Context {M : Type -> Type}.
    Context {id : Id string M}.

  Definition hoare_triple_product
             (P : Assertion) (r : @com I ) (Q : Assertion) : Prop := hoare_triple P r Q.
    (*forall st1 st2 st1' st2',
      P st1 st2 ->
      (st1, st2) =[ r ]=> (st1', st2') ->
      Q st1' st2'. *)

  Definition hoare_triple_relational
             (P : @Assertion M) (s1 s2 : @com string) (Q : @Assertion M) : Prop :=
    forall st1 st2 st1' st2',
      P (st1 ,st2)  ->
      ceval s1 st1 st1' ->
      ceval s2 st2 st2' ->
      Q (st1', st2').

  Lemma hoare_triple_prod_a :
    forall (s1 s2 : @com string)(P Q : Assertion)
           (r : @algn_com string),
      align_eqv r (embed_com s1 s2) /\ (hoare_triple_product P (reify_com r) Q) ->
      hoare_triple_relational P s1 s2 Q.
  Proof.
    unfold hoare_triple_product, hoare_triple_relational, align_eqv. intros.
    destruct H as [eqv_r P_r].
    eapply P_r.
    eassumption.
    apply embed_reify_sound with (s1 := s1) (s2 := s2). unfold align_eqv. eauto.
    split. assumption. assumption.
  Qed.

  Lemma hoare_triple_prod_b :
    forall (s1 s2 : @com string)(P Q : Assertion),
      hoare_triple_relational P s1 s2 Q ->
      exists r : @algn_com string, align_eqv r (embed_com s1 s2) /\
                                (hoare_triple_product P (reify_com r) Q).
  Proof.
    unfold hoare_triple_product, hoare_triple, hoare_triple_relational.
    intros; eexists; split; try reflexivity; intros.
    eapply reify_is_iso in H1.
    unfold embed_com in H1; inversion H1; subst. destruct st.
    eapply H; eassumption.
  Qed.

End rel_verification.
