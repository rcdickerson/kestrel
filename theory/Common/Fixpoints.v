From stdpp Require Import prelude.

Section Sets.
  (* Extensional: Explicitly spell out all the members of a set.
     I.e. The set of states in the US is "Alabama, Alaska, ...." *)
  (* Seen this style of definition before... *)
  Definition Set' (A : Type) := list A.

  (* Intensional: Characteristic 'Function' approach: every input to a
     boolean valued function which returns true is a member of the
     set, and is not an element otherwise. *)

  Definition Bool_Set (A : Type) := A -> bool.

  Fixpoint evenb (n:nat) : bool :=
    match n with
    | O => true
    | S O => false
    | S (S n') => evenb n'
    end.

  Definition evens : Bool_Set nat := evenb.
  Definition In_b {A} (a : A) (e : Bool_Set A) : Prop :=
    e a = true.

  Example even_4 : In_b 4 evens. Proof. unfold In_b. simpl. reflexivity. Qed.

  Definition Same_Set' {A} (e1 e2 : Bool_Set A) : Prop :=
    forall x, e1 x = e2 x.

  (* How to define Intersection, Union, Subset ? *)
  Definition Union' {A} (e1 e2 : Bool_Set A) : Bool_Set A :=
    fun x => orb (e1 x) (e2 x).

  Definition Intersection' {A} (e1 e2 : Bool_Set A)
    : Bool_Set A :=
    fun x => andb (e1 x) (e2 x).

  Definition Subset' {A} (e1 e2 : Bool_Set A) : Prop :=
    forall x, In_b e1 x -> In_b e2 x.
  (* This encoding of sets means membership is always decideable! *)
End Sets.

Section Fixpoints.

  (* Propositional analogues to Characteristic Function from above.  A
     set is a property (propositional-valued function), and an object
     is an element if there is some proof that it satisfies that property. *)
  Definition PSet (A : Type) := A -> Prop.
  Definition In {A} (a : A) (e : PSet A) : Prop := e a.
  Definition PSet_Union {A} (e1 e2 : PSet A) : PSet A := fun a : A => In a e1 \/ In a e2.
  Definition PSet_Intersection {A} (e1 e2 : PSet A) : PSet A := fun a : A => In a e1 /\ In a e2.

  #[global]
   Instance PSet_In_ElemOf {A} : ElemOf A (PSet A) := In.

  #[global]
   Instance PSet_Union_Union {A} : Union (PSet A) := PSet_Union.

  #[global]
   Instance PSet_Intersection_Intersection {A} : Intersection (PSet A) :=
    PSet_Intersection.

  Definition even x := exists n : nat, x = 2 * n.

  Example even_6 : 6 ∈ even. Proof. unfold In. exists 3. reflexivity. Qed.

  Definition Subset {A} (e1 e2 : PSet A) : Prop :=
    forall x, x ∈ e1 -> x ∈ e2.

  Lemma Subset_trans {A} : forall (s1 s2 s3 : PSet A),
      s1 ⊆ s2 -> s2 ⊆ s3 -> s1 ⊆ s3.
  Proof.
    set_solver.
  Qed.

  Lemma Subset_refl {A} : forall (s1 : PSet A), s1 ⊆ s1.
  Proof.
    set_solver.
  Qed.

  Lemma Same_set_refl {A} : forall (s1 : PSet A), s1 ≡ s1.
  Proof.
    set_solver.
  Qed.

  Lemma Same_set_sym {A} : forall (s1 s2 : PSet A), s1 ≡ s2 -> s2 ≡ s1.
  Proof.
    set_solver.
  Qed.

  Lemma Same_set_trans {A} : forall (s1 s2 s3 : PSet A),
      s1 ≡ s2 ->
      s2 ≡ s3 ->
      s1 ≡ s3.
  Proof.
    set_solver.
  Qed.

  Lemma Subset_impl {A} (P Q : PSet A) :
    (forall x, P x -> Q x) <-> P ⊆ Q.
  Proof.
    unfold subseteq, set_subseteq_instance; intuition.
  Qed.

  Lemma Equiv_iff {A} (P Q : PSet A) :
    (forall x, P x <-> Q x) <-> P ≡ Q.
  Proof.
    intuition.
  Qed.

  Context {U : Type}. (* The type of elements of our set. *)
  Variable F : PSet U -> PSet U. (* Our generating function-- takes a set of Us and builds a new set.*)

  (* A generator function is monotone if it preserves the subset
  relation on its argument. *)
  Definition Monotone (F : PSet U -> PSet U) : Prop :=
    forall (S S' : PSet U),
      S ⊆ S' -> F S ⊆ F S'.

  Variable Monotone_F : Monotone F.

  Definition FClosed (S : PSet U) : Prop := F S ⊆ S.

  Definition FConsistent (S : PSet U) : Prop := S ⊆ F S.

  Definition FixedPoint (S : PSet U) : Prop :=
    FClosed S /\ FConsistent S.

  Lemma FixedPoint_unfold FP : FixedPoint FP -> FP ≡ (F FP).
  Proof.
    split; intros; apply H; assumption.
  Qed.

  (* LFP is defined as the intersection of all F-closed sets. An
     element is in LFP iff it is a member of every F-Closed set. *)
  Definition LFP : PSet U :=
    fun a => forall S, FClosed S -> a ∈ S.

  Theorem LFP_is_FClosed
    : FClosed LFP.
  Proof.
    unfold FClosed.
    (* By the definition of LFP, it is a subset of every F-Closed set. *)
    assert (forall (X : PSet U), FClosed X -> LFP ⊆ X).
    { unfold subseteq, set_subseteq_instance; intros.
      apply H0. assumption. }
    (* Since F is monotone, the previous fact entails that [F LFP ⊆ F X]
       for every F-Closed set X.*)
    assert (forall (X : PSet U), FClosed X -> F LFP ⊆ F X).
    { intros. apply Monotone_F. apply H. assumption. }
    (* By transitivity of the subset relation, it follows that [F LFP ⊆ X]
       for every F-Closed set X.  *)
    assert (forall (X : PSet U), FClosed X -> F LFP ⊆ X).
    { intros. apply Subset_trans with (s2 := F X).
      - apply H0. assumption.
      - apply H1. }
    (* Now we just need to show that every element of [F LFP] is an
       element of [LFP], By definition, this is equivalent to showing
       that every element of [F LFP] is also a member of every
       F-Closed set. This follows from the fact that [F LFP] is a
       the previously proof that [F LFP] is a subset of every F-Closed set! *)
    unfold Subset; intros ? ? S FClosed_S.
    apply H1.
    assumption.
    assumption.
  Qed.

  Theorem LFP_is_FConsistent
    : FConsistent LFP.
  Proof.
    unfold FConsistent; intros.
    (*By the previous lemma, we know that F LFP ⊆ LFP. By monotonicity of
       F, F (F LFP) ⊆ F LFP. *)
    assert (F (F LFP) ⊆ F LFP).
    { apply Monotone_F. apply LFP_is_FClosed. }
    (* By definition, this means [F LFP] is F-Closed. *)
    assert (FClosed (F LFP)) by apply H.
    (* Since [F LFP] is F-Closed, it is a superset of LFP. *)
    intros x In_x.
    apply In_x.
    assumption.
  Qed.

  Theorem LFP_is_FixedPoint
    : FixedPoint LFP.
  Proof.
    unfold FixedPoint.
    split.
    - apply LFP_is_FClosed; eauto.
    - apply LFP_is_FConsistent; eauto.
  Qed.

  Theorem LFP_is_LeastFixedPoint :
    forall FP, FixedPoint FP -> LFP ⊆ FP.
  Proof.
    unfold FixedPoint; intros FP [? ?].
    intros x In_x.
    apply In_x.
    apply H.
  Qed.

  Corollary LFP_unfold : LFP ≡ (F LFP).
  Proof. apply FixedPoint_unfold. apply LFP_is_FixedPoint. Qed.

  Corollary LFP_fold : (F LFP) ≡ LFP.
  Proof. rewrite <- LFP_unfold. reflexivity. Qed.

  (* This admits the principle of Induction-- if we can show a set is
     F-Closed, it follows that every element of LFP is in that set. *)

  Lemma Ind
    : forall (Ind : PSet U),
      FClosed Ind -> forall a, LFP a -> Ind a.
  Proof.
    unfold LFP, FClosed; intros; eapply H0; eauto.
  Qed.

  (* GFP is defined as the union of all F-consistent sets.  An
     element is in GFP iff it is a member of /some/ F-Consistent set.*)
  Definition GFP : PSet U :=
    fun a => exists S, FConsistent S /\ a ∈ S.

  Lemma GFP_is_FConsistent
    : FConsistent GFP.
  Proof.
    unfold FConsistent.
    intros ? ?.
    (* By the definition of GFP, there must be some F-consistent set, X, that contains x *)
    destruct H as [X [? ?] ].
    (* Since X is F-consistent, by definition x is a member of F X. *)
    apply H in H0.
    (* We have now established that F X ⊆ F GFP: *)
    revert x H0; fold (Subset (F X) (F GFP)).
    (* Since F is monotone, it suffices to show that X ⊆ GFP *)
    eapply Monotone_F.
    (* To show X ⊆ GFP, we just need to show that every x in X is in GFP *)
    intros ? ?.
    (* By definition, x is an element of GFP if it is a member of an
    F-consistent set. By assumption, x is in X and F is F-consistent,
    so we're done!*)
    unfold In, GFP.
    eexists X.
    eauto.
  Qed.

  Lemma GFP_is_FClosed
    : FClosed GFP.
  Proof.
    intros ? ?.
    (* By our previous lemma, we know that GFP ⊆ F GFP. By monotonicity of
       F, F GFP ⊆ F (F GFP). *)
    assert (F GFP ⊆ F (F GFP)).
    { apply Monotone_F.
      apply GFP_is_FConsistent. }
    (* By definition, this means [F GFP] is F-consistent. *)
    assert (FConsistent (F GFP)).
    { intros ? ?.
      apply H0.
      assumption. }
    (* Since F is a member of an F-consistent set, it must be a member
    of GFP.*)
    unfold In, GFP.
    exists (F GFP).
    split; assumption.
  Qed.

  Theorem GFP_is_FixedPoint
    : FixedPoint GFP.
  Proof.
    unfold FixedPoint.
    split.
    - apply GFP_is_FClosed; eauto.
    - apply GFP_is_FConsistent; eauto.
  Qed.

  Theorem GFP_is_Greatest_FixedPoint
    : forall FP, FixedPoint FP -> FP ⊆ GFP.
  Proof.
    intros ? [? ?].
    intros x In_x.
    exists FP; split; assumption.
  Qed.

  (* This admits the principle of Co-Induction-- if we can show a set is
     F-Consistent, every element of that set is also in GFP. *)

  Lemma CoInd
    : forall (Ind : PSet U),
      FConsistent Ind -> forall a, Ind a -> GFP a.
  Proof.
    unfold GFP, FConsistent; intros; eauto.
  Qed.

End Fixpoints.

Section Ind_Example.
(*A quick example of the principle of Induction *)
Inductive isEven : nat -> Prop :=
| isEvenZero : isEven 0
| isEvenSS : forall (n : nat), isEven n -> isEven (S (S n)).

Definition isEven_F : PSet nat -> PSet nat :=
  fun X n => (n = 0) \/ (exists n', X n' /\ n = S (S n')).

Definition isEven' := LFP isEven_F.

Theorem isEven_eqv : forall n,
    isEven n <-> isEven' n.
Proof.
  split; intro.
  - induction H.
    + unfold isEven', LFP.
      intros.
      apply H.
      unfold isEven_F, In; intuition.
      compute; intuition.
    + unfold isEven', LFP.
      intros.
      apply H0.
      unfold isEven_F, In; right.
      eexists; intuition.
      unfold isEven' in IHisEven.
      apply IHisEven in H0; eauto.
  - unfold LFP in H. eapply Ind; try eassumption.
    intros ? ?; unfold In in *.
    destruct H0 as [ | [n' [? ?] ] ]; subst.
    + econstructor.
    + econstructor.
      eassumption.
Qed.

End Ind_Example.

(* Helper lemmas and tactics for working with sets. *)

(* Forward reasoning lemmas for simplifying assumptions involving
     set comprehensions into assumptions using basic set operations *)
Lemma elem_exists_forward {A B} (P : B -> PSet A) :
  forall (a : A),
    a ∈ (fun a => ∃ b : B, P b a)
    -> ∃ b : B, a ∈ (P b).
Proof.
  intuition.
Qed.

Lemma elem_and_forward {A} (P1 P2 : PSet A) :
  forall (a : A),
    a ∈ (fun a => P1 a /\ P2 a)
    -> a ∈ P1 /\ a ∈ P2.
Proof.
  set_solver.
Qed.

Lemma elem_or_forward {A} (P1 P2 : PSet A) :
  forall (a : A),
    a ∈ (fun a => P1 a \/ P2 a)
    -> a ∈ P1 \/ a ∈ P2.
Proof.
  intuition.
Qed.

(* Variants of our helper lemmas for sets of pairs: *)
Lemma elem_pair_exists_forward {A B C} (P : C -> A -> B -> Prop) :
  forall (ab : A * B ),
    ab ∈ (fun a : A * B => let (a, b) := a in ∃ c , P c a b ) ->
    exists c, ab ∈ (fun a : A * B => let (a, b) := a in P c a b).
Proof.
  intros (a, b) In_a_b; intuition.
Qed.

Lemma elem_pair_and_forward {A B} (P1 P2 : A -> B -> Prop) :
  forall (a : A * B ),
    a ∈ (fun a : A * B => let (a, b) := a in P1 a b /\ P2 a b)
    -> a ∈ (fun a : A * B => let (a, b) := a in P1 a b) /\
         a ∈ (fun a : A * B => let (a, b) := a in P2 a b).
Proof.
  intros (a, b); set_solver.
Qed.

Lemma elem_pair_or_forward {A B} (P1 P2 : A -> B -> Prop) :
  forall (a : A * B ),
    a ∈ (fun a : A * B => let (a, b) := a in P1 a b \/ P2 a b)
    -> a ∈ (fun a : A * B => let (a, b) := a in P1 a b) \/
         a ∈ (fun a : A * B => let (a, b) := a in P2 a b).
Proof.
  intros (a, b); intuition.
Qed.

Lemma elem_singleton_forward {A} :
  forall (a a' : A),
    a ∈ (fun a => a = a')
    -> a = a'.
Proof.
  intuition.
Qed.

Lemma elem_singleton_sym_forward {A} :
  forall (a a' : A),
    a ∈ (fun a => a' = a)
    -> a = a'.
Proof.
  intuition.
Qed.

(* Backward reasoning lemmas for decomposing goals involving set
     comprehensions into subgoals involving basic set operations *)
Lemma elem_exists_backward {A B} (P : B -> PSet A) :
  forall (a : A),
    (∃ b : B, a ∈ (P b)) ->
    a ∈ (fun a => ∃ b : B, P b a).
Proof.
  intuition.
Qed.

Lemma elem_and_backward {A} (P1 P2 : PSet A) :
  forall (a : A),
    a ∈ P1 ->
    a ∈ P2 ->
    a ∈ (fun a => P1 a /\ P2 a).
Proof.
  intros; split; auto.
Qed.

Lemma elem_or_backward {A} (P1 P2 : PSet A) :
  forall (a : A),
    a ∈ P1 \/ a ∈ P2 ->
    a ∈ (fun a => P1 a \/ P2 a).
Proof.
  set_solver.
Qed.

Lemma elem_pair_fst_singleton_forward {A B} :
  forall (ab : A * B) (a' : A),
    ab ∈ (fun ab': A * B => let (a, b) := ab' in a = a')
    -> fst ab = a'.
Proof.
  intuition.
Qed.

Lemma elem_pair_snd_singleton_forward {A B} :
  forall (ab : A * B) (b' : B),
    ab ∈ (fun ab': A * B => let (a, b) := ab' in b = b')
    -> snd ab = b'.
Proof.
  intuition.
Qed.

Lemma elem_pair_singleton_forward {A B} (f : B -> A):
  forall (ab : A * B),
    ab ∈ (fun ab': A * B => let (a, b) := ab' in a = f b)
    -> fst ab = f (snd ab).
Proof.
  intros (a, b); firstorder.
Qed.

Lemma elem_pair_singleton_sym_forward {A B} (f : B -> A):
  forall (ab : A * B),
    ab ∈ (fun ab: A * B => let (a, b) := ab in f b = a)
    -> fst ab = f (snd ab).
Proof.
  intros (a, b); firstorder.
Qed.

Lemma elem_pair_singleton_forward' {A B} (f : A -> B):
  forall (ab : A * B),
    ab ∈ (fun ab': A * B => let (a, b) := ab' in f a = b)
    -> f (fst ab) = snd ab.
Proof.
  intros (a, b); firstorder.
Qed.

Lemma elem_pair_singleton_sym_forward' {A B} (f : A -> B):
  forall (ab : A * B),
    ab ∈ (fun ab: A * B => let (a, b) := ab in b = f a)
    -> f (fst ab) = snd ab.
Proof.
  intros (a, b); firstorder.
Qed.

Lemma elem_pair_fst_singleton_sym_forward {A B} :
  forall (ab : A * B) (a' : A),
    ab ∈ (fun ab': A * B => let (a, b) := ab' in a' = a)
    -> fst ab = a'.
Proof.
  intuition.
Qed.

Lemma elem_pair_snd_singleton_sym_forward {A B} :
  forall (ab : A * B) (b' : B),
    ab ∈ (fun ab': A * B => let (a, b) := ab' in b' = b)
    -> snd ab = b'.
Proof.
  intuition.
Qed.

(* Variants of our helper lemmas for sets of pairs: *)
Lemma elem_pair_exists_backward {A B C} (P : C -> A -> B -> Prop) :
  forall (ab : A * B),
    (exists c, ab ∈ (fun a : A * B => let (a, b) := a in P c a b)) ->
    ab ∈ (fun a : A * B => let (a, b) := a in ∃ c , P c a b ).
Proof.
  intros (a, b) In_a_b; intuition.
Qed.

Lemma elem_pair_and_backward {A B} (P1 P2 : A -> B -> Prop) :
  forall (a : A * B ),
    a ∈ (fun a : A * B => let (a, b) := a in P1 a b) ->
    a ∈ (fun a : A * B => let (a, b) := a in P2 a b) ->
    a ∈ (fun a : A * B => let (a, b) := a in P1 a b /\ P2 a b).
Proof.
  intros (a, b); intros; split; intuition.
Qed.

Lemma elem_pair_or_backward {A B} (P1 P2 : A -> B -> Prop) :
  forall (a : A * B ),
    a ∈ (fun a : A * B => let (a, b) := a in P1 a b) \/
      a ∈ (fun a : A * B => let (a, b) := a in P2 a b) ->
    a ∈ (fun a : A * B => let (a, b) := a in P1 a b \/ P2 a b).
Proof.
  intros (a, b); firstorder.
Qed.

Lemma elem_singleton_backward {A} :
  forall (a a' : A),
    a = a' ->
    a ∈ (fun a => a = a').
Proof.
  intuition.
Qed.

Lemma elem_singleton_sym_backward {A} :
  forall (a a' : A),
    a = a' ->
    a ∈ (fun a => a' = a).
Proof.
  subst; set_solver.
Qed.

Lemma elem_pair_fst_singleton_backward {A B} :
  forall (ab : A * B) (a' : A),
    fst ab = a' ->
    ab ∈ (fun ab': A * B => let (a, b) := ab' in a = a').
Proof.
  intuition.
Qed.

Lemma elem_pair_snd_singleton_backward {A B} :
  forall (ab : A * B) (b' : B),
    snd ab = b' ->
    ab ∈ (fun ab': A * B => let (a, b) := ab' in b = b').
Proof.
  intuition.
Qed.

Lemma elem_pair_fst_singleton_sym_backward {A B} :
  forall (ab : A * B) (a' : A),
    fst ab = a' ->
    ab ∈ (fun ab': A * B => let (a, b) := ab' in a' = a).
Proof.
  intros (a, b); set_solver.
Qed.

Lemma elem_pair_snd_singleton_sym_backward {A B} :
  forall (ab : A * B) (b' : B),
    snd ab = b' ->
    ab ∈ (fun ab': A * B => let (a, b) := ab' in b' = b).
Proof.
  intros (a, b); set_solver.
Qed.


Lemma In_pair_inv {A B} :
  forall ab (s : PSet (Datatypes.prod A B)),
    ab ∈ s -> exists a b, ab = Datatypes.pair a b /\ s (Datatypes.pair a b).
Proof.
  destruct ab; eauto.
Qed.

Lemma In_union_if_or {A} :
  forall a (s1 s2 : PSet A),
    a ∈ (s1 ∪ s2) -> a ∈ s1 \/ a ∈ s2.
Proof.
  intros ? ? ? [? | ?]; eauto.
Qed.

Lemma In_union_if_or_conv {A} :
  forall a (s1 s2 : PSet A),
    a ∈ s1 \/ a ∈ s2 -> a ∈ (s1 ∪ s2).
Proof.
  intros ? ? ? [? | ?]; compute; intuition.
Qed.

Lemma adjust_pair_prop_backward {A B} (P : A -> B -> Prop):
  forall (ab : A * B),
    ab ∈ (fun ab' : A * B => P (fst ab') (snd ab')) ->
    ab ∈ (fun ab' : A * B => let (a, b) := ab' in
                             P a b).
Proof.
  intros (a, b); firstorder.
Qed.

Lemma adjust_pair_prop_forward {A B} (P : A -> B -> Prop):
  forall (ab : A * B),
    ab ∈ (fun ab' : A * B => let (a, b) := ab' in
                             P a b) ->
    ab ∈ (fun ab' : A * B => P (fst ab') (snd ab')).
Proof.
  intros (a, b); firstorder.
Qed.

Lemma adjust_pair_prop_f_forward {A B C} (P : A -> B -> Prop)
      (f : C -> A * B):
  forall c,
    c ∈ (fun c : C => let (a, b) := f c in
                      P a b) ->
    c ∈ (fun c : C => P (fst (f c)) (snd (f c))).
Proof.
  compute in *; intros; destruct (f c); auto.
Qed.

Lemma adjust_pair_prop_f_backward {A B C} (P : A -> B -> Prop)
      (f : C -> A * B):
  forall c,
    c ∈ (fun c : C => P (fst (f c)) (snd (f c))) ->
    c ∈ (fun c : C => let (a, b) := f c in
                      P a b).
Proof.
  compute in *; intros; destruct (f c); auto.
Qed.

Ltac In_inversion :=
  repeat match goal with
         | H : @In _ _ (_ ∪ _) |- _ => apply In_union_if_or in H
         | H : @In (Datatypes.prod ?A ?B) ?ab _ |- _ =>
             apply In_pair_inv in H;
             destruct H as [? [? [? H] ] ]; subst ab
         | |- @Fixpoints.In _ _ (_ ∪ _) => apply In_union_if_or_conv
         (* existentials: *)
         | H : _ ∈ (fun a => ∃ b , _) |- _ =>
             let b' := fresh b in
             apply elem_exists_forward in H; destruct H as [b' H]
         | H : _ ∈ (fun a : prod _ _ => let (a1, a2) := a in ∃ b , @?P b a1 a2) |- _ =>
             let b' := fresh b in
             apply elem_pair_exists_forward in H; destruct H as [b' H]
         (* conjunction *)
         | H : _ ∈ (fun a => @?P a /\ @?Q a) |- _ =>
             apply elem_and_forward in H; destruct H
         | H : _ ∈ (fun a => let (a', b) := a in @?P a' b /\ @?Q a' b) |- _ =>
             apply elem_pair_and_forward in H; destruct H

         (* disjunction *)
         | H : _ ∈ (fun a => @?P a \/ @?Q a) |- _ =>
             apply elem_or_forward in H; destruct H
         | H : _ ∈ (fun a => let (a', b) := a in @?P a' b \/ @?Q a' b) |- _ =>
             apply elem_pair_or_forward in H; destruct H

         (* singletons: *)
         | H : _ ∈ (fun a => a = _) |- _ =>
             apply elem_singleton_forward in H; subst
         | H : _ ∈ (fun a => _ = a) |- _ =>
             apply elem_singleton_sym_forward in H; subst

         | H : _ ∈ (fun aa' => let (a, a') := aa' in a = a') |- _ =>
             apply (elem_pair_singleton_forward id) in H; simpl in H; subst
         | H : _ ∈ (fun aa' => let (a, a') := aa' in a' = a) |- _ =>
             apply (elem_pair_singleton_sym_forward id) in H; simpl in H; subst
         | H : _ ∈ (fun aa' => let (a, a') := aa' in a = @?f a') |- _ =>
             apply (elem_pair_singleton_forward f) in H; simpl in H; subst
         | H : _ ∈ (fun aa' => let (a, a') := aa' in @?f a' = a) |- _ =>
             apply (elem_pair_singleton_sym_forward f) in H; simpl in H; subst
         | H : _ ∈ (fun aa' => let (a, a') := aa' in @?f a = a') |- _ =>
             apply (elem_pair_singleton_forward' f) in H; simpl in H; subst
         | H : _ ∈ (fun aa' => let (a, a') := aa' in a' = @?f a) |- _ =>
             apply (elem_pair_singleton_sym_forward' f) in H; simpl in H; subst

         | H : _ ∈ (fun a' => let (a, b) := a' in a = _) |- _ =>
             apply elem_pair_fst_singleton_forward in H; simpl in H; subst
         | H : _ ∈ (fun a' => let (a, b) := a' in b = _) |- _ =>
             apply elem_pair_snd_singleton_forward in H; simpl in H; subst
         | H : _ ∈ (fun a' => let (a, b) := a' in _ = a) |- _ =>
             apply elem_pair_fst_singleton_sym_forward in H; simpl in H; subst
         | H : _ ∈ (fun a' => let (a, b) := a' in _ = b) |- _ =>
             apply elem_pair_snd_singleton_sym_forward in H; simpl in H; subst

         (* Munging pairs around so previous patterns match *)
         | H : _ ∈ (fun ab' => let (a, b) := ab' in
                               @?P a b) |- _ =>
             apply (adjust_pair_prop_forward P) in H; simpl in H
         | H : _ ∈ (fun ab' => let (a, b) := @?f ab' in _) |- _ =>
             apply adjust_pair_prop_f_forward in H; simpl in H

         (* | H : elem_of _ _ |- _ => unfold elem_of in H *)
         | H : @PSet_In_ElemOf _ _ _ |- _ => unfold PSet_In_ElemOf in H
         | H : @Fixpoints.In _ _ _ |- _ => unfold Fixpoints.In in H

         (* Simplifying nested elements *)
         | H : _ ∈ (fun a => let (_, _) := a in _ ∈ _) |- _ =>
             unfold elem_of at 1, PSet_In_ElemOf, Fixpoints.In in H
         | H : _ ∈ (fun a => _ ∈ _) |- _ =>
             unfold elem_of at 1, PSet_In_ElemOf, Fixpoints.In in H

         | H : _ /\ _ |- _ => destruct H
         | H : _ \/ _ |- _ => destruct H
         | H : _ ∪ _ |- _ => unfold Union in H
         | H : exists _, _ |- _ => destruct H
         | H : _ = _ |- _ => solve [discriminate]
         end.

Ltac destruct_ex :=
  repeat match goal with
         | H : exists a : _ * _ , _ |- _ =>
             let a' := fresh a in
             let a'' := fresh a in
             destruct H as [ [a' a''] H]
         | H : exists a , _ |- _ =>
             let a' := fresh a in
             destruct H as [a' H]
         end.

Ltac In_intro :=
  repeat match goal with
         (* existentials: *)
         | |- _ ∈ (fun a => ∃ b , _) =>
             apply elem_exists_backward; eexists _
         | |- _ ∈ (fun a : prod _ _ => let (a1, a2) := a in ∃ b , @?P b a1 a2) =>
             apply elem_pair_exists_backward; eexists _

         (* conjunction *)
         | |- _ ∈ (fun a => @?P a /\ @?Q a)  =>
             apply elem_and_backward
         | |- _ ∈ (fun a => let (a', b) := a in @?P a' b /\ @?Q a' b)  =>
             apply elem_pair_and_backward

         (* disjunction *)
         | |- _ ∈ (fun a => @?P a \/ @?Q a)  =>
             apply elem_or_backward
         | |- _ ∈ (fun a => let (a', b) := a in @?P a' b \/ @?Q a' b)  =>
             apply elem_pair_or_backward

         (* singletons: *)
         | |- _ ∈ (fun a => a = _)  =>
             apply elem_singleton_backward
         | |- _ ∈ (fun a => _ = a)  =>
             apply elem_singleton_sym_backward
         | |- _ ∈ (fun a' => let (a, b) := a' in a = _) =>
             apply elem_pair_fst_singleton_backward
         | |- _ ∈ (fun a' => let (a, b) := a' in b = _)  =>
             apply elem_pair_snd_singleton_backward
         | |- _ ∈ (fun a' => let (a, b) := a' in _ = a)  =>
             apply elem_pair_fst_singleton_sym_backward
         | |- _ ∈ (fun a' => let (a, b) := a' in _ = b)  =>
             apply elem_pair_snd_singleton_sym_backward

         (* Simplifying nested elements *)
         | |- _ ∈ (fun a => let (_, _) := a in _ ∈ _) =>
             unfold elem_of at 1, PSet_In_ElemOf, Fixpoints.In
         | |- _ ∈ (fun a => _ ∈ _) =>
             unfold elem_of at 1, PSet_In_ElemOf, Fixpoints.In

         (* Munging pairs around so previous patterns match *)
         | |- _ ∈ (fun ab' => let (a, b) := ab' in @?P a b) =>
             apply (adjust_pair_prop_backward P); simpl
         | |- _ ∈ (fun ab' => let (a, b) := @?f ab' in _) =>
             apply (adjust_pair_prop_f_backward _ f); simpl

         end.
