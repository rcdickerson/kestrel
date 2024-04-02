From Coq Require Import Strings.String.
From Coq Require Import Setoids.Setoid.
From Common Require Import Id Fixpoints.
From Imp Require Import Syntax Semantics.
From CR Require Import Syntax Semantics Hoare Equiv Embed.

Import Imp.Syntax.notations.
Import Imp.Semantics.notations.
Import CR.Syntax.notations.
Import CR.Semantics.notations.
Import CR.Semantics.notations.

Definition I := string.
Context {M : Type -> Type}.
Context {id : Id I M}.

Section Examples.

  Variable W X Y Z : I.

  Lemma comm_def : forall c1 c2 c3 c4,
      align_eqv <{ <|c1; c2 | c3; c4|> }> <{ <| c1 | c3|> ;; <| c2 | c4 |> }>.
  Proof.
    intros. rewrite rel_def. rewrite  prod_hom_l. rewrite prod_hom_r.
    rewrite prod_seq_assoc.
    rewrite <- prod_seq_assoc with (r3 := <{<| skip | c4 |>}>) . rewrite <- rel_comm.
    rewrite <- !prod_seq_assoc.  rewrite <- rel_def.
    rewrite prod_seq_assoc. rewrite <- rel_def. reflexivity.
  Qed.

  Lemma comm_skip : forall c1 c3 c4,
      align_eqv <{ <|c1 | c3; c4|> }> <{ <| c1 | c3|> ;; <| skip | c4 |> }>.
  Proof.
    intros. rewrite rel_def. rewrite prod_hom_r. rewrite <- prod_seq_assoc.
    rewrite <- rel_def. reflexivity.
  Qed.

  Definition ex_1 Y Z : @algn_com I :=
    <{
     <| Y := 0 | Y := 0 |>;;
     <| Z :=  2 * 2 | Z := 2 * 2|> }>.

  Compute reify_com (ex_1 Y Z).

  Definition ex_2 Y Z : @algn_com I :=
   <{ <| Y := 0 ; Z := 2 * 2 | skip |>;;
      <| skip | Y :=  0 ; Z := 2 * 2|> }>.

  Compute reify_com (ex_2 Y Z).

  Lemma example_12 : align_eqv  (ex_1 Y Z) (ex_2 Y Z).
  Proof.
    unfold ex_2. rewrite <- rel_def.  rewrite comm_def. reflexivity.
  Qed.

  Definition AId' : I -> aexp := AId.
  Coercion AId' : I >-> aexp.

  Definition kestrel_paper_p1 : @com I :=
   <{Y := 0;
     Z := 2 * X;
     while (~(Z <= 0)) do
       Z := Z - 1;
       Y := Y + X;
       Z := Z - 1;
       Y := Y + X
       end}>.

  Definition kestrel_paper_p2 : @com I :=
    <{ Y := 0;
      Z := X;
     while ~ (Z <= 0) do
       Z := Z - 1;
       Y := Y + X
     end; Y := Y * 2 }>.

  Definition kestrel_paper_example_1_prod_efficient : @algn_com I :=
 <{ <| Y := 0 | Y := 0 |>;;
     <| Z :=  2 * X | Z := X|>;;
   (whileR <| ~(Z <= 0) | ~(Z <= 0) |> do
            <| Z := Z - 1; Y := Y + X;
               Z :=  Z - 1; Y := Y + X |
               Z :=  Z - 1; Y := Y + X |> end;; <|while  ~(Z <= 0) do Z := Z - 1; Y := Y + X;
               Z :=  Z - 1; Y := Y + X end | while ~(Z <= 0) do  Z :=  Z - 1; Y := Y + X end|>);;
     <| skip | Y := Y * 2 |> }>.

  Definition kestrel_paper_skip1 : @com I := <{skip}>.

  Definition kestrel_paper_skip2 : @com I := <{ skip }>.

  Definition kestrel_paper_skip_prod_efficient : @algn_com I :=
    <{ <|skip | skip|>}>.

  Definition kestrel_paper_while1 : @com I := <{while false do skip end}>.

  Definition kestrel_paper_while2 : @com I := <{while false do skip end}>.

  Definition kestrel_paper_while_prod_efficient : @algn_com I :=
    <{ whileR <| false | false |> do <|skip | skip|> end ;;
    <| while false do skip end | while false do skip end |>}>.


  Lemma paper_example1_eqv : align_eqv (embed_com kestrel_paper_p1 kestrel_paper_p2)
                                       kestrel_paper_example_1_prod_efficient.
  Proof.
    unfold kestrel_paper_p1, kestrel_paper_p2; unfold embed_com; simpl.
    rewrite comm_def.
    rewrite comm_def.
    rewrite comm_skip.
    rewrite whileR_lockstep.
    reflexivity.
  Qed.

  Lemma paper_while_eqv : align_eqv (embed_com kestrel_paper_while1 kestrel_paper_while2)
                                    kestrel_paper_while_prod_efficient.
  Proof.
    unfold kestrel_paper_while1, kestrel_paper_while2; unfold embed_com; simpl.
    rewrite whileR_lockstep. unfold kestrel_paper_while_prod_efficient. reflexivity.
  Qed.


  Lemma paper_skip_eqv : align_eqv (embed_com kestrel_paper_skip1 kestrel_paper_skip2)
                                   kestrel_paper_skip_prod_efficient.
  Proof.
    unfold kestrel_paper_skip1, kestrel_paper_skip2; unfold embed_com; simpl.
    unfold kestrel_paper_skip_prod_efficient. reflexivity.
  Qed.

  Definition equiv_state : @Assertion M :=
    fun st: state => forall id : I, (st : @prod_M M nat) !!! (@inl I I id : prod_I) = (st : @prod_M M nat) !!! (@inr I I id : prod_I).


  Ltac assn_auto :=
    try auto;
    try (unfold assert_implies, assn_sub, insert;
         intros; simpl in *; lia).

  Lemma paper_skip :
    hoare_triple_relational equiv_state
                            kestrel_paper_skip1 kestrel_paper_skip2
                            equiv_state.
  Proof.
    eapply hoare_triple_prod_a. split.
    symmetry. exact paper_skip_eqv.
    simpl. unfold hoare_triple_product, equiv_state.
    eapply hoare_seq. apply hoare_skip. apply hoare_skip.
  Qed.

End Examples.
