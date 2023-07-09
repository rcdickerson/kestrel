From Common Require Import Id Fixpoints.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Strings.String.
From Imp Require Import Syntax Semantics Equiv.

Import ListNotations.

From Common Require Import Id Fixpoints.

From stdpp Require Export prelude fin_maps fin_map_dom.
From Imp Require Import Syntax.

Import Imp.Syntax.notations.
Import Imp.Semantics.notations.

Section Definitions.
(* The type of variable identifiers. *)
Definition I := @prod_I string.
Context {M : Type -> Type}.
Context {id : Id I (@prod_M M)}.

Definition state := (@prod_M M) nat.

Definition Assertion := state -> Prop.

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Declare Scope hoare_spec_scope.
Notation "P ->> Q" := (assert_implies P Q) (at level 80) : hoare_spec_scope.
Open Scope hoare_spec_scope.
Notation "P <<->> Q" :=
  (P ->> Q /\ Q ->> P) (at level 80) : hoare_spec_scope. 


Definition Aexp : Type := state -> nat.

Definition assert_of_Prop (P : Prop) : Assertion := fun _ => P.
Definition Aexp_of_nat (n : nat) : Aexp := fun _ => n.

Definition Aexp_of_aexp (a : aexp) : Aexp := fun st => aeval st a.

Coercion assert_of_Prop : Sortclass >-> Assertion.
Coercion Aexp_of_nat : nat >-> Aexp.
Coercion Aexp_of_aexp : aexp >-> Aexp.
Add Printing Coercion Aexp_of_nat Aexp_of_aexp assert_of_Prop.

Arguments assert_of_Prop /.
Arguments Aexp_of_nat /.
Arguments Aexp_of_aexp /.
Add Printing Coercion Aexp_of_nat Aexp_of_aexp assert_of_Prop.

Declare Scope assertion_scope.
Bind Scope assertion_scope with Assertion.
Bind Scope assertion_scope with Aexp.
Delimit Scope assertion_scope with assertion.

Notation assert P := (P%assertion : Assertion).
Notation mkAexp a := (a%assertion : Aexp).

Notation "~ P" := (fun st => ~ assert P st) : assertion_scope.
Notation "P /\ Q" := (fun st => assert P st /\ assert Q st) : assertion_scope.
Notation "P \/ Q" := (fun st => assert P st \/ assert Q st) : assertion_scope.
Notation "P -> Q" := (fun st => assert P st ->  assert Q st) : assertion_scope.
Notation "P <-> Q" := (fun st => assert P st <->  assert Q st) : assertion_scope.
Notation "a = b" := (fun st => mkAexp a st = mkAexp b st) : assertion_scope.
Notation "a <> b" := (fun st => mkAexp a st <> mkAexp b st) : assertion_scope.
Notation "a <= b" := (fun st => mkAexp a st <= mkAexp b st) : assertion_scope.
Notation "a < b" := (fun st => mkAexp a st < mkAexp b st) : assertion_scope.
Notation "a >= b" := (fun st => mkAexp a st >= mkAexp b st) : assertion_scope.
Notation "a > b" := (fun st => mkAexp a st > mkAexp b st) : assertion_scope.
Notation "a + b" := (fun st => mkAexp a st + mkAexp b st) : assertion_scope.
Notation "a - b" := (fun st => mkAexp a st - mkAexp b st) : assertion_scope.
Notation "a * b" := (fun st => mkAexp a st * mkAexp b st) : assertion_scope.


Definition ap {X} (f : nat -> X) (x : Aexp) :=
  fun st => f (x st).

Definition ap2 {X} (f : nat -> nat -> X) (x : Aexp) (y : Aexp) (st : state) :=
  f (x st) (y st).


Definition hoare_triple
           (P : Assertion) (c : @com I) (Q : Assertion) : Prop :=
  forall st st',
     P st  ->
      st =[ c ]=> st' ->
     Q st'.

Notation "{{ P }}  c  {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c custom com at level 99)
  : hoare_spec_scope.


Definition assn_sub X a (P:Assertion) : Assertion :=
  fun (st : state) => 
    P (<[X := aeval st a]> st).

Set Printing All.
Print assn_sub.
Unset Printing All.

Notation "P [ X |-> a ]" := (assn_sub X a P)
  (at level 10, X at next level, a custom com) : hoare_spec_scope.


(*skip rule*)
Theorem hoare_skip : forall P,
     hoare_triple P <{skip}> P.
Proof.
  unfold hoare_triple. intros. inversion H0; subst. assumption.
Qed.

(*sequence*)
Theorem hoare_seq : forall P Q R r1 r2,
     hoare_triple Q r2 R ->
     hoare_triple P r1 Q ->
     hoare_triple P <{r1; r2}> R.
Proof.
 unfold hoare_triple; intros. inversion H2; subst. eapply H0 in H1.
 eapply H. eassumption. eassumption. eassumption.
Qed.

(*hoare_triple (assn_sub X a Q) X := a Q*)
Theorem hoare_asgn : forall Q X a, 
  hoare_triple (assn_sub X a Q) <{X := a}> Q.
Proof.
unfold hoare_triple, assn_sub. intros. inversion H0; subst. 
assumption.
Qed.

Hint Unfold assert_implies hoare_triple assn_sub insert : core.
Hint Unfold assert_of_Prop Aexp_of_nat Aexp_of_aexp : core.

(*assn_auto, assn_auto''*)
Ltac assn_auto :=
  try auto; 
  try (unfold "->>", assn_sub, insert;
       intros; simpl in *; lia).

Print assn_auto.



(*strengthen precc.*)
Theorem hoare_consequence_pre : forall (P P' Q : Assertion) r,
  hoare_triple P' r Q ->
  assert_implies P P' ->
  hoare_triple P r Q. 
Proof.
 unfold hoare_triple, "->>".
  intros P P' Q c Hhoare Himp st st' Heval Hpre.
  eapply Hhoare. eapply Himp. eassumption. assumption.
Qed.

(*weaken post.*)
Theorem hoare_consequence_post : forall (P Q Q' : Assertion) r,
  hoare_triple P r Q' ->
  assert_implies Q' Q ->
  hoare_triple P r Q. 
Proof.
 unfold hoare_triple, "->>". intros.
 eapply H0. eapply H. eassumption. assumption.
Qed.


Definition bassn b : Assertion :=
  fun st => (beval st b = true).

Coercion bassn : bexp >-> Assertion.

Arguments bassn /.

Ltac assn_auto' :=
  unfold "->>", assn_sub, insert, bassn;
  intros; simpl in *;
  try rewrite -> eqb_eq in *; (* for equalities *)
  auto; try lia.

Ltac assn_auto'' :=
  unfold "->>", assn_sub, insert, bassn;
  intros; simpl in *;
  try rewrite -> eqb_eq in *;
  try rewrite -> leb_le in *;  (* for inequalities *)
  auto; try lia.

(** A useful fact about [bassn]: *)

Lemma bexp_eval_false : forall b st,
  beval st b = false -> ~ ((bassn b) st).
Proof. congruence. Qed.

Hint Resolve bexp_eval_false : core.

(*hoare_if*)
Theorem hoare_if : forall P Q (b:bexp) r1 r2,
  hoare_triple (P /\ b) r1 Q ->
  hoare_triple (P /\ ~ b) r2 Q ->
  hoare_triple P <{if b then r1 else r2 end}> Q.
Proof.
unfold hoare_triple; intros.
inversion H2; subst. eapply H. eauto.
assumption. eauto.
Qed.

(*hoare_while*)
Theorem hoare_while : forall P (b: bexp) r,
  hoare_triple (P /\ b) r P ->
  hoare_triple P <{while b do r end}> (P /\ ~ b).
Proof.
unfold hoare_triple; intros. 
remember <{while b do r end}> as original_command eqn:Horig.
induction H1. discriminate. discriminate. discriminate. discriminate.
discriminate. inversion Horig; subst. eauto. 
inversion Horig; subst. eauto.
Qed.

End Definitions.



