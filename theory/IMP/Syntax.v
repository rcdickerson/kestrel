(** * Imp: Simple Imperative Programs *)

(* This definition is largely identical to the one in Programming
   Language Foundations, except that the definitions are now
   parametric in the set of variable identifiers. *)

Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lia.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
Import ListNotations.

From Common Require Import Id.
From stdpp Require Export prelude fin_maps fin_map_dom.

Section Syntax.

  (* The type of variables identifiers. *)
  Context {I : Type}.
  Context {M : Type -> Type}.
  Context {id : Id I M}.

(* ================================================================= *)
(** ** Syntax  *)

(** We can add variables to the arithmetic expressions we had before by
    simply adding one more constructor: *)

Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : I)              (* <--- NEW *)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

(** Defining a few variable names as notational shorthands will make
    examples easier to read: *)

Variable W X Y Z : I.

(** The definition of [bexp]s is unchanged (except that it now refers
    to the new [aexp]s): *)

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

(* ================================================================= *)
(** ** Notations *)

(** To make Imp programs easier to read and write, we introduce some
    notations and implicit coercions.  You do not need to understand
    exactly what these declarations do.  Briefly, though:
       - The [Coercion] declaration stipulates that a function (or
         constructor) can be implicitly used by the type system to
         coerce a value of the input type to a value of the output
         type.  For instance, the coercion declaration for [AId]
         allows us to use plain strings when an [aexp] is expected;
         the string will implicitly be wrapped with [AId].
       - [Declare Custom Entry com] tells Coq to create a new
         "custom grammar" for parsing Imp expressions and
         programs. The first notation declaration after this tells Coq
         that anything between [<{] and [}>] should be parsed using
         the Imp grammar. Again, it is not necessary to understand the
         details, but it is important to recognize that we are
         defining _new_ interpretations for some familiar operators
         like [+], [-], [*], [=], [<=], etc., when they occur between
         [<{] and [}>]. *)

Coercion AId : I >-> aexp.
Coercion ANum : nat >-> aexp.

(* ################################################################# *)
(** * Commands *)

(** Now we are ready define the syntax and behavior of Imp
    _commands_ (sometimes called _statements_). *)

(* ================================================================= *)
(** ** Syntax *)

(** Informally, commands [c] are described by the following BNF
    grammar.

     c := skip | x := a | c ; c | if b then c else c end
         | while b do c end
*)

Inductive com : Type :=
  | CSkip
  | CAss (x : I) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).
End Syntax.

Module notations.

  Context {I : Type}.
  Context {M : Type -> Type}.
  Context {id : Id I M}.

  Declare Custom Entry com.
  Declare Scope com_scope.

  Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
  Notation "( x )" := x (in custom com, x at level 99) : com_scope.
  Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
  Notation "f x .. y" := (.. (f x) .. y)
                           (in custom com at level 0, only parsing,
                               f constr at level 0, x constr at level 9,
                               y constr at level 9) : com_scope.
  Notation "x + y" := (APlus x y) (in custom com at level 50, left associativity).
  Notation "x - y" := (AMinus x y) (in custom com at level 50, left associativity).
  Notation "x * y" := (AMult x y) (in custom com at level 40, left associativity).
  Notation "'true'"  := true (at level 1).
  Notation "'true'"  := BTrue (in custom com at level 0).
  Notation "'false'"  := false (at level 1).
  Notation "'false'"  := BFalse (in custom com at level 0).
  Notation "x <= y" := (BLe x y) (in custom com at level 70, no associativity).
  Notation "x = y"  := (BEq x y) (in custom com at level 70, no associativity).
  Notation "x && y" := (BAnd x y) (in custom com at level 80, left associativity).
  Notation "'~' b"  := (BNot b) (in custom com at level 75, right associativity).

  Notation "'skip'"  :=
    CSkip (in custom com at level 0) : com_scope.
  Notation "x := y"  :=
    (CAss x y)
      (in custom com at level 0, x constr at level 0,
          y at level 85, no associativity) : com_scope.
  Notation "x ; y" :=
    (CSeq x y)
      (in custom com at level 90, right associativity) : com_scope.
  Notation "'if' x 'then' y 'else' z 'end'" :=
    (CIf x y z)
      (in custom com at level 89, x at level 99,
          y at level 99, z at level 99) : com_scope.
  Notation "'while' x 'do' y 'end'" :=
    (CWhile x y)
      (in custom com at level 89, x at level 99, y at level 99) : com_scope.

  Open Scope com_scope.

End notations.
