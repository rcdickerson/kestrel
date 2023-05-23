From Imp Require Import Syntax Semantics.
From Common Require Import Id.
From stdpp Require Export prelude fin_maps fin_map_dom.

(* Aligned Commands *)

Section Syntax.

  (* The type of variables identifiers. *)
  Context {I : Type}.
  Context {M : Type -> Type}.
  Context {id : Id I M}.

  Inductive algn_com : Type :=
  | ACBlock (s1 s2 : @com I) : algn_com
  | ACSeq (r1 r2 : algn_com) : algn_com
  | ACIf (b1 b2 : @bexp I) (r1 r2 : algn_com) : algn_com
  | ACWhile (b1 b2 : @bexp I) (r : algn_com) : algn_com.

End Syntax.

Module notations.

  Context {I : Type}.
  Context {M : Type -> Type}.
  Context {id : Id I M}.

Notation "'<|' s1 '|' s2 '|>'"  :=
  (ACBlock s1 s2) (in custom com at level 91, s1 at level 99, s2 at level 99) : com_scope.

Notation "r1 ';;' r2" :=
         (ACSeq r1 r2)
           (in custom com at level 90, right associativity) : com_scope.

Notation "'ifR' '<|' b1 '|' b2 '|>' 'then' r1 'else' r2 'end'" :=
         (ACIf b1 b2 r1 r2)
           (in custom com at level 89, b1 at level 99, b2 at level 99,
               r1 at level 99, r2 at level 99) : com_scope.

Notation "'whileR' '<|' b1 '|' b2 '|>' 'do' r 'end'" :=
         (ACWhile b1 b2 r)
            (in custom com at level 89, b1 at level 99, b2 at level 99, r at level 99) : com_scope.

Open Scope com_scope.

Import Imp.Syntax.notations.

(* Definition ex_1 X Y Z : @algn_com I :=
  <{ <| Y := 0 | Y := 0 |>;;
     <| Z :=  2 * X | Z := X|>;;
     whileR <| true | false |> do
            <| Z := Z - 1; Y := Y + X;
               Z :=  Z - 1; Y := Y + X |
               Z :=  Z - 1; Y := Y + X |> end;;
     <| skip | Y := Y * 2 |> }>. *)

End notations.
