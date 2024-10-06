From stdpp Require Import stringmap mapset.
From Coq Require Import String.

(* This class allows us to avoid carrying around the bazillion of hypotheses
   that stdpp's finite map implementation expects :p *)

Class Id A M := {
  (* Constraints. *)
    id_finmap_fmap :: FMap M | 0;
    id_finmap_lookup :: ∀ C, Lookup A C (M C) | 0;
    id_finmap_empty :: ∀ C, Empty (M C) | 0;
    id_finmap_partial_alter :: ∀ C, PartialAlter A C (M C) | 0;
    id_finmap_omap :: OMap M | 0;
    id_finmap_merge :: Merge M | 0;
    id_finmap_fold :: forall C, MapFold A C (M C) | 0;

    (* Properties that we care about. *)
    id_eq_decision :: EqDecision A | 0;
    id_finmap :: FinMap A M | 0
  }.

(** Strings as ids. *)
Module string_id_instance.

  Definition id := string.
  Definition idmap := stringmap.

  #[export]
  Instance is_string : Id id idmap.
  Proof.
    econstructor; try typeclasses eauto.
  Defined.

End string_id_instance.

Module Pair_id_instance.

  Definition id := (string + string)%type.
  Definition idmap := (gmap.gmap (string + string)%type).

  #[export]
  Instance is_string : Id id idmap.
  Proof.
    econstructor; try typeclasses eauto.
  Defined.

End Pair_id_instance.


(* Constructing product identifiers. *)
Section Id_prod.

  (* The type of variables identifiers. *)
  Context {I : Type}.
  Context {M : Type -> Type}.
  Context {id : Id I M}.

  Definition prod_I : Type := I + I.
  Definition prod_M (T : Type) : Type := M T * M T.

  Definition prod_id_finmap_fmap : FMap prod_M :=
    fun A B f M2 => (id_finmap_fmap A B f (fst M2), id_finmap_fmap A B f (snd M2)).

  Definition prod_id_finmap_lookup : ∀ C, Lookup prod_I C (prod_M C) :=
    fun C i M2 => match i with
                  | inl i' => id_finmap_lookup C i' (fst M2)
                  | inr i' => id_finmap_lookup C i' (snd M2)
                  end.

  Definition prod_id_finmap_empty : ∀ C, Empty (prod_M C) :=
    fun C => (id_finmap_empty C , id_finmap_empty C).

  Definition prod_id_finmap_partial_alter : ∀ C, PartialAlter prod_I C (prod_M C) :=
    fun C f i M2 =>
      match i with
      | inl i' => (id_finmap_partial_alter C f i' (fst M2), snd M2)
      | inr i' => (fst M2, id_finmap_partial_alter C f i' (snd M2))
      end.

  Definition prod_id_finmap_omap : OMap prod_M :=
    fun A B f M2 => (id_finmap_omap A B f (fst M2), id_finmap_omap A B f (snd M2)).

  Definition prod_id_finmap_merge : Merge prod_M :=
    fun A B C f MA2 MB2 => (id_finmap_merge A B C f (fst MA2) (fst MB2),
                             id_finmap_merge A B C f (snd MA2) (snd MB2)).

  Definition prod_id_finmap_fold : ∀ C, MapFold prod_I C (prod_M C) :=
    fun C A f a M2 => id_finmap_fold C A (fun i => f (inl i)) a (fst M2).

  Definition prod_id_eq_decision : EqDecision prod_I.
    unfold EqDecision.
    unfold Decision.
    decide equality; apply id_eq_decision.
  Defined.

Definition fin_map_prod : @FinMap prod_I prod_M
                                 prod_id_finmap_fmap
                                 prod_id_finmap_lookup
                                 prod_id_finmap_empty
                                 prod_id_finmap_partial_alter
                                 prod_id_finmap_omap
                                 prod_id_finmap_merge
                                 prod_id_finmap_fold
                                 prod_id_eq_decision.
Proof.
  constructor; simpl.
  - unfold prod_M, prod_I; simpl; intros A [m11 m12] [m21 m22] ?.
    rewrite (map_eq m11 m21), (map_eq m12 m22); auto.
    + intro; specialize (H (inr i)); unfold lookup; eauto.
    + intro; specialize (H (inl i)); unfold lookup; eauto.
Admitted.

#[global]
 Instance id_prod : Id prod_I prod_M :=
  {| id_finmap := fin_map_prod |}.

End Id_prod.
