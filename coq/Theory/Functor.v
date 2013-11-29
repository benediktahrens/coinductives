(*----------------------------------------------------------------------------*)
(*    Functor definition                                                      *)
(*----------------------------------------------------------------------------*)

Require Import Theory.Category.

(*
 * Functor structure without laws
 *)
Structure RawFunctor (𝒞 𝒟 : Category) : Type :=
  { Fobj :> 𝒞 → 𝒟
  ; Fhom : ∀ {A B : 𝒞}, A ⇒ B → Fobj A ⇒ Fobj B }.

Arguments Fobj {_} {_} _ _.
Arguments Fhom {_} {_} _ {A B} _.

Notation "F ⋅ f" := (Fhom F f) (at level 35).

(*
 * Functoriality
 *)
Class IsFunctor {𝒞 𝒟} (F : RawFunctor 𝒞 𝒟) : Prop :=
  { identity     : ∀ {X : 𝒞}, id[ F X ] ≈ F⋅id
  ; Fhom_compose : ∀ {A B C : 𝒞} {g : B ⇒ C} {f : A ⇒ B}, F⋅(g ∘ f) ≈ F⋅g ∘ F⋅f
  ; Fhom_cong    :> ∀ {A B : 𝒞}, (@Fhom _ _ F A B) Preserves _≈_ ⟶ _≈_ }.

(*
 * Functor
 *)
Structure Functor (𝒞 𝒟 : Category) : Type :=
  { rawFunctor :> RawFunctor 𝒞 𝒟
  ; isFunctor  : IsFunctor rawFunctor }.

Existing Instance isFunctor.
