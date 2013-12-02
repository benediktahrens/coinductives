(*----------------------------------------------------------------------------*)
(*    Functor definition                                                      *)
(*----------------------------------------------------------------------------*)

Require Import Theory.Category.

Generalizable All Variables.

(*
 * Functor structure without laws
 *)
Structure functor (𝒞 𝒟 : category) : Type :=
  { Fobj :> 𝒞 → 𝒟
  ; Fhom : ∀ {A B : 𝒞}, A ⇒ B → Fobj A ⇒ Fobj B }.

Arguments Fobj {_} {_} _ _.
Arguments Fhom {_} {_} {_} {A B} _.

(*----------------------------------------------------------------------------*)

(*
 * Overloaded operator [Fhom] for functors
 *)

Class FMap {𝒞 𝒟 : category} (F : 𝒞 → 𝒟) :=
  fmap : ∀ {A B : 𝒞}, A ⇒ B → F A ⇒ F B.

Notation "F ⋅ f" := (fmap (F := F) f) (at level 35).

Instance: ∀ `(F : functor 𝒞 𝒟), FMap F := { fmap := λ A B ∙ Fhom (A := A) (B := B) }.

(*----------------------------------------------------------------------------*)

(*
 * Functoriality
 *)
Class IsFunctor {𝒞 𝒟} (F : functor 𝒞 𝒟) : Prop :=
  { identity     : ∀ {X : 𝒞}, id[ F X ] ≈ᶜ F⋅id
  ; Fhom_compose : ∀ {A B C : 𝒞} {g : B ⇒ C} {f : A ⇒ B}, F⋅(g ∘ f) ≈ᶜ F⋅g ∘ F⋅f
  ; Fhom_cong    :> ∀ {A B : 𝒞}, (@Fhom _ _ F A B) Preserves _≈ᶜ_ ⟶ _≈ᶜ_ }.

(*
 * Functor
 *)
Structure Functor (𝒞 𝒟 : Category) : Type :=
  { _functor :> functor 𝒞 𝒟
  ; isFunctor  : IsFunctor _functor }.

Existing Instance isFunctor.

Instance: Morphism category := functor.
Instance: Morphism Category := Functor.