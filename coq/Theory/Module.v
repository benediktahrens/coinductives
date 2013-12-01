(*----------------------------------------------------------------------------*)
(*    Module definition                                                       *)
(*----------------------------------------------------------------------------*)

Require Import Theory.Category.
Require Import Theory.Functor.
Require Import Theory.RelativeComonad.

Generalizable All Variables.

(*
 * Module over a Relative Comonad without laws
 *)
Structure RawModuleRC `{F : RawFunctor 𝒞 𝒟} (T : RawRelativeComonad F) (ℰ : RawCategory) : Type :=
  { M       :> 𝒞 → ℰ
  ; mcobind : ∀ {C D : 𝒞}, T C ⇒ F D → M C ⇒ M D }.

Arguments mcobind {_} {_} {_} {_} {_} {_} {C D} _.

(*
 * Module over a Relative Comonad laws
 *)
Class IsModuleRC `{F : RawFunctor 𝒞 𝒟} {T : RawRelativeComonad F} {ℰ} (M : RawModuleRC T ℰ) : Prop :=
  { mcobind_counit  : ∀ {C : 𝒞}, mcobind (counit[ C ]) ≈ᶜ id[ M C ]
  ; mcobind_compose : ∀ {C D E : 𝒞} {f : T C ⇒ F D} {g : T D ⇒ F E},
                        mcobind(g) ∘ mcobind(f) ≈ᶜ mcobind(g ∘ cobind(f)) :> ℰ [ M C , M E ]
  ; mcobind_cong    :> ∀ {C D : 𝒞}, (mcobind (r := M) (C := C) (D := D)) Preserves _≈ᶜ_ ⟶ _≈ᶜ_ }.

(*
 * Module over Relative Comonad
 *)
Structure ModuleRC `{F : Functor 𝒞 𝒟} (T : RelativeComonad F) (ℰ : Category) : Type :=
  { rawModuleRC :> RawModuleRC T ℰ
  ; isModuleRC  : IsModuleRC rawModuleRC }.

Existing Instance isModuleRC.
