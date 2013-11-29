(*----------------------------------------------------------------------------*)
(*    Relative Comonad definition                                             *)
(*----------------------------------------------------------------------------*)

Require Import Theory.Category.
Require Import Theory.Functor.

Generalizable All Variables.

(*
 * Relative Comonad without laws
 *)
Structure RawRelativeComonad `(F : RawFunctor 𝒞 𝒟) : Type :=
  { T      :> 𝒞 → 𝒟
  ; counit : ∀ {X : 𝒞}, T X ⇒ F X
  ; cobind : ∀ {X Y : 𝒞}, T X ⇒ F Y → T X ⇒ T Y }.

Arguments counit {_} {_} {_} {_} {X}.
Arguments cobind {_} {_} {_} {_} {X Y} _.

Notation "'counit[' X ]" := (@counit _ _ _ _ X) (only parsing).

(*
 * Relative Comonad laws
 *)
Class IsRelativeComonad `{F : RawFunctor 𝒞 𝒟} (T : RawRelativeComonad F) : Prop :=
  { cobind_counit   : ∀ {X : 𝒞}, cobind (counit[ X ]) ≈ id[ T X ]
  ; counit_cobind   : ∀ {X Y : 𝒞} {f : T X ⇒ F Y}, counit ∘ cobind(f) ≈ f
  ; cobind_compose  : ∀ {X Y Z : 𝒞} {f : T X ⇒ F Y} {g : T Y ⇒ F Z}, cobind(g) ∘ cobind(f) ≈ cobind(g ∘ cobind(f))
  ; cobind_cong     :> ∀ {X Y : 𝒞}, (cobind (r := T) (X := X) (Y := Y)) Preserves _≈_ ⟶ _≈_ }.

(*
 * Relative Comonad
 *)
Structure RelativeComonad `(F : Functor 𝒞 𝒟) : Type :=
  { rawRelativeComonad :> RawRelativeComonad F
  ; isRelativeComonad  : IsRelativeComonad rawRelativeComonad }.

Existing Instance isRelativeComonad.
