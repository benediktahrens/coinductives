Require Import Theory.Category.

Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.

(*------------------------------------------------------------------------------
  -- ＩＮＩＴＩＡＬ  ＯＢＪＥＣＴ
  ----------------------------------------------------------------------------*)

Structure Initial (𝒞 : Category) := mkInitial
{ zero :> 𝒞
; bottom : ∀ {A : 𝒞}, zero ⇒ A
; bottom_unique : ∀ `{f : zero ⇒ A}, f ≈ bottom }.

Notation "⟨⊥⟩"      := zero (only parsing).
Notation "!-⊥"      := bottom (only parsing).
Notation "⊥-unique" := bottom_unique (only parsing).


(*------------------------------------------------------------------------------
  -- ＴＥＲＭＩＮＡＬ  ＯＢＪＥＣＴ
  ----------------------------------------------------------------------------*)
Structure Terminal (𝒞 : Category) := mkTerminal
{ one :> 𝒞
; top : ∀ {A : 𝒞}, A ⇒ one
; top_unique : ∀ `{f : A ⇒ one}, f ≈ top }.

Notation "⟨⊤⟩"      := one (only parsing).
Notation "!-⊤"      := top (only parsing).
Notation "⊤-unique" := top_unique (only parsing).
