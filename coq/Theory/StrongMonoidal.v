Require Import Theory.Category.
Require Import Theory.Product.

Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.

(*------------------------------------------------------------------------------
  -- ＳＴＲＯＮＧ  ＭＯＮＯＩＤＡＬ  ＦＵＮＣＴＯＲ  ＤＥＦＩＮＩＴＩＯＮ
  ----------------------------------------------------------------------------*)

Section StrongMonoidal.

  Context `{BinaryProduct 𝒞} `{BinaryProduct 𝒟} (F : Functor 𝒞 𝒟).

  Definition projection (A B : 𝒞) : F (A × B) ⇒ F A × F B := ⟨ F ⋅ π₁ , F ⋅ π₂ ⟩.

  Class StrongMonoidal :=
  { inv_α : ∀ A B, F A × F B ⇒ F (A × B)
  ; sm_is_inverse :> ∀ A B, IsInverse (projection A B) (inv_α A B) }.

End StrongMonoidal.