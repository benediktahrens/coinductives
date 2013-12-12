Require Import Theory.Category.
Require Import Theory.Product.

Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.

(*------------------------------------------------------------------------------
  -- ＳＴＲＯＮＧ  ＭＯＮＯＩＤＡＬ  ＦＵＮＣＴＯＲ  ＤＥＦＩＮＩＴＩＯＮ
  ----------------------------------------------------------------------------*)

Class StrongMonoidal `{BinaryProduct 𝒞} `{BinaryProduct 𝒟} (F : Functor 𝒞 𝒟)
      (α : ∀ A B, F (A × B) ⇒ F A × F B) :=
{ inv_α : ∀ A B, F A × F B ⇒ F (A × B)
; sm_is_inverse :> ∀ A B, IsInverse (α A B) (inv_α A B) }.