Require Import Theory.Category.
Require Import Theory.Isomorphism.
Require Import Theory.Functor.
Require Import Theory.Product.

Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.

(*------------------------------------------------------------------------------
  -- ＳＴＲＯＮＧ  ＭＯＮＯＩＤＡＬ  ＦＵＮＣＴＯＲ  ＤＥＦＩＮＩＴＩＯＮ
  ----------------------------------------------------------------------------*)

(** ¡¡ Very 'direct' definition !! **)
Class StrongMonoidal `{BinaryProduct 𝒞} `{BinaryProduct 𝒟} (F : Functor 𝒞 𝒟) :=
  strong_monoidal : ∀ {A B : 𝒞}, F (A × B) ≅ F A × F B.

Notation "F -×" := (strong_monoidal (F0 := F)) (at level 0, only parsing).