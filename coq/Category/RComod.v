Require Import Theory.Category.
Require Import Theory.RelativeComonad.
Require Import Theory.Comodule.Core.
Require Import Theory.Comodule.Morphism.

Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.

(*------------------------------------------------------------------------------
  -- ＣＡＴＥＧＯＲＹ  ＯＦ  ＣＯＭＯＤＵＬＥＳ
  ----------------------------------------------------------------------------*)

Section Definitions.

  Context `{F : Functor 𝒞 𝒟} (T : RelativeComonad F) (ℰ : Category).

  Implicit Types (A B C D : Comodule T ℰ).

  Import Comodule.Morphism.

  Infix "⇛" := Hom (at level 70).
  Infix "⟨∘⟩" := compose (at level 40, left associativity).

  Lemma cm_left_id A B  (f : A ⇛ B) : id ⟨∘⟩ f ≈ f.
  Proof.
    intro x; simpl. rewrite left_id. reflexivity.
  Qed.

  Lemma cm_right_id A B (f : A ⇛ B) : f ⟨∘⟩ id ≈ f.
  Proof.
    intro x; simpl. now rewrite right_id.
  Qed.

  Lemma cm_compose_assoc A B C D (f : A ⇛ B) (g : B ⇛ C) (h : C ⇛ D) : h ⟨∘⟩ g ⟨∘⟩ f ≈ h ⟨∘⟩ (g ⟨∘⟩ f).
  Proof.
    intro x; simpl. now rewrite compose_assoc.
  Qed.

  Definition 𝑹𝑪𝒐𝒎𝒐𝒅 : Category :=
    mkCategory cm_left_id cm_right_id cm_compose_assoc.

End Definitions.
