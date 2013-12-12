(*----------------------------------------------------------------------------*)
(*    Category of Relative Comonads                                           *)
(*----------------------------------------------------------------------------*)

Require Import Theory.Category.
Require Import Theory.RelativeComonad.Core.
Require Import Theory.RelativeComonad.Morphism.

Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.

(*------------------------------------------------------------------------------
  -- ＣＡＴＥＧＯＲＹ  ＯＦ  ＣＯＭＯＤＵＬＥＳ
  ----------------------------------------------------------------------------*)

Section Definitions.

  Context `(F : Functor 𝒞 𝒟).

  Implicit Types (A B C D : RelativeComonad F).

  Import Morphism.

  Infix "⇛" := Hom (at level 70).
  Infix "⟨∘⟩" := compose (at level 40, left associativity).

  Lemma rc_left_id A B  (f : A ⇛ B) : id ⟨∘⟩ f ≈ f.
  Proof.
    intro x; simpl. rewrite left_id. reflexivity.
  Qed.

  Lemma rc_right_id A B (f : A ⇛ B) : f ⟨∘⟩ id ≈ f.
  Proof.
    intro x; simpl. now rewrite right_id.
  Qed.

  Lemma rc_compose_assoc A B C D (f : A ⇛ B) (g : B ⇛ C) (h : C ⇛ D) : h ⟨∘⟩ g ⟨∘⟩ f ≈ h ⟨∘⟩ (g ⟨∘⟩ f).
  Proof.
    intro x; simpl. now rewrite compose_assoc.
  Qed.

  Definition 𝑹𝑪𝒐𝒎𝒐𝒏𝒂𝒅 : Category :=
    mkCategory rc_left_id rc_right_id rc_compose_assoc.

End Definitions.
