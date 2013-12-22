Require Import Theory.Category.
Require Import Theory.Functor.
Require Import Theory.RelativeComonadWithCut.
Require Import Theory.Product.
Require Import Theory.StrongMonoidal.

Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.

(*------------------------------------------------------------------------------
  -- ＣＡＴＥＧＯＲＹ  ＯＦ  ＲＥＬＡＴＩＶＥ  ＣＯＭＯＮＡＤＳ  ＷＩＴＨ  ＣＵＴ
  ----------------------------------------------------------------------------*)

Section Definitions.

  Context `{BinaryProduct 𝒞} `{BinaryProduct 𝒟}
          (F : Functor 𝒞 𝒟) (E : 𝒞) `{!CartesianStrongMonoidal F}.

  Implicit Types (A B C D : RelativeComonadWithCut F E).

  Import Morphism.

  Infix "⇛" := Hom (at level 70).
  Infix "⟨∘⟩" := compose (at level 40, left associativity).

  Lemma left_id A B  (f : A ⇛ B) : id ⟨∘⟩ f ≈ f.
  Proof.
    intro x; simpl. rewrite left_id. reflexivity.
  Qed.

  Lemma right_id A B (f : A ⇛ B) : f ⟨∘⟩ id ≈ f.
  Proof.
    intro x; simpl. now rewrite right_id.
  Qed.

  Lemma compose_assoc A B C D (f : A ⇛ B) (g : B ⇛ C) (h : C ⇛ D) : h ⟨∘⟩ g ⟨∘⟩ f ≈ h ⟨∘⟩ (g ⟨∘⟩ f).
  Proof.
    intro x; simpl. now rewrite compose_assoc.
  Qed.

  Canonical Structure 𝑹𝑪𝒐𝒎𝒐𝒏𝒂𝒅𝑾𝒊𝒕𝒉𝑪𝒖𝑡 : Category :=
    mkCategory left_id right_id compose_assoc.

End Definitions.