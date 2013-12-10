Require Import Theory.Category.
Require Import Functor.

Set Implicit Arguments.
Unset Strict Implicit.

(*------------------------------------------------------------------------------
  -- ＣＡＴＥＧＯＲＹ  ＯＦ  ＳＭＡＬＬ  ＣＡＴＥＧＯＲＩＥＳ
  ----------------------------------------------------------------------------*)

Import Functor.Morphism.

Definition Obj := Category.

Local Infix "⟨∘⟩" := compose (at level 40, left associativity).

Lemma left_id 𝒞 𝒟 (F : 𝒞 ⇛ 𝒟) : id ⟨∘⟩ F ≈ F.
Proof.
  hnf. intros A B f.
  simpl. apply Heq_refl.
Qed.

Lemma right_id A B (f : A ⇛ B) : f ⟨∘⟩ id ≈ f.
Proof.
  hnf; simpl; intros.
  apply Heq_refl.
Qed.

Lemma compose_assoc A B C D (f : A ⇛ B) (g : B ⇛ C) (h : C ⇛ D) : h ⟨∘⟩ g ⟨∘⟩ f ≈ h ⟨∘⟩ (g ⟨∘⟩ f).
Proof.
  hnf; simpl; intros.
  apply Heq_refl.
Qed.

Definition 𝑪𝒂𝒕 : Category :=
  Category.make left_id right_id compose_assoc.

