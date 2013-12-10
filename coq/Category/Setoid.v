Require Import Theory.Category.
Require Import Theory.SetoidType.

Set Implicit Arguments.
Unset Strict Implicit.

(*------------------------------------------------------------------------------
  -- ＣＡＴＥＧＯＲＹ  ＯＦ  ＳＥＴＯＩＤＳ
  ----------------------------------------------------------------------------*)

Definition Obj := Setoid.

Program Definition Hom (A B : Obj) : Setoid := Π.setoid A B.

Local Infix "⇛" := Hom (at level 30, right associativity).

Definition id {A} : A ⇛ A := Π.id.

Program Definition compose {A B C} : [ B ⇛ C ⟶ A ⇛ B ⟶ A ⇛ C ] :=
  Π₂.make (λ g f ∙ Π.compose g f).
Next Obligation.
  intros f₁ f₂ eq_f₁f₂ g₁ g₂ eq_g₁g₂ x y eq_xy.
  simpl. rewrite eq_xy. apply eq_f₁f₂. apply eq_g₁g₂. reflexivity.
Qed.

Local Infix "⟨∘⟩" := compose (at level 40, left associativity).

Lemma left_id A B (f : A ⇛ B) : id ⟨∘⟩ f ≈ f.
Proof.
  intros x y eq_xy; now rewrite eq_xy.
Qed.

Lemma right_id A B (f : A ⇛ B) : f ⟨∘⟩ id ≈ f.
Proof.
  intros x y eq_xy; now rewrite eq_xy.
Qed.

Lemma compose_assoc A B C D (f : A ⇛ B) (g : B ⇛ C) (h : C ⇛ D) : h ⟨∘⟩ g ⟨∘⟩ f ≈ h ⟨∘⟩ (g ⟨∘⟩ f).
Proof.
  intros x y eq_xy; now rewrite eq_xy.
Qed.

Definition 𝑺𝒆𝒕𝒐𝒊𝒅 : Category :=
  mkCategory left_id right_id compose_assoc.