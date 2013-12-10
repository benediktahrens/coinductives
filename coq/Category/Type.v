Require Import Theory.Category.
Require Import Theory.SetoidType.

Set Implicit Arguments.
Unset Strict Implicit.

(*------------------------------------------------------------------------------
  -- ＣＡＴＥＧＯＲＹ  ＯＦ  ＴＹＰＥＳ
  ----------------------------------------------------------------------------*)

Definition Obj := Type.

Program Definition Hom (A B : Obj) : Setoid := Setoid.make (A → B) (λ f g ∙ ∀ x, f x = g x).
Next Obligation.
  constructor; hnf; simpl; [ reflexivity | now symmetry | etransitivity ; eauto ].
Qed.

Local Infix "⇛" := Hom (at level 30, right associativity).

Definition id {A} : A ⇛ A := λ x ∙ x.

Program Definition compose {A B C} : [ B ⇛ C ⟶ A ⇛ B ⟶ A ⇛ C ] :=
  Π₂.make (λ g f x ∙ g (f x)).
Next Obligation.
  intros f₁ f₂ eq_f₁f₂ g₁ g₂ eq_g₁g₂ x.
  now rewrite eq_f₁f₂, eq_g₁g₂.
Qed.

Local Infix "⟨∘⟩" := compose (at level 40, left associativity).

Lemma left_id A B (f : A ⇛ B) : id ⟨∘⟩ f ≈ f.
Proof.
  hnf ; intuition.
Qed.

Lemma right_id A B (f : A ⇛ B) : f ⟨∘⟩ id ≈ f.
Proof.
  hnf ; intuition.
Qed.

Lemma compose_assoc A B C D (f : A ⇛ B) (g : B ⇛ C) (h : C ⇛ D) : h ⟨∘⟩ g ⟨∘⟩ f ≈ h ⟨∘⟩ (g ⟨∘⟩ f).
Proof.
  hnf ; intuition.
Qed.

Definition 𝑻𝒚𝒑𝒆 : Category :=
  mkCategory left_id right_id compose_assoc.