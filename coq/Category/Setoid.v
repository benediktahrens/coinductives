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


(*------------------------------------------------------------------------------
  -- ＳＥＴＯＩＤＳ  ＨＡＶＥ  ＢＩＮＡＲＹ  ＰＲＯＤＵＣＴ
  ----------------------------------------------------------------------------*)

Require Import Theory.Product.

Section Product_construction.

  Program Definition product (A B : 𝑺𝒆𝒕𝒐𝒊𝒅) : 𝑺𝒆𝒕𝒐𝒊𝒅 :=
    Setoid.make (A ⟨×⟩ B) (λ S₁ S₂ ∙ fst S₁ ≈ fst S₂ ∧ snd S₁ ≈ snd S₂).
  Next Obligation.
    constructor; hnf; simpl.
    - intros [a  b]; split; reflexivity.
    - intros [x y] [x' y'] [eq_xx' eq_yy']; split; now symmetry.
    - intros [x y] [x' y'] [x'' y''] [eq_xx' eq_yy'] [eq_x'x'' eq_y'y''];
      split; etransitivity; eauto.
  Qed.

  Program Definition product_mor (A B C : 𝑺𝒆𝒕𝒐𝒊𝒅) (f : C ⇒ A) (g : C ⇒ B) : C ⇒ product A B :=
    Π.make (λ c ∙ (f c , g c)).
  Next Obligation.
    intros x y eq_xy; simpl; split; now rewrite eq_xy.
  Qed.

  Program Definition proj_l {A B} : product A B ⇒ A := Π.make fst.
  Next Obligation.
    intros x y [eq_fst _]; exact eq_fst.
  Qed.

  Program Definition proj_r {A B} : product A B ⇒ B := Π.make snd.
  Next Obligation.
    intros x y [_ eq_snd]; exact eq_snd.
  Qed.

End Product_construction.


Program Instance 𝑺𝒆𝒕𝒐𝒊𝒅_BinaryProduct : BinaryProduct 𝑺𝒆𝒕𝒐𝒊𝒅 :=
  Product.make 𝑺𝒆𝒕𝒐𝒊𝒅 product (@product_mor _ _) proj_l proj_r.
Next Obligation. (* Pmor_cong₂ *)
  intros f₁ f₂ eq_f₁f₂ g₁ g₂ eq_g₁g₂ x y eq_xy; simpl; split.
  - now apply eq_f₁f₂.
  - now apply eq_g₁g₂.
Qed.
Next Obligation.
  now rewrite H.
Qed.
Next Obligation.
  now rewrite H.
Qed.