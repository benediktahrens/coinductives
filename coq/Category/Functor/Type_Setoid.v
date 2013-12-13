Require Import Theory.Category.
Require Import Category.Type.
Require Import Category.Setoid.

Set Implicit Arguments.
Unset Strict Implicit.

(*------------------------------------------------------------------------------
  -- ＦＵＮＣＴＯＲ  ＥＱ
  ----------------------------------------------------------------------------*)

Definition F : 𝑻𝒚𝒑𝒆 → 𝑺𝒆𝒕𝒐𝒊𝒅 := Setoid.eq_setoid.

Program Definition map {A B} : [ A ⇒ B ⟶ F A ⇒ F B ] :=
  λ f ↦ Π.make f.
Next Obligation.
  idtac.
  intros x y eq_xy. rewrite eq_xy.
  reflexivity.
Qed.
Next Obligation.
  intros f g eq_fg x y eq_xy. simpl. rewrite eq_xy. apply eq_fg.
Qed.

Definition identity A : id[ F A ] ≈ map id[ A ].
Proof.
  intros x y eq_xy. now rewrite eq_xy.
Qed.

Definition map_compose A B C (f : A ⇒ B) (g : B ⇒ C) : map (g ∘ f) ≈ (map g) ∘ (map f).
Proof.
  intros x y eq_xy. now rewrite eq_xy.
Qed.

Definition 𝑬𝑸 : Functor 𝑻𝒚𝒑𝒆 𝑺𝒆𝒕𝒐𝒊𝒅 := mkFunctor identity map_compose.

(*------------------------------------------------------------------------------
  -- ＥＱ  ＩＳ  ＳＴＲＯＮＧ  ＭＯＮＯＩＤＡＬ
  ----------------------------------------------------------------------------*)

Require Import Theory.Product.
Require Import Theory.Morphism.
Require Import Theory.StrongMonoidal.

Program Instance 𝑬𝑸_SM : StrongMonoidal 𝑬𝑸 :=
  λ (A B : 𝑻𝒚𝒑𝒆) ∙ Iso.make ⟨ 𝑬𝑸 ⋅ π₁ , 𝑬𝑸 ⋅ π₂ ⟩ (λ x ↦ x).
Next Obligation. (* id_cong *)
  intros [x x'] [y y'] [eq_xx' eq_yy']; now f_equal.
Qed.
