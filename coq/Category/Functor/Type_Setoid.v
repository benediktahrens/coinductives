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
Require Import Theory.StrongMonoidal.

Definition 𝑬𝑸_α (A B : 𝑻𝒚𝒑𝒆) : 𝑬𝑸 (A × B) ⇒ 𝑬𝑸 A × 𝑬𝑸 B := ⟨ 𝑬𝑸 ⋅ π₁ , 𝑬𝑸 ⋅ π₂ ⟩.
Program Definition α_𝑬𝑸 (A B : 𝑻𝒚𝒑𝒆) : 𝑬𝑸 A × 𝑬𝑸 B ⇒ 𝑬𝑸 (A × B) :=
  λ x ↦ x.
Next Obligation.
  intros [x x'] [y y'] [eq_xx' eq_yy']; now f_equal.
Qed.

Program Instance 𝑬𝑸_SM : StrongMonoidal 𝑬𝑸_α := {| inv_α := α_𝑬𝑸 |}.
Next Obligation.
  constructor.
  - (* iso_left *)
    intros [x x'] [y y'] [eq_xx' eq_yy']; split; auto.
  - (* iso_right *)
    intros [x x'] [y y']; auto.
Qed.