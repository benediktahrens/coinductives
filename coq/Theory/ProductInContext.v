Require Import Theory.Category.
Require Import Theory.Functor.
Require Import Theory.Isomorphism.
Require Import Theory.RelativeComonad.
Require Import Theory.RelativeComonadWithCut.
Require Import Theory.Comodule.
Require Import Theory.Product.
Require Import Theory.StrongMonoidal.

Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.

(*------------------------------------------------------------------------------
  -- ＲＥＬＡＴＩＶＥ  ＣＯＭＯＮＡＤ  ＤＥＦＩＮＩＴＩＯＮ  ＷＩＴＨ  ＣＵＴ
  ----------------------------------------------------------------------------*)

(*------------------------------------------------------------------------------
  -- ＰＲＯＤＵＣＴ  ＩＮ  ＣＯＮＴＥＸＴ
  ----------------------------------------------------------------------------*)

Section ProductInContext.

  Context `{BinaryProduct 𝒞} `{BinaryProduct 𝒟} (F : Functor 𝒞  𝒟)
          (E : 𝒞) `{!CartesianStrongMonoidal F} (T : RelativeComonadWithCut F E)
          (ℰ : Category) (M : Comodule T ℰ).

  Program Definition product_in_context : Comodule T ℰ :=
    Comodule.make (λ C ∙ M (E × C)) ( λ A B ∙ λ f ↦ M⋅mcobind (extend(f))).
  Next Obligation.
    intros f g eq_fg. now rewrite eq_fg.
  Qed.
  Next Obligation.
    rewrite cut_counit. rewrite <- ∘-×. rewrite <- compose_assoc. rewrite iso_right.
    rewrite left_id. rewrite mcobind_counit. reflexivity.
  Qed.
  Next Obligation.
    rewrite mcobind_compose. apply Π_cong. repeat rewrite compose_assoc.
    rewrite ∘-×. rewrite cut_cobind. unfold Extend. simpl.
    repeat rewrite compose_assoc. rewrite counit_cobind.
    assert (eq_π₁ : ∀ A B : 𝒞, F ⋅ π₁[A , B] ∘ φ⁻¹ ≈ π₁).
    {
      intros A B. assert (eq_F : F ⋅ π₁[A , B] ≈ π₁ ∘ φ). unfold φ. now rewrite π₁_compose.
      rewrite eq_F. rewrite compose_assoc. rewrite iso_left. now rewrite right_id.
    }
    repeat rewrite <- compose_assoc. rewrite eq_π₁. rewrite π₁_compose. reflexivity.
  Qed.

End ProductInContext.

Arguments product_in_context {_ _ _ _ _} _ {_ _ _} _.

Require Import Category.RComod.

Section Morphisms.

  Context `{BinaryProduct 𝒞} `{BinaryProduct 𝒟} (F : Functor 𝒞  𝒟)
          (E : 𝒞) `{!CartesianStrongMonoidal F} (T : RelativeComonadWithCut F E)
          (ℰ : Category) (M : Comodule T ℰ) (N : Comodule T ℰ) (α : M ⇒ N).

  Program Definition product_in_context_mor : product_in_context E M ⇒ product_in_context E N :=
    Comodule.Morphism.make (λ A ∙ α (E × A)).
  Next Obligation.
    now rewrite α_commutes.
  Qed.

End Morphisms.