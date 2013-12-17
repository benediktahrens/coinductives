Require Import Theory.Category.
Require Import Theory.Functor.
Require Import Theory.Isomorphism.
Require Import Theory.RelativeComonad.
Require Import Theory.Comodule.
Require Import Theory.Product.
Require Import Theory.StrongMonoidal.

Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.

(*------------------------------------------------------------------------------
  -- ＥＸＴＥＮＤ  ＣＯＮＳＴＲＵＣＴＩＯＮ
  ----------------------------------------------------------------------------*)

Section ExtendConstruction.

  Context `{BinaryProduct 𝒞} `{BinaryProduct 𝒟} (F : Functor 𝒞  𝒟)
          {T : RelativeComonad F} {E : 𝒞} `{!CartesianStrongMonoidal F}.

  Program Definition extend {A B : 𝒞} : [ T A ⇒ F B ⟶ T(E × A) ⇒ F(E × B) ] :=
    λ f ↦ φ⁻¹ ∘ ⟨ F ⋅ π₁ ∘ T⋅counit , f ∘ (Lift(T) ⋅ π₂) ⟩.
  Next Obligation.
  (*   intros f g eq_fg. now rewrite eq_fg. *)
  (* Qed. *)
  Admitted.

End ExtendConstruction.


(*------------------------------------------------------------------------------
  -- ＰＲＯＤＵＣＴ  ＩＮ  ＣＯＮＴＥＸＴ
  ----------------------------------------------------------------------------*)

Section ProductInContext.

  Context `{BinaryProduct 𝒞} `{BinaryProduct 𝒟} (F : Functor 𝒞  𝒟)
          (T : RelativeComonad F) (E : 𝒞) `{!CartesianStrongMonoidal F}
          (ℰ : Category) (M : Comodule T ℰ).

  Program Definition product_in_context : Comodule T ℰ :=
    Comodule.make (λ C ∙ M (E × C)) ( λ A B ∙ λ f ↦ M⋅mcobind (extend(f))).
  Next Obligation.
  (*   intros f g eq_fg. now rewrite eq_fg. *)
  (* Qed. *)
  Admitted.
  Next Obligation.
  (*   rewrite counit_cobind. rewrite <- ∘-×. rewrite <- compose_assoc. *)
  (*   rewrite iso_right. rewrite left_id. now rewrite mcobind_counit. *)
  (* Qed. *)
  Admitted.
  Next Obligation.
  (*   rewrite mcobind_compose. repeat rewrite compose_assoc. *)
  (*   rewrite ∘-×. *)
  (*   repeat rewrite compose_assoc. *)
  (*   rewrite counit_cobind. *)
  (*   rewrite cobind_compose. *)
  (*   repeat rewrite compose_assoc. *)
  (*   rewrite counit_cobind. *)
  (*   repeat rewrite <- compose_assoc. *)
  (*   assert (eq_π₁ : ∀ A B : 𝒞, F ⋅ π₁[A , B] ∘ φ⁻¹ ≈ π₁). *)
  (*   { *)
  (*     intros A B. assert (eq_F : F ⋅ π₁[A , B] ≈ π₁ ∘ φ). unfold φ. now rewrite π₁_compose. *)
  (*     rewrite eq_F. rewrite compose_assoc. rewrite iso_left. now rewrite right_id. *)
  (*   } *)
  (*   assert (eq_π₂ : ∀ A B : 𝒞, F ⋅ π₂[A , B] ∘ φ⁻¹ ≈ π₂). *)
  (*   { *)
  (*     intros A B. assert (eq_F : F ⋅ π₂[A , B] ≈ π₂ ∘ φ). unfold φ. now rewrite π₂_compose. *)
  (*     rewrite eq_F. rewrite compose_assoc. rewrite iso_left. now rewrite right_id. *)
  (*   } *)
  (*   rewrite eq_π₁, eq_π₂. *)
  (*   rewrite π₁_compose, π₂_compose. rewrite compose_assoc. now rewrite cobind_compose. *)
  (* Qed. *)
  Admitted.

End ProductInContext.

Require Import Category.RComod.

Section Morphisms.

  Context `{BinaryProduct 𝒞} `{BinaryProduct 𝒟} (F : Functor 𝒞  𝒟)
          (T : RelativeComonad F) (E : 𝒞) `{!CartesianStrongMonoidal F}
          (ℰ : Category) (M : Comodule T ℰ) (N : Comodule T ℰ) (α : M ⇒ N).

  Program Definition product_in_context_mor : product_in_context E M ⇒ product_in_context E N :=
    Comodule.Morphism.make (λ A ∙ α (E × A)).
  Next Obligation.
    now rewrite α_commutes.
  Qed.

End Morphisms.