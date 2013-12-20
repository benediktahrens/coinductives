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
  -- ＲＥＬＡＴＩＶＥ  ＣＯＭＯＮＡＤ  ＤＥＦＩＮＩＴＩＯＮ  ＷＩＴＨ  ＣＵＴ
  ----------------------------------------------------------------------------*)

Section Defs.

  Context `{BinaryProduct 𝒞} `{BinaryProduct 𝒟}
          (F : Functor 𝒞 𝒟) (E : 𝒞) `{!CartesianStrongMonoidal F}.

  Section ExtendConstruction.

    Context {T : RelativeComonad F}
            (cut : ∀ A, T (E × A) ⇒ T A).

    Program Definition Extend {A B} : [ T A ⇒ F B ⟶ T (E × A) ⇒ F (E × B) ] :=
      λ f ↦ φ⁻¹ ∘ ⟨ F ⋅ π₁ ∘ T⋅counit , f ∘ cut A ⟩.
    Next Obligation.
      intros f g eq_fg. now rewrite eq_fg.
    Qed.

  End ExtendConstruction.

  Structure RelativeComonadWithCut := mkRelativeComonadWithCut
  { Tc  :> RelativeComonad F
  ; cut : ∀ {A}, Tc (E × A) ⇒ Tc A
  ; cut_counit : ∀ A, Tc⋅counit[A] ∘ cut ≈ F ⋅ π₂ ∘ Tc⋅counit
  ; cut_cobind : ∀ A B (f : Tc A ⇒ F B), Tc⋅cobind(f) ∘ cut ≈ cut ∘ Tc⋅cobind (Extend (@cut) f) }.

  Definition extend {T : RelativeComonadWithCut} {A B} : [ T A ⇒ F B ⟶ T (E × A) ⇒ F (E × B) ] :=
    Extend (@cut T).

End Defs.

Notation "'cut[' X ]" := (cut _ (A := X)) (only parsing).
Notation "T '⋅cut'" := (cut T) (at level 0, only parsing).
Notation "T '⋅cut[' X ]" := (cut T (A := X)) (at level 0, only parsing).

Notation make T cut :=
  (mkRelativeComonadWithCut (Tc := T) (cut := cut) _ _) (only parsing).

Arguments RelativeComonadWithCut {_ _ _ _} _ _ {_}.

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
  (*   intros f g eq_fg. now rewrite eq_fg. *)
  (* Qed. *)
  Admitted.
  Next Obligation.
  (*   rewrite cut_counit. rewrite <- ∘-×. rewrite <- compose_assoc. rewrite iso_right. *)
  (*   rewrite left_id. rewrite mcobind_counit. reflexivity. *)
  (* Qed. *)
  Admitted.
  Next Obligation.
  (*   rewrite mcobind_compose. apply Π_cong. repeat rewrite compose_assoc. *)
  (*   rewrite ∘-×. rewrite cut_cobind. unfold Extend. simpl. *)
  (*   repeat rewrite compose_assoc. rewrite counit_cobind. *)
  (*   assert (eq_π₁ : ∀ A B : 𝒞, F ⋅ π₁[A , B] ∘ φ⁻¹ ≈ π₁). *)
  (*   { *)
  (*     intros A B. assert (eq_F : F ⋅ π₁[A , B] ≈ π₁ ∘ φ). unfold φ. now rewrite π₁_compose. *)
  (*     rewrite eq_F. rewrite compose_assoc. rewrite iso_left. now rewrite right_id. *)
  (*   } *)
  (*   repeat rewrite <- compose_assoc. rewrite eq_π₁. rewrite π₁_compose. reflexivity. *)
  (* Qed. *)
  Admitted.

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