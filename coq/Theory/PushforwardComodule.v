Require Import Category.RComonad.
Require Import Category.RComod.
Require Import Category.RComonadWithCut.
Require Import Theory.Functor.
Require Import Theory.RelativeComonad.
Require Import Theory.Comodule.
Require Import Category.
Require Import Theory.Product.
Require Import Theory.StrongMonoidal.
Require Import Theory.ProductInContext.
Require Import Theory.Isomorphism.

Set Implicit Arguments.
Unset Strict Implicit.
Generalizable All Variables.

(*------------------------------------------------------------------------------
  -- ＰＵＳＨＦＯＲＷＡＲＤ  ＣＯＭＯＤＵＬＥ
  ----------------------------------------------------------------------------*)

Section Pushforward_construction.

  Import RelativeComonad.Morphism.

  Variables (𝒞 𝒟 ℰ: Category) (F : Functor 𝒞 𝒟)
            (T S : RelativeComonad F) (τ : T ⇒ S)
            (M : Comodule T ℰ).

  Program Definition pushforward : Comodule S ℰ :=
    Comodule.make M (λ C D ∙ λ f ↦ M⋅mcobind (f ∘ τ(C))).
  Next Obligation. (* mcobind_cong *)
    solve_proper.
  Qed.
  Next Obligation. (* mcobind_counit *)
    rewrite <- τ_counit. now rewrite mcobind_counit.
  Qed.
  Next Obligation. (* mcobind_compose *)
    now rewrite compose_assoc,
                <- τ_commutes,
                mcobind_compose,
                <- compose_assoc.
  Qed.

End Pushforward_construction.

(*------------------------------------------------------------------------------
  -- ＰＵＳＨＦＯＲＷＡＲＤ  ＩＳ  ＦＵNＣＴＯＲＩＡＬ
  ----------------------------------------------------------------------------*)

Section Pushforward_functorial.

  Import RelativeComonad.Morphism.

  Variables (𝒞 𝒟 ℰ: Category) (F : Functor 𝒞 𝒟)
            (T S : RelativeComonad F) (τ :S ⇒ T).

  Import Comodule.Morphism.

  Variables (M N : Comodule S ℰ) (α : M ⇒ N).

  Infix "*" := pushforward.

  Program Definition pushforwardm : (τ*M) ⇒ (τ*N) :=
    Comodule.Morphism.make α.
  Next Obligation. (* α_commutes *)
    now rewrite α_commutes.
  Qed.

End Pushforward_functorial.

Section tautological_comodule.

  Variables (𝒞 𝒟 : Category) (F : Functor 𝒞 𝒟)
            (T : RelativeComonad F).

  Program Canonical Structure tcomod : Comodule T 𝒟 :=
    Comodule.make T (@cobind _ _ _ T).
  Next Obligation. (* mcobind_counit *)
    now rewrite cobind_counit.
  Qed.
  Next Obligation. (* mcobind_compose *)
    now rewrite cobind_compose.
  Qed.

End tautological_comodule.

Section induced_morphism.

  Import RelativeComonad.Morphism.

  Variables (𝒞 𝒟 : Category) (F : Functor 𝒞 𝒟)
            (T S : RelativeComonad F) (τ : T ⇒ S).

  Infix "*" := pushforward.

  Program Definition induced_morphism : (τ * (tcomod T)) ⇒ (tcomod S) :=
    Comodule.Morphism.make (λ C ∙ τ(C)).
  Next Obligation. (* α_commutes *)
    now rewrite τ_commutes.
  Qed.

End induced_morphism.

Require Import Theory.RelativeComonadWithCut.

Section Commutes.

  Context `{BinaryProduct 𝒞} `{BinaryProduct 𝒟} (F : Functor 𝒞 𝒟)
          (E : 𝒞) `{!CartesianStrongMonoidal F} (T S : RelativeComonadWithCut F E)
          (ℰ : Category) (M : Comodule T ℰ) (τ : T ⇒ S).

    Let ME := pushforward (rcm τ) (product_in_context E M).
    Let ME' := product_in_context E (pushforward (rcm τ) M).

    Program Definition pushf_prodctx: ME ⇒ ME' :=
      Comodule.Morphism.make (λ X ∙ id[M (E × X)]).
    Next Obligation.
      rewrite left_id, right_id.
      apply Π_cong.
      repeat rewrite compose_assoc.
      apply Π_cong₂.
      reflexivity.
      rewrite ∘-×.
      apply Π_cong₂.
      rewrite compose_assoc.
      apply Π_cong₂; [reflexivity|].
      apply τ_counit.
      rewrite compose_assoc.
      apply Π_cong₂; [reflexivity|].
      now rewrite τ_cut.
    Qed.

End Commutes.
