Require Import Theory.Category.
Require Import Theory.RelativeComonad.
Require Import Theory.Product.
Require Import Theory.StrongMonoidal.
Require Import Theory.Comodule.Core.
Require Import Theory.Comodule.Morphism.

Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.

Section ProductInContext.

  Context `{BinaryProduct 𝒞} `{BinaryProduct 𝒟} (ℰ : Category) (F : Functor 𝒞 𝒟) `{!StrongMonoidal F}
           (T : RelativeComonad F) (E : 𝒞).

  Notation α := (projection F _ _).
  Notation "'α[' A , B ]" := (projection F A B).

  Program Definition extend {A B : 𝒞} : [ T A ⇒ F B ⟶ T (E × A) ⇒ F (E × B) ] :=
    λ f ↦ α⁻¹ ∘ (T⋅counit -×- f) ∘ ⟨ Lift(T)⋅(π₁) , Lift(T)⋅(π₂) ⟩.
  Next Obligation.
  Admitted.

  Context (M : Comodule T ℰ).

  Lemma compose_cong : ∀ {𝒞 : Category} {A B C : 𝒞} (h : B ⇒ C) (f g : A ⇒ B),
                           f ≈ g → h ∘ f ≈ h ∘ g.
  Proof.
    intros. now rewrite H1.
  Qed.

  Lemma prod_compose : ∀ `{BinaryProduct 𝒞} (A A' B B' C C' : 𝒞)
                        (g : B ⇒ C) (f : A ⇒ B) (g' : B' ⇒ C') (f' : A' ⇒ B'),
                        (g ∘ f) -×- (g' ∘ f') ≈ (g -×- g') ∘ (f -×- f').
  Proof.
    intros. simpl. unfold prod_mor. rewrite <- ∘-×. repeat rewrite compose_assoc.
    now rewrite π₁_compose, π₂_compose.
  Qed.

  Lemma prod_compose_left_id : ∀ `{BinaryProduct 𝒞} (A A' B B' C C' : 𝒞)
                        (g : B ⇒ C) (g' : B' ⇒ C') (f' : A' ⇒ B'),
                        g -×- (g' ∘ f') ≈ (g -×- g') ∘ (id[ B ] -×- f').
  Proof.
    intros. rewrite <- prod_compose. now rewrite right_id.
  Qed.

  Lemma prod_compose_right_id : ∀ `{BinaryProduct 𝒞} (A A' B B' C C' : 𝒞)
                        (g : B ⇒ C) (g' : B' ⇒ C') (f' : A' ⇒ B'),
                        g -×- (g' ∘ f') ≈ (id[C] -×- g') ∘ (g -×- f').
  Proof.
    intros. rewrite <- prod_compose. now rewrite left_id.
  Qed.

  Lemma extend_compose (A B C : 𝒞) (f : T B ⇒ F C) (g : T A ⇒ F B) :
    extend f ∘ T⋅cobind(extend g) ≈ extend (f ∘ T⋅cobind g) :> T (E × A) ⇒ F (E × C).
  Proof.
    simpl. repeat rewrite compose_assoc.
    rewrite <- ∘-×. apply compose_cong.
    repeat rewrite cobind_compose.
    repeat rewrite compose_assoc.
    rewrite counit_cobind.
    set (H := prod_compose_left_id (T⋅counit) f (
    rewrite prod_compose_left_id.


  Program Definition ProductInContext : Comodule T ℰ :=
    Core.make (mcobind := λ A B ∙ λ f ↦ M⋅mcobind (extend f)) _ _.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
    rename C into A. rename D into B. rename E0 into C.
    rewrite mcobind_compose.
    apply proper_prf.
    f_equiv.


  