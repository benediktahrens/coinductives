Require Import Theory.Category.
Require Import Theory.RelativeComonad.
Require Import Theory.Comodule.Core.

Set Implicit Arguments.
Unset Strict Implicit.
Generalizable All Variables.

(*------------------------------------------------------------------------------
  -- ＭＯＲＰＨＩＳＭ
  ----------------------------------------------------------------------------*)

Structure Morphism `{F : Functor 𝒞 𝒟} {T : RelativeComonad F} {ℰ} (M N : Comodule T ℰ) : Type := make
{ α          :> ∀ C, M C ⇒ N C
; α_commutes : ∀ {C D} {f : T C ⇒ F D}, α(D) ∘ M⋅mcobind f ≈ N⋅mcobind f ∘ α(C) }.

(* -- Ｉｄｅｎｔｉｔｙ  /  Ｃｏｍｐｏｓｉｔｉｏｎ                      -- *)
Section id_composition.

  Context `{F : Functor 𝒞 𝒟} {T : RelativeComonad F} {ℰ : Category}.

  Program Definition Hom (M N : Comodule T ℰ) : Setoid :=
    Setoid.make (Morphism M N) (λ f g ∙ ∀ x, f x ≈ g x).
  Next Obligation.
    constructor.
    - intros f x; reflexivity.
    - intros f g eq_fg x. symmetry. apply eq_fg.
    - intros f g h eq_fg eq_gh; etransitivity; eauto.
  Qed.

  Infix "⇛" := Hom (at level 70).

  Program Definition id {M : Comodule T ℰ} : M ⇛ M :=
    make (α := λ C ∙ id[ M C ]) _.
  Next Obligation.
    now rewrite left_id, right_id.
  Qed.

  Program Definition compose {M N P : Comodule T ℰ} : [ N ⇛ P ⟶ M ⇛ N ⟶ M ⇛ P ] :=
    λ g f ↦₂ make (α := λ C ∙ g(C) ∘ f(C)) _.
  Next Obligation.
    rewrite <- compose_assoc; rewrite <- α_commutes.
    rewrite compose_assoc; rewrite α_commutes; rewrite compose_assoc.
    reflexivity.
  Qed.
  Next Obligation.
    intros f₁ f₂ eq_f₁f₂ g₁ g₂ eq_g₁g₂ x. simpl. rewrite eq_f₁f₂, eq_g₁g₂.
    reflexivity.
  Qed.

End id_composition.
