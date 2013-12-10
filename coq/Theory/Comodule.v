Require Import Theory.Category.
Require Import Theory.Functor.
Require Import Theory.RelativeComonad.
Require Import Theory.SetoidType.

Set Implicit Arguments.
Unset Strict Implicit.
Generalizable All Variables.

(*------------------------------------------------------------------------------
  -- ＣＯＭＯＤＵＬＥ  ＯＶＥＲ  ＲＥＬＡＴＩＶＥ  ＣＯＭＯＮＡＤＥ  ＤＥＦＩＮＩＴＩＯＮ
  ----------------------------------------------------------------------------*)

Structure Comodule `{F : Functor 𝒞 𝒟} (T : RelativeComonad F) (ℰ : Category) : Type := make
{ M               :> 𝒞 → ℰ
; mcobind         : ∀ {C D}, [ T C ⇒ F D ⟶ M C ⇒ M D ]
; mcobind_counit  : ∀ {C}, mcobind counit[ C ] ≈ id[ M C ]
; mcobind_compose : ∀ {C D E} {f : T C ⇒ F D} {g : T D ⇒ F E},
                      mcobind(g) ∘ mcobind(f) ≈ mcobind(g ∘ T⋅cobind(f)) }.

Notation "M '⋅mcobind'" := (mcobind M) (at level 0, only parsing).


(*------------------------------------------------------------------------------
  -- ＦＵＮＣＴＯＲ
  ----------------------------------------------------------------------------*)

Section Functor.

  Context `{F : Functor 𝒞 𝒟} {T : RelativeComonad F} {ℰ} (M : Comodule T ℰ).

  Program Definition mlift {A B} : [ A ⇒ B ⟶ M A ⇒ M B ] :=
    Π.make (λ f ∙ M⋅mcobind (F⋅f ∘ counit[ A ])).
  Next Obligation.
    intros x y eq_xy. now rewrite eq_xy.
  Qed.

  Lemma mlift_id A : id[ M A ] ≈ mlift id[ A ].
  Proof.
    simpl. rewrite <- identity, left_id, mcobind_counit.
    reflexivity.
  Qed.

  Lemma mlift_compose A B C (f : A ⇒ B) (g : B ⇒ C) : mlift (g ∘ f) ≈ (mlift g) ∘ (mlift f).
  Proof.
    simpl.
    rewrite mcobind_compose,
            compose_assoc,
            counit_cobind,
            <- compose_assoc,
            <- map_compose.
    reflexivity.
  Qed.

  Definition MLift : Functor 𝒞 ℰ := mkFunctor mlift_id mlift_compose.

End Functor.


(*------------------------------------------------------------------------------
  -- ＭＯＲＰＨＩＳＭ
  ----------------------------------------------------------------------------*)

Module Morphism.

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
      Π₂.make (λ g f ∙ make (α := λ C ∙ g(C) ∘ f(C)) _ ).
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

End Morphism.