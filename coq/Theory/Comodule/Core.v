Require Import Theory.Category.
Require Import Theory.RelativeComonad.

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
    λ f ↦ M⋅mcobind (F⋅f ∘ counit[ A ]).
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

