Require Import Theory.Category.

Set Implicit Arguments.
Unset Strict Implicit.
Generalizable All Variables.

(*------------------------------------------------------------------------------
  -- ＲＥＬＡＴＩＶＥ  ＣＯＭＯＮＡＤ  ＤＥＦＩＮＩＴＩＯＮ
  ----------------------------------------------------------------------------*)

Structure RelativeComonad `(F : Functor 𝒞 𝒟) : Type := make
{ T              :> 𝒞 → 𝒟
; counit         : ∀ {X}, T X ⇒ F X
; cobind         : ∀ {X Y}, [ (T X ⇒ F Y) ⟶ T X ⇒ T Y ]
; cobind_counit  : ∀ {X}, cobind counit ≈ id[ T X ]
; counit_cobind  : ∀ {X Y} {f : T X ⇒ F Y}, counit ∘ cobind(f) ≈ f
; cobind_compose : ∀ {X Y Z} {f : T X ⇒ F Y} {g : T Y ⇒ F Z}, cobind(g) ∘ cobind(f) ≈ cobind(g ∘ cobind(f)) }.

Notation "'counit[' X ]" := (counit _ (X := X)) (only parsing).
Notation "T '⋅counit'" := (counit T) (at level 0, only parsing).
Notation "T '⋅counit[' X ]" := (counit T (X := X)) (at level 0, only parsing).

Notation "T '⋅cobind'" := (cobind T) (at level 0, only parsing).


(*------------------------------------------------------------------------------
  -- ＦＵＮＣＴＯＲ
  ----------------------------------------------------------------------------*)

Section Functor.

  Context `{F : Functor 𝒞 𝒟} (T : RelativeComonad F).

  Program Definition lift {A B} : [ (A ⇒ B) ⟶ T A ⇒ T B ] :=
    λ f ↦ T⋅cobind (F⋅f ∘ T⋅counit).
  Next Obligation.
    intros f g eq_fg. now rewrite eq_fg.
  Qed.

  Lemma lift_id : ∀ A, id[ T A ] ≈ lift id[ A ].
  Proof.
    intros A; simpl; unfold lift.
    rewrite <- identity, left_id, cobind_counit.
    reflexivity.
  Qed.

  Lemma lift_compose : ∀ A B C (f : A ⇒ B) (g : B ⇒ C), lift (g ∘ f) ≈ (lift g) ∘ (lift f).
  Proof.
    intros A B C g f; simpl; unfold lift.
    rewrite cobind_compose,
            compose_assoc,
            counit_cobind,
            <- compose_assoc,
            <- map_compose.
    reflexivity.
  Qed.

  Definition Lift : Functor 𝒞 𝒟 := mkFunctor lift_id lift_compose.

End Functor.

