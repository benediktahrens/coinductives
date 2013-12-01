(*----------------------------------------------------------------------------*)
(*    Relative Comonad definition                                             *)
(*----------------------------------------------------------------------------*)

Require Import Theory.Category.
Require Import Theory.Functor.

Generalizable All Variables.

(*
 * Relative Comonad without laws
 *)
Structure RawRelativeComonad `(F : RawFunctor 𝒞 𝒟) : Type :=
  { T      :> 𝒞 → 𝒟
  ; counit : ∀ {X : 𝒞}, T X ⇒ F X
  ; cobind : ∀ {X Y : 𝒞}, T X ⇒ F Y → T X ⇒ T Y }.

Arguments counit {_} {_} {_} {_} {X}.
Arguments cobind {_} {_} {_} {_} {X Y} _.

Notation "'counit[' X ]" := (@counit _ _ _ _ X) (only parsing).

(*
 * Relative Comonad laws
 *)
Class IsRelativeComonad `{F : RawFunctor 𝒞 𝒟} (T : RawRelativeComonad F) : Prop :=
  { cobind_counit   : ∀ {X : 𝒞}, cobind (counit[ X ]) ≈ id[ T X ]
  ; counit_cobind   : ∀ {X Y : 𝒞} {f : T X ⇒ F Y}, counit ∘ cobind(f) ≈ f
  ; cobind_compose  : ∀ {X Y Z : 𝒞} {f : T X ⇒ F Y} {g : T Y ⇒ F Z}, cobind(g) ∘ cobind(f) ≈ cobind(g ∘ cobind(f))
  ; cobind_cong     :> ∀ {X Y : 𝒞}, (cobind (r := T) (X := X) (Y := Y)) Preserves _≈_ ⟶ _≈_ }.

(*
 * Relative Comonad
 *)
Structure RelativeComonad `(F : Functor 𝒞 𝒟) : Type :=
  { rawRelativeComonad :> RawRelativeComonad F
  ; isRelativeComonad  : IsRelativeComonad rawRelativeComonad }.

Existing Instance isRelativeComonad.

(*
 * Relative Comonad ⟹ Functor
 *)

Section RComonad_Functor.

  Definition lift `{F : RawFunctor 𝒞 𝒟} (T : RawRelativeComonad F) {A B : 𝒞} (f : A ⇒ B) : T A ⇒ T B :=
    cobind (F⋅f ∘ counit).

  Section Lift_Functoriality.

    Context `{F : Functor 𝒞 𝒟} {T : RelativeComonad F}.

    Lemma lift_id : ∀ (A : 𝒞), id[ T A ] ≈ lift T id[ A ].
    Proof.
      intro A; simpl; unfold lift.
      rewrite <- identity, left_id, cobind_counit.
      reflexivity.
    Qed.

    Lemma lift_compose : ∀ (A B C : 𝒞) (g : B ⇒ C) (f : A ⇒ B), lift T (g ∘ f) ≈ (lift T g) ∘ (lift T f).
    Proof.
      intros A B C g f; simpl; unfold lift.
      rewrite cobind_compose,
              compose_assoc,
              counit_cobind,
              <- compose_assoc,
              <- Fhom_compose.
      reflexivity.
    Qed.

    Lemma lift_cong : ∀ (A B : 𝒞), (lift T (A := A) (B := B)) Preserves _≈_ ⟶ _≈_.
    Proof.
      intros A B f g eq_fg.
      unfold lift. now rewrite eq_fg.
    Qed.

  End Lift_Functoriality.

  Program Definition RComonad_Functor `{F : Functor 𝒞 𝒟} (T : RelativeComonad F) : Functor 𝒞 𝒟 :=
    {| rawFunctor := {| Fobj := T ; Fhom := λ A B ∙ lift T (A := A) (B := B) |}
     ; isFunctor  := {| identity := lift_id ; Fhom_compose := lift_compose ; Fhom_cong := lift_cong |} |}.

End RComonad_Functor.

