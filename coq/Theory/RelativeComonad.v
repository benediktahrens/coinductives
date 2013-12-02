(*----------------------------------------------------------------------------*)
(*    Relative Comonad definition                                             *)
(*----------------------------------------------------------------------------*)

Require Import Theory.Category.
Require Import Theory.Functor.

Generalizable All Variables.

(*
 * Relative Comonad without laws
 *)
Structure relative_comonad `(F : functor 𝒞 𝒟) : Type :=
  { T      :> 𝒞 → 𝒟
  ; counit : ∀ {X : 𝒞}, T X ⇒ F X
  ; cobind : ∀ {X Y : 𝒞}, T X ⇒ F Y → T X ⇒ T Y }.

Arguments counit {_} {_} {_} {_} {X}.
Arguments cobind {_} {_} {_} {_} {X Y} _.

Notation "'counit[' X ]" := (@counit _ _ _ _ X) (only parsing).

(*
 * Relative Comonad laws
 *)
Class IsRelativeComonad `{F : functor 𝒞 𝒟} (T : relative_comonad F) : Prop :=
  { cobind_counit   : ∀ {X : 𝒞}, cobind (counit[ X ]) ≈ᶜ id[ T X ]
  ; counit_cobind   : ∀ {X Y : 𝒞} {f : T X ⇒ F Y}, counit ∘ cobind(f) ≈ᶜ f
  ; cobind_compose  : ∀ {X Y Z : 𝒞} {f : T X ⇒ F Y} {g : T Y ⇒ F Z},
                        cobind(g) ∘ cobind(f) ≈ᶜ cobind(g ∘ cobind(f))
  ; cobind_cong     :> ∀ {X Y : 𝒞}, (cobind (r := T) (X := X) (Y := Y)) Preserves _≈ᶜ_ ⟶ _≈ᶜ_ }.

(*
 * Relative Comonad
 *)
Structure RelativeComonad `(F : Functor 𝒞 𝒟) : Type :=
  { _relative_comonad :> relative_comonad F
  ; isRelativeComonad  : IsRelativeComonad _relative_comonad }.

Existing Instance isRelativeComonad.

(*
 * Relative Comonad ⟹ Functor
 *)

Section RComonad_Functor.

  Definition lift `{F : functor 𝒞 𝒟} (T : relative_comonad F) {A B : 𝒞} (f : A ⇒ B) : T A ⇒ T B :=
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

  Program Definition RelativeComonad_Functor `{F : Functor 𝒞 𝒟} (T : RelativeComonad F) : 𝒞 ⟹ 𝒟 :=
    {| _functor := {| Fobj := T ; Fhom := λ A B ∙ lift T (A := A) (B := B) |}
     ; isFunctor  := {| identity := lift_id ; Fhom_compose := lift_compose ; Fhom_cong := lift_cong |} |}.

End RComonad_Functor.

(*
 * Morphism between Relative comonads
 *)

Section RelativeComonad_Morphism.

  Notation cobind T f := (cobind (r := T) f).
  Notation counit T X := (counit (r := T) (X := X)).

  Structure relative_comonad_mor `{F : functor 𝒞 𝒟} (T S : relative_comonad F) : Type :=
    { T_mor :> ∀ (C : 𝒞), T C ⇒ S C }.

  Class IsRelativeComonadMor `{F : functor 𝒞 𝒟} {T S : relative_comonad F}
          (τ : relative_comonad_mor T S) : Prop :=
    { T_mor_counit   : ∀ {C : 𝒞}, T.(counit) C ≈ᶜ S.(counit) C ∘ τ(C)
    ; T_mor_commutes : ∀ {C D : 𝒞} {f : S C ⇒ F D}, τ(D) ∘ T.(cobind) (f ∘ τ(C)) ≈ᶜ S.(cobind) f ∘ τ(C) }.

  Structure RelativeComonadMor `{F : Functor 𝒞 𝒟} (T S : RelativeComonad F) : Type :=
    { _relative_comonad_mor :> relative_comonad_mor T S
    ; isRelativeComonadMor  : IsRelativeComonadMor _relative_comonad_mor }.

  Existing Instance isRelativeComonadMor.


  (*
   * Morphism instances
   *)

  Global Instance: ∀ `{F : functor 𝒞 𝒟}, Morphism (relative_comonad F) :=
    {| mor := relative_comonad_mor |}.

  Global Instance: ∀ `{F : Functor 𝒞 𝒟}, Morphism (RelativeComonad F) :=
    {| mor := RelativeComonadMor |}.

End RelativeComonad_Morphism.