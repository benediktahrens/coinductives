(*----------------------------------------------------------------------------*)
(*    Comodule definition                                                     *)
(*----------------------------------------------------------------------------*)

Require Import Theory.Category.
Require Import Theory.Functor.
Require Import Theory.RelativeComonad.

Generalizable All Variables.

(*
 * Comodule over a Relative Comonad without laws
 *)
Structure RawComoduleRC `{F : RawFunctor 𝒞 𝒟} (T : RawRelativeComonad F) (ℰ : RawCategory) : Type :=
  { M       :> 𝒞 → ℰ
  ; mcobind : ∀ {C D : 𝒞}, T C ⇒ F D → M C ⇒ M D }.

Arguments mcobind {_} {_} {_} {_} {_} {_} {C D} _.

(*
 * Comodule over a Relative Comonad laws
 *)
Class IsComoduleRC `{F : RawFunctor 𝒞 𝒟} {T : RawRelativeComonad F} {ℰ} (M : RawComoduleRC T ℰ) : Prop :=
  { mcobind_counit  : ∀ {C : 𝒞}, mcobind (counit[ C ]) ≈ᶜ id[ M C ]
  ; mcobind_compose : ∀ {C D E : 𝒞} {f : T C ⇒ F D} {g : T D ⇒ F E},
                        mcobind(g) ∘ mcobind(f) ≈ᶜ mcobind(g ∘ cobind(f)) :> ℰ [ M C , M E ]
  ; mcobind_cong    :> ∀ {C D : 𝒞}, (mcobind (r := M) (C := C) (D := D)) Preserves _≈ᶜ_ ⟶ _≈ᶜ_ }.

(*
 * Comodule over Relative Comonad
 *)
Structure ComoduleRC `{F : Functor 𝒞 𝒟} (T : RelativeComonad F) (ℰ : Category) : Type :=
  { rawComoduleRC :> RawComoduleRC T ℰ
  ; isComoduleRC  : IsComoduleRC rawComoduleRC }.

Existing Instance isComoduleRC.

(*
 * Comodule over Relative Comonad ⟹ Functor
 *)

Section ComoduleRC_Functor.

  Definition mlift `{F : RawFunctor 𝒞 𝒟} {T : RawRelativeComonad F} {ℰ} (M : RawComoduleRC T ℰ)
                    {A B : 𝒞} (f : A ⇒ B) : M A ⇒ M B := mcobind (F⋅f ∘ counit).

  Section Mlift_Functoriality.

    Context `{F : Functor 𝒞 𝒟} {T : RelativeComonad F} `{M : ComoduleRC T ℰ}.

    Lemma mlift_id : ∀ (A : 𝒞), id[ M A ] ≈ mlift M id[ A ].
    Proof.
      intro A; simpl; unfold mlift.
      rewrite <- identity, left_id, mcobind_counit.
      reflexivity.
    Qed.

    Lemma mlift_compose : ∀ (A B C : 𝒞) (g : B ⇒ C) (f : A ⇒ B), mlift M (g ∘ f) ≈ (mlift M g) ∘ (mlift M f).
    Proof.
      intros A B C g f; simpl; unfold mlift.
      rewrite mcobind_compose,
              compose_assoc,
              counit_cobind,
              <- compose_assoc,
              <- Fhom_compose.
      reflexivity.
    Qed.

    Lemma mlift_cong : ∀ (A B : 𝒞), (mlift M (A := A) (B := B)) Preserves _≈_ ⟶ _≈_.
    Proof.
      intros A B f g eq_fg.
      unfold mlift. now rewrite eq_fg.
    Qed.

  End Mlift_Functoriality.

  Program Definition ComoduleRC_Functor
                       `{F : Functor 𝒞 𝒟} {T : RelativeComonad F} {ℰ} (M : ComoduleRC T ℰ) : Functor 𝒞 ℰ :=
    {| rawFunctor := {| Fobj := M ; Fhom := λ A B ∙ mlift M (A := A) (B := B) |}
     ; isFunctor  := {| identity := mlift_id ; Fhom_compose := mlift_compose ; Fhom_cong := mlift_cong |} |}.

End ComoduleRC_Functor.
