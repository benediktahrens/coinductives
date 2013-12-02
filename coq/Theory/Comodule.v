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
Structure comodule_rc `{F : functor 𝒞 𝒟} (T : relative_comonad F) (ℰ : category) : Type :=
  { M       :> 𝒞 → ℰ
  ; mcobind : ∀ {C D : 𝒞}, T C ⇒ F D → M C ⇒ M D }.

Arguments mcobind {_} {_} {_} {_} {_} {_} {C D} _.

(*
 * Comodule over a Relative Comonad laws
 *)
Class IsComoduleRC `{F : functor 𝒞 𝒟} {T : relative_comonad F} {ℰ} (M : comodule_rc T ℰ) : Prop :=
  { mcobind_counit  : ∀ {C : 𝒞}, mcobind (counit[ C ]) ≈ᶜ id[ M C ]
  ; mcobind_compose : ∀ {C D E : 𝒞} {f : T C ⇒ F D} {g : T D ⇒ F E},
                        mcobind(g) ∘ mcobind(f) ≈ᶜ mcobind(g ∘ cobind(f)) :> ℰ [ M C , M E ]
  ; mcobind_cong    :> ∀ {C D : 𝒞}, (mcobind (c := M) (C := C) (D := D)) Preserves _≈ᶜ_ ⟶ _≈ᶜ_ }.

(*
 * Comodule over Relative Comonad
 *)
Structure ComoduleRC `{F : Functor 𝒞 𝒟} (T : RelativeComonad F) (ℰ : Category) : Type :=
  { _coModule_rc  :> comodule_rc T ℰ
  ; isComoduleRC  : IsComoduleRC _coModule_rc }.

Existing Instance isComoduleRC.

(*
 * Comodule over Relative Comonad ⟹ Functor
 *)
Section ComoduleRC_Functor.

  Definition mlift `{F : functor 𝒞 𝒟} {T : relative_comonad F} {ℰ} (M : comodule_rc T ℰ)
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
                       `{F : Functor 𝒞 𝒟} {T : RelativeComonad F} {ℰ} (M : ComoduleRC T ℰ) : 𝒞 ⟹ ℰ :=
    {| _functor   := {| Fobj := M ; Fhom := λ A B ∙ mlift M (A := A) (B := B) |}
     ; isFunctor  := {| identity := mlift_id ; Fhom_compose := mlift_compose ; Fhom_cong := mlift_cong |} |}.

End ComoduleRC_Functor.

(*
 * Morphism between Comodules over a Relative Comonad
 *)

Section Comodule_Morphism.

  Notation mcobind M f := (mcobind (c := M) f).

  Structure comodule_rc_mor `{F : functor 𝒞 𝒟} {T : relative_comonad F} {ℰ} (M N : comodule_rc T ℰ) : Type :=
    { M_mor :> ∀ (C : 𝒞), M C ⇒ N C }.

  Class IsComoduleRCMor `{F : functor 𝒞 𝒟} {T : relative_comonad F} {ℰ} {M N : comodule_rc T ℰ}
              (α : comodule_rc_mor M N) : Prop :=
    M_mor_commutes : ∀ {C D : 𝒞} {f : T C ⇒ F D}, α(D) ∘ M.(mcobind) f ≈ᶜ N.(mcobind) f ∘ α(C).

  Structure ComoduleRCMor `{F : Functor 𝒞 𝒟} {T : RelativeComonad F} {ℰ} (M N : ComoduleRC T ℰ) : Type :=
    { _comodule_rc_mor :> comodule_rc_mor M N
    ; isComoduleRCMor  : IsComoduleRCMor _comodule_rc_mor }.

  Existing Instance isComoduleRCMor.


  (*
   * Morphism instances
   *)

  Global Instance: ∀ `{F : functor 𝒞 𝒟} (T : relative_comonad F) (ℰ : category), Morphism (comodule_rc T ℰ) :=
    {| mor := comodule_rc_mor |}.

  Global Instance: ∀ `{F : Functor 𝒞 𝒟} (T : RelativeComonad F) (ℰ : Category), Morphism (ComoduleRC T ℰ) :=
    {| mor := ComoduleRCMor |}.

End Comodule_Morphism.
