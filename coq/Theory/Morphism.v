Require Import Theory.Category.

Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.

(*------------------------------------------------------------------------------
  -- ＭＯＲＰＨＩＳＭ  ＰＲＯＰＥＲＴＩＥＳ
  ----------------------------------------------------------------------------*)
Module Iso.
  Structure Iso {𝒞 : Category} (A B : 𝒞) := mkIso
  { iso_from      :> A ⇒ B
  ; iso_to        : B ⇒ A
  ; iso_left  : iso_from ∘ iso_to ≈ id
  ; iso_right : iso_to ∘ iso_from ≈ id }.

  Infix "≅" := Iso (at level 70).
  Notation "f ⁻¹" := (iso_to f) (at level 0).
  Notation "I '⋅≅-left'":= (iso_left I) (at level 0, only parsing).
  Notation "I '⋅≅-right'":= (iso_left I) (at level 0, only parsing).

  Notation make from to := (@mkIso _ _ _ from to _ _).

  Section Iso_Equivalence.

    Context {𝒞 : Category}.

    Program Definition refl {A : 𝒞} : A ≅ A :=
      make id id.
    Next Obligation. (* iso_left *)
      now rewrite left_id.
    Qed.
    Next Obligation. (* iso_right *)
      now rewrite right_id.
    Qed.

    Program Definition sym {A B : 𝒞} (iso_AB : A ≅ B) : B ≅ A :=
      make iso_AB⁻¹ iso_AB.
    Next Obligation. (* iso_left *)
      now rewrite iso_right.
    Qed.
    Next Obligation. (* iso_left *)
      now rewrite iso_left.
    Qed.

    Program Definition trans {A B C : 𝒞} (iso_AB : A ≅ B) (iso_BC : B ≅ C) : A ≅ C :=
      make (iso_BC ∘ iso_AB) (iso_AB ⁻¹ ∘ iso_BC ⁻¹).
    Next Obligation. (* iso_left *)
      rewrite compose_assoc; setoid_rewrite <- compose_assoc at 2.
      now rewrite iso_left, left_id, iso_left.
    Qed.
    Next Obligation. (* iso_right *)
      rewrite compose_assoc; setoid_rewrite <- compose_assoc at 2.
      now rewrite iso_right, left_id, iso_right.
    Qed.

  End Iso_Equivalence.

  Notation "≅-refl" := refl (only parsing).
  Notation "≅-sym" := sym (only parsing).
  Notation "≅-trans" := trans (only parsing).

End Iso.

(*----------------------------------------------------------------------------*)

Export Iso.