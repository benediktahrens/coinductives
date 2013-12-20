Require Import Misc.Unicode.
Require Import Morphisms.
Require Export SetoidClass.
Require Import Coq.Logic.Eqdep.

Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.

(*------------------------------------------------------------------------------
  -- ＳＥＴＯＩＤ  ＤＥＦＩＮＩＴＩＯＮ
  ----------------------------------------------------------------------------*)

Module Setoid.

  Polymorphic Structure Setoid : Type := mkSetoid
  { Carrier :> Type
  ; _       : SetoidClass.Setoid Carrier }.

  Instance Setoid_Setoid (S : Setoid) : SetoidClass.Setoid S :=
    let 'mkSetoid s := S in s.

  Notation make c eq := (@mkSetoid c (@Build_Setoid _ eq _)) (only parsing).

  Program Definition eq_setoid (T : Type) : Setoid := make T eq.

  Notation "_≈_" := equiv                    (only parsing).
  Notation "x ≈ y :> T" := (equiv (A := T) x y) (at level 70, y at next level, no associativity).
  Notation "x ≈ y" := (equiv x y)            (at level 70, no associativity).
  Notation "x ≉ y" := (complement equiv x y) (at level 70, no associativity).

  Notation "f 'Preserves' r₁ ⟶ r₂" := (Proper (r₁ ==> r₂) f) (at level 30, no associativity).
  Notation "f 'Preserves₂' r₁ ⟶ r₂ ⟶ r₃" := (Proper (r₁ ==> r₂ ==> r₃) f) (at level 30, no associativity).

End Setoid.


(*------------------------------------------------------------------------------
  -- ＳＥＴＯＩＤ  ＭＯＲＰＨＩＳＭ
  ----------------------------------------------------------------------------*)

Module Π.

  Import Setoid.

  Structure Π (From To : Setoid) : Type := mkΠ
  { map :> From → To
  ; _   : map Preserves _≈_ ⟶ _≈_ }.

  Instance Π_Proper From To (f : Π From To) : f Preserves _≈_ ⟶ _≈_ :=
    let 'mkΠ p := f in p.

  Lemma Π_cong From To (f : Π From To) : ∀ x y, x ≈ y → f x ≈ f y.
  Proof.
    intros x y eq_xy; now rewrite eq_xy.
  Qed.

  Program Definition setoid (From To : Setoid) : Setoid :=
    Setoid.make (Π From To) (λ f g ∙ ∀ x y, x ≈ y → f x ≈ g y).
  Next Obligation.
    constructor.
    - (* Reflexivity *)
      intros f x y eq_xy. now rewrite eq_xy.
    - (* Symmetry *)
      intros f g eq_fg x y eq_xy. rewrite eq_xy. symmetry. now apply eq_fg.
    - (* Transitivity *)
      intros f g h eq_fg eq_gh x y eq_xy. etransitivity; eauto.
      now apply eq_gh.
  Qed.

  Notation "[ A ⟶ B ]" := (Π A B).

  Notation make f := (@mkΠ _ _ f _) (only parsing).

  Notation "'λ' x .. y ↦ F" := (make (λ x ∙ .. (λ y ∙ F) ..))
    (at level 200, x binder, y binder, no associativity).

  Program Definition id {A} : [A ⟶ A] := make (λ x ∙ x).
  Next Obligation.
    intros f g eq_fg. exact eq_fg.
  Qed.

  Program Definition compose A B C (g : [B ⟶ C]) (f : [A ⟶ B]) : [A ⟶ C] := make (λ x ∙ g (f x)).
  Next Obligation.
    intros x y eq_xy. rewrite eq_xy. reflexivity.
  Qed.

End Π.

Module Π₂.

  Import Setoid.

  Structure Π₂ (A B C : Setoid) : Type := mkΠ₂
  { map :> A → B → C
  ; _   : map Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_ }.

  Instance Π_Proper A B C (f : Π₂ A B C) : f Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_ :=
    let 'mkΠ₂ p := f in p.

  Lemma Π_cong₂ A B C (f : Π₂ A B C) : ∀ x x' y y', x ≈ x' → y ≈ y' → f x y ≈ f x' y'.
  Proof.
    intros x x' y y' eq_xx' eq_yy'; now rewrite eq_xx', eq_yy'.
  Qed.

  Notation "[ A ⟶ B ⟶ C ]" := (Π₂ A B C).

  Notation make  f := (@mkΠ₂ _ _ _ f _) (only parsing).

  Notation "'λ' x .. y ↦₂ F" := (make (λ x ∙ .. (λ y ∙ F) ..))
    (at level 200, x binder, y binder, no associativity).

End Π₂.

(*----------------------------------------------------------------------------*)

Export Setoid Π Π₂.
