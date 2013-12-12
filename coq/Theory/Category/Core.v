Require Import Misc.Unicode.
Require Import Theory.Notations.
Require Import Theory.Category.SetoidType.

Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.

(*------------------------------------------------------------------------------
  -- ＣＡＴＥＧＯＲＹ  ＤＥＦＩＮＩＴＩＯＮ
  ----------------------------------------------------------------------------*)

Polymorphic Structure Category : Type := mkCategory
{ Obj           :> Type
; Hom           :  Obj → Obj → Setoid where "A ⇒ B" := (Hom A B)
; id            :  ∀ {A}, A ⇒ A
; compose       :  ∀ {A B C}, [ B ⇒ C ⟶ A ⇒ B ⟶ A ⇒ C ] where "g ∘ f" := (compose g f)
; left_id       :  ∀ {A B} {f : A ⇒ B}, id ∘ f ≈ f
; right_id      :  ∀ {A B} {f : A ⇒ B}, f ∘ id ≈ f
; compose_assoc :  ∀ {A B C D} {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D}, h ∘ g ∘ f ≈ h ∘ (g ∘ f) }.

Notation "_⇒_" := Hom (only parsing).
Infix "⇒" := Hom.

Notation "_∘_" := compose (only parsing).
Infix "∘" := compose.

Notation "'id[' X ]" := (id (A := X)) (only parsing).
Notation "T '⋅id'" := (id (c := T)) (at level 0, only parsing).
Notation "T '⋅id[' X ]" := (id (c := T) (A := X)) (at level 0, only parsing).

Notation make Hom id compose := (@mkCategory _ Hom id compose _ _ _).

(*------------------------------------------------------------------------------
  -- ＨＥＴＥＲＯＧＥＮＥＯＵＳ  ＥＱＵＡＬＩＴＹ
  ----------------------------------------------------------------------------*)

Require Import Program.Equality. (* JMeq_eq Axiom *)

Inductive Heq_Hom {𝒞 : Category} {A B : 𝒞} (f : A ⇒ B) : ∀ {C D : 𝒞} (g : C ⇒ D), Prop :=
  heq_hom : ∀ {g : A ⇒ B}, f ≈ g → Heq_Hom f g.

Notation "_∼_" := Heq_Hom (only parsing).
Infix    "∼"   := Heq_Hom (at level 70).

Section Heq.

  Variable (𝒞 : Category).

  Lemma domain_eq : ∀ {A B C D : 𝒞} {f : A ⇒ B} {g : C ⇒ D}, f ∼ g → A = C.
  Proof.
    intros. now elim H.
  Qed.

  Lemma codomain_eq : ∀ {A B C D : 𝒞} {f : A ⇒ B} {g : C ⇒ D}, f ∼ g → B = D.
  Proof.
    intros. now elim H.
  Qed.

  Lemma Heq_refl : ∀ {A B : 𝒞} {f : A ⇒ B},  f ∼ f.
  Proof.
    intros A B f. constructor. reflexivity.
  Qed.

  Lemma Heq_sym : ∀ {A B C D : 𝒞} {f : A ⇒ B} {g : C ⇒ D}, f ∼ g → g ∼ f.
  Proof.
    intros.
    destruct H.
    constructor.
    now symmetry.
  Qed.

  Lemma Heq_trans : ∀ {A B C D E F : 𝒞} {f : A ⇒ B} {g : C ⇒ D} {h : E ⇒ F}, f ∼ g → g ∼ h → f ∼ h.
  Proof.
    intros. destruct H. destruct H0. constructor. etransitivity; eauto.
  Qed.

  Lemma Heq_equiv : ∀ {A B : 𝒞} {f g : A ⇒ B}, f ∼ g → f ≈ g.
  Proof.
    intros. dependent destruction H. exact H.
  Qed.

End Heq.

Notation "∼-refl"  := Heq_refl (only parsing).
Notation "∼-sym"   := Heq_sym (only parsing).
Notation "∼-trans" := Heq_trans (only parsing).
Notation "∼⇒≈"     := Heq_equiv (only parsing).
