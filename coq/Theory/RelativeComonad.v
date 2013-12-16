Require Import Theory.Category.
Require Import Theory.Functor.
Require Import Theory.SetoidType.

Set Implicit Arguments.
Unset Strict Implicit.
Generalizable All Variables.

(*------------------------------------------------------------------------------
  -- ＲＥＬＡＴＩＶＥ  ＣＯＭＯＮＡＤ  ＤＥＦＩＮＩＴＩＯＮ
  ----------------------------------------------------------------------------*)

Structure RelativeComonad `(F : Functor 𝒞 𝒟) : Type := mkRelativeComonad
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

Notation make T counit cobind :=
  (mkRelativeComonad (T := T) (counit := counit) (cobind := cobind) _ _ _) (only parsing).

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


(*------------------------------------------------------------------------------
  -- ＭＯＲＰＨＩＳＭ
  ----------------------------------------------------------------------------*)

Structure Morphism `(F : Functor 𝒞 𝒟) (T S : RelativeComonad F) : Type := mkMorphism
{ τ          :> ∀ C, T C ⇒ S C
; τ_counit   : ∀ {C}, T⋅counit[ C ] ≈ S⋅counit[ C ] ∘ τ(C)
; τ_commutes : ∀ {C D} {f : S C ⇒ F D}, τ(D) ∘ T⋅cobind (f ∘ τ(C)) ≈ S⋅cobind f ∘ τ(C) }.

Module Morphism.

  Notation make τ := (mkMorphism (τ := τ) _ _) (only parsing).

  (* -- Ｉｄｅｎｔｉｔｙ  /  Ｃｏｍｐｏｓｉｔｉｏｎ                      -- *)
  Section id_composition.

    Context `{F : Functor 𝒞 𝒟}.

    Implicit Types (T S U : RelativeComonad F).

    Program Definition Hom T S : Setoid :=
      Setoid.make (Morphism T S) (λ f g ∙ ∀ x, f x ≈ g x).
    Next Obligation.
      constructor.
      - intros f x; reflexivity.
      - intros f g eq_fg x. symmetry. apply eq_fg.
      - intros f g h eq_fg eq_gh; etransitivity; eauto.
    Qed.

    Infix "⇛" := Hom (at level 70).

    Program Definition id {S} : S ⇛ S :=
      make (λ C ∙ id[ S C ]).
    Next Obligation.
      now rewrite right_id.
    Qed.
    Next Obligation.
      rewrite left_id; now do 2 rewrite right_id.
    Qed.

    Program Definition compose {S T U} : [ T ⇛ U ⟶ S ⇛ T ⟶ S ⇛ U ] :=
      λ g f ↦₂ make (λ C ∙ g(C) ∘ f(C)).
    Next Obligation.
      rewrite <- compose_assoc; now do 2 rewrite <- τ_counit.
    Qed.
    Next Obligation.
      setoid_rewrite <- compose_assoc at 2.
      rewrite <- τ_commutes. rewrite compose_assoc.
      setoid_rewrite <- compose_assoc at 2. rewrite τ_commutes.
      rewrite <- compose_assoc. reflexivity.
    Qed.
    Next Obligation.
      intros f₁ f₂ eq_f₁f₂ g₁ g₂ eq_g₁g₂ x. simpl.
      now rewrite eq_f₁f₂, eq_g₁g₂.
    Qed.

  End id_composition.

End Morphism.


(*------------------------------------------------------------------------------
  -- ＥＸＴＥＮＤ  ＣＯＮＳＴＲＵＣＴＩＯＮ
  ----------------------------------------------------------------------------*)

Require Import Theory.Product.
Require Import Theory.Isomorphism.
Require Import Theory.StrongMonoidal.

Section ExtendConstruction.

  Context `{BinaryProduct 𝒞} `{BinaryProduct 𝒟}
          `{F : Functor 𝒞 𝒟} `{!StrongMonoidal F}
           {T : RelativeComonad F} {E : 𝒞}.

  Notation "'α[E,A]'" := (F-×).

  Program Definition extend (A B : 𝒞) : [ T A ⇒ F B ⟶ T (E × A) ⇒ F (E × B) ] :=
    λ f ↦ α[E,A]⁻¹ ∘ ⟨ π₁[ F E , F A ] ∘ α[E,A] ∘ T⋅counit , f ∘ Lift(T) ⋅ π₂[ E , A ] ⟩.
  Next Obligation.
    intros f g eq_fg.
    now rewrite eq_fg.
  Qed.

End ExtendConstruction.
