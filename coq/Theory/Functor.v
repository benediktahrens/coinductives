Require Import Theory.Category.

Set Implicit Arguments.
Unset Strict Implicit.

(*------------------------------------------------------------------------------
  -- ＦＵＮＣＴＯＲ  ＤＥＦＩＮＩＴＩＯＮ
  ----------------------------------------------------------------------------*)

Structure Functor (𝒞 𝒟 : Category) : Type := mkFunctor
{ F           :> 𝒞 → 𝒟
; map         : ∀ {A B}, [ (A ⇒ B) ⟶ F A ⇒ F B ]
; identity    : ∀ {A}, id[ F A ] ≈ map id[ A ]
; map_compose : ∀ {A B C} {f : A ⇒ B} {g : B ⇒ C}, map (g ∘ f) ≈ (map g) ∘ (map f) }.

Notation "F ⋅ f" := (map F f) (at level 35, no associativity).

Local Notation make F map := (mkFunctor (F := F) (map0 := map) _ _).

(*------------------------------------------------------------------------------
  -- ＣＡＴＥＧＯＲＹ  ＭＯＲＰＨＩＳＭ
  ----------------------------------------------------------------------------*)

Module Morphism.

  Definition FEq {𝒞 𝒟 : Category} (F G : Functor 𝒞 𝒟) : Prop :=
    ∀ (A B : 𝒞) (f : A ⇒ B), F⋅f ∼ G⋅f.

  Program Definition Hom (𝒞 𝒟 : Category) : Setoid :=
    Setoid.make (Functor 𝒞 𝒟) FEq.
  Next Obligation.
    constructor; hnf; unfold FEq; simpl.
    - intros F A B f. apply ∼-refl.
    - intros F G eq_FG A B f. apply ∼-sym. now apply eq_FG.
    - intros F G H eq_FG eq_GH A B f. eapply ∼-trans; eauto.
  Qed.

  Infix "⇛" := Hom (at level 70).

  Lemma Heq_map_cong : ∀ {𝒞 𝒟 : Category} {F : Functor 𝒞 𝒟} {A B C D : 𝒞} (f : A ⇒ B) (g : C ⇒ D),
             f ∼ g → F⋅f ∼ F⋅g.
  Proof.
    intros 𝒞 𝒟 F A B C D f g eq_fg.
    assert (EqA := domain_eq eq_fg).
    assert (EqB := codomain_eq eq_fg).
    generalize dependent f; subst; intros.
    constructor.
    apply Heq_equiv in eq_fg; now rewrite eq_fg.
  Qed.

  Notation "∼-map-cong" := Heq_map_cong (only parsing).

  (* -- Ｉｄｅｎｔｉｔｙ  /  Ｃｏｍｐｏｓｉｔｉｏｎ                      -- *)
  Program Definition id {𝒞} : 𝒞 ⇛ 𝒞 :=
    make (λ X ∙ X) (λ A B ∙ λ f ↦ f).
  Next Obligation. (* map_cong *)
    intros f g eq_fg. apply eq_fg.
  Qed.
  Next Obligation. (* identity *)
    reflexivity.
  Qed.
  Next Obligation. (* map_compose *)
    reflexivity.
  Qed.

  Program Definition compose {𝒞 𝒟 ℰ} : [ 𝒟 ⇛ ℰ ⟶ 𝒞 ⇛ 𝒟 ⟶ 𝒞 ⇛ ℰ ] :=
    λ G F ↦₂ make (λ X ∙ G (F X)) (λ A B ∙ λ f ↦ G⋅(F⋅f)).
  Next Obligation. (* map_cong *)
    intros x y eq_xy. now rewrite eq_xy.
  Qed.
  Next Obligation. (* identity *)
    now do 2 rewrite <- identity.
  Qed.
  Next Obligation. (* map_compose *)
    now do 2 rewrite <- map_compose.
  Qed.
  Next Obligation. (* map_cong₂ *)
    intros F₁ F₂ eq_F₁F₂ G₁ G₂ eq_G₁G₂ A B f. simpl.
    eapply Heq_trans.
    apply eq_F₁F₂.
    apply Heq_map_cong.
    apply eq_G₁G₂.
  Qed.

End Morphism.

