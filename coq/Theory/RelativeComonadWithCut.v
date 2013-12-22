Require Import Category.RComonad.
Require Import Theory.Functor.
Require Import Theory.Isomorphism.
Require Import Theory.RelativeComonad.
Require Import Theory.Comodule.
Require Import Theory.Category.
Require Import Theory.Product.
Require Import Theory.StrongMonoidal.

Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.

(*------------------------------------------------------------------------------
  -- ＲＥＬＡＴＩＶＥ  ＣＯＭＯＮＡＤ  ＤＥＦＩＮＩＴＩＯＮ  ＷＩＴＨ  ＣＵＴ
  ----------------------------------------------------------------------------*)

Section Defs.

  Context `{BinaryProduct 𝒞} `{BinaryProduct 𝒟}
          (F : Functor 𝒞 𝒟) (E : 𝒞) `{!CartesianStrongMonoidal F}.

  Section ExtendConstruction.

    Context {T : RelativeComonad F}
            (cut : ∀ A, T (E × A) ⇒ T A).

    Program Definition Extend {A B} : [ T A ⇒ F B ⟶ T (E × A) ⇒ F (E × B) ] :=
      λ f ↦ φ⁻¹ ∘ ⟨ F ⋅ π₁ ∘ T⋅counit , f ∘ cut A ⟩.
    Next Obligation.
      intros f g eq_fg. now rewrite eq_fg.
    Qed.

  End ExtendConstruction.

  Structure RelativeComonadWithCut := mkRelativeComonadWithCut
  { Tc  :> RelativeComonad F
  ; cut : ∀ {A}, Tc (E × A) ⇒ Tc A
  ; cut_counit : ∀ A, Tc⋅counit[A] ∘ cut ≈ F ⋅ π₂ ∘ Tc⋅counit
  ; cut_cobind : ∀ A B (f : Tc A ⇒ F B), Tc⋅cobind(f) ∘ cut ≈ cut ∘ Tc⋅cobind (Extend (@cut) f) }.

  Definition extend {T : RelativeComonadWithCut} {A B} : [ T A ⇒ F B ⟶ T (E × A) ⇒ F (E × B) ] :=
    Extend (@cut T).

End Defs.

Notation "'cut[' X ]" := (cut _ (A := X)) (only parsing).
Notation "T '⋅cut'" := (cut T) (at level 0, only parsing).
Notation "T '⋅cut[' X ]" := (cut T (A := X)) (at level 0, only parsing).

Notation make T cut :=
  (mkRelativeComonadWithCut (Tc := T) (cut := cut) _ _) (only parsing).

Arguments RelativeComonadWithCut {_ _ _ _} _ _ {_}.


(*------------------------------------------------------------------------------
  -- ＭＯＲＰＨＩＳＭ
  ----------------------------------------------------------------------------*)


Section MDefs.

  Context `{BinaryProduct 𝒞} `{BinaryProduct 𝒟}
          (F : Functor 𝒞 𝒟) (E : 𝒞) `{!CartesianStrongMonoidal F}.

  Structure Morphism (T S : RelativeComonadWithCut F E) : Type := mkMorphism
  { τ        :> ∀ C, T C ⇒ S C
  ; τ_counit : ∀ {C}, T⋅counit[ C ] ≈ S⋅counit[ C ] ∘ τ(C)
  ; τ_cobind : ∀ {C D} {f : S C ⇒ F D}, τ(D) ∘ T⋅cobind (f ∘ τ(C)) ≈ S⋅cobind f ∘ τ(C)
  ; τ_cut    : ∀ {A}, cut S ∘ τ(E × A) ≈ τ(A) ∘ cut T }.

  Program Definition rcm {T S : RelativeComonadWithCut F E} (M : Morphism T S) : RelativeComonad.Morphism T S :=
    RelativeComonad.Morphism.make M.
  Next Obligation.
    now apply τ_counit.
  Qed.
  Next Obligation.
    now apply τ_cobind.
  Qed.

End MDefs.

Module Morphism.

  Notation make τ := (mkMorphism (τ := τ) _ _ _) (only parsing).

  (* -- Ｉｄｅｎｔｉｔｙ  /  Ｃｏｍｐｏｓｉｔｉｏｎ                      -- *)
  Section id_composition.

    Context `{BinaryProduct 𝒞} `{BinaryProduct 𝒟}
            {F : Functor 𝒞 𝒟} {E : 𝒞} `{!CartesianStrongMonoidal F}.

    Implicit Types (T S U : RelativeComonadWithCut F E).

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
    Next Obligation.
      now rewrite left_id, right_id.
    Qed.

    Program Definition compose {S T U} : [ T ⇛ U ⟶ S ⇛ T ⟶ S ⇛ U ] :=
      λ g f ↦₂ make (λ C ∙ g(C) ∘ f(C)).
    Next Obligation.
      rewrite <- compose_assoc; now do 2 rewrite <- τ_counit.
    Qed.
    Next Obligation.
      setoid_rewrite <- compose_assoc at 2.
      rewrite <- τ_cobind. rewrite compose_assoc.
      setoid_rewrite <- compose_assoc at 2. rewrite τ_cobind.
      rewrite <- compose_assoc. reflexivity.
    Qed.
    Next Obligation.
      rewrite compose_assoc. rewrite <- τ_cut. repeat rewrite <- compose_assoc.
      now rewrite τ_cut.
    Qed.
    Next Obligation.
      intros f₁ f₂ eq_f₁f₂ g₁ g₂ eq_g₁g₂ x. simpl.
      now rewrite eq_f₁f₂, eq_g₁g₂.
    Qed.

  End id_composition.

End Morphism.