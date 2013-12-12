Require Import Theory.Category.
Require Import Theory.RelativeComonad.Core.

Set Implicit Arguments.
Unset Strict Implicit.
Generalizable All Variables.
    
(*------------------------------------------------------------------------------
  -- ＭＯＲＰＨＩＳＭ
  ----------------------------------------------------------------------------*)

Structure Morphism `(F : Functor 𝒞 𝒟) (T S : RelativeComonad F) : Type := make
{ τ          :> ∀ C, T C ⇒ S C
; τ_counit   : ∀ {C}, T⋅counit[ C ] ≈ S⋅counit[ C ] ∘ τ(C)
; τ_commutes : ∀ {C D} {f : S C ⇒ F D}, τ(D) ∘ T⋅cobind (f ∘ τ(C)) ≈ S⋅cobind f ∘ τ(C) }.

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
    make (τ := λ C ∙ id[ S C ]) _ _.
  Next Obligation.
    now rewrite right_id.
  Qed.
  Next Obligation.
    rewrite left_id; now do 2 rewrite right_id.
  Qed.

  Program Definition compose {S T U} : [ T ⇛ U ⟶ S ⇛ T ⟶ S ⇛ U ] :=
    λ g f ↦₂ make (τ := λ C ∙ g(C) ∘ f(C)) _ _.
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
