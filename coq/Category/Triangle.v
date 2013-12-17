Require Import Category.Setoid.
Require Import Category.Type.
Require Import Category.Functor.Type_Setoid.
Require Import Category.RComod.
Require Import Category.RComonad.
Require Import Theory.Category.
Require Import Theory.Functor.
Require Import Theory.RelativeComonad.
Require Import Theory.SetoidType.
Require Import Theory.Comodule.
Require Import Theory.Product.
Require Import Theory.ProductInContext.
Require Import Theory.PushforwardComodule.

Set Implicit Arguments.
Unset Strict Implicit.
Generalizable All Variables.

Section defs.

  Variable (E : 𝑻𝒚𝒑𝒆).

  Structure TObj : Type :=
  { TCarrier :> 𝑹𝑪𝒐𝒎𝒐𝒏𝒂𝒅 𝑬𝑸
  ; TMor     :> (tcomod TCarrier) ⇒ (product_in_context E (tcomod TCarrier)) }.

  Infix "*" := pushforward.

  Structure THom (T S : TObj) : Type := mkTHom
  { Tτ :> T ⇒ S
  ; Tτ_commutes : product_in_context_mor E (induced_morphism Tτ) ∘ (pushf_prodctx E _ Tτ)  ∘ (pushforwardm Tτ T) ≈
                  S ∘ induced_morphism Tτ }.

  Notation make Tτ := (mkTHom (Tτ := Tτ) _).

  Program Definition THom_Setoid (T S : TObj) : Setoid :=
    Setoid.make (THom T S) (λ g f ∙ (Tτ g) ≈ (Tτ f)).
  Next Obligation.
  Admitted.

  Infix "⇛" := THom_Setoid (at level 70).

  Program Definition T_id {T} : T ⇛ T :=
    make (id[T]).
  Next Obligation.
    now rewrite H.
  Qed.

  Obligation Tactic := idtac.
  Program Definition T_compose {T S R : TObj} : [ S ⇛ R ⟶ T ⇛ S ⟶ T ⇛ R ] :=
    λ g f ↦₂ make (g ∘ f).
  Next Obligation.
    intros T S R g f.
    destruct g as [g g_commutes]. simpl in g_commutes.
    destruct f as [f f_commutes]. simpl in f_commutes. simpl.
    intros.
    rewrite H.
    etransitivity.
    eapply Π_cong.
    apply f_commutes.
    reflexivity.
    apply g_commutes.
    reflexivity.
  Qed.
  Next Obligation.
    repeat intro.
    simpl.
    etransitivity. eapply Π_cong.
    eapply Π_cong. apply H1.
    etransitivity. eapply Π_cong.
    apply H0. reflexivity.
    apply H.
    reflexivity.
  Qed.

End defs.



