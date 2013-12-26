Require Import Category.Setoid.
Require Import Category.Type.
Require Import Category.Functor.Type_Setoid.
Require Import Category.RComod.
Require Import Category.RComonadWithCut.
Require Import Theory.Category.
Require Import Theory.Functor.
Require Import Theory.RelativeComonadWithCut.
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
  { TCarrier :> 𝑹𝑪𝒐𝒎𝒐𝒏𝒂𝒅𝑾𝒊𝒕𝒉𝑪𝒖𝑡 E (F := 𝑬𝑸)
  ; TMor     :> (tcomod TCarrier) ⇒ (product_in_context E (tcomod TCarrier))
  ; TMor_cut : ∀ A, (α TMor _) ∘ TCarrier⋅cut[A] ≈ TCarrier⋅cut ∘ (α TMor _) }.

    (* Hypothesis T_cut_rest : ∀ A,  T⋅rest ∘ T⋅cut[A] ≈ T⋅cut ∘ T⋅rest. *)
  Infix "*" := pushforward.

  Structure THom (T S : TObj) : Type := mkTHom
  { Tτ :> T ⇒ S
  ; Tτ_commutes : product_in_context_mor (induced_morphism (rcm Tτ))
                    ∘ (pushf_prodctx _ Tτ)  ∘ (pushforwardm (rcm Tτ) T) ≈ S ∘ induced_morphism (rcm Tτ) }.

  Notation make Tτ := (mkTHom (Tτ := Tτ) _).

  Program Definition THom_Setoid (T S : TObj) : Setoid :=
    Setoid.make (THom T S) (λ g f ∙ (Tτ g) ≈ (Tτ f)).
  Next Obligation.
    constructor.
    - repeat intro. now rewrite H.
    - repeat intro. symmetry; now rewrite H.
    - repeat intro; etransitivity; eauto. now apply H0.
  Qed.

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

  Infix "⟨∘⟩" := T_compose (at level 40, left associativity).

  Lemma left_id : ∀ T S (f : T ⇛ S), T_id ⟨∘⟩ f ≈ f.
  Proof.
    intros. simpl. intros. rewrite H.
    reflexivity.
  Qed.

  Lemma right_id : ∀ T S (f : T ⇛ S), f ⟨∘⟩ T_id ≈ f.
  Proof.
    repeat intro. simpl. now rewrite H.
  Qed.

  Lemma compose_assoc A B C D (f : A ⇛ B) (g : B ⇛ C) (h : C ⇛ D) : h ⟨∘⟩ g ⟨∘⟩ f ≈ h ⟨∘⟩ (g ⟨∘⟩ f).
  Proof.
    repeat intro.
    simpl. now rewrite H.
  Qed.

  Canonical Structure 𝑻𝒓𝒊𝒂𝒏𝒈𝒍𝒆 : Category :=
    mkCategory left_id right_id compose_assoc.

End defs.


