Require Import InfiniteTriangles.redecInfiniteTriangles8_4.
Require Import Category.Setoid.
Require Import Category.Type.
Require Import Category.Functor.Type_Setoid.
Require Import Category.RComod.
Require Import Category.RComonad.
Require Import Category.RComonadWithCut.
Require Import Category.Triangle.
Require Import Theory.Category.
Require Import Theory.Functor.
Require Import Theory.RelativeComonad.
Require Import Theory.RelativeComonadWithCut.
Require Import Theory.Comodule.
Require Import Theory.Product.
Require Import Theory.ProductInContext.
Require Import Theory.PushforwardComodule.

Set Implicit Arguments.
Unset Strict Implicit.
Generalizable All Variables.

(*------------------------------------------------------------------------------
  -- ＴＲＩ  ＩＳ  Ａ  ＲＥＬＡＴＩＶＥ  ＣＯＭＯＮＡＤ
  ----------------------------------------------------------------------------*)

Section Definitions.

  Variable E : Type.

  Program Definition Tri (A : 𝑻𝒚𝒑𝒆) : 𝑺𝒆𝒕𝒐𝒊𝒅 :=
    Setoid.make (Tri E A) (@bisimilar _ _).
  Next Obligation.
    constructor.
    - apply bisimilar_refl.
    - apply bisimilar_sym.
    - apply bisimilar_trans.
  Qed.

  Program Definition Top {A : 𝑻𝒚𝒑𝒆} : Tri A ⇒ 𝑬𝑸 A :=
    Π.make (@top E A).
  Next Obligation.
    hnf. apply top_cong.
  Qed.

  Program Definition Redec {X Y : 𝑻𝒚𝒑𝒆} : [ Tri X ⇒ 𝑬𝑸 Y ⟶ Tri X ⇒ Tri Y ] :=
    λ f ↦ Π.make (@redec E X Y f).
  Next Obligation.
    intros u v eq_uv. apply redec_cong; intuition.
    intros t₁ t₂ eq_t₁t₂; now rewrite eq_t₁t₂.
  Qed.
  Next Obligation.
    intros f g eq_fg t₁ t₂ eq_t₁t₂; simpl in *.
    eapply bisimilar_trans.
    apply redec_ext. intro t. apply eq_fg. apply bisimilar_refl.
    apply redec_cong. intros u v eq_uv; now rewrite eq_uv.
    exact eq_t₁t₂.
  Qed.

  Lemma Redec_Top X : Redec Top ≈ id[ Tri X ].
  Proof.
    simpl. intros x y eq_xy. eapply bisimilar_trans; eauto.
    apply comonad2.
  Qed.

  Lemma Top_Redec X Y (f : Tri X ⇒ 𝑬𝑸 Y) : Top ∘ Redec(f) ≈ f.
  Proof.
    intros x y eq_xy. rewrite eq_xy. reflexivity.
  Qed.

  Lemma Redec_compose X Y Z (f : Tri X ⇒ 𝑬𝑸 Y) (g : Tri Y ⇒ 𝑬𝑸 Z) :
    Redec(g) ∘ Redec(f) ≈ Redec(g ∘ Redec(f)).
  Proof.
    intros x y eq_xy.
    symmetry. rewrite eq_xy. apply comonad3.
    intros u v eq_uv; now rewrite eq_uv.
  Qed.

  Definition 𝑻𝑹𝑰 : RelativeComonad 𝑬𝑸 :=
    mkRelativeComonad Redec_Top Top_Redec Redec_compose.

  Program Definition cut A : 𝑻𝑹𝑰 (E × A) ⇒ 𝑻𝑹𝑰 A :=
    λ t ↦ @redecInfiniteTriangles8_4.cut E A t.
  Next Obligation.
    intros t t' eq_tt'.
    apply cut_cong.
    exact eq_tt'.
  Qed.

  Program Definition TRI : RelativeComonadWithCut 𝑬𝑸 E :=
    RelativeComonadWithCut.make 𝑻𝑹𝑰 cut.
  Next Obligation.
    assert (top (redecInfiniteTriangles8_4.cut x) = snd (top x)).
    apply cut_top.
    simpl in H0. rewrite H0. f_equal. now apply top_cong.
  Qed.
  Next Obligation.
    eapply bisimilar_trans. apply redec_cut.
    unfold redecInfiniteTriangles8_4.lift. apply cut_cong.
    apply redec_cong.
    repeat intro. f_equal. f_equal. now apply top_cong.
    destruct f as [f f_compat].
    simpl. apply f_compat. now apply cut_cong.
    exact H.
  Qed.

  Definition 𝑴𝑻𝑹𝑰 : Comodule TRI 𝑺𝒆𝒕𝒐𝒊𝒅 := tcomod TRI.

  Definition 𝑴𝑻𝑹𝑰_prod : Comodule TRI 𝑺𝒆𝒕𝒐𝒊𝒅 :=
    product_in_context (F := 𝑬𝑸) (T := TRI) E 𝑴𝑻𝑹𝑰.

  Program Definition tail (A : 𝑻𝒚𝒑𝒆) : 𝑴𝑻𝑹𝑰 A ⇒ 𝑴𝑻𝑹𝑰_prod A :=
    λ t ↦ @rest E A t.
  Next Obligation.
    intros x y eq_xy. now destruct eq_xy.
  Qed.

  Program Definition TAIL_MOR : 𝑴𝑻𝑹𝑰 ⇒ 𝑴𝑻𝑹𝑰_prod :=
    Comodule.Morphism.make tail.
  Next Obligation.
    apply redec_cong.
    repeat intro. f_equal. f_equal. now apply top_cong.
    destruct f as [f f_compat]. apply f_compat. now apply cut_cong.
    now apply rest_cong.
  Qed.

  Definition 𝑻𝒓𝒊 : 𝑻𝒓𝒊𝒂𝒏𝒈𝒍𝒆 E.
    exists TRI TAIL_MOR.
    abstract (
    repeat intro; rewrite H;
    match goal with
                    | H : _ |- _ ≈ ?x => let x' := eval simpl in x in change x with x'
                  end;
    rewrite <- cut_rest; apply bisimilar_refl).
  Defined.

  Section CoIniatiality.

    Variable (Tr : 𝑻𝒓𝒊𝒂𝒏𝒈𝒍𝒆 E).

    (** Notations for T **)
    Let T : RelativeComonadWithCut 𝑬𝑸 E := TCarrier Tr.
    Notation "'T⋅top'" := (T⋅counit).
    Notation "'T⋅top[' A ]" := (T⋅counit[ A ]).
    Notation "'T⋅rest'" := (TMor Tr _).
    Notation "'T⋅rest[' A ]" := (TMor Tr A).
    Notation "'[T]'" := (tcomod T).
    Notation "'[T]-×'" := (product_in_context E [T]).
    Notation "'T⋅cut'" := (RelativeComonadWithCut.cut T).
    Notation "'T⋅cut[' A ]" := (RelativeComonadWithCut.cut T (A := A)).
    Notation "'T⋅extend'" := (extend (T0 := T)).

    (** Notations for TRI **)
    Notation "'TRI⋅top'" := (Top).
    Notation "'TRI⋅rest'" := (TAIL_MOR _).
    Notation "'TRI⋅extend'" := (extend (T0 := TRI)).
    Notation "'[TRI]'" := (tcomod TRI).
    Notation "'[TRI]-×'" := (product_in_context E [TRI]).

    Definition bisim_ext {A B} (f g : A ⇒ TRI B) : Prop :=
      ∀ x, f x ≈ g x.

    Infix "∼" := bisim_ext (at level 70).

    Lemma bisim_ext_bisim : ∀ A B (f g : A ⇒ TRI B), f ∼ g → f ≈ g.
    Proof.
      intros. destruct f as [f f_cong]; destruct g as [g g_cong]; simpl in *.
      intros. eapply bisimilar_trans. apply f_cong. apply H0.
      apply H.
    Qed.

    Lemma bisim_bisim_ext : ∀ A B (f g : A ⇒ TRI B), f ≈ g → f ∼ g.
    Proof.
      intros. simpl in *. intro. apply H. reflexivity.
    Qed.

    (** Definition of τ : ∀ A, T A ⇒ TRI A **)
    CoFixpoint tau A (t : T A) : TRI A :=
      constr (T⋅top t) (tau (T⋅rest t)).

    Lemma top_tau : ∀ A (t : T A), top (tau t) = T⋅top t.
    Proof.
      reflexivity.
    Qed.

    Lemma rest_tau : ∀ A (t : T A), rest (tau t) = tau (T⋅rest t).
    Proof.
      reflexivity.
    Qed.

    Lemma tau_cong : ∀ A (x y : T A), x ≈ y → tau x ≈ tau y.
    Proof.
      cofix Hc; intros; constructor; simpl.
      - now rewrite H.
      - apply Hc. now rewrite H.
    Qed.

    Program Definition τ A : T A ⇒ TRI A :=
      λ t ↦ tau t.
    Next Obligation.
      repeat intro; now apply tau_cong.
    Qed.

    Arguments τ _.

    Lemma Rest_τ : ∀ {A}, TRI⋅rest ∘ τ(A) ≈ τ(E×A) ∘ T⋅rest.
    Proof.
      repeat intro; simpl. apply tau_cong. now rewrite H.
    Qed.

    (**** 1ˢᵗ law ****)
    Lemma τ_counit : ∀ A, T⋅top[A] ≈ TRI⋅top ∘ τ(A).
    Proof.
      intro A. symmetry. repeat intro. now rewrite H.
    Qed.

    (**** 3ʳᵈ law ****)
    Lemma τ_cut_trans : ∀ A x t₁ t₂, t₁ ≈ τ(A) (T⋅cut x) → TRI⋅cut (τ(E × A) x) ≈ t₂ → t₁ ≈ t₂.
    Proof.
      cofix Hc; intros A x t₁ t₂ eq_t₁ eq_t₂; constructor.
      - (* set up goal *)
        etransitivity; [apply top_cong; apply eq_t₁ |]; clear eq_t₁ t₁.
        etransitivity; [| apply top_cong; apply eq_t₂]; clear eq_t₂ t₂.
        (***********************************************************)
        match goal with
          | H : _ |- _ = top ?x => let x' := eval simpl in x in change x with x'
        end.
        rewrite cut_top. rewrite top_tau. simpl.
        generalize (@cut_counit _ _ _ _ _ _ _ T); intro cc.
        now apply cc.
      - (* set up goal *)
        apply Hc with (T⋅rest x);
        [ etransitivity; [apply rest_cong; apply eq_t₁|]; clear eq_t₁ eq_t₂ t₁ t₂;
          revert x; change (TRI⋅rest ∘ (τ(A) ∘ T⋅cut[A]) ∼ τ(E×A) ∘ (T⋅cut[E×A] ∘ T⋅rest))
        | etransitivity; [| apply rest_cong; apply eq_t₂]; clear eq_t₁ eq_t₂ t₁ t₂;
          revert x; change (TRI⋅cut ∘ (τ (E × (E × A)) ∘ T⋅rest) ∼ TRI⋅rest ∘ (TRI⋅cut ∘ τ (E × A)))
        ]; apply bisim_bisim_ext.
        (************************************************************)
        + rewrite <- compose_assoc.
          etransitivity. apply Π_cong₂; [ apply Rest_τ | reflexivity ].
          etransitivity. apply compose_assoc.
          apply Π_cong₂; [reflexivity|].
          apply TMor_cut.
        + rewrite <- compose_assoc. symmetry.
          cut (TRI⋅rest ∘ TRI⋅cut[A] ≈ TRI⋅cut ∘ TRI⋅rest); intro.
          etransitivity. apply Π_cong₂. apply H. reflexivity.
          rewrite compose_assoc. apply Π_cong₂; [reflexivity|].
          apply Rest_τ.
          intros.
          etransitivity; [ now rewrite H |].
          change (bisimilar (rest (redecInfiniteTriangles8_4.cut y)) (redecInfiniteTriangles8_4.cut (rest y))).
          rewrite cut_rest. apply bisimilar_refl.
    Qed.

    Lemma τ_cut : ∀ A, τ(A) ∘ T⋅cut ≈ TRI⋅cut ∘ τ(E×A).
    Proof.
      repeat intro.
      etransitivity. now rewrite H.
      apply τ_cut_trans with y; reflexivity.
    Qed.


    (**** 2ⁿᵈ law ****)
    Lemma τ_cobind_trans : ∀ A B (f : TRI A ⇒ 𝑬𝑸 B) x t₁ t₂,
                             t₁ ≈ τ(B) (T⋅cobind (f ∘ τ(A)) x) → TRI⋅cobind f (τ(A) x) ≈ t₂ → t₁ ≈ t₂.
    Proof.
      cofix Hc; intros A B f x t₁ t₂ eq_t₁ eq_t₂; constructor.
      - (* set up goal *)
        etransitivity; [ apply top_cong; apply eq_t₁ |]; clear eq_t₁ t₁.
        etransitivity; [| apply top_cong; apply eq_t₂]; clear eq_t₂ t₂.
        (**************************************************************)
        simpl. generalize(@counit_cobind _ _ _ T); intro cc.
        etransitivity. apply cc. reflexivity. reflexivity.
      - (* set up goal *)
        apply Hc with (f := extend (T0 := TRI) f) (x := T⋅rest x);
        [ etransitivity; [apply rest_cong; apply eq_t₁ |]; clear eq_t₁ eq_t₂ t₁ t₂;
          revert x; change (TRI⋅rest ∘ (τ(B) ∘ T⋅cobind (f ∘ τ(A)))
                                 ∼ τ (E × B) ∘ (T⋅cobind (extend (T0 := TRI) f ∘ τ(E × A)) ∘ T⋅rest))
        | etransitivity; [| apply rest_cong; apply eq_t₂]; clear eq_t₁ eq_t₂ t₁ t₂;
          revert x; change (TRI⋅cobind (extend (T0 := TRI) f) ∘ (τ (E × A) ∘ T⋅rest)
                             ∼ TRI⋅rest ∘ (TRI⋅cobind f ∘ τ(A)))
        ]; apply bisim_bisim_ext.
        (***************************************************************)
        + rewrite <- compose_assoc.
          etransitivity. apply Π_cong₂; [apply Rest_τ | reflexivity].
          etransitivity. apply compose_assoc. apply Π_cong₂; [reflexivity |].
          etransitivity. generalize (@α_commutes); intro cc.
          specialize (cc _ _ _ _ _ _ _ (TMor Tr)).
          apply cc.
          apply Π_cong₂; [| reflexivity].
          transitivity (T⋅cobind (T⋅extend (f ∘ τ(A)))).
          reflexivity.
          apply Π_cong. repeat intro. simpl.
          f_equal. f_equal. now rewrite H.
          destruct f as [f f_cong]. apply f_cong.
          etransitivity. apply τ_cut. apply H. reflexivity.
        + rewrite <- compose_assoc. symmetry.
          generalize (@α_commutes); intro cc.
          specialize (cc _ _ _ _ _ _ _ TAIL_MOR).
          transitivity (TRI⋅rest ∘ (mcobind [TRI]) f ∘ τ A).
          reflexivity.
          etransitivity. apply Π_cong₂; [| reflexivity].
          apply cc.
          rewrite compose_assoc.
          etransitivity. apply Π_cong₂; [reflexivity|].
          apply Rest_τ. reflexivity.
    Qed.

    Lemma τ_cobind : ∀ A B (f : TRI A ⇒ 𝑬𝑸 B), τ(B) ∘ T⋅cobind (f ∘ τ(A)) ≈ TRI⋅cobind f ∘ τ(A).
    Proof.
      repeat intro. etransitivity. now rewrite H.
      apply τ_cobind_trans with (f := f) (x := y); reflexivity.
    Qed.

    Definition TAU : T ⇒ TRI.
      apply RelativeComonadWithCut.mkMorphism with τ.
      - apply τ_counit.
      - apply τ_cobind.
      - intro A; symmetry; apply τ_cut.
    Defined.

  End CoIniatiality.

  Definition TAUm (T : 𝑻𝒓𝒊𝒂𝒏𝒈𝒍𝒆 E) : T ⇒ 𝑻𝒓𝒊.
    exists (TAU T).
    - abstract (simpl; intros; apply tau_cong; now rewrite H).
  Defined.

  Lemma TAU_unique_trans : ∀ (T : 𝑻𝒓𝒊𝒂𝒏𝒈𝒍𝒆 E) (f g : T ⇒ 𝑻𝒓𝒊) u v t₁ t₂, t₁ ≈ (Tτ f) u v → (Tτ g) u v ≈ t₂ → t₁ ≈ t₂.
    cofix Hc; intros; constructor.
    - (* set up goal *)
      etransitivity; [ apply top_cong; apply H |]; clear H t₁.
      etransitivity; [| apply top_cong; apply H0]; clear H0 t₂.
      generalize (@RelativeComonadWithCut.τ_counit); intro cc.
      specialize (cc _ _ _ _ _ _ _ _ _ (Tτ f)).
      simpl in cc. etransitivity. symmetry. apply cc. reflexivity. clear cc.
      generalize (@RelativeComonadWithCut.τ_counit); intro cc.
      specialize (cc _ _ _ _ _ _ _ _ _ (Tτ g)). now apply cc.
    - eapply Hc.
      + etransitivity. apply rest_cong. apply H.
        generalize (@Tτ_commutes); intro cc. specialize (cc _ _ _ f). simpl in cc.
        symmetry. apply cc. reflexivity.
      + etransitivity; [| apply rest_cong; apply H0].
        generalize (@Tτ_commutes); intro cc. specialize (cc _ _ _ g). simpl in cc.
        apply cc. reflexivity.
  Qed.

  Lemma TAU_unique : ∀ (T : 𝑻𝒓𝒊𝒂𝒏𝒈𝒍𝒆 E) (f g : T ⇒ 𝑻𝒓𝒊), f ≈ g.
  Proof.
    repeat intro. etransitivity. now rewrite H.
    apply TAU_unique_trans with (f := f) (g := g) (v := y); reflexivity.
  Qed.

  Require Import Theory.InitialTerminal.
  Definition CoInitiality : Terminal (𝑻𝒓𝒊𝒂𝒏𝒈𝒍𝒆 E).
    exists 𝑻𝒓𝒊 TAUm.
    - abstract (intros; apply TAU_unique).
  Defined.

End Definitions.

Print Assumptions CoInitiality.