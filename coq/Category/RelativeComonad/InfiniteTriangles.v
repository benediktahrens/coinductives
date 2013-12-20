Require Import InfiniteTriangles.redecInfiniteTriangles8_4.
Require Import Category.Setoid.
Require Import Category.Type.
Require Import Category.Functor.Type_Setoid.
Require Import Theory.Category.
Require Import Theory.Functor.
Require Import Theory.RelativeComonad.
Require Import Theory.Product.
Require Import Theory.ProductInContext.

Set Implicit Arguments.
Unset Strict Implicit.

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

  Program Definition tri_cut : RelativeComonadWithCut 𝑬𝑸 E :=
    ProductInContext.make 𝑻𝑹𝑰 cut.
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

End Definitions.
