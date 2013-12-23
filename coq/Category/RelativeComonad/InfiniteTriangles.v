Require Import InfiniteTriangles.redecInfiniteTriangles8_4.
Require Import Category.Setoid.
Require Import Category.Type.
Require Import Category.Functor.Type_Setoid.
Require Import Category.RComod.
Require Import Category.RComonad.
Require Import Theory.Category.
Require Import Theory.Functor.
Require Import Theory.RelativeComonad.
Require Import Theory.RelativeComonadWithCut.
Require Import Theory.Comodule.
Require Import Theory.Product.
Require Import Theory.ProductInContext.

Set Implicit Arguments.
Unset Strict Implicit.
Generalizable All Variables.

(*------------------------------------------------------------------------------
  -- ＴＲＩ  ＩＳ  Ａ  ＲＥＬＡＴＩＶＥ  ＣＯＭＯＮＡＤ
  ----------------------------------------------------------------------------*)

Section TAUTO.

  Context `{F : Functor 𝒞 𝒟} (T : RelativeComonad F).

  Program Definition tauto : Comodule T 𝒟 :=
    Comodule.make _ (@cobind _ _ _ T).
  Next Obligation.
    now rewrite cobind_counit.
  Qed.
  Next Obligation.
    now rewrite cobind_compose.
  Qed.

End TAUTO.

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

  Definition 𝑴𝑻𝑹𝑰 : Comodule tri_cut 𝑺𝒆𝒕𝒐𝒊𝒅 := tauto tri_cut.
Require Import Cat.Theory.PushforwardComodule.
  Definition 𝑴𝑻𝑹𝑰_alt : Comodule tri_cut 𝑺𝒆𝒕𝒐𝒊𝒅 := tcomod tri_cut.

(*  Goal  𝑴𝑻𝑹𝑰 = 𝑴𝑻𝑹𝑰_alt.
    reflexivity.
*)
  Definition 𝑴𝑻𝑹𝑰_prod : Comodule tri_cut 𝑺𝒆𝒕𝒐𝒊𝒅 :=
    product_in_context (F := 𝑬𝑸) (T := tri_cut) E 𝑴𝑻𝑹𝑰.

Definition 𝑴𝑻𝑹𝑰_prod_alt : Comodule tri_cut 𝑺𝒆𝒕𝒐𝒊𝒅 :=
    product_in_context (F := 𝑬𝑸) (T := tri_cut) E 𝑴𝑻𝑹𝑰_alt.


  Program Definition tail (A : 𝑻𝒚𝒑𝒆) : 𝑴𝑻𝑹𝑰 A ⇒ 𝑴𝑻𝑹𝑰_prod A :=
    λ t ↦ @rest E A t.
  Next Obligation.
    intros x y eq_xy. now destruct eq_xy.
  Qed.

  Program Definition tail_alt (A : 𝑻𝒚𝒑𝒆) : 𝑴𝑻𝑹𝑰_alt A ⇒ 𝑴𝑻𝑹𝑰_prod_alt A :=
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


  Program Definition TAIL_MOR_alt : 𝑴𝑻𝑹𝑰_alt ⇒ 𝑴𝑻𝑹𝑰_prod_alt :=
    Comodule.Morphism.make tail.
  Next Obligation.
    apply redec_cong.
    repeat intro. f_equal. f_equal. now apply top_cong.
    destruct f as [f f_compat]. apply f_compat. now apply cut_cong.
    now apply rest_cong.
  Qed.


End Definitions.
