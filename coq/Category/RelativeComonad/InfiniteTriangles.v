Require Import InfiniteTriangles.triangle.
Require Import Category.Setoid.
Require Import Category.Type.
Require Import Category.Functor.Type_Setoid.
Require Import Theory.Category.
Require Import Theory.Functor.
Require Import Theory.RelativeComonad.
Require Import Theory.SetoidType.
Require Import Theory.Comodule.
Require Import Category.RComod.
Require Import ProductInContext.

Set Implicit Arguments.
Unset Strict Implicit.
Generalizable All Variables.

(*------------------------------------------------------------------------------
  -- ＴＲＩ  ＩＳ  Ａ  ＲＥＬＡＴＩＶＥ  ＣＯＭＯＮＡＤ
  -- ＴＡＩＬ  ＩＳ  Ａ  ＭＯＲＰＨＩＳＭ  ＯＦ  ＣＯＭＯＤＵＬＥＳ
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
    Setoid.make (tri E A) (@bisimilar _ _).

  Program Definition Top {A : 𝑻𝒚𝒑𝒆} : Tri A ⇒ 𝑬𝑸 A :=
    Π.make (@top E A).
  Next Obligation.
    repeat intro. now destruct H.
  Qed.

  Program Definition Redec {X Y : 𝑻𝒚𝒑𝒆} : [ Tri X ⇒ 𝑬𝑸 Y ⟶ Tri X ⇒ Tri Y ] :=
    λ f ↦ Π.make (@redec E X Y f).
  Next Obligation.
    intros u v eq_uv. apply redec_cong; intuition.
  Qed.
  Next Obligation.
    intros f g eq_fg t₁ t₂ eq_t₁t₂; simpl in *.
    apply redec_cong; auto.
  Qed.

  Lemma Redec_Top X : Redec Top ≈ id[ Tri X ].
  Proof.
    simpl. intros x y eq_xy. rewrite eq_xy.
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

  Definition 𝑴𝑻𝑹𝑰 : Comodule 𝑻𝑹𝑰 𝑺𝒆𝒕𝒐𝒊𝒅 := tauto 𝑻𝑹𝑰.

  Definition 𝑴𝑻𝑹𝑰_prod : Comodule 𝑻𝑹𝑰 𝑺𝒆𝒕𝒐𝒊𝒅.
  Proof.
    apply product_in_context.
    exact E.
    eauto with typeclass_instances.
    exact 𝑴𝑻𝑹𝑰.
  Defined.

  Program Definition tail (A : 𝑻𝒚𝒑𝒆) : 𝑴𝑻𝑹𝑰 A ⇒ 𝑴𝑻𝑹𝑰_prod A :=
    λ t ↦ @rest E A t.
  Next Obligation.
    intros x y eq_xy. now destruct eq_xy.
  Qed.

  Program Definition TAIL_MOR : 𝑴𝑻𝑹𝑰 ⇒ 𝑴𝑻𝑹𝑰_prod :=
    Comodule.Morphism.make tail.
  Next Obligation.
    apply redec_cong.
    intros t t' eq_tt'; rewrite eq_tt'. unfold triangle.extend.
    f_equal.
    destruct f as [f f_cong]. apply f_cong.
    rewrite <- lift_map. reflexivity.
    now destruct H.
  Qed.

End Definitions.