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

(* Section TAUTO. *)

(*   Context `{F : Functor 𝒞 𝒟} (T : RelativeComonad F). *)

(*   Program Definition tauto : Comodule T 𝒟 := *)
(*     Comodule.make _ (@cobind _ _ _ T). *)
(*   Next Obligation. *)
(*     now rewrite cobind_counit. *)
(*   Qed. *)
(*   Next Obligation. *)
(*     now rewrite cobind_compose. *)
(*   Qed. *)

(* End TAUTO. *)


Section Definitions.

  Variable E : Type.

  Program Definition Tri (A : 𝑻𝒚𝒑𝒆) : 𝑺𝒆𝒕𝒐𝒊𝒅 :=
    Setoid.make (tri E A) (@bisimilar _ _).
  Next Obligation.
    constructor.
    - apply bisimilar_refl.
    - apply bisimilar_sym.
    - apply bisimilar_trans.
  Qed.

  Program Definition Top {A : 𝑻𝒚𝒑𝒆} : Tri A ⇒ 𝑬𝑸 A :=
    Π.make (@top E A).

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

  Notation tri := redecInfiniteTriangles8_4.Tri.

  Notation extend := redecInfiniteTriangles8_4.lift.

  Definition Extend {A B} (f : tri E A → B) (r : Trap E A) :=
    (fst (top r), f (redec (λ t ∙ snd (top t)) r)).

  (* Lemma xxx : ∀ {A B : Type} (f : tri E A → B) (t : tri E A), *)
  (*               bisimilar (rest (redec f t)) (redec (Extend f) (rest t)). *)
  (* Proof. *)
  (*   cofix; intros. *)
  (*   rewrite redec_rest. *)
  (*   apply redec_ext. *)
  (*   hnf. intros. *)
  (*   unfold extend. unfold Extend. *)

  (*   apply bisimilar_refl. *)

  Lemma xxx : ∀ {A : Type} (t : Trap E A), bisimilar (cut t) (redec (λ x ∙ snd (top x)) t).
  Proof.
    cofix; intros.
    constructor.
    - rewrite cut_top. reflexivity.
    - rewrite cut_rest. rewrite redec_rest.
      eapply bisimilar_trans.
      apply xxx.
      unfold extend.
      
      apply redec_ext.
      hnf. intros. simpl. unfold extend. rewrite cut_top. simpl.



  (*   cofix; intros. *)
  (*   constructor. *)
  (*   - destruct t; rewrite cut_OK, redec_OK. reflexivity. *)
  (*   - rewrite cut_rest. rewrite redec_rest. *)


  (* CoFixpoint TRI {A B : Type} (f : A → B) (t : tri E A) : tri E B := *)
  (*   match t with *)
  (*     | constr a t' => constr (f a) (TRI (λ x ∙ (fst x, f (snd x))) t') *)
  (*   end. *)

  (* Lemma cut_TRI : ∀ {A B : Type} (t : Trap E A), bisimilar (cut t) (TRI snd t). *)
  (* Proof. *)
  (*   cofix; intros. *)
  (*   constructor. *)
  (*   destruct t. rewrite cut_OK. reflexivity. *)
  (*   rewrite cut_rest. destruct t. simpl. *)


  (* Lemma cut_redec : ∀ (A : Type) (t, cut t ≈ redec (λ x ∙ snd (top x)) t *)

  Definition TAIL_MOR : 𝑴𝑻𝑹𝑰 ⇒ 𝑴𝑻𝑹𝑰_prod.
  Proof.
    refine (Comodule.Morphism.make tail).
    intros C D f. intros x y eq_xy. hnf.
    eapply bisimilar_trans. instantiate (1 := tail D (mcobind 𝑴𝑻𝑹𝑰 f x)).
    apply bisimilar_refl.
    match goal with
      | H : _ |- bisimilar (?t ?r) ?z =>
        let t' := eval simpl in t in change t with t';
        let r' := eval simpl in r in change r with r'
    end. cbv beta.
    eapply bisimilar_trans.
    apply rest_cong.
    apply redec_cong. destruct f. now apply p.
    apply eq_xy.
    rewrite (redec_rest). simpl.
    rewrite redec_rest.
    simpl.
    apply redec_ext.
    hnf. intros t. unfold redecInfiniteTriangles8_4.lift.
    simpl. clear eq_xy. revert y. cofix.
    apply redec_ext.
    hnf. intros t. f_equal.
    f_equal.
    simpl.
    unfold redecInfiniteTriangles8_4.lift.
    f_equal. destruct f. apply p.
    revert t ; cofix.
    intros.
    destruct t.
    rewrite cut_OK, redec_OK.
    simpl. constructor. reflexivity.
    simpl.
    simpl in *.
    specialize (TAIL_MOR (E ⟨×⟩ C)).
    specialize

    destruct t.
    simpl. f_equal. destruct f. simpl. apply p.
    revert a t. cofix.
    intros. rewrite cut_OK. rewrite redec_OK.
    constructor. simpl. reflexivity.
    simpl. destruct t.
    apply TAIL_MOR.
    cofix.
    rewrite cut_OK. rewrite redec_OK. simpl.
    rewrite cut_OK.
    rewrite redec_OK. simpl.

  Program Definition TAIL_MOR : 𝑴𝑻𝑹𝑰 ⇒ 𝑴𝑻𝑹𝑰_prod :=
    Comodule.Morphism.make tail.
  Next Obligation.
    rewrite <- redec_rest.
    match goal with
      | H : _ |- bisimilar ?x ?y => change x with (redec (redecInfiniteTriangles8_4.lift f) (rest x))
    end.
    match goal with
      | _ : _ |- bisimilar ?x ?y => change x with (redec (redecInfiniteTriangles8_4.lift f) (rest x))
    end.
    fold (redec (redecInfiniteTriangles8_4.lift f) (rest x)).
  Proof.
    refine (Comodule.Morphism.make (λ A ∙ @rest E A)).

End Definitions.


(*------------------------------------------------------------------------------
  -- ＴＡＩＬ  ＩＳ  Ａ  ＭＯＲＰＨＩＳＭ  ＯＦ  ＣＯＭＯＤＵＬＥＳ
  ----------------------------------------------------------------------------*)


Section TAIL.

  Variable (E : Type).

  Definition 𝑴𝑻𝑹𝑰 : Comodule (𝑻𝑹𝑰 E) 𝑺𝒆𝒕𝒐𝒊𝒅 :=
    Comodule.make (𝑻𝑹𝑰 E) (λ A B f ∙ (𝑻𝑹𝑰 E)⋅cobind f).