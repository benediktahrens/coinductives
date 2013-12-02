(*----------------------------------------------------------------------------*)
(*    Redecoration is a relative comonad on 𝑻𝒚𝒑𝒆⟹𝑺𝒆𝒕𝒐𝒊𝒅                       *)
(*----------------------------------------------------------------------------*)

Require Import InfiniteTriangles.redecInfiniteTriangles8_4.
Require Import Theory.Category.
Require Import Theory.Functor.
Require Import Theory.RelativeComonad.
Require Import Category.Type.
Require Import Category.Setoid.
Require Import Category.Functor.Type_Setoid.

Section RComonad_def.

  Variable E : Type.

  Program Definition TriSetoid (A : Type) : SetoidType :=
    {| Carrier := Tri E A ; Carrier_setoid := {| equiv := @bisimilar _ _ |} |}.
  Next Obligation.
    constructor.
    + apply bisimilar_refl.
    + apply bisimilar_sym.
    + apply bisimilar_trans.
  Defined.

  Program Definition TopSetoid (X : 𝑻𝒚𝒑𝒆) : TriSetoid X ⟹ FreeSetoid X :=
    {| setoid_hom := @top E X |}.
  Next Obligation.
    hnf. apply top_cong.
  Defined.

  Program Definition RedecSetoid (X Y : 𝑻𝒚𝒑𝒆) (F : TriSetoid X ⟹ FreeSetoid Y) : TriSetoid X ⟹ TriSetoid Y :=
    {| setoid_hom := @redec E X Y F |}.
  Next Obligation.
    hnf in *; simpl in *.
    apply redec_cong.
    hnf. apply F.(setoid_hom_cong).
  Defined.

  Program Definition IT : relative_comonad 𝑻𝒚𝒑𝒆⟹𝑺𝒆𝒕𝒐𝒊𝒅 :=
    {| T := TriSetoid
     ; counit := TopSetoid
     ; cobind := RedecSetoid |}.

  Definition IT_isRelativeComonad : IsRelativeComonad IT.
  Proof. constructor.
    - (* cobind_counit *)
      intro X. simpl.
      intros x y eq_xy. eapply bisimilar_trans.
      apply comonad2. exact eq_xy.
    - (* counit_cobind *)
      simpl. intros X Y f x y eq_xy. apply f.(setoid_hom_cong). exact eq_xy.
    - (* cobind_assoc *)
      intros X Y Z f g x y eq_xy. simpl.
      apply bisimilar_sym. eapply bisimilar_trans.
      apply comonad3. apply g.(setoid_hom_cong).
      apply redec_cong. apply g.(setoid_hom_cong).
      apply redec_cong. apply f.(setoid_hom_cong).
      apply bisimilar_sym; exact eq_xy.
    - (* cobind_cong *)
      intros X Y f g eq_fg x y eq_xy; simpl.
      eapply bisimilar_trans.
      apply redec_ext. intro t. apply eq_fg. apply bisimilar_refl.
      apply redec_cong. apply g.(setoid_hom_cong). exact eq_xy.
  Qed.

  Definition 𝑅𝑒𝑑𝑒𝑐 : RelativeComonad 𝑻𝒚𝒑𝒆⟹𝑺𝒆𝒕𝒐𝒊𝒅 :=
    {| _relative_comonad := IT
     ; isRelativeComonad  := IT_isRelativeComonad |}.

End RComonad_def.
