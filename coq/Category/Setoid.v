(*----------------------------------------------------------------------------*)
(*    Category of setoids                                                     *)
(*----------------------------------------------------------------------------*)

Require Import Theory.Category.

(*
 * Objects & Morphisms
 *)

Structure SetoidType : Type :=
  { Carrier        :> Type
  ; Carrier_setoid : Setoid Carrier }.

Existing Instance Carrier_setoid.

Structure Setoid_Hom (S₁ S₂ : SetoidType) : Type :=
  { setoid_hom :> S₁ → S₂
  ; setoid_hom_cong : setoid_hom Preserves _≈_ ⟶ _≈_ }.

Arguments setoid_hom_cong {_} {_} _ _ _ _.

Existing Instance setoid_hom_cong.

Notation "_⟶_" := (Setoid_Hom).
Infix "⟶" := Setoid_Hom (at level 70).

(*
 * Trivial Setoid on a type
 *)
Definition FreeSetoid (A : Type) : SetoidType :=
  {| Carrier := A
   ; Carrier_setoid := {| equiv := eq |} |}.

(*
 * Setoid_Hom is a Setoid
 *)
Program Definition SS (S₁ S₂ : SetoidType) : SetoidType :=
  {| Carrier := S₁ ⟶ S₂
   ; Carrier_setoid := {| equiv := λ f g ∙ ∀ {x y}, x ≈ y → f x ≈ g y |} |}.
Next Obligation. constructor.
  + (* reflexivity *)
    hnf. intros f x y eq_xy. rewrite eq_xy; reflexivity.
  + (* symmetry *)
    hnf. intros f g eq_fg x y eq_xy. symmetry in eq_xy; symmetry.
    rewrite eq_fg; eauto.
    reflexivity.
  + (* transitivity *)
    hnf. intros f g h eq_fg eq_gh x y eq_xy.
    etransitivity. apply (eq_fg _ _ eq_xy). apply eq_gh.
    reflexivity.
Defined.

(*----------------------------------------------------------------------------*)

Definition Id (A : SetoidType) : A ⟶ A :=
  {| setoid_hom      := λ x ∙ x
   ; setoid_hom_cong := λ _ _ x ∙ x |}.

Program Definition Compose (A B C : SetoidType) (g : B ⟶ C) (f : A ⟶ B) : A ⟶ C :=
  {| setoid_hom := λ x ∙ g (f x) |}.
Next Obligation.
  intros x y eq_xy. now rewrite eq_xy.
Defined.

(*----------------------------------------------------------------------------*)

(*
 * RawCategory
 *)
Definition Setoid_category : category :=
  {| Obj     := SetoidType
   ; Hom     := _⟶_
   ; id      := Id
   ; compose := Compose
   ; Hom_eq  := λ A B f₁ f₂ ∙ ∀ x y, x ≈ y → f₁ x ≈ f₂ y |}.

(*
 * IsCategory
 *)
Definition Setoid_IsCategory : IsCategory Setoid_category.
Proof. constructor.
  - (* Hom_eq_Equivalence *)
    intros A B; constructor; hnf ; simpl.
    + (* Reflexivity *)
      intros f x y eq_xy. rewrite eq_xy; reflexivity.
    + (* symmetry *)
      intros f g eq_fg x y eq_xy.
      symmetry; apply eq_fg. now symmetry.
    + (* transitivity *)
      intros f g h eq_fg eq_gh x y eq_xy.
      etransitivity; eauto. apply eq_gh. reflexivity.
  - (* left_id *)
    eapply @setoid_hom_cong; eauto.
  - (* right_id *)
    eapply @setoid_hom_cong; eauto.
  - (* assoc *)
    simpl. intros A B C D h g f x y eq_xy; rewrite eq_xy; reflexivity.
  - (* compose_cong *)
    intros A B C f₁ f₂ eq_f₁f₂ g₁ g₂ eq_g₁g₂ x y eq_xy; simpl in *.
    now rewrite eq_xy, eq_g₁g₂, eq_f₁f₂.
Qed.

Definition 𝑺𝒆𝒕𝒐𝒊𝒅 : Category :=
  {| _category := Setoid_category
   ; isCategory  := Setoid_IsCategory |}.
