(*----------------------------------------------------------------------------*)
(*    Category of Relative Comonads                                           *)
(*----------------------------------------------------------------------------*)

Require Import Theory.Category.
Require Import Theory.Functor.
Require Import Theory.RelativeComonad.
Require Import Setoid.

Generalizable All Variables.

(*
 * Raw category
 *)

Section category_def.

  Context `(F : Functor 𝒞 𝒟).

  Notation RComonad := (RelativeComonad F).

  Definition Id (T : RComonad) : T ⟹ T.
    constructor 1 with {| T_mor := λ C ∙ id[ T C ] |}.
    abstract (
        (* IsRelativeComonadMor *) constructor;
        [ (* T_mor_counit *)
          intro C; simpl; rewrite right_id; reflexivity
        | (* T_mor_cobind *)
          intros C D f; simpl; rewrite left_id; do 2 rewrite right_id; reflexivity ]
    ).
  Defined.

  Definition Compose (M N P : RComonad) (f : N ⟹ P) (g : M ⟹ N) : M ⟹ P.
    constructor 1 with {| T_mor := λ C ∙ (f C) ∘ (g C) |}.
    abstract (
        (* IsRelativeComonadMor *) constructor;
        [ (* T_mor_counit *)
          intros C; simpl; rewrite <- compose_assoc;
          do 2 rewrite <- T_mor_counit; reflexivity
        | (* T_mor_cobind *)
        intros C D h; simpl; setoid_rewrite <- compose_assoc at 2;
        rewrite <- T_mor_commutes; rewrite compose_assoc;
        setoid_rewrite <- compose_assoc at 2; rewrite T_mor_commutes;
        rewrite <- compose_assoc; reflexivity ]
    ).
  Defined.

  Definition Eq (M N : RComonad) (f g : M ⟹ N) : Prop := ∀ (C : 𝒞), f C ≈ᶜ g C.

  Definition rcomonad : category :=
  {| Obj     := RComonad
   ; Hom     := _⟹_
   ; id      := Id
   ; compose := Compose
   ; Hom_eq  := Eq |}.

End category_def.

(*
 * IsCategory
 *)
Definition rcomonad_IsCategory `{F : Functor 𝒞 𝒟} : IsCategory (rcomonad F).
Proof. constructor.
  - (* Hom_eq_equivalence *)
    intros T S. constructor; hnf; simpl.
    + (* reflexivity *)
      intros f C. reflexivity.
    + (* symmetry *)
      intros f g eq_sym C. symmetry. apply eq_sym.
    + (* transitivity *)
      intros f g h eq_fg eq_gh C. etransitivity. apply eq_fg. apply eq_gh.
  - (* left_id *)
    intros T S f C. simpl. rewrite left_id. reflexivity.
  - (* right_id *)
    intros T S f C. simpl. rewrite right_id. reflexivity.
  - (* assoc *)
    intros T S P Q h g f C; simpl. rewrite compose_assoc. reflexivity.
  - (* compose_cong *)
    intros T S U f₁ f₂ eq_f₁f₂ g₁ g₂ eq_g₁g₂ C. simpl.
    rewrite (eq_f₁f₂ C), (eq_g₁g₂ C). reflexivity.
Qed.

Definition 𝑹𝑪𝒐𝒎𝒐𝒏𝒂𝒅 `(F : Functor 𝒞 𝒟) : Category :=
  {| _category := rcomonad F
   ; isCategory := rcomonad_IsCategory |}.
