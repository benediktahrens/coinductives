(*----------------------------------------------------------------------------*)
(*    Category of Relative Comonads                                           *)
(*----------------------------------------------------------------------------*)

Require Import Theory.Category.
Require Import Theory.Functor.
Require Import Theory.RelativeComonad.

Generalizable All Variables.

(*
 * Raw category
 *)

Section category_def.

  Context `(F : functor 𝒞 𝒟).

  Notation RComonad := (relative_comonad F).

  Definition Id (T : RComonad) : T ⟹ T := {| T_mor := λ C ∙ id[ T C ] |}.

  Definition Compose (M N P : RComonad) (f : N ⟹ P) (g : M ⟹ N) : M ⟹ P :=
    {| T_mor := λ C ∙ (f C) ∘ (g C) |}.

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
