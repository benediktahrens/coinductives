(*----------------------------------------------------------------------------*)
(*    Category of Comodules over Relative Comonads                            *)
(*----------------------------------------------------------------------------*)

Require Import Theory.Category.
Require Import Theory.Functor.
Require Import Theory.RelativeComonad.
Require Import Theory.Comodule.

Generalizable All Variables.

(*
 * Raw category
 *)

Section category_def.

  Context `{F : functor 𝒞 𝒟} (T : relative_comonad F) (ℰ : category).

  Notation RComod := (comodule_rc T ℰ).

  Definition Id (M : RComod) : M ⟹ M := {| M_mor := λ C ∙ id[ M C ] |}.

  Definition Compose (M N P : RComod) (f : N ⟹ P) (g : M ⟹ N) : M ⟹ P :=
    {| M_mor := λ C ∙ (f C) ∘ (g C) |}.

  Definition Eq (M N : RComod) (f g : M ⟹ N) : Prop := ∀ (C : 𝒞), f C ≈ᶜ g C.

  Definition rcomod : category :=
  {| Obj     := RComod
   ; Hom     := _⟹_
   ; id      := Id
   ; compose := Compose
   ; Hom_eq  := Eq |}.

End category_def.

(*
 * IsCategory
 *)
Definition rcomod_IsCategory `{F : Functor 𝒞 𝒟} {T : RelativeComonad F} {ℰ : Category} : IsCategory (rcomod T ℰ).
Proof. constructor.
  - (* Hom_eq_equivalence *)
    intros M N. constructor; hnf; simpl.
    + (* reflexivity *)
      intros f C. reflexivity.
    + (* symmetry *)
      intros f g eq_sym C. symmetry. apply eq_sym.
    + (* transitivity *)
      intros f g h eq_fg eq_gh C. etransitivity. apply eq_fg. apply eq_gh.
  - (* left_id *)
    intros M N f C. simpl. rewrite left_id. reflexivity.
  - (* right_id *)
    intros M N f C. simpl. rewrite right_id. reflexivity.
  - (* assoc *)
    intros M N P Q h g f C; simpl. rewrite compose_assoc. reflexivity.
  - (* compose_cong *)
    intros M N P f₁ f₂ eq_f₁f₂ g₁ g₂ eq_g₁g₂ C. simpl.
    rewrite (eq_f₁f₂ C), (eq_g₁g₂ C). reflexivity.
Qed.

Definition 𝑹𝑪𝒐𝒎𝒐𝒅 `{F : Functor 𝒞 𝒟} (T : RelativeComonad F) (ℰ : Category) : Category :=
  {| _category := rcomod T ℰ
   ; isCategory := rcomod_IsCategory |}.

