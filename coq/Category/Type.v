(*----------------------------------------------------------------------------*)
(*    Category of types                                                       *)
(*----------------------------------------------------------------------------*)

Require Import Theory.Category.

(*
 * RawCategory
 *)
Definition Type_category : category :=
  {| Obj     := Type
   ; Hom     := λ A B ∙ A → B
   ; id      := λ A x ∙ x
   ; compose := λ A B C f g x ∙ f (g x)
   ; Hom_eq  := λ A B f₁ f₂ ∙ ∀ x, f₁ x = f₂ x |}.

(*
 * IsCategory
 *)
Definition Type_IsCategory : IsCategory Type_category.
Proof. constructor.
  + (* Hom_eq_Equivalence *)
    intros A B; constructor; hnf; simpl; [ reflexivity | now symmetry | etransitivity ; eauto].
  + (* left_id *)
    now simpl.
  + (* right_id *)
    now simpl.
  + (* assoc *)
    now simpl.
  + (* compose_cong *)
    intros A B C f₁ f₂ eq_f₁f₂ g₁ g₂ eq_g₁g₂ x; simpl in *.
    now rewrite eq_g₁g₂, eq_f₁f₂.
Qed.

Definition 𝑻𝒚𝒑𝒆 : Category := {| _category := Type_category
                              ; isCategory   := Type_IsCategory |}.
