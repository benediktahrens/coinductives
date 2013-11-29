(*----------------------------------------------------------------------------*)
(*    Category definition                                                     *)
(*----------------------------------------------------------------------------*)

Require Export Misc.Unicode.
Require Export Theory.Notations.
Require Export SetoidClass.

(*
 * Category structure without laws
 *)
Structure RawCategory : Type :=
  { Obj     :> Type
  ; Hom     : Obj → Obj → Type where "A ⇒ B" := (Hom A B)
  ; id      : ∀ {A}, A ⇒ A
  ; compose : ∀ {A B C}, B ⇒ C → A ⇒ B → A ⇒ C
  ; Hom_eq  : ∀ {A B}, Rel (A ⇒ B) }.

Arguments Hom     {_} _ _ , _ _ _.
Arguments id      {_} {_}.
Arguments compose {_} {A B C} _ _.
Arguments Hom_eq  {_} {A B} _ _, _ {A B} _ _.

Notation "_∘_" := compose.
Infix "∘"      := compose.

Notation "_⇒_" := Hom.
Infix "⇒"      := Hom.

Notation "'id[' X ]" := (@id _ X) (only parsing).

Local Notation "_≈_" := Hom_eq.
Local Infix "≈"      := Hom_eq (at level 70).

(*
 * Laws on RawCategory
 *)
Class IsCategory (𝒞 : RawCategory) : Prop :=
  { Hom_eq_Equivalence :> ∀ {A B : 𝒞}, Equivalence (@Hom_eq _ A B)
  ; left_id            : ∀ {A B : 𝒞} {f : A ⇒ B}, id ∘ f ≈ f
  ; right_id           : ∀ {A B : 𝒞} {f : A ⇒ B}, f ∘ id ≈ f
  ; compose_assoc      : ∀ {A B C D : 𝒞} {h : C ⇒ D} {g : B ⇒ C} {f : A ⇒ B}, h ∘ g ∘ f ≈ h ∘ (g ∘ f)
  ; compose_cong       :> ∀ {A B C : 𝒞}, (@compose _ A B C) Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_ }.

Instance: ∀ {𝒞 : RawCategory}, IsCategory 𝒞 → ∀ {A B : 𝒞}, Setoid (A ⇒ B) := { equiv := Hom_eq }.

Export SetoidNotations.

(*
 * Category
 *)

Structure Category : Type :=
  { rawCategory :> RawCategory
  ; isCategory : IsCategory rawCategory }.

Existing Instance isCategory.