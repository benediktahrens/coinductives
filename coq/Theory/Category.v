(*----------------------------------------------------------------------------*)
(*    Category definition                                                     *)
(*----------------------------------------------------------------------------*)

Require Export Misc.Unicode.
Require Export Theory.Notations.
Require Export SetoidClass.

(*
 * Category structure without laws
 *)
Structure category : Type :=
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

(* Notations for equality on RawCategory *)
Notation "_≈ᶜ_" := Hom_eq.
Infix "≈ᶜ"      := Hom_eq (at level 70).
Notation "x ≈ᶜ y :> C [ A , B ]" := (@Hom_eq C A B x y) (at level 70, y at next level).

(*
 * Laws on RawCategory
 *)
Class IsCategory (𝒞 : category) : Prop :=
  { Hom_eq_Equivalence :> ∀ {A B : 𝒞}, Equivalence (@Hom_eq _ A B)
  ; left_id            : ∀ {A B : 𝒞} {f : A ⇒ B}, id ∘ f ≈ᶜ f
  ; right_id           : ∀ {A B : 𝒞} {f : A ⇒ B}, f ∘ id ≈ᶜ f
  ; compose_assoc      : ∀ {A B C D : 𝒞} {h : C ⇒ D} {g : B ⇒ C} {f : A ⇒ B}, h ∘ g ∘ f ≈ᶜ h ∘ (g ∘ f)
  ; compose_cong       :> ∀ {A B C : 𝒞}, (@compose _ A B C) Preserves₂ _≈ᶜ_ ⟶ _≈ᶜ_ ⟶ _≈ᶜ_ }.

Instance: ∀ {𝒞 : category}, IsCategory 𝒞 → ∀ {A B : 𝒞}, Setoid (A ⇒ B) := { equiv := Hom_eq }.

Export SetoidNotations.

(*
 * Category
 *)

Structure Category : Type :=
  { _category :> category
  ; isCategory : IsCategory _category }.

Existing Instance isCategory.

(*
 * Notation for morphisms
 *)
Class Morphism (A : Type) : Type :=
  mor : A → A → Type.

Notation "_⟹_" := mor.
Infix "⟹"      := mor (at level 60, right associativity).

Instance: ∀ (𝒞 : category), Morphism 𝒞 := λ 𝒞 ∙ Hom (c := 𝒞).