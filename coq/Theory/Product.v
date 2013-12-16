Require Import Theory.Category.

Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.

(*------------------------------------------------------------------------------
  -- ＰＲＯＤＵＣＴ  ＯＦ  ＯＢＪＥＣＴＳ
  ----------------------------------------------------------------------------*)

Structure Product (𝒞 : Category) (A B : 𝒞) : Type := mkProduct
{ AxB :> 𝒞
; Pmor : ∀ {C : 𝒞}, [ C ⇒ A ⟶ C ⇒ B ⟶ C ⇒ AxB ] where "⟨ f , g ⟩" := (Pmor f g)
; π₁ : AxB ⇒ A
; π₂ : AxB ⇒ B
; π₁_compose : ∀ {C : 𝒞} {f : C ⇒ A} {g : C ⇒ B}, π₁ ∘ ⟨ f , g ⟩ ≈ f
; π₂_compose : ∀ {C : 𝒞} {f : C ⇒ A} {g : C ⇒ B}, π₂ ∘ ⟨ f , g ⟩ ≈ g
; Pmor_universal : ∀ {C : 𝒞} {f : C ⇒ A} {g : C ⇒ B} {i : C ⇒ AxB},
                     π₁ ∘ i ≈ f → π₂ ∘ i ≈ g → i ≈ ⟨ f , g ⟩ }.
Arguments π₁ [𝒞 A B p].
Arguments π₂ [𝒞 A B p].

Notation "⟨ f , g ⟩" := (Pmor _ f g).
Notation "P '⋅π₁'" := (π₁ (p := P)) (at level 0, only parsing).
Notation "P '⋅π₂'" := (π₂ (p := P)) (at level 0, only parsing).
Notation "'π₁[' A , B ]" := (π₁ (A := A) (B := B)) (only parsing).
Notation "'π₂[' A , B ]" := (π₂ (A := A) (B := B)) (only parsing).

(*------------------------------------------------------------------------------
  -- ＨＡＳ  ＢＩＮＡＲＹ  ＰＲＯＤＵＣＴ
  ----------------------------------------------------------------------------*)

Class BinaryProduct (𝒞 : Category) :=
  product : ∀ (A B : 𝒞), Product A B.

Infix "×" := product (at level 20).

Module BinaryProduct.
  Notation make 𝒞 pr prm pr1 pr2 :=
    (λ (A B : 𝒞) ∙ @mkProduct _ A B (pr A B) (λ C ∙ Π₂.make (prm C)) pr1 pr2 _ _ _).
End BinaryProduct.


(*------------------------------------------------------------------------------
  -- ＰＲＯＤＵＣＴ  ＬＡＷＳ
  ----------------------------------------------------------------------------*)

Definition prod_mor `{BinaryProduct 𝒞} `(f : A ⇒ A') `(g : B ⇒ B') : A × B ⇒ A' × B' :=
  ⟨ f ∘ π₁ , g ∘ π₂ ⟩.

Infix "-×-" := prod_mor (at level 35).

Lemma product_postcompose `{BinaryProduct 𝒞} {A B C C' : 𝒞} {f : B ⇒ C} {g : B ⇒ C'} {p : A ⇒ B} :
   ⟨ f , g ⟩ ∘ p ≈ ⟨ f ∘ p , g ∘ p ⟩    :> A ⇒ C × C'.
Proof.
  apply Pmor_universal.
  - rewrite <- compose_assoc. now rewrite π₁_compose.
  - rewrite <- compose_assoc. now rewrite π₂_compose.
Qed.

Lemma product_precompose `{BinaryProduct 𝒞} {A B C D E : 𝒞}
      {f : B ⇒ D} {g : C ⇒ E} {h : A ⇒ B} {k : A ⇒ C} : f-×-g ∘ ⟨ h , k ⟩ ≈ ⟨ f ∘ h , g ∘ k ⟩    :> A ⇒ D × E.
Proof.
  apply Pmor_universal.
  - rewrite <- compose_assoc. unfold "-×-". rewrite π₁_compose. rewrite compose_assoc. now rewrite π₁_compose.
  - rewrite <- compose_assoc. unfold "-×-". rewrite π₂_compose. rewrite compose_assoc. now rewrite π₂_compose.
Qed.

Notation "∘-×" := product_postcompose (only parsing).
Notation "×-∘" := product_precompose  (only parsing).
