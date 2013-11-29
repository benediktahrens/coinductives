(*----------------------------------------------------------------------------*)
(*    Notations                                                               *)
(*----------------------------------------------------------------------------*)

(*
 * Core Notations
 *)
Notation "⊤" := True.
Notation "⊥" := False.
Infix "⊎" := sum (at level 50, left associativity).
Infix "×" := prod (at level 40, left associativity).

Notation "'Rel' A" := (A -> A -> Prop) (at level 70, only parsing).

(*
 * Equality on setoids (overloads)
 *)
Require Import SetoidClass.

Notation "f 'Preserves' r₁ ⟶ r₂" := (Proper (r₁ ==> r₂) f) (at level 70, no associativity).
Notation "f 'Preserves₂' r₁ ⟶ r₂ ⟶ r₃" := (Proper (r₁ ==> r₂ ==> r₃) f) (at level 70, no associativity).

Module SetoidNotations.
  Notation "_≈_" := equiv                    (only parsing).
  Notation "x ≈ y" := (equiv x y)            (at level 70, no associativity).
  Notation "x ≉ y" := (complement equiv x y) (at level 70, no associativity).
End SetoidNotations.

(*
 * Morphism & composition
 *)

Reserved Notation "A ⇒ B" (at level 30, right associativity).
Reserved Notation "f ∘ g" (at level 40, left associativity).
