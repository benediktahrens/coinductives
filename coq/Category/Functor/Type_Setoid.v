(*----------------------------------------------------------------------------*)
(*    Free functor betwen 𝑻𝒚𝒑𝒆 and 𝑺𝒆𝒕𝒐𝒊𝒅                                      *)
(*----------------------------------------------------------------------------*)

Require Import Theory.Category.
Require Import Theory.Functor.
Require Import Category.Type.
Require Import Category.Setoid.

(*
 * RawFunctor
 *)
Program Definition TS_RawFunctor : RawFunctor 𝑻𝒚𝒑𝒆 𝑺𝒆𝒕𝒐𝒊𝒅 :=
  {| Fobj := FreeSetoid
   ; Fhom := λ A B f ∙ {| setoid_hom := f |} |}.

(*
 * IsFunctor
 *)
Definition TS_IsFunctor : IsFunctor TS_RawFunctor.
Proof. constructor.
  + (* identity *)
    intros X. simpl; auto.
  + (* resp_compose *)
    intros A B C g f; simpl.
    intros x y eq_xy; now rewrite eq_xy.
  + (* Fhom_cong *)
    intros A B f g eq_fg; simpl.
    intros x y eq_xy. now rewrite eq_xy.
Defined.

Definition TS : Functor 𝑻𝒚𝒑𝒆 𝑺𝒆𝒕𝒐𝒊𝒅 :=
  {| rawFunctor := TS_RawFunctor
   ; isFunctor  := TS_IsFunctor |}.

Notation "'𝑻𝒚𝒑𝒆⟹𝑺𝒆𝒕𝒐𝒊𝒅'" := TS.