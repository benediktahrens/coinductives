Require Import Category.Setoid.
Require Import Category.Type.
Require Import Category.Functor.Type_Setoid.
Require Import Theory.Category.
Require Import Theory.Functor.
Require Import Theory.RelativeComonad.
Require Import Theory.Comodule.
Require Import Category.RComod.
Require Import Theory.Product.
Require Import ProductInContext.

Set Implicit Arguments.
Generalizable All Variables.

(** Tri functor **)
Section Triangles.

  (** pointwise equality **)
  Definition pointwise_eq {A B : Type} (f g : A → B) : Prop := ∀ x, f x = g x.
  Notation "_≗_" := pointwise_eq.
  Infix "≗" := pointwise_eq (at level 70).

  Global Instance pointwise_Equivalence : ∀ {A B}, Equivalence (@pointwise_eq A B).
  Proof.
    admit.
  Qed.

  Variable E: Type. (* fixed throughout *)

  CoInductive tri (A: Type): Type :=
    constr: A -> tri(E ⟨×⟩ A) -> tri A.

  (** the datatype of trapeziums *)
  Definition Trap A := tri(E ⟨×⟩ A).

  (** destructors **)
  (* Definition top A (t: tri A): A := *)
  Definition top A : tri A → A :=
    λ t ∙ match t with constr a _ => a end.

  Definition rest A : tri A → Trap A :=
    λ t ∙ match t with constr _ r => r end.

  (** Bisimulation **)
  CoInductive bisimilar: forall {A}, tri A -> tri A -> Prop :=
    constrB: forall {A: Type}{t t': tri A},
               top t = top t' -> bisimilar (rest t) (rest t') -> bisimilar t t'.

  Notation "_∼_" := bisimilar.
  Infix "∼" := bisimilar (at level 70).

  Definition pointwise_bisim {A B} (f g : tri A → B) := ∀ t t', t ∼ t' → f t = g t'.

  Global Instance pointwise_bisim_Equivalence : ∀ {A B}, Equivalence (@pointwise_bisim A B).
  Proof.
    admit.
  Qed.

  Notation "_∼≗_" := pointwise_bisim.
  Infix "∼≗" := pointwise_bisim (at level 70).

  Lemma bisimilar_refl : ∀ A, Reflexive (@bisimilar A).
  Proof.
    cofix COFIX; repeat intro.
    constructor.
    - reflexivity.
    - now apply COFIX.
  Qed.

  Lemma bisimilar_sym : forall A, Symmetric (@bisimilar A).
  Proof.
    cofix COFIX; repeat intro.
    constructor.
    - now destruct H.
    - destruct H. now apply COFIX.
  Qed.

  Lemma bisimilar_trans : forall A, Transitive (@bisimilar A).
  Proof.
  cofix COFIX; repeat intro.
  constructor.
  - destruct H, H0. etransitivity; eauto.
  - destruct H, H0. eapply COFIX; eauto.
  Qed.

  Global Instance bisimilar_Equivalence : ∀ A, Equivalence (@bisimilar A).
  Proof.
    constructor.
    - apply bisimilar_refl.
    - apply bisimilar_sym.
    - apply bisimilar_trans.
  Qed.

  Ltac prove_bisim :=
    let C := fresh "COFIX" in cofix C; intros;
    constructor; autorewrite with coind; [|try apply C].

  Notation "f ≗ g" := (∀ x, f x = g x) (at level 70).

  (** Functor **)

  Definition Prod_fun {A A' B B'} (f : A → A') (g : B → B') : A ⟨×⟩ B → A' ⟨×⟩ B' :=
    λ x ∙ (f (fst x), g (snd x)).

  Notation "f -⟨×⟩- g" := (Prod_fun f g) (at level 70).

  CoFixpoint map {A B} (f : A → B) : tri A → tri B :=
    λ t ∙ constr (f (top t)) (map ((λ x ∙ x) -⟨×⟩- f) (rest t)).

  Lemma top_map {A B} (f : A → B) (t : tri A) : top (map f t) = f (top t).
  Proof.
    reflexivity.
  Qed.

  Lemma rest_map {A B} (f : A → B) (t : tri A) : rest (map f t) = map ((λ x ∙ x) -⟨×⟩- f) (rest t).
  Proof.
    reflexivity.
  Qed.

  Hint Rewrite -> @top_map : coind.
  Hint Rewrite -> @rest_map : coind.

  Global Instance map_cong : ∀ {A B}, Proper (_≗_ ==> _∼_ ==> _∼_) (@map A B).
  Proof.
    prove_bisim.
    - destruct H0. rewrite H0; now apply H.
    - intros [u v]. unfold Prod_fun; congruence.
    - now destruct H0.
  Qed.

  Lemma map_id' : ∀ A (f : A → A) (t : tri A), f ≗ (λ x ∙ x) → map f t ∼ t.
  Proof.
    prove_bisim.
    - apply H.
    - unfold Prod_fun. intros [? ?]. now f_equal.
  Qed.

  Lemma map_id : ∀ A (f : A → A) (t : tri A), map (λ x ∙ x) t ∼ t.
  Proof.
    intros. apply map_id'. reflexivity.
  Qed.

  Lemma map_compose' : ∀ A B C (h : A → C) (g : B → C) (f : A → B) t,
                         h ≗ (λ x ∙ g (f x)) → map h t ∼ map g (map f t).
  Proof.
    prove_bisim.
    - apply H.
    - intros [u v]; unfold Prod_fun. simpl. f_equal. apply H.
  Qed.

  Lemma map_compose : ∀ A B C (h : A → C) (g : B → C) (f : A → B) t,
                         map (λ x ∙ g (f x)) t ∼ map g (map f t).
  Proof.
    intros; now apply map_compose'.
  Qed.

  Definition extend {A B} (f : tri A → B) (r : tri (E ⟨×⟩ A)) : E ⟨×⟩ B :=
    (fst (top r), f (map snd r)).

  Lemma extend_top {A} : extend (top (A := A)) ≗ top(A := E ⟨×⟩ A).
  Proof.
    intros [[e a] r].
    reflexivity.
  Qed.

  CoFixpoint redec {A B} (f : tri A → B) (t : tri A) : tri B :=
    constr (f t) (redec (extend f) (rest t)).

  Lemma top_redec : ∀ A B (f : tri A → B) t, top (redec f t) = f t.
  Proof.
    reflexivity.
  Qed.

  Lemma rest_redec : ∀ A B (f : tri A → B) t, rest(redec f t) = redec (extend f) (rest t).
  Proof.
    reflexivity.
  Qed.

  Hint Rewrite -> @top_redec : coind.
  Hint Rewrite -> @rest_redec : coind.

  Global Instance extend_cong : ∀ {A B}, Proper (_∼≗_ ==> _∼_ ==> eq) (@extend A B).
  Proof.
    intros A B f g eq_fg t t' eq_tt'. unfold extend.
    f_equal.
    - f_equal; now destruct eq_tt'.
    - apply eq_fg. now rewrite eq_tt'.
  Qed.

  Lemma extend_ext : ∀ {A B} {f g : tri A → B}, f ≗ g → extend f ≗ extend g.
  Proof.
    intros. destruct x as [ea r].
    unfold extend.
    now rewrite H.
  Qed.

  Global Instance redec_cong : ∀ {A B}, Proper (_∼≗_ ==> _∼_ ==> _∼_) (@redec A B).
  Proof.
    prove_bisim.
    - now apply H.
    - now apply extend_cong.
    - now destruct H0.
  Qed.

  Lemma comonad2' : ∀ {A} (f : tri A → A) (t : tri A), f ≗ (@top A) → redec f t ∼ t.
  Proof.
    prove_bisim.
    - now apply H.
    - etransitivity. eapply extend_ext. apply H. apply extend_top.
  Qed.

  Lemma comonad2 : ∀ {A} (t : tri A), redec (top (A := A)) t ∼ t.
  Proof.
    intros; now apply comonad2'.
  Qed.

  Definition Lift {A B} (f : A → B) (t : tri A) : tri B :=
    redec (λ x ∙ f (top x)) t.

  Lemma top_Lift : ∀ {A B} (f : A → B) (t : tri A), top (Lift f t) = f (top t).
  Proof.
    reflexivity.
  Qed.

  Lemma rest_Lift : ∀ {A B} (f : A → B) (t : tri A), rest(Lift f t) = Lift (λ x ∙ (fst x, f (snd x))) (rest t).
  Proof.
    reflexivity.
  Qed.

  Hint Rewrite -> @top_Lift : coind.
  Hint Rewrite -> @rest_Lift : coind.

  Lemma lift_map : ∀ {A B} (f : A → B) (t : tri A),
                     Lift f t ∼ map f t.
  Proof.
    prove_bisim.
    reflexivity.
  Qed.

  Definition fcompat A B (f : tri A → B) : Prop := ∀ t t', t ∼ t' → f t = f t'.

  CoFixpoint cut A (t : Trap A) : tri A :=
    constr (snd (top t)) (cut (rest t)).

  Lemma top_cut : ∀ A (t : Trap A), top (cut t) = snd (top t).
  Proof.
    reflexivity.
  Qed.

  Lemma rest_cut : ∀ A (t : Trap A), rest (cut t) = cut (rest t).
  Proof.
    reflexivity.
  Qed.

  Hint Rewrite -> @top_cut : coind.
  Hint Rewrite -> @rest_cut : coind.

  (* Lemma cut_map : ∀ A (f : tri (E ⟨×⟩ A) → A) (t : Trap A), *)
  (*                   (∀ t, f t = snd (top t)) → cut t ∼ redec f t. *)
  (* Proof. *)
  (*   cofix Hc; intros. *)
  (*   constructor. *)
  (*   - simpl. symmetry. apply H. *)
  (*   - simpl. apply Hc. *)
  (*     intros. unfold extend. destruct t0. *)
  (*     simpl. *)
  (*     rewrite H. simpl. *)
  (*     destruct p. *)
  (*     simpl. destruct p. simpl. f_equal. *)

  (*     intros [[e a] r]. unfold extend. simpl. destruct a. simpl. *)
  (*     unfold extend. *)
  (*     specialize (Hc (E ⟨×⟩ A)). *)

  (*     apply Hc. *)


  (* Lemma rest_cut : ∀ A (t : tri (E ⟨×⟩ A)), rest (cut t) = cut (rest t). *)
  (* Proof. *)
  (*   intros. *)
  (*   unfold cut at 1. *)
  (*   rewrite rest_map. unfold cut. unfold Prod_fun. *)

(*   Proof. *)
(*     cofix Hc. *)
(*     intros A B f [[e a] t]. *)
(*     constructor. *)
(*     - reflexivity. *)
(*     - simpl. *)
(*       unfold cut in Hc. *)
(*       unfold extend at 3.  *)
(*     prove_bisim. *)
(*     - simpl. reflexivity. *)
(*     -  *)
(*   cofix Hc. *)
(*   intros A B f [[e a] t]. *)
(*   apply constrB; simpl. *)
(*   reflexivity. *)
(*   apply Hc. *)
(* Qed. *)

  (* Lemma xxxx : ∀ A B C (f : tri A → B) (g : E ⟨×⟩ B → B) (t : tri (E ⟨×⟩ A)), *)
  (*                Lift g (redec (extend f) t) ∼ redec f (Lift g t). *)

  Lemma xxxx : ∀ A B (f : tri A → B) (gA : E ⟨×⟩ A → A) (gB : E ⟨×⟩ B → B) (t : tri (E ⟨×⟩ A)), 
                 fcompat f →
                 gA ≗ snd → gB ≗ snd → redec f (map gA t) ∼ map gB (redec (extend f) t).
  Proof.
    cofix Hc. intros.
    constructor.
    - admit.
    - autorewrite with coind.
      unfold Prod_fun.
      apply Hc.
      admit.
    prove_bisim.
    - rewrite H1. apply H. now apply map_cong.
    - admit.
    - rewrite H0. simpl. f_equal.
    - reflexivity.
    - apply COFIX.

  Lemma extend_redec : ∀ A B C (f: tri A → B) (g : tri B → C),
                         fcompat g → extend (λ x ∙ g (redec f x)) ≗ λ x ∙ extend g (redec (extend f) x).
  Proof.
    intros.
    unfold extend. simpl.
    f_equal. apply H.

    intros.
  Admitted.


  (* Lemma xxx : ∀ A B C (x : A ⟨×⟩ (B ⟨×⟩ C)), snd (snd x) = snd ((λ x ∙ ((fst x, fst (snd x)), snd (snd x))) x). *)
  (* Proof. *)
  (*   intros A B C [x [y z]]. *)
  (*   simpl. reflexivity. *)

  Lemma comonad3' : ∀ A B C (f : tri A → B) (g : tri B → C) (h : tri A → C) (t : tri A),
                       fcompat g → h ∼≗ (λ x ∙ g (redec f x)) → redec h t ∼ redec g (redec f t).
  Proof.
    prove_bisim.
    - apply H0. reflexivity.
    - admit.
    - 
    cofix Hc; intros.
    (* assert (extend_redec' : ∀ A B C (f : tri A → B) (g : tri B → C), *)
    (*                        fcompat g → extend (λ x ∙ g (redec f x)) ≗ λ x ∙ extend g (redec (extend f) x)). *)
    (* intros. *)
    unfold 
    constructor.
    - simpl. now apply H0.
    - simpl.
      apply Hc.
      admit.
  extend_redec' : ∀ A B C (f : tri A → B) (g : tri B → C),
                           fcompat g → extend (λ x ∙ g (redec f x)) ≗ λ x ∙ extend g (redec (extend f) x).


    intr
    prove_bisim.
    - apply H0. reflexivity.
    - intros u v eq_uv. apply extend_cong. apply H. apply eq_uv.
    - 
    - intros u v eq_uv. etransitivity. eapply extend_cong. apply H0. apply eq_uv.
      now rewrite extend_redec.
  Qed.

  Lemma comonad3 : ∀ A B C (f : tri A → B) (g : tri B → C) (t : tri A),
                       fcompat g → redec (λ x ∙ g (redec f x)) t ∼ redec g (redec f t).
  Proof.
    intros. apply comonad3'.
    apply H.
    reflexivity.
  Qed.

End Triangles.