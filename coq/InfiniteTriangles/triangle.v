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

End Triangles.