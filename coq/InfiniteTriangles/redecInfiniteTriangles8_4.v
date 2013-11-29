(* tested with Coq 8.4 *)

(* Copyright 2012, Ralph Matthes and Celia Picard, IRIT, CNRS & Université de Toulouse *)

Set Implicit Arguments.
Require Import Utf8. (* just for displaying purposes *)
Require Import Streams. (* this hides hd of List *)
Require Import Setoid.
Require Import SetoidTactics.

Require Import Relations.
Require Import Morphisms.

Section TriangleDef.

Variable E: Type. (* fixed throughout *)

Open Scope type_scope. (* asterisk is interpreted as product of types *)

(** the datatype of triangles *)

CoInductive Tri (A: Type): Type :=
  constr: A -> Tri(E * A) -> Tri A.

(** the datatype of trapeziums *)

Definition Trap (A: Type) := Tri(E * A).

Check constr: forall A: Type, A -> Trap A -> Tri A.

Definition top (A: Type) (t: Tri A): A :=
  match t with constr a _ => a end.

Definition rest (A: Type) (t: Tri A): Trap A :=
  match t with constr _ r => r end.

Lemma toprestOK (A: Type) (t: Tri A):
  t = constr (top t) (rest t).
Proof.
  destruct t as [a r].
  reflexivity.
Qed.

(** cutting off the top row *)

CoFixpoint cut (A: Type) (t: Trap A): Tri A := match t with constr (e, a) r => constr a (cut r) end.

Lemma cut_top (A: Type) (t: Trap A): top(cut t) = snd(top t).
Proof.
  destruct t as [[e a] r].
  reflexivity.
Qed.

Lemma cut_rest  (A: Type) (t: Trap A): rest(cut t) = cut(rest t).
Proof.
  destruct t as [[e a] r].
  reflexivity.
Qed.

Lemma cut_OK (A: Type)(ea: E * A)(r: Trap(E * A)): cut (constr ea r) = constr (snd ea) (cut r).
Proof.
  destruct ea as [e a].
  rewrite (toprestOK (cut (constr (e, a) r))).
  reflexivity.
Qed.

Lemma cut_OK_eager (A: Type) (t: Trap A): cut t = constr (snd (top t)) (cut (rest t)).
Proof.
  destruct t as [ea r].
  apply cut_OK.
Qed.

(** lifting a redecoration rule from triangles to trapeziums *)

Definition lift (A B: Type) (f: Tri A -> B) (r: Trap A) : E * B := (fst(top r), f(cut r)).

(* pattern-matching version - not ideal for computation
CoFixpoint redec (A B: Type) (f: Tri A -> B) (t: Tri A): Tri B :=
  match t with
    constr a r => constr (f t) (redec (lift f) r)
  end.
*)

(** the short and elegant definition with the nested datatype *)
CoFixpoint redec (A B: Type) (f: Tri A -> B) (t: Tri A): Tri B := 
  constr (f t) (redec (lift f) (rest t)).

Lemma comonad1 (A B: Type) (f: Tri A -> B) (t: Tri A): top(redec f t) = f t.
Proof.
  reflexivity.
Qed.

Lemma redec_rest (A B: Type) (f: Tri A -> B) (t: Tri A):
  rest(redec f t) = redec (lift f) (rest t).
Proof.
  reflexivity.
Qed.

Lemma redec_OK (A B: Type) (f: Tri A -> B) (a: A) (r: Trap A): redec f (constr a r) = 
  constr (f (constr a r)) (redec (lift f) r).
Proof.
  rewrite (toprestOK (redec f (constr a r))).
  reflexivity.
Qed.


(** printing ~~ %\ensuremath{\simeq}% *)
(** printing t' %\ensuremath{t'}% *)

(* the canonical notion of bisimilarity on Tri *)

CoInductive bisimilar: forall A, Tri A -> Tri A -> Prop :=
  constrB: forall (A: Type)(t t': Tri A), 
    top t = top t' -> bisimilar (rest t) (rest t') -> bisimilar t t'.
(* begin hide *)
Infix "~~" := bisimilar (at level 60).
(* end hide *)

(** The relation [bisimilar] is displayed as the infix $\simeq$#~~#. *)
(** printing a' %\ensuremath{a'}% *)

(* what cut exactly cuts out *)

CoFixpoint es_cut (A: Type) (t: Trap A): Stream E :=
  match t with 
    constr (e, a) r => Cons e (es_cut r) 
  end.

CoFixpoint add_es (A: Type)(es: Stream E)(t: Tri A): Trap A := 
  match es, t with 
    Cons e es', constr a r => constr (e, a) (add_es es' r) 
  end.

(* already the following lemma cannot be expected to hold with Leibniz equality *)

Lemma es_cut_reconstr (A: Type)(t: Trap A): add_es (es_cut t) (cut t) ~~ t.
Proof.
  revert A t ; cofix Hc ; intros A [[e a] r].
  apply constrB.
  reflexivity.
  simpl.
  apply Hc.
Qed.

Lemma cut_add_es (A: Type)(es: Stream E)(t: Tri A): cut (add_es es t) ~~ t.
Proof.
  revert A es t; cofix Hc; intros A [e es] [a r].
  apply constrB; simpl.
  reflexivity.
  apply Hc.
Qed.

(* inversion lemmas for constrB *)

Lemma bisimilar_injr (A: Type) (a a': A) (t t': Trap A):
  constr a t ~~ constr a' t' -> t ~~ t'.
Proof.
  intros H.
  refine (match H in (t ~~ t')  return (rest t ~~ rest t') with 
            constrB t t' Hyp1 Hyp2  => _ end).
  assumption.
Qed.

Lemma bisimilar_injl (A: Type) (a a': A) (t t': Trap A):
  constr a t ~~ constr a' t' -> a = a'.
Proof.
  intros H.
  refine (match H in (t ~~ t') return (top t = top t') with 
            constrB t t' Hyp1 Hyp2  => _ end).
  assumption.  
Qed.

(* bisimilarity is an equivalence relation *)

Lemma bisimilar_refl : forall (A: Type), Reflexive (@bisimilar A).
Proof.
  cofix Hc.
  intros A [t r].
  apply constrB;
  reflexivity.
Qed.

(** printing t1 %\ensuremath{t_1}% *)
(** printing t2 %\ensuremath{t_2}% *)
(** printing t3 %\ensuremath{t_3}% *)

Lemma bisimilar_sym : forall (A: Type), Symmetric (@bisimilar A).
Proof.
  cofix Hc.
  intros A [t1 r1] [t2 r2] H.
  apply constrB; simpl.
  rewrite (bisimilar_injl H).  
  reflexivity.
  symmetry.
  apply (bisimilar_injr H).
Qed.

Lemma bisimilar_trans : forall (A: Type), Transitive (@bisimilar A).
Proof.
  cofix Hc.
  intros A [t1 r1] [t2 r2] [t3 r3] H1 H2.
  apply constrB; simpl.
  rewrite (bisimilar_injl H1), (bisimilar_injl H2).
  reflexivity.
  transitivity r2.
  apply (bisimilar_injr H1). 
  apply (bisimilar_injr H2).
Qed.

Add Parametric Relation (A: Type): (Tri A) (bisimilar(A:= A)) 
  reflexivity proved by (bisimilar_refl(A:= A))
  symmetry proved by (bisimilar_sym(A:= A))
  transitivity proved by (bisimilar_trans(A:= A))
  as bisimilarRel.

(** printing ==> %\ensuremath{\Longrightarrow}% *)

Lemma top_cong (A: Type) (t1 t2: Tri A): t1 ~~ t2 -> top t1 = top t2.
Proof.
  intros H.
  destruct t1 as [t1 r1] ; destruct t2 as [t2 r2].
  rewrite (bisimilar_injl H).
  reflexivity.
Qed.
  
Add Parametric Morphism (A: Type): (top(A:= A))
  with signature (bisimilar(A:= A)) ==> (eq(A:= A))
  as topM.
Proof.
  exact (top_cong(A:= A)).
Qed.

Lemma rest_cong (A: Type) (t1 t2: Tri A): t1 ~~ t2 -> rest t1 ~~ rest t2.
Proof.
  intros H.
  destruct t1 as [t1 r1] ; destruct t2 as [t2 r2].
  apply bisimilar_injr in H.
  assumption.
Qed.
  
Add Parametric Morphism (A: Type): (rest(A:= A))
  with signature (bisimilar(A:= A)) ==> (bisimilar(A:= E * A))
  as restM.
Proof.
  exact (rest_cong(A:= A)).
Qed.

Lemma cut_cong : forall (A: Type)(t t': Trap A), t ~~ t' -> cut t ~~ cut t'.
Proof.
  cofix Hc.
  intros A [[e a] r] [[e' a'] r'] H.
  apply constrB; simpl.
  apply bisimilar_injl in H.
  inversion H ; reflexivity.
  apply Hc.
  apply (bisimilar_injr H).
Qed.

Add Parametric Morphism (A: Type): (cut(A:= A))
  with signature (bisimilar(A:= E * A)) ==> (bisimilar(A:= A))
  as cutM.
Proof.
  exact (cut_cong(A:= A)).
Qed.

Lemma add_es_cong (A: Type)(es: Stream E)(t1 t2: Tri A): t1 ~~ t2 -> add_es es t1 ~~ add_es es t2.
Proof.
  revert A es t1 t2.
  cofix Hc; intros.
  destruct t1 as [a1 r1]; destruct t2 as [a2 r2].
  destruct es as [e es'].
  apply constrB; simpl.
  rewrite (bisimilar_injl H).
  reflexivity.
  apply Hc.
  apply (bisimilar_injr H).
Qed.

Add Parametric Morphism (A: Type)(es: Stream E): (add_es es)
  with signature (bisimilar(A:= A)) ==> (bisimilar(A:= E * A))
  as add_esM.
Proof.
  intros.
  apply add_es_cong.
  assumption.
Qed.

(** printing f' %\ensuremath{f'}% *)

Definition fequiv (A B: Type) (f f': A -> B): Prop := forall t: A, f t = f' t.
(* begin hide *)
Infix "=e" := fequiv (at level 60).
(* end hide *)

Lemma fequiv_refl (A B: Type): Reflexive (@fequiv A B).
Proof.
  do 2 red; intros; reflexivity.
Qed.

Lemma fequiv_sym (A B: Type): Symmetric (@fequiv A B).
Proof.
  do 2 red; intros; symmetry; apply H.
Qed.

Lemma fequiv_trans (A B: Type): Transitive (@fequiv A B).
Proof.
  do 2 red; intros f g h H1 H2 a.
  transitivity (g a); (apply H1 || apply H2).
Qed.

Add Parametric Relation (A B: Type): (A -> B) (@fequiv A B) 
  reflexivity proved by (fequiv_refl(A:= A)(B:= B))
  symmetry proved by (fequiv_sym(A:= A)(B:= B))
  transitivity proved by (fequiv_trans(A:= A)(B:= B))
  as fequivRel.

Lemma lift_ext : forall (A B: Type) (f f': Tri A -> B), f =e f' -> lift f =e lift f'.
Proof.
  intros A B f f' H [ea r].
  unfold lift.
  rewrite H.
  reflexivity.
Qed.

(** redec only depends on the extension of its functional argument *)

Lemma redec_ext : forall (A B: Type) (f f': Tri A -> B) (t: Tri A), f =e f' -> redec f t ~~ redec f' t.
Proof.
  cofix Hc.
  intros A B f f' [t r] H.
  apply constrB; simpl.
  apply H.
  apply Hc.
  apply lift_ext.
  assumption.
Qed.

Definition fcompat (A B: Type)(f: Tri A -> B): Prop := forall (t t': Tri A), t ~~ t' -> f t = f t'.

Ltac fcompat2Proper f Hf := change (Morphisms.Proper (@bisimilar _ ==> @eq _) f) in Hf.

Lemma lift_cong (A B: Type)(f: Tri A -> B): fcompat f -> fcompat (lift f).
Proof.
  red.
  intros Hf [ea r] [ea' r'] Hyp.
  apply injective_projections; simpl.
  apply bisimilar_injl in Hyp.
  rewrite Hyp.
  reflexivity.
  apply Hf.
  apply cut_cong.
  assumption.
Qed.

(* a preparation for the second comonad law *)

Lemma lift_top (A: Type): lift (top(A:= A)) =e top(A:= E * A).
Proof.
  intros [[e a] r].
  reflexivity.
Qed.

(* a stronger statement to get the proof through *)

Lemma comonad2_stronger (A: Type)(f: Tri A -> A)(Hf: f =e top(A:= A))(t: Tri A): redec f t ~~ t.
Proof.
  revert A f Hf t.
  cofix Hc.
  intros A f Hf [a r].
  apply constrB.
  simpl.
  rewrite Hf.
  reflexivity.
  simpl.
  apply Hc.
  clear a r.
  rewrite <- lift_top.
  apply lift_ext.
  assumption.
Qed.

Corollary comonad2 (A: Type) (t: Tri A): redec (top(A:= A)) t ~~ t.
Proof.
  apply comonad2_stronger.
  reflexivity.
Qed.

(* preparations for the third comonad law *)

Lemma redec_cut: forall (A B: Type) (f: Tri A -> B) (r: Trap A),
  redec f (cut r) ~~ cut(redec (lift f) r).
Proof.
  cofix Hc.
  intros A B f [[e a] t].
  apply constrB; simpl.
  reflexivity.
  apply Hc.
Qed.

(** composition *)
(** printing o %\ensuremath{\circ}% *)
Definition comp (A B C: Type) (g: B -> C) (f: A -> B): A -> C := fun x => g (f x).
(* begin hide *)
Infix "o" := comp (at level 90).
(* end hide *)

(** [comp] is displayed as the infix $\circ$#o#. *)

Lemma auxcomonad3 (A B C: Type) (f: Tri A -> B) (g: Tri B -> C)(Hg: fcompat g):
  lift (g o redec f) =e (lift g o redec (lift f)).
Proof.
  intro r.
  unfold comp.
  unfold lift at 1 2.
  rewrite comonad1.
  apply injective_projections; simpl.
  reflexivity.
  apply Hg, redec_cut.
Qed.

(* a stronger statement to get the proof through *)

Lemma comonad3_stronger (A B C: Type)(f: Tri A -> B)(g: Tri B -> C)(Hg : fcompat g)(h: Tri A -> C)
  (Hh: h =e (g  o (redec f)))(t: Tri A): redec h t ~~ redec g (redec f t).
Proof.
  revert A B C f g Hg h Hh t.
  cofix Hc.
  intros A B C f g Hg h Hh [a r].
  apply constrB.
  simpl.
  rewrite Hh.
  reflexivity.
  simpl. 
  apply Hc.
  apply lift_cong.
  assumption.
  clear a r.
  rewrite <- (auxcomonad3 f (g:= g)); try assumption.
  apply lift_ext.
  assumption.
Qed.

Corollary comonad3 (A B C: Type) (f: Tri A -> B) (g: Tri B -> C) (t: Tri A): 
  fcompat g -> redec (g o redec f) t ~~ redec g (redec f t).
Proof.
  intro Hg.
  apply (comonad3_stronger f Hg); reflexivity.
Qed.

(* a preliminary version without type classes:
Definition fcompatGen (T: Type -> Type)(equiv: forall A: Type, relation (T A))(A B: Type)(f: T A -> B): Prop := 
  forall (t t': T A), equiv _ t t' -> f t = f t'.
*)

Class Equiv (T: Type -> Type) := equiv : forall {A: Type}, relation (T A).
Infix "~~^" := equiv (at level 70):type_scope.

Definition fcompatGen (T: Type -> Type)(E_eq: Equiv T)(A B: Type)(f: T A -> B): Prop := 
  forall (t t': T A), t ~~^ t' -> f t = f t'.

Lemma fcompatGenProper (T: Type -> Type)(E_eq: Equiv T)(A B: Type)(f: T A -> B):
  fcompatGen E_eq A f = Proper (E_eq A ==> eq) f.
Proof.
  reflexivity.
Qed.

Class WeakComonad (T: Type -> Type)(E_eq: Equiv T) := 
  {wcounit: forall A: Type, T A -> A; wcobind: forall (A B: Type), (T A -> B) -> T A -> T B; 
   wcomonad1gen: forall (A B: Type)(f: T A -> B)(t: T A), wcounit (wcobind f t) = f t;
   wcomonad2gen: forall (A: Type)(t: T A), wcobind (wcounit(A:= A)) t ~~^ t;
   wcomonad3gen: forall (A B C: Type)(f: T A -> B)(g: T B -> C)(t: T A), 
     Proper (E_eq B ==> eq) g -> wcobind (g o wcobind f) t ~~^ wcobind g (wcobind f t)}.

Program Instance TriComonad: WeakComonad(T:= Tri) bisimilar.
Next Obligation.
  exact (top X).
Defined.
Next Obligation.
  exact (redec X X0).
Defined.
Next Obligation.
  apply comonad2.
Qed.
Next Obligation.
  apply comonad3.
  assumption.
Qed.

(* we use streams as defined in the Coq standard library *)

Lemma StreamUnfold (A: Type) (l: Stream A): l = Cons (hd l) (tl l).
Proof.
  destruct l as [a l].
  reflexivity.
Qed.

(** printing == %\ensuremath{\equiv}% *)
(** The following definition is part of the library.
<<
CoInductive EqSt (A : Type) (s1 s2 : Stream A) : Prop :=
    eqst : hd s1 = hd s2 -> EqSt (tl s1) (tl s2) -> EqSt s1 s2.
>> *)

(* a less usable alternative that would come to mind:
CoInductive EqSt (A : Type): relation(Stream A) :=
    eqst : forall (a1 a2: A)(s1 s2 : Stream A), a1 = a2 -> EqSt s1 s2 -> EqSt (Cons a1 s1) (Cons a2 s2).
*)

(* begin hide *)
Infix "==" := EqSt (at level 60).
(* end hide *)
(** [EqSt] is displayed as the infix $\equiv$#==#. *)

Add Parametric Relation (A: Type): (Stream A) (EqSt(A:= A))
  reflexivity proved by (EqSt_reflex(A:= A))
  symmetry proved by (sym_EqSt(A:= A))
  transitivity proved by (trans_EqSt(A:= A))
  as EqStRel.

(** printing l1 %\ensuremath{l_1}% *)
(** printing l2 %\ensuremath{l_2}% *)
(** printing l3 %\ensuremath{l_3}% *)
(** printing a1 %\ensuremath{a_1}% *)
(** printing a2 %\ensuremath{a_2}% *)
(** printing a3 %\ensuremath{a_3}% *)

Lemma EqSt_injl (A: Type)(a1 a2: A)(l1 l2: Stream A): Cons a1 l1 == Cons a2 l2 -> a1 = a2.
Proof.
  intros [H1 _].
  assumption.
Qed.

Lemma EqSt_injr (A: Type)(a1 a2: A)(l1 l2: Stream A):
  Cons a1 l1 == Cons a2 l2 -> l1 == l2.
Proof.
  intros [_ H2].
  assumption.
Qed.

Lemma hd_cong (A: Type) (l1 l2: Stream A): l1 == l2 -> hd l1 = hd l2.
Proof.
  intros [H1 _]; assumption.
Qed.

Add Parametric Morphism (A: Type): (@hd A)
  with signature (@EqSt A) ==> (@eq A)
  as hdM.
Proof.
  exact (@hd_cong A).
Qed.  

Lemma tl_cong (A: Type) (l1 l2: Stream A): l1 == l2 -> tl l1 == tl l2.
Proof.
  intros [_ H].
  assumption.
Qed.

Add Parametric Morphism (A: Type):  (@tl A)
  with signature (@EqSt A) ==> (@EqSt A)
  as tlM.
Proof.
  exact (@tl_cong A).
Qed.

(* direct would have been:
Add Parametric Morphism (A: Type): (@hd A)
  with signature (@EqSt A) ==> (@eq A)
  as hdM.
Proof.
  intros.
  exact (match H with eqst H _ => H end).
Qed.

Add Parametric Morphism (A: Type): (@tl A)
  with signature (@EqSt A) ==> (@EqSt A)
  as tlM.
Proof.
  intros.
  exact (match H with eqst _ H => H end).
Qed.
*)

Lemma Cons_cong (A: Type) (a: A) (l1 l2: Stream A): l1 == l2 -> Cons a l1 == Cons a l2.
Proof.
  intros H.
  apply eqst.
  reflexivity.
  assumption.
Qed.

Add Parametric Morphism (A: Type): (@Cons A)
  with signature (@eq A) ==> (@EqSt A) ==> (@EqSt A)
  as ConsM2.
Proof.
  exact (@Cons_cong A).
Qed.

Lemma map_OK (A B: Type) (f: A -> B) (a: A) (l: Stream A):
  map f (Cons a l) = Cons (f a) (map f l).
Proof.
  rewrite (unfold_Stream(map f (Cons a l))).
  reflexivity.
Qed.

Lemma map_OK_eager (A B: Type) (f: A -> B)(l: Stream A):
  map f l = Cons (f (hd l)) (map f (tl l)).
Proof.
  destruct l as [a l'].
  apply map_OK.
Qed.

Corollary hd_map (A B: Type) (f: A -> B)(l: Stream A): hd (map f l) = f (hd l).
Proof.
  rewrite map_OK_eager.
  reflexivity.
Qed.

Corollary tl_map (A B: Type) (f: A -> B)(l: Stream A): tl (map f l) = map f (tl l).
Proof.
  rewrite map_OK_eager.
  reflexivity.
Qed.

(*
Opaque map.
*)

Lemma map_cong (A B: Type) (f: A -> B): forall (l1 l2: Stream A), l1 == l2 -> map f l1 == map f l2.
Proof.
  cofix Hc.
  intros [a1 l1] [a2 l2] [H1 H2].
  apply eqst; do 2 rewrite map_OK; simpl in *|-*.
  rewrite H1.
  reflexivity.
  apply (Hc _ _ H2).
Qed.

Add Parametric Morphism (A B: Type) (f: A -> B): (map f)
  with signature (@EqSt A) ==> (@EqSt B)
  as mapM.
Proof.
  exact (map_cong f).
Qed.
(** One might wish to include that [map] also does not change when replacing [f] 
    by an extensionally equal function. *)

Definition TriS (A: Type) : Type := Stream (A * Stream E).

Definition topAS (A :Type)(t: TriS A) : A := fst (hd t).
Definition topEsS (A :Type)(t: TriS A) : Stream E := snd (hd t).			  
Definition restS (A :Type)(t: TriS A) : TriS A := tl t.

Lemma toprestS_OK (A :Type)(t: TriS A) : t = Cons (topAS t, topEsS t) (restS t).
Proof.
  destruct t as [[a es] t].
  reflexivity.
Qed.

Definition topEs (A :Type)(t: Tri A) : Stream E := es_cut (rest t).	

CoFixpoint toStreamRep (A: Type)(t: Tri A) : TriS A := 
   Cons (top t, topEs t) (toStreamRep (cut (rest t))).

Lemma toStreamRep_OK (A: Type)(t: Tri A) :
   toStreamRep t = Cons (top t, topEs t) (toStreamRep (cut (rest t))).
Proof.
  rewrite (toprestS_OK (toStreamRep t)).
  reflexivity.
Qed.

CoFixpoint add_esS (A : Type)(es : Stream E) (t: TriS A) : TriS (E * A) := 
  Cons ((hd es, topAS t), tl es) (add_esS (topEsS t) (restS t)).

Lemma add_esS_OK (A : Type)(es : Stream E) (t: TriS A) :
  add_esS es t = Cons ((hd es, topAS t), tl es) (add_esS (topEsS t) (restS t)).
Proof.
  rewrite (toprestS_OK (add_esS es t)).
  reflexivity.
Qed.

CoFixpoint fromStreamRep (A: Type)(t: TriS A) : Tri A := 
  constr (topAS t) (fromStreamRep (add_esS (topEsS t) (restS t))).

Lemma fromStreamRep_OK (A: Type)(t: TriS A) : 
  fromStreamRep t = constr (topAS t) (fromStreamRep (add_esS (topEsS t) (restS t))).
Proof.
  rewrite (toprestOK (fromStreamRep t)).
  reflexivity.
Qed.

(*
Expected definition, but not guarded :
CoFixpoint fromStreamRep_orig (A: Type)(t: TriS A) : Tri A := 
  constr (topAS t) (add_es (topEsS t) (fromStreamRep_orig (restS t))).
*)

Definition fromStreamRep_equation (fromStreamRep_candidate: forall A: Type, TriS A -> Tri A): Prop :=
  forall (A: Type)(t: TriS A), 
    fromStreamRep_candidate A t ~~ constr (topAS t) (add_es (topEsS t) (fromStreamRep_candidate A (restS t))).

CoInductive bisimilarS (A: Type) : TriS A -> TriS A -> Prop := 
  constrBS : forall t t', topAS t = topAS t' -> 
    topEsS t == topEsS t' -> bisimilarS (restS t) (restS t') -> bisimilarS t t'.
				  
(* begin hide *)
Infix "==^" := bisimilarS (at level 60).
(* end hide *)
		  
Lemma bisimilarS_refl(A: Type) : Reflexive (@bisimilarS A).
Proof.
  cofix Hc.
  intros t.
  apply constrBS; reflexivity.
Qed.

Lemma bisimilarS_sym(A: Type) : Symmetric (@bisimilarS A).
Proof.
  cofix Hc.
  red.
  intros t t' H.
  destruct H.
  apply constrBS; (symmetry; assumption).
Qed.

Lemma bisimilarS_trans(A: Type) : Transitive (@bisimilarS A).
Proof.
  cofix Hc.
  intros _ _ t3 [t1 t2 H1 H2 H3] H4.
  destruct H4 as [t2 t3 H4 H5 H6].
  apply constrBS.
  transitivity (topAS t2) ; assumption.
  transitivity (topEsS t2) ; assumption.
  transitivity (restS t2); assumption.
Qed.

Add Parametric Relation (A: Type): (TriS A) (@bisimilarS A)
  reflexivity proved by (@bisimilarS_refl A)
  symmetry proved by (@bisimilarS_sym A)
  transitivity proved by (@bisimilarS_trans A)
  as bisimilarSRel.

Instance EqStImpBisimS (A: Type): subrelation (@EqSt (A * Stream E))(@bisimilarS A).
Proof.
  cofix Hc.
  do 4 red; intros s1 s2 Hyp.
  destruct s1 as [[a1 es1] r1]; destruct s2 as [[a2 es2] r2].
  destruct Hyp as [H1 H2].
  simpl in H1.
  simpl in H2.
  inversion H1.
  apply constrBS; simpl.
  reflexivity.
  reflexivity.
  apply Hc.
  assumption.
Qed.

Lemma topAS_cong (A: Type)(t t': TriS A): t ==^ t' -> topAS t = topAS t'.
Proof.
  intro H.
  destruct H.
  assumption.
Qed.

Add Parametric Morphism (A: Type) : (@topAS A)
  with signature ((@bisimilarS A) ==> (@eq _))
  as topASM.
Proof.
  exact (@topAS_cong A).
Qed.

Lemma topEsS_cong (A: Type)(t t': TriS A): t ==^ t' -> topEsS t == topEsS t'.
Proof.
  intro H.
  destruct H.
  assumption.
Qed.

Add Parametric Morphism (A: Type) : (@topEsS A)
  with signature ((@bisimilarS A) ==> (@EqSt _))
  as topEsSM.
Proof.
  exact (@topEsS_cong A).
Qed.

Lemma restS_cong (A: Type)(t t': TriS A): t ==^ t' -> restS t ==^ restS t'.
Proof.
  intro H.
  destruct H.
  assumption.
Qed.

Add Parametric Morphism (A: Type) : (@restS A)
  with signature ((@bisimilarS A) ==> (@bisimilarS A))
  as restSM.
Proof.
  exact (@restS_cong A).
Qed.

Lemma es_cut_add_esS (A: Type)(t: TriS A)(es: Stream E): 
  es_cut (fromStreamRep (add_esS es t)) == es.
Proof.
  revert A t es; cofix Hc ; intros A [[a es] t] [e es'].
  apply eqst.
  reflexivity.
  simpl.
  apply (Hc _ (add_esS es t)).
Qed.

Lemma cut_fSR(A: Type)(t: TriS A)(es: Stream E) : 
  fromStreamRep t ~~ cut (fromStreamRep (add_esS es t)).
Proof.
  revert A t es ; cofix Hc ; intros A [[a es'] t] es.
  apply constrB.
  reflexivity.
  simpl.
  apply Hc.
Qed.

Lemma es_cut_cong (A : Type)(t1 t2 : Tri (E * A)) : 
  t1 ~~ t2 -> es_cut t1 == es_cut t2.
Proof.
  revert A t1 t2 ; cofix Hc ; intros A [[a1 e1] t1] [[a2 e2] t2] H1.
  apply eqst; simpl.
  apply bisimilar_injl in H1.
  inversion H1.
  reflexivity.
  apply Hc.
  apply (bisimilar_injr H1).
Qed.

Add Parametric Morphism (A: Type) : (@es_cut A)
  with signature ((@bisimilar (E *A)) ==> (@EqSt _))
  as es_cutM.
Proof.
  exact (@es_cut_cong A).
Qed.

Add Parametric Morphism (A: Type) : (@toStreamRep A)
  with signature ((@bisimilar A) ==> (@bisimilarS A))
  as toStreamRepM.
Proof.
  revert A ; cofix Hc ; intros _ _ _ [A t1 t2 H1 H2].
  apply constrBS.
  assumption.
  unfold topEsS ; simpl.
  apply es_cut_cong, H2.
  simpl.
  apply Hc, cut_cong, H2.
Qed.

Lemma tSR_fSR_stronger (A: Type)(t u: TriS A) : toStreamRep (fromStreamRep t) ==^ u -> t ==^ u.
Proof.
  revert t u; cofix Hc ; intros [[a es] t] u H1.
  inversion_clear H1 as [t' t'' H2 H3 H4].
  apply constrBS.
  assumption.
  rewrite <- H3.
  unfold topEsS ; simpl.
  symmetry.
  unfold topEs; simpl.
  apply es_cut_add_esS.
  simpl.
  apply Hc.
  rewrite <- H4.
  simpl.
  rewrite cut_fSR.
  reflexivity.
Qed.

Corollary tSR_fSR (A: Type)(t: TriS A) : t ==^ toStreamRep (fromStreamRep t).
Proof.
  apply tSR_fSR_stronger.
  reflexivity.
Qed.

Lemma add_esS_tSR_OK (A: Type) (t: Trap A): 
  toStreamRep t ==^ add_esS (es_cut t) (toStreamRep (cut t)).
Proof.
  revert t ; cofix Hc ; intros [[e a] t].
  apply constrBS; try reflexivity.
  simpl.
  apply Hc.
Qed.

Lemma add_esS_cong (A : Type)(t1 t2 : TriS A) (s1 s2 : Stream E) : 
  t1 ==^ t2 -> s1 == s2 -> add_esS s1 t1 ==^ add_esS s2 t2.
Proof.
  revert t1 t2 s1 s2 ; cofix Hc ; intros _ _  s1 s2 [t1 t2 H1 H2 H3] [H4 H5].
  apply constrBS.
  unfold topAS.
  simpl.
  rewrite H1, H4 ; reflexivity.
  assumption.
  simpl.
  apply Hc ; assumption.
Qed.

Add Parametric Morphism (A: Type) : (@fromStreamRep A)
  with signature ((@bisimilarS A) ==> (@bisimilar A))
  as fromStreamRepM.
Proof.
  revert A ; cofix Hc ; intros A _ _ [t1 t2 H1 H2 H3].
  apply constrB.
  assumption.
  simpl.
  apply Hc.
  apply add_esS_cong ; assumption.
Qed.

Lemma fSR_tSR_stronger (A: Type)(t u: Tri A) : 
  fromStreamRep (toStreamRep t) ~~ u -> t ~~ u.
Proof.
  revert A t u; cofix Hc ; intros A [a t] u H1.
  apply constrB.
  apply (top_cong H1).
  simpl.
  apply Hc.
  assert (H2 := rest_cong H1).
  transitivity (rest (fromStreamRep (toStreamRep (constr a t)))); try assumption.
  simpl.
  rewrite add_esS_tSR_OK.
  reflexivity.
Qed.
 
Lemma fSR_tSR (A: Type)(t: Tri A) : t ~~ fromStreamRep (toStreamRep t).
Proof.
  apply fSR_tSR_stronger.
  reflexivity.
Qed.


Definition redecS_indir (A B: Type) (f: TriS A -> B) (t: TriS A): TriS B := 
  toStreamRep (redec (f o (@toStreamRep A)) (fromStreamRep t)).

(*
Lemma redecS_indir_OK (A B: Type) (f: TriS A -> B) (t: TriS A):  
  redecS_indir f t = toStreamRep (redec (f o (@toStreamRep A)) (fromStreamRep t)).
Proof.
  reflexivity.
Qed.
*)

CoFixpoint redecS (A B: Type) (f: TriS A -> B) (t: TriS A): TriS B :=  
  Cons (f t, topEsS t) (redecS f (restS t)).

Lemma redecS_OK (A B: Type) (f: TriS A -> B) (t: TriS A):  
  redecS f t = Cons (f t, topEsS t) (redecS f (restS t)).
Proof.
  rewrite (toprestS_OK (redecS f t)).
  reflexivity.
Qed.

Lemma redecS_not_on_E (n: nat)(A B: Type) (f: TriS A -> B)(t: TriS A):
  map (@snd B (Stream E)) (redecS f t) == map (@snd A (Stream E)) t.
Proof.
  revert A B f t; cofix Hc; intros; destruct t as [[a es] r]; apply eqst; simpl.
  reflexivity.
  change (map (@snd B (Stream E)) (redecS f r) == map (@snd A (Stream E)) r).
  apply Hc.
Qed.
(* notice that streams of Stream E are compared only w.r.t. standard stream bisimilarity -
   therefore in each row, the E part is really not touched at all *)

Definition redec_indirS (A B: Type) (f: Tri A -> B) (t: Tri A): Tri B := 
  fromStreamRep (redecS (f o (@fromStreamRep A)) (toStreamRep t)).

(*
Lemma redec_indirS_OK (A B: Type) (f: Tri E A -> B) (t: Tri E A):  
  redec_indirS f t = fromStreamRep (redecS (f o (@fromStreamRep A)) (toStreamRep t)).
Proof.
  reflexivity.
Qed.
*)

Lemma add_esS_fSR (A: Type)(t: TriS A) :
  fromStreamRep (add_esS (topEsS t) (restS t)) = rest (fromStreamRep t).
Proof.
  reflexivity.
Qed.

Lemma topEstopEsS(A: Type)(t: Tri A) : topEs t = topEsS (toStreamRep t).
Proof.
  reflexivity.
Qed.

Lemma add_es_OK (A : Type) (es : Stream E) (t : Tri A) : 
  add_es es t = constr (hd es, top t) (add_es (tl es) (rest t)).
Proof.
  destruct es as [e es]; destruct t as [a t].
  rewrite (toprestOK (add_es (Cons e es) (constr a t))).
  reflexivity.
Qed.

Lemma add_esS_add_es (A: Type)(t: TriS A)(es: Stream E): 
  fromStreamRep (add_esS es t) ~~ add_es es (fromStreamRep t).
Proof.
  revert A t es ; cofix Hc ; intros A t [e es].
  apply constrB.
  reflexivity.
  simpl.
  apply Hc.
Qed.

Lemma fromStreamRep_is_orig: fromStreamRep_equation fromStreamRep.
Proof.
  red.
  intros.
  rewrite fromStreamRep_OK.
  apply constrB; simpl.
  reflexivity.
  apply add_esS_add_es.
Qed.

(* problem with guardedness:
Lemma fromStreamRep_unique_TRY (fSR1 fSR2: forall A: Type, TriS A -> Tri A):
  fromStreamRep_equation fSR1 -> fromStreamRep_equation fSR2 ->
  forall (A: Type)(t: TriS A), fSR1 _ t ~~ fSR2 _ t.
Proof.
  intros Hyp1 Hyp2.
  cofix Hc.
  intros.
  apply constrB; simpl.
  rewrite (Hyp1 _ t).
  rewrite (Hyp2 _ t).
  reflexivity.
  rewrite (Hyp1 _ t).
  rewrite (Hyp2 _ t).
  simpl.
  apply add_es_cong.
  apply Hc.
Guarded.
*)

Lemma es_cut_add_es (A: Type)(es: Stream E)(t: Tri A): es_cut (add_es es t) == es.
Proof.
  revert A es t; cofix Hc; intros A [e es] [a r].
  apply eqst; simpl.
  reflexivity.
  apply Hc.
Qed.

(* still unguarded:
Lemma fromStreamRep_unique_stronger_TRY (fSR1 fSR2: forall A: Type, TriS A -> Tri A):
  fromStreamRep_equation fSR1 -> fromStreamRep_equation fSR2 ->
  forall (A: Type)(t: TriS A), toStreamRep (fSR1 _ t) ==^ toStreamRep (fSR2 _ t).
Proof.
  intros Hyp1 Hyp2.
  cofix Hc; intros A t.
  apply constrBS; simpl.
  unfold topAS; simpl.
  red in Hyp1.
  red in Hyp2.
  rewrite Hyp1, Hyp2.
  reflexivity.
  red in Hyp1.
  red in Hyp2.
  rewrite Hyp1, Hyp2.
  unfold topEsS; simpl.
  unfold topEs; simpl.
  do 2 rewrite es_cut_add_es.
  reflexivity.
  red in Hyp1.
  red in Hyp2.
  rewrite Hyp1, Hyp2.
  simpl.
  do 2 rewrite cut_add_es.
  apply Hc.
Guarded.
*)

Lemma fromStreamRep_unique_stronger (fSR1 fSR2: forall A: Type, TriS A -> Tri A):
  fromStreamRep_equation fSR1 -> fromStreamRep_equation fSR2 ->
  forall (A: Type)(t: TriS A)(u1 u2: TriS A), toStreamRep (fSR1 _ t) ==^ u1 -> toStreamRep (fSR2 _ t) ==^ u2 -> u1 ==^ u2.
Proof.
  intros Hyp1 Hyp2.
  cofix Hc; intros A (*[[a es] r]*) t u1 u2 Hu1 Hu2.
  apply constrBS; simpl.
  rewrite <- Hu1, <- Hu2.
  red in Hyp1.
  red in Hyp2.
  rewrite Hyp1, Hyp2.
  reflexivity.
  rewrite <- Hu1, <- Hu2.
  red in Hyp1.
  red in Hyp2.
  rewrite Hyp1, Hyp2.
  unfold topEsS; simpl.
  unfold topEs; simpl.
  do 2 rewrite es_cut_add_es.
  reflexivity.
  red in Hyp1.
  red in Hyp2.
  rewrite Hyp1 in Hu1.
  rewrite Hyp2 in Hu2.
  apply restS_cong in Hu1.
  simpl in Hu1.
  rewrite cut_add_es in Hu1.
  apply restS_cong in Hu2.
  simpl in Hu2.
  rewrite cut_add_es in Hu2.
  apply (Hc _ (restS t)); assumption.
Qed.

Corollary fromStreamRep_unique (fSR1 fSR2: forall A: Type, TriS A -> Tri A):
  fromStreamRep_equation fSR1 -> fromStreamRep_equation fSR2 ->
  forall (A: Type)(t: TriS A), fSR1 _ t ~~ fSR2 _ t.
Proof.
  intros Hyp1 Hyp2.
  intros.
  rewrite (fSR_tSR (fSR1 A t)).
  rewrite (fSR_tSR (fSR2 A t)).
  apply fromStreamRepM.
  apply (fromStreamRep_unique_stronger Hyp1 Hyp2 t); (reflexivity || assumption).
Qed.


Definition fcompatS (A B: Type)(f: TriS A -> B): Prop := forall (t t': TriS A), t ==^ t' -> f t = f t'.

Ltac fcompatS2Proper f Hf := change (Morphisms.Proper (@bisimilarS _ ==> @eq _) f) in Hf.

Lemma f_toStreamRepM (A B : Type)(f: TriS A -> B)(Hf: fcompatS f) : fcompat (f o (@toStreamRep _)).
Proof.
  intros t1 t2 H.
  apply Hf, toStreamRepM, H.
Qed.

Lemma es_cut_redec (A B: Type)(f: Tri A -> B)(t: Tri A)(es: Stream E) : 
  es_cut (redec (lift f) (add_es es t)) == es.
Proof.
  revert A B f t es ; cofix Hc ; intros A B f [a t] [e es].
  apply eqst.
  reflexivity.
  simpl.
  apply Hc.
Qed.

Lemma redec_cong (A B: Type)(f: Tri A -> B)(Hf: fcompat f)(t t': Tri A): t ~~ t' -> redec f t ~~ redec f t'.
Proof.
  revert A B f Hf t t'.
  cofix Hc.
  intros A B f Hf [esa r] [esa' r'] Hyp.
  apply constrB; simpl.
  apply Hf.
  assumption.
  apply Hc.
  apply lift_cong; assumption.
  apply rest_cong in Hyp.
  assumption.
Qed.

Add Parametric Morphism (A B: Type)(f: Tri A -> B)(Hf: Morphisms.Proper (@bisimilar _ ==> @eq _) f):  (redec f)
  with signature (@bisimilar _) ==> (@bisimilar _)
  as redecM.
Proof.
  exact (redec_cong Hf).
Qed.

Lemma redecS_redecS_indir_stronger (A B: Type) (f: TriS A -> B)
  (Hf: fcompatS f) (t: TriS A)(u: TriS B): redecS_indir f t ==^ u -> redecS f t ==^ u.
Proof.
  revert t u ; cofix Hc ; intros t u H1.
  fcompatS2Proper f Hf.
  inversion_clear H1 as [t1 t2 H2 H3 H4].
  assert (Hf': fcompat (f o (toStreamRep(A:= A)))).
  red.
  intros.
  apply f_toStreamRepM; assumption.
  fcompat2Proper (f o (toStreamRep(A:= A))) Hf'.
  apply constrBS.
(* topAS *)
  rewrite <- H2.
  unfold topAS.
  simpl.
  unfold comp.
  rewrite <- tSR_fSR.
  reflexivity.
(* topEsS *)
  rewrite <- H3.
(*  destruct t as [[a es] t]. *)
  symmetry.
  rewrite redecS_OK.
  unfold redecS_indir.  
  rewrite (fromStreamRep_is_orig t).
  unfold topEsS; simpl.
  unfold topEs; simpl.
  apply es_cut_redec.

(* this case alternatively:
  rewrite <- H3.
  destruct t as [[a es] t].
  symmetry.
  rewrite redecS_OK.
  unfold redecS_indir, topEsS.
  simpl.
  unfold topEsS; simpl.
  assert (Hl: fcompat (lift(f o (toStreamRep(A:= A))))).
  apply lift_cong.
  assumption.
  fcompat2Proper (lift(f o (toStreamRep(A:= A)))) Hl.
  rewrite add_esS_add_es.
  apply es_cut_redec.
*)

(* restS *)
  simpl.
  apply Hc.
  rewrite <- H4.
  unfold redecS_indir.
  unfold restS.
  simpl.
  rewrite <- redec_cut.
  apply toStreamRepM.
  apply redec_cong; try assumption.
  rewrite cut_fSR.
  reflexivity.
Qed.

Lemma redecS_redecS_indir (A B: Type)(f: TriS A -> B)(Hf: fcompatS f)(t: TriS A): redecS f t ==^ redecS_indir f t.
Proof.
  apply redecS_redecS_indir_stronger.
  assumption.
  reflexivity.
Qed.

Lemma f_fromStreamRepM (A B : Type)(f: Tri A -> B)(Hf: fcompat f): fcompatS (f o (@fromStreamRep _)).
Proof.
  intros t1 t2 H.
  apply Hf, fromStreamRepM, H.
Qed.
 
Lemma es_cut_OK (A: Type)(t: Trap A) : es_cut t = Cons (fst (top t)) (es_cut (rest t)).
Proof.
  rewrite (StreamUnfold (es_cut t)).
  destruct t as [[e a] t].
  reflexivity.
Qed.

Lemma es_cut_cut_stronger (A B :Type)(f: Tri A -> B)(t: Trap (E* A)) (u: Stream E): 
  es_cut (redec (lift f) (cut t)) == u -> es_cut (cut t) == u.
Proof.
  revert A B f t u; cofix Hc ; intros A B f [[e1 [e2 a]] t] u [H1 H2].
  apply eqst.
  apply H1.
  rewrite (es_cut_OK (cut (constr (e1, (e2, a)) t))).
  simpl.
  change (es_cut (cut t) == tl u).
  apply (Hc _ _ _ _ _ H2).
Qed.

Lemma es_cut_cut (A B :Type)(f: Tri A -> B)(t: Trap (E* A)): 
  es_cut (cut t) == es_cut (redec (lift f) (cut t)).
Proof.
  apply (es_cut_cut_stronger f).
  reflexivity.
Qed.

Lemma cut_fSR_tSR (A: Type)(t: Trap A): 
  fromStreamRep (toStreamRep (cut t)) ~~ cut (fromStreamRep (toStreamRep t)).
Proof.
  rewrite <- fSR_tSR.
  apply cut_cong.
  apply fSR_tSR.
Qed.

Lemma add_esS_redecS (A B : Type)(f: Tri A -> B)(Hf: fcompat f)(t: Trap A) : 
  add_esS (es_cut t) (redecS (f o (@fromStreamRep _)) (toStreamRep (cut t))) ==^
  redecS ((lift f) o (@fromStreamRep _)) (toStreamRep t).
Proof.
  revert t ; cofix Hc ; intros [[e a] t].
  apply constrBS; simpl.
 
  unfold topAS, comp, lift.
  simpl.
  f_equal.
  unfold topAS.
  simpl.
  apply Hf, cut_fSR_tSR.

  unfold topEsS.
  simpl.
  fold (es_cut t).
  rewrite <- topEstopEsS.
  reflexivity.

  repeat (unfold topEsS ; simpl).
  fold (cut t).
  apply Hc.
Qed.

Lemma rest_redec_indirS(A B: Type)(f: Tri A -> B)(Hf: fcompat f)(t: Tri A): 
  rest (redec_indirS f t) ~~ redec_indirS (lift f) (rest t).
Proof.
  destruct t as [a [[e a'] t]].
  apply constrB ; simpl.
  unfold topAS, comp, lift, topAS.
  simpl.
  f_equal.
  unfold topAS ; simpl.
  apply Hf.
  rewrite <- fSR_tSR.
  apply cut_cong.
  apply fSR_tSR.

  apply fromStreamRepM.
  apply add_esS_cong ; try reflexivity.
  repeat (unfold topEsS ; simpl).
  fold (cut t).
  apply add_esS_redecS, Hf.
Qed.

Lemma redec_redec_indirS_stronger (A B: Type) (f: Tri A -> B)(Hf: fcompat f) (t: Tri A)(u: Tri B): 
  redec_indirS f t ~~ u -> redec f t ~~ u.
Proof.
  revert A B f Hf t u ; cofix Hc ; intros A B f Hf [a t] u H1.
  apply constrB; simpl.
  rewrite <- (top_cong H1).
  simpl.
  unfold topAS.
  unfold comp.
  simpl.
  fcompat2Proper f Hf.
  rewrite <- fSR_tSR.
  reflexivity.
  
  fold (redec (lift f) t).
  apply Hc.
  apply lift_cong, Hf.
  apply rest_cong in H1.
  rewrite <- H1.
  rewrite rest_redec_indirS; try assumption.
  reflexivity.
Qed.

Lemma redec_redec_indirS (A B: Type) (f: Tri A -> B)(Hf: fcompat f) (t: Tri A): 
  redec f t ~~ redec_indirS f t.
Proof.
  apply redec_redec_indirS_stronger.
  apply Hf.
  reflexivity.
Qed.

(* now a different approach through the comultiplication of the comonad instead of coextension *)

CoFixpoint tails (T: Type)(s: Stream T) := Cons s (tails (tl s)).

Definition liftS (A B: Type) (f: TriS A -> B)(t: TriS A): B * Stream E := (f t, topEsS t).

Definition redecS' (A B: Type) (f: TriS A -> B)(t: TriS A) : TriS B:= map (liftS f) (tails t).

Lemma redecS_redecS' (A B: Type) (f: TriS A -> B)(t: TriS A) : redecS f t == redecS' f t.
Proof.
  revert t ; cofix Hc ; intros t.
  apply eqst.
  reflexivity.
  simpl.
  apply Hc.
Qed.

Lemma tailscomonadS1 (T: Type)(s: Stream T): hd (tails s) = s.
Proof.
  reflexivity.
Qed.

Lemma tailscomonadS2 (T: Type)(s: Stream T): map (@hd T) (tails s) == s.
Proof.
  revert s.
  cofix Hc; intros.
  destruct s as [t s].
  apply eqst; simpl.
  reflexivity.
  apply Hc.
Qed.
 
Lemma tailscomonadS3 (T: Type)(s: Stream T): map (@tails T) (tails s) == tails (tails s).
Proof.
  revert s.
  cofix Hc; intros.
  destruct s as [t s].
  apply eqst; simpl.
  reflexivity.
  apply Hc.
Qed.
  
(* we can see this even more generically *)

Definition redecSgen (A B: Type) (f: Stream A -> B)(t: Stream A) : Stream B:= map f (tails t).

Lemma redecS'_is_instance (A B: Type) (f: TriS A -> B)(t: TriS A) : redecS' f t = redecSgen (liftS f) t.
Proof.
  reflexivity.
Qed.

Lemma redecSgen_ext (A B: Type)(f f': Stream A -> B)(s: Stream A): f =e f' -> redecSgen f s == redecSgen f' s.
Proof.
  intro H; revert s; cofix Hc; intros.
  destruct s as [a s].
  apply eqst; simpl.
  apply H.
  apply Hc.
Qed.

Lemma comonad1Sgen (A B: Type) (f: Stream A -> B) (t: Stream A): hd(redecSgen f t) = f t.
Proof.
  unfold redecSgen.
  rewrite hd_map.
  rewrite tailscomonadS1.
  reflexivity.
Qed.

Lemma comonad2Sgen (A: Type) (t: Stream A): redecSgen (hd(A:= A)) t == t.
Proof.
  unfold redecSgen.
  apply tailscomonadS2.
Qed.

Lemma tailsNatural (A B: Type)(f: A -> B)(s: Stream A): map (map f) (tails s) == tails (map f s).
Proof.
  revert s.
  cofix Hc; intros.
  destruct s as [a s].
  apply eqst; simpl.
  reflexivity.
  apply Hc.
Qed.

Lemma map_fct2 (A B C: Type) (f: A -> B) (g: B -> C)(l: Stream A):
  map g (map f l) == map (g o f) l.
Proof.
  revert l.
  cofix Hc.
  intros [a l].
  apply eqst.
  reflexivity.
  do 2 rewrite map_OK.
  apply Hc.
Qed.

Lemma comonad3Sgen (A B C: Type) (f: Stream A -> B) (g: Stream B -> C) (t: Stream A): 
  redecSgen (g o redecSgen f) t == redecSgen g (redecSgen f t).
Proof.
  unfold redecSgen.
  rewrite <- map_fct2.
  fold ((map f) o (@tails A)).
  rewrite <- map_fct2.
  apply map_cong.
  rewrite tailscomonadS3.
  apply tailsNatural.
Qed.

Class Comonad (T: Type -> Type)(E_eq: Equiv T) := 
  {counit: forall A: Type, T A -> A; cobind: forall (A B: Type), (T A -> B) -> T A -> T B; 
   comonad1gen: forall (A B: Type)(f: T A -> B)(t: T A), counit (cobind f t) = f t;
   comonad2gen: forall (A: Type)(t: T A), cobind (counit(A:= A)) t ~~^ t;
   comonad3gen: forall (A B C: Type)(f: T A -> B)(g: T B -> C)(t: T A), 
     cobind (g o cobind f) t ~~^ cobind g (cobind f t)}.

Program Instance StreamComonad: Comonad(T:= fun A: Type => Stream A) EqSt.
Next Obligation.
  exact (hd X).
Defined.
Next Obligation.
  exact (redecSgen X X0).
Defined.
Next Obligation.
  apply comonad2Sgen.
Qed.
Next Obligation.
  apply comonad3Sgen.
Qed.

Corollary comonad1S' (A B: Type) (f: TriS A -> B) (t: TriS A): topAS(redecS' f t) = f t.
Proof.
  rewrite redecS'_is_instance.
  unfold topAS.
  rewrite comonad1Sgen.
  reflexivity.
Qed.

Lemma EqStImplBisimilarS (A: Type)(t t': TriS A): t == t' -> t ==^ t'.
Proof.
  revert t t'; cofix Hc; intros.
  destruct t as [a t]; destruct t' as [a' t'].
  apply constrBS; simpl.
  unfold topAS.
  apply EqSt_injl in H.
  rewrite H.
  reflexivity.
  unfold topEsS.
  apply EqSt_injl in H.
  rewrite H.
  reflexivity.
  apply EqSt_injr in H.
  apply Hc.
  assumption.
Qed.

Lemma liftS_aux2 (A: Type): liftS (topAS (A:= A)) =e hd (A:= A * Stream E).
Proof.
  red; intro.
  apply injective_projections; reflexivity.
Qed.

Corollary comonad2S' (A: Type) (t: TriS A): redecS' (topAS(A:= A)) t == t.
Proof.
  rewrite redecS'_is_instance.
  transitivity (redecSgen (@hd (A * Stream E)) t).
  apply redecSgen_ext.
  apply liftS_aux2.
  apply comonad2Sgen.
Qed.

Lemma liftS_aux3 (A B C: Type)(f : TriS A → B)(g : TriS B → C): 
  liftS (g o redecS' f) =e (liftS g o redecS' f).
Proof.
  intros t.
  apply injective_projections; simpl.
  reflexivity.
  rewrite redecS'_is_instance.
  unfold topEsS.
  rewrite comonad1Sgen.
  reflexivity.
Qed.

Corollary comonad3S' (A B C: Type) (f: TriS A -> B) (g: TriS B -> C) (t: TriS A): 
  redecS' (g o redecS' f) t == redecS' g (redecS' f t).
Proof.
  repeat rewrite redecS'_is_instance.
  rewrite <- comonad3Sgen.
  apply redecSgen_ext.
  rewrite liftS_aux3.
  intros x; f_equal; rewrite redecS'_is_instance.
Qed.

Program Instance TriSComonad': Comonad(T:= TriS) (fun A: Type => EqSt(A:= A * Stream E)).
Next Obligation.
  exact (topAS X).
Defined.
Next Obligation.
  exact (redecS' X X0).
Defined.
Next Obligation.
  apply comonad2S'.
Qed.
Next Obligation.
  apply comonad3S'.
Qed.

Instance comonadWeakening `{T: Type -> Type, E_eq: Equiv T, c: Comonad T (E_eq:= E_eq)} : WeakComonad E_eq.
Proof.
  destruct c.
  apply (Build_WeakComonad E_eq counit0 cobind0 comonad1gen0 comonad2gen0).
  intros.
  clear H.
  apply comonad3gen0.
Defined.

(* Program does not serve here:
Program Instance comonadWeakening_ALT `{T: Type -> Type, E_eq: Equiv T, c: Comonad T (E_eq:= E_eq)} : WeakComonad E_eq.
Next Obligation.
  revert A X.
  exact counit.
Defined.
Next Obligation.
  revert A B X X0.
  exact cobind.
Defined.
Next Obligation.
  apply comonad1gen.
Qed.
Next Obligation.
  unfold comonadWeakening_ALT_obligation_1, comonadWeakening_ALT_obligation_2.
  apply (comonad2gen(Comonad:= c) _ t).
does not work because of forced eta-expansion in instance for wcounit
*)

(* Can we infer the weak comonad laws for redec through Lemma redec_redec_indirS ? 
   No, only even weaker ones! *)
Lemma comonad1_ALT_weaker (A B: Type) (f: Tri A -> B) (Hf: fcompat f) (t: Tri A): top(redec f t) = f t.
Proof.
  rewrite redec_redec_indirS; try assumption.
  unfold redec_indirS.
  simpl.
  rewrite toStreamRep_OK.
  rewrite redecS_OK.
  unfold topAS.
  simpl.
  unfold comp.
  apply Hf.
  rewrite fromStreamRep_OK.
  apply constrB; simpl.
  reflexivity.
  unfold topEsS.
  simpl.
  rewrite add_esS_add_es.
  rewrite <- fSR_tSR.
  unfold topEs.
  apply es_cut_reconstr.
Qed.

Lemma comonad2_ALT_aux (A: Type): ((top(A:= A)) o (fromStreamRep(A:= A))) =e topAS(A:= A).
Proof.
  red.
  intro.
  unfold comp.
  rewrite fromStreamRep_OK.
  simpl.
  reflexivity.
Qed.

Lemma redecS_ext_strong : forall (A B: Type) (f f': TriS A -> B) (t: TriS A), f =e f' -> redecS f t == redecS f' t.
Proof.
  cofix Hc.
  intros A B f f' [[a es] r] H.
  apply eqst; simpl.
  apply injective_projections; simpl.
  apply H.
  reflexivity.
  apply Hc.
  assumption.
Qed.

(* not even necessary thanks to the type classes:
Corollary redecS_ext : forall (A B: Type) (f f': TriS A -> B) (t: TriS A), f =e f' -> redecS f t ==^ redecS f' t.
Proof.
  intros.
  apply EqStImpBisimS.
  apply redecS_ext_strong.
  assumption.
Qed.
*)
 
Lemma comonad2_ALT (A: Type) (t: Tri A): redec (top(A:= A)) t ~~ t.
Proof.
  rewrite redec_redec_indirS.
  rewrite (fSR_tSR t) at 2.
  apply fromStreamRepM.
  rewrite (redecS_ext_strong _ (comonad2_ALT_aux(A:= A))).
  rewrite redecS_redecS'.
  apply EqStImpBisimS.
  apply comonad2S'.

  clear t; revert A.
  exact top_cong.
Qed.

Lemma redecS_ext_strong2 (A B: Type) (f: TriS A -> B)(fC: fcompatS f)(t t': TriS A) :
  t ==^t' -> redecS f t ==^ redecS f t'.
Proof.
  intros H.
  rewrite redecS_redecS_indir, redecS_redecS_indir ; try assumption.
  apply toStreamRepM, redec_cong.
  intros t1 t2 H1.
  apply fC.
  apply toStreamRepM, H1.
  apply fromStreamRepM, H.
Qed.

Lemma redecS_redecS'_weaker (A B: Type) (f: TriS A -> B)(fC: fcompatS f)(t t': TriS A) : 
  t ==^t' -> redecS f t ==^ redecS' f t'.
Proof.
  intros H.
  rewrite <- redecS_redecS'.
  apply redecS_ext_strong2 ; assumption.
Qed.

Lemma comonad3_ALT_aux (A B: Type) (f: Tri A -> B)(fC: fcompat f): 
  forall t, redec f (fromStreamRep t) ~~ fromStreamRep (redecS' (f o @fromStreamRep _) t).
Proof.
  intros t.
  rewrite redec_redec_indirS ; try assumption.
  apply fromStreamRepM.
  apply redecS_redecS'_weaker.
  apply f_fromStreamRepM, fC.
  symmetry.
  apply tSR_fSR.
Qed.

Lemma fromStreamRep_inj (A: Type) (t t': TriS A): 
  fromStreamRep t ~~ fromStreamRep t' -> t ==^ t'.
Proof.
  intros H.
  rewrite (tSR_fSR t), (tSR_fSR t').
  rewrite H.
  reflexivity.
Qed.

Lemma redec_redecS' (A B: Type) (f: Tri A -> B)(fC: fcompat f)(t: Tri A): 
  toStreamRep (redec f t) ==^ redecS' (f o @fromStreamRep _) (toStreamRep t).
Proof.
  apply fromStreamRep_inj.
  rewrite <- fSR_tSR.
  rewrite <- redecS_redecS'.
  apply redec_redec_indirS, fC.
Qed.

Lemma comonad3_ALT_weaker (A B C: Type) (f: Tri A -> B) (g: Tri B -> C) (t: Tri A): 
  fcompat f -> fcompat g -> redec (g o redec f) t ~~ redec g (redec f t).
Proof.
  intros H1 H2.
  repeat rewrite redec_redec_indirS ; try assumption.  
  apply fromStreamRepM.
  rewrite (@redecS_ext_strong _ _ _
    (g o @fromStreamRep _ o (redecS' (f o @fromStreamRep _)))).
  do 2 rewrite redecS_redecS'.
  rewrite comonad3S'.
  rewrite <- redecS_redecS'.
  symmetry.
  rewrite <- redecS_redecS'.
  apply redecS_ext_strong2.
  apply f_fromStreamRepM, H2.
  apply redec_redecS', H1.
  intros t1.
  apply H2.
  apply comonad3_ALT_aux, H1.
  intros t1 t2 H3.
  apply H2.
  apply redec_cong, H3.
  apply H1.
Qed.

Class WeakerComonad (T: Type -> Type)(E_eq: Equiv T) := 
  {wcounit': forall A: Type, T A -> A; wcobind': forall (A B: Type), (T A -> B) -> T A -> T B; 
   wcomonad1gen': forall (A B: Type)(f: T A -> B)(t: T A), Proper (E_eq A ==> eq) f -> wcounit' (wcobind' f t) = f t;
   wcomonad2gen': forall (A: Type)(t: T A), wcobind' (wcounit'(A:= A)) t ~~^ t;
   wcomonad3gen': forall (A B C: Type)(f: T A -> B)(g: T B -> C)(t: T A), Proper (E_eq A ==> eq) f ->
     Proper (E_eq B ==> eq) g -> wcobind' (g o wcobind' f) t ~~^ wcobind' g (wcobind' f t)}.

Instance TriComonad_ALT: WeakerComonad(T:= Tri) bisimilar.
  apply (Build_WeakerComonad bisimilar top redec).
  intros.
  apply comonad1_ALT_weaker.
  assumption.
  exact comonad2_ALT.
  intros.
  apply comonad3_ALT_weaker; assumption.
Defined.

End TriangleDef.
