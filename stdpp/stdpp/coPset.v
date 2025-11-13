(** This file implements an abstract type [coPset] of (possibly infinite) sets
of positive binary natural numbers ([positive]). This type supports the
following operations:

- the empty set;
- a singleton set;
- the full set;
- union, intersection, and complement;
- picking an element in an infinite set;
- splitting a set into two disjoint subsets in such a way that if the original
  set is infinite then both parts are infinite;
- the (infinite) set of all numbers that have a certain suffix;
- conversions to and from other representations of sets.

Also, these sets support the following tests
(that is, the following properties are decidable):

- equality;
- membership;
- disjointness;
- inclusion;
- finiteness.

Equality is extensional: that is, two sets are equal
if and only if they have the same elements:
[X = Y ↔ ∀ x, x ∈ X ↔ x ∈ Y]. *)

(** Since [positive]s are bitstrings, we encode a set as a decision tree
(a trie) that maps bitstrings to Booleans. *)
From stdpp Require Export sets.
From stdpp Require Import pmap gmap mapset.
From stdpp Require Import options.
Local Open Scope positive_scope.

(** * The raw tree data structure *)

(** [coPLeaf false] is the empty set; [coPLeaf true] is the full set. *)
(** In [coPNode b l r], the Boolean flag [b] indicates whether the number
1 is a member of the set, while the subtrees [l] and [r] must be
consulted to determine whether a number of the form [2i] or [2i+1]
is a member of the set. *)
(** This [Inductive] is internal, but Rocq does not allow us to make it
[Local]. *)
Inductive coPset_raw :=
  | coPLeaf : bool → coPset_raw
  | coPNode : bool → coPset_raw → coPset_raw → coPset_raw.
Local Instance coPset_raw_eq_dec : EqDecision coPset_raw.
Proof. solve_decision. Defined.

(** The type of raw trees (above) offers several representations of the
empty set and several representations of the full set. In order to
achieve extensional equality, this redundancy must be eliminated.
This is achieved by imposing a well-formedness criterion on trees. *)
Local Fixpoint coPset_wf (t : coPset_raw) : bool :=
  match t with
  | coPLeaf _ => true
  | coPNode true (coPLeaf true) (coPLeaf true) => false
  | coPNode false (coPLeaf false) (coPLeaf false) => false
  | coPNode _ l r => coPset_wf l && coPset_wf r
  end.
Local Arguments coPset_wf !_ / : simpl nomatch, assert.

Local Lemma coPNode_wf b l r :
  coPset_wf l → coPset_wf r →
  (l = coPLeaf true → r = coPLeaf true → b = true → False) →
  (l = coPLeaf false → r = coPLeaf false → b = false → False) →
  coPset_wf (coPNode b l r).
Proof. destruct b, l as [[]|], r as [[]|]; naive_solver. Qed.

Local Lemma coPNode_wf_l b l r : coPset_wf (coPNode b l r) → coPset_wf l.
Proof. destruct b, l as [[]|],r as [[]|]; simpl; rewrite ?andb_True; tauto. Qed.
Local Lemma coPNode_wf_r b l r : coPset_wf (coPNode b l r) → coPset_wf r.
Proof. destruct b, l as [[]|],r as [[]|]; simpl; rewrite ?andb_True; tauto. Qed.
Local Hint Immediate coPNode_wf_l coPNode_wf_r : core.

(** The smart constructor [coPNode'] preserves well-formedness. *)
Local Definition coPNode' (b : bool) (l r : coPset_raw) : coPset_raw :=
  match b, l, r with
  | true, coPLeaf true, coPLeaf true => coPLeaf true
  | false, coPLeaf false, coPLeaf false => coPLeaf false
  | _, _, _ => coPNode b l r
  end.
Local Arguments coPNode' : simpl never.
Local Lemma coPNode'_wf b l r :
  coPset_wf l → coPset_wf r → coPset_wf (coPNode' b l r).
Proof. destruct b, l as [[]|], r as [[]|]; simpl; auto. Qed.
Local Hint Resolve coPNode'_wf : core.

(** The membership test. *)
Local Fixpoint coPset_elem_of_raw (p : positive) (t : coPset_raw) {struct t} : bool :=
  match t, p with
  | coPLeaf b, _ => b
  | coPNode b l r, 1 => b
  | coPNode _ l _, p~0 => coPset_elem_of_raw p l
  | coPNode _ _ r, p~1 => coPset_elem_of_raw p r
  end.
Local Notation e_of := coPset_elem_of_raw.
Local Arguments coPset_elem_of_raw _ !_ / : simpl nomatch, assert.
Local Lemma coPset_elem_of_node b l r p :
  e_of p (coPNode' b l r) = e_of p (coPNode b l r).
Proof. by destruct p, b, l as [[]|], r as [[]|]. Qed.

(** The full set and the empty set have a unique representation. *)
Local Lemma coPLeaf_wf t b : (∀ p, e_of p t = b) → coPset_wf t → t = coPLeaf b.
Proof.
  induction t as [b'|b' l IHl r IHr]; intros Ht ?; [f_equal; apply (Ht 1)|].
  assert (b' = b) by (apply (Ht 1)); subst.
  assert (l = coPLeaf b) as -> by (apply IHl; try apply (λ p, Ht (p~0)); eauto).
  assert (r = coPLeaf b) as -> by (apply IHr; try apply (λ p, Ht (p~1)); eauto).
  by destruct b.
Qed.

(** Equality is extensional. *)
Local Lemma coPset_eq t1 t2 :
  (∀ p, e_of p t1 = e_of p t2) → coPset_wf t1 → coPset_wf t2 → t1 = t2.
Proof.
  revert t2.
  induction t1 as [b1|b1 l1 IHl r1 IHr]; intros [b2|b2 l2 r2] Ht ??; simpl in *.
  - f_equal; apply (Ht 1).
  - by discriminate (coPLeaf_wf (coPNode b2 l2 r2) b1).
  - by discriminate (coPLeaf_wf (coPNode b1 l1 r1) b2).
  - f_equal; [apply (Ht 1)| |].
    + apply IHl; try apply (λ x, Ht (x~0)); eauto.
    + apply IHr; try apply (λ x, Ht (x~1)); eauto.
Qed.

(** Singleton. *)
Local Fixpoint coPset_singleton_raw (p : positive) : coPset_raw :=
  match p with
  | 1 => coPNode true (coPLeaf false) (coPLeaf false)
  | p~0 => coPNode' false (coPset_singleton_raw p) (coPLeaf false)
  | p~1 => coPNode' false (coPLeaf false) (coPset_singleton_raw p)
  end.

(** Union. *)
Local Instance coPset_union_raw : Union coPset_raw :=
  fix go t1 t2 := let _ : Union _ := @go in
  match t1, t2 with
  | coPLeaf false, coPLeaf false => coPLeaf false
  | _, coPLeaf true => coPLeaf true
  | coPLeaf true, _ => coPLeaf true
  | coPNode b l r, coPLeaf false => coPNode b l r
  | coPLeaf false, coPNode b l r => coPNode b l r
  | coPNode b1 l1 r1, coPNode b2 l2 r2 => coPNode' (b1||b2) (l1 ∪ l2) (r1 ∪ r2)
  end.
Local Arguments union _ _!_ !_ / : assert.

(** Intersection. *)
Local Instance coPset_intersection_raw : Intersection coPset_raw :=
  fix go t1 t2 := let _ : Intersection _ := @go in
  match t1, t2 with
  | coPLeaf true, coPLeaf true => coPLeaf true
  | _, coPLeaf false => coPLeaf false
  | coPLeaf false, _ => coPLeaf false
  | coPNode b l r, coPLeaf true => coPNode b l r
  | coPLeaf true, coPNode b l r => coPNode b l r
  | coPNode b1 l1 r1, coPNode b2 l2 r2 => coPNode' (b1&&b2) (l1 ∩ l2) (r1 ∩ r2)
  end.
Local Arguments intersection _ _!_ !_ / : assert.

(** Complement. *)
Local Fixpoint coPset_opp_raw (t : coPset_raw) : coPset_raw :=
  match t with
  | coPLeaf b => coPLeaf (negb b)
  | coPNode b l r => coPNode' (negb b) (coPset_opp_raw l) (coPset_opp_raw r)
  end.

(** Well-formedness for the above operations. *)
Local Lemma coPset_singleton_wf p : coPset_wf (coPset_singleton_raw p).
Proof. induction p; simpl; eauto. Qed.
Local Lemma coPset_union_wf t1 t2 :
  coPset_wf t1 → coPset_wf t2 → coPset_wf (t1 ∪ t2).
Proof. revert t2; induction t1 as [[]|[]]; intros [[]|[] ??]; simpl; eauto. Qed.
Local Lemma coPset_intersection_wf t1 t2 :
  coPset_wf t1 → coPset_wf t2 → coPset_wf (t1 ∩ t2).
Proof. revert t2; induction t1 as [[]|[]]; intros [[]|[] ??]; simpl; eauto. Qed.
Local Lemma coPset_opp_wf t : coPset_wf (coPset_opp_raw t).
Proof. induction t as [[]|[]]; simpl; eauto. Qed.

(** Correctness for the above operations. *)
Local Lemma coPset_elem_of_singleton p q :
  e_of p (coPset_singleton_raw q) ↔ p = q.
Proof.
  split; [|by intros <-; induction p; simpl; rewrite ?coPset_elem_of_node].
  by revert q; induction p; intros [?|?|]; simpl;
    rewrite ?coPset_elem_of_node; intros; f_equal/=; auto.
Qed.
Local Lemma coPset_elem_of_union t1 t2 p :
  e_of p (t1 ∪ t2) = e_of p t1 || e_of p t2.
Proof.
  by revert t2 p; induction t1 as [[]|[]]; intros [[]|[] ??] [?|?|]; simpl;
    rewrite ?coPset_elem_of_node; simpl;
    rewrite ?orb_true_l, ?orb_false_l, ?orb_true_r, ?orb_false_r.
Qed.
Local Lemma coPset_elem_of_intersection t1 t2 p :
  e_of p (t1 ∩ t2) = e_of p t1 && e_of p t2.
Proof.
  by revert t2 p; induction t1 as [[]|[]]; intros [[]|[] ??] [?|?|]; simpl;
    rewrite ?coPset_elem_of_node; simpl;
    rewrite ?andb_true_l, ?andb_false_l, ?andb_true_r, ?andb_false_r.
Qed.
Local Lemma coPset_elem_of_opp t p : e_of p (coPset_opp_raw t) = negb (e_of p t).
Proof.
  by revert p; induction t as [[]|[]]; intros [?|?|]; simpl;
    rewrite ?coPset_elem_of_node; simpl.
Qed.

(** * The abstract type [coPset] *)

(** A set is a well-formed tree. *)
Definition coPset := { t | coPset_wf t }.

(** All operations are redefined at the level of [coPset]. *)
Global Instance coPset_singleton : Singleton positive coPset := λ p,
  coPset_singleton_raw p ↾ coPset_singleton_wf _.
Global Instance coPset_elem_of : ElemOf positive coPset := λ p X, e_of p (`X).
Global Instance coPset_empty : Empty coPset := coPLeaf false ↾ I.
Global Instance coPset_top : Top coPset := coPLeaf true ↾ I.
Global Instance coPset_union : Union coPset := λ X Y,
  let (t1,Ht1) := X in let (t2,Ht2) := Y in
  (t1 ∪ t2) ↾ coPset_union_wf _ _ Ht1 Ht2.
Global Instance coPset_intersection : Intersection coPset := λ X Y,
  let (t1,Ht1) := X in let (t2,Ht2) := Y in
  (t1 ∩ t2) ↾ coPset_intersection_wf _ _ Ht1 Ht2.
Global Instance coPset_difference : Difference coPset := λ X Y,
  let (t1,Ht1) := X in let (t2,Ht2) := Y in
  (t1 ∩ coPset_opp_raw t2) ↾ coPset_intersection_wf _ _ Ht1 (coPset_opp_wf _).

Global Instance coPset_set : Set_ positive coPset.
Proof.
  split; [split| |].
  - by intros ??.
  - intros p q. apply coPset_elem_of_singleton.
  - intros [t] [t'] p; unfold elem_of, coPset_elem_of, coPset_union; simpl.
    by rewrite coPset_elem_of_union, orb_True.
  - intros [t] [t'] p; unfold elem_of,coPset_elem_of,coPset_intersection; simpl.
    by rewrite coPset_elem_of_intersection, andb_True.
  - intros [t] [t'] p; unfold elem_of, coPset_elem_of, coPset_difference; simpl.
    by rewrite coPset_elem_of_intersection,
      coPset_elem_of_opp, andb_True, negb_True.
Qed.
Global Instance coPset_top_set : TopSet positive coPset.
Proof. by split. Qed.

(** Iris and specifically [solve_ndisj] heavily rely on this hint. *)
Local Definition coPset_top_subseteq := top_subseteq (C:=coPset).
Global Hint Resolve coPset_top_subseteq : core.

(** Extensional equality. *)
Global Instance coPset_leibniz : LeibnizEquiv coPset.
Proof.
  intros X Y; rewrite set_equiv; intros HXY.
  apply (sig_eq_pi _), coPset_eq; try apply @proj2_sig.
  intros p; apply eq_bool_prop_intro, (HXY p).
Qed.

(** Decidable membership. *)
Global Instance coPset_elem_of_dec : RelDecision (∈@{coPset}).
Proof. solve_decision. Defined.
(** Decidable equality. *)
Global Instance coPset_equiv_dec : RelDecision (≡@{coPset}).
Proof. refine (λ X Y, cast_if (decide (X = Y))); abstract (by fold_leibniz). Defined.
(** Decidable disjointness. *)
Global Instance mapset_disjoint_dec : RelDecision (##@{coPset}).
Proof.
 refine (λ X Y, cast_if (decide (X ∩ Y = ∅)));
  abstract (by rewrite disjoint_intersection_L).
Defined.
(** Decidable inclusion. *)
Global Instance mapset_subseteq_dec : RelDecision (⊆@{coPset}).
Proof.
 refine (λ X Y, cast_if (decide (X ∪ Y = Y))); abstract (by rewrite subseteq_union_L).
Defined.

(** * Finiteness *)
(** The internal function [coPset_finite] determines whether a (raw) set is
finite. This definition is internal, use [set_finite] instead. *)
Local Fixpoint coPset_finite (t : coPset_raw) : bool :=
  match t with
  | coPLeaf b => negb b | coPNode b l r => coPset_finite l && coPset_finite r
  end.
Local Lemma coPset_finite_node b l r :
  coPset_finite (coPNode' b l r) = coPset_finite l && coPset_finite r.
Proof. by destruct b, l as [[]|], r as [[]|]. Qed.
(** This function is correct; it is equivalent to [set_finite], which is
    defined in terms of set membership. *)
Local Lemma coPset_finite_spec X : set_finite X ↔ coPset_finite (`X).
Proof.
  destruct X as [t Ht].
  unfold set_finite, elem_of at 1, coPset_elem_of; simpl; clear Ht; split.
  - induction t as [b|b l IHl r IHr]; simpl.
    { destruct b; simpl; [intros [l Hl]|done].
      by apply (infinite_is_fresh l), Hl. }
    intros [ll Hll]; rewrite andb_True; split.
    + apply IHl; exists (omap (maybe (~0)) ll); intros i.
      rewrite list_elem_of_omap; intros; exists (i~0); auto.
    + apply IHr; exists (omap (maybe (~1)) ll); intros i.
      rewrite list_elem_of_omap; intros; exists (i~1); auto.
  - induction t as [b|b l IHl r IHr]; simpl; [by exists []; destruct b|].
    rewrite andb_True; intros [??]; destruct IHl as [ll ?], IHr as [rl ?]; auto.
    exists ([1] ++ ((~0) <$> ll) ++ ((~1) <$> rl))%list; intros [i|i|]; simpl;
      rewrite elem_of_cons, elem_of_app, !list_elem_of_fmap; naive_solver.
Qed.
(** Thus, finiteness is decidable. *)
Global Instance coPset_finite_dec (X : coPset) : Decision (set_finite X).
Proof.
  refine (cast_if (decide (coPset_finite (`X)))); by rewrite coPset_finite_spec.
Defined.

(** * Picking an element out of a non-empty set *)

(** Provided that the set [X] is non-empty, [coPpick X] yields an element of
this set. Note that [coPpick] is implemented by depth-first search, so
using it repeatedly to obtain elements [x] and inserting these elements
[x] into some set [Y] will give rise to a very unbalanced tree. *)
Local Fixpoint coPpick_raw (t : coPset_raw) : option positive :=
  match t with
  | coPLeaf true | coPNode true _ _ => Some 1
  | coPLeaf false => None
  | coPNode false l r =>
     match coPpick_raw l with
     | Some i => Some (i~0) | None => (~1) <$> coPpick_raw r
     end
  end.
Definition coPpick (X : coPset) : positive := default 1 (coPpick_raw (`X)).

Local Lemma coPpick_raw_elem_of t i : coPpick_raw t = Some i → e_of i t.
Proof.
  revert i; induction t as [[]|[] l ? r]; intros i ?; simplify_eq/=; auto.
  destruct (coPpick_raw l); simplify_option_eq; auto.
Qed.
Local Lemma coPpick_raw_None t i : coPpick_raw t = None → ¬e_of i t.
Proof.
  revert i. induction t as [[]|[] l ? r]; intros [] ?;
    repeat (case_match || simplify_option_eq); auto.
Qed.
Lemma coPpick_elem_of X : X ≠ ∅ → coPpick X ∈ X.
Proof.
  rewrite elem_of_equiv_empty_L.
  destruct X as [t ?]; unfold coPpick; destruct (coPpick_raw _) as [j|] eqn:?.
  - by intros; apply coPpick_raw_elem_of.
  - intros []; intros ?. by apply coPpick_raw_None.
Qed.

(** * Conversion to finite sets *)
(** [coPset_to_Pset] converts a set, as defined in this library,
    to a finite set, as defined in the library [stdpp.pmap].
    This conversion is correct only if the original set is finite. *)
Local Fixpoint coPset_to_Pset_raw (t : coPset_raw) : Pmap () :=
  match t with
  | coPLeaf _ => PEmpty
  | coPNode false l r => pmap.PNode (coPset_to_Pset_raw l) None (coPset_to_Pset_raw r)
  | coPNode true l r => pmap.PNode (coPset_to_Pset_raw l) (Some ()) (coPset_to_Pset_raw r)
  end.
Definition coPset_to_Pset (X : coPset) : Pset :=
  let (t,Ht) := X in Mapset (coPset_to_Pset_raw t).
Lemma elem_of_coPset_to_Pset X i : set_finite X → i ∈ coPset_to_Pset X ↔ i ∈ X.
Proof.
  rewrite coPset_finite_spec; destruct X as [t Ht].
  change (coPset_finite t → coPset_to_Pset_raw t !! i = Some () ↔ e_of i t).
  clear Ht; revert i; induction t as [[]|[] l IHl r IHr]; intros [i|i|];
    simpl; rewrite ?andb_True, ?pmap.Pmap_lookup_PNode; naive_solver.
Qed.

(** * Conversion from finite sets *)
(** [Pset_to_coPset] converts a finite set,
    as defined in the library [stdpp.pmap],
    to a set, as defined in this library.
    This set is of course finite. *)
Local Definition Pset_to_coPset_raw_aux (go : Pmap_ne () → coPset_raw)
    (mt : Pmap ()) : coPset_raw :=
  match mt with PNodes t => go t | PEmpty => coPLeaf false end.
Local Fixpoint Pset_ne_to_coPset_raw (t : Pmap_ne ()) : coPset_raw :=
  pmap.Pmap_ne_case t $ λ ml mx mr,
    coPNode match mx with Some _ => true | None => false end
      (Pset_to_coPset_raw_aux Pset_ne_to_coPset_raw ml)
      (Pset_to_coPset_raw_aux Pset_ne_to_coPset_raw mr).
Local Definition Pset_to_coPset_raw : Pmap () → coPset_raw :=
  Pset_to_coPset_raw_aux Pset_ne_to_coPset_raw.

Local Lemma Pset_to_coPset_raw_PNode ml mx mr :
  pmap.PNode_valid ml mx mr →
  Pset_to_coPset_raw (pmap.PNode ml mx mr) =
    coPNode match mx with Some _ => true | None => false end
    (Pset_to_coPset_raw ml) (Pset_to_coPset_raw mr).
Proof. by destruct ml, mx, mr. Qed.
Local Lemma Pset_to_coPset_raw_wf t : coPset_wf (Pset_to_coPset_raw t).
Proof.
  induction t as [|ml mx mr] using pmap.Pmap_ind; [done|].
  rewrite Pset_to_coPset_raw_PNode by done.
  apply coPNode_wf; [done|done|..];
    destruct mx; destruct ml using pmap.Pmap_ind; destruct mr using pmap.Pmap_ind;
    rewrite ?Pset_to_coPset_raw_PNode by done; naive_solver.
Qed.
Local Lemma elem_of_Pset_to_coPset_raw i t :
  e_of i (Pset_to_coPset_raw t) ↔ t !! i = Some ().
Proof.
  revert i. induction t as [|ml mx mr] using pmap.Pmap_ind; [done|].
  intros []; rewrite Pset_to_coPset_raw_PNode,
    pmap.Pmap_lookup_PNode by done; destruct mx as [[]|]; naive_solver.
Qed.
Local Lemma Pset_to_coPset_raw_finite t : coPset_finite (Pset_to_coPset_raw t).
Proof.
  induction t as [|ml mx mr] using pmap.Pmap_ind; [done|].
  rewrite Pset_to_coPset_raw_PNode by done. destruct mx; naive_solver.
Qed.

(** The main conversion function. *)
Definition Pset_to_coPset (X : Pset) : coPset :=
  let 'Mapset t := X in Pset_to_coPset_raw t ↾ Pset_to_coPset_raw_wf _.
(* This conversion function is correct. *)
Lemma elem_of_Pset_to_coPset X i : i ∈ Pset_to_coPset X ↔ i ∈ X.
Proof. destruct X; apply elem_of_Pset_to_coPset_raw. Qed.
(* This conversion function produces a finite set. *)
Lemma Pset_to_coPset_finite X : set_finite (Pset_to_coPset X).
Proof. apply coPset_finite_spec; destruct X; apply Pset_to_coPset_raw_finite. Qed.

Global Instance set_unfold_Pset_to_coPSet x X P :
  SetUnfoldElemOf x X P →
  SetUnfoldElemOf x (Pset_to_coPset X) P.
Proof.
  constructor. rewrite elem_of_Pset_to_coPset. by apply set_unfold_elem_of.
Qed.

(** * Conversion to and from gsets of positives *)
Definition coPset_to_gset (X : coPset) : gset positive :=
  let 'Mapset m := coPset_to_Pset X in
  Mapset (pmap_to_gmap m).

Definition gset_to_coPset (X : gset positive) : coPset :=
  let 'Mapset m := X in
  Pset_to_coPset_raw (gmap_to_pmap m) ↾ Pset_to_coPset_raw_wf _.

Lemma elem_of_coPset_to_gset X i : set_finite X → i ∈ coPset_to_gset X ↔ i ∈ X.
Proof.
  intros ?. rewrite <-elem_of_coPset_to_Pset by done. destruct X as [X ?].
  unfold elem_of, gset_elem_of, mapset_elem_of, coPset_to_gset; simpl.
  by rewrite lookup_pmap_to_gmap.
Qed.

Lemma elem_of_gset_to_coPset X i : i ∈ gset_to_coPset X ↔ i ∈ X.
Proof.
  destruct X as [m]. unfold elem_of, coPset_elem_of; simpl.
  by rewrite elem_of_Pset_to_coPset_raw, lookup_gmap_to_pmap.
Qed.
Lemma gset_to_coPset_finite X : set_finite (gset_to_coPset X).
Proof.
  apply coPset_finite_spec; destruct X as [[?]]; apply Pset_to_coPset_raw_finite.
Qed.

Global Instance set_unfold_gset_to_coPSet x X P :
  SetUnfoldElemOf x X P →
  SetUnfoldElemOf x (gset_to_coPset X) P.
Proof.
  constructor. rewrite elem_of_gset_to_coPset. by apply set_unfold_elem_of.
Qed.

(** * Infiniteness *)
(* TODO: The following lemma should probably be proved at a more generic level.
   It does not depend on the details of [coPset]. It depends only on the
   existence of a choice function out of an infinite set. *)
Lemma coPset_infinite_finite (X : coPset) : set_infinite X ↔ ¬set_finite X.
Proof.
  split; [intros ??; by apply (set_not_infinite_finite X)|].
  intros Hfin xs. exists (coPpick (X ∖ list_to_set xs)).
  cut (coPpick (X ∖ list_to_set xs) ∈ X ∖ list_to_set xs); [set_solver|].
  apply coPpick_elem_of; intros Hfin'.
  apply Hfin, (difference_finite_inv _ (list_to_set xs)).
  - apply list_to_set_finite.
  - rewrite Hfin'. apply empty_finite.
Qed.
(** A set is finite if and only if it is not infinite. *)
Lemma coPset_finite_infinite (X : coPset) : set_finite X ↔ ¬set_infinite X.
Proof. rewrite coPset_infinite_finite. split; [tauto|apply dec_stable]. Qed.
(** Infiniteness is decidable. *)
Global Instance coPset_infinite_dec (X : coPset) : Decision (set_infinite X).
Proof.
  refine (cast_if (decide (¬set_finite X))); by rewrite coPset_infinite_finite.
Defined.

(** * Inverse suffix closure *)
(** [coPset_suffixes q] is the set of all numbers [p] such that [q] is a suffix
of [p], when these numbers are viewed as sequences of bits. In other words, it
is the set of all numbers that have the suffix [q]. It is always an infinite
set. *)
Local Fixpoint coPset_suffixes_raw (p : positive) : coPset_raw :=
  match p with
  | 1 => coPLeaf true
  | p~0 => coPNode' false (coPset_suffixes_raw p) (coPLeaf false)
  | p~1 => coPNode' false (coPLeaf false) (coPset_suffixes_raw p)
  end.
Local Lemma coPset_suffixes_wf p : coPset_wf (coPset_suffixes_raw p).
Proof. induction p; simpl; eauto. Qed.

Definition coPset_suffixes (p : positive) : coPset :=
  coPset_suffixes_raw p ↾ coPset_suffixes_wf _.
Lemma elem_coPset_suffixes p q : p ∈ coPset_suffixes q ↔ ∃ q', p = q' ++ q.
Proof.
  unfold elem_of, coPset_elem_of; simpl; split.
  - revert p; induction q; intros [?|?|]; simpl;
      rewrite ?coPset_elem_of_node; naive_solver.
  - by intros [q' ->]; induction q; simpl; rewrite ?coPset_elem_of_node.
Qed.

Lemma coPset_suffixes_not_finite p : ¬set_finite (coPset_suffixes p).
Proof.
  rewrite coPset_finite_spec; simpl.
  induction p; simpl; rewrite ?coPset_finite_node, ?andb_True; naive_solver.
Qed.
Lemma coPset_suffixes_infinite p : set_infinite (coPset_suffixes p).
Proof. apply coPset_infinite_finite, coPset_suffixes_not_finite. Qed.

(** * Splitting a set *)
(** Every infinite [X : coPset] can be split into two disjoint parts, which are
infinite sets. In proofs, you typically want to use the lemmas [coPset_split]
and [coPset_split_infinite]. Use the functions [coPset_l] and [coPset_r] if you
need a constructive witness. *)
Local Fixpoint coPset_l_raw (t : coPset_raw) : coPset_raw :=
  match t with
  | coPLeaf false => coPLeaf false
  | coPLeaf true => coPNode true (coPLeaf true) (coPLeaf false)
  | coPNode b l r => coPNode' b (coPset_l_raw l) (coPset_l_raw r)
  end.
Local Fixpoint coPset_r_raw (t : coPset_raw) : coPset_raw :=
  match t with
  | coPLeaf false => coPLeaf false
  | coPLeaf true => coPNode false (coPLeaf false) (coPLeaf true)
  | coPNode b l r => coPNode' false (coPset_r_raw l) (coPset_r_raw r)
  end.

Local Lemma coPset_l_wf t : coPset_wf (coPset_l_raw t).
Proof. induction t as [[]|]; simpl; auto. Qed.
Local Lemma coPset_r_wf t : coPset_wf (coPset_r_raw t).
Proof. induction t as [[]|]; simpl; auto. Qed.

(* A set [X] can be split into two sets [coPset_l X] and [coPset_r X]. *)
Definition coPset_l (X : coPset) : coPset :=
  let (t,Ht) := X in coPset_l_raw t ↾ coPset_l_wf _.
Definition coPset_r (X : coPset) : coPset :=
  let (t,Ht) := X in coPset_r_raw t ↾ coPset_r_wf _.

(** These two sets are disjoint. *)
Lemma coPset_lr_disjoint X : coPset_l X ∩ coPset_r X = ∅.
Proof.
  apply elem_of_equiv_empty_L; intros p; apply Is_true_false.
  destruct X as [t Ht]; simpl; clear Ht; rewrite coPset_elem_of_intersection.
  revert p; induction t as [[]|[]]; intros [?|?|]; simpl;
    rewrite ?coPset_elem_of_node; simpl;
    rewrite ?orb_true_l, ?orb_false_l, ?orb_true_r, ?orb_false_r; auto.
Qed.
(** Their union is [X]. Thus, they form a partition of [X]. *)
Lemma coPset_lr_union X : coPset_l X ∪ coPset_r X = X.
Proof.
  apply set_eq; intros p; apply eq_bool_prop_elim.
  destruct X as [t Ht]; simpl; clear Ht; rewrite coPset_elem_of_union.
  revert p; induction t as [[]|[]]; intros [?|?|]; simpl;
    rewrite ?coPset_elem_of_node; simpl;
    rewrite ?orb_true_l, ?orb_false_l, ?orb_true_r, ?orb_false_r; auto.
Qed.
(** If [X] is infinite then both parts are infinite as well. *)
Lemma coPset_l_finite X : set_finite (coPset_l X) → set_finite X.
Proof.
  rewrite !coPset_finite_spec; destruct X as [t Ht]; simpl; clear Ht.
  induction t as [[]|]; simpl; rewrite ?coPset_finite_node, ?andb_True; tauto.
Qed.
Lemma coPset_r_finite X : set_finite (coPset_r X) → set_finite X.
Proof.
  rewrite !coPset_finite_spec; destruct X as [t Ht]; simpl; clear Ht.
  induction t as [[]|]; simpl; rewrite ?coPset_finite_node, ?andb_True; tauto.
Qed.
Lemma coPset_split (X : coPset) :
  ¬set_finite X →
  ∃ X1 X2, X = X1 ∪ X2 ∧ X1 ∩ X2 = ∅ ∧ ¬set_finite X1 ∧ ¬set_finite X2.
Proof.
  exists (coPset_l X), (coPset_r X); eauto 10 using coPset_lr_union,
    coPset_lr_disjoint, coPset_l_finite, coPset_r_finite.
Qed.
(** Thus, in summary, every infinite set [X] can be split into two
disjoint parts, which are infinite sets. *)
Lemma coPset_split_infinite (X : coPset) :
  set_infinite X →
  ∃ X1 X2, X = X1 ∪ X2 ∧ X1 ∩ X2 = ∅ ∧ set_infinite X1 ∧ set_infinite X2.
Proof.
  setoid_rewrite coPset_infinite_finite.
  eapply coPset_split.
Qed.
