(** This file implements boolsets as functions into Prop. *)
From stdpp Require Export prelude.
From stdpp Require Import options.

Record boolset (A : Type) : Type := BoolSet { boolset_car : A → bool }.
Global Arguments BoolSet {_} _ : assert.
Global Arguments boolset_car {_} _ _ : assert.

Global Instance boolset_top {A} : Top (boolset A) := BoolSet (λ _, true).
Global Instance boolset_empty {A} : Empty (boolset A) := BoolSet (λ _, false).
Global Instance boolset_singleton `{EqDecision A} : Singleton A (boolset A) := λ x,
  BoolSet (λ y, bool_decide (y = x)).
Global Instance boolset_elem_of {A} : ElemOf A (boolset A) := λ x X, boolset_car X x.
Global Instance boolset_union {A} : Union (boolset A) := λ X1 X2,
  BoolSet (λ x, boolset_car X1 x || boolset_car X2 x).
Global Instance boolset_intersection {A} : Intersection (boolset A) := λ X1 X2,
  BoolSet (λ x, boolset_car X1 x && boolset_car X2 x).
Global Instance boolset_difference {A} : Difference (boolset A) := λ X1 X2,
  BoolSet (λ x, boolset_car X1 x && negb (boolset_car X2 x)).
Global Instance boolset_cprod {A B} :
  CProd (boolset A) (boolset B) (boolset (A * B)) := λ X1 X2,
  BoolSet (λ x, boolset_car X1 x.1 && boolset_car X2 x.2).

Global Instance boolset_set `{!EqDecision A} : Set_ A (boolset A).
Proof.
  split; [split| |].
  - by intros x ?.
  - by intros x y; rewrite <-(bool_decide_spec (x = y)).
  - split; [apply orb_prop_elim | apply orb_prop_intro].
  - split; [apply andb_prop_elim | apply andb_prop_intro].
  - intros X Y x; unfold elem_of, boolset_elem_of; simpl.
    destruct (boolset_car X x), (boolset_car Y x); simpl; tauto.
Qed.
Global Instance boolset_top_set `{!EqDecision A} : TopSet A (boolset A).
Proof. by split. Qed.
Global Instance boolset_elem_of_dec {A} : RelDecision (∈@{boolset A}).
Proof. refine (λ x X, cast_if (decide (boolset_car X x))); done. Defined.

Lemma elem_of_boolset_cprod {A B} (X1 : boolset A) (X2 : boolset B) (x : A * B) :
  x ∈ cprod X1 X2 ↔ x.1 ∈ X1 ∧ x.2 ∈ X2.
Proof. apply andb_True. Qed.

Global Instance set_unfold_boolset_cprod {A B} (X1 : boolset A) (X2 : boolset B) x P Q :
  SetUnfoldElemOf x.1 X1 P → SetUnfoldElemOf x.2 X2 Q →
  SetUnfoldElemOf x (cprod X1 X2) (P ∧ Q).
Proof.
  intros ??; constructor.
  by rewrite elem_of_boolset_cprod, (set_unfold_elem_of x.1 X1 P),
    (set_unfold_elem_of x.2 X2 Q).
Qed.

Global Typeclasses Opaque boolset_elem_of.
Global Opaque boolset_empty boolset_singleton boolset_union
  boolset_intersection boolset_difference boolset_cprod.
