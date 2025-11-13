(** This file implements the type [topGset A] of finite sets with a top element,
of elements of any countable type [A].

Unlike [coGset], the only cofinite element of [topGset] is its top element,
[⊤]. In particular, this implies that if the union of two [topGset]s equals the
top element, then at least one of them must already be the top element. This
property, expressed by the lemma [topGset_union_top], does not hold for [coGset].
On the other hand, unlike [coGset], there is no notion of set difference (∖),
and hence [topGset] is not a [Set_], only a [SemiSet]. *)
From stdpp Require Export sets countable.
From stdpp Require Import decidable finite gmap coPset.
From stdpp Require Import options.

(* Pick up extra assumptions from section parameters. *)
Set Default Proof Using "Type*".

Inductive topGset `{Countable A} :=
  | FinGSet (X : gset A)
  | TopGSet.
Global Arguments topGset _ {_ _} : assert.

Global Instance topGset_eq_dec `{Countable A} : EqDecision (topGset A).
Proof. solve_decision. Defined.
Global Instance topGset_countable `{Countable A} : Countable (topGset A).
Proof.
  apply (inj_countable'
    (λ X, match X with FinGSet X => Some X | TopGSet => None end)
    (λ s, match s with Some X => FinGSet X | None => TopGSet end)).
  by intros [].
Qed.

Section topGset.
  Context `{Countable A}.

  Global Instance topGset_elem_of : ElemOf A (topGset A) := λ x X,
    match X with FinGSet X => x ∈ X | TopGSet => True end.
  Global Instance topGset_empty : Empty (topGset A) := FinGSet ∅.
  Global Instance topGset_top : Top (topGset A) := TopGSet.
  Global Instance topGset_singleton : Singleton A (topGset A) := λ x,
    FinGSet {[x]}.
  Global Instance topGset_union : Union (topGset A) := λ X Y,
    match X, Y with
    | FinGSet X, FinGSet Y => FinGSet (X ∪ Y)
    | _, _ => TopGSet
    end.

  Global Instance topGset_set : SemiSet A (topGset A).
  Proof.
    split.
    - by intros ??.
    - intros x y. unfold elem_of, topGset_elem_of; simpl.
      by rewrite elem_of_singleton.
    - intros [X|] [Y|] x; unfold elem_of, topGset_elem_of, topGset_union;
        naive_solver set_solver.
  Qed.
  Global Instance topGset_top_set : TopSet A (topGset A).
  Proof. by split. Qed.
End topGset.

Global Instance topGset_elem_of_dec `{Countable A} : RelDecision (∈@{topGset A}) :=
  λ x X,
  match X with
  | FinGSet X => decide_rel elem_of x X
  | TopGSet => left I
  end.

Section infinite.
  Context `{Countable A, Infinite A}.

  (** [topGset A] is only [LeibnizEquiv] for infinite [A], as, for example for
  [unit], [FinGSet {[ tt ]}] and [TopGSet] are equivalent ([≡]), but not equal
  ([=]). *)
  Global Instance topGset_leibniz : LeibnizEquiv (topGset A).
  Proof.
    intros [X|] [Y|]; rewrite set_equiv;
    unfold elem_of, topGset_elem_of; simpl; intros HXY.
    - f_equal. by apply leibniz_equiv.
    - destruct (exist_fresh X) as [? ?]; naive_solver.
    - destruct (exist_fresh Y) as [? ?]; naive_solver.
    - done.
  Qed.

  Global Instance topGset_equiv_dec : RelDecision (≡@{topGset A}).
  Proof.
    refine (λ X Y, cast_if (decide (X = Y))); abstract (by fold_leibniz).
  Defined.

  (** We need [Inhabited A] to conclude that [TopGSet] is not disjoint from
  itself. *)
  Global Program Instance topGset_disjoint_dec `{Inhabited A} :
      RelDecision (##@{topGset A}) := λ X Y,
    match X, Y return _ with
    | FinGSet X, FinGSet Y => cast_if (decide (X ## Y))
    | FinGSet X, TopGSet => cast_if (decide (X = ∅))
    | TopGSet, FinGSet Y => cast_if (decide (Y = ∅))
    | TopGSet, TopGSet => right _
    end.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. intros ??? X -> x []%not_elem_of_empty. Qed.
  Next Obligation.
    intros ??? X HX Hdisj. destruct (set_choose_L X) as [x ?]; first done.
    by apply (Hdisj x).
  Qed.
  Next Obligation. intros ??? X -> x ? []%not_elem_of_empty. Qed.
  Next Obligation.
    intros ??? X HX Hdisj. destruct (set_choose_L X) as [x ?]; first done.
    by apply (Hdisj x).
  Qed.
  Next Obligation. intros ??? Hdisj. by apply (Hdisj inhabitant). Qed.

  Global Instance topGset_subseteq_dec : RelDecision (⊆@{topGset A}).
  Proof.
    refine (λ X Y, cast_if (decide (X ∪ Y = Y)));
      abstract (by rewrite subseteq_union_L).
  Defined.

  Definition topGset_finite (X : topGset A) : bool :=
    match X with FinGSet _ => true | TopGSet => false end.
  Lemma topGset_finite_spec X : set_finite X ↔ topGset_finite X.
  Proof.
    destruct X as [X|];
    unfold set_finite, elem_of at 1, topGset_elem_of; simpl.
    - split; [done|intros _]. exists (elements X). set_solver.
    - split; [intros [Y HXY]%(pred_finite_set(C:=gset A))|done].
      destruct (exist_fresh Y) as [? ?]. naive_solver.
  Qed.
  Global Instance topGset_finite_dec (X : topGset A) :
    Decision (set_finite X).
  Proof.
    refine (cast_if (decide (topGset_finite X)));
      abstract (by rewrite topGset_finite_spec).
  Defined.
End infinite.

(** * Conversion from gset *)
Definition gset_to_topGset `{Countable A} : gset A → topGset A := FinGSet.

Section to_gset.
  Context `{Countable A}.

  Lemma elem_of_gset_to_topGset (X : gset A) x : x ∈ gset_to_topGset X ↔ x ∈ X.
  Proof. done. Qed.

  Lemma gset_to_topGset_finite (X : gset A) : set_finite (gset_to_topGset X).
  Proof. exists (elements X). set_solver. Qed.
End to_gset.

(** * Conversion to coPset *)
Definition topGset_to_coPset (X : topGset positive) : coPset :=
  match X with
  | FinGSet X => gset_to_coPset X
  | TopGSet => ⊤
  end.
Lemma elem_of_topGset_to_coPset X x : x ∈ topGset_to_coPset X ↔ x ∈ X.
Proof.
  destruct X as [X|]; simpl.
  - by rewrite elem_of_gset_to_coPset.
  - done.
Qed.

(** * If the union of two [topGset]s is [⊤], then one of them is also [⊤]. *)
Lemma topGset_union_top `{Countable A} (X Y : topGset A) :
  X ∪ Y = ⊤ → X = ⊤ ∨ Y = ⊤.
Proof. destruct X, Y; naive_solver. Qed.

Global Typeclasses Opaque topGset_elem_of topGset_empty topGset_top.
Global Typeclasses Opaque topGset_singleton topGset_union.
