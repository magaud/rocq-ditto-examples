From stdpp Require Import gmap sorting.

(** This file provides a quick start guide to finite sets in std++. It is
recommended to read this guide by stepping through it in an IDE. *)

(** * What set data type to use? *)

(** [gset K] is the type of sets you probably want to use. It enjoys good
properties w.r.t. computation (most operations are logarithmic or linear w.r.t.
the number of elements in the set) and equality (which is extensional and
decidable). It works for any type [K] that is countable (see type class
[Countable]). There are [Countable] instances for all the usual types, [nat],
[list nat], [nat * nat], [gset nat], etc. *)

Check gset.


(** * Set operations *)

(* All the set operations are overloaded via type classes, but there are
instances for [gset]. The most important operations are:

- [elem_of], notation [∈]
- [subseteq], notation [⊆]
- [subset], notation [⊂]
- [empty], notation [∅]
- [singleton], notation [ {[ x ]} ]
- [union], notation [∪]
- [intersection], notation [∩]
- [difference], notation [∖]
*)

(** Let us try to type check some stuff. Keep in mind that the operations are
overloaded via type classes, so you need [gset] type annotations. *)

Fail Definition my_set := {[ 10 ]}.

Definition my_set : gset nat := {[ 10 ]}.

Definition my_set_of_lists : gset (list nat) := {[ [10] ]}.

Definition my_set_of_sets : gset (gset nat) := {[ {[ 10 ]} ]}.

Definition my_set_fun := λ X : gset nat, X ∪ {[ 10 ]}.
(** [(.∪ Y)] is notation for [λ X, X ∪ Y]. *)
Definition my_set_fun_alt : gset nat → gset nat := (.∪ {[ 10 ]}).

(** [filter], [set_map], [set_seq], etc are also overloaded,
so you again need sufficient type annotations.  *)

Fail Definition evens X :=
  filter (Nat.divide 2) X.

Definition evens (X : gset nat) : gset nat :=
  filter (Nat.divide 2) X.

(** [(.∈ Y)] is notation for [(λ y, y ∈ Y)] *)
Definition intersection_alt (X Y : gset nat) : gset nat :=
  filter (.∈ Y) X.

Definition add_one (X : gset nat) : gset nat :=
  set_map S X.

Definition until_n (n : nat) : gset nat :=
  set_seq 0 n.


(** * Automatic proofs using [set_solver] *)

(** Let us write some lemmas. The most useful tactic is [set_solver]. *)

Lemma some_stuff (X Y Z : gset nat) :
  X ∪ Y ∩ X ∪ Z ∩ X = (Y ∪ X ∪ Z ∖ ∅ ∪ X) ∩ X.
Proof. set_solver. Qed.

Lemma some_stuff_poly `{Countable A} (X Y Z : gset A) :
  X ∪ Y ∩ X ∪ Z ∩ X = (Y ∪ X ∪ Z ∖ ∅ ∪ X) ∩ X.
Proof. set_solver. Qed.


(** * Searching for lemmas *)

(** Unfortunately, [set_solver] cannot solve everything. In particular,
it will not be able to prove lemmas that involve other domains than sets
(numbers, lists, etc), or lemmas for which classical reasoning is needed (which
is often the case for [difference]/[∖]).

If you want to search for lemmas, search for the operations using their
type class projections (e.g., [elem_of], [subseteq], [union]). Some important
points:

- Most lemmas look a bit daunting because of the additional arguments (e.g.,
  [∀ {A C : Type} {H : ElemOf A C} {H0 : Empty C} {H1 : Singleton A C} ...]
  due to type classes, but these arguments can mostly be ignored.
- There are often two versions, one for Leibniz equality [=] and another for
  setoid equality [≡]. The first ones are suffixed [_L]. For [gset] you always
  want to use [=] (and thus the [_L] lemmas) because we have [X ≡ Y ↔ X = Y].
  This is not the case for other implementations of sets, like
  [propset A := A → Prop] or [listset A := list A], hence [≡] is useful in the
  general case.
- You will not find much about them when searching for [gset], e.g.,
  [Search gset difference union] returns nothing useful, so simply use
  [Search difference union]. You can add [SemiSet], [Set_] or [FinSet] if there
  are too many irrelevant results for maps or lists.
*)

Lemma set_solver_fail_other_domain (X Y : gset nat) x y :
  x + y ∈ X → y + x ∈ X ∪ Y.
Proof.
  (** If the statement involves other domains (e.g., [nat]), you might have to
  massage the goal a bit to get [set_solver] to work. *)
  rewrite Nat.add_comm.
  set_solver.
Qed.

Lemma set_solver_fail_classic `{Countable A} (X Y Z : gset A) :
  X ∪ Y = Y → Y ∪ Y = X ∪ Y ∖ X.
Proof.
  intros.
  Fail set_solver.
  Search gset difference union. (* nothing useful *)
  Search Set_ difference union. (* plenty of results *)

  (** The relevant lemma is [union_difference_L], note the [_L]. *)
  (** We massage the goal a bit using the lemma and use [set_solver] to prove
  the side-condition and remaining goal. *)
  rewrite <-union_difference_L by set_solver.
  set_solver.
Abort.


(** * Computation via [vm_compute] *)

(** When computing with sets, always make sure to cast the result that you want
to display is a simple type like [nat], [list nat], [bool], etc. The result
of a [gset] computation is a big sigma type with lots of noise, so it won't be
pretty (or useful) to look at. *)

(** [elements] converts a set to a (unsorted) list. *)
Eval vm_compute in elements (add_one (evens {[ 10; 11; 14 ]})).
Eval vm_compute in elements (evens (until_n 40)).
Eval vm_compute in fresh ({[ 10; 12 ]} : gset nat).
Eval vm_compute in size ({[ 10; 12 ]} : gset nat).
(** You can use [bool_decide] to turn decidable [Prop]s into [bool]s. *)
Eval vm_compute in bool_decide (10 ∈ evens {[ 10; 11 ]}).
Eval vm_compute in bool_decide ({[ 10; 14; 17 ]} ⊂ until_n 40).
Eval vm_compute in bool_decide (set_Forall (λ x, (2 | x)) (evens (until_n 40))).


(** ** Want to know more? *)

(**
- Look up the definitions of the type classes for [union], [intersection], etc.,
  the interfaces [SemiSet], [Set_], [FiniteSet] etc. in [theories/base.v].
- Look up the generic theory of sets in [theories/sets.v].
- Look up the generic theory of finite sets in [theories/fin_sets.v].
- Probably don't look into the implementation of [gset] in [theories/gmap.v],
  unless you are very interested in encodings as bit strings and radix-2 search
  trees. You should treat [gset] as a black box. *)
