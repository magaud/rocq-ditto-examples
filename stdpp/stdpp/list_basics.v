From stdpp Require Export numbers base option.
From stdpp Require Import options.

Module Export list.

Global Arguments length {_} _ : assert.
Global Arguments cons {_} _ _ : assert.
Global Arguments app {_} _ _ : assert.

Global Instance: Params (@length) 1 := {}.
Global Instance: Params (@cons) 1 := {}.
Global Instance: Params (@app) 1 := {}.

(** [head] and [tail] are defined as [parsing only] for [hd_error] and [tl] in
the Coq standard library. We redefine these notations to make sure they also
pretty print properly. *)
Notation head := hd_error.
Notation tail := tl.

Notation take := firstn.
Notation drop := skipn.

Global Arguments head {_} _ : assert.
Global Arguments tail {_} _ : assert.

Global Arguments take {_} !_ !_ / : assert.
Global Arguments drop {_} !_ !_ / : assert.

Global Instance: Params (@head) 1 := {}.
Global Instance: Params (@tail) 1 := {}.
Global Instance: Params (@take) 1 := {}.
Global Instance: Params (@drop) 1 := {}.

Notation "(::)" := cons (only parsing) : list_scope.
Notation "( x ::.)" := (cons x) (only parsing) : list_scope.
Notation "(.:: l )" := (λ x, cons x l) (only parsing) : list_scope.
Notation "(++)" := app (only parsing) : list_scope.
Notation "( l ++.)" := (app l) (only parsing) : list_scope.
Notation "(.++ k )" := (λ l, app l k) (only parsing) : list_scope.

Global Instance maybe_cons {A} : Maybe2 (@cons A) := λ l,
  match l with x :: l => Some (x,l) | _ => None end.

(** The operation [l !! i] gives the [i]th element of the list [l], or [None]
in case [i] is out of bounds. *)
Global Instance list_lookup {A} : Lookup nat A (list A) :=
  fix go i l {struct l} : option A := let _ : Lookup _ _ _ := @go in
  match l with
  | [] => None | x :: l => match i with 0 => Some x | S i => l !! i end
  end.

(** The operation [l !!! i] is a total version of the lookup operation
[l !! i]. *)
Global Instance list_lookup_total `{!Inhabited A} : LookupTotal nat A (list A) :=
  fix go i l {struct l} : A := let _ : LookupTotal _ _ _ := @go in
  match l with
  | [] => inhabitant
  | x :: l => match i with 0 => x | S i => l !!! i end
  end.

(** The operation [alter f i l] applies the function [f] to the [i]th element
of [l]. In case [i] is out of bounds, the list is returned unchanged. *)
Global Instance list_alter {A} : Alter nat A (list A) := λ f,
  fix go i l {struct l} :=
  match l with
  | [] => []
  | x :: l => match i with 0 => f x :: l | S i => x :: go i l end
  end.

(** The operation [<[i:=x]> l] overwrites the element at position [i] with the
value [x]. In case [i] is out of bounds, the list is returned unchanged. *)
Global Instance list_insert {A} : Insert nat A (list A) :=
  fix go i y l {struct l} := let _ : Insert _ _ _ := @go in
  match l with
  | [] => []
  | x :: l => match i with 0 => y :: l | S i => x :: <[i:=y]>l end
  end.
Fixpoint list_inserts {A} (i : nat) (k l : list A) : list A :=
  match k with
  | [] => l
  | y :: k => <[i:=y]>(list_inserts (S i) k l)
  end.
Global Instance: Params (@list_inserts) 1 := {}.

(** The operation [delete i l] removes the [i]th element of [l] and moves
all consecutive elements one position ahead. In case [i] is out of bounds,
the list is returned unchanged. *)
Global Instance list_delete {A} : Delete nat (list A) :=
  fix go (i : nat) (l : list A) {struct l} : list A :=
  match l with
  | [] => []
  | x :: l => match i with 0 => l | S i => x :: @delete _ _ go i l end
  end.

(** The function [option_list o] converts an element [Some x] into the
singleton list [[x]], and [None] into the empty list [[]]. *)
Definition option_list {A} : option A → list A := option_rect _ (λ x, [x]) [].
Global Instance: Params (@option_list) 1 := {}.
Global Instance maybe_list_singleton {A} : Maybe (λ x : A, [x]) := λ l,
  match l with [x] => Some x | _ => None end.

(** The function [filter P l] returns the list of elements of [l] that
satisfies [P]. The order remains unchanged. *)
Global Instance list_filter {A} : Filter A (list A) :=
  fix go P _ l := let _ : Filter _ _ := @go in
  match l with
  | [] => []
  | x :: l => if decide (P x) then x :: filter P l else filter P l
  end.

(** The function [replicate n x] generates a list with length [n] of elements
with value [x]. *)
Fixpoint replicate {A} (n : nat) (x : A) : list A :=
  match n with 0 => [] | S n => x :: replicate n x end.
Global Instance: Params (@replicate) 2 := {}.

(** The function [reverse l] returns the elements of [l] in reverse order. *)
Definition reverse {A} (l : list A) : list A := rev_append l [].
Global Instance: Params (@reverse) 1 := {}.

(** The function [last l] returns the last element of the list [l], or [None]
if the list [l] is empty. *)
Fixpoint last {A} (l : list A) : option A :=
  match l with [] => None | [x] => Some x | _ :: l => last l end.
Global Instance: Params (@last) 1 := {}.
Global Arguments last : simpl nomatch.

(** Functions to fold over a list. We redefine [foldl] with the arguments in
the same order as in Haskell. *)
Notation foldr := fold_right.
Definition foldl {A B} (f : A → B → A) : A → list B → A :=
  fix go a l := match l with [] => a | x :: l => go (f a x) l end.

(** Set operations on lists *)
Section list_set.
  Context `{dec : EqDecision A}.
  Global Instance list_elem_of_dec : RelDecision (∈@{list A}).
  Proof using Type*.
   refine (
    fix go x l :=
    match l return Decision (x ∈ l) with
    | [] => right _
    | y :: l => cast_if_or (decide (x = y)) (go x l)
    end); clear go dec; subst; try (by constructor); abstract by inv 1.
  Defined.
  Fixpoint remove_dups (l : list A) : list A :=
    match l with
    | [] => []
    | x :: l =>
      if decide_rel (∈) x l then remove_dups l else x :: remove_dups l
    end.
  Fixpoint list_difference (l k : list A) : list A :=
    match l with
    | [] => []
    | x :: l =>
      if decide_rel (∈) x k
      then list_difference l k else x :: list_difference l k
    end.
  Definition list_union (l k : list A) : list A := list_difference l k ++ k.
  Fixpoint list_intersection (l k : list A) : list A :=
    match l with
    | [] => []
    | x :: l =>
      if decide_rel (∈) x k
      then x :: list_intersection l k else list_intersection l k
    end.
  Definition list_intersection_with (f : A → A → option A) :
    list A → list A → list A := fix go l k :=
    match l with
    | [] => []
    | x :: l => foldr (λ y,
        match f x y with None => id | Some z => (z ::.) end) (go l k) k
    end.
End list_set.

(** * General theorems *)
Section general_properties.
Context {A : Type}.
Implicit Types x y z : A.
Implicit Types l k : list A.

(* TODO: Coq 8.20 has the same lemma under the same name, so remove our version
once we require Coq 8.20. In Coq 8.19 and before, this lemma is called
[app_length]. *)
Lemma length_app (l l' : list A) : length (l ++ l') = length l + length l'.
Proof. induction l; f_equal/=; auto. Qed.

Lemma app_inj_1 (l1 k1 l2 k2 : list A) :
  length l1 = length k1 → l1 ++ l2 = k1 ++ k2 → l1 = k1 ∧ l2 = k2.
Proof. revert k1. induction l1; intros [|??]; naive_solver. Qed.
Lemma app_inj_2 (l1 k1 l2 k2 : list A) :
  length l2 = length k2 → l1 ++ l2 = k1 ++ k2 → l1 = k1 ∧ l2 = k2.
Proof.
  intros ? Hl. apply app_inj_1; auto.
  apply (f_equal length) in Hl. rewrite !length_app in Hl. lia.
Qed.

Global Instance cons_eq_inj : Inj2 (=) (=) (=) (@cons A).
Proof. by injection 1. Qed.

Global Instance: ∀ k, Inj (=) (=) (k ++.).
Proof. intros ???. apply app_inv_head. Qed.
Global Instance: ∀ k, Inj (=) (=) (.++ k).
Proof. intros ???. apply app_inv_tail. Qed.
Global Instance: Assoc (=) (@app A).
Proof. intros ???. apply app_assoc. Qed.
Global Instance: LeftId (=) [] (@app A).
Proof. done. Qed.
Global Instance: RightId (=) [] (@app A).
Proof. intro. apply app_nil_r. Qed.

Lemma app_nil l1 l2 : l1 ++ l2 = [] ↔ l1 = [] ∧ l2 = [].
Proof. split; [apply app_eq_nil|]. by intros [-> ->]. Qed.
Lemma app_nil_l_inv l1 l2 : l1 ++ l2 = [] → l1 = [].
Proof. by rewrite app_nil; intros [-> _]. Qed.
Lemma app_nil_r_inv l1 l2 : l1 ++ l2 = [] → l2 = [].
Proof. by rewrite app_nil; intros [_ ->]. Qed.

Lemma app_singleton l1 l2 x :
  l1 ++ l2 = [x] ↔ l1 = [] ∧ l2 = [x] ∨ l1 = [x] ∧ l2 = [].
Proof. split; [apply app_eq_unit|]. by intros [[-> ->]|[-> ->]]. Qed.
Lemma cons_middle x l1 l2 : l1 ++ x :: l2 = l1 ++ [x] ++ l2.
Proof. done. Qed.
Lemma list_eq l1 l2 : (∀ i, l1 !! i = l2 !! i) → l1 = l2.
Proof.
  revert l2. induction l1 as [|x l1 IH]; intros [|y l2] H.
  - done.
  - discriminate (H 0).
  - discriminate (H 0).
  - f_equal; [by injection (H 0)|]. apply (IH _ $ λ i, H (S i)).
Qed.
Global Instance list_eq_dec {dec : EqDecision A} : EqDecision (list A) :=
  list_eq_dec dec.
Global Instance list_eq_nil_dec l : Decision (l = []).
Proof. by refine match l with [] => left _ | _ => right _ end. Defined.
Lemma list_singleton_reflect l :
  option_reflect (λ x, l = [x]) (length l ≠ 1) (maybe (λ x, [x]) l).
Proof. by destruct l as [|? []]; constructor. Defined.

Lemma list_eq_Forall2 l1 l2 : l1 = l2 ↔ Forall2 eq l1 l2.
Proof.
  split.
  - intros <-. induction l1; eauto using Forall2.
  - induction 1; naive_solver.
Qed.

Definition length_nil : length (@nil A) = 0 := eq_refl.
Definition length_cons x l : length (x :: l) = S (length l) := eq_refl.

Lemma nil_or_length_pos l : l = [] ∨ length l ≠ 0.
Proof. destruct l; simpl; auto with lia. Qed.
Lemma nil_length_inv l : length l = 0 → l = [].
Proof. by destruct l. Qed.
Lemma lookup_cons_ne_0 l x i : i ≠ 0 → (x :: l) !! i = l !! pred i.
Proof. by destruct i. Qed.
Lemma lookup_total_cons_ne_0 `{!Inhabited A} l x i :
  i ≠ 0 → (x :: l) !!! i = l !!! pred i.
Proof. by destruct i. Qed.
Lemma lookup_nil i : @nil A !! i = None.
Proof. by destruct i. Qed.
Lemma lookup_total_nil `{!Inhabited A} i : @nil A !!! i = inhabitant.
Proof. by destruct i. Qed.
Lemma lookup_tail l i : tail l !! i = l !! S i.
Proof. by destruct l. Qed.
Lemma lookup_total_tail `{!Inhabited A} l i : tail l !!! i = l !!! S i.
Proof. by destruct l. Qed.
Lemma lookup_lt_Some l i x : l !! i = Some x → i < length l.
Proof. revert i. induction l; intros [|?] ?; naive_solver auto with arith. Qed.
Lemma lookup_lt_is_Some_1 l i : is_Some (l !! i) → i < length l.
Proof. intros [??]; eauto using lookup_lt_Some. Qed.
Lemma lookup_lt_is_Some_2 l i : i < length l → is_Some (l !! i).
Proof. revert i. induction l; intros [|?] ?; naive_solver auto with lia. Qed.
Lemma lookup_lt_is_Some l i : is_Some (l !! i) ↔ i < length l.
Proof. split; auto using lookup_lt_is_Some_1, lookup_lt_is_Some_2. Qed.
Lemma lookup_ge_None l i : l !! i = None ↔ length l ≤ i.
Proof. rewrite eq_None_not_Some, lookup_lt_is_Some. lia. Qed.
Lemma lookup_ge_None_1 l i : l !! i = None → length l ≤ i.
Proof. by rewrite lookup_ge_None. Qed.
Lemma lookup_ge_None_2 l i : length l ≤ i → l !! i = None.
Proof. by rewrite lookup_ge_None. Qed.

Lemma list_eq_same_length l1 l2 n :
  length l2 = n → length l1 = n →
  (∀ i x y, i < n → l1 !! i = Some x → l2 !! i = Some y → x = y) → l1 = l2.
Proof.
  intros <- Hlen Hl; apply list_eq; intros i. destruct (l2 !! i) as [x|] eqn:Hx.
  - destruct (lookup_lt_is_Some_2 l1 i) as [y Hy].
    { rewrite Hlen; eauto using lookup_lt_Some. }
    rewrite Hy; f_equal; apply (Hl i); eauto using lookup_lt_Some.
  - by rewrite lookup_ge_None, Hlen, <-lookup_ge_None.
Qed.

Lemma nth_lookup l i d : nth i l d = default d (l !! i).
Proof. revert i. induction l as [|x l IH]; intros [|i]; simpl; auto. Qed.
Lemma nth_lookup_Some l i d x : l !! i = Some x → nth i l d = x.
Proof. rewrite nth_lookup. by intros ->. Qed.
Lemma nth_lookup_or_length l i d : {l !! i = Some (nth i l d)} + {length l ≤ i}.
Proof.
  rewrite nth_lookup. destruct (l !! i) eqn:?; eauto using lookup_ge_None_1.
Qed.

Lemma list_lookup_total_alt `{!Inhabited A} l i :
  l !!! i = default inhabitant (l !! i).
Proof. revert i. induction l; intros []; naive_solver. Qed.
Lemma list_lookup_total_correct `{!Inhabited A} l i x :
  l !! i = Some x → l !!! i = x.
Proof. rewrite list_lookup_total_alt. by intros ->. Qed.
Lemma list_lookup_lookup_total `{!Inhabited A} l i :
  is_Some (l !! i) → l !! i = Some (l !!! i).
Proof. rewrite list_lookup_total_alt; by intros [x ->]. Qed.
Lemma list_lookup_lookup_total_lt `{!Inhabited A} l i :
  i < length l → l !! i = Some (l !!! i).
Proof. intros ?. by apply list_lookup_lookup_total, lookup_lt_is_Some_2. Qed.
Lemma list_lookup_alt `{!Inhabited A} l i x :
  l !! i = Some x ↔ i < length l ∧ l !!! i = x.
Proof.
  naive_solver eauto using list_lookup_lookup_total_lt,
    list_lookup_total_correct, lookup_lt_Some.
Qed.

Lemma lookup_app l1 l2 i :
  (l1 ++ l2) !! i =
    match l1 !! i with Some x => Some x | None => l2 !! (i - length l1) end.
Proof. revert i. induction l1 as [|x l1 IH]; intros [|i]; naive_solver. Qed.
Lemma lookup_app_l l1 l2 i : i < length l1 → (l1 ++ l2) !! i = l1 !! i.
Proof. rewrite lookup_app. by intros [? ->]%lookup_lt_is_Some. Qed.
Lemma lookup_total_app_l `{!Inhabited A} l1 l2 i :
  i < length l1 → (l1 ++ l2) !!! i = l1 !!! i.
Proof. intros. by rewrite !list_lookup_total_alt, lookup_app_l. Qed.
Lemma lookup_app_l_Some l1 l2 i x : l1 !! i = Some x → (l1 ++ l2) !! i = Some x.
Proof. rewrite lookup_app. by intros ->. Qed.
Lemma lookup_app_r l1 l2 i :
  length l1 ≤ i → (l1 ++ l2) !! i = l2 !! (i - length l1).
Proof. rewrite lookup_app. by intros ->%lookup_ge_None. Qed.
Lemma lookup_total_app_r `{!Inhabited A} l1 l2 i :
  length l1 ≤ i → (l1 ++ l2) !!! i = l2 !!! (i - length l1).
Proof. intros. by rewrite !list_lookup_total_alt, lookup_app_r. Qed.
Lemma lookup_app_Some l1 l2 i x :
  (l1 ++ l2) !! i = Some x ↔
    l1 !! i = Some x ∨ length l1 ≤ i ∧ l2 !! (i - length l1) = Some x.
Proof.
  rewrite lookup_app. destruct (l1 !! i) eqn:Hi.
  - apply lookup_lt_Some in Hi. naive_solver lia.
  - apply lookup_ge_None in Hi. naive_solver lia.
Qed.

Lemma lookup_cons x l i :
  (x :: l) !! i =
    match i with 0 => Some x | S i => l !! i end.
Proof. reflexivity. Qed.
Lemma lookup_cons_Some x l i y :
  (x :: l) !! i = Some y ↔
    (i = 0 ∧ x = y) ∨ (1 ≤ i ∧ l !! (i - 1) = Some y).
Proof.
  rewrite lookup_cons. destruct i as [|i].
  - naive_solver lia.
  - replace (S i - 1) with i by lia. naive_solver lia.
Qed.

Lemma list_lookup_singleton x i :
  [x] !! i =
    match i with 0 => Some x | S _ => None end.
Proof. reflexivity. Qed.
Lemma list_lookup_singleton_Some x i y :
  [x] !! i = Some y ↔ i = 0 ∧ x = y.
Proof. rewrite lookup_cons_Some. naive_solver. Qed.

Lemma lookup_snoc_Some x l i y :
  (l ++ [x]) !! i = Some y ↔
    (i < length l ∧ l !! i = Some y) ∨ (i = length l ∧ x = y).
Proof.
  rewrite lookup_app_Some, list_lookup_singleton_Some.
  naive_solver auto using lookup_lt_is_Some_1 with lia.
Qed.

Lemma list_lookup_middle l1 l2 x n :
  n = length l1 → (l1 ++ x :: l2) !! n = Some x.
Proof. intros ->. by induction l1. Qed.
Lemma list_lookup_total_middle `{!Inhabited A} l1 l2 x n :
  n = length l1 → (l1 ++ x :: l2) !!! n = x.
Proof. intros. by rewrite !list_lookup_total_alt, list_lookup_middle. Qed.

Lemma list_insert_alter l i x : <[i:=x]>l = alter (λ _, x) i l.
Proof. by revert i; induction l; intros []; intros; f_equal/=. Qed.
Lemma length_alter f l i : length (alter f i l) = length l.
Proof. revert i. by induction l; intros [|?]; f_equal/=. Qed.
Lemma length_insert l i x : length (<[i:=x]>l) = length l.
Proof. revert i. by induction l; intros [|?]; f_equal/=. Qed.
Lemma list_insert_ge l i x : length l ≤ i → <[i:=x]>l = l.
Proof. revert i. induction l; intros [|i] ?; f_equal/=; auto with lia. Qed.

Lemma list_lookup_alter_eq f l i : alter f i l !! i = f <$> l !! i.
Proof.
  revert i. induction l as [|?? IHl]; [done|].
  intros [|i]; [done|]. apply (IHl i).
Qed.
Lemma list_lookup_alter_ne f l i j : i ≠ j → alter f i l !! j = l !! j.
Proof. revert i j. induction l; [done|]. intros [] []; naive_solver. Qed.
Lemma list_lookup_alter f l i j :
  alter f i l !! j = if decide (i = j) then f <$> l !! i else l !! j.
Proof.
  case_decide; subst; auto using list_lookup_alter_eq, list_lookup_alter_ne.
Qed.

Lemma list_lookup_total_alter_eq `{!Inhabited A} f l i :
  i < length l → alter f i l !!! i = f (l !!! i).
Proof.
  intros [x Hx]%lookup_lt_is_Some_2.
  by rewrite !list_lookup_total_alt, list_lookup_alter_eq, Hx.
Qed.
Lemma list_lookup_total_alter_ne `{!Inhabited A} f l i j :
  i ≠ j → alter f i l !!! j = l !!! j.
Proof. intros. by rewrite !list_lookup_total_alt, list_lookup_alter_ne. Qed.
Lemma list_lookup_total_alter `{!Inhabited A} f l i j :
  alter f i l !!! j =
    if decide (i = j ∧ i < length l) then f (l !!! i) else l !!! j.
Proof.
  rewrite !list_lookup_total_alt, list_lookup_alter.
  destruct (l !! i) as [x|] eqn:Hi.
  - repeat case_decide; naive_solver eauto using lookup_lt_Some.
  - assert (length l ≤ i) by auto using lookup_ge_None_1.
    repeat case_decide; subst; rewrite ?Hi; naive_solver eauto with lia.
Qed.

Lemma list_lookup_insert_eq l i x : i < length l → <[i:=x]> l !! i = Some x.
Proof. revert i. induction l; intros [|?] ?; f_equal/=; auto with lia. Qed.
Lemma list_lookup_insert_ne l i j x : i ≠ j → <[i:=x]> l !! j = l !! j.
Proof. revert i j. induction l; [done|]. intros [] []; naive_solver. Qed.
Lemma list_lookup_insert l i j x :
  <[i:=x]> l !! j = if decide (i = j ∧ i < length l) then Some x else l !! j.
Proof.
  destruct (decide _) as [[-> ?]|[?|?]%not_and_l].
  - by rewrite list_lookup_insert_eq.
  - by apply list_lookup_insert_ne.
  - by rewrite list_insert_ge by lia.
Qed.

Lemma list_lookup_total_insert_eq `{!Inhabited A} l i x :
  i < length l → <[i:=x]>l !!! i = x.
Proof. intros. by rewrite !list_lookup_total_alt, list_lookup_insert_eq. Qed.
Lemma list_lookup_total_insert_ne `{!Inhabited A} l i j x :
  i ≠ j → <[i:=x]>l !!! j = l !!! j.
Proof. intros. by rewrite !list_lookup_total_alt, list_lookup_insert_ne. Qed.
Lemma list_lookup_total_insert `{!Inhabited A} l i j x :
  <[i:=x]> l !!! j = if decide (i = j ∧ i < length l) then x else l !!! j.
Proof. rewrite !list_lookup_total_alt, list_lookup_insert. by case_decide. Qed.

Lemma list_lookup_insert_Some l i x j y :
  <[i:=x]>l !! j = Some y ↔
    i = j ∧ x = y ∧ j < length l ∨ i ≠ j ∧ l !! j = Some y.
Proof.
  destruct (decide (i = j)) as [->|];
    [split|rewrite list_lookup_insert_ne by done; tauto].
  - intros Hy. assert (j < length l).
    { rewrite <-(length_insert l j x); eauto using lookup_lt_Some. }
    rewrite list_lookup_insert_eq in Hy by done; naive_solver.
  - intros [(?&?&?)|[??]]; rewrite ?list_lookup_insert_eq; naive_solver.
Qed.
Lemma list_lookup_insert_is_Some l i x j :
  is_Some (<[i:=x]> l !! j) ↔ is_Some (l !! j).
Proof.
  rewrite list_lookup_insert.
  case_decide; naive_solver eauto using lookup_lt_is_Some_2.
Qed.
Lemma list_lookup_insert_None l i x j :
  <[i:=x]> l !! j = None ↔ l !! j = None.
Proof. by rewrite !eq_None_not_Some, list_lookup_insert_is_Some. Qed.

Lemma list_insert_insert_eq l i x y : <[i:=x]> (<[i:=y]> l) = <[i:=x]> l.
Proof. revert i. induction l; intros [|i]; f_equal/=; auto. Qed.
Lemma list_insert_insert_ne l i j x y :
  i ≠ j → <[i:=x]> (<[j:=y]> l) = <[j:=y]> (<[i:=x]> l).
Proof. revert i j. by induction l; intros [|?] [|?] ?; f_equal/=; auto. Qed.
Lemma list_insert_insert l i j x y :
  <[i:=x]> (<[j:=y]> l) =
    if decide (i = j) then <[i:=x]> l else <[j:=y]> (<[i:=x]> l).
Proof.
  case_decide; subst; auto using list_insert_insert_eq, list_insert_insert_ne.
Qed.

Lemma list_insert_id' l i x : (i < length l → l !! i = Some x) → <[i:=x]>l = l.
Proof. revert i. induction l; intros [|i] ?; f_equal/=; naive_solver lia. Qed.
Lemma list_insert_id l i x : l !! i = Some x → <[i:=x]>l = l.
Proof. intros ?. by apply list_insert_id'. Qed.

Lemma list_lookup_other l i x :
  length l ≠ 1 → l !! i = Some x → ∃ j y, j ≠ i ∧ l !! j = Some y.
Proof.
  intros. destruct i, l as [|x0 [|x1 l]]; simplify_eq/=.
  - by exists 1, x1.
  - by exists 0, x0.
Qed.

Lemma alter_app_l f l1 l2 i :
  i < length l1 → alter f i (l1 ++ l2) = alter f i l1 ++ l2.
Proof. revert i. induction l1; intros [|?] ?; f_equal/=; auto with lia. Qed.
Lemma alter_app_r f l1 l2 i :
  alter f (length l1 + i) (l1 ++ l2) = l1 ++ alter f i l2.
Proof. revert i. induction l1; intros [|?]; f_equal/=; auto. Qed.
Lemma alter_app_r_alt f l1 l2 i :
  length l1 ≤ i →
  alter f i (l1 ++ l2) = l1 ++ alter f (i - length l1) l2.
Proof.
  intros. assert (i = length l1 + (i - length l1)) as Hi by lia.
  rewrite Hi at 1. by apply alter_app_r.
Qed.
Lemma alter_app f l1 l2 i :
  alter f i (l1 ++ l2) =
    if decide (i < length l1) then alter f i l1 ++ l2
    else l1 ++ alter f (i - length l1) l2.
Proof. case_decide; auto using alter_app_l, alter_app_r_alt with lia. Qed.

Lemma list_alter_id f l i : (∀ x, f x = x) → alter f i l = l.
Proof. intros ?. revert i. induction l; intros [|?]; f_equal/=; auto. Qed.
Lemma list_alter_ext f g l k i :
  (∀ x, l !! i = Some x → f x = g x) → l = k → alter f i l = alter g i k.
Proof. intros H ->. revert i H. induction k; intros [|?] ?; f_equal/=; auto. Qed.

Lemma list_alter_alter_eq f g l i :
  alter f i (alter g i l) = alter (f ∘ g) i l.
Proof. revert i. induction l; intros [|?]; f_equal/=; auto. Qed.
Lemma list_alter_alter_ne f g l i j :
  i ≠ j → alter f i (alter g j l) = alter g j (alter f i l).
Proof. revert i j. induction l; intros [|?][|?] ?; f_equal/=; auto with lia. Qed.
Lemma list_alter_alter f g l i j :
  alter f i (alter g j l) =
    if decide (i = j) then alter (f ∘ g) i l else alter g j (alter f i l).
Proof.
  case_decide; subst; auto using list_alter_alter_eq, list_alter_alter_ne.
Qed.

Lemma insert_app_l l1 l2 i x :
  i < length l1 → <[i:=x]>(l1 ++ l2) = <[i:=x]>l1 ++ l2.
Proof. revert i. induction l1; intros [|?] ?; f_equal/=; auto with lia. Qed.
Lemma insert_app_r l1 l2 i x : <[length l1+i:=x]>(l1 ++ l2) = l1 ++ <[i:=x]>l2.
Proof. revert i. induction l1; intros [|?]; f_equal/=; auto. Qed.
Lemma insert_app_r_alt l1 l2 i x :
  length l1 ≤ i → <[i:=x]>(l1 ++ l2) = l1 ++ <[i - length l1:=x]>l2.
Proof.
  intros. assert (i = length l1 + (i - length l1)) as Hi by lia.
  rewrite Hi at 1. by apply insert_app_r.
Qed.
Lemma insert_app l1 l2 i x :
  <[i:=x]> (l1 ++ l2) =
    if decide (i < length l1) then <[i:=x]> l1 ++ l2
    else l1 ++ <[i - length l1:=x]> l2.
Proof. case_decide; auto using insert_app_l, insert_app_r_alt with lia. Qed.

Lemma delete_middle l1 l2 x : delete (length l1) (l1 ++ x :: l2) = l1 ++ l2.
Proof. induction l1; f_equal/=; auto. Qed.
Lemma length_delete l i :
  is_Some (l !! i) → length (delete i l) = length l - 1.
Proof.
  rewrite lookup_lt_is_Some. revert i.
  induction l as [|x l IH]; intros [|i] ?; simpl in *; [lia..|].
  rewrite IH by lia. lia.
Qed.

Lemma list_lookup_delete_lt l i j : j < i → delete i l !! j = l !! j.
Proof. revert i j; induction l; intros [] []; naive_solver eauto with lia. Qed.
Lemma list_lookup_delete_ge l i j : i ≤ j → delete i l !! j = l !! S j.
Proof. revert i j; induction l; intros [] []; naive_solver eauto with lia. Qed.
Lemma list_lookup_delete l i j :
  delete i l !! j = l !! (if decide (j < i) then j else S j).
Proof.
  case_decide; auto using list_lookup_delete_lt, list_lookup_delete_ge with lia.
Qed.

Lemma list_lookup_total_delete_lt `{!Inhabited A} l i j :
  j < i → delete i l !!! j = l !!! j.
Proof. intros. by rewrite !list_lookup_total_alt, list_lookup_delete_lt. Qed.
Lemma list_lookup_total_delete_ge `{!Inhabited A} l i j :
  i ≤ j → delete i l !!! j = l !!! S j.
Proof. intros. by rewrite !list_lookup_total_alt, list_lookup_delete_ge. Qed.
Lemma list_lookup_total_delete `{!Inhabited A} l i j :
  delete i l !!! j = l !!! (if decide (j < i) then j else S j).
Proof. by rewrite !list_lookup_total_alt, list_lookup_delete. Qed.

Lemma length_inserts l i k : length (list_inserts i k l) = length l.
Proof.
  revert i. induction k; intros ?; csimpl; rewrite ?length_insert; auto.
Qed.

Lemma list_lookup_inserts l i k j :
  i ≤ j < i + length k → j < length l →
  list_inserts i k l !! j = k !! (j - i).
Proof.
  revert i j. induction k as [|y k IH]; csimpl; intros i j ??; [lia|].
  destruct (decide (i = j)) as [->|].
  { by rewrite list_lookup_insert_eq, Nat.sub_diag
      by (rewrite length_inserts; lia). }
  rewrite list_lookup_insert_ne, IH by lia.
  by replace (j - i) with (S (j - S i)) by lia.
Qed.
Lemma list_lookup_inserts_lt l i k j :
  j < i → list_inserts i k l !! j = l !! j.
Proof.
  revert i j. induction k; intros i j ?; csimpl;
    rewrite ?list_lookup_insert_ne by lia; auto with lia.
Qed.
Lemma list_lookup_inserts_ge l i k j :
  i + length k ≤ j → list_inserts i k l !! j = l !! j.
Proof.
  revert i j. induction k; csimpl; intros i j ?;
    rewrite ?list_lookup_insert_ne by lia; auto with lia.
Qed.

Lemma list_lookup_total_inserts `{!Inhabited A} l i k j :
  i ≤ j < i + length k → j < length l →
  list_inserts i k l !!! j = k !!! (j - i).
Proof. intros. by rewrite !list_lookup_total_alt, list_lookup_inserts. Qed.
Lemma list_lookup_total_inserts_lt `{!Inhabited A}l i k j :
  j < i → list_inserts i k l !!! j = l !!! j.
Proof. intros. by rewrite !list_lookup_total_alt, list_lookup_inserts_lt. Qed.
Lemma list_lookup_total_inserts_ge `{!Inhabited A} l i k j :
  i + length k ≤ j → list_inserts i k l !!! j = l !!! j.
Proof. intros. by rewrite !list_lookup_total_alt, list_lookup_inserts_ge. Qed.

Lemma list_lookup_inserts_Some l i k j y :
  list_inserts i k l !! j = Some y ↔
    (j < i ∨ i + length k ≤ j) ∧ l !! j = Some y ∨
    i ≤ j < i + length k ∧ j < length l ∧ k !! (j - i) = Some y.
Proof.
  destruct (decide (j < i)).
  { rewrite list_lookup_inserts_lt by done; intuition lia. }
  destruct (decide (i + length k ≤ j)).
  { rewrite list_lookup_inserts_ge by done; intuition lia. }
  split.
  - intros Hy. assert (j < length l).
    { rewrite <-(length_inserts l i k); eauto using lookup_lt_Some. }
    rewrite list_lookup_inserts in Hy by lia. intuition lia.
  - intuition. by rewrite list_lookup_inserts by lia.
Qed.

Lemma list_insert_inserts_lt l i j x k :
  i < j → <[i:=x]>(list_inserts j k l) = list_inserts j k (<[i:=x]>l).
Proof.
  revert i j. induction k; intros i j ?; simpl;
    rewrite 1?list_insert_insert_ne by lia; auto with f_equal.
Qed.

Lemma list_inserts_app_l l1 l2 l3 i :
  list_inserts i (l1 ++ l2) l3 = list_inserts (length l1 + i) l2 (list_inserts i l1 l3).
Proof.
  revert i; induction l1 as [|x l1 IH]; [done|].
  intro i. simpl. rewrite IH, Nat.add_succ_r. apply list_insert_inserts_lt. lia.
Qed.
Lemma list_inserts_app_r l1 l2 l3 i :
  list_inserts (length l2 + i) l1 (l2 ++ l3) = l2 ++ list_inserts i l1 l3.
Proof.
  revert i; induction l1 as [|x l1 IH]; [done|].
  intros i. simpl. by rewrite plus_n_Sm, IH, insert_app_r.
Qed.
Lemma list_inserts_nil l1 i : list_inserts i l1 [] = [].
Proof.
  revert i; induction l1 as [|x l1 IH]; [done|].
  intro i. simpl. by rewrite IH.
Qed.
Lemma list_inserts_cons l1 l2 i x :
  list_inserts (S i) l1 (x :: l2) = x :: list_inserts i l1 l2.
Proof.
  revert i; induction l1 as [|y l1 IH]; [done|].
  intro i. simpl. by rewrite IH.
Qed.
Lemma list_inserts_0_r l1 l2 l3 :
  length l1 = length l2 → list_inserts 0 l1 (l2 ++ l3) = l1 ++ l3.
Proof.
  revert l2. induction l1 as [|x l1 IH]; intros [|y l2] ?; simplify_eq/=; [done|].
  rewrite list_inserts_cons. simpl. by rewrite IH.
Qed.
Lemma list_inserts_0_l l1 l2 l3 :
  length l1 = length l3 → list_inserts 0 (l1 ++ l2) l3 = l1.
Proof.
  revert l3. induction l1 as [|x l1 IH]; intros [|z l3] ?; simplify_eq/=.
  { by rewrite list_inserts_nil. }
  rewrite list_inserts_cons. simpl. by rewrite IH.
Qed.

(** ** Properties of the [reverse] function *)
Lemma reverse_nil : reverse [] =@{list A} [].
Proof. done. Qed.
Lemma reverse_singleton x : reverse [x] = [x].
Proof. done. Qed.
Lemma reverse_cons l x : reverse (x :: l) = reverse l ++ [x].
Proof. unfold reverse. by rewrite <-!rev_alt. Qed.
Lemma reverse_snoc l x : reverse (l ++ [x]) = x :: reverse l.
Proof. unfold reverse. by rewrite <-!rev_alt, rev_unit. Qed.
Lemma reverse_app l1 l2 : reverse (l1 ++ l2) = reverse l2 ++ reverse l1.
Proof. unfold reverse. rewrite <-!rev_alt. apply rev_app_distr. Qed.
Lemma length_reverse l : length (reverse l) = length l.
Proof.
  induction l as [|x l IH]; [done|].
  rewrite reverse_cons, length_app, IH. simpl. lia.
Qed.
Lemma reverse_involutive l : reverse (reverse l) = l.
Proof. unfold reverse. rewrite <-!rev_alt. apply rev_involutive. Qed.
Lemma reverse_lookup l i :
  i < length l →
  reverse l !! i = l !! (length l - S i).
Proof.
  revert i. induction l as [|x l IH]; simpl; intros i Hi; [done|].
  rewrite reverse_cons.
  destruct (decide (i = length l)); subst.
  + by rewrite list_lookup_middle, Nat.sub_diag by by rewrite length_reverse.
  + rewrite lookup_app_l by (rewrite length_reverse; lia).
    rewrite IH by lia.
    by assert (length l - i = S (length l - S i)) as -> by lia.
Qed.
Lemma reverse_lookup_Some l i x :
  reverse l !! i = Some x ↔ l !! (length l - S i) = Some x ∧ i < length l.
Proof.
  split.
  - destruct (decide (i < length l)); [ by rewrite reverse_lookup|].
    rewrite lookup_ge_None_2; [done|]. rewrite length_reverse. lia.
  - intros [??]. by rewrite reverse_lookup.
Qed.
Global Instance: Inj (=) (=) (@reverse A).
Proof.
  intros l1 l2 Hl.
  by rewrite <-(reverse_involutive l1), <-(reverse_involutive l2), Hl.
Qed.

(** ** Properties of the [elem_of] predicate *)
Lemma not_elem_of_nil x : x ∉ [].
Proof. by inv 1. Qed.
Lemma elem_of_nil x : x ∈ [] ↔ False.
Proof. intuition. by destruct (not_elem_of_nil x). Qed.
Lemma elem_of_nil_inv l : (∀ x, x ∉ l) → l = [].
Proof. destruct l; [done|]. by edestruct 1; constructor. Qed.
Lemma elem_of_not_nil x l : x ∈ l → l ≠ [].
Proof. intros ? ->. by apply (elem_of_nil x). Qed.
Lemma elem_of_cons l x y : x ∈ y :: l ↔ x = y ∨ x ∈ l.
Proof. by split; [inv 1; subst|intros [->|?]]; constructor. Qed.
Lemma not_elem_of_cons l x y : x ∉ y :: l ↔ x ≠ y ∧ x ∉ l.
Proof. rewrite elem_of_cons. tauto. Qed.
Lemma elem_of_app l1 l2 x : x ∈ l1 ++ l2 ↔ x ∈ l1 ∨ x ∈ l2.
Proof.
  induction l1 as [|y l1 IH]; simpl.
  - rewrite elem_of_nil. naive_solver.
  - rewrite !elem_of_cons, IH. naive_solver.
Qed.
Lemma not_elem_of_app l1 l2 x : x ∉ l1 ++ l2 ↔ x ∉ l1 ∧ x ∉ l2.
Proof. rewrite elem_of_app. tauto. Qed.
Lemma list_elem_of_singleton x y : x ∈ [y] ↔ x = y.
Proof. rewrite elem_of_cons, elem_of_nil. tauto. Qed.
Lemma elem_of_reverse_2 x l : x ∈ l → x ∈ reverse l.
Proof.
  induction 1; rewrite reverse_cons, elem_of_app,
    ?list_elem_of_singleton; intuition.
Qed.
Lemma elem_of_reverse x l : x ∈ reverse l ↔ x ∈ l.
Proof.
  split; auto using elem_of_reverse_2.
  intros. rewrite <-(reverse_involutive l). by apply elem_of_reverse_2.
Qed.

Lemma list_elem_of_lookup_1 l x : x ∈ l → ∃ i, l !! i = Some x.
Proof.
  induction 1 as [|???? IH]; [by exists 0 |].
  destruct IH as [i ?]; auto. by exists (S i).
Qed.
Lemma list_elem_of_lookup_total_1 `{!Inhabited A} l x :
  x ∈ l → ∃ i, i < length l ∧ l !!! i = x.
Proof.
  intros [i Hi]%list_elem_of_lookup_1.
  eauto using lookup_lt_Some, list_lookup_total_correct.
Qed.
Lemma list_elem_of_lookup_2 l i x : l !! i = Some x → x ∈ l.
Proof.
  revert i. induction l; intros [|i] ?; simplify_eq/=; constructor; eauto.
Qed.
Lemma list_elem_of_lookup_total_2 `{!Inhabited A} l i :
  i < length l → l !!! i ∈ l.
Proof. intros. by eapply list_elem_of_lookup_2, list_lookup_lookup_total_lt. Qed.
Lemma list_elem_of_lookup l x : x ∈ l ↔ ∃ i, l !! i = Some x.
Proof. firstorder eauto using list_elem_of_lookup_1, list_elem_of_lookup_2. Qed.
Lemma list_elem_of_lookup_total `{!Inhabited A} l x :
  x ∈ l ↔ ∃ i, i < length l ∧ l !!! i = x.
Proof.
  naive_solver eauto using list_elem_of_lookup_total_1, list_elem_of_lookup_total_2.
Qed.
Lemma list_elem_of_split_length l i x :
  l !! i = Some x → ∃ l1 l2, l = l1 ++ x :: l2 ∧ i = length l1.
Proof.
  revert i; induction l as [|y l IH]; intros [|i] Hl; simplify_eq/=.
  - exists []; eauto.
  - destruct (IH _ Hl) as (?&?&?&?); simplify_eq/=.
    eexists (y :: _); eauto.
Qed.
Lemma list_elem_of_split l x : x ∈ l → ∃ l1 l2, l = l1 ++ x :: l2.
Proof.
  intros [? (?&?&?&_)%list_elem_of_split_length]%list_elem_of_lookup_1; eauto.
Qed.
Lemma list_elem_of_split_l `{EqDecision A} l x :
  x ∈ l → ∃ l1 l2, l = l1 ++ x :: l2 ∧ x ∉ l1.
Proof.
  induction 1 as [x l|x y l ? IH].
  { exists [], l. rewrite elem_of_nil. naive_solver. }
  destruct (decide (x = y)) as [->|?].
  - exists [], l. rewrite elem_of_nil. naive_solver.
  - destruct IH as (l1 & l2 & -> & ?).
    exists (y :: l1), l2. rewrite elem_of_cons. naive_solver.
Qed.
Lemma list_elem_of_split_r `{EqDecision A} l x :
  x ∈ l → ∃ l1 l2, l = l1 ++ x :: l2 ∧ x ∉ l2.
Proof.
  induction l as [|y l IH] using rev_ind.
  { by rewrite elem_of_nil. }
  destruct (decide (x = y)) as [->|].
  - exists l, []. rewrite elem_of_nil. naive_solver.
  - rewrite elem_of_app, list_elem_of_singleton. intros [?| ->]; try done.
    destruct IH as (l1 & l2 & -> & ?); auto.
    exists l1, (l2 ++ [y]).
    rewrite elem_of_app, list_elem_of_singleton, <-(assoc_L (++)). naive_solver.
Qed.

Lemma list_elem_of_insert l i x : i < length l → x ∈ <[i:=x]>l.
Proof. intros. by eapply list_elem_of_lookup_2, list_lookup_insert_eq. Qed.
Lemma nth_elem_of l i d : i < length l → nth i l d ∈ l.
Proof.
  intros; eapply list_elem_of_lookup_2.
  destruct (nth_lookup_or_length l i d); [done | by lia].
Qed.

Lemma list_elem_of_delete_inv x i l : x ∈ delete i l → x ∈ l.
Proof.
  rewrite !list_elem_of_lookup. intros [j Hj].
  rewrite list_lookup_delete in Hj. case_decide; eauto.
Qed.
Lemma list_elem_of_foldr_delete_inv x is l : x ∈ foldr delete l is → x ∈ l.
Proof. induction is; simpl; eauto using list_elem_of_delete_inv. Qed.

Lemma not_elem_of_app_cons_inv_l x y l1 l2 k1 k2 :
  x ∉ k1 → y ∉ l1 →
  l1 ++ x :: l2 = k1 ++ y :: k2 →
  l1 = k1 ∧ x = y ∧ l2 = k2.
Proof.
  revert k1. induction l1 as [|x' l1 IH]; intros [|y' k1] Hx Hy ?; simplify_eq/=;
    try apply not_elem_of_cons in Hx as [??];
    try apply not_elem_of_cons in Hy as [??]; naive_solver.
Qed.
Lemma not_elem_of_app_cons_inv_r x y l1 l2 k1 k2 :
  x ∉ k2 → y ∉ l2 →
  l1 ++ x :: l2 = k1 ++ y :: k2 →
  l1 = k1 ∧ x = y ∧ l2 = k2.
Proof.
  intros. destruct (not_elem_of_app_cons_inv_l x y (reverse l2) (reverse l1)
    (reverse k2) (reverse k1)); [..|naive_solver].
  - by rewrite elem_of_reverse.
  - by rewrite elem_of_reverse.
  - rewrite <-!reverse_snoc, <-!reverse_app, <-!(assoc_L (++)). by f_equal.
Qed.

(** ** Set operations on lists *)
Section list_set.
  Lemma list_elem_of_intersection_with f l k x :
    x ∈ list_intersection_with f l k ↔ ∃ x1 x2,
        x1 ∈ l ∧ x2 ∈ k ∧ f x1 x2 = Some x.
  Proof.
    split.
    - induction l as [|x1 l IH]; simpl; [by rewrite elem_of_nil|].
      intros Hx. setoid_rewrite elem_of_cons.
      cut ((∃ x2, x2 ∈ k ∧ f x1 x2 = Some x)
           ∨ x ∈ list_intersection_with f l k); [naive_solver|].
      clear IH. revert Hx. generalize (list_intersection_with f l k).
      induction k; simpl; [by auto|].
      case_match; setoid_rewrite elem_of_cons; naive_solver.
    - intros (x1&x2&Hx1&Hx2&Hx). induction Hx1 as [x1 l|x1 ? l ? IH]; simpl.
      + generalize (list_intersection_with f l k).
        induction Hx2; simpl; [by rewrite Hx; left |].
        case_match; simpl; try setoid_rewrite elem_of_cons; auto.
      + generalize (IH Hx). clear Hx IH Hx2.
        generalize (list_intersection_with f l k).
        induction k; simpl; intros; [done|].
        case_match; simpl; rewrite ?elem_of_cons; auto.
  Qed.

  Context `{!EqDecision A}.
  Lemma list_elem_of_difference l k x : x ∈ list_difference l k ↔ x ∈ l ∧ x ∉ k.
  Proof.
    split; induction l; simpl; try case_decide;
      rewrite ?elem_of_nil, ?elem_of_cons; intuition congruence.
  Qed.
  Lemma list_elem_of_union l k x : x ∈ list_union l k ↔ x ∈ l ∨ x ∈ k.
  Proof.
    unfold list_union. rewrite elem_of_app, list_elem_of_difference.
    intuition. case (decide (x ∈ k)); intuition.
  Qed.
  Lemma list_elem_of_intersection l k x :
    x ∈ list_intersection l k ↔ x ∈ l ∧ x ∈ k.
  Proof.
    split; induction l; simpl; repeat case_decide;
      rewrite ?elem_of_nil, ?elem_of_cons; intuition congruence.
  Qed.
End list_set.

(** ** Properties of the [last] function *)
Lemma last_nil : last [] =@{option A} None.
Proof. done. Qed.
Lemma last_singleton x : last [x] = Some x.
Proof. done. Qed.
Lemma last_cons_cons x1 x2 l : last (x1 :: x2 :: l) = last (x2 :: l).
Proof. done. Qed.
Lemma last_app_cons l1 l2 x :
  last (l1 ++ x :: l2) = last (x :: l2).
Proof. induction l1 as [|y [|y' l1] IHl]; done. Qed.
Lemma last_snoc x l : last (l ++ [x]) = Some x.
Proof. induction l as [|? []]; simpl; auto. Qed.
Lemma last_None l : last l = None ↔ l = [].
Proof.
  split; [|by intros ->].
  induction l as [|x1 [|x2 l] IH]; naive_solver.
Qed.
Lemma last_Some l x : last l = Some x ↔ ∃ l', l = l' ++ [x].
Proof.
  split.
  - destruct l as [|x' l'] using rev_ind; [done|].
    rewrite last_snoc. naive_solver.
  - intros [l' ->]. by rewrite last_snoc.
Qed.
Lemma last_is_Some l : is_Some (last l) ↔ l ≠ [].
Proof. rewrite <-not_eq_None_Some, last_None. naive_solver. Qed.
Lemma last_app l1 l2 :
  last (l1 ++ l2) = match last l2 with Some y => Some y | None => last l1 end.
Proof.
  destruct l2 as [|x l2 _] using rev_ind.
  - by rewrite (right_id_L _ (++)).
  - by rewrite (assoc_L (++)), !last_snoc.
Qed.
Lemma last_app_Some l1 l2 x :
  last (l1 ++ l2) = Some x ↔ last l2 = Some x ∨ last l2 = None ∧ last l1 = Some x.
Proof. rewrite last_app. destruct (last l2); naive_solver. Qed.
Lemma last_app_None l1 l2 :
  last (l1 ++ l2) = None ↔ last l1 = None ∧ last l2 = None.
Proof. rewrite last_app. destruct (last l2); naive_solver. Qed.
Lemma last_cons x l :
  last (x :: l) = match last l with Some y => Some y | None => Some x end.
Proof. by apply (last_app [x]). Qed.
Lemma last_cons_Some_ne x y l :
  x ≠ y → last (x :: l) = Some y → last l = Some y.
Proof. rewrite last_cons. destruct (last l); naive_solver. Qed.
Lemma last_lookup l : last l = l !! pred (length l).
Proof. by induction l as [| ?[]]. Qed.
Lemma last_reverse l : last (reverse l) = head l.
Proof. destruct l as [|x l]; simpl; by rewrite ?reverse_cons, ?last_snoc. Qed.
Lemma last_Some_elem_of l x :
  last l = Some x → x ∈ l.
Proof.
  rewrite last_Some. intros [l' ->]. apply elem_of_app. right.
  by apply list_elem_of_singleton.
Qed.

(** ** Properties of the [head] function *)
Lemma head_nil : head [] =@{option A} None.
Proof. done. Qed.
Lemma head_cons x l : head (x :: l) = Some x.
Proof. done. Qed.

Lemma head_None l : head l = None ↔ l = [].
Proof. split; [|by intros ->]. by destruct l. Qed.
Lemma head_Some l x : head l = Some x ↔ ∃ l', l = x :: l'.
Proof. split; [destruct l as [|x' l]; naive_solver | by intros [l' ->]]. Qed.
Lemma head_is_Some l : is_Some (head l) ↔ l ≠ [].
Proof. rewrite <-not_eq_None_Some, head_None. naive_solver. Qed.

Lemma head_snoc x l :
  head (l ++ [x]) = match head l with Some y => Some y | None => Some x end.
Proof. by destruct l. Qed.
Lemma head_snoc_snoc x1 x2 l :
  head (l ++ [x1; x2]) = head (l ++ [x1]).
Proof. by destruct l. Qed.
Lemma head_lookup l : head l = l !! 0.
Proof. by destruct l. Qed.

Lemma head_app l1 l2 :
  head (l1 ++ l2) = match head l1 with Some y => Some y | None => head l2 end.
Proof. by destruct l1. Qed.
Lemma head_app_Some l1 l2 x :
  head (l1 ++ l2) = Some x ↔ head l1 = Some x ∨ head l1 = None ∧ head l2 = Some x.
Proof. rewrite head_app. destruct (head l1); naive_solver. Qed.
Lemma head_app_None l1 l2 :
  head (l1 ++ l2) = None ↔ head l1 = None ∧ head l2 = None.
Proof. rewrite head_app. destruct (head l1); naive_solver. Qed.
Lemma head_reverse l : head (reverse l) = last l.
Proof. by rewrite <-last_reverse, reverse_involutive. Qed.
Lemma head_Some_elem_of l x :
  head l = Some x → x ∈ l.
Proof. rewrite head_Some. intros [l' ->]. left. Qed.

(** ** Properties of the [take] function *)
Definition take_drop i l : take i l ++ drop i l = l := firstn_skipn i l.
Lemma take_drop_middle l i x :
  l !! i = Some x → take i l ++ x :: drop (S i) l = l.
Proof.
  revert i x. induction l; intros [|?] ??; simplify_eq/=; f_equal; auto.
Qed.
Lemma take_0 l : take 0 l = [].
Proof. reflexivity. Qed.
Lemma take_nil n : take n [] =@{list A} [].
Proof. by destruct n. Qed.
Lemma take_nil_inv l n : take n l = [] → n = 0 ∨ l = [].
Proof. destruct n, l; naive_solver. Qed.
Lemma take_S_r l n x : l !! n = Some x → take (S n) l = take n l ++ [x].
Proof. revert n. induction l; intros []; naive_solver eauto with f_equal. Qed.
Lemma take_ge l n : length l ≤ n → take n l = l.
Proof. revert n. induction l; intros [|?] ?; f_equal/=; auto with lia. Qed.

(** [take_app] is the most general lemma for [take] and [app]. Below that we
establish a number of useful corollaries. *)
Lemma take_app l k n : take n (l ++ k) = take n l ++ take (n - length l) k.
Proof. apply firstn_app. Qed.

Lemma take_app_ge l k n :
  length l ≤ n → take n (l ++ k) = l ++ take (n - length l) k.
Proof. intros. by rewrite take_app, take_ge. Qed.
Lemma take_app_le l k n : n ≤ length l → take n (l ++ k) = take n l.
Proof.
  intros. by rewrite take_app, (proj2 (Nat.sub_0_le _ _)), take_0, (right_id _ _).
Qed.
Lemma take_app_add l k m :
  take (length l + m) (l ++ k) = l ++ take m k.
Proof. rewrite take_app, take_ge by lia. repeat f_equal; lia. Qed.
Lemma take_app_add' l k n m :
  n = length l → take (n + m) (l ++ k) = l ++ take m k.
Proof. intros ->. apply take_app_add. Qed.
Lemma take_app_length l k : take (length l) (l ++ k) = l.
Proof. by rewrite take_app, take_ge, Nat.sub_diag, take_0, (right_id _ _). Qed.
Lemma take_app_length' l k n : n = length l → take n (l ++ k) = l.
Proof. intros ->. by apply take_app_length. Qed.
Lemma take_app3_length l1 l2 l3 : take (length l1) ((l1 ++ l2) ++ l3) = l1.
Proof. by rewrite <-(assoc_L (++)), take_app_length. Qed.
Lemma take_app3_length' l1 l2 l3 n :
  n = length l1 → take n ((l1 ++ l2) ++ l3) = l1.
Proof. intros ->. by apply take_app3_length. Qed.

Lemma take_take l n m : take n (take m l) = take (min n m) l.
Proof. revert n m. induction l; intros [|?] [|?]; f_equal/=; auto. Qed.
Lemma take_idemp l n : take n (take n l) = take n l.
Proof. by rewrite take_take, Nat.min_id. Qed.
Lemma length_take l n : length (take n l) = min n (length l).
Proof. revert n. induction l; intros [|?]; f_equal/=; done. Qed.
Lemma length_take_le l n : n ≤ length l → length (take n l) = n.
Proof. rewrite length_take. apply Nat.min_l. Qed.
Lemma length_take_ge l n : length l ≤ n → length (take n l) = length l.
Proof. rewrite length_take. apply Nat.min_r. Qed.
Lemma take_drop_commute l n m : take n (drop m l) = drop m (take (m + n) l).
Proof.
  revert n m. induction l; intros [|?][|?]; simpl; auto using take_nil with lia.
Qed.

Lemma lookup_take_lt l n i : i < n → take n l !! i = l !! i.
Proof. revert n i. induction l; intros [|n] [|i] ?; simpl; auto with lia. Qed.
Lemma lookup_take_ge l n i : n ≤ i → take n l !! i = None.
Proof. revert n i. induction l; intros [|?] [|?] ?; simpl; auto with lia. Qed.
Lemma lookup_take l i n :
  take n l !! i = if decide (i < n) then l !! i else None.
Proof. case_decide; auto using lookup_take_lt, lookup_take_ge with lia. Qed.

Lemma lookup_total_take_lt `{!Inhabited A} l n i :
  i < n → take n l !!! i = l !!! i.
Proof. intros. by rewrite !list_lookup_total_alt, lookup_take_lt. Qed.
Lemma lookup_total_take_ge `{!Inhabited A} l n i :
  n ≤ i → take n l !!! i = inhabitant.
Proof. intros. by rewrite list_lookup_total_alt, lookup_take_ge. Qed.
Lemma lookup_total_take `{!Inhabited A} l i n :
  take n l !!! i = if decide (i < n) then l !!! i else inhabitant.
Proof. rewrite !list_lookup_total_alt, lookup_take. by case_decide. Qed.

Lemma lookup_take_Some l n i a :
  take n l !! i = Some a ↔ l !! i = Some a ∧ i < n.
Proof. rewrite lookup_take; case_decide; naive_solver. Qed.
Lemma lookup_take_is_Some l n i :
  is_Some (take n l !! i) ↔ is_Some (l !! i) ∧ i < n.
Proof. unfold is_Some. setoid_rewrite lookup_take_Some. naive_solver. Qed.
Lemma lookup_take_None l n i :
  take n l !! i = None ↔ l !! i = None ∨ n ≤ i.
Proof. rewrite lookup_take. case_decide; naive_solver lia. Qed.

Lemma elem_of_take x n l : x ∈ take n l ↔ ∃ i, l !! i = Some x ∧ i < n.
Proof.
  rewrite list_elem_of_lookup. setoid_rewrite lookup_take_Some. naive_solver.
Qed.

Lemma take_alter_ge f l n i : n ≤ i → take n (alter f i l) = take n l.
Proof.
  intros. apply list_eq. intros j. destruct (le_lt_dec n j).
  - by rewrite !lookup_take_ge.
  - by rewrite !lookup_take, !list_lookup_alter_ne by lia.
Qed.
Lemma take_alter_lt f l n i : i < n → take n (alter f i l) = alter f i (take n l).
Proof.
  revert l i. induction n as [|? IHn]; auto; simpl.
  intros [|] [|] ?; auto; csimpl. by rewrite IHn by lia.
Qed.
Lemma take_alter f l n i :
  take n (alter f i l) =
    if decide (i < n) then alter f i (take n l) else take n l.
Proof. case_decide; auto using take_alter_ge, take_alter_lt with lia. Qed.

Lemma take_insert_ge l n i x : n ≤ i → take n (<[i:=x]>l) = take n l.
Proof.
  intros. apply list_eq. intros j. destruct (le_lt_dec n j).
  - by rewrite !lookup_take_ge.
  - by rewrite !lookup_take, !list_lookup_insert_ne by lia.
Qed.
Lemma take_insert_lt l n i x : i < n → take n (<[i:=x]>l) = <[i:=x]>(take n l).
Proof.
  revert l i. induction n as [|? IHn]; auto; simpl.
  intros [|] [|] ?; auto; simpl. by rewrite IHn by lia.
Qed.
Lemma take_insert l n i x :
  take n (<[i:=x]> l) = if decide (i < n) then <[i:=x]> (take n l) else take n l.
Proof. case_decide; auto using take_insert_ge, take_insert_lt with lia. Qed.

(** ** Properties of the [drop] function *)
Lemma drop_0 l : drop 0 l = l.
Proof. done. Qed.
Lemma drop_nil n : drop n [] =@{list A} [].
Proof. by destruct n. Qed.
Lemma drop_nil_inv l n : drop n l = [] → length l ≤ n.
Proof. revert n; induction l; intros [|?]; naive_solver eauto with lia. Qed.
Lemma drop_S l x n :
  l !! n = Some x → drop n l = x :: drop (S n) l.
Proof. revert n. induction l; intros []; naive_solver. Qed.
Lemma length_drop l n : length (drop n l) = length l - n.
Proof. revert n. by induction l; intros [|i]; f_equal/=. Qed.
Lemma drop_ge l n : length l ≤ n → drop n l = [].
Proof. revert n. induction l; intros [|?]; simpl in *; auto with lia. Qed.
Lemma drop_all l : drop (length l) l = [].
Proof. by apply drop_ge. Qed.
Lemma drop_drop l n1 n2 : drop n1 (drop n2 l) = drop (n2 + n1) l.
Proof. revert n2. induction l; intros [|?]; simpl; rewrite ?drop_nil; auto. Qed.

(** [drop_app] is the most general lemma for [drop] and [app]. Below we prove a
number of useful corollaries. *)
Lemma drop_app l k n : drop n (l ++ k) = drop n l ++ drop (n - length l) k.
Proof. apply skipn_app. Qed.

Lemma drop_app_ge l k n :
  length l ≤ n → drop n (l ++ k) = drop (n - length l) k.
Proof. intros. by rewrite drop_app, drop_ge. Qed.
Lemma drop_app_le l k n :
  n ≤ length l → drop n (l ++ k) = drop n l ++ k.
Proof. intros. by rewrite drop_app, (proj2 (Nat.sub_0_le _ _)), drop_0. Qed.
Lemma drop_app_add l k m :
  drop (length l + m) (l ++ k) = drop m k.
Proof. rewrite drop_app, drop_ge by lia. simpl. f_equal; lia. Qed.
Lemma drop_app_add' l k n m :
  n = length l → drop (n + m) (l ++ k) = drop m k.
Proof. intros ->. apply drop_app_add. Qed.
Lemma drop_app_length l k : drop (length l) (l ++ k) = k.
Proof. by rewrite drop_app_le, drop_all. Qed.
Lemma drop_app_length' l k n : n = length l → drop n (l ++ k) = k.
Proof. intros ->. by apply drop_app_length. Qed.
Lemma drop_app3_length l1 l2 l3 :
  drop (length l1) ((l1 ++ l2) ++ l3) = l2 ++ l3.
Proof. by rewrite <-(assoc_L (++)), drop_app_length. Qed.
Lemma drop_app3_length' l1 l2 l3 n :
  n = length l1 → drop n ((l1 ++ l2) ++ l3) = l2 ++ l3.
Proof. intros ->. apply drop_app3_length. Qed.

Lemma lookup_drop l n i : drop n l !! i = l !! (n + i).
Proof. revert n i. induction l; intros [|i] ?; simpl; auto. Qed.
Lemma lookup_total_drop `{!Inhabited A} l n i : drop n l !!! i = l !!! (n + i).
Proof. by rewrite !list_lookup_total_alt, lookup_drop. Qed.

Lemma drop_alter_ge f l n i :
  n ≤ i → drop n (alter f i l) = alter f (i - n) (drop n l).
Proof. revert i n. induction l; intros [] []; naive_solver lia. Qed.
Lemma drop_alter_lt f l n i : i < n → drop n (alter f i l) = drop n l.
Proof.
  intros. apply list_eq. intros j.
  by rewrite !lookup_drop, !list_lookup_alter_ne by lia.
Qed.
Lemma drop_alter f l n i :
  drop n (alter f i l) =
    if decide (n ≤ i) then alter f (i - n) (drop n l) else drop n l.
Proof. case_decide; auto using drop_alter_ge, drop_alter_lt with lia. Qed.

Lemma drop_insert_ge l n i x : n ≤ i → drop n (<[i:=x]>l) = <[i-n:=x]>(drop n l).
Proof. revert i n. induction l; intros [] []; naive_solver lia. Qed.
Lemma drop_insert_lt l n i x : i < n → drop n (<[i:=x]>l) = drop n l.
Proof.
  intros. apply list_eq. intros j.
  by rewrite !lookup_drop, !list_lookup_insert_ne by lia.
Qed.
Lemma drop_insert l n i x :
  drop n (<[i:=x]> l) =
    if decide (n ≤ i) then <[i-n:=x]> (drop n l) else drop n l.
Proof. case_decide; auto using drop_insert_ge, drop_insert_lt with lia. Qed.

Lemma delete_take_drop l i : delete i l = take i l ++ drop (S i) l.
Proof. revert i. induction l; intros [|?]; f_equal/=; auto. Qed.
Lemma take_take_drop l n m : take n l ++ take m (drop n l) = take (n + m) l.
Proof. revert n m. induction l; intros [|?] [|?]; f_equal/=; auto. Qed.
Lemma drop_take_drop l n m : n ≤ m → drop n (take m l) ++ drop m l = drop n l.
Proof.
  revert n m. induction l; intros [|?] [|?] ?;
    f_equal/=; auto using take_drop with lia.
Qed.
Lemma insert_take_drop l i x :
  i < length l →
  <[i:=x]> l = take i l ++ x :: drop (S i) l.
Proof.
  intros Hi.
  rewrite <-(take_drop_middle (<[i:=x]> l) i x).
  2:{ by rewrite list_lookup_insert_eq. }
  rewrite take_insert_ge by done.
  rewrite drop_insert_lt by lia.
  done.
Qed.

(** ** Interaction between the [take]/[drop]/[reverse] functions *)
Lemma take_reverse l n : take n (reverse l) = reverse (drop (length l - n) l).
Proof. unfold reverse; rewrite <-!rev_alt. apply firstn_rev. Qed.
Lemma drop_reverse l n : drop n (reverse l) = reverse (take (length l - n) l).
Proof. unfold reverse; rewrite <-!rev_alt. apply skipn_rev. Qed.
Lemma reverse_take l n : reverse (take n l) = drop (length l - n) (reverse l).
Proof.
  rewrite drop_reverse. destruct (decide (n ≤ length l)).
  - repeat f_equal; lia.
  - by rewrite !take_ge by lia.
Qed.
Lemma reverse_drop l n : reverse (drop n l) = take (length l - n) (reverse l).
Proof.
  rewrite take_reverse. destruct (decide (n ≤ length l)).
  - repeat f_equal; lia.
  - by rewrite !drop_ge by lia.
Qed.

(** ** Other lemmas that use [take]/[drop] in their proof. *)
Lemma app_eq_inv l1 l2 k1 k2 :
  l1 ++ l2 = k1 ++ k2 →
  (∃ k, l1 = k1 ++ k ∧ k2 = k ++ l2) ∨ (∃ k, k1 = l1 ++ k ∧ l2 = k ++ k2).
Proof.
  intros Hlk. destruct (decide (length l1 < length k1)).
  - right. rewrite <-(take_drop (length l1) k1), <-(assoc_L _) in Hlk.
    apply app_inj_1 in Hlk as [Hl1 Hl2]; [|rewrite length_take; lia].
    exists (drop (length l1) k1). by rewrite Hl1 at 1; rewrite take_drop.
  - left. rewrite <-(take_drop (length k1) l1), <-(assoc_L _) in Hlk.
    apply app_inj_1 in Hlk as [Hk1 Hk2]; [|rewrite length_take; lia].
    exists (drop (length k1) l1). by rewrite <-Hk1 at 1; rewrite take_drop.
Qed.

(** ** Properties of the [replicate] function *)
Lemma length_replicate n x : length (replicate n x) = n.
Proof. induction n; simpl; auto. Qed.
Lemma lookup_replicate n x y i :
  replicate n x !! i = Some y ↔ y = x ∧ i < n.
Proof.
  split.
  - revert i. induction n; intros [|?]; naive_solver auto with lia.
  - intros [-> Hi]. revert i Hi.
    induction n; intros [|?]; naive_solver auto with lia.
Qed.
Lemma elem_of_replicate n x y : y ∈ replicate n x ↔ y = x ∧ n ≠ 0.
Proof.
  rewrite list_elem_of_lookup, Nat.neq_0_lt_0.
  setoid_rewrite lookup_replicate; naive_solver eauto with lia.
Qed.
Lemma lookup_replicate_1 n x y i :
  replicate n x !! i = Some y → y = x ∧ i < n.
Proof. by rewrite lookup_replicate. Qed.
Lemma lookup_replicate_2 n x i : i < n → replicate n x !! i = Some x.
Proof. by rewrite lookup_replicate. Qed.
Lemma lookup_total_replicate_2 `{!Inhabited A} n x i :
  i < n → replicate n x !!! i = x.
Proof. intros. by rewrite list_lookup_total_alt, lookup_replicate_2. Qed.
Lemma lookup_replicate_None n x i : n ≤ i ↔ replicate n x !! i = None.
Proof.
  rewrite eq_None_not_Some, Nat.le_ngt. split.
  - intros Hin [x' Hx']; destruct Hin. rewrite lookup_replicate in Hx'; tauto.
  - intros Hx ?. destruct Hx. exists x; auto using lookup_replicate_2.
Qed.
Lemma insert_replicate x n i : <[i:=x]>(replicate n x) = replicate n x.
Proof. revert i. induction n; intros [|?]; f_equal/=; auto. Qed.
Lemma insert_replicate_lt x y n i :
  i < n →
  <[i:=y]>(replicate n x) = replicate i x ++ y :: replicate (n - S i) x.
Proof.
  revert i. induction n as [|n IH]; intros [|i] Hi; simpl; [lia..| |].
  - by rewrite Nat.sub_0_r.
  - by rewrite IH by lia.
Qed.
Lemma elem_of_replicate_inv x n y : x ∈ replicate n y → x = y.
Proof. induction n; simpl; rewrite ?elem_of_nil, ?elem_of_cons; intuition. Qed.
Lemma replicate_S n x : replicate (S n) x = x :: replicate n x.
Proof. done. Qed.
Lemma replicate_S_end n x : replicate (S n) x = replicate n x ++ [x].
Proof. induction n; f_equal/=; auto. Qed.
Lemma replicate_add n m x :
  replicate (n + m) x = replicate n x ++ replicate m x.
Proof. induction n; f_equal/=; auto. Qed.
Lemma replicate_cons_app n x :
  x :: replicate n x = replicate n x ++ [x].
Proof. induction n; f_equal/=; eauto.  Qed.
Lemma take_replicate n m x : take n (replicate m x) = replicate (min n m) x.
Proof. revert m. by induction n; intros [|?]; f_equal/=. Qed.
Lemma take_replicate_add n m x : take n (replicate (n + m) x) = replicate n x.
Proof. by rewrite take_replicate, min_l by lia. Qed.
Lemma drop_replicate n m x : drop n (replicate m x) = replicate (m - n) x.
Proof. revert m. by induction n; intros [|?]; f_equal/=. Qed.
Lemma drop_replicate_add n m x : drop n (replicate (n + m) x) = replicate m x.
Proof. rewrite drop_replicate. f_equal. lia. Qed.
Lemma replicate_as_elem_of x n l :
  replicate n x = l ↔ length l = n ∧ ∀ y, y ∈ l → y = x.
Proof.
  split; [intros <-; eauto using elem_of_replicate_inv, length_replicate|].
  intros [<- Hl]. symmetry. induction l as [|y l IH]; f_equal/=.
  - apply Hl. by left.
  - apply IH. intros ??. apply Hl. by right.
Qed.
Lemma reverse_replicate n x : reverse (replicate n x) = replicate n x.
Proof.
  symmetry. apply replicate_as_elem_of.
  rewrite length_reverse, length_replicate. split; auto.
  intros y. rewrite elem_of_reverse. by apply elem_of_replicate_inv.
Qed.
Lemma replicate_false βs n : length βs = n → replicate n false =.>* βs.
Proof. intros <-. by induction βs; simpl; constructor. Qed.
Lemma tail_replicate x n : tail (replicate n x) = replicate (pred n) x.
Proof. by destruct n. Qed.
Lemma head_replicate_Some x n : head (replicate n x) = Some x ↔ 0 < n.
Proof. destruct n; naive_solver lia. Qed.

(** ** Properties of the [filter] function *)
Section filter.
  Context (P : A → Prop) `{∀ x, Decision (P x)}.
  Local Arguments filter {_ _ _} _ {_} !_ /.

  Lemma filter_nil : filter P [] = [].
  Proof. done. Qed.

  Lemma filter_cons x l :
    filter P (x :: l) = if decide (P x) then x :: filter P l else filter P l.
  Proof. done. Qed.
  Lemma filter_cons_True x l : P x → filter P (x :: l) = x :: filter P l.
  Proof. intros. by rewrite filter_cons, decide_True. Qed.
  Lemma filter_cons_False x l : ¬P x → filter P (x :: l) = filter P l.
  Proof. intros. by rewrite filter_cons, decide_False. Qed.

  Lemma filter_singleton x l : filter P [x] = if decide (P x) then [x] else [].
  Proof. done. Qed.
  Lemma filter_singleton_True x l : P x → filter P [x] = [x].
  Proof. intros. by rewrite filter_singleton, decide_True. Qed.
  Lemma filter_singleton_False x l : ¬P x → filter P [x] = [].
  Proof. intros. by rewrite filter_singleton, decide_False. Qed.

  Lemma filter_app l1 l2 : filter P (l1 ++ l2) = filter P l1 ++ filter P l2.
  Proof.
    induction l1 as [|x l1 IH]; simpl; [done| ].
    case_decide; [|done].
    by rewrite IH.
  Qed.

  Lemma list_elem_of_filter l x : x ∈ filter P l ↔ P x ∧ x ∈ l.
  Proof.
    induction l; simpl; repeat case_decide;
      rewrite ?elem_of_nil, ?elem_of_cons; naive_solver.
  Qed.

  Lemma length_filter l : length (filter P l) ≤ length l.
  Proof. induction l; simpl; repeat case_decide; simpl; lia. Qed.
  Lemma length_filter_lt l x : x ∈ l → ¬P x → length (filter P l) < length l.
  Proof.
    intros (l1 & l2 & ->)%list_elem_of_split ?.
    rewrite filter_app, !length_app, filter_cons, decide_False by done.
    pose proof (length_filter l1); pose proof (length_filter l2). simpl. lia.
  Qed.

  Lemma filter_nil_not_elem_of l x : filter P l = [] → P x → x ∉ l.
  Proof. induction 3; simplify_eq/=; case_decide; naive_solver. Qed.
  Lemma filter_reverse l : filter P (reverse l) = reverse (filter P l).
  Proof.
    induction l as [|x l IHl]; [done|].
    rewrite reverse_cons, filter_app, IHl, !filter_cons.
    case_decide; [by rewrite reverse_cons|by rewrite filter_nil, app_nil_r].
  Qed.
End filter.

Lemma list_filter_iff (P1 P2 : A → Prop)
    `{!∀ x, Decision (P1 x), !∀ x, Decision (P2 x)} (l : list A) :
  (∀ x, P1 x ↔ P2 x) →
  filter P1 l = filter P2 l.
Proof.
  intros HPiff. induction l as [|a l IH]; [done|].
  destruct (decide (P1 a)).
  - rewrite !filter_cons_True by naive_solver. by rewrite IH.
  - rewrite !filter_cons_False by naive_solver. by rewrite IH.
Qed.

Lemma list_filter_filter (P1 P2 : A → Prop)
    `{!∀ x, Decision (P1 x), !∀ x, Decision (P2 x)} (l : list A) :
  filter P1 (filter P2 l) = filter (λ a, P1 a ∧ P2 a) l.
Proof.
  induction l as [|x l IH]; [done|].
  rewrite !filter_cons. case (decide (P2 x)) as [HP2|HP2].
  - rewrite filter_cons, IH. apply decide_ext. naive_solver.
  - rewrite IH. symmetry. apply decide_False. by intros [_ ?].
Qed.

Lemma list_filter_filter_l (P1 P2 : A → Prop)
    `{!∀ x, Decision (P1 x), !∀ x, Decision (P2 x)} (l : list A) :
  (∀ x, P1 x → P2 x) →
  filter P1 (filter P2 l) = filter P1 l.
Proof.
  intros HPimp. rewrite list_filter_filter.
  apply list_filter_iff. naive_solver.
Qed.

Lemma list_filter_filter_r (P1 P2 : A → Prop)
    `{!∀ x, Decision (P1 x), !∀ x, Decision (P2 x)} (l : list A) :
  (∀ x, P2 x → P1 x) →
  filter P1 (filter P2 l) = filter P2 l.
Proof.
  intros HPimp. rewrite list_filter_filter.
  apply list_filter_iff. naive_solver.
Qed.
End general_properties.

(** * Basic tactics on lists *)
(** These are used already in [list_relations] so we cannot have them in
[list_tactics]. *)

(** The tactic [discriminate_list] discharges a goal if there is a hypothesis
[l1 = l2] where [l1] and [l2] have different lengths. The tactic is guaranteed
to work if [l1] and [l2] contain solely [ [] ], [(::)] and [(++)]. *)
Tactic Notation "discriminate_list" hyp(H) :=
  apply (f_equal length) in H;
  repeat (csimpl in H || rewrite length_app in H); exfalso; lia.
Tactic Notation "discriminate_list" :=
  match goal with H : _ =@{list _} _ |- _ => discriminate_list H end.

(** The tactic [simplify_list_eq] simplifies hypotheses involving
equalities on lists using injectivity of [(::)] and [(++)]. Also, it simplifies
lookups in singleton lists. *)
Ltac simplify_list_eq :=
  repeat match goal with
  | _ => progress simplify_eq/=
  | H : _ ++ _ = _ ++ _ |- _ => first
    [ apply app_inv_head in H | apply app_inv_tail in H
    | apply app_inj_1 in H; [destruct H|done]
    | apply app_inj_2 in H; [destruct H|done] ]
  | H : [?x] !! ?i = Some ?y |- _ =>
    destruct i; [change (Some x = Some y) in H | discriminate]
  end.

End list.
