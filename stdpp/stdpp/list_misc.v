From Coq Require Export Permutation.
From stdpp Require Export numbers base option list_basics list_relations list_monad.
From stdpp Require Import options.

Module Export list.

(** The function [list_find P l] returns the first index [i] whose element
satisfies the predicate [P]. *)
Definition list_find {A} P `{∀ x, Decision (P x)} : list A → option (nat * A) :=
  fix go l :=
  match l with
  | [] => None
  | x :: l => if decide (P x) then Some (0,x) else prod_map S id <$> go l
  end.
Global Instance: Params (@list_find) 3 := {}.

(** The function [resize n y l] takes the first [n] elements of [l] in case
[length l ≤ n], and otherwise appends elements with value [x] to [l] to obtain
a list of length [n]. *)
Fixpoint resize {A} (n : nat) (y : A) (l : list A) : list A :=
  match l with
  | [] => replicate n y
  | x :: l => match n with 0 => [] | S n => x :: resize n y l end
  end.
Global Arguments resize {_} !_ _ !_ : assert.
Global Instance: Params (@resize) 2 := {}.

(** The function [rotate n l] rotates the list [l] by [n], e.g., [rotate 1
[x0; x1; ...; xm]] becomes [x1; ...; xm; x0]. Rotating by a multiple of
[length l] is the identity function. **)
Definition rotate {A} (n : nat) (l : list A) : list A :=
  drop (n `mod` length l) l ++ take (n `mod` length l) l.
Global Instance: Params (@rotate) 2 := {}.

(** The function [rotate_take s e l] returns the range between the
indices [s] (inclusive) and [e] (exclusive) of [l]. If [e ≤ s], all
elements after [s] and before [e] are returned. *)
Definition rotate_take {A} (s e : nat) (l : list A) : list A :=
  take (rotate_nat_sub s e (length l)) (rotate s l).
Global Instance: Params (@rotate_take) 3 := {}.

(** The function [reshape k l] transforms [l] into a list of lists whose sizes
are specified by [k]. In case [l] is too short, the resulting list will be
padded with empty lists. In case [l] is too long, it will be truncated. *)
Fixpoint reshape {A} (szs : list nat) (l : list A) : list (list A) :=
  match szs with
  | [] => [] | sz :: szs => take sz l :: reshape szs (drop sz l)
  end.
Global Instance: Params (@reshape) 2 := {}.

Definition sublist_lookup {A} (i n : nat) (l : list A) : option (list A) :=
  guard (i + n ≤ length l);; Some (take n (drop i l)).
Definition sublist_alter {A} (f : list A → list A)
    (i n : nat) (l : list A) : list A :=
  take i l ++ f (take n (drop i l)) ++ drop (i + n) l.

(** The function [mask f βs l] applies the function [f] to elements in [l] at
positions that are [true] in [βs]. *)
Fixpoint mask {A} (f : A → A) (βs : list bool) (l : list A) : list A :=
  match βs, l with
  | β :: βs, x :: l => (if β then f x else x) :: mask f βs l
  | _, _ => l
  end.

(** These next functions allow to efficiently encode lists of positives (bit
strings) into a single positive and go in the other direction as well. This is
for example used for the countable instance of lists and in namespaces.
 The main functions are [positives_flatten] and [positives_unflatten]. *)
Fixpoint positives_flatten_go (xs : list positive) (acc : positive) : positive :=
  match xs with
  | [] => acc
  | x :: xs => positives_flatten_go xs (acc~1~0 ++ Pos.reverse (Pos.dup x))
  end.

(** Flatten a list of positives into a single positive by duplicating the bits
of each element, so that:

- [0 -> 00]
- [1 -> 11]

and then separating each element with [10]. *)
Definition positives_flatten (xs : list positive) : positive :=
  positives_flatten_go xs 1.

Fixpoint positives_unflatten_go
        (p : positive)
        (acc_xs : list positive)
        (acc_elm : positive)
  : option (list positive) :=
  match p with
  | 1 => Some acc_xs
  | p'~0~0 => positives_unflatten_go p' acc_xs (acc_elm~0)
  | p'~1~1 => positives_unflatten_go p' acc_xs (acc_elm~1)
  | p'~1~0 => positives_unflatten_go p' (acc_elm :: acc_xs) 1
  | _ => None
  end%positive.

(** Unflatten a positive into a list of positives, assuming the encoding
used by [positives_flatten]. *)
Definition positives_unflatten (p : positive) : option (list positive) :=
  positives_unflatten_go p [] 1.

Section general_properties.
Context {A : Type}.
Implicit Types x y z : A.
Implicit Types l k : list A.

(** * Properties of the [find] function *)
Section find.
  Context (P : A → Prop) `{!∀ x, Decision (P x)}.

  Lemma list_find_Some l i x  :
    list_find P l = Some (i,x) ↔
      l !! i = Some x ∧ P x ∧ ∀ j y, l !! j = Some y → j < i → ¬P y.
  Proof.
    revert i. induction l as [|y l IH]; intros i; csimpl; [naive_solver|].
    case_decide.
    - split; [naive_solver lia|]. intros (Hi&HP&Hlt).
      destruct i as [|i]; simplify_eq/=; [done|].
      destruct (Hlt 0 y); naive_solver lia.
    - split.
      + intros ([i' x']&Hl&?)%fmap_Some; simplify_eq/=.
        apply IH in Hl as (?&?&Hlt). split_and!; [done..|].
        intros [|j] ?; naive_solver lia.
      + intros (?&?&Hlt). destruct i as [|i]; simplify_eq/=; [done|].
        rewrite (proj2 (IH i)); [done|]. split_and!; [done..|].
        intros j z ???. destruct (Hlt (S j) z); naive_solver lia.
  Qed.

  Lemma list_find_elem_of l x : x ∈ l → P x → is_Some (list_find P l).
  Proof.
    induction 1 as [|x y l ? IH]; intros; simplify_option_eq; eauto.
    by destruct IH as [[i x'] ->]; [|exists (S i, x')].
  Qed.

  Lemma list_find_None l :
    list_find P l = None ↔ Forall (λ x, ¬P x) l.
  Proof.
    rewrite eq_None_not_Some, Forall_forall. split.
    - intros Hl x Hx HP. destruct Hl. eauto using list_find_elem_of.
    - intros HP [[i x] (?%list_elem_of_lookup_2&?&?)%list_find_Some]; naive_solver.
  Qed.

  Lemma list_find_app_None l1 l2 :
    list_find P (l1 ++ l2) = None ↔ list_find P l1 = None ∧ list_find P l2 = None.
  Proof. by rewrite !list_find_None, Forall_app. Qed.

  Lemma list_find_app_Some l1 l2 i x :
    list_find P (l1 ++ l2) = Some (i,x) ↔
      list_find P l1 = Some (i,x) ∨
      length l1 ≤ i ∧ list_find P l1 = None ∧ list_find P l2 = Some (i - length l1,x).
  Proof.
    split.
    - intros ([?|[??]]%lookup_app_Some&?&Hleast)%list_find_Some.
      + left. apply list_find_Some; eauto using lookup_app_l_Some.
      + right. split; [lia|]. split.
        { apply list_find_None, Forall_lookup. intros j z ??.
          assert (j < length l1) by eauto using lookup_lt_Some.
          naive_solver eauto using lookup_app_l_Some with lia. }
        apply list_find_Some. split_and!; [done..|].
        intros j z ??. eapply (Hleast (length l1 + j)); [|lia].
        by rewrite lookup_app_r, Nat.add_sub' by lia.
    - intros [(?&?&Hleast)%list_find_Some|(?&Hl1&(?&?&Hleast)%list_find_Some)].
      + apply list_find_Some. split_and!; [by auto using lookup_app_l_Some..|].
        assert (i < length l1) by eauto using lookup_lt_Some.
        intros j y ?%lookup_app_Some; naive_solver eauto with lia.
      + rewrite list_find_Some, lookup_app_Some. split_and!; [by auto..|].
        intros j y [?|?]%lookup_app_Some ?; [|naive_solver auto with lia].
        by eapply (Forall_lookup_1 (not ∘ P) l1); [by apply list_find_None|..].
  Qed.
  Lemma list_find_app_l l1 l2 i x:
    list_find P l1 = Some (i, x) → list_find P (l1 ++ l2) = Some (i, x).
  Proof. rewrite list_find_app_Some. auto. Qed.
  Lemma list_find_app_r l1 l2:
    list_find P l1 = None →
    list_find P (l1 ++ l2) = prod_map (λ n, n + length l1) id <$> list_find P l2.
  Proof.
    intros. apply option_eq; intros [j y]. rewrite list_find_app_Some. split.
    - intros [?|(?&?&->)]; naive_solver auto with f_equal lia.
    - intros ([??]&->&?)%fmap_Some; naive_solver auto with f_equal lia.
  Qed.

  Lemma list_find_insert_Some l i j x y :
    list_find P (<[i:=x]> l) = Some (j,y) ↔
      (j < i ∧ list_find P l = Some (j,y)) ∨
      (i = j ∧ x = y ∧ j < length l ∧ P x ∧ ∀ i' z, l !! i' = Some z → i' < i → ¬P z) ∨
      (i < j ∧ ¬P x ∧ list_find P l = Some (j,y) ∧ ∀ z, l !! i = Some z → ¬P z) ∨
      (∃ z, i < j ∧ ¬P x ∧ P y ∧ P z ∧ l !! i = Some z ∧ l !! j = Some y ∧
            ∀ i' z, l !! i' = Some z → i' ≠ i → i' < j → ¬P z).
   Proof.
     split.
     - intros ([(->&->&?)|[??]]%list_lookup_insert_Some&?&Hleast)%list_find_Some.
       { right; left. split_and!; [done..|]. intros k z ??.
         apply (Hleast k); [|lia]. by rewrite list_lookup_insert_ne by lia. }
       assert (j < i ∨ i < j) as [?|?] by lia.
       { left. rewrite list_find_Some. split_and!; [by auto..|]. intros k z ??.
         apply (Hleast k); [|lia]. by rewrite list_lookup_insert_ne by lia. }
       right; right. assert (j < length l) by eauto using lookup_lt_Some.
       destruct (lookup_lt_is_Some_2 l i) as [z ?]; [lia|].
       destruct (decide (P z)).
       { right. exists z. split_and!; [done| |done..|].
         + apply (Hleast i); [|done]. by rewrite list_lookup_insert_eq by lia.
         + intros k z' ???.
           apply (Hleast k); [|lia]. by rewrite list_lookup_insert_ne by lia. }
       left. split_and!; [done|..|naive_solver].
       + apply (Hleast i); [|done]. by rewrite list_lookup_insert_eq by lia.
       + apply list_find_Some. split_and!; [by auto..|]. intros k z' ??.
         destruct (decide (k = i)) as [->|]; [naive_solver|].
         apply (Hleast k); [|lia]. by rewrite list_lookup_insert_ne by lia.
     - intros [[? Hl]|[(->&->&?&?&Hleast)|[(?&?&Hl&Hnot)|(z&?&?&?&?&?&?&?Hleast)]]];
         apply list_find_Some.
       + apply list_find_Some in Hl as (?&?&Hleast).
         rewrite list_lookup_insert_ne by lia. split_and!; [done..|].
         intros k z [(->&->&?)|[??]]%list_lookup_insert_Some; eauto with lia.
       + rewrite list_lookup_insert_eq by done. split_and!; [by auto..|].
         intros k z [(->&->&?)|[??]]%list_lookup_insert_Some; eauto with lia.
       + apply list_find_Some in Hl as (?&?&Hleast).
         rewrite list_lookup_insert_ne by lia. split_and!; [done..|].
         intros k z [(->&->&?)|[??]]%list_lookup_insert_Some; eauto with lia.
       + rewrite list_lookup_insert_ne by lia. split_and!; [done..|].
         intros k z' [(->&->&?)|[??]]%list_lookup_insert_Some; eauto with lia.
  Qed.

  Lemma list_find_ext (Q : A → Prop) `{∀ x, Decision (Q x)} l :
    (∀ x, P x ↔ Q x) →
    list_find P l = list_find Q l.
  Proof.
    intros HPQ. induction l as [|x l IH]; simpl; [done|].
    by rewrite (decide_ext (P x) (Q x)), IH by done.
  Qed.
End find.

Lemma list_find_fmap {B} (f : A → B) (P : B → Prop)
    `{!∀ y : B, Decision (P y)} (l : list A) :
  list_find P (f <$> l) = prod_map id f <$> list_find (P ∘ f) l.
Proof.
  induction l as [|x l IH]; [done|]; csimpl. (* csimpl re-folds fmap *)
  case_decide; [done|].
  rewrite IH. by destruct (list_find (P ∘ f) l).
Qed.

(** ** Properties of the [resize] function *)
Lemma resize_spec l n x : resize n x l = take n l ++ replicate (n - length l) x.
Proof. revert n. induction l; intros [|?]; f_equal/=; auto. Qed.
Lemma resize_0 l x : resize 0 x l = [].
Proof. by destruct l. Qed.
Lemma resize_nil n x : resize n x [] = replicate n x.
Proof. rewrite resize_spec. rewrite take_nil. f_equal/=. lia. Qed.
Lemma resize_ge l n x :
  length l ≤ n → resize n x l = l ++ replicate (n - length l) x.
Proof. intros. by rewrite resize_spec, take_ge. Qed.
Lemma resize_le l n x : n ≤ length l → resize n x l = take n l.
Proof.
  intros. rewrite resize_spec, (proj2 (Nat.sub_0_le _ _)) by done.
  simpl. by rewrite (right_id_L [] (++)).
Qed.
Lemma resize_all l x : resize (length l) x l = l.
Proof. intros. by rewrite resize_le, take_ge. Qed.
Lemma resize_all_alt l n x : n = length l → resize n x l = l.
Proof. intros ->. by rewrite resize_all. Qed.
Lemma resize_add l n m x :
  resize (n + m) x l = resize n x l ++ resize m x (drop n l).
Proof.
  revert n m. induction l; intros [|?] [|?]; f_equal/=; auto.
  - by rewrite Nat.add_0_r, (right_id_L [] (++)).
  - by rewrite replicate_add.
Qed.
Lemma resize_add_eq l n m x :
  length l = n → resize (n + m) x l = l ++ replicate m x.
Proof. intros <-. by rewrite resize_add, resize_all, drop_all, resize_nil. Qed.
Lemma resize_app_le l1 l2 n x :
  n ≤ length l1 → resize n x (l1 ++ l2) = resize n x l1.
Proof.
  intros. by rewrite !resize_le, take_app_le by (rewrite ?length_app; lia).
Qed.
Lemma resize_app l1 l2 n x : n = length l1 → resize n x (l1 ++ l2) = l1.
Proof. intros ->. by rewrite resize_app_le, resize_all. Qed.
Lemma resize_app_ge l1 l2 n x :
  length l1 ≤ n → resize n x (l1 ++ l2) = l1 ++ resize (n - length l1) x l2.
Proof.
  intros. rewrite !resize_spec, take_app_ge, (assoc_L (++)) by done.
  do 2 f_equal. rewrite length_app. lia.
Qed.
Lemma length_resize l n x : length (resize n x l) = n.
Proof. rewrite resize_spec, length_app, length_replicate, length_take. lia. Qed.
Lemma resize_replicate x n m : resize n x (replicate m x) = replicate n x.
Proof. revert m. induction n; intros [|?]; f_equal/=; auto. Qed.
Lemma resize_resize l n m x : n ≤ m → resize n x (resize m x l) = resize n x l.
Proof.
  revert n m. induction l; simpl.
  - intros. by rewrite !resize_nil, resize_replicate.
  - intros [|?] [|?] ?; f_equal/=; auto with lia.
Qed.
Lemma resize_idemp l n x : resize n x (resize n x l) = resize n x l.
Proof. by rewrite resize_resize. Qed.
Lemma resize_take_le l n m x : n ≤ m → resize n x (take m l) = resize n x l.
Proof. revert n m. induction l; intros [|?][|?] ?; f_equal/=; auto with lia. Qed.
Lemma resize_take_eq l n x : resize n x (take n l) = resize n x l.
Proof. by rewrite resize_take_le. Qed.
Lemma take_resize l n m x : take n (resize m x l) = resize (min n m) x l.
Proof.
  revert n m. induction l; intros [|?][|?]; f_equal/=; auto using take_replicate.
Qed.
Lemma take_resize_le l n m x : n ≤ m → take n (resize m x l) = resize n x l.
Proof. intros. by rewrite take_resize, Nat.min_l. Qed.
Lemma take_resize_eq l n x : take n (resize n x l) = resize n x l.
Proof. intros. by rewrite take_resize, Nat.min_l. Qed.
Lemma take_resize_add l n m x : take n (resize (n + m) x l) = resize n x l.
Proof. by rewrite take_resize, min_l by lia. Qed.
Lemma drop_resize_le l n m x :
  n ≤ m → drop n (resize m x l) = resize (m - n) x (drop n l).
Proof.
  revert n m. induction l; simpl.
  - intros. by rewrite drop_nil, !resize_nil, drop_replicate.
  - intros [|?] [|?] ?; simpl; try case_match; auto with lia.
Qed.
Lemma drop_resize_add l n m x :
  drop n (resize (n + m) x l) = resize m x (drop n l).
Proof. rewrite drop_resize_le by lia. f_equal. lia. Qed.
Lemma lookup_resize l n x i : i < n → i < length l → resize n x l !! i = l !! i.
Proof.
  intros ??. destruct (decide (n < length l)).
  - by rewrite resize_le, lookup_take_lt by lia.
  - by rewrite resize_ge, lookup_app_l by lia.
Qed.
Lemma lookup_total_resize `{!Inhabited A} l n x i :
  i < n → i < length l → resize n x l !!! i = l !!! i.
Proof. intros. by rewrite !list_lookup_total_alt, lookup_resize. Qed.
Lemma lookup_resize_new l n x i :
  length l ≤ i → i < n → resize n x l !! i = Some x.
Proof.
  intros ??. rewrite resize_ge by lia.
  replace i with (length l + (i - length l)) by lia.
  by rewrite lookup_app_r, lookup_replicate_2 by lia.
Qed.
Lemma lookup_total_resize_new `{!Inhabited A} l n x i :
  length l ≤ i → i < n → resize n x l !!! i = x.
Proof. intros. by rewrite !list_lookup_total_alt, lookup_resize_new. Qed.
Lemma lookup_resize_old l n x i : n ≤ i → resize n x l !! i = None.
Proof. intros ?. apply lookup_ge_None_2. by rewrite length_resize. Qed.
Lemma lookup_total_resize_old `{!Inhabited A} l n x i :
  n ≤ i → resize n x l !!! i = inhabitant.
Proof. intros. by rewrite !list_lookup_total_alt, lookup_resize_old. Qed.
Lemma Forall_resize P n x l : P x → Forall P l → Forall P (resize n x l).
Proof.
  intros ? Hl. revert n.
  induction Hl; intros [|?]; simpl; auto using Forall_replicate.
Qed.
Lemma fmap_resize {B} (f : A → B) n x l : f <$> resize n x l = resize n (f x) (f <$> l).
Proof.
  revert n. induction l; intros [|?]; f_equal/=; auto using fmap_replicate.
Qed.
Lemma Forall_resize_inv P n x l :
  length l ≤ n → Forall P (resize n x l) → Forall P l.
Proof. intros ?. rewrite resize_ge, Forall_app by done. by intros []. Qed.

(** ** Properties of the [rotate] function *)
Lemma rotate_replicate n1 n2 x:
  rotate n1 (replicate n2 x) = replicate n2 x.
Proof.
  unfold rotate. rewrite drop_replicate, take_replicate, <-replicate_add.
  f_equal. lia.
Qed.

Lemma length_rotate l n:
  length (rotate n l) = length l.
Proof. unfold rotate. rewrite length_app, length_drop, length_take. lia. Qed.

Lemma lookup_rotate_r l n i:
  i < length l →
  rotate n l !! i = l !! rotate_nat_add n i (length l).
Proof.
  intros Hlen. pose proof (Nat.mod_upper_bound n (length l)) as ?.
  unfold rotate. rewrite rotate_nat_add_add_mod, rotate_nat_add_alt by lia.
  remember (n `mod` length l) as n'.
  case_decide.
  - by rewrite lookup_app_l, lookup_drop by (rewrite length_drop; lia).
  - rewrite lookup_app_r, lookup_take_lt, length_drop by (rewrite length_drop; lia).
    f_equal. lia.
Qed.

Lemma lookup_rotate_r_Some l n i x:
  rotate n l !! i = Some x ↔
  l !! rotate_nat_add n i (length l) = Some x ∧ i < length l.
Proof.
  split.
  - intros Hl. pose proof (lookup_lt_Some _ _ _ Hl) as Hlen.
    rewrite length_rotate in Hlen. by rewrite <-lookup_rotate_r.
  - intros [??]. by rewrite lookup_rotate_r.
Qed.

Lemma lookup_rotate_l l n i:
  i < length l → rotate n l !! rotate_nat_sub n i (length l) = l !! i.
Proof.
  intros ?. rewrite lookup_rotate_r, rotate_nat_add_sub;[done..|].
  apply rotate_nat_sub_lt. lia.
Qed.

Lemma elem_of_rotate l n x:
  x ∈ rotate n l ↔ x ∈ l.
Proof.
  unfold rotate. rewrite <-(take_drop (n `mod` length l) l) at 5.
  rewrite !elem_of_app. naive_solver.
Qed.

Lemma rotate_insert_l l n i x:
  i < length l →
  rotate n (<[rotate_nat_add n i (length l):=x]> l) = <[i:=x]> (rotate n l).
Proof.
  intros Hlen. pose proof (Nat.mod_upper_bound n (length l)) as ?. unfold rotate.
  rewrite length_insert, rotate_nat_add_add_mod, rotate_nat_add_alt by lia.
  remember (n `mod` length l) as n'.
  rewrite take_insert, drop_insert, insert_app, length_drop.
  repeat case_decide; auto with f_equal lia.
Qed.

Lemma rotate_insert_r l n i x:
  i < length l →
  rotate n (<[i:=x]> l) = <[rotate_nat_sub n i (length l):=x]> (rotate n l).
Proof.
  intros ?. rewrite <-rotate_insert_l, rotate_nat_add_sub;[done..|].
  apply rotate_nat_sub_lt. lia.
Qed.

(** ** Properties of the [rotate_take] function *)
Lemma rotate_take_insert l s e i x:
  i < length l →
  rotate_take s e (<[i:=x]>l) =
  if decide (rotate_nat_sub s i (length l) < rotate_nat_sub s e (length l)) then
    <[rotate_nat_sub s i (length l):=x]> (rotate_take s e l) else rotate_take s e l.
Proof.
  intros ?. unfold rotate_take. rewrite rotate_insert_r, length_insert by done.
  rewrite take_insert; case_decide; naive_solver lia.
Qed.

Lemma rotate_take_add l b i :
  i < length l →
  rotate_take b (rotate_nat_add b i (length l)) l = take i (rotate b l).
Proof. intros ?. unfold rotate_take. by rewrite rotate_nat_sub_add. Qed.

(** ** Properties of the [reshape] function *)
Lemma length_reshape szs l : length (reshape szs l) = length szs.
Proof. revert l. by induction szs; intros; f_equal/=. Qed.
Lemma Forall_reshape P l szs : Forall P l → Forall (Forall P) (reshape szs l).
Proof.
  revert l. induction szs; simpl; auto using Forall_take, Forall_drop.
Qed.

(** ** Properties of [sublist_lookup] and [sublist_alter] *)
Lemma sublist_lookup_length l i n k :
  sublist_lookup i n l = Some k → length k = n.
Proof.
  unfold sublist_lookup; intros; simplify_option_eq.
  rewrite length_take, length_drop; lia.
Qed.
Lemma sublist_lookup_all l n : length l = n → sublist_lookup 0 n l = Some l.
Proof.
  intros. unfold sublist_lookup; case_guard; [|lia].
  by rewrite take_ge by (rewrite length_drop; lia).
Qed.
Lemma sublist_lookup_Some l i n :
  i + n ≤ length l → sublist_lookup i n l = Some (take n (drop i l)).
Proof. by unfold sublist_lookup; intros; simplify_option_eq. Qed.
Lemma sublist_lookup_Some' l i n l' :
  sublist_lookup i n l = Some l' ↔ l' = take n (drop i l) ∧ i + n ≤ length l.
Proof. unfold sublist_lookup. case_guard; naive_solver lia. Qed.
Lemma sublist_lookup_None l i n :
  length l < i + n → sublist_lookup i n l = None.
Proof. by unfold sublist_lookup; intros; simplify_option_eq by lia. Qed.
Lemma sublist_eq l k n :
  (n | length l) → (n | length k) →
  (∀ i, sublist_lookup (i * n) n l = sublist_lookup (i * n) n k) → l = k.
Proof.
  revert l k. assert (∀ l i,
    n ≠ 0 → (n | length l) → ¬n * i `div` n + n ≤ length l → length l ≤ i).
  { intros l i ? [j ->] Hjn. apply Nat.nlt_ge; contradict Hjn.
    rewrite <-Nat.mul_succ_r, (Nat.mul_comm n).
    apply Nat.mul_le_mono_r, Nat.le_succ_l, Nat.Div0.div_lt_upper_bound; lia. }
  intros l k Hl Hk Hlookup. destruct (decide (n = 0)) as [->|].
  { by rewrite (nil_length_inv l),
      (nil_length_inv k) by eauto using Nat.divide_0_l. }
  apply list_eq; intros i. specialize (Hlookup (i `div` n)).
  rewrite (Nat.mul_comm _ n) in Hlookup.
  unfold sublist_lookup in *; simplify_option_eq;
    [|by rewrite !lookup_ge_None_2 by auto].
  apply (f_equal (.!! i `mod` n)) in Hlookup.
  by rewrite !lookup_take_lt, !lookup_drop, <-!Nat.div_mod in Hlookup
    by (auto using Nat.mod_upper_bound with lia).
Qed.
Lemma sublist_eq_same_length l k j n :
  length l = j * n → length k = j * n →
  (∀ i,i < j → sublist_lookup (i * n) n l = sublist_lookup (i * n) n k) → l = k.
Proof.
  intros Hl Hk ?. destruct (decide (n = 0)) as [->|].
  { by rewrite (nil_length_inv l), (nil_length_inv k) by lia. }
  apply sublist_eq with n; [by exists j|by exists j|].
  intros i. destruct (decide (i < j)); [by auto|].
  assert (∀ m, m = j * n → m < i * n + n).
  { intros ? ->. replace (i * n + n) with (S i * n) by lia.
    apply Nat.mul_lt_mono_pos_r; lia. }
  by rewrite !sublist_lookup_None by auto.
Qed.
Lemma sublist_lookup_reshape l i n m :
  0 < n → length l = m * n →
  reshape (replicate m n) l !! i = sublist_lookup (i * n) n l.
Proof.
  intros Hn Hl. unfold sublist_lookup.  apply option_eq; intros x; split.
  - intros Hx. case_guard as Hi; simplify_eq/=.
    { f_equal. clear Hi. revert i l Hl Hx.
      induction m as [|m IH]; intros [|i] l ??; simplify_eq/=; auto.
      rewrite <-drop_drop. apply IH; rewrite ?length_drop; auto with lia. }
    destruct Hi. rewrite Hl, <-Nat.mul_succ_l.
    apply Nat.mul_le_mono_r, Nat.le_succ_l. apply lookup_lt_Some in Hx.
    by rewrite length_reshape, length_replicate in Hx.
  - intros Hx. case_guard as Hi; simplify_eq/=.
    revert i l Hl Hi. induction m as [|m IH]; [auto with lia|].
    intros [|i] l ??; simpl; [done|]. rewrite <-drop_drop.
    rewrite IH; rewrite ?length_drop; auto with lia.
Qed.
Lemma sublist_lookup_compose l1 l2 l3 i n j m :
  sublist_lookup i n l1 = Some l2 → sublist_lookup j m l2 = Some l3 →
  sublist_lookup (i + j) m l1 = Some l3.
Proof.
  unfold sublist_lookup; intros; simplify_option_eq;
    repeat match goal with
    | H : _ ≤ length _ |- _ => rewrite length_take, length_drop in H
    end; rewrite ?take_drop_commute, ?drop_drop, ?take_take,
      ?Nat.min_l, Nat.add_assoc by lia; auto with lia.
Qed.
Lemma length_sublist_alter f l i n k :
  sublist_lookup i n l = Some k → length (f k) = n →
  length (sublist_alter f i n l) = length l.
Proof.
  unfold sublist_alter, sublist_lookup. intros Hk ?; simplify_option_eq.
  rewrite !length_app, Hk, !length_take, !length_drop; lia.
Qed.
Lemma sublist_lookup_alter f l i n k :
  sublist_lookup i n l = Some k → length (f k) = n →
  sublist_lookup i n (sublist_alter f i n l) = f <$> sublist_lookup i n l.
Proof.
  unfold sublist_lookup. intros Hk ?. erewrite length_sublist_alter by eauto.
  unfold sublist_alter; simplify_option_eq.
  by rewrite Hk, drop_app_length', take_app_length' by (rewrite ?length_take; lia).
Qed.
Lemma sublist_lookup_alter_ne f l i j n k :
  sublist_lookup j n l = Some k → length (f k) = n → i + n ≤ j ∨ j + n ≤ i →
  sublist_lookup i n (sublist_alter f j n l) = sublist_lookup i n l.
Proof.
  unfold sublist_lookup. intros Hk Hi ?. erewrite length_sublist_alter by eauto.
  unfold sublist_alter; simplify_option_eq; f_equal; rewrite Hk.
  apply list_eq; intros ii.
  destruct (decide (ii < length (f k))); [|by rewrite !lookup_take_ge by lia].
  rewrite !lookup_take_lt, !lookup_drop by done. destruct (decide (i + ii < j)).
  { by rewrite lookup_app_l, lookup_take_lt by (rewrite ?length_take; lia). }
  rewrite lookup_app_r by (rewrite length_take; lia).
  rewrite length_take_le, lookup_app_r, lookup_drop by lia. f_equal; lia.
Qed.
Lemma sublist_alter_all f l n : length l = n → sublist_alter f 0 n l = f l.
Proof.
  intros <-. unfold sublist_alter; simpl.
  by rewrite drop_all, (right_id_L [] (++)), take_ge.
Qed.
Lemma sublist_alter_compose f g l i n k :
  sublist_lookup i n l = Some k → length (f k) = n → length (g k) = n →
  sublist_alter (f ∘ g) i n l = sublist_alter f i n (sublist_alter g i n l).
Proof.
  unfold sublist_alter, sublist_lookup. intros Hk ??; simplify_option_eq.
  by rewrite !take_app_length', drop_app_length', !(assoc_L (++)), drop_app_length',
    take_app_length' by (rewrite ?length_app, ?length_take, ?Hk; lia).
Qed.
Lemma Forall_sublist_lookup P l i n k :
  sublist_lookup i n l = Some k → Forall P l → Forall P k.
Proof.
  unfold sublist_lookup. intros; simplify_option_eq.
  auto using Forall_take, Forall_drop.
Qed.
Lemma Forall_sublist_alter P f l i n k :
  Forall P l → sublist_lookup i n l = Some k → Forall P (f k) →
  Forall P (sublist_alter f i n l).
Proof.
  unfold sublist_alter, sublist_lookup. intros; simplify_option_eq.
  auto using Forall_app_2, Forall_drop, Forall_take.
Qed.
Lemma Forall_sublist_alter_inv P f l i n k :
  sublist_lookup i n l = Some k →
  Forall P (sublist_alter f i n l) → Forall P (f k).
Proof.
  unfold sublist_alter, sublist_lookup. intros ?; simplify_option_eq.
  rewrite !Forall_app; tauto.
Qed.
End general_properties.

Lemma zip_with_sublist_alter {A B} (f : A → B → A) g l k i n l' k' :
  length l = length k →
  sublist_lookup i n l = Some l' → sublist_lookup i n k = Some k' →
  length (g l') = length k' → zip_with f (g l') k' = g (zip_with f l' k') →
  zip_with f (sublist_alter g i n l) k = sublist_alter g i n (zip_with f l k).
Proof.
  unfold sublist_lookup, sublist_alter. intros Hlen; rewrite Hlen.
  intros ?? Hl' Hk'. simplify_option_eq.
  by rewrite !zip_with_app_l, !zip_with_drop, Hl', drop_drop, !zip_with_take,
    !length_take_le, Hk' by (rewrite ?length_drop; auto with lia).
Qed.

(** Interaction of [Forall2] with the above operations (needs to be outside the
section since the operations are used at different types). *)
Section Forall2.
  Context {A B} (P : A → B → Prop).
  Implicit Types x : A.
  Implicit Types y : B.
  Implicit Types l : list A.
  Implicit Types k : list B.

  Lemma Forall2_resize l (k : list B) x (y : B) n :
    P x y → Forall2 P l k → Forall2 P (resize n x l) (resize n y k).
  Proof.
    intros. rewrite !resize_spec, (Forall2_length P l k) by done.
    auto using Forall2_app, Forall2_take, Forall2_replicate.
  Qed.
  Lemma Forall2_resize_l l k x y n m :
    P x y → Forall (flip P y) l →
    Forall2 P (resize n x l) k → Forall2 P (resize m x l) (resize m y k).
  Proof.
    intros. destruct (decide (m ≤ n)).
    { rewrite <-(resize_resize l m n) by done. by apply Forall2_resize. }
    intros. assert (n = length k); subst.
    { by rewrite <-(Forall2_length P (resize n x l) k), length_resize. }
    rewrite (Nat.le_add_sub (length k) m), !resize_add,
      resize_all, drop_all, resize_nil by lia.
    auto using Forall2_app, Forall2_replicate_r,
      Forall_resize, Forall_drop, length_resize.
  Qed.
  Lemma Forall2_resize_r l k x y n m :
    P x y → Forall (P x) k →
    Forall2 P l (resize n y k) → Forall2 P (resize m x l) (resize m y k).
  Proof.
    intros. destruct (decide (m ≤ n)).
    { rewrite <-(resize_resize k m n) by done. by apply Forall2_resize. }
    assert (n = length l); subst.
    { by rewrite (Forall2_length P l (resize n y k)), length_resize. }
    rewrite (Nat.le_add_sub (length l) m), !resize_add,
      resize_all, drop_all, resize_nil by lia.
    auto using Forall2_app, Forall2_replicate_l,
      Forall_resize, Forall_drop, length_resize.
  Qed.
  Lemma Forall2_resize_r_flip l k x y n m :
    P x y → Forall (P x) k →
    length k = m → Forall2 P l (resize n y k) → Forall2 P (resize m x l) k.
  Proof.
    intros ?? <- ?. rewrite <-(resize_all k y) at 2.
    apply Forall2_resize_r with n; auto using Forall_true.
  Qed.

  Lemma Forall2_rotate n l k :
    Forall2 P l k → Forall2 P (rotate n l) (rotate n k).
  Proof.
    intros HAll. unfold rotate. rewrite (Forall2_length _ _ _ HAll).
    eauto using Forall2_app, Forall2_take, Forall2_drop.
  Qed.

  Lemma Forall2_rotate_take s e l k :
    Forall2 P l k → Forall2 P (rotate_take s e l) (rotate_take s e k).
  Proof.
    intros HAll. unfold rotate_take. rewrite (Forall2_length _ _ _ HAll).
    eauto using Forall2_take, Forall2_rotate.
  Qed.

  Lemma Forall2_sublist_lookup_l l k n i l' :
    Forall2 P l k → sublist_lookup n i l = Some l' →
    ∃ k', sublist_lookup n i k = Some k' ∧ Forall2 P l' k'.
  Proof.
    unfold sublist_lookup. intros Hlk Hl.
    exists (take i (drop n k)); simplify_option_eq.
    - auto using Forall2_take, Forall2_drop.
    - apply Forall2_length in Hlk; lia.
  Qed.
  Lemma Forall2_sublist_lookup_r l k n i k' :
    Forall2 P l k → sublist_lookup n i k = Some k' →
    ∃ l', sublist_lookup n i l = Some l' ∧ Forall2 P l' k'.
  Proof.
    intro. unfold sublist_lookup.
    erewrite (Forall2_length P) by eauto; intros; simplify_option_eq.
    eauto using Forall2_take, Forall2_drop.
  Qed.
  Lemma Forall2_sublist_alter f g l k i n l' k' :
    Forall2 P l k → sublist_lookup i n l = Some l' →
    sublist_lookup i n k = Some k' → Forall2 P (f l') (g k') →
    Forall2 P (sublist_alter f i n l) (sublist_alter g i n k).
  Proof.
    intro. unfold sublist_alter, sublist_lookup.
    erewrite Forall2_length by eauto; intros; simplify_option_eq.
    auto using Forall2_app, Forall2_drop, Forall2_take.
  Qed.
  Lemma Forall2_sublist_alter_l f l k i n l' k' :
    Forall2 P l k → sublist_lookup i n l = Some l' →
    sublist_lookup i n k = Some k' → Forall2 P (f l') k' →
    Forall2 P (sublist_alter f i n l) k.
  Proof.
    intro. unfold sublist_lookup, sublist_alter.
    erewrite <-(Forall2_length P) by eauto; intros; simplify_option_eq.
    apply Forall2_app_l;
      rewrite ?length_take_le by lia; auto using Forall2_take.
    apply Forall2_app_l; erewrite Forall2_length, length_take,
      length_drop, <-Forall2_length, Nat.min_l by eauto with lia; [done|].
    rewrite drop_drop; auto using Forall2_drop.
  Qed.

End Forall2.

Section Forall2_proper.
  Context {A} (R : relation A).

  Global Instance: ∀ n, Proper (R ==> Forall2 R ==> Forall2 R) (resize n).
  Proof. repeat intro. eauto using Forall2_resize. Qed.
  Global Instance resize_proper `{!Equiv A} n : Proper ((≡) ==> (≡) ==> (≡@{list A})) (resize n).
  Proof.
    induction n; destruct 2; simpl; repeat (constructor || f_equiv); auto.
  Qed.

  Global Instance : ∀ n, Proper (Forall2 R ==> Forall2 R) (rotate n).
  Proof. repeat intro. eauto using Forall2_rotate. Qed.
  Global Instance rotate_proper `{!Equiv A} n : Proper ((≡@{list A}) ==> (≡)) (rotate n).
  Proof. intros ??. rewrite !list_equiv_Forall2. by apply Forall2_rotate. Qed.

  Global Instance: ∀ s e, Proper (Forall2 R ==> Forall2 R) (rotate_take s e).
  Proof. repeat intro. eauto using Forall2_rotate_take. Qed.
  Global Instance rotate_take_proper `{!Equiv A} s e : Proper ((≡@{list A}) ==> (≡)) (rotate_take s e).
  Proof. intros ??. rewrite !list_equiv_Forall2. by apply Forall2_rotate_take. Qed.
End Forall2_proper.

Section more_general_properties.
Context {A : Type}.
Implicit Types x y z : A.
Implicit Types l k : list A.

(** ** Properties of the [mask] function *)
Lemma mask_nil f βs : mask f βs [] =@{list A} [].
Proof. by destruct βs. Qed.
Lemma length_mask f βs l : length (mask f βs l) = length l.
Proof. revert βs. induction l; intros [|??]; f_equal/=; auto. Qed.
Lemma mask_true f l n : length l ≤ n → mask f (replicate n true) l = f <$> l.
Proof. revert n. induction l; intros [|?] ?; f_equal/=; auto with lia. Qed.
Lemma mask_false f l n : mask f (replicate n false) l = l.
Proof. revert l. induction n; intros [|??]; f_equal/=; auto. Qed.
Lemma mask_app f βs1 βs2 l :
  mask f (βs1 ++ βs2) l
  = mask f βs1 (take (length βs1) l) ++ mask f βs2 (drop (length βs1) l).
Proof. revert l. induction βs1;intros [|??]; f_equal/=; auto using mask_nil. Qed.
Lemma mask_app_2 f βs l1 l2 :
  mask f βs (l1 ++ l2)
  = mask f (take (length l1) βs) l1 ++ mask f (drop (length l1) βs) l2.
Proof. revert βs. induction l1; intros [|??]; f_equal/=; auto. Qed.
Lemma take_mask f βs l n : take n (mask f βs l) = mask f (take n βs) (take n l).
Proof. revert n βs. induction l; intros [|?] [|[] ?]; f_equal/=; auto. Qed.
Lemma drop_mask f βs l n : drop n (mask f βs l) = mask f (drop n βs) (drop n l).
Proof.
  revert n βs. induction l; intros [|?] [|[] ?]; f_equal/=; auto using mask_nil.
Qed.
Lemma sublist_lookup_mask f βs l i n :
  sublist_lookup i n (mask f βs l)
  = mask f (take n (drop i βs)) <$> sublist_lookup i n l.
Proof.
  unfold sublist_lookup; rewrite length_mask; simplify_option_eq; auto.
  by rewrite drop_mask, take_mask.
Qed.
Lemma mask_mask f g βs1 βs2 l :
  (∀ x, f (g x) = f x) → βs1 =.>* βs2 →
  mask f βs2 (mask g βs1 l) = mask f βs2 l.
Proof.
  intros ? Hβs. revert l. by induction Hβs as [|[] []]; intros [|??]; f_equal/=.
Qed.
Lemma lookup_mask f βs l i :
  βs !! i = Some true → mask f βs l !! i = f <$> l !! i.
Proof.
  revert i βs. induction l; intros [] [] ?; simplify_eq/=; f_equal; auto.
Qed.
Lemma lookup_mask_notin f βs l i :
  βs !! i ≠ Some true → mask f βs l !! i = l !! i.
Proof.
  revert i βs. induction l; intros [] [|[]] ?; simplify_eq/=; auto.
Qed.
End more_general_properties.

(** Lemmas about [positives_flatten] and [positives_unflatten]. *)
Section positives_flatten_unflatten.
  Local Open Scope positive_scope.

  Lemma positives_flatten_go_app xs acc :
    positives_flatten_go xs acc = acc ++ positives_flatten_go xs 1.
  Proof.
    revert acc.
    induction xs as [|x xs IH]; intros acc; simpl.
    - reflexivity.
    - rewrite IH.
      rewrite (IH (6 ++ _)).
      rewrite 2!(assoc_L (++)).
      reflexivity.
  Qed.

  Lemma positives_unflatten_go_app p suffix xs acc :
    positives_unflatten_go (suffix ++ Pos.reverse (Pos.dup p)) xs acc =
    positives_unflatten_go suffix xs (acc ++ p).
  Proof.
    revert suffix acc.
    induction p as [p IH|p IH|]; intros acc suffix; simpl.
    - rewrite 2!Pos.reverse_xI.
      rewrite 2!(assoc_L (++)).
      rewrite IH.
      reflexivity.
    - rewrite 2!Pos.reverse_xO.
      rewrite 2!(assoc_L (++)).
      rewrite IH.
      reflexivity.
    - reflexivity.
  Qed.

  Lemma positives_unflatten_flatten_go suffix xs acc :
    positives_unflatten_go (suffix ++ positives_flatten_go xs 1) acc 1 =
    positives_unflatten_go suffix (xs ++ acc) 1.
  Proof.
    revert suffix acc.
    induction xs as [|x xs IH]; intros suffix acc; simpl.
    - reflexivity.
    - rewrite positives_flatten_go_app.
      rewrite (assoc_L (++)).
      rewrite IH.
      rewrite (assoc_L (++)).
      rewrite positives_unflatten_go_app.
      simpl.
      rewrite (left_id_L 1 (++)).
      reflexivity.
  Qed.

  Lemma positives_unflatten_flatten xs :
    positives_unflatten (positives_flatten xs) = Some xs.
  Proof.
    unfold positives_flatten, positives_unflatten.
    replace (positives_flatten_go xs 1)
      with (1 ++ positives_flatten_go xs 1)
      by apply (left_id_L 1 (++)).
    rewrite positives_unflatten_flatten_go.
    simpl.
    rewrite (right_id_L [] (++)%list).
    reflexivity.
  Qed.

  Lemma positives_flatten_app xs ys :
    positives_flatten (xs ++ ys) = positives_flatten xs ++ positives_flatten ys.
  Proof.
    unfold positives_flatten.
    revert ys.
    induction xs as [|x xs IH]; intros ys; simpl.
    - rewrite (left_id_L 1 (++)).
      reflexivity.
    - rewrite positives_flatten_go_app, (positives_flatten_go_app xs).
      rewrite IH.
      rewrite (assoc_L (++)).
      reflexivity.
  Qed.

  Lemma positives_flatten_cons x xs :
    positives_flatten (x :: xs)
    = 1~1~0 ++ Pos.reverse (Pos.dup x) ++ positives_flatten xs.
  Proof.
    change (x :: xs) with ([x] ++ xs)%list.
    rewrite positives_flatten_app.
    rewrite (assoc_L (++)).
    reflexivity.
  Qed.

  Lemma positives_flatten_suffix (l k : list positive) :
    l `suffix_of` k → ∃ q, positives_flatten k = q ++ positives_flatten l.
  Proof.
    intros [l' ->].
    exists (positives_flatten l').
    apply positives_flatten_app.
  Qed.

  Lemma positives_flatten_suffix_eq p1 p2 (xs ys : list positive) :
    length xs = length ys →
    p1 ++ positives_flatten xs = p2 ++ positives_flatten ys →
    xs = ys.
  Proof.
    revert p1 p2 ys; induction xs as [|x xs IH];
      intros p1 p2 [|y ys] ?; simplify_eq/=; auto.
    rewrite !positives_flatten_cons, !(assoc _); intros Hl.
    assert (xs = ys) as <- by eauto; clear IH; f_equal.
    apply (inj (.++ positives_flatten xs)) in Hl.
    rewrite 2!Pos.reverse_dup in Hl.
    apply (Pos.dup_suffix_eq _ _ p1 p2) in Hl.
    by apply (inj Pos.reverse).
  Qed.
End positives_flatten_unflatten.

End list.
