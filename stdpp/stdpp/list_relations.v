From Coq Require Export Permutation.
From stdpp Require Export numbers base option list_basics.
From stdpp Require Import options.

Module Export list.

Global Instance: Params (@Forall) 1 := {}.
Global Instance: Params (@Exists) 1 := {}.
Global Instance: Params (@NoDup) 1 := {}.

Global Arguments Permutation {_} _ _ : assert.
Global Arguments Forall_cons {_} _ _ _ _ _ : assert.

Infix "≡ₚ" := Permutation (at level 70, no associativity) : stdpp_scope.
Notation "(≡ₚ)" := Permutation (only parsing) : stdpp_scope.
Notation "( x ≡ₚ.)" := (Permutation x) (only parsing) : stdpp_scope.
Notation "(.≡ₚ x )" := (λ y, y ≡ₚ x) (only parsing) : stdpp_scope.
Notation "(≢ₚ)" := (λ x y, ¬x ≡ₚ y) (only parsing) : stdpp_scope.
Notation "x ≢ₚ y":= (¬x ≡ₚ y) (at level 70, no associativity) : stdpp_scope.
Notation "( x ≢ₚ.)" := (λ y, x ≢ₚ y) (only parsing) : stdpp_scope.
Notation "(.≢ₚ x )" := (λ y, y ≢ₚ x) (only parsing) : stdpp_scope.

Infix "≡ₚ@{ A }" :=
  (@Permutation A) (at level 70, no associativity, only parsing) : stdpp_scope.
Notation "(≡ₚ@{ A } )" := (@Permutation A) (only parsing) : stdpp_scope.

(** Setoid equality lifted to lists *)
Inductive list_equiv `{Equiv A} : Equiv (list A) :=
  | nil_equiv : [] ≡ []
  | cons_equiv x y l k : x ≡ y → l ≡ k → x :: l ≡ y :: k.
Global Existing Instance list_equiv.

(** The predicate [suffix] holds if the first list is a suffix of the second.
The predicate [prefix] holds if the first list is a prefix of the second. *)
Definition suffix {A} : relation (list A) := λ l1 l2, ∃ k, l2 = k ++ l1.
Definition prefix {A} : relation (list A) := λ l1 l2, ∃ k, l2 = l1 ++ k.
Infix "`suffix_of`" := suffix (at level 70) : stdpp_scope.
Infix "`prefix_of`" := prefix (at level 70) : stdpp_scope.
Global Hint Extern 0 (_ `prefix_of` _) => reflexivity : core.
Global Hint Extern 0 (_ `suffix_of` _) => reflexivity : core.

(** A list is a "subset" of another if each element of the first also appears
somewhere in the second. *)
Global Instance list_subseteq {A} : SubsetEq (list A) := λ l1 l2, ∀ x, x ∈ l1 → x ∈ l2.

(** A list [l1] is a sublist of [l2] if [l2] is obtained by removing elements
from [l1] without changing the order. *)
Inductive sublist {A} : relation (list A) :=
  | sublist_nil : sublist [] []
  | sublist_skip x l1 l2 : sublist l1 l2 → sublist (x :: l1) (x :: l2)
  | sublist_cons x l1 l2 : sublist l1 l2 → sublist l1 (x :: l2).
Infix "`sublist_of`" := sublist (at level 70) : stdpp_scope.
Global Hint Extern 0 (_ `sublist_of` _) => reflexivity : core.

(** A list [l2] submseteq a list [l1] if [l2] is obtained by removing elements
from [l1] while possibly changing the order. *)
Inductive submseteq {A} : relation (list A) :=
  | submseteq_nil : submseteq [] []
  | submseteq_skip x l1 l2 : submseteq l1 l2 → submseteq (x :: l1) (x :: l2)
  | submseteq_swap x y l : submseteq (y :: x :: l) (x :: y :: l)
  | submseteq_cons x l1 l2 : submseteq l1 l2 → submseteq l1 (x :: l2)
  | submseteq_trans l1 l2 l3 : submseteq l1 l2 → submseteq l2 l3 → submseteq l1 l3.
Infix "⊆+" := submseteq (at level 70) : stdpp_scope.
Global Hint Extern 0 (_ ⊆+ _) => reflexivity : core.

Section prefix_suffix_ops.
  Context `{EqDecision A}.

  Definition max_prefix : list A → list A → list A * list A * list A :=
    fix go l1 l2 :=
    match l1, l2 with
    | [], l2 => ([], l2, [])
    | l1, [] => (l1, [], [])
    | x1 :: l1, x2 :: l2 =>
      if decide_rel (=) x1 x2
      then prod_map id (x1 ::.) (go l1 l2) else (x1 :: l1, x2 :: l2, [])
    end.
  Definition max_suffix (l1 l2 : list A) : list A * list A * list A :=
    match max_prefix (reverse l1) (reverse l2) with
    | (k1, k2, k3) => (reverse k1, reverse k2, reverse k3)
    end.
  Definition strip_prefix (l1 l2 : list A) := (max_prefix l1 l2).1.2.
  Definition strip_suffix (l1 l2 : list A) := (max_suffix l1 l2).1.2.
End prefix_suffix_ops.

Inductive Forall3 {A B C} (P : A → B → C → Prop) :
     list A → list B → list C → Prop :=
  | Forall3_nil : Forall3 P [] [] []
  | Forall3_cons x y z l k k' :
     P x y z → Forall3 P l k k' → Forall3 P (x :: l) (y :: k) (z :: k').

Section general_properties.
Context {A : Type}.
Implicit Types x y z : A.
Implicit Types l k : list A.

(** ** Properties of the [NoDup] predicate *)
Lemma NoDup_nil : NoDup (@nil A) ↔ True.
Proof. split; constructor. Qed.
Lemma NoDup_cons x l : NoDup (x :: l) ↔ x ∉ l ∧ NoDup l.
Proof. split; [by inv 1|]. intros [??]. by constructor. Qed.
Lemma NoDup_cons_1_1 x l : NoDup (x :: l) → x ∉ l.
Proof. rewrite NoDup_cons. by intros [??]. Qed.
Lemma NoDup_cons_1_2 x l : NoDup (x :: l) → NoDup l.
Proof. rewrite NoDup_cons. by intros [??]. Qed.
Lemma NoDup_singleton x : NoDup [x].
Proof. constructor; [apply not_elem_of_nil | constructor]. Qed.
Lemma NoDup_app l k : NoDup (l ++ k) ↔ NoDup l ∧ (∀ x, x ∈ l → x ∉ k) ∧ NoDup k.
Proof.
  induction l; simpl.
  - rewrite NoDup_nil. setoid_rewrite elem_of_nil. naive_solver.
  - rewrite !NoDup_cons.
    setoid_rewrite elem_of_cons. setoid_rewrite elem_of_app. naive_solver.
Qed.
Lemma NoDup_lookup l i j x :
  NoDup l → l !! i = Some x → l !! j = Some x → i = j.
Proof.
  intros Hl. revert i j. induction Hl as [|x' l Hx Hl IH].
  { intros; simplify_eq. }
  intros [|i] [|j] ??; simplify_eq/=; eauto with f_equal;
    exfalso; eauto using list_elem_of_lookup_2.
Qed.
Lemma NoDup_alt l :
  NoDup l ↔ ∀ i j x, l !! i = Some x → l !! j = Some x → i = j.
Proof.
  split; eauto using NoDup_lookup.
  induction l as [|x l IH]; intros Hl; constructor.
  - rewrite list_elem_of_lookup. intros [i ?].
    opose proof* (Hl (S i) 0); by auto.
  - apply IH. intros i j x' ??. by apply (inj S), (Hl (S i) (S j) x').
Qed.

Lemma NoDup_filter (P : A → Prop) `{∀ x, Decision (P x)} l :
  NoDup l → NoDup (filter P l).
Proof.
  induction 1; rewrite ?filter_cons; repeat case_decide;
    rewrite ?NoDup_nil, ?NoDup_cons, ?list_elem_of_filter; tauto.
Qed.

Section no_dup_dec.
  Context `{!EqDecision A}.
  Global Instance NoDup_dec: ∀ l, Decision (NoDup l) :=
    fix NoDup_dec l :=
    match l return Decision (NoDup l) with
    | [] => left NoDup_nil_2
    | x :: l =>
      match decide_rel (∈) x l with
      | left Hin => right (λ H, NoDup_cons_1_1 _ _ H Hin)
      | right Hin =>
        match NoDup_dec l with
        | left H => left (NoDup_cons_2 _ _ Hin H)
        | right H => right (H ∘ NoDup_cons_1_2 _ _)
        end
      end
    end.
  Lemma elem_of_remove_dups l x : x ∈ remove_dups l ↔ x ∈ l.
  Proof.
    split; induction l; simpl; repeat case_decide;
      rewrite ?elem_of_cons; intuition (simplify_eq; auto).
  Qed.
  Lemma NoDup_remove_dups l : NoDup (remove_dups l).
  Proof.
    induction l; simpl; repeat case_decide; try constructor; auto.
    by rewrite elem_of_remove_dups.
  Qed.

  Lemma NoDup_list_difference l k : NoDup l → NoDup (list_difference l k).
  Proof.
    induction 1; simpl; try case_decide.
    - constructor.
    - done.
    - constructor; [|done]. rewrite list_elem_of_difference; intuition.
  Qed.
  Lemma NoDup_list_union l k : NoDup l → NoDup k → NoDup (list_union l k).
  Proof.
    intros. apply NoDup_app. repeat split.
    - by apply NoDup_list_difference.
    - intro. rewrite list_elem_of_difference. intuition.
    - done.
  Qed.
  Lemma NoDup_list_intersection l k : NoDup l → NoDup (list_intersection l k).
  Proof.
    induction 1; simpl; try case_decide.
    - constructor.
    - constructor; [|done]. rewrite list_elem_of_intersection; intuition.
    - done.
  Qed.

End no_dup_dec.

(** ** Properties of the [Permutation] predicate *)
Lemma Permutation_nil_r l : l ≡ₚ [] ↔ l = [].
Proof. split; [by intro; apply Permutation_nil | by intros ->]. Qed.
Lemma Permutation_singleton_r l x : l ≡ₚ [x] ↔ l = [x].
Proof. split; [by intro; apply Permutation_length_1_inv | by intros ->]. Qed.
Lemma Permutation_nil_l l : [] ≡ₚ l ↔ [] = l.
Proof. by rewrite (symmetry_iff (≡ₚ)), Permutation_nil_r. Qed.
Lemma Permutation_singleton_l l x : [x] ≡ₚ l ↔ [x] = l.
Proof. by rewrite (symmetry_iff (≡ₚ)), Permutation_singleton_r. Qed.

Lemma Permutation_skip x l l' : l ≡ₚ l' → x :: l ≡ₚ x :: l'.
Proof. apply perm_skip. Qed.
Lemma Permutation_swap x y l : y :: x :: l ≡ₚ x :: y :: l.
Proof. apply perm_swap. Qed.
Lemma Permutation_singleton_inj x y : [x] ≡ₚ [y] → x = y.
Proof. apply Permutation_length_1. Qed.

Global Instance length_Permutation_proper : Proper ((≡ₚ) ==> (=)) (@length A).
Proof. induction 1; simpl; auto with lia. Qed.
Global Instance elem_of_Permutation_proper x : Proper ((≡ₚ) ==> iff) (x ∈.).
Proof. induction 1; rewrite ?elem_of_nil, ?elem_of_cons; intuition. Qed.
Global Instance NoDup_Permutation_proper: Proper ((≡ₚ) ==> iff) (@NoDup A).
Proof.
  induction 1 as [|x l k Hlk IH | |].
  - by rewrite !NoDup_nil.
  - by rewrite !NoDup_cons, IH, Hlk.
  - rewrite !NoDup_cons, !elem_of_cons. intuition.
  - intuition.
Qed.

Global Instance app_Permutation_comm : Comm (≡ₚ) (@app A).
Proof.
  intros l1. induction l1 as [|x l1 IH]; intros l2; simpl.
  - by rewrite (right_id_L [] (++)).
  - rewrite Permutation_middle, IH. simpl. by rewrite Permutation_middle.
Qed.

Global Instance cons_Permutation_inj_r x : Inj (≡ₚ) (≡ₚ) (x ::.).
Proof. red. eauto using Permutation_cons_inv. Qed.
Global Instance app_Permutation_inj_r k : Inj (≡ₚ) (≡ₚ) (k ++.).
Proof.
  induction k as [|x k IH]; intros l1 l2; simpl; auto.
  intros. by apply IH, (inj (x ::.)).
Qed.
Global Instance cons_Permutation_inj_l k : Inj (=) (≡ₚ) (.:: k).
Proof.
  intros x1 x2 Hperm. apply Permutation_singleton_inj.
  apply (inj (k ++.)). by rewrite !(comm (++) k).
Qed.
Global Instance app_Permutation_inj_l k : Inj (≡ₚ) (≡ₚ) (.++ k).
Proof. intros l1 l2. rewrite !(comm (++) _ k). by apply (inj (k ++.)). Qed.

Lemma replicate_Permutation n x l : replicate n x ≡ₚ l → replicate n x = l.
Proof.
  intros Hl. apply replicate_as_elem_of. split.
  - by rewrite <-Hl, length_replicate.
  - intros y. rewrite <-Hl. by apply elem_of_replicate_inv.
Qed.
Lemma reverse_Permutation l : reverse l ≡ₚ l.
Proof.
  induction l as [|x l IH]; [done|].
  by rewrite reverse_cons, (comm (++)), IH.
Qed.
Lemma delete_Permutation l i x : l !! i = Some x → l ≡ₚ x :: delete i l.
Proof.
  revert i; induction l as [|y l IH]; intros [|i] ?; simplify_eq/=; auto.
  by rewrite Permutation_swap, <-(IH i).
Qed.
Lemma elem_of_Permutation l x : x ∈ l ↔ ∃ k, l ≡ₚ x :: k.
Proof.
  split.
  - intros [i ?]%list_elem_of_lookup. eexists. by apply delete_Permutation.
  - intros [k ->]. by left.
Qed.

Lemma Permutation_cons_inv_r l k x :
  k ≡ₚ x :: l → ∃ k1 k2, k = k1 ++ x :: k2 ∧ l ≡ₚ k1 ++ k2.
Proof.
  intros Hk. assert (∃ i, k !! i = Some x) as [i Hi].
  { apply list_elem_of_lookup. rewrite Hk, elem_of_cons; auto. }
  exists (take i k), (drop (S i) k). split.
  - by rewrite take_drop_middle.
  - rewrite <-delete_take_drop. apply (inj (x ::.)).
    by rewrite <-Hk, <-(delete_Permutation k) by done.
Qed.
Lemma Permutation_cons_inv_l l k x :
  x :: l ≡ₚ k → ∃ k1 k2, k = k1 ++ x :: k2 ∧ l ≡ₚ k1 ++ k2.
Proof. by intros ?%(symmetry_iff (≡ₚ))%Permutation_cons_inv_r. Qed.

Lemma Permutation_cross_split (la lb lc ld : list A) :
  la ++ lb ≡ₚ lc ++ ld →
  ∃ lac lad lbc lbd,
    lac ++ lad ≡ₚ la ∧ lbc ++ lbd ≡ₚ lb ∧ lac ++ lbc ≡ₚ lc ∧ lad ++ lbd ≡ₚ ld.
Proof.
  revert lc ld.
  induction la as [|x la IH]; simpl; intros lc ld Hperm.
  { exists [], [], lc, ld. by rewrite !(right_id_L [] (++)). }
  assert (x ∈ lc ++ ld)
    as [[lc' Hlc]%elem_of_Permutation|[ld' Hld]%elem_of_Permutation]%elem_of_app.
  { rewrite <-Hperm, elem_of_cons. auto. }
  - rewrite Hlc in Hperm. simpl in Hperm. apply (inj (x ::.)) in Hperm.
    apply IH in Hperm as (lac&lad&lbc&lbd&Ha&Hb&Hc&Hd).
    exists (x :: lac), lad, lbc, lbd; simpl. by rewrite Ha, Hb, Hc, Hd.
  - rewrite Hld, <-Permutation_middle in Hperm. apply (inj (x ::.)) in Hperm.
    apply IH in Hperm as (lac&lad&lbc&lbd&Ha&Hb&Hc&Hd).
    exists lac, (x :: lad), lbc, lbd; simpl.
    by rewrite <-Permutation_middle, Ha, Hb, Hc, Hd.
Qed.

Lemma Permutation_inj l1 l2 :
  Permutation l1 l2 ↔
    length l1 = length l2 ∧
    ∃ f : nat → nat, Inj (=) (=) f ∧ ∀ i, l1 !! i = l2 !! f i.
Proof.
  split.
  - intros Hl; split; [by apply Permutation_length|].
    induction Hl as [|x l1 l2 _ [f [??]]|x y l|l1 l2 l3 _ [f [? Hf]] _ [g [? Hg]]].
    + exists id; split; [apply _|done].
    + exists (λ i, match i with 0 => 0 | S i => S (f i) end); split.
      * by intros [|i] [|j] ?; simplify_eq/=.
      * intros [|i]; simpl; auto.
    + exists (λ i, match i with 0 => 1 | 1 => 0 | _ => i end); split.
      * intros [|[|i]] [|[|j]]; congruence.
      * by intros [|[|i]].
    + exists (g ∘ f); split; [apply _|]. intros i; simpl. by rewrite <-Hg, <-Hf.
  - intros (Hlen & f & Hf & Hl). revert l2 f Hlen Hf Hl.
    induction l1 as [|x l1 IH]; intros l2 f Hlen Hf Hl; [by destruct l2|].
    rewrite (delete_Permutation l2 (f 0) x) by (by rewrite <-Hl).
    pose (g n := let m := f (S n) in if lt_eq_lt_dec m (f 0) then m else m - 1).
    apply Permutation_skip, (IH _ g).
    + rewrite length_delete by (rewrite <-Hl; eauto); simpl in *; lia.
    + unfold g. intros i j Hg.
      repeat destruct (lt_eq_lt_dec _ _) as [[?|?]|?]; simplify_eq/=; try lia.
      apply (inj S), (inj f); lia.
    + intros i. unfold g. destruct (lt_eq_lt_dec _ _) as [[?|?]|?].
      * by rewrite list_lookup_delete_lt, <-Hl.
      * simplify_eq.
      * rewrite list_lookup_delete_ge, <-Nat.sub_succ_l by lia; simpl.
        by rewrite Nat.sub_0_r, <-Hl.
Qed.

Global Instance filter_Permutation (P : A → Prop) `{∀ x, Decision (P x)} :
  Proper ((≡ₚ) ==> (≡ₚ)) (filter P).
Proof.
  induction 1; rewrite ?filter_cons;
    repeat (simpl; repeat case_decide); by econstructor.
Qed.

(** ** Properties of the [filter] function that need permutation *)
Section filter.
  Context (P : A → Prop) `{∀ x, Decision (P x)}.
  Local Arguments filter {_ _ _} _ {_} !_ /.

  Lemma filter_app_complement l : filter P l ++ filter (λ x, ¬P x) l ≡ₚ l.
  Proof.
    induction l as [|x l IH]; simpl; [done|]. case_decide.
    - rewrite decide_False by naive_solver. simpl. by rewrite IH.
    - rewrite decide_True by done. by rewrite <-Permutation_middle, IH.
  Qed.
End filter.

(** ** Properties of the [prefix] and [suffix] predicates *)
Global Instance: PartialOrder (@prefix A).
Proof.
  split; [split|].
  - intros ?. eexists []. by rewrite (right_id_L [] (++)).
  - intros ???[k1->] [k2->]. exists (k1 ++ k2). by rewrite (assoc_L (++)).
  - intros l1 l2 [k1 ?] [[|x2 k2] ->]; [|discriminate_list].
    by rewrite (right_id_L _ _).
Qed.
Lemma prefix_nil l : [] `prefix_of` l.
Proof. by exists l. Qed.
Lemma prefix_nil_inv l : l `prefix_of` [] → l = [].
Proof. intros [k ?]. by destruct l. Qed.
Lemma prefix_nil_not x l : ¬x :: l `prefix_of` [].
Proof. by intros [k ?]. Qed.
Lemma prefix_cons x l1 l2 : l1 `prefix_of` l2 → x :: l1 `prefix_of` x :: l2.
Proof. intros [k ->]. by exists k. Qed.
Lemma prefix_cons_alt x y l1 l2 :
  x = y → l1 `prefix_of` l2 → x :: l1 `prefix_of` y :: l2.
Proof. intros ->. apply prefix_cons. Qed.
Lemma prefix_cons_inv_1 x y l1 l2 : x :: l1 `prefix_of` y :: l2 → x = y.
Proof. by intros [k ?]; simplify_eq/=. Qed.
Lemma prefix_cons_inv_2 x y l1 l2 :
  x :: l1 `prefix_of` y :: l2 → l1 `prefix_of` l2.
Proof. intros [k ?]; simplify_eq/=. by exists k. Qed.
Lemma prefix_app k l1 l2 : l1 `prefix_of` l2 → k ++ l1 `prefix_of` k ++ l2.
Proof. intros [k' ->]. exists k'. by rewrite (assoc_L (++)). Qed.
Lemma prefix_app_alt k1 k2 l1 l2 :
  k1 = k2 → l1 `prefix_of` l2 → k1 ++ l1 `prefix_of` k2 ++ l2.
Proof. intros ->. apply prefix_app. Qed.
Lemma prefix_app_inv k l1 l2 :
  k ++ l1 `prefix_of` k ++ l2 → l1 `prefix_of` l2.
Proof.
  intros [k' E]. exists k'. rewrite <-(assoc_L (++)) in E. by simplify_list_eq.
Qed.
Lemma prefix_app_l l1 l2 l3 : l1 ++ l3 `prefix_of` l2 → l1 `prefix_of` l2.
Proof. intros [k ->]. exists (l3 ++ k). by rewrite (assoc_L (++)). Qed.
Lemma prefix_app_r l1 l2 l3 : l1 `prefix_of` l2 → l1 `prefix_of` l2 ++ l3.
Proof. intros [k ->]. exists (k ++ l3). by rewrite (assoc_L (++)). Qed.
Lemma prefix_take l n : take n l `prefix_of` l.
Proof. rewrite <-(take_drop n l) at 2. apply prefix_app_r. done. Qed.
Lemma prefix_lookup_lt l1 l2 i :
  i < length l1 → l1 `prefix_of` l2 → l1 !! i = l2 !! i.
Proof. intros ? [? ->]. by rewrite lookup_app_l. Qed.
Lemma prefix_lookup_Some l1 l2 i x :
  l1 !! i = Some x → l1 `prefix_of` l2 → l2 !! i = Some x.
Proof. intros ? [k ->]. rewrite lookup_app_l; eauto using lookup_lt_Some. Qed.
Lemma prefix_length l1 l2 : l1 `prefix_of` l2 → length l1 ≤ length l2.
Proof. intros [? ->]. rewrite length_app. lia. Qed.
Lemma prefix_snoc_not l x : ¬l ++ [x] `prefix_of` l.
Proof. intros [??]. discriminate_list. Qed.
Lemma elem_of_prefix l1 l2 x :
  x ∈ l1 → l1 `prefix_of` l2 → x ∈ l2.
Proof. intros Hin [l' ->]. apply elem_of_app. by left. Qed.
(* [prefix] is not a total order, but [l1] and [l2] are always comparable if
  they are both prefixes of some [l3]. *)
Lemma prefix_weak_total l1 l2 l3 :
  l1 `prefix_of` l3 → l2 `prefix_of` l3 → l1 `prefix_of` l2 ∨ l2 `prefix_of` l1.
Proof.
  intros [k1 H1] [k2 H2]. rewrite H2 in H1.
  apply app_eq_inv in H1 as [(k&?&?)|(k&?&?)]; [left|right]; exists k; eauto.
Qed.
Global Instance: PartialOrder (@suffix A).
Proof.
  split; [split|].
  - intros ?. by eexists [].
  - intros ???[k1->] [k2->]. exists (k2 ++ k1). by rewrite (assoc_L (++)).
  - intros l1 l2 [k1 ?] [[|x2 k2] ->]; [done|discriminate_list].
Qed.
Global Instance prefix_dec `{!EqDecision A} : RelDecision prefix :=
  fix go l1 l2 :=
  match l1, l2  with
  | [], _ => left (prefix_nil _)
  | _, [] => right (prefix_nil_not _ _)
  | x :: l1, y :: l2 =>
    match decide_rel (=) x y with
    | left Hxy =>
      match go l1 l2 with
      | left Hl1l2 => left (prefix_cons_alt _ _ _ _ Hxy Hl1l2)
      | right Hl1l2 => right (Hl1l2 ∘ prefix_cons_inv_2 _ _ _ _)
      end
    | right Hxy => right (Hxy ∘ prefix_cons_inv_1 _ _ _ _)
    end
  end.
Lemma prefix_not_elem_of_app_cons_inv x y l1 l2 k1 k2 :
  x ∉ k1 → y ∉ l1 →
  (l1 ++ x :: l2) `prefix_of` (k1 ++ y :: k2) →
  l1 = k1 ∧ x = y ∧ l2 `prefix_of` k2.
Proof.
  intros Hin1 Hin2 [k Hle]. rewrite <-(assoc_L (++)) in Hle.
  apply not_elem_of_app_cons_inv_l in Hle; [|done..]. unfold prefix. naive_solver.
Qed.

Lemma prefix_length_eq l1 l2 :
  l1 `prefix_of` l2 → length l2 ≤ length l1 → l1 = l2.
Proof.
  intros Hprefix Hlen. assert (length l1 = length l2).
  { apply prefix_length in Hprefix. lia. }
  eapply list_eq_same_length with (length l1); [done..|].
  intros i x y _ ??. assert (l2 !! i = Some x) by eauto using prefix_lookup_Some.
  congruence.
Qed.

Section prefix_ops.
  Context `{!EqDecision A}.
  Lemma max_prefix_fst l1 l2 :
    l1 = (max_prefix l1 l2).2 ++ (max_prefix l1 l2).1.1.
  Proof.
    revert l2. induction l1; intros [|??]; simpl;
      repeat case_decide; f_equal/=; auto.
  Qed.
  Lemma max_prefix_fst_alt l1 l2 k1 k2 k3 :
    max_prefix l1 l2 = (k1, k2, k3) → l1 = k3 ++ k1.
  Proof.
    intros. pose proof (max_prefix_fst l1 l2).
    by destruct (max_prefix l1 l2) as [[]?]; simplify_eq.
  Qed.
  Lemma max_prefix_fst_prefix l1 l2 : (max_prefix l1 l2).2 `prefix_of` l1.
  Proof. eexists. apply max_prefix_fst. Qed.
  Lemma max_prefix_fst_prefix_alt l1 l2 k1 k2 k3 :
    max_prefix l1 l2 = (k1, k2, k3) → k3 `prefix_of` l1.
  Proof. eexists. eauto using max_prefix_fst_alt. Qed.
  Lemma max_prefix_snd l1 l2 :
    l2 = (max_prefix l1 l2).2 ++ (max_prefix l1 l2).1.2.
  Proof.
    revert l2. induction l1; intros [|??]; simpl;
      repeat case_decide; f_equal/=; auto.
  Qed.
  Lemma max_prefix_snd_alt l1 l2 k1 k2 k3 :
    max_prefix l1 l2 = (k1, k2, k3) → l2 = k3 ++ k2.
  Proof.
    intro. pose proof (max_prefix_snd l1 l2).
    by destruct (max_prefix l1 l2) as [[]?]; simplify_eq.
  Qed.
  Lemma max_prefix_snd_prefix l1 l2 : (max_prefix l1 l2).2 `prefix_of` l2.
  Proof. eexists. apply max_prefix_snd. Qed.
  Lemma max_prefix_snd_prefix_alt l1 l2 k1 k2 k3 :
    max_prefix l1 l2 = (k1,k2,k3) → k3 `prefix_of` l2.
  Proof. eexists. eauto using max_prefix_snd_alt. Qed.
  Lemma max_prefix_max l1 l2 k :
    k `prefix_of` l1 → k `prefix_of` l2 → k `prefix_of` (max_prefix l1 l2).2.
  Proof.
    intros [l1' ->] [l2' ->]. by induction k; simpl; repeat case_decide;
      simpl; auto using prefix_nil, prefix_cons.
  Qed.
  Lemma max_prefix_max_alt l1 l2 k1 k2 k3 k :
    max_prefix l1 l2 = (k1,k2,k3) →
    k `prefix_of` l1 → k `prefix_of` l2 → k `prefix_of` k3.
  Proof.
    intro. pose proof (max_prefix_max l1 l2 k).
    by destruct (max_prefix l1 l2) as [[]?]; simplify_eq.
  Qed.
  Lemma max_prefix_max_snoc l1 l2 k1 k2 k3 x1 x2 :
    max_prefix l1 l2 = (x1 :: k1, x2 :: k2, k3) → x1 ≠ x2.
  Proof.
    intros Hl ->. destruct (prefix_snoc_not k3 x2).
    eapply max_prefix_max_alt; eauto.
    - rewrite (max_prefix_fst_alt _ _ _ _ _ Hl).
      apply prefix_app, prefix_cons, prefix_nil.
    - rewrite (max_prefix_snd_alt _ _ _ _ _ Hl).
      apply prefix_app, prefix_cons, prefix_nil.
  Qed.
End prefix_ops.

Lemma prefix_suffix_reverse l1 l2 :
  l1 `prefix_of` l2 ↔ reverse l1 `suffix_of` reverse l2.
Proof.
  split; intros [k E]; exists (reverse k).
  - by rewrite E, reverse_app.
  - by rewrite <-(reverse_involutive l2), E, reverse_app, reverse_involutive.
Qed.
Lemma suffix_prefix_reverse l1 l2 :
  l1 `suffix_of` l2 ↔ reverse l1 `prefix_of` reverse l2.
Proof. by rewrite prefix_suffix_reverse, !reverse_involutive. Qed.
Lemma suffix_nil l : [] `suffix_of` l.
Proof. exists l. by rewrite (right_id_L [] (++)). Qed.
Lemma suffix_nil_inv l : l `suffix_of` [] → l = [].
Proof. by intros [[|?] ?]; simplify_list_eq. Qed.
Lemma suffix_cons_nil_inv x l : ¬x :: l `suffix_of` [].
Proof. by intros [[] ?]. Qed.
Lemma suffix_snoc l1 l2 x :
  l1 `suffix_of` l2 → l1 ++ [x] `suffix_of` l2 ++ [x].
Proof. intros [k ->]. exists k. by rewrite (assoc_L (++)). Qed.
Lemma suffix_snoc_alt x y l1 l2 :
  x = y → l1 `suffix_of` l2 → l1 ++ [x] `suffix_of` l2 ++ [y].
Proof. intros ->. apply suffix_snoc. Qed.
Lemma suffix_app l1 l2 k : l1 `suffix_of` l2 → l1 ++ k `suffix_of` l2 ++ k.
Proof. intros [k' ->]. exists k'. by rewrite (assoc_L (++)). Qed.
Lemma suffix_app_alt l1 l2 k1 k2 :
  k1 = k2 → l1 `suffix_of` l2 → l1 ++ k1 `suffix_of` l2 ++ k2.
Proof. intros ->. apply suffix_app. Qed.
Lemma suffix_snoc_inv_1 x y l1 l2 :
  l1 ++ [x] `suffix_of` l2 ++ [y] → x = y.
Proof. intros [k' E]. rewrite (assoc_L (++)) in E. by simplify_list_eq. Qed.
Lemma suffix_snoc_inv_2 x y l1 l2 :
  l1 ++ [x] `suffix_of` l2 ++ [y] → l1 `suffix_of` l2.
Proof.
  intros [k' E]. exists k'. rewrite (assoc_L (++)) in E. by simplify_list_eq.
Qed.
Lemma suffix_app_inv l1 l2 k :
  l1 ++ k `suffix_of` l2 ++ k → l1 `suffix_of` l2.
Proof.
  intros [k' E]. exists k'. rewrite (assoc_L (++)) in E. by simplify_list_eq.
Qed.
Lemma suffix_cons_l l1 l2 x : x :: l1 `suffix_of` l2 → l1 `suffix_of` l2.
Proof. intros [k ->]. exists (k ++ [x]). by rewrite <-(assoc_L (++)). Qed.
Lemma suffix_app_l l1 l2 l3 : l3 ++ l1 `suffix_of` l2 → l1 `suffix_of` l2.
Proof. intros [k ->]. exists (k ++ l3). by rewrite <-(assoc_L (++)). Qed.
Lemma suffix_cons_r l1 l2 x : l1 `suffix_of` l2 → l1 `suffix_of` x :: l2.
Proof. intros [k ->]. by exists (x :: k). Qed.
Lemma suffix_app_r l1 l2 l3 : l1 `suffix_of` l2 → l1 `suffix_of` l3 ++ l2.
Proof. intros [k ->]. exists (l3 ++ k). by rewrite (assoc_L (++)). Qed.
Lemma suffix_drop l n : drop n l `suffix_of` l.
Proof. rewrite <-(take_drop n l) at 2. apply suffix_app_r. done. Qed.
Lemma suffix_cons_inv l1 l2 x y :
  x :: l1 `suffix_of` y :: l2 → x :: l1 = y :: l2 ∨ x :: l1 `suffix_of` l2.
Proof.
  intros [[|? k] E]; [by left|]. right. simplify_eq/=. by apply suffix_app_r.
Qed.
Lemma suffix_lookup_lt l1 l2 i :
  i < length l1 →
  l1 `suffix_of` l2 →
  l1 !! i = l2 !! (i + (length l2 - length l1)).
Proof.
  intros Hi [k ->]. rewrite length_app, lookup_app_r by lia. f_equal; lia.
Qed.
Lemma suffix_lookup_Some l1 l2 i x :
  l1 !! i = Some x →
  l1 `suffix_of` l2 →
  l2 !! (i + (length l2 - length l1)) = Some x.
Proof. intros. by rewrite <-suffix_lookup_lt by eauto using lookup_lt_Some. Qed.
Lemma suffix_length l1 l2 : l1 `suffix_of` l2 → length l1 ≤ length l2.
Proof. intros [? ->]. rewrite length_app. lia. Qed.
Lemma suffix_cons_not x l : ¬x :: l `suffix_of` l.
Proof. intros [??]. discriminate_list. Qed.
Lemma elem_of_suffix l1 l2 x :
  x ∈ l1 → l1 `suffix_of` l2 → x ∈ l2.
Proof. intros Hin [l' ->]. apply elem_of_app. by right. Qed.
(* [suffix] is not a total order, but [l1] and [l2] are always comparable if
  they are both suffixes of some [l3]. *)
Lemma suffix_weak_total l1 l2 l3 :
  l1 `suffix_of` l3 → l2 `suffix_of` l3 → l1 `suffix_of` l2 ∨ l2 `suffix_of` l1.
Proof.
  intros [k1 Hl1] [k2 Hl2]. rewrite Hl1 in Hl2.
  apply app_eq_inv in Hl2 as [(k&?&?)|(k&?&?)]; [left|right]; exists k; eauto.
Qed.
Global Instance suffix_dec `{!EqDecision A} : RelDecision (@suffix A).
Proof.
  refine (λ l1 l2, cast_if (decide_rel prefix (reverse l1) (reverse l2)));
   abstract (by rewrite suffix_prefix_reverse).
Defined.
Lemma suffix_not_elem_of_app_cons_inv x y l1 l2 k1 k2 :
  x ∉ k2 → y ∉ l2 →
  (l1 ++ x :: l2) `suffix_of` (k1 ++ y :: k2) →
  l1 `suffix_of` k1 ∧ x = y ∧ l2 = k2.
Proof.
  intros Hin1 Hin2 [k Hle]. rewrite (assoc_L (++)) in Hle.
  apply not_elem_of_app_cons_inv_r in Hle; [|done..]. unfold suffix. naive_solver.
Qed.

Lemma suffix_length_eq l1 l2 :
  l1 `suffix_of` l2 → length l2 ≤ length l1 → l1 = l2.
Proof.
  intros. apply (inj reverse), prefix_length_eq.
  - by apply suffix_prefix_reverse.
  - by rewrite !length_reverse.
Qed.

Section max_suffix.
  Context `{!EqDecision A}.

  Lemma max_suffix_fst l1 l2 :
    l1 = (max_suffix l1 l2).1.1 ++ (max_suffix l1 l2).2.
  Proof.
    rewrite <-(reverse_involutive l1) at 1.
    rewrite (max_prefix_fst (reverse l1) (reverse l2)). unfold max_suffix.
    destruct (max_prefix (reverse l1) (reverse l2)) as ((?&?)&?); simpl.
    by rewrite reverse_app.
  Qed.
  Lemma max_suffix_fst_alt l1 l2 k1 k2 k3 :
    max_suffix l1 l2 = (k1, k2, k3) → l1 = k1 ++ k3.
  Proof.
    intro. pose proof (max_suffix_fst l1 l2).
    by destruct (max_suffix l1 l2) as [[]?]; simplify_eq.
  Qed.
  Lemma max_suffix_fst_suffix l1 l2 : (max_suffix l1 l2).2 `suffix_of` l1.
  Proof. eexists. apply max_suffix_fst. Qed.
  Lemma max_suffix_fst_suffix_alt l1 l2 k1 k2 k3 :
    max_suffix l1 l2 = (k1, k2, k3) → k3 `suffix_of` l1.
  Proof. eexists. eauto using max_suffix_fst_alt. Qed.
  Lemma max_suffix_snd l1 l2 :
    l2 = (max_suffix l1 l2).1.2 ++ (max_suffix l1 l2).2.
  Proof.
    rewrite <-(reverse_involutive l2) at 1.
    rewrite (max_prefix_snd (reverse l1) (reverse l2)). unfold max_suffix.
    destruct (max_prefix (reverse l1) (reverse l2)) as ((?&?)&?); simpl.
    by rewrite reverse_app.
  Qed.
  Lemma max_suffix_snd_alt l1 l2 k1 k2 k3 :
    max_suffix l1 l2 = (k1,k2,k3) → l2 = k2 ++ k3.
  Proof.
    intro. pose proof (max_suffix_snd l1 l2).
    by destruct (max_suffix l1 l2) as [[]?]; simplify_eq.
  Qed.
  Lemma max_suffix_snd_suffix l1 l2 : (max_suffix l1 l2).2 `suffix_of` l2.
  Proof. eexists. apply max_suffix_snd. Qed.
  Lemma max_suffix_snd_suffix_alt l1 l2 k1 k2 k3 :
    max_suffix l1 l2 = (k1,k2,k3) → k3 `suffix_of` l2.
  Proof. eexists. eauto using max_suffix_snd_alt. Qed.
  Lemma max_suffix_max l1 l2 k :
    k `suffix_of` l1 → k `suffix_of` l2 → k `suffix_of` (max_suffix l1 l2).2.
  Proof.
    generalize (max_prefix_max (reverse l1) (reverse l2)).
    rewrite !suffix_prefix_reverse. unfold max_suffix.
    destruct (max_prefix (reverse l1) (reverse l2)) as ((?&?)&?); simpl.
    rewrite reverse_involutive. auto.
  Qed.
  Lemma max_suffix_max_alt l1 l2 k1 k2 k3 k :
    max_suffix l1 l2 = (k1, k2, k3) →
    k `suffix_of` l1 → k `suffix_of` l2 → k `suffix_of` k3.
  Proof.
    intro. pose proof (max_suffix_max l1 l2 k).
    by destruct (max_suffix l1 l2) as [[]?]; simplify_eq.
  Qed.
  Lemma max_suffix_max_snoc l1 l2 k1 k2 k3 x1 x2 :
    max_suffix l1 l2 = (k1 ++ [x1], k2 ++ [x2], k3) → x1 ≠ x2.
  Proof.
    intros Hl ->. destruct (suffix_cons_not x2 k3).
    eapply max_suffix_max_alt; eauto.
    - rewrite (max_suffix_fst_alt _ _ _ _ _ Hl).
      by apply (suffix_app [x2]), suffix_app_r.
    - rewrite (max_suffix_snd_alt _ _ _ _ _ Hl).
      by apply (suffix_app [x2]), suffix_app_r.
  Qed.
End max_suffix.

(** ** Properties of the [sublist] predicate *)
Lemma sublist_length l1 l2 : l1 `sublist_of` l2 → length l1 ≤ length l2.
Proof. induction 1; simpl; auto with arith. Qed.
Lemma sublist_nil_l l : [] `sublist_of` l.
Proof. induction l; try constructor; auto. Qed.
Lemma sublist_nil_r l : l `sublist_of` [] ↔ l = [].
Proof. split; [by inv 1|]. intros ->. constructor. Qed.
Lemma sublist_app l1 l2 k1 k2 :
  l1 `sublist_of` l2 → k1 `sublist_of` k2 → l1 ++ k1 `sublist_of` l2 ++ k2.
Proof. induction 1; simpl; try constructor; auto. Qed.
Lemma sublist_inserts_l k l1 l2 : l1 `sublist_of` l2 → l1 `sublist_of` k ++ l2.
Proof. induction k; try constructor; auto. Qed.
Lemma sublist_inserts_r k l1 l2 : l1 `sublist_of` l2 → l1 `sublist_of` l2 ++ k.
Proof. induction 1; simpl; try constructor; auto using sublist_nil_l. Qed.

Lemma sublist_cons_r x l k :
  l `sublist_of` x :: k ↔ l `sublist_of` k ∨ ∃ l', l = x :: l' ∧ l' `sublist_of` k.
Proof. split; [inv 1; eauto|]. intros [?|(?&->&?)]; constructor; auto. Qed.
Lemma sublist_cons_l x l k :
  x :: l `sublist_of` k ↔ ∃ k1 k2, k = k1 ++ x :: k2 ∧ l `sublist_of` k2.
Proof.
  split.
  - intros Hlk. induction k as [|y k IH]; inv Hlk.
    + eexists [], k. by repeat constructor.
    + destruct IH as (k1&k2&->&?); auto. by exists (y :: k1), k2.
  - intros (k1&k2&->&?). by apply sublist_inserts_l, sublist_skip.
Qed.

Lemma sublist_app_r l k1 k2 :
  l `sublist_of` k1 ++ k2 ↔
    ∃ l1 l2, l = l1 ++ l2 ∧ l1 `sublist_of` k1 ∧ l2 `sublist_of` k2.
Proof.
  split.
  - revert l k2. induction k1 as [|y k1 IH]; intros l k2; simpl.
    { eexists [], l. by repeat constructor. }
    rewrite sublist_cons_r. intros [?|(l' & ? &?)]; subst.
    + destruct (IH l k2) as (l1&l2&?&?&?); trivial; subst.
      exists l1, l2. auto using sublist_cons.
    + destruct (IH l' k2) as (l1&l2&?&?&?); trivial; subst.
      exists (y :: l1), l2. auto using sublist_skip.
  - intros (?&?&?&?&?); subst. auto using sublist_app.
Qed.
Lemma sublist_app_l l1 l2 k :
  l1 ++ l2 `sublist_of` k ↔
    ∃ k1 k2, k = k1 ++ k2 ∧ l1 `sublist_of` k1 ∧ l2 `sublist_of` k2.
Proof.
  split.
  - revert l2 k. induction l1 as [|x l1 IH]; intros l2 k; simpl.
    { eexists [], k. by repeat constructor. }
    rewrite sublist_cons_l. intros (k1 & k2 &?&?); subst.
    destruct (IH l2 k2) as (h1 & h2 &?&?&?); trivial; subst.
    exists (k1 ++ x :: h1), h2. rewrite <-(assoc_L (++)).
    auto using sublist_inserts_l, sublist_skip.
  - intros (?&?&?&?&?); subst. auto using sublist_app.
Qed.

Lemma sublist_app_inv_l k l1 l2 : k ++ l1 `sublist_of` k ++ l2 → l1 `sublist_of` l2.
Proof.
  induction k as [|y k IH]; simpl; [done |].
  rewrite sublist_cons_r. intros [Hl12|(?&?&?)]; [|simplify_eq; eauto].
  rewrite sublist_cons_l in Hl12. destruct Hl12 as (k1&k2&Hk&?).
  apply IH. rewrite Hk. eauto using sublist_inserts_l, sublist_cons.
Qed.
Lemma sublist_app_inv_r k l1 l2 : l1 ++ k `sublist_of` l2 ++ k → l1 `sublist_of` l2.
Proof.
  revert l1 l2. induction k as [|y k IH]; intros l1 l2.
  { by rewrite !(right_id_L [] (++)). }
  intros. opose proof* (IH (l1 ++ [_]) (l2 ++ [_])) as Hl12.
  { by rewrite <-!(assoc_L (++)). }
  rewrite sublist_app_l in Hl12. destruct Hl12 as (k1&k2&E&?&Hk2).
  destruct k2 as [|z k2] using rev_ind; [inv Hk2|].
  rewrite (assoc_L (++)) in E; simplify_list_eq.
  eauto using sublist_inserts_r.
Qed.

Lemma sublist_app_cons_r x l k1 k2 :
  l `sublist_of` k1 ++ x :: k2 ↔
    l `sublist_of` k1 ++ k2 ∨
    ∃ l1 l2, l = l1 ++ x :: l2 ∧ l1 `sublist_of` k1 ∧ l2 `sublist_of` k2.
Proof.
  split.
  - intros (l1 & l2 & -> & ? & [?|(l1'&->&?)]%sublist_cons_r)%sublist_app_r;
      by eauto 10 using sublist_app.
  - intros [(l1 & l1' & -> & ? & ?)%sublist_app_r|(l1 & l2 & -> & ? & ?)].
    + by apply sublist_app, sublist_cons.
    + by apply sublist_app, sublist_skip.
Qed.
Lemma sublist_app_cons_l x l1 l2 k :
  l1 ++ x :: l2 `sublist_of` k ↔
    ∃ k1 k2, k = k1 ++ x :: k2 ∧ l1 `sublist_of` k1 ∧ l2 `sublist_of` k2.
Proof.
  split.
  - intros (k1 & k2 & -> & ? & (k1' & k2' & -> & ?)%sublist_cons_l)%sublist_app_l.
    exists (k1 ++ k1'), k2'. rewrite !(assoc_L (++)).
    eauto using sublist_inserts_r.
  - intros (k1 & k2 & -> & ? & ?). by apply sublist_app, sublist_skip.
Qed.

Global Instance: PartialOrder (@sublist A).
Proof.
  split; [split|].
  - intros l. induction l; constructor; auto.
  - intros l1 l2 l3 Hl12. revert l3. induction Hl12.
    + auto using sublist_nil_l.
    + intros ?. rewrite sublist_cons_l. intros (?&?&?&?); subst.
      eauto using sublist_inserts_l, sublist_skip.
    + intros ?. rewrite sublist_cons_l. intros (?&?&?&?); subst.
      eauto using sublist_inserts_l, sublist_cons.
  - intros l1 l2 Hl12 Hl21. apply sublist_length in Hl21.
    induction Hl12 as [| |??? Hl12]; f_equal/=; auto with arith.
    apply sublist_length in Hl12. lia.
Qed.
Lemma sublist_take l i : take i l `sublist_of` l.
Proof. rewrite <-(take_drop i l) at 2. by apply sublist_inserts_r. Qed.
Lemma sublist_drop l i : drop i l `sublist_of` l.
Proof. rewrite <-(take_drop i l) at 2. by apply sublist_inserts_l. Qed.
Lemma sublist_delete l i : delete i l `sublist_of` l.
Proof. revert i. by induction l; intros [|?]; simpl; constructor. Qed.
Lemma sublist_foldr_delete l is : foldr delete l is `sublist_of` l.
Proof.
  induction is as [|i is IH]; simpl; [done |].
  trans (foldr delete l is); auto using sublist_delete.
Qed.
Lemma sublist_alt l1 l2 : l1 `sublist_of` l2 ↔ ∃ is, l1 = foldr delete l2 is.
Proof.
  split; [|intros [is ->]; apply sublist_foldr_delete].
  intros Hl12. cut (∀ k, ∃ is, k ++ l1 = foldr delete (k ++ l2) is).
  { intros help. apply (help []). }
  induction Hl12 as [|x l1 l2 _ IH|x l1 l2 _ IH]; intros k.
  - by eexists [].
  - destruct (IH (k ++ [x])) as [is His]. exists is.
    by rewrite <-!(assoc_L (++)) in His.
  - destruct (IH k) as [is His]. exists (is ++ [length k]).
    rewrite fold_right_app. simpl. by rewrite delete_middle.
Qed.

Lemma sublist_subseteq l1 l2 : l1 `sublist_of` l2 → l1 ⊆ l2.
Proof. intros [is ->]%sublist_alt x. apply list_elem_of_foldr_delete_inv. Qed.
Lemma elem_of_sublist l1 l2 x : x ∈ l1 → l1 `sublist_of` l2 → x ∈ l2.
Proof. intros. by eapply sublist_subseteq. Qed.

Lemma singleton_sublist_l l x :
  [x] `sublist_of` l ↔ x ∈ l.
Proof.
  split.
  - intros Hl. eapply elem_of_sublist, Hl. by apply list_elem_of_singleton.
  - intros (l1&l2&->)%list_elem_of_split.
    apply sublist_inserts_l, sublist_skip, sublist_nil_l.
Qed.
Lemma sublist_NoDup l1 l2 :
  NoDup l2 → l1 `sublist_of` l2 → NoDup l1.
Proof.
  intros Hdup. revert l1.
  induction Hdup; inv 1; try constructor; eauto using elem_of_sublist.
Qed.

Lemma sublist_filter P `{! ∀ x : A, Decision (P x)} l :
  filter P l `sublist_of` l.
Proof.
  induction l as [|x l IHl]; [done|]. rewrite filter_cons.
  destruct (decide (P x)); auto using sublist_skip, sublist_cons.
Qed.

Lemma Permutation_sublist l1 l2 l3 :
  l1 ≡ₚ l2 → l2 `sublist_of` l3 → ∃ l4, l1 `sublist_of` l4 ∧ l4 ≡ₚ l3.
Proof.
  intros Hl1l2. revert l3.
  induction Hl1l2 as [|x l1 l2 ? IH|x y l1|l1 l1' l2 ? IH1 ? IH2].
  - intros l3. by exists l3.
  - intros l3. rewrite sublist_cons_l. intros (l3'&l3''&?&?); subst.
    destruct (IH l3'') as (l4&?&Hl4); auto. exists (l3' ++ x :: l4).
    split.
    + by apply sublist_inserts_l, sublist_skip.
    + by rewrite Hl4.
  - intros l3. rewrite sublist_cons_l. intros (l3'&l3''&?& Hl3); subst.
    rewrite sublist_cons_l in Hl3. destruct Hl3 as (l5'&l5''&?& Hl5); subst.
    exists (l3' ++ y :: l5' ++ x :: l5''). split.
    + by do 2 apply sublist_inserts_l, sublist_skip.
    + by rewrite !Permutation_middle, Permutation_swap.
  - intros l3 ?. destruct (IH2 l3) as (l3'&?&?); trivial.
    destruct (IH1 l3') as (l3'' &?&?); trivial. exists l3''.
    split; [done|]. etrans; eauto.
Qed.
Lemma sublist_Permutation l1 l2 l3 :
  l1 `sublist_of` l2 → l2 ≡ₚ l3 → ∃ l4, l1 ≡ₚ l4 ∧ l4 `sublist_of` l3.
Proof.
  intros Hl1l2 Hl2l3. revert l1 Hl1l2.
  induction Hl2l3 as [|x l2 l3 ? IH|x y l2|l2 l2' l3 ? IH1 ? IH2].
  - intros l1. by exists l1.
  - intros l1. rewrite sublist_cons_r. intros [?|(l1'&l1''&?)]; subst.
    { destruct (IH l1) as (l4&?&?); trivial.
      exists l4. split.
      - done.
      - by constructor. }
    destruct (IH l1') as (l4&?&Hl4); auto. exists (x :: l4).
    split; [ by constructor | by constructor ].
  - intros l1. rewrite sublist_cons_r. intros [Hl1|(l1'&l1''&Hl1)]; subst.
    { exists l1. split; [done|]. rewrite sublist_cons_r in Hl1.
      destruct Hl1 as [?|(l1'&?&?)]; subst; by repeat constructor. }
    rewrite sublist_cons_r in Hl1. destruct Hl1 as [?|(l1''&?&?)]; subst.
    + exists (y :: l1'). by repeat constructor.
    + exists (x :: y :: l1''). by repeat constructor.
  - intros l1 ?. destruct (IH1 l1) as (l3'&?&?); trivial.
    destruct (IH2 l3') as (l3'' &?&?); trivial. exists l3''.
    split; [|done]. etrans; eauto.
Qed.

(** Properties of the [submseteq] predicate *)
Lemma submseteq_length l1 l2 : l1 ⊆+ l2 → length l1 ≤ length l2.
Proof. induction 1; simpl; auto with lia. Qed.
Lemma submseteq_nil_l l : [] ⊆+ l.
Proof. induction l; constructor; auto. Qed.
Lemma submseteq_nil_r l : l ⊆+ [] ↔ l = [].
Proof.
  split; [|intros ->; constructor].
  intros Hl. apply submseteq_length in Hl. destruct l; simpl in *; auto with lia.
Qed.
Global Instance: PreOrder (@submseteq A).
Proof.
  split.
  - intros l. induction l; constructor; auto.
  - red. apply submseteq_trans.
Qed.
Lemma Permutation_submseteq l1 l2 : l1 ≡ₚ l2 → l1 ⊆+ l2.
Proof. induction 1; econstructor; eauto. Qed.
Lemma sublist_submseteq l1 l2 : l1 `sublist_of` l2 → l1 ⊆+ l2.
Proof. induction 1; constructor; auto. Qed.
Lemma submseteq_Permutation l1 l2 : l1 ⊆+ l2 → ∃ k, l2 ≡ₚ l1 ++ k.
Proof.
  induction 1 as
    [|x y l ? [k Hk]| |x l1 l2 ? [k Hk]|l1 l2 l3 ? [k Hk] ? [k' Hk']].
  - by eexists [].
  - exists k. by rewrite Hk.
  - eexists []. rewrite (right_id_L [] (++)). by constructor.
  - exists (x :: k). by rewrite Hk, Permutation_middle.
  - exists (k ++ k'). by rewrite Hk', Hk, (assoc_L (++)).
Qed.

Global Instance: Proper ((≡ₚ) ==> (≡ₚ) ==> iff) (@submseteq A).
Proof.
  intros l1 l2 ? k1 k2 ?. split; intros.
  - trans l1; [by apply Permutation_submseteq|].
    trans k1; [done|]. by apply Permutation_submseteq.
  - trans l2; [by apply Permutation_submseteq|].
    trans k2; [done|]. by apply Permutation_submseteq.
Qed.

Lemma submseteq_length_Permutation l1 l2 :
  l1 ⊆+ l2 → length l2 ≤ length l1 → l1 ≡ₚ l2.
Proof.
  intros Hsub Hlen. destruct (submseteq_Permutation l1 l2) as [[|??] Hk]; auto.
  - by rewrite Hk, (right_id_L [] (++)).
  - rewrite Hk, length_app in Hlen. simpl in *; lia.
Qed.

Global Instance: AntiSymm (≡ₚ) (@submseteq A).
Proof.
  intros l1 l2 ??.
  apply submseteq_length_Permutation; auto using submseteq_length.
Qed.

Lemma elem_of_submseteq l k x : x ∈ l → l ⊆+ k → x ∈ k.
Proof. intros ? [l' ->]%submseteq_Permutation. apply elem_of_app; auto. Qed.
Lemma lookup_submseteq l k i x :
  l !! i = Some x →
  l ⊆+ k →
  ∃ j, k !! j = Some x.
Proof.
  intros Hsub Hlook.
  eapply list_elem_of_lookup_1, elem_of_submseteq;
    eauto using list_elem_of_lookup_2.
Qed.

Lemma submseteq_take l i : take i l ⊆+ l.
Proof. auto using sublist_take, sublist_submseteq. Qed.
Lemma submseteq_drop l i : drop i l ⊆+ l.
Proof. auto using sublist_drop, sublist_submseteq. Qed.
Lemma submseteq_delete l i : delete i l ⊆+ l.
Proof. auto using sublist_delete, sublist_submseteq. Qed.
Lemma submseteq_foldr_delete l is : foldr delete l is `sublist_of` l.
Proof. auto using sublist_foldr_delete, sublist_submseteq. Qed.
Lemma submseteq_sublist_l l1 l3 : l1 ⊆+ l3 ↔ ∃ l2, l1 `sublist_of` l2 ∧ l2 ≡ₚ l3.
Proof.
  split.
  { intros Hl13. elim Hl13; clear l1 l3 Hl13.
    - by eexists [].
    - intros x l1 l3 ? (l2&?&?). exists (x :: l2). by repeat constructor.
    - intros x y l. exists (y :: x :: l). by repeat constructor.
    - intros x l1 l3 ? (l2&?&?). exists (x :: l2). by repeat constructor.
    - intros l1 l3 l5 ? (l2&?&?) ? (l4&?&?).
      destruct (Permutation_sublist l2 l3 l4) as (l3'&?&?); trivial.
      exists l3'. split; etrans; eauto. }
  intros (l2&?&?).
  trans l2; auto using sublist_submseteq, Permutation_submseteq.
Qed.
Lemma submseteq_sublist_r l1 l3 :
  l1 ⊆+ l3 ↔ ∃ l2, l1 ≡ₚ l2 ∧ l2 `sublist_of` l3.
Proof.
  rewrite submseteq_sublist_l.
  split; intros (l2&?&?); eauto using sublist_Permutation, Permutation_sublist.
Qed.
Lemma submseteq_inserts_l k l1 l2 : l1 ⊆+ l2 → l1 ⊆+ k ++ l2.
Proof. induction k; try constructor; auto. Qed.
Lemma submseteq_inserts_r k l1 l2 : l1 ⊆+ l2 → l1 ⊆+ l2 ++ k.
Proof. rewrite (comm (++)). apply submseteq_inserts_l. Qed.
Lemma submseteq_skips_l k l1 l2 : l1 ⊆+ l2 → k ++ l1 ⊆+ k ++ l2.
Proof. induction k; try constructor; auto. Qed.
Lemma submseteq_skips_r k l1 l2 : l1 ⊆+ l2 → l1 ++ k ⊆+ l2 ++ k.
Proof. rewrite !(comm (++) _ k). apply submseteq_skips_l. Qed.
Lemma submseteq_app l1 l2 k1 k2 : l1 ⊆+ l2 → k1 ⊆+ k2 → l1 ++ k1 ⊆+ l2 ++ k2.
Proof. trans (l1 ++ k2); auto using submseteq_skips_l, submseteq_skips_r. Qed.
Lemma submseteq_cons_r x l k :
  l ⊆+ x :: k ↔ l ⊆+ k ∨ ∃ l', l ≡ₚ x :: l' ∧ l' ⊆+ k.
Proof.
  split.
  - rewrite submseteq_sublist_r. intros (l'&E&Hl').
    rewrite sublist_cons_r in Hl'. destruct Hl' as [?|(?&?&?)]; subst.
    + left. rewrite E. eauto using sublist_submseteq.
    + right. eauto using sublist_submseteq.
  - intros [?|(?&E&?)]; [|rewrite E]; by constructor.
Qed.
Lemma submseteq_cons_l x l k : x :: l ⊆+ k ↔ ∃ k', k ≡ₚ x :: k' ∧ l ⊆+ k'.
Proof.
  split.
  - rewrite submseteq_sublist_l. intros (l'&Hl'&E).
    rewrite sublist_cons_l in Hl'. destruct Hl' as (k1&k2&?&?); subst.
    exists (k1 ++ k2). split; eauto using submseteq_inserts_l, sublist_submseteq.
    by rewrite Permutation_middle.
  - intros (?&E&?). rewrite E. by constructor.
Qed.
Lemma submseteq_app_r l k1 k2 :
  l ⊆+ k1 ++ k2 ↔ ∃ l1 l2, l ≡ₚ l1 ++ l2 ∧ l1 ⊆+ k1 ∧ l2 ⊆+ k2.
Proof.
  split.
  - rewrite submseteq_sublist_r. intros (l'&E&Hl').
    rewrite sublist_app_r in Hl'. destruct Hl' as (l1&l2&?&?&?); subst.
    exists l1, l2. eauto using sublist_submseteq.
  - intros (?&?&E&?&?). rewrite E. eauto using submseteq_app.
Qed.
Lemma submseteq_app_l l1 l2 k :
  l1 ++ l2 ⊆+ k ↔ ∃ k1 k2, k ≡ₚ k1 ++ k2 ∧ l1 ⊆+ k1 ∧ l2 ⊆+ k2.
Proof.
  split.
  - rewrite submseteq_sublist_l. intros (l'&Hl'&E).
    rewrite sublist_app_l in Hl'. destruct Hl' as (k1&k2&?&?&?); subst.
    exists k1, k2. split; [done|]. eauto using sublist_submseteq.
  - intros (?&?&E&?&?). rewrite E. eauto using submseteq_app.
Qed.
Lemma submseteq_app_inv_l l1 l2 k : k ++ l1 ⊆+ k ++ l2 → l1 ⊆+ l2.
Proof.
  induction k as [|y k IH]; simpl; [done |]. rewrite submseteq_cons_l.
  intros (?&E%(inj (cons y))&?). apply IH. by rewrite E.
Qed.
Lemma submseteq_app_inv_r l1 l2 k : l1 ++ k ⊆+ l2 ++ k → l1 ⊆+ l2.
Proof. rewrite <-!(comm (++) k). apply submseteq_app_inv_l. Qed.
Lemma submseteq_cons_middle x l k1 k2 : l ⊆+ k1 ++ k2 → x :: l ⊆+ k1 ++ x :: k2.
Proof. rewrite <-Permutation_middle. by apply submseteq_skip. Qed.
Lemma submseteq_app_middle l1 l2 k1 k2 :
  l2 ⊆+ k1 ++ k2 → l1 ++ l2 ⊆+ k1 ++ l1 ++ k2.
Proof.
  rewrite !(assoc (++)), (comm (++) k1 l1), <-(assoc_L (++)).
  by apply submseteq_skips_l.
Qed.
Lemma submseteq_middle l k1 k2 : l ⊆+ k1 ++ l ++ k2.
Proof. by apply submseteq_inserts_l, submseteq_inserts_r. Qed.

Lemma NoDup_submseteq l k : NoDup l → (∀ x, x ∈ l → x ∈ k) → l ⊆+ k.
Proof.
  intros Hl. revert k. induction Hl as [|x l Hx ? IH].
  { intros k Hk. by apply submseteq_nil_l. }
  intros k Hlk. destruct (list_elem_of_split k x) as (l1&l2&?); subst.
  { apply Hlk. by constructor. }
  rewrite <-Permutation_middle. apply submseteq_skip, IH.
  intros y Hy. rewrite elem_of_app.
  specialize (Hlk y). rewrite elem_of_app, !elem_of_cons in Hlk.
  by destruct Hlk as [?|[?|?]]; subst; eauto.
Qed.
Lemma NoDup_Permutation l k : NoDup l → NoDup k → (∀ x, x ∈ l ↔ x ∈ k) → l ≡ₚ k.
Proof.
  intros. apply (anti_symm submseteq); apply NoDup_submseteq; naive_solver.
Qed.

Lemma submseteq_insert l1 l2 i j x y :
  l1 !! i = Some x →
  l2 !! j = Some x →
  l1 ⊆+ l2 →
  (<[i := y]> l1) ⊆+ (<[j := y]> l2).
Proof.
  intros ?? Hsub.
  rewrite !insert_take_drop,
    <-!Permutation_middle by eauto using lookup_lt_Some.
  rewrite <-(take_drop_middle l1 i x), <-(take_drop_middle l2 j x),
    <-!Permutation_middle in Hsub by done.
  by apply submseteq_skip, (submseteq_app_inv_l _ _ [x]).
Qed.

Lemma singleton_submseteq_l l x :
  [x] ⊆+ l ↔ x ∈ l.
Proof.
  split.
  - intros Hsub. eapply elem_of_submseteq; [|done].
    apply list_elem_of_singleton. done.
  - intros (l1&l2&->)%list_elem_of_split.
    apply submseteq_cons_middle, submseteq_nil_l.
Qed.
Lemma singleton_submseteq x y :
  [x] ⊆+ [y] ↔ x = y.
Proof. rewrite singleton_submseteq_l. apply list_elem_of_singleton. Qed.

Section submseteq_dec.
  Context `{!EqDecision A}.

  Local Program Fixpoint elem_of_or_Permutation x l :
      (x ∉ l) + { k | l ≡ₚ x :: k } :=
    match l with
    | [] => inl _
    | y :: l =>
       if decide (x = y) then inr (l ↾ _) else
       match elem_of_or_Permutation x l return _ with
       | inl _ => inl _ | inr (k ↾ _) => inr ((y :: k) ↾ _)
       end
    end.
  Next Obligation. inv 2. Qed.
  Next Obligation. naive_solver. Qed.
  Next Obligation. intros ? x y l <- ??. by rewrite not_elem_of_cons. Qed.
  Next Obligation.
    intros ? x y l <- ? _ k Hl. simpl. by rewrite Hl, Permutation_swap.
  Qed.

  Global Program Instance submseteq_dec : RelDecision (@submseteq A) :=
    fix go l1 l2 :=
    match l1 with
    | [] => left _
    | x :: l1 =>
       match elem_of_or_Permutation x l2 return _ with
       | inl _ => right _
       | inr (l2 ↾ _) => cast_if (go l1 l2)
       end
    end.
  Next Obligation. intros _ l1 l2 _. apply submseteq_nil_l. Qed.
  Next Obligation.
    intros _ ? l2 x l1 <- Hx Hxl1. eapply Hx, elem_of_submseteq, Hxl1. by left.
  Qed.
  Next Obligation. intros _ ?? x l1 <- _ l2 -> Hl. by apply submseteq_skip. Qed.
  Next Obligation.
    intros _ ?? x l1 <- _ l2 -> Hl (l2' & Hl2%(inj _) & ?)%submseteq_cons_l.
    apply Hl. by rewrite Hl2.
  Qed.

  Global Instance Permutation_dec : RelDecision (≡ₚ@{A}).
  Proof using Type*.
    refine (λ l1 l2, cast_if_and
      (decide (l1 ⊆+ l2)) (decide (length l2 ≤ length l1)));
      [by apply submseteq_length_Permutation
      |abstract (intros He; by rewrite He in *)..].
  Defined.
End submseteq_dec.


(** ** Properties of the [Forall] and [Exists] predicate *)
Lemma Forall_Exists_dec (P Q : A → Prop) (dec : ∀ x, {P x} + {Q x}) :
  ∀ l, {Forall P l} + {Exists Q l}.
Proof.
 refine (
  fix go l :=
  match l return {Forall P l} + {Exists Q l} with
  | [] => left _
  | x :: l => cast_if_and (dec x) (go l)
  end); clear go; intuition.
Defined.

(** Export the Coq stdlib constructors under different names,
because we use [Forall_nil] and [Forall_cons] for a version with a biimplication. *)
Definition Forall_nil_2 := @Forall_nil A.
Definition Forall_cons_2 := @Forall_cons A.
Global Instance Forall_proper:
  Proper (pointwise_relation _ (↔) ==> (=) ==> (↔)) (@Forall A).
Proof. split; subst; induction 1; constructor; by firstorder auto. Qed.
Global Instance Exists_proper:
  Proper (pointwise_relation _ (↔) ==> (=) ==> (↔)) (@Exists A).
Proof. split; subst; induction 1; constructor; by firstorder auto. Qed.

Section Forall_Exists.
  Context (P : A → Prop).

  Lemma Forall_forall l : Forall P l ↔ ∀ x, x ∈ l → P x.
  Proof.
    split; [induction 1; inv 1; auto|].
    intros Hin; induction l as [|x l IH]; constructor; [apply Hin; constructor|].
    apply IH. intros ??. apply Hin. by constructor.
  Qed.
  Lemma Forall_nil : Forall P [] ↔ True.
  Proof. done. Qed.
  Lemma Forall_cons_1 x l : Forall P (x :: l) → P x ∧ Forall P l.
  Proof. by inv 1. Qed.
  Lemma Forall_cons x l : Forall P (x :: l) ↔ P x ∧ Forall P l.
  Proof. split; [by inv 1|]. intros [??]. by constructor. Qed.
  Lemma Forall_singleton x : Forall P [x] ↔ P x.
  Proof. rewrite Forall_cons, Forall_nil; tauto. Qed.
  Lemma Forall_app_2 l1 l2 : Forall P l1 → Forall P l2 → Forall P (l1 ++ l2).
  Proof. induction 1; simpl; auto. Qed.
  Lemma Forall_app l1 l2 : Forall P (l1 ++ l2) ↔ Forall P l1 ∧ Forall P l2.
  Proof.
    split; [induction l1; inv 1; naive_solver|].
    intros [??]; auto using Forall_app_2.
  Qed.
  Lemma Forall_true l : (∀ x, P x) → Forall P l.
  Proof. intros ?. induction l; auto. Defined.
  Lemma Forall_impl (Q : A → Prop) l :
    Forall P l → (∀ x, P x → Q x) → Forall Q l.
  Proof. intros H ?. induction H; auto. Defined.
  Lemma Forall_iff l (Q : A → Prop) :
    (∀ x, P x ↔ Q x) → Forall P l ↔ Forall Q l.
  Proof. intros H. apply Forall_proper. { red; apply H. } done. Qed.
  Lemma Forall_not l : length l ≠ 0 → Forall (not ∘ P) l → ¬Forall P l.
  Proof. by destruct 2; inv 1. Qed.
  Lemma Forall_and {Q} l : Forall (λ x, P x ∧ Q x) l ↔ Forall P l ∧ Forall Q l.
  Proof.
    split; [induction 1; constructor; naive_solver|].
    intros [Hl Hl']; revert Hl'; induction Hl; inv 1; auto.
  Qed.
  Lemma Forall_and_l {Q} l : Forall (λ x, P x ∧ Q x) l → Forall P l.
  Proof. rewrite Forall_and; tauto. Qed.
  Lemma Forall_and_r {Q} l : Forall (λ x, P x ∧ Q x) l → Forall Q l.
  Proof. rewrite Forall_and; tauto. Qed.
  Lemma Forall_delete l i : Forall P l → Forall P (delete i l).
  Proof. intros H. revert i. by induction H; intros [|i]; try constructor. Qed.

  Lemma Forall_lookup l : Forall P l ↔ ∀ i x, l !! i = Some x → P x.
  Proof.
    rewrite Forall_forall. setoid_rewrite list_elem_of_lookup. naive_solver.
  Qed.
  Lemma Forall_lookup_total `{!Inhabited A} l :
    Forall P l ↔ ∀ i, i < length l → P (l !!! i).
  Proof. rewrite Forall_lookup. setoid_rewrite list_lookup_alt. naive_solver. Qed.
  Lemma Forall_lookup_1 l i x : Forall P l → l !! i = Some x → P x.
  Proof. rewrite Forall_lookup. eauto. Qed.
  Lemma Forall_lookup_total_1 `{!Inhabited A} l i :
    Forall P l → i < length l → P (l !!! i).
  Proof. rewrite Forall_lookup_total. eauto. Qed.
  Lemma Forall_lookup_2 l : (∀ i x, l !! i = Some x → P x) → Forall P l.
  Proof. by rewrite Forall_lookup. Qed.
  Lemma Forall_lookup_total_2 `{!Inhabited A} l :
    (∀ i, i < length l → P (l !!! i)) → Forall P l.
  Proof. by rewrite Forall_lookup_total. Qed.
  Lemma Forall_nth d l : Forall P l ↔ ∀ i, i < length l → P (nth i l d).
  Proof.
    rewrite Forall_lookup. split.
    - intros Hl ? [x Hl']%lookup_lt_is_Some_2.
      rewrite (nth_lookup_Some _ _ _ _ Hl'). by eapply Hl.
    - intros Hl i x Hl'. specialize (Hl _ (lookup_lt_Some _ _ _ Hl')).
      by rewrite (nth_lookup_Some _ _ _ _ Hl') in Hl.
  Qed.

  Lemma Forall_reverse l : Forall P (reverse l) ↔ Forall P l.
  Proof.
    induction l as [|x l IH]; simpl; [done|].
    rewrite reverse_cons, Forall_cons, Forall_app, Forall_singleton. naive_solver.
  Qed.
  Lemma Forall_tail l : Forall P l → Forall P (tail l).
  Proof. destruct 1; simpl; auto. Qed.
  Lemma Forall_alter f l i :
    Forall P l → (∀ x, l !! i = Some x → P x → P (f x)) → Forall P (alter f i l).
  Proof.
    intros Hl. revert i. induction Hl; simpl; intros [|i]; constructor; auto.
  Qed.
  Lemma Forall_alter_inv f l i :
    Forall P (alter f i l) → (∀ x, l !! i = Some x → P (f x) → P x) → Forall P l.
  Proof.
    revert i. induction l; intros [|?]; simpl;
      inv 1; constructor; eauto.
  Qed.
  Lemma Forall_insert l i x : Forall P l → P x → Forall P (<[i:=x]>l).
  Proof. rewrite list_insert_alter; auto using Forall_alter. Qed.
  Lemma Forall_inserts l i k :
    Forall P l → Forall P k → Forall P (list_inserts i k l).
  Proof.
    intros Hl Hk; revert i.
    induction Hk; simpl; auto using Forall_insert.
  Qed.
  Lemma Forall_replicate n x : P x → Forall P (replicate n x).
  Proof. induction n; simpl; constructor; auto. Qed.
  Lemma Forall_replicate_eq n (x : A) : Forall (x =.) (replicate n x).
  Proof using -(P). induction n; simpl; constructor; auto. Qed.
  Lemma Forall_take n l : Forall P l → Forall P (take n l).
  Proof. intros Hl. revert n. induction Hl; intros [|?]; simpl; auto. Qed.
  Lemma Forall_drop n l : Forall P l → Forall P (drop n l).
  Proof. intros Hl. revert n. induction Hl; intros [|?]; simpl; auto. Qed.
  Lemma Forall_rev_ind (Q : list A → Prop) :
    Q [] → (∀ x l, P x → Forall P l → Q l → Q (l ++ [x])) →
    ∀ l, Forall P l → Q l.
  Proof.
    intros ?? l. induction l using rev_ind; auto.
    rewrite Forall_app, Forall_singleton; intros [??]; auto.
  Qed.

  Lemma Exists_exists l : Exists P l ↔ ∃ x, x ∈ l ∧ P x.
  Proof.
    split.
    - induction 1 as [x|y ?? [x [??]]]; exists x; by repeat constructor.
    - intros [x [Hin ?]]. induction l; [by destruct (not_elem_of_nil x)|].
      inv Hin; subst; [left|right]; auto.
  Qed.
  Lemma Exists_inv x l : Exists P (x :: l) → P x ∨ Exists P l.
  Proof. inv 1; intuition trivial. Qed.
  Lemma Exists_app l1 l2 : Exists P (l1 ++ l2) ↔ Exists P l1 ∨ Exists P l2.
  Proof.
    split.
    - induction l1; inv 1; naive_solver.
    - intros [H|H]; [induction H | induction l1]; simpl; intuition.
  Qed.
  Lemma Exists_impl (Q : A → Prop) l :
    Exists P l → (∀ x, P x → Q x) → Exists Q l.
  Proof. intros H ?. induction H; auto. Defined.

  Lemma Exists_not_Forall l : Exists (not ∘ P) l → ¬Forall P l.
  Proof. induction 1; inv 1; contradiction. Qed.
  Lemma Forall_not_Exists l : Forall (not ∘ P) l → ¬Exists P l.
  Proof. induction 1; inv 1; contradiction. Qed.

  Lemma Forall_list_difference `{!EqDecision A} l k :
    Forall P l → Forall P (list_difference l k).
  Proof.
    rewrite !Forall_forall.
    intros ? x; rewrite list_elem_of_difference; naive_solver.
  Qed.
  Lemma Forall_list_union `{!EqDecision A} l k :
    Forall P l → Forall P k → Forall P (list_union l k).
  Proof. intros. apply Forall_app; auto using Forall_list_difference. Qed.
  Lemma Forall_list_intersection `{!EqDecision A} l k :
    Forall P l → Forall P (list_intersection l k).
  Proof.
    rewrite !Forall_forall.
    intros ? x; rewrite list_elem_of_intersection; naive_solver.
  Qed.

  Context {dec : ∀ x, Decision (P x)}.
  Lemma not_Forall_Exists l : ¬Forall P l → Exists (not ∘ P) l.
  Proof using Type*. intro. by destruct (Forall_Exists_dec P (not ∘ P) dec l). Qed.
  Lemma not_Exists_Forall l : ¬Exists P l → Forall (not ∘ P) l.
  Proof using Type*.
    by destruct (Forall_Exists_dec (not ∘ P) P
        (λ x : A, swap_if (decide (P x))) l).
  Qed.
  Global Instance Forall_dec l : Decision (Forall P l) :=
    match Forall_Exists_dec P (not ∘ P) dec l with
    | left H => left H
    | right H => right (Exists_not_Forall _ H)
    end.
  Global Instance Exists_dec l : Decision (Exists P l) :=
    match Forall_Exists_dec (not ∘ P) P (λ x, swap_if (decide (P x))) l with
    | left H => right (Forall_not_Exists _ H)
    | right H => left H
    end.
End Forall_Exists.

Global Instance Forall_Permutation :
  Proper (pointwise_relation _ (↔) ==> (≡ₚ) ==> (↔)) (@Forall A).
Proof.
  intros P1 P2 HP l1 l2 Hl. rewrite !Forall_forall.
  apply forall_proper; intros x. by rewrite Hl, (HP x).
Qed.
Global Instance Exists_Permutation :
  Proper (pointwise_relation _ (↔) ==> (≡ₚ) ==> (↔)) (@Exists A).
Proof.
  intros P1 P2 HP l1 l2 Hl. rewrite !Exists_exists.
  f_equiv; intros x. by rewrite Hl, (HP x).
Qed.

Lemma head_filter_Some P `{!∀ x : A, Decision (P x)} l x :
  head (filter P l) = Some x →
  ∃ l1 l2, l = l1 ++ x :: l2 ∧ Forall (λ z, ¬P z) l1.
Proof.
  intros Hl. induction l as [|x' l IH]; [done|].
  rewrite filter_cons in Hl. case_decide; simplify_eq/=.
  - exists [], l. repeat constructor.
  - destruct IH as (l1&l2&->&?); [done|].
    exists (x' :: l1), l2. by repeat constructor.
Qed.
Lemma last_filter_Some P `{!∀ x : A, Decision (P x)} l x :
  last (filter P l) = Some x →
  ∃ l1 l2, l = l1 ++ x :: l2 ∧ Forall (λ z, ¬P z) l2.
Proof.
  rewrite <-(reverse_involutive (filter P l)), last_reverse, <-filter_reverse.
  intros (l1&l2&Heq&Hl)%head_filter_Some.
  exists (reverse l2), (reverse l1).
  rewrite <-(reverse_involutive l), Heq, reverse_app, reverse_cons, <-(assoc_L (++)).
  split; [done|by apply Forall_reverse].
Qed.

Lemma list_exist_dec P l :
  (∀ x, Decision (P x)) → Decision (∃ x, x ∈ l ∧ P x).
Proof.
  refine (λ _, cast_if (decide (Exists P l))); by rewrite <-Exists_exists.
Defined.
Lemma list_forall_dec P l :
  (∀ x, Decision (P x)) → Decision (∀ x, x ∈ l → P x).
Proof.
  refine (λ _, cast_if (decide (Forall P l))); by rewrite <-Forall_forall.
Defined.

Lemma forallb_True (f : A → bool) xs : forallb f xs ↔ Forall f xs.
Proof.
  split.
  - induction xs; naive_solver.
  - induction 1; naive_solver.
Qed.
Lemma existb_True (f : A → bool) xs : existsb f xs ↔ Exists f xs.
Proof.
  split.
  - induction xs; naive_solver.
  - induction 1; naive_solver.
Qed.

Lemma replicate_as_Forall (x : A) n l :
  replicate n x = l ↔ length l = n ∧ Forall (x =.) l.
Proof. rewrite replicate_as_elem_of, Forall_forall. naive_solver. Qed.
Lemma replicate_as_Forall_2 (x : A) n l :
  length l = n → Forall (x =.) l → replicate n x = l.
Proof. by rewrite replicate_as_Forall. Qed.
End general_properties.

Lemma Forall_swap {A B} (Q : A → B → Prop) l1 l2 :
  Forall (λ y, Forall (Q y) l1) l2 ↔ Forall (λ x, Forall (flip Q x) l2) l1.
Proof. repeat setoid_rewrite Forall_forall. simpl. split; eauto. Qed.

(** ** Properties of the [Forall2] predicate *)
Lemma Forall_Forall2_diag {A} (Q : A → A → Prop) l :
  Forall (λ x, Q x x) l → Forall2 Q l l.
Proof. induction 1; constructor; auto. Qed.

Lemma Forall2_forall `{Inhabited A} B C (Q : A → B → C → Prop) l k :
  Forall2 (λ x y, ∀ z, Q z x y) l k ↔ ∀ z, Forall2 (Q z) l k.
Proof.
  split; [induction 1; constructor; auto|].
  intros Hlk. induction (Hlk inhabitant) as [|x y l k _ _ IH]; constructor.
  - intros z. by oinv Hlk.
  - apply IH. intros z. by oinv Hlk.
Qed.

Lemma Forall2_same_length {A B} (l : list A) (k : list B) :
  Forall2 (λ _ _, True) l k ↔ length l = length k.
Proof.
  split; [by induction 1; f_equal/=|].
  revert k. induction l; intros [|??] ?; simplify_eq/=; auto.
Qed.

Lemma Forall2_Forall {A} P (l1 l2 : list A) :
  Forall2 P l1 l2 → Forall (uncurry P) (zip l1 l2).
Proof. induction 1; constructor; auto. Qed.

(** Export the Coq stdlib constructors under a different name,
because we use [Forall2_nil] and [Forall2_cons] for a version with a biimplication. *)
Definition Forall2_nil_2 := @Forall2_nil.
Definition Forall2_cons_2 := @Forall2_cons.
Section Forall2.
  Context {A B} (P : A → B → Prop).
  Implicit Types x : A.
  Implicit Types y : B.
  Implicit Types l : list A.
  Implicit Types k : list B.

  Lemma Forall2_length l k : Forall2 P l k → length l = length k.
  Proof. by induction 1; f_equal/=. Qed.
  Lemma Forall2_length_l l k n : Forall2 P l k → length l = n → length k = n.
  Proof. intros ? <-; symmetry. by apply Forall2_length. Qed.
  Lemma Forall2_length_r l k n : Forall2 P l k → length k = n → length l = n.
  Proof. intros ? <-. by apply Forall2_length. Qed.

  Lemma Forall2_true l k : (∀ x y, P x y) → length l = length k → Forall2 P l k.
  Proof. rewrite <-Forall2_same_length. induction 2; naive_solver. Qed.
  Lemma Forall2_flip l k : Forall2 (flip P) k l ↔ Forall2 P l k.
  Proof. split; induction 1; constructor; auto. Qed.
  Lemma Forall2_transitive {C} (Q : B → C → Prop) (R : A → C → Prop) l k lC :
    (∀ x y z, P x y → Q y z → R x z) →
    Forall2 P l k → Forall2 Q k lC → Forall2 R l lC.
  Proof. intros ? Hl. revert lC. induction Hl; inv 1; eauto. Qed.
  Lemma Forall2_impl (Q : A → B → Prop) l k :
    Forall2 P l k → (∀ x y, P x y → Q x y) → Forall2 Q l k.
  Proof. intros H ?. induction H; auto. Defined.
  Lemma Forall2_unique l k1 k2 :
    Forall2 P l k1 → Forall2 P l k2 →
    (∀ x y1 y2, P x y1 → P x y2 → y1 = y2) → k1 = k2.
  Proof.
    intros H. revert k2. induction H; inv 1; intros; f_equal; eauto.
  Qed.

  Lemma Forall_Forall2_l l k :
    length l = length k → Forall (λ x, ∀ y, P x y) l → Forall2 P l k.
  Proof. rewrite <-Forall2_same_length. induction 1; inv 1; auto. Qed.
  Lemma Forall_Forall2_r l k :
    length l = length k → Forall (λ y, ∀ x, P x y) k → Forall2 P l k.
  Proof. rewrite <-Forall2_same_length. induction 1; inv 1; auto. Qed.

  Lemma Forall2_Forall_l (Q : A → Prop) l k :
    Forall2 P l k → Forall (λ y, ∀ x, P x y → Q x) k → Forall Q l.
  Proof. induction 1; inv 1; eauto. Qed.
  Lemma Forall2_Forall_r (Q : B → Prop) l k :
    Forall2 P l k → Forall (λ x, ∀ y, P x y → Q y) l → Forall Q k.
  Proof. induction 1; inv 1; eauto. Qed.

  Lemma Forall2_nil_inv_l k : Forall2 P [] k → k = [].
  Proof. by inv 1. Qed.
  Lemma Forall2_nil_inv_r l : Forall2 P l [] → l = [].
  Proof. by inv 1. Qed.
  Lemma Forall2_nil : Forall2 P [] [] ↔ True.
  Proof. done. Qed.

  Lemma Forall2_cons_1 x l y k :
    Forall2 P (x :: l) (y :: k) → P x y ∧ Forall2 P l k.
  Proof. by inv 1. Qed.
  Lemma Forall2_cons_inv_l x l k :
    Forall2 P (x :: l) k → ∃ y k', P x y ∧ Forall2 P l k' ∧ k = y :: k'.
  Proof. inv 1; eauto. Qed.
  Lemma Forall2_cons_inv_r l k y :
    Forall2 P l (y :: k) → ∃ x l', P x y ∧ Forall2 P l' k ∧ l = x :: l'.
  Proof. inv 1; eauto. Qed.
  Lemma Forall2_cons_nil_inv x l : Forall2 P (x :: l) [] → False.
  Proof. by inv 1. Qed.
  Lemma Forall2_nil_cons_inv y k : Forall2 P [] (y :: k) → False.
  Proof. by inv 1. Qed.

  Lemma Forall2_cons x l y k :
    Forall2 P (x :: l) (y :: k) ↔ P x y ∧ Forall2 P l k.
  Proof.
    split; [by apply Forall2_cons_1|]. intros []. by apply Forall2_cons_2.
  Qed.

  Lemma Forall2_app_l l1 l2 k :
    Forall2 P l1 (take (length l1) k) → Forall2 P l2 (drop (length l1) k) →
    Forall2 P (l1 ++ l2) k.
  Proof. intros. rewrite <-(take_drop (length l1) k). by apply Forall2_app. Qed.
  Lemma Forall2_app_r l k1 k2 :
    Forall2 P (take (length k1) l) k1 → Forall2 P (drop (length k1) l) k2 →
    Forall2 P l (k1 ++ k2).
  Proof. intros. rewrite <-(take_drop (length k1) l). by apply Forall2_app. Qed.
  Lemma Forall2_app_inv l1 l2 k1 k2 :
    length l1 = length k1 →
    Forall2 P (l1 ++ l2) (k1 ++ k2) → Forall2 P l1 k1 ∧ Forall2 P l2 k2.
  Proof.
    rewrite <-Forall2_same_length. induction 1; inv 1; naive_solver.
  Qed.
  Lemma Forall2_app_inv_l l1 l2 k :
    Forall2 P (l1 ++ l2) k ↔
      ∃ k1 k2, Forall2 P l1 k1 ∧ Forall2 P l2 k2 ∧ k = k1 ++ k2.
  Proof.
    split; [|intros (?&?&?&?&->); by apply Forall2_app].
    revert k. induction l1; inv 1; naive_solver.
  Qed.
  Lemma Forall2_app_inv_r l k1 k2 :
    Forall2 P l (k1 ++ k2) ↔
      ∃ l1 l2, Forall2 P l1 k1 ∧ Forall2 P l2 k2 ∧ l = l1 ++ l2.
  Proof.
    split; [|intros (?&?&?&?&->); by apply Forall2_app].
    revert l. induction k1; inv 1; naive_solver.
  Qed.

  Lemma Forall2_tail l k : Forall2 P l k → Forall2 P (tail l) (tail k).
  Proof. destruct 1; simpl; auto. Qed.
  Lemma Forall2_take l k n : Forall2 P l k → Forall2 P (take n l) (take n k).
  Proof. intros Hl. revert n. induction Hl; intros [|?]; simpl; auto. Qed.
  Lemma Forall2_drop l k n : Forall2 P l k → Forall2 P (drop n l) (drop n k).
  Proof. intros Hl. revert n. induction Hl; intros [|?]; simpl; auto. Qed.

  Lemma Forall2_lookup l k :
    Forall2 P l k ↔ ∀ i, option_Forall2 P (l !! i) (k !! i).
  Proof.
    split; [induction 1; intros [|?]; simpl; try constructor; eauto|].
    revert k. induction l as [|x l IH]; intros [| y k] H.
    - done.
    - oinv (H 0).
    - oinv (H 0).
    - constructor; [by oinv (H 0)|]. apply (IH _ $ λ i, H (S i)).
  Qed.
  Lemma Forall2_lookup_lr l k i x y :
    Forall2 P l k → l !! i = Some x → k !! i = Some y → P x y.
  Proof. rewrite Forall2_lookup; intros H; destruct (H i); naive_solver. Qed.
  Lemma Forall2_lookup_l l k i x :
    Forall2 P l k → l !! i = Some x → ∃ y, k !! i = Some y ∧ P x y.
  Proof. rewrite Forall2_lookup; intros H; destruct (H i); naive_solver. Qed.
  Lemma Forall2_lookup_r l k i y :
    Forall2 P l k → k !! i = Some y → ∃ x, l !! i = Some x ∧ P x y.
  Proof. rewrite Forall2_lookup; intros H; destruct (H i); naive_solver. Qed.
  Lemma Forall2_same_length_lookup_2 l k :
    length l = length k →
    (∀ i x y, l !! i = Some x → k !! i = Some y → P x y) → Forall2 P l k.
  Proof.
    rewrite <-Forall2_same_length. intros Hl Hlookup.
    induction Hl as [|?????? IH]; constructor; [by apply (Hlookup 0)|].
    apply IH. apply (λ i, Hlookup (S i)).
  Qed.
  Lemma Forall2_same_length_lookup l k :
    Forall2 P l k ↔
      length l = length k ∧
      (∀ i x y, l !! i = Some x → k !! i = Some y → P x y).
  Proof.
    naive_solver eauto using Forall2_length,
      Forall2_lookup_lr, Forall2_same_length_lookup_2.
  Qed.

  Lemma Forall2_alter_l f l k i :
    Forall2 P l k →
    (∀ x y, l !! i = Some x → k !! i = Some y → P x y → P (f x) y) →
    Forall2 P (alter f i l) k.
  Proof. intros Hl. revert i. induction Hl; intros [|]; constructor; auto. Qed.
  Lemma Forall2_alter_r f l k i :
    Forall2 P l k →
    (∀ x y, l !! i = Some x → k !! i = Some y → P x y → P x (f y)) →
    Forall2 P l (alter f i k).
  Proof. intros Hl. revert i. induction Hl; intros [|]; constructor; auto. Qed.
  Lemma Forall2_alter f g l k i :
    Forall2 P l k →
    (∀ x y, l !! i = Some x → k !! i = Some y → P x y → P (f x) (g y)) →
    Forall2 P (alter f i l) (alter g i k).
  Proof. intros Hl. revert i. induction Hl; intros [|]; constructor; auto. Qed.

  Lemma Forall2_insert l k x y i :
    Forall2 P l k → P x y → Forall2 P (<[i:=x]> l) (<[i:=y]> k).
  Proof. intros Hl. revert i. induction Hl; intros [|]; constructor; auto. Qed.
  Lemma Forall2_inserts l k l' k' i :
    Forall2 P l k → Forall2 P l' k' →
    Forall2 P (list_inserts i l' l) (list_inserts i k' k).
  Proof. intros ? H. revert i. induction H; eauto using Forall2_insert. Qed.

  Lemma Forall2_delete l k i :
    Forall2 P l k → Forall2 P (delete i l) (delete i k).
  Proof. intros Hl. revert i. induction Hl; intros [|]; simpl; intuition. Qed.
  Lemma Forall2_option_list mx my :
    option_Forall2 P mx my → Forall2 P (option_list mx) (option_list my).
  Proof. destruct 1; by constructor. Qed.

  Lemma Forall2_filter Q1 Q2 `{∀ x, Decision (Q1 x), ∀ y, Decision (Q2 y)} l k:
    (∀ x y, P x y → Q1 x ↔ Q2 y) →
    Forall2 P l k → Forall2 P (filter Q1 l) (filter Q2 k).
  Proof.
    intros HP; induction 1 as [|x y l k]; unfold filter; simpl; auto.
    simplify_option_eq by (by rewrite <-(HP x y)); repeat constructor; auto.
  Qed.

  Lemma Forall2_replicate_l k n x :
    length k = n → Forall (P x) k → Forall2 P (replicate n x) k.
  Proof. intros <-. induction 1; simpl; auto. Qed.
  Lemma Forall2_replicate_r l n y :
    length l = n → Forall (flip P y) l → Forall2 P l (replicate n y).
  Proof. intros <-. induction 1; simpl; auto. Qed.
  Lemma Forall2_replicate n x y :
    P x y → Forall2 P (replicate n x) (replicate n y).
  Proof. induction n; simpl; constructor; auto. Qed.

  Lemma Forall2_reverse l k : Forall2 P l k → Forall2 P (reverse l) (reverse k).
  Proof.
    induction 1; rewrite ?reverse_nil, ?reverse_cons; eauto using Forall2_app.
  Qed.
  Lemma Forall2_last l k : Forall2 P l k → option_Forall2 P (last l) (last k).
  Proof. induction 1 as [|????? []]; simpl; repeat constructor; auto. Qed.

  Global Instance Forall2_dec `{dec : ∀ x y, Decision (P x y)} :
    RelDecision (Forall2 P).
  Proof.
   refine (
    fix go l k : Decision (Forall2 P l k) :=
    match l, k with
    | [], [] => left _
    | x :: l, y :: k => cast_if_and (decide (P x y)) (go l k)
    | _, _ => right _
    end); clear dec go; abstract first [by constructor | by inv 1].
  Defined.
End Forall2.

Lemma Forall_exists_Forall2_l {A B} (R : A → B → Prop) (l : list A) :
  Forall (λ x, ∃ y, R x y) l ↔ ∃ k, Forall2 R l k.
Proof.
  split.
  - induction 1; naive_solver.
  - intros [k HRlk]. induction HRlk; eauto.
Qed.
Lemma Forall_exists_Forall2_r {A B} (R : A → B → Prop) (k : list B) :
  Forall (λ y, ∃ x, R x y) k ↔ ∃ l, Forall2 R l k.
Proof. setoid_rewrite Forall2_flip. apply Forall_exists_Forall2_l. Qed.

Section Forall2_proper.
  Context  {A} (R : relation A).

  Global Instance: Reflexive R → Reflexive (Forall2 R).
  Proof. intros ? l. induction l; by constructor. Qed.
  Global Instance: Symmetric R → Symmetric (Forall2 R).
  Proof. intros. induction 1; constructor; auto. Qed.
  Global Instance: Transitive R → Transitive (Forall2 R).
  Proof. intros ????. apply Forall2_transitive. by apply @transitivity. Qed.
  Global Instance: Equivalence R → Equivalence (Forall2 R).
  Proof. split; apply _. Qed.
  Global Instance: PreOrder R → PreOrder (Forall2 R).
  Proof. split; apply _. Qed.
  Global Instance: AntiSymm (=) R → AntiSymm (=) (Forall2 R).
  Proof. induction 2; inv 1; f_equal; auto. Qed.

  Global Instance: Proper (R ==> Forall2 R ==> Forall2 R) (::).
  Proof. by constructor. Qed.
  Global Instance: Proper (Forall2 R ==> Forall2 R ==> Forall2 R) (++).
  Proof. repeat intro. by apply Forall2_app. Qed.
  Global Instance: Proper (Forall2 R ==> (=)) length.
  Proof. repeat intro. eauto using Forall2_length. Qed.
  Global Instance: Proper (Forall2 R ==> Forall2 R) tail.
  Proof. repeat intro. eauto using Forall2_tail. Qed.
  Global Instance: ∀ n, Proper (Forall2 R ==> Forall2 R) (take n).
  Proof. repeat intro. eauto using Forall2_take. Qed.
  Global Instance: ∀ n, Proper (Forall2 R ==> Forall2 R) (drop n).
  Proof. repeat intro. eauto using Forall2_drop. Qed.

  Global Instance: ∀ i, Proper (Forall2 R ==> option_Forall2 R) (lookup i).
  Proof. repeat intro. by apply Forall2_lookup. Qed.
  Global Instance:
    Proper ((R ==> R) ==> (=) ==> Forall2 R ==> Forall2 R) (alter (M:=list A)).
  Proof. repeat intro. subst. eauto using Forall2_alter. Qed.
  Global Instance: ∀ i, Proper (R ==> Forall2 R ==> Forall2 R) (insert i).
  Proof. repeat intro. eauto using Forall2_insert. Qed.
  Global Instance: ∀ i,
    Proper (Forall2 R ==> Forall2 R ==> Forall2 R) (list_inserts i).
  Proof. repeat intro. eauto using Forall2_inserts. Qed.
  Global Instance: ∀ i, Proper (Forall2 R ==> Forall2 R) (delete i).
  Proof. repeat intro. eauto using Forall2_delete. Qed.

  Global Instance: Proper (option_Forall2 R ==> Forall2 R) option_list.
  Proof. repeat intro. eauto using Forall2_option_list. Qed.
  Global Instance: ∀ P `{∀ x, Decision (P x)},
    Proper (R ==> iff) P → Proper (Forall2 R ==> Forall2 R) (filter P).
  Proof. repeat intro; eauto using Forall2_filter. Qed.

  Global Instance: ∀ n, Proper (R ==> Forall2 R) (replicate n).
  Proof. repeat intro. eauto using Forall2_replicate. Qed.
  Global Instance: Proper (Forall2 R ==> Forall2 R) reverse.
  Proof. repeat intro. eauto using Forall2_reverse. Qed.
  Global Instance: Proper (Forall2 R ==> option_Forall2 R) last.
  Proof. repeat intro. eauto using Forall2_last. Qed.
End Forall2_proper.

Section Forall3.
  Context {A B C} (P : A → B → C → Prop).
  Local Hint Extern 0 (Forall3 _ _ _ _) => constructor : core.

  Lemma Forall3_app l1 l2 k1 k2 k1' k2' :
    Forall3 P l1 k1 k1' → Forall3 P l2 k2 k2' →
    Forall3 P (l1 ++ l2) (k1 ++ k2) (k1' ++ k2').
  Proof. induction 1; simpl; auto. Qed.
  Lemma Forall3_cons_inv_l x l k k' :
    Forall3 P (x :: l) k k' → ∃ y k2 z k2',
      k = y :: k2 ∧ k' = z :: k2' ∧ P x y z ∧ Forall3 P l k2 k2'.
  Proof. inv 1; naive_solver. Qed.
  Lemma Forall3_app_inv_l l1 l2 k k' :
    Forall3 P (l1 ++ l2) k k' → ∃ k1 k2 k1' k2',
     k = k1 ++ k2 ∧ k' = k1' ++ k2' ∧ Forall3 P l1 k1 k1' ∧ Forall3 P l2 k2 k2'.
  Proof.
    revert k k'. induction l1 as [|x l1 IH]; simpl; inv 1.
    - by repeat eexists; eauto.
    - by repeat eexists; eauto.
    - edestruct IH as (?&?&?&?&?&?&?&?); eauto; naive_solver.
  Qed.
  Lemma Forall3_cons_inv_m l y k k' :
    Forall3 P l (y :: k) k' → ∃ x l2 z k2',
      l = x :: l2 ∧ k' = z :: k2' ∧ P x y z ∧ Forall3 P l2 k k2'.
  Proof. inv 1; naive_solver. Qed.
  Lemma Forall3_app_inv_m l k1 k2 k' :
    Forall3 P l (k1 ++ k2) k' → ∃ l1 l2 k1' k2',
     l = l1 ++ l2 ∧ k' = k1' ++ k2' ∧ Forall3 P l1 k1 k1' ∧ Forall3 P l2 k2 k2'.
  Proof.
    revert l k'. induction k1 as [|x k1 IH]; simpl; inv 1.
    - by repeat eexists; eauto.
    - by repeat eexists; eauto.
    - edestruct IH as (?&?&?&?&?&?&?&?); eauto; naive_solver.
  Qed.
  Lemma Forall3_cons_inv_r l k z k' :
    Forall3 P l k (z :: k') → ∃ x l2 y k2,
      l = x :: l2 ∧ k = y :: k2 ∧ P x y z ∧ Forall3 P l2 k2 k'.
  Proof. inv 1; naive_solver. Qed.
  Lemma Forall3_app_inv_r l k k1' k2' :
    Forall3 P l k (k1' ++ k2') → ∃ l1 l2 k1 k2,
      l = l1 ++ l2 ∧ k = k1 ++ k2 ∧ Forall3 P l1 k1 k1' ∧ Forall3 P l2 k2 k2'.
  Proof.
    revert l k. induction k1' as [|x k1' IH]; simpl; inv 1.
    - by repeat eexists; eauto.
    - by repeat eexists; eauto.
    - edestruct IH as (?&?&?&?&?&?&?&?); eauto; naive_solver.
  Qed.
  Lemma Forall3_impl (Q : A → B → C → Prop) l k k' :
    Forall3 P l k k' → (∀ x y z, P x y z → Q x y z) → Forall3 Q l k k'.
  Proof. intros Hl ?; induction Hl; auto. Defined.
  Lemma Forall3_length_lm l k k' : Forall3 P l k k' → length l = length k.
  Proof. by induction 1; f_equal/=. Qed.
  Lemma Forall3_length_lr l k k' : Forall3 P l k k' → length l = length k'.
  Proof. by induction 1; f_equal/=. Qed.
  Lemma Forall3_lookup_lmr l k k' i x y z :
    Forall3 P l k k' →
    l !! i = Some x → k !! i = Some y → k' !! i = Some z → P x y z.
  Proof.
    intros H. revert i. induction H; intros [|?] ???; simplify_eq/=; eauto.
  Qed.
  Lemma Forall3_lookup_l l k k' i x :
    Forall3 P l k k' → l !! i = Some x →
    ∃ y z, k !! i = Some y ∧ k' !! i = Some z ∧ P x y z.
  Proof.
    intros H. revert i. induction H; intros [|?] ?; simplify_eq/=; eauto.
  Qed.
  Lemma Forall3_lookup_m l k k' i y :
    Forall3 P l k k' → k !! i = Some y →
    ∃ x z, l !! i = Some x ∧ k' !! i = Some z ∧ P x y z.
  Proof.
    intros H. revert i. induction H; intros [|?] ?; simplify_eq/=; eauto.
  Qed.
  Lemma Forall3_lookup_r l k k' i z :
    Forall3 P l k k' → k' !! i = Some z →
    ∃ x y, l !! i = Some x ∧ k !! i = Some y ∧ P x y z.
  Proof.
    intros H. revert i. induction H; intros [|?] ?; simplify_eq/=; eauto.
  Qed.
  Lemma Forall3_alter_lm f g l k k' i :
    Forall3 P l k k' →
    (∀ x y z, l !! i = Some x → k !! i = Some y → k' !! i = Some z →
      P x y z → P (f x) (g y) z) →
    Forall3 P (alter f i l) (alter g i k) k'.
  Proof. intros Hl. revert i. induction Hl; intros [|]; auto. Qed.
End Forall3.

(** ** Properties of [subseteq] *)
Section subseteq.
Context {A : Type}.
Implicit Types x y z : A.
Implicit Types l k : list A.

Global Instance list_subseteq_po : PreOrder (⊆@{list A}).
Proof. split; firstorder. Qed.
Lemma list_subseteq_nil l : [] ⊆ l.
Proof. intros x. by rewrite elem_of_nil. Qed.
Lemma list_nil_subseteq l : l ⊆ [] → l = [].
Proof.
  intro Hl. destruct l as [|x l1]; [done|]. exfalso.
  rewrite <-(elem_of_nil x).
  apply Hl, elem_of_cons. by left.
Qed.
Lemma list_subseteq_skip x l1 l2 : l1 ⊆ l2 → x :: l1 ⊆ x :: l2.
Proof.
  intros Hin y Hy%elem_of_cons.
  destruct Hy as [-> | Hy]; [by left|]. right. by apply Hin.
Qed.
Lemma list_subseteq_cons x l1 l2 : l1 ⊆ l2 → l1 ⊆ x :: l2.
Proof. intros Hin y Hy. right. by apply Hin. Qed.
Lemma list_subseteq_app_l l1 l2 l : l1 ⊆ l2 → l1 ⊆ l2 ++ l.
Proof. unfold subseteq, list_subseteq. setoid_rewrite elem_of_app. naive_solver. Qed.
Lemma list_subseteq_app_r l1 l2 l : l1 ⊆ l2 → l1 ⊆ l ++ l2.
Proof. unfold subseteq, list_subseteq. setoid_rewrite elem_of_app. naive_solver. Qed.

Lemma list_subseteq_app_iff_l l1 l2 l :
  l1 ++ l2 ⊆ l ↔ l1 ⊆ l ∧ l2 ⊆ l.
Proof. unfold subseteq, list_subseteq. setoid_rewrite elem_of_app. naive_solver. Qed.
Lemma list_subseteq_cons_iff x l1 l2 :
  x :: l1 ⊆ l2 ↔ x ∈ l2 ∧ l1 ⊆ l2.
Proof. unfold subseteq, list_subseteq. setoid_rewrite elem_of_cons. naive_solver. Qed.

Lemma list_subseteq_delete i l : delete i l ⊆ l.
Proof. apply sublist_subseteq, sublist_delete. Qed.
Lemma list_subseteq_filter P `{!∀ x : A, Decision (P x)} l : filter P l ⊆ l.
Proof. apply sublist_subseteq. apply sublist_filter. Qed.

Lemma subseteq_drop n l : drop n l ⊆ l.
Proof. rewrite <-(take_drop n l) at 2. apply list_subseteq_app_r. done. Qed.
Lemma subseteq_take n l : take n l ⊆ l.
Proof. rewrite <-(take_drop n l) at 2. apply list_subseteq_app_l. done. Qed.

Global Instance list_subseteq_Permutation:
  Proper ((≡ₚ) ==> (≡ₚ) ==> (↔)) (⊆@{list A}) .
Proof.
  intros l1 l2 Hl k1 k2 Hk. apply forall_proper; intros x. by rewrite Hl, Hk.
Qed.

Global Program Instance list_subseteq_dec `{!EqDecision A} : RelDecision (⊆@{list A}) :=
  λ xs ys, cast_if (decide (Forall (λ x, x ∈ ys) xs)).
Next Obligation. intros ???. by rewrite Forall_forall. Qed.
Next Obligation. intros ???. by rewrite Forall_forall. Qed.
End subseteq.

(** Setoids *)
Section setoid.
  Context `{Equiv A}.
  Implicit Types l k : list A.

  Lemma list_equiv_Forall2 l k : l ≡ k ↔ Forall2 (≡) l k.
  Proof. split; induction 1; constructor; auto. Qed.
  Lemma list_equiv_lookup l k : l ≡ k ↔ ∀ i, l !! i ≡ k !! i.
  Proof.
    rewrite list_equiv_Forall2, Forall2_lookup.
    by setoid_rewrite option_equiv_Forall2.
  Qed.

  Global Instance list_equivalence :
    Equivalence (≡@{A}) → Equivalence (≡@{list A}).
  Proof.
    split.
    - intros l. by apply list_equiv_Forall2.
    - intros l k; rewrite !list_equiv_Forall2; by intros.
    - intros l1 l2 l3; rewrite !list_equiv_Forall2; intros; by trans l2.
  Qed.
  Global Instance list_leibniz `{!LeibnizEquiv A} : LeibnizEquiv (list A).
  Proof. induction 1; f_equal; fold_leibniz; auto. Qed.

  Global Instance cons_proper : Proper ((≡) ==> (≡) ==> (≡@{list A})) cons.
  Proof. by constructor. Qed.
  Global Instance app_proper : Proper ((≡) ==> (≡) ==> (≡@{list A})) app.
  Proof. induction 1; intros ???; simpl; try constructor; auto. Qed.
  Global Instance length_proper : Proper ((≡@{list A}) ==> (=)) length.
  Proof. induction 1; f_equal/=; auto. Qed.
  Global Instance tail_proper : Proper ((≡@{list A}) ==> (≡)) tail.
  Proof. destruct 1; try constructor; auto. Qed.
  Global Instance take_proper n : Proper ((≡@{list A}) ==> (≡)) (take n).
  Proof. induction n; destruct 1; constructor; auto. Qed.
  Global Instance drop_proper n : Proper ((≡@{list A}) ==> (≡)) (drop n).
  Proof. induction n; destruct 1; simpl; try constructor; auto. Qed.
  Global Instance list_lookup_proper i : Proper ((≡@{list A}) ==> (≡)) (lookup i).
  Proof. induction i; destruct 1; simpl; try constructor; auto. Qed.
  Global Instance list_lookup_total_proper `{!Inhabited A} i :
    Proper (≡@{A}) inhabitant →
    Proper ((≡@{list A}) ==> (≡)) (lookup_total i).
  Proof. intros ?. induction i; destruct 1; simpl; auto. Qed.
  Global Instance list_alter_proper :
    Proper (((≡) ==> (≡)) ==> (=) ==> (≡) ==> (≡@{list A})) alter.
  Proof.
    intros f1 f2 Hf i ? <-. induction i; destruct 1; constructor; eauto.
  Qed.
  Global Instance list_insert_proper i :
    Proper ((≡) ==> (≡) ==> (≡@{list A})) (insert i).
  Proof. intros ???; induction i; destruct 1; constructor; eauto. Qed.
  Global Instance list_inserts_proper i :
    Proper ((≡) ==> (≡) ==> (≡@{list A})) (list_inserts i).
  Proof.
    intros k1 k2 Hk; revert i.
    induction Hk; intros ????; simpl; try f_equiv; naive_solver.
  Qed.
  Global Instance list_delete_proper i :
    Proper ((≡) ==> (≡@{list A})) (delete i).
  Proof. induction i; destruct 1; try constructor; eauto. Qed.
  Global Instance option_list_proper : Proper ((≡) ==> (≡@{list A})) option_list.
  Proof. destruct 1; repeat constructor; auto. Qed.
  Global Instance list_filter_proper P `{∀ x, Decision (P x)} :
    Proper ((≡) ==> iff) P → Proper ((≡) ==> (≡@{list A})) (filter P).
  Proof. intros ???. rewrite !list_equiv_Forall2. by apply Forall2_filter. Qed.
  Global Instance replicate_proper n : Proper ((≡@{A}) ==> (≡)) (replicate n).
  Proof. induction n; constructor; auto. Qed.
  Global Instance reverse_proper : Proper ((≡) ==> (≡@{list A})) reverse.
  Proof.
    induction 1; rewrite ?reverse_cons; simpl; [constructor|].
    apply app_proper; repeat constructor; auto.
  Qed.
  Global Instance last_proper : Proper ((≡) ==> (≡)) (@last A).
  Proof. induction 1 as [|????? []]; simpl; repeat constructor; auto. Qed.

  Global Instance cons_equiv_inj : Inj2 (≡) (≡) (≡) (@cons A).
  Proof. inv 1; auto. Qed.

  Lemma nil_equiv_eq l : l ≡ [] ↔ l = [].
  Proof. split; [by inv 1|intros ->; constructor]. Qed.
  Lemma cons_equiv_eq l x k : l ≡ x :: k ↔ ∃ x' k', l = x' :: k' ∧ x' ≡ x ∧ k' ≡ k.
  Proof. split; [inv 1; naive_solver|naive_solver (by constructor)]. Qed.
  Lemma list_singleton_equiv_eq l x : l ≡ [x] ↔ ∃ x', l = [x'] ∧ x' ≡ x.
  Proof. rewrite cons_equiv_eq. setoid_rewrite nil_equiv_eq. naive_solver. Qed.
  Lemma app_equiv_eq l k1 k2 :
    l ≡ k1 ++ k2 ↔ ∃ k1' k2', l = k1' ++ k2' ∧ k1' ≡ k1 ∧ k2' ≡ k2.
  Proof.
    split; [|intros (?&?&->&?&?); by f_equiv].
    setoid_rewrite list_equiv_Forall2. rewrite Forall2_app_inv_r. naive_solver.
  Qed.

  Lemma equiv_Permutation l1 l2 l3 :
    l1 ≡ l2 → l2 ≡ₚ l3 → ∃ l2', l1 ≡ₚ l2' ∧ l2' ≡ l3.
  Proof.
    intros Hequiv Hperm. revert l1 Hequiv.
    induction Hperm as [|x l2 l3 _ IH|x y l2|l2 l3 l4 _ IH1 _ IH2]; intros l1.
    - intros ?. by exists l1.
    - intros (x'&l2'&->&?&(l2''&?&?)%IH)%cons_equiv_eq.
      exists (x' :: l2''). by repeat constructor.
    - intros (y'&?&->&?&(x'&l2'&->&?&?)%cons_equiv_eq)%cons_equiv_eq.
      exists (x' :: y' :: l2'). by repeat constructor.
    - intros (l2'&?&(l3'&?&?)%IH2)%IH1. exists l3'. split; [by etrans|done].
  Qed.

  Lemma Permutation_equiv `{!Equivalence (≡@{A})} l1 l2 l3 :
    l1 ≡ₚ l2 → l2 ≡ l3 → ∃ l2', l1 ≡ l2' ∧ l2' ≡ₚ l3.
  Proof.
    intros Hperm%symmetry Hequiv%symmetry.
    destruct (equiv_Permutation _ _  _ Hequiv Hperm) as (l2'&?&?).
    by exists l2'.
  Qed.
End setoid.

Lemma TCForall_Forall {A} (P : A → Prop) xs : TCForall P xs ↔ Forall P xs.
Proof. split; induction 1; constructor; auto. Qed.

Global Instance TCForall_app {A} (P : A → Prop) xs ys :
  TCForall P xs → TCForall P ys → TCForall P (xs ++ ys).
Proof. rewrite !TCForall_Forall. apply Forall_app_2. Qed.

Lemma TCForall2_Forall2 {A B} (P : A → B → Prop) xs ys :
  TCForall2 P xs ys ↔ Forall2 P xs ys.
Proof. split; induction 1; constructor; auto. Qed.

Lemma TCExists_Exists {A} (P : A → Prop) l : TCExists P l ↔ Exists P l.
Proof. split; induction 1; constructor; solve [auto]. Qed.

End list.
