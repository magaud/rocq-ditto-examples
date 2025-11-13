From Coq Require Export Permutation.
From stdpp Require Export numbers base option list_basics list_relations.
From stdpp Require Import options.

Module Export list.

(** The monadic operations. *)
Global Instance list_ret: MRet list := λ A x, x :: @nil A.
Global Instance list_fmap : FMap list := λ A B f,
  fix go (l : list A) := match l with [] => [] | x :: l => f x :: go l end.
Global Instance list_omap : OMap list := λ A B f,
  fix go (l : list A) :=
  match l with
  | [] => []
  | x :: l => match f x with Some y => y :: go l | None => go l end
  end.
Global Instance list_bind : MBind list := λ A B f,
  fix go (l : list A) := match l with [] => [] | x :: l => f x ++ go l end.
Global Instance list_join: MJoin list :=
  fix go A (ls : list (list A)) : list A :=
  match ls with [] => [] | l :: ls => l ++ @mjoin _ go _ ls end.

Definition mapM `{MBind M, MRet M} {A B} (f : A → M B) : list A → M (list B) :=
  fix go l :=
  match l with [] => mret [] | x :: l => y ← f x; k ← go l; mret (y :: k) end.
Global Instance: Params (@mapM) 5 := {}.

(** We define stronger variants of the map function that allow the mapped
function to use the index of the elements. *)
Fixpoint imap {A B} (f : nat → A → B) (l : list A) : list B :=
  match l with
  | [] => []
  | x :: l => f 0 x :: imap (f ∘ S) l
  end.
Global Instance: Params (@imap) 2 := {}.

Definition zipped_map {A B} (f : list A → list A → A → B) :
    list A → list A → list B := fix go l k :=
  match k with
  | [] => []
  | x :: k => f l k x :: go (x :: l) k
  end.
Global Instance: Params (@zipped_map) 2 := {}.

Fixpoint imap2 {A B C} (f : nat → A → B → C) (l : list A) (k : list B) : list C :=
  match l, k with
  | [], _ | _, [] => []
  | x :: l, y :: k => f 0 x y :: imap2 (f ∘ S) l k
  end.
Global Instance: Params (@imap2) 3 := {}.

Inductive zipped_Forall {A} (P : list A → list A → A → Prop) :
    list A → list A → Prop :=
  | zipped_Forall_nil l : zipped_Forall P l []
  | zipped_Forall_cons l k x :
     P l k x → zipped_Forall P (x :: l) k → zipped_Forall P l (x :: k).
Global Arguments zipped_Forall_nil {_ _} _ : assert.
Global Arguments zipped_Forall_cons {_ _} _ _ _ _ _ : assert.

(** The Cartesian product on lists satisfies (lemma [list_elem_of_cprod]):

  x ∈ cprod l k ↔ x.1 ∈ l ∧ x.2 ∈ k

There are little meaningful things to say about the order of the elements in
[cprod] (so there are no lemmas for that). It thus only makes sense to use
[cprod] when treating the lists as a set-like structure (i.e., up to duplicates
and permutations). *)
Global Instance list_cprod {A B} : CProd (list A) (list B) (list (A * B)) :=
  λ l k, x ← l; (x,.) <$> k.

(** The function [permutations l] yields all permutations of [l]. *)
Fixpoint interleave {A} (x : A) (l : list A) : list (list A) :=
  match l with
  | [] => [[x]]| y :: l => (x :: y :: l) :: ((y ::.) <$> interleave x l)
  end.
Fixpoint permutations {A} (l : list A) : list (list A) :=
  match l with [] => [[]] | x :: l => permutations l ≫= interleave x end.

(** The function [powermset l] returns the list of all lists [l'] such that
[l' ⊆+ l] (notation for [submseteq l' l]). In other words, it returns the
"powerset" of [l], where each [l'] is obtained from [l] by removing elements
and possibly changing the order. *)
Fixpoint powermset {A} (l : list A) : list (list A) :=
  match l with
  | [] => [[]]
  | x :: l => (powermset l ≫= interleave x) ++ powermset l
  end.

Section general_properties.
Context {A : Type}.
Implicit Types x y z : A.
Implicit Types l k : list A.

(** The Cartesian product *)
(** Correspondence to [list_prod] from the stdlib, a version that does not use
the [CProd] class for the interface, nor the monad classes for the definition *)
Lemma list_cprod_list_prod {B} l (k : list B) : cprod l k = list_prod l k.
Proof. unfold cprod, list_cprod. induction l; f_equal/=; auto. Qed.

Lemma list_elem_of_cprod {B} l (k : list B) (x : A * B) :
  x ∈ cprod l k ↔ x.1 ∈ l ∧ x.2 ∈ k.
Proof.
  rewrite list_cprod_list_prod, !list_elem_of_In.
  destruct x. apply in_prod_iff.
Qed.

End general_properties.

(** * Properties of the monadic operations *)
Lemma list_fmap_id {A} (l : list A) : id <$> l = l.
Proof. induction l; f_equal/=; auto. Qed.

Global Instance list_fmap_proper `{!Equiv A, !Equiv B} :
  Proper (((≡) ==> (≡)) ==> (≡@{list A}) ==> (≡@{list B})) fmap.
Proof. induction 2; csimpl; constructor; auto. Qed.

Section fmap.
  Context {A B : Type} (f : A → B).
  Implicit Types l : list A.

  Lemma list_fmap_compose {C} (g : B → C) l : g ∘ f <$> l = g <$> (f <$> l).
  Proof. induction l; f_equal/=; auto. Qed.

  Lemma list_fmap_inj_1 f' l x :
    f <$> l = f' <$> l → x ∈ l → f x = f' x.
  Proof. intros Hf Hin. induction Hin; naive_solver. Qed.

  Definition fmap_nil : f <$> [] = [] := eq_refl.
  Definition fmap_cons x l : f <$> x :: l = f x :: (f <$> l) := eq_refl.

  Lemma list_fmap_singleton x : f <$> [x] = [f x].
  Proof. reflexivity. Qed.
  Lemma fmap_app l1 l2 : f <$> l1 ++ l2 = (f <$> l1) ++ (f <$> l2).
  Proof. by induction l1; f_equal/=. Qed.
  Lemma fmap_snoc l x : f <$> l ++ [x] = (f <$> l) ++ [f x].
  Proof. rewrite fmap_app, list_fmap_singleton. done. Qed.
  Lemma fmap_nil_inv k :  f <$> k = [] → k = [].
  Proof. by destruct k. Qed.
  Lemma fmap_cons_inv y l k :
    f <$> l = y :: k → ∃ x l', y = f x ∧ k = f <$> l' ∧ l = x :: l'.
  Proof. intros. destruct l; simplify_eq/=; eauto. Qed.
  Lemma fmap_app_inv l k1 k2 :
    f <$> l = k1 ++ k2 → ∃ l1 l2, k1 = f <$> l1 ∧ k2 = f <$> l2 ∧ l = l1 ++ l2.
  Proof.
    revert l. induction k1 as [|y k1 IH]; simpl; [intros l ?; by eexists [],l|].
    intros [|x l] ?; simplify_eq/=.
    destruct (IH l) as (l1&l2&->&->&->); [done|]. by exists (x :: l1), l2.
  Qed.
  Lemma fmap_option_list mx :
    f <$> (option_list mx) = option_list (f <$> mx).
  Proof. by destruct mx. Qed.

  Lemma list_fmap_alt l :
    f <$> l = omap (λ x, Some (f x)) l.
  Proof. induction l; simplify_eq/=; done. Qed.

  Lemma length_fmap l : length (f <$> l) = length l.
  Proof. by induction l; f_equal/=. Qed.
  Lemma fmap_reverse l : f <$> reverse l = reverse (f <$> l).
  Proof.
    induction l as [|?? IH]; csimpl; by rewrite ?reverse_cons, ?fmap_app, ?IH.
  Qed.
  Lemma fmap_tail l : f <$> tail l = tail (f <$> l).
  Proof. by destruct l. Qed.
  Lemma fmap_last l : last (f <$> l) = f <$> last l.
  Proof. induction l as [|? []]; simpl; auto. Qed.
  Lemma fmap_replicate n x :  f <$> replicate n x = replicate n (f x).
  Proof. by induction n; f_equal/=. Qed.
  Lemma fmap_take n l : f <$> take n l = take n (f <$> l).
  Proof. revert n. by induction l; intros [|?]; f_equal/=. Qed.
  Lemma fmap_drop n l : f <$> drop n l = drop n (f <$> l).
  Proof. revert n. by induction l; intros [|?]; f_equal/=. Qed.

  Lemma const_fmap (l : list A) (y : B) :
    (∀ i x, l !! i = Some x → f x = y) →
    f <$> l = replicate (length l) y.
  Proof. rewrite <-Forall_lookup. induction 1; f_equal/=; auto. Qed.

  Lemma list_lookup_fmap l i : (f <$> l) !! i = f <$> (l !! i).
  Proof. revert i. induction l; intros [|n]; by try revert n. Qed.
  Lemma list_lookup_total_fmap `{!Inhabited A, !Inhabited B} l i :
    i < length l → (f <$> l) !!! i = f (l !!! i).
  Proof.
    intros [x Hx]%lookup_lt_is_Some_2.
    by rewrite !list_lookup_total_alt, list_lookup_fmap, Hx.
  Qed.

  Lemma list_lookup_fmap_Some l i y :
    (f <$> l) !! i = Some y ↔ ∃ x, y = f x ∧ l !! i = Some x.
  Proof. rewrite list_lookup_fmap, fmap_Some. naive_solver. Qed.
  Lemma list_lookup_fmap_Some_1 l i y :
    (f <$> l) !! i = Some y → ∃ x, y = f x ∧ l !! i = Some x.
  Proof. by rewrite list_lookup_fmap_Some. Qed.
  Lemma list_lookup_fmap_Some_2 l i x :
    l !! i = Some x → (f <$> l) !! i = Some (f x).
  Proof. rewrite list_lookup_fmap_Some. naive_solver. Qed.

  Lemma list_fmap_insert l i x: f <$> <[i:=x]>l = <[i:=f x]>(f <$> l).
  Proof. revert i. by induction l; intros [|i]; f_equal/=. Qed.
  Lemma list_fmap_alter (g : A → A) (h : B → B) l i :
    Forall (λ x, f (g x) = h (f x)) l → f <$> alter g i l = alter h i (f <$> l).
  Proof. intros Hl. revert i. by induction Hl; intros [|i]; f_equal/=. Qed.
  Lemma list_fmap_delete l i : f <$> (delete i l) = delete i (f <$> l).
  Proof.
    revert i. induction l; intros i; destruct i; csimpl; eauto.
    naive_solver congruence.
  Qed.

  Lemma list_elem_of_fmap l y : y ∈ f <$> l ↔ ∃ x, y = f x ∧ x ∈ l.
  Proof.
    setoid_rewrite list_elem_of_lookup. setoid_rewrite list_lookup_fmap_Some.
    naive_solver.
  Qed.
  Lemma list_elem_of_fmap_1 l x : x ∈ f <$> l → ∃ y, x = f y ∧ y ∈ l.
  Proof. by rewrite list_elem_of_fmap. Qed.
  Lemma list_elem_of_fmap_2 l x : x ∈ l → f x ∈ f <$> l.
  Proof. rewrite list_elem_of_fmap. naive_solver. Qed.
  Lemma list_elem_of_fmap_2' l x y : x ∈ l → y = f x → y ∈ f <$> l.
  Proof. intros ? ->. by apply list_elem_of_fmap_2. Qed.

  Lemma list_elem_of_fmap_inj `{!Inj (=) (=) f} l x : f x ∈ f <$> l ↔ x ∈ l.
  Proof. rewrite list_elem_of_fmap. naive_solver. Qed.
  Lemma list_elem_of_fmap_inj_2 `{!Inj (=) (=) f} l x : f x ∈ f <$> l → x ∈ l.
  Proof. by rewrite list_elem_of_fmap_inj. Qed.

  Lemma list_fmap_inj R1 R2 :
    Inj R1 R2 f → Inj (Forall2 R1) (Forall2 R2) (fmap f).
  Proof.
    intros ? l1. induction l1; intros [|??]; inv 1; constructor; auto.
  Qed.
  Global Instance list_fmap_eq_inj : Inj (=) (=) f → Inj (=@{list A}) (=) (fmap f).
  Proof.
    intros ?%list_fmap_inj ?? ?%list_eq_Forall2%(inj _). by apply list_eq_Forall2.
  Qed.
  Global Instance list_fmap_equiv_inj `{!Equiv A, !Equiv B} :
    Inj (≡) (≡) f → Inj (≡@{list A}) (≡) (fmap f).
  Proof.
    intros ?%list_fmap_inj ?? ?%list_equiv_Forall2%(inj _).
    by apply list_equiv_Forall2.
  Qed.

  (** A version of [NoDup_fmap_2] that does not require [f] to be injective for
      *all* inputs. *)
  Lemma NoDup_fmap_2_strong l :
    (∀ x y, x ∈ l → y ∈ l → f x = f y → x = y) →
    NoDup l →
    NoDup (f <$> l).
  Proof.
    intros Hinj. induction 1 as [|x l ?? IH]; simpl; constructor.
    - intros [y [Hxy ?]]%list_elem_of_fmap.
      apply Hinj in Hxy; [by subst|by constructor..].
    - apply IH. clear- Hinj.
      intros x' y Hx' Hy. apply Hinj; by constructor.
  Qed.

  Lemma NoDup_fmap_1 l : NoDup (f <$> l) → NoDup l.
  Proof.
    induction l; simpl; inv 1; constructor; auto.
    rewrite list_elem_of_fmap in *. naive_solver.
  Qed.
  Lemma NoDup_fmap_2 `{!Inj (=) (=) f} l : NoDup l → NoDup (f <$> l).
  Proof. apply NoDup_fmap_2_strong. intros ?? _ _. apply (inj f). Qed.
  Lemma NoDup_fmap `{!Inj (=) (=) f} l : NoDup (f <$> l) ↔ NoDup l.
  Proof. split; auto using NoDup_fmap_1, NoDup_fmap_2. Qed.

  Global Instance fmap_sublist: Proper (sublist ==> sublist) (fmap f).
  Proof. induction 1; simpl; econstructor; eauto. Qed.
  Global Instance fmap_submseteq: Proper (submseteq ==> submseteq) (fmap f).
  Proof. induction 1; simpl; econstructor; eauto. Qed.
  Global Instance fmap_Permutation: Proper ((≡ₚ) ==> (≡ₚ)) (fmap f).
  Proof. induction 1; simpl; econstructor; eauto. Qed.

  Lemma Forall_fmap_ext_1 (g : A → B) (l : list A) :
    Forall (λ x, f x = g x) l → fmap f l = fmap g l.
  Proof. by induction 1; f_equal/=. Qed.
  Lemma Forall_fmap_ext (g : A → B) (l : list A) :
    Forall (λ x, f x = g x) l ↔ fmap f l = fmap g l.
  Proof.
    split; [auto using Forall_fmap_ext_1|].
    induction l; simpl; constructor; simplify_eq; auto.
  Qed.
  Lemma Forall_fmap (P : B → Prop) l : Forall P (f <$> l) ↔ Forall (P ∘ f) l.
  Proof. split; induction l; inv 1; constructor; auto. Qed.
  Lemma Exists_fmap (P : B → Prop) l : Exists P (f <$> l) ↔ Exists (P ∘ f) l.
  Proof. split; induction l; inv 1; constructor; by auto. Qed.

  Lemma Forall2_fmap_l {C} (P : B → C → Prop) l k :
    Forall2 P (f <$> l) k ↔ Forall2 (P ∘ f) l k.
  Proof.
    split; revert k; induction l; inv 1; constructor; auto.
  Qed.
  Lemma Forall2_fmap_r {C} (P : C → B → Prop) k l :
    Forall2 P k (f <$> l) ↔ Forall2 (λ x, P x ∘ f) k l.
  Proof.
    split; revert k; induction l; inv 1; constructor; auto.
  Qed.
  Lemma Forall2_fmap_1 {C D} (g : C → D) (P : B → D → Prop) l k :
    Forall2 P (f <$> l) (g <$> k) → Forall2 (λ x1 x2, P (f x1) (g x2)) l k.
  Proof. revert k; induction l; intros [|??]; inv 1; auto. Qed.
  Lemma Forall2_fmap_2 {C D} (g : C → D) (P : B → D → Prop) l k :
    Forall2 (λ x1 x2, P (f x1) (g x2)) l k → Forall2 P (f <$> l) (g <$> k).
  Proof. induction 1; csimpl; auto. Qed.
  Lemma Forall2_fmap {C D} (g : C → D) (P : B → D → Prop) l k :
    Forall2 P (f <$> l) (g <$> k) ↔ Forall2 (λ x1 x2, P (f x1) (g x2)) l k.
  Proof. split; auto using Forall2_fmap_1, Forall2_fmap_2. Qed.

  Lemma list_fmap_bind {C} (g : B → list C) l : (f <$> l) ≫= g = l ≫= g ∘ f.
  Proof. by induction l; f_equal/=. Qed.
End fmap.

Section ext.
  Context {A B : Type}.
  Implicit Types l : list A.

  Lemma list_fmap_ext (f g : A → B) l :
    (∀ i x, l !! i = Some x → f x = g x) → f <$> l = g <$> l.
  Proof.
    intros Hfg. apply list_eq; intros i. rewrite !list_lookup_fmap.
    destruct (l !! i) eqn:?; f_equal/=; eauto.
  Qed.
  Lemma list_fmap_equiv_ext `{!Equiv B} (f g : A → B) l :
    (∀ i x, l !! i = Some x → f x ≡ g x) → f <$> l ≡ g <$> l.
  Proof.
    intros Hl. apply list_equiv_lookup; intros i. rewrite !list_lookup_fmap.
    destruct (l !! i) eqn:?; simpl; constructor; eauto.
  Qed.
End ext.

Lemma NoDup_fmap_fst {A B} (l : list (A * B)) :
  (∀ x y1 y2, (x,y1) ∈ l → (x,y2) ∈ l → y1 = y2) → NoDup l → NoDup (l.*1).
Proof.
  intros Hunique. induction 1 as [|[x1 y1] l Hin Hnodup IH]; csimpl; constructor.
  - rewrite list_elem_of_fmap.
    intros [[x2 y2] [??]]; simpl in *; subst. destruct Hin.
    rewrite (Hunique x2 y1 y2); rewrite ?elem_of_cons; auto.
  - apply IH. intros. eapply Hunique; rewrite ?elem_of_cons; eauto.
Qed.

Global Instance list_omap_proper `{!Equiv A, !Equiv B} :
  Proper (((≡) ==> (≡)) ==> (≡@{list A}) ==> (≡@{list B})) omap.
Proof.
  intros f1 f2 Hf. induction 1 as [|x1 x2 l1 l2 Hx Hl]; csimpl; [constructor|].
  destruct (Hf _ _ Hx); by repeat f_equiv.
Qed.

Section omap.
  Context {A B : Type} (f : A → option B).
  Implicit Types l : list A.

  Lemma list_fmap_omap {C} (g : B → C) l :
    g <$> omap f l = omap (λ x, g <$> (f x)) l.
  Proof.
    induction l as [|x y IH]; [done|]. csimpl.
    destruct (f x); csimpl; [|done]. by f_equal.
  Qed.
  Lemma list_omap_ext {A'} (g : A' → option B) l1 (l2 : list A') :
    Forall2 (λ a b, f a = g b) l1 l2 →
    omap f l1 = omap g l2.
  Proof.
    induction 1 as [|x y l l' Hfg ? IH]; [done|].
    csimpl. rewrite Hfg. destruct (g y); [|done]. by f_equal.
  Qed.
  Lemma list_elem_of_omap l y : y ∈ omap f l ↔ ∃ x, x ∈ l ∧ f x = Some y.
  Proof.
    split.
    - induction l as [|x l]; csimpl; repeat case_match;
        repeat (setoid_rewrite elem_of_nil || setoid_rewrite elem_of_cons);
        naive_solver.
    - intros (x&Hx&?). by induction Hx; csimpl; repeat case_match;
        simplify_eq; try constructor; auto.
  Qed.
  Global Instance omap_Permutation : Proper ((≡ₚ) ==> (≡ₚ)) (omap f).
  Proof. induction 1; simpl; repeat case_match; econstructor; eauto. Qed.

  Lemma omap_app l1 l2 :
    omap f (l1 ++ l2) = omap f l1 ++ omap f l2.
  Proof. induction l1; csimpl; repeat case_match; naive_solver congruence. Qed.
  Lemma omap_option_list mx :
    omap f (option_list mx) = option_list (mx ≫= f).
  Proof. by destruct mx. Qed.
End omap.

Global Instance list_bind_proper `{!Equiv A, !Equiv B} :
  Proper (((≡) ==> (≡)) ==> (≡@{list A}) ==> (≡@{list B})) mbind.
Proof. induction 2; csimpl; constructor || f_equiv; auto. Qed.

Section bind.
  Context {A B : Type} (f : A → list B).

  Lemma list_bind_ext (g : A → list B) l1 l2 :
    (∀ x, f x = g x) → l1 = l2 → l1 ≫= f = l2 ≫= g.
  Proof. intros ? <-. by induction l1; f_equal/=. Qed.
  Lemma Forall_bind_ext (g : A → list B) (l : list A) :
    Forall (λ x, f x = g x) l → l ≫= f = l ≫= g.
  Proof. by induction 1; f_equal/=. Qed.
  Global Instance bind_sublist: Proper (sublist ==> sublist) (mbind f).
  Proof.
    induction 1; simpl; auto;
      [by apply sublist_app|by apply sublist_inserts_l].
  Qed.
  Global Instance bind_submseteq: Proper (submseteq ==> submseteq) (mbind f).
  Proof.
    induction 1; csimpl; auto.
    - by apply submseteq_app.
    - by rewrite !(assoc_L (++)), (comm (++) (f _)).
    - by apply submseteq_inserts_l.
    - etrans; eauto.
  Qed.
  Global Instance bind_Permutation: Proper ((≡ₚ) ==> (≡ₚ)) (mbind f).
  Proof.
    induction 1; csimpl; auto.
    - by f_equiv.
    - by rewrite !(assoc_L (++)), (comm (++) (f _)).
    - etrans; eauto.
  Qed.
  Lemma bind_cons x l : (x :: l) ≫= f = f x ++ l ≫= f.
  Proof. done. Qed.
  Lemma bind_singleton x : [x] ≫= f = f x.
  Proof. csimpl. by rewrite (right_id_L _ (++)). Qed.
  Lemma bind_app l1 l2 : (l1 ++ l2) ≫= f = (l1 ≫= f) ++ (l2 ≫= f).
  Proof. by induction l1; csimpl; rewrite <-?(assoc_L (++)); f_equal. Qed.
  Lemma list_elem_of_bind (x : B) (l : list A) :
    x ∈ l ≫= f ↔ ∃ y, x ∈ f y ∧ y ∈ l.
  Proof.
    split.
    - induction l as [|y l IH]; csimpl; [inv 1|].
      rewrite elem_of_app. intros [?|?].
      + exists y. split; [done | by left].
      + destruct IH as [z [??]]; [done|]. exists z. split; [done | by right].
    - intros [y [Hx Hy]]. induction Hy; csimpl; rewrite elem_of_app; intuition.
  Qed.
  Lemma Forall_bind (P : B → Prop) l :
    Forall P (l ≫= f) ↔ Forall (Forall P ∘ f) l.
  Proof.
    split.
    - induction l; csimpl; rewrite ?Forall_app; constructor; csimpl; intuition.
    - induction 1; csimpl; rewrite ?Forall_app; auto.
  Qed.
  Lemma Forall2_bind {C D} (g : C → list D) (P : B → D → Prop) l1 l2 :
    Forall2 (λ x1 x2, Forall2 P (f x1) (g x2)) l1 l2 →
    Forall2 P (l1 ≫= f) (l2 ≫= g).
  Proof. induction 1; csimpl; auto using Forall2_app. Qed.
  Lemma NoDup_bind l :
    (∀ x1 x2 y, x1 ∈ l → x2 ∈ l → y ∈ f x1 → y ∈ f x2 → x1 = x2) →
    (∀ x, x ∈ l → NoDup (f x)) → NoDup l → NoDup (l ≫= f).
  Proof.
    intros Hinj Hf. induction 1 as [|x l ?? IH]; csimpl; [constructor|].
    apply NoDup_app. split_and!.
    - eauto 10 using list_elem_of_here.
    - intros y ? (x'&?&?)%list_elem_of_bind.
      destruct (Hinj x x' y); auto using list_elem_of_here, list_elem_of_further.
    - eauto 10 using list_elem_of_further.
  Qed.
End bind.

Global Instance list_join_proper `{!Equiv A} :
  Proper ((≡) ==> (≡@{list A})) mjoin.
Proof. induction 1; simpl; [constructor|solve_proper]. Qed.

Section ret_join.
  Context {A : Type}.

  Lemma list_join_bind (ls : list (list A)) : mjoin ls = ls ≫= id.
  Proof. by induction ls; f_equal/=. Qed.
  Global Instance join_Permutation : Proper ((≡ₚ@{list A}) ==> (≡ₚ)) mjoin.
  Proof. intros ?? E. by rewrite !list_join_bind, E. Qed.
  Lemma list_elem_of_ret (x y : A) : x ∈ @mret list _ A y ↔ x = y.
  Proof. apply list_elem_of_singleton. Qed.
  Lemma list_elem_of_join (x : A) (ls : list (list A)) :
    x ∈ mjoin ls ↔ ∃ l : list A, x ∈ l ∧ l ∈ ls.
  Proof. by rewrite list_join_bind, list_elem_of_bind. Qed.
  Lemma join_nil (ls : list (list A)) : mjoin ls = [] ↔ Forall (.= []) ls.
  Proof.
    split; [|by induction 1 as [|[|??] ?]].
    by induction ls as [|[|??] ?]; constructor; auto.
  Qed.
  Lemma join_nil_1 (ls : list (list A)) : mjoin ls = [] → Forall (.= []) ls.
  Proof. by rewrite join_nil. Qed.
  Lemma join_nil_2 (ls : list (list A)) : Forall (.= []) ls → mjoin ls = [].
  Proof. by rewrite join_nil. Qed.

  Lemma join_app (l1 l2 : list (list A)) :
    mjoin (l1 ++ l2) = mjoin l1 ++ mjoin l2.
  Proof.
    induction l1 as [|x l1 IH]; simpl; [done|]. by rewrite <-(assoc_L _ _), IH.
  Qed.

  Lemma Forall_join (P : A → Prop) (ls: list (list A)) :
    Forall (Forall P) ls → Forall P (mjoin ls).
  Proof. induction 1; simpl; auto using Forall_app_2. Qed.
  Lemma Forall2_join {B} (P : A → B → Prop) ls1 ls2 :
    Forall2 (Forall2 P) ls1 ls2 → Forall2 P (mjoin ls1) (mjoin ls2).
  Proof. induction 1; simpl; auto using Forall2_app. Qed.
End ret_join.

Global Instance mapM_proper `{!Equiv A, !Equiv B} :
  Proper (((≡) ==> (≡)) ==> (≡@{list A}) ==> (≡@{option (list B)})) mapM.
Proof.
  induction 2; csimpl; repeat (f_equiv || constructor || intro || auto).
Qed.

Section mapM.
  Context {A B : Type} (f : A → option B).

  Lemma mapM_ext (g : A → option B) l : (∀ x, f x = g x) → mapM f l = mapM g l.
  Proof. intros Hfg. by induction l as [|?? IHl]; simpl; rewrite ?Hfg, ?IHl. Qed.

  Lemma Forall2_mapM_ext (g : A → option B) l k :
    Forall2 (λ x y, f x = g y) l k → mapM f l = mapM g k.
  Proof. induction 1 as [|???? Hfg ? IH]; simpl; [done|]. by rewrite Hfg, IH. Qed.
  Lemma Forall_mapM_ext (g : A → option B) l :
    Forall (λ x, f x = g x) l → mapM f l = mapM g l.
  Proof. induction 1 as [|?? Hfg ? IH]; simpl; [done|]. by rewrite Hfg, IH. Qed.

  Lemma mapM_Some_1 l k : mapM f l = Some k → Forall2 (λ x y, f x = Some y) l k.
  Proof.
    revert k. induction l as [|x l]; intros [|y k]; simpl; try done.
    - destruct (f x); simpl; [|discriminate]. by destruct (mapM f l).
    - destruct (f x) eqn:?; intros; simplify_option_eq; auto.
  Qed.
  Lemma mapM_Some_2 l k : Forall2 (λ x y, f x = Some y) l k → mapM f l = Some k.
  Proof.
    induction 1 as [|???? Hf ? IH]; simpl; [done |].
    rewrite Hf. simpl. by rewrite IH.
  Qed.
  Lemma mapM_Some l k : mapM f l = Some k ↔ Forall2 (λ x y, f x = Some y) l k.
  Proof. split; auto using mapM_Some_1, mapM_Some_2. Qed.
  Lemma length_mapM l k : mapM f l = Some k → length l = length k.
  Proof. intros. by eapply Forall2_length, mapM_Some_1. Qed.
  Lemma mapM_None_1 l : mapM f l = None → Exists (λ x, f x = None) l.
  Proof.
    induction l as [|x l IH]; simpl; [done|].
    destruct (f x) eqn:?; simpl; eauto. by destruct (mapM f l); eauto.
  Qed.
  Lemma mapM_None_2 l : Exists (λ x, f x = None) l → mapM f l = None.
  Proof.
    induction 1 as [x l Hx|x l ? IH]; simpl; [by rewrite Hx|].
    by destruct (f x); simpl; rewrite ?IH.
  Qed.
  Lemma mapM_None l : mapM f l = None ↔ Exists (λ x, f x = None) l.
  Proof. split; auto using mapM_None_1, mapM_None_2. Qed.
  Lemma mapM_is_Some_1 l : is_Some (mapM f l) → Forall (is_Some ∘ f) l.
  Proof.
    unfold compose. setoid_rewrite <-not_eq_None_Some.
    rewrite mapM_None. apply (not_Exists_Forall _).
  Qed.
  Lemma mapM_is_Some_2 l : Forall (is_Some ∘ f) l → is_Some (mapM f l).
  Proof.
    unfold compose. setoid_rewrite <-not_eq_None_Some.
    rewrite mapM_None. apply (Forall_not_Exists _).
  Qed.
  Lemma mapM_is_Some l : is_Some (mapM f l) ↔ Forall (is_Some ∘ f) l.
  Proof. split; auto using mapM_is_Some_1, mapM_is_Some_2. Qed.

  Lemma mapM_fmap_Forall_Some (g : B → A) (l : list B) :
    Forall (λ x, f (g x) = Some x) l → mapM f (g <$> l) = Some l.
  Proof. by induction 1; simpl; simplify_option_eq. Qed.
  Lemma mapM_fmap_Some (g : B → A) (l : list B) :
    (∀ x, f (g x) = Some x) → mapM f (g <$> l) = Some l.
  Proof. intros. by apply mapM_fmap_Forall_Some, Forall_true. Qed.

  Lemma mapM_fmap_Forall2_Some_inv (g : B → A) (l : list A) (k : list B) :
    mapM f l = Some k → Forall2 (λ x y, f x = Some y → g y = x) l k → g <$> k = l.
  Proof. induction 2; simplify_option_eq; naive_solver. Qed.
  Lemma mapM_fmap_Some_inv (g : B → A) (l : list A) (k : list B) :
    mapM f l = Some k → (∀ x y, f x = Some y → g y = x) → g <$> k = l.
  Proof. eauto using mapM_fmap_Forall2_Some_inv, Forall2_true, length_mapM. Qed.
End mapM.

Lemma imap_const {A B} (f : A → B) l : imap (const f) l = f <$> l.
Proof. induction l; f_equal/=; auto. Qed.

Global Instance imap_proper `{!Equiv A, !Equiv B} :
  Proper (pointwise_relation _ ((≡) ==> (≡)) ==> (≡@{list A}) ==> (≡@{list B}))
         imap.
Proof.
  intros f f' Hf l l' Hl. revert f f' Hf.
  induction Hl as [|x1 x2 l1 l2 ?? IH]; intros f f' Hf; simpl; constructor.
  - by apply Hf.
  - apply IH. intros i y y' ?; simpl. by apply Hf.
Qed.

Section imap.
  Context {A B : Type} (f : nat → A → B).

  Lemma imap_ext g l :
    (∀ i x, l !! i = Some x → f i x = g i x) → imap f l = imap g l.
  Proof. revert f g; induction l as [|x l IH]; intros; f_equal/=; eauto. Qed.

  Lemma imap_nil : imap f [] = [].
  Proof. done. Qed.
  Lemma imap_app l1 l2 :
    imap f (l1 ++ l2) = imap f l1 ++ imap (λ n, f (length l1 + n)) l2.
  Proof.
    revert f. induction l1 as [|x l1 IH]; intros f; f_equal/=.
    by rewrite IH.
  Qed.
  Lemma imap_cons x l : imap f (x :: l) = f 0 x :: imap (f ∘ S) l.
  Proof. done. Qed.

  Lemma imap_fmap {C} (g : C → A) l : imap f (g <$> l) = imap (λ n, f n ∘ g) l.
  Proof. revert f. induction l; intros; f_equal/=; eauto. Qed.
  Lemma fmap_imap {C} (g : B → C) l : g <$> imap f l = imap (λ n, g ∘ f n) l.
  Proof. revert f. induction l; intros; f_equal/=; eauto. Qed.

  Lemma list_lookup_imap l i : imap f l !! i = f i <$> l !! i.
  Proof.
    revert f i. induction l as [|x l IH]; intros f [|i]; f_equal/=; auto.
    by rewrite IH.
  Qed.
  Lemma list_lookup_imap_Some l i x :
    imap f l !! i = Some x ↔ ∃ y, l !! i = Some y ∧ x = f i y.
  Proof. by rewrite list_lookup_imap, fmap_Some. Qed.
  Lemma list_lookup_total_imap `{!Inhabited A, !Inhabited B} l i :
    i < length l → imap f l !!! i = f i (l !!! i).
  Proof.
    intros [x Hx]%lookup_lt_is_Some_2.
    by rewrite !list_lookup_total_alt, list_lookup_imap, Hx.
  Qed.

  Lemma length_imap l : length (imap f l) = length l.
  Proof. revert f. induction l; simpl; eauto. Qed.

  Lemma elem_of_lookup_imap_1 l x :
    x ∈ imap f l → ∃ i y, x = f i y ∧ l !! i = Some y.
  Proof.
    intros [i Hin]%list_elem_of_lookup. rewrite list_lookup_imap in Hin.
    simplify_option_eq; naive_solver.
  Qed.
  Lemma elem_of_lookup_imap_2 l x i : l !! i = Some x → f i x ∈ imap f l.
  Proof.
    intros Hl. rewrite list_elem_of_lookup.
    exists i. by rewrite list_lookup_imap, Hl.
  Qed.
  Lemma elem_of_lookup_imap l x :
    x ∈ imap f l ↔ ∃ i y, x = f i y ∧ l !! i = Some y.
  Proof. naive_solver eauto using elem_of_lookup_imap_1, elem_of_lookup_imap_2. Qed.
End imap.

(** ** Properties of the [permutations] function *)
Section permutations.
  Context {A : Type}.
  Implicit Types x y z : A.
  Implicit Types l : list A.

  Lemma interleave_cons x l : x :: l ∈ interleave x l.
  Proof. destruct l; simpl; rewrite elem_of_cons; auto. Qed.
  Lemma elem_of_interleave l1 l2 x :
    l1 ∈ interleave x l2 ↔ ∃ l l', l1 = l ++ x :: l' ∧ l2 = l ++ l'.
  Proof.
    split.
    - revert l1. induction l2 as [|y l IH]; intros l1; simpl.
      { intros ->%list_elem_of_singleton. by exists [], []. }
      intros [->|H]%elem_of_cons; [by exists [], (y :: l)|].
      apply list_elem_of_fmap in H as [? [-> H]].
      apply IH in H as (l' & l'' & -> & ->).
      exists (y :: l'), l''. eauto.
    - intros (l & l' & -> & ->).
      induction l as [|y l IH]; simpl; [apply interleave_cons|].
      apply list_elem_of_further. by apply list_elem_of_fmap_2.
  Qed.
  Lemma interleave_Permutation x l l' : l' ∈ interleave x l → l' ≡ₚ x :: l.
  Proof.
    intros (l1&l2&->&->)%elem_of_interleave. by rewrite Permutation_middle.
  Qed.

  Lemma permutations_refl l : l ∈ permutations l.
  Proof.
    induction l; simpl; [by apply list_elem_of_singleton|].
    apply list_elem_of_bind. eauto using interleave_cons.
  Qed.
  Lemma permutations_skip x l l' :
    l ∈ permutations l' → x :: l ∈ permutations (x :: l').
  Proof. intro. apply list_elem_of_bind; eauto using interleave_cons. Qed.
  Lemma permutations_swap x y l : y :: x :: l ∈ permutations (x :: y :: l).
  Proof.
    simpl. apply list_elem_of_bind. exists (y :: l). split; simpl.
    - destruct l; csimpl; rewrite !elem_of_cons; auto.
    - apply list_elem_of_bind. simpl.
      eauto using interleave_cons, permutations_refl.
  Qed.
  Lemma permutations_nil l : l ∈ permutations [] ↔ l = [].
  Proof. simpl. by rewrite list_elem_of_singleton. Qed.
  Lemma interleave_interleave_toggle x1 x2 l1 l2 l3 :
    l1 ∈ interleave x1 l2 → l2 ∈ interleave x2 l3 → ∃ l4,
      l1 ∈ interleave x2 l4 ∧ l4 ∈ interleave x1 l3.
  Proof.
    revert l1 l2. induction l3 as [|y l3 IH]; intros l1 l2; simpl.
    { rewrite !list_elem_of_singleton. intros ? ->. exists [x1].
      change (interleave x2 [x1]) with ([[x2; x1]] ++ [[x1; x2]]).
      by rewrite (comm (++)), list_elem_of_singleton. }
    rewrite elem_of_cons, list_elem_of_fmap.
    intros Hl1 [? | [l2' [??]]]; simplify_eq/=.
    - rewrite !elem_of_cons, list_elem_of_fmap in Hl1.
      destruct Hl1 as [? | [? | [l4 [??]]]]; subst.
      + exists (x1 :: y :: l3). csimpl. rewrite !elem_of_cons. tauto.
      + exists (x1 :: y :: l3). csimpl. rewrite !elem_of_cons. tauto.
      + exists l4. simpl. rewrite elem_of_cons. auto using interleave_cons.
    - rewrite elem_of_cons, list_elem_of_fmap in Hl1.
      destruct Hl1 as [? | [l1' [??]]]; subst.
      + exists (x1 :: y :: l3). csimpl.
        rewrite !elem_of_cons, !list_elem_of_fmap.
        split; [| by auto]. right. right. exists (y :: l2').
        rewrite list_elem_of_fmap. naive_solver.
      + destruct (IH l1' l2') as [l4 [??]]; auto. exists (y :: l4). simpl.
        rewrite !elem_of_cons, !list_elem_of_fmap. naive_solver.
  Qed.
  Lemma permutations_interleave_toggle x l1 l2 l3 :
    l1 ∈ permutations l2 → l2 ∈ interleave x l3 → ∃ l4,
      l1 ∈ interleave x l4 ∧ l4 ∈ permutations l3.
  Proof.
    revert l1 l2. induction l3 as [|y l3 IH]; intros l1 l2; simpl.
    { rewrite list_elem_of_singleton. intros Hl1 ->. eexists [].
      by rewrite list_elem_of_singleton. }
    rewrite elem_of_cons, list_elem_of_fmap.
    intros Hl1 [? | [l2' [? Hl2']]]; simplify_eq/=.
    - rewrite list_elem_of_bind in Hl1.
      destruct Hl1 as [l1' [??]]. by exists l1'.
    - rewrite list_elem_of_bind in Hl1. setoid_rewrite list_elem_of_bind.
      destruct Hl1 as [l1' [??]]. destruct (IH l1' l2') as (l1''&?&?); auto.
      destruct (interleave_interleave_toggle y x l1 l1' l1'') as (?&?&?); eauto.
  Qed.
  Lemma permutations_trans l1 l2 l3 :
    l1 ∈ permutations l2 → l2 ∈ permutations l3 → l1 ∈ permutations l3.
  Proof.
    revert l1 l2. induction l3 as [|x l3 IH]; intros l1 l2; simpl.
    - rewrite !list_elem_of_singleton. intros Hl1 ->; simpl in *.
      by rewrite list_elem_of_singleton in Hl1.
    - rewrite !list_elem_of_bind. intros Hl1 [l2' [Hl2 Hl2']].
      destruct (permutations_interleave_toggle x l1 l2 l2') as [? [??]]; eauto.
  Qed.
  Lemma permutations_Permutation l l' : l' ∈ permutations l ↔ l ≡ₚ l'.
  Proof.
    split.
    - revert l'. induction l; simpl; intros l''.
      + rewrite list_elem_of_singleton. by intros ->.
      + rewrite list_elem_of_bind. intros [l' [Hl'' ?]].
        rewrite (interleave_Permutation _ _ _ Hl''). constructor; auto.
    - induction 1; eauto using permutations_refl,
        permutations_skip, permutations_swap, permutations_trans.
  Qed.
End permutations.

(** ** Properties of the [powermset] function. *)
Section powermset.
  Context {A : Type}.
  Implicit Types x y z : A.
  Implicit Types l : list A.

  Lemma powermset_submseteq l l' : l ∈ powermset l' ↔ l ⊆+ l'.
  Proof.
   split.
   - revert l; induction l' as [|x l' IH]; simpl; intros l.
     { by intros ->%list_elem_of_singleton. }
     intros [(k & Hl & Hk)%list_elem_of_bind|?]%elem_of_app.
     + apply IH in Hk. apply interleave_Permutation in Hl as ->.
       by apply submseteq_skip.
     + by apply submseteq_cons, IH.
   - revert l; induction l' as [|x l' IH]; simpl; intros l.
     { intros ->%submseteq_nil_r. apply list_elem_of_here. }
     rewrite elem_of_app, list_elem_of_bind.
     intros [H|(k & Hperm & Hsub)]%submseteq_cons_r; [by eauto|].
     apply Permutation_cons_inv_r in Hperm as (k1 & k2 & -> & Hperm).
     left. exists (k1 ++ k2). split.
     + apply elem_of_interleave. by exists k1, k2.
     + apply IH. by rewrite <-Hperm.
  Qed.
  Lemma powermset_refl l : l ∈ powermset l.
  Proof. by rewrite powermset_submseteq. Qed.
  Lemma powermset_nil l : l ∈ powermset [] ↔ l = [].
  Proof. simpl. by rewrite list_elem_of_singleton. Qed.
  Lemma powermset_permutations l l' : l ∈ permutations l' → l ∈ powermset l'.
  Proof.
    rewrite powermset_submseteq, permutations_Permutation. by intros ->.
  Qed.
  Lemma powermset_trans l1 l2 l3 :
    l1 ∈ powermset l2 → l2 ∈ powermset l3 → l1 ∈ powermset l3.
  Proof. rewrite !powermset_submseteq. apply submseteq_trans. Qed.
End powermset.

(** ** Properties of the folding functions *)
(** Note that [foldr] has much better support, so when in doubt, it should be
preferred over [foldl]. *)
Definition foldr_app := @fold_right_app.

Lemma foldr_cons {A B} (f : B → A → A) (a : A) l x :
  foldr f a (x :: l) = f x (foldr f a l).
Proof. done. Qed.
Lemma foldr_snoc {A B} (f : B → A → A) (a : A) l x :
  foldr f a (l ++ [x]) = foldr f (f x a) l.
Proof. rewrite foldr_app. done. Qed.

Lemma foldr_fmap {A B C} (f : B → A → A) x (l : list C) g :
  foldr f x (g <$> l) = foldr (λ b a, f (g b) a) x l.
Proof. induction l; f_equal/=; auto. Qed.
Lemma foldr_ext {A B} (f1 f2 : B → A → A) x1 x2 l1 l2 :
  (∀ b a, f1 b a = f2 b a) → l1 = l2 → x1 = x2 → foldr f1 x1 l1 = foldr f2 x2 l2.
Proof. intros Hf -> ->. induction l2 as [|x l2 IH]; f_equal/=; by rewrite Hf, IH. Qed.

Lemma foldr_permutation {A B} (R : relation B) `{!PreOrder R}
    (f : A → B → B) (b : B) `{Hf : !∀ x, Proper (R ==> R) (f x)} (l1 l2 : list A) :
  (∀ j1 a1 j2 a2 b,
    j1 ≠ j2 → l1 !! j1 = Some a1 → l1 !! j2 = Some a2 →
    R (f a1 (f a2 b)) (f a2 (f a1 b))) →
  l1 ≡ₚ l2 → R (foldr f b l1) (foldr f b l2).
Proof.
  intros Hf'. induction 1 as [|x l1 l2 _ IH|x y l|l1 l2 l3 Hl12 IH _ IH']; simpl.
  - done.
  - apply Hf, IH; eauto.
  - apply (Hf' 0 _ 1); eauto.
  - etrans; [eapply IH, Hf'|].
    apply IH'; intros j1 a1 j2 a2 b' ???.
    symmetry in Hl12; apply Permutation_inj in Hl12 as [_ (g&?&Hg)].
    apply (Hf' (g j1) _ (g j2)); [naive_solver|by rewrite <-Hg..].
Qed.

Lemma foldr_permutation_proper {A B} (R : relation B) `{!PreOrder R}
    (f : A → B → B) (b : B) `{!∀ x, Proper (R ==> R) (f x)}
    (Hf : ∀ a1 a2 b, R (f a1 (f a2 b)) (f a2 (f a1 b))) :
  Proper ((≡ₚ) ==> R) (foldr f b).
Proof. intros l1 l2 Hl. apply foldr_permutation; auto. Qed.

Global Instance foldr_permutation_proper' {A} (R : relation A) `{!PreOrder R}
    (f : A → A → A) (a : A) `{!∀ a, Proper (R ==> R) (f a), !Assoc R f, !Comm R f} :
  Proper ((≡ₚ) ==> R) (foldr f a).
Proof.
  apply (foldr_permutation_proper R f); [solve_proper|].
  assert (Proper (R ==> R ==> R) f).
  { intros a1 a2 Ha b1 b2 Hb. by rewrite Hb, (comm f a1), Ha, (comm f). }
  intros a1 a2 b.
  by rewrite (assoc f), (comm f _ b), (assoc f), (comm f b), (comm f _ a2).
Qed.

Lemma foldr_cons_permute_strong {A B} (R : relation B) `{!PreOrder R}
    (f : A → B → B) (b : B) `{!∀ a, Proper (R ==> R) (f a)} x l :
  (∀ j1 a1 j2 a2 b,
    j1 ≠ j2 → (x :: l) !! j1 = Some a1 → (x :: l) !! j2 = Some a2 →
    R (f a1 (f a2 b)) (f a2 (f a1 b))) →
  R (foldr f b (x :: l)) (foldr f (f x b) l).
Proof.
  intros. rewrite <-foldr_snoc.
  apply (foldr_permutation _ f b); [done|]. by rewrite Permutation_app_comm.
Qed.
Lemma foldr_cons_permute {A} (f : A → A → A) (a : A) x l :
  Assoc (=) f →
  Comm (=) f →
  foldr f a (x :: l) = foldr f (f x a) l.
Proof.
  intros. apply (foldr_cons_permute_strong (=) f a).
  intros j1 a1 j2 a2 b _ _ _. by rewrite !(assoc_L f), (comm_L f a1).
Qed.

(** The following lemma shows that folding over a list twice (using the result
of the first fold as input for the second fold) is equivalent to folding over
the list once, *if* the function is idempotent for the elements of the list
and does not care about the order in which elements are processed. *)
Lemma foldr_idemp_strong {A B} (R : relation B) `{!PreOrder R}
    (f : A → B → B) (b : B) `{!∀ x, Proper (R ==> R) (f x)} (l : list A) :
  (∀ j a b,
    (** This is morally idempotence for elements of [l] *)
    l !! j = Some a →
    R (f a (f a b)) (f a b)) →
  (∀ j1 a1 j2 a2 b,
    (** This is morally commutativity + associativity for elements of [l] *)
    j1 ≠ j2 → l !! j1 = Some a1 → l !! j2 = Some a2 →
    R (f a1 (f a2 b)) (f a2 (f a1 b))) →
  R (foldr f (foldr f b l) l) (foldr f b l).
Proof.
  intros Hfidem Hfcomm. induction l as [|x l IH]; simpl; [done|].
  trans (f x (f x (foldr f (foldr f b l) l))).
  { f_equiv. rewrite <-foldr_snoc, <-foldr_cons.
    apply (foldr_permutation (flip R) f).
    - solve_proper.
    - intros j1 a1 j2 a2 b' ???. by apply (Hfcomm j2 _ j1).
    - by rewrite <-Permutation_cons_append. }
  rewrite <-foldr_cons.
  trans (f x (f x (foldr f b l))); [|by apply (Hfidem 0)].
  simpl. do 2 f_equiv. apply IH.
  - intros j a b' ?. by apply (Hfidem (S j)).
  - intros j1 a1 j2 a2 b' ???. apply (Hfcomm (S j1) _ (S j2)); auto with lia.
Qed.
Lemma foldr_idemp {A} (f : A → A → A) (a : A) (l : list A) :
  IdemP (=) f →
  Assoc (=) f →
  Comm (=) f →
  foldr f (foldr f a l) l = foldr f a l.
Proof.
  intros. apply (foldr_idemp_strong (=) f a).
  - intros j a1 a2 _. by rewrite (assoc_L f), (idemp f).
  - intros x1 a1 x2 a2 a3 _ _ _. by rewrite !(assoc_L f), (comm_L f a1).
Qed.

Lemma foldr_comm_acc_strong {A B} (R : relation B) `{!PreOrder R}
    (f : A → B → B) (g : B → B) b l :
  (∀ x, Proper (R ==> R) (f x)) →
  (∀ x y, x ∈ l → R (f x (g y)) (g (f x y))) →
  R (foldr f (g b) l) (g (foldr f b l)).
Proof.
  intros ? Hcomm. induction l as [|x l IH]; simpl; [done|].
  rewrite <-Hcomm by eauto using list_elem_of_here.
  by rewrite IH by eauto using list_elem_of_further.
Qed.
Lemma foldr_comm_acc {A B} (f : A → B → B) (g : B → B) (b : B) l :
  (∀ x y, f x (g y) = g (f x y)) →
  foldr f (g b) l = g (foldr f b l).
Proof. intros. apply (foldr_comm_acc_strong _); [solve_proper|done]. Qed.

Lemma foldl_app {A B} (f : A → B → A) (l k : list B) (a : A) :
  foldl f a (l ++ k) = foldl f (foldl f a l) k.
Proof. revert a. induction l; simpl; auto. Qed.
Lemma foldl_snoc {A B} (f : A → B → A) (a : A) l x :
  foldl f a (l ++ [x]) = f (foldl f a l) x.
Proof. rewrite foldl_app. done. Qed.
Lemma foldl_fmap {A B C} (f : A → B → A) x (l : list C) g :
  foldl f x (g <$> l) = foldl (λ a b, f a (g b)) x l.
Proof. revert x. induction l; f_equal/=; auto. Qed.

(** ** Properties of the [zip_with] and [zip] functions *)
Global Instance zip_with_proper `{!Equiv A, !Equiv B, !Equiv C} :
  Proper (((≡) ==> (≡) ==> (≡)) ==>
          (≡@{list A}) ==> (≡@{list B}) ==> (≡@{list C})) zip_with.
Proof.
  intros f1 f2 Hf. induction 1; destruct 1; simpl; [constructor..|].
  f_equiv; [|by auto]. by apply Hf.
Qed.

Section zip_with.
  Context {A B C : Type} (f : A → B → C).
  Implicit Types x : A.
  Implicit Types y : B.
  Implicit Types l : list A.
  Implicit Types k : list B.

  Lemma zip_with_nil_l k : zip_with f [] k = [].
  Proof. done. Qed.
  Lemma zip_with_nil_r l : zip_with f l [] = [].
  Proof. by destruct l. Qed.
  Lemma zip_with_app l1 l2 k1 k2 :
    length l1 = length k1 →
    zip_with f (l1 ++ l2) (k1 ++ k2) = zip_with f l1 k1 ++ zip_with f l2 k2.
  Proof. rewrite <-Forall2_same_length. induction 1; f_equal/=; auto. Qed.
  Lemma zip_with_app_l l1 l2 k :
    zip_with f (l1 ++ l2) k
    = zip_with f l1 (take (length l1) k) ++ zip_with f l2 (drop (length l1) k).
  Proof.
    revert k. induction l1; intros [|??]; f_equal/=; auto. by destruct l2.
  Qed.
  Lemma zip_with_app_r l k1 k2 :
    zip_with f l (k1 ++ k2)
    = zip_with f (take (length k1) l) k1 ++ zip_with f (drop (length k1) l) k2.
  Proof. revert l. induction k1; intros [|??]; f_equal/=; auto. Qed.
  Lemma zip_with_flip l k : zip_with (flip f) k l = zip_with f l k.
  Proof. revert k. induction l; intros [|??]; f_equal/=; auto. Qed.
  Lemma zip_with_ext (g : A → B → C) l1 l2 k1 k2 :
    (∀ x y, f x y = g x y) → l1 = l2 → k1 = k2 →
    zip_with f l1 k1 = zip_with g l2 k2.
  Proof. intros ? <-<-. revert k1. by induction l1; intros [|??]; f_equal/=. Qed.
  Lemma Forall_zip_with_ext_l (g : A → B → C) l k1 k2 :
    Forall (λ x, ∀ y, f x y = g x y) l → k1 = k2 →
    zip_with f l k1 = zip_with g l k2.
  Proof. intros Hl <-. revert k1. by induction Hl; intros [|??]; f_equal/=. Qed.
  Lemma Forall_zip_with_ext_r (g : A → B → C) l1 l2 k :
    l1 = l2 → Forall (λ y, ∀ x, f x y = g x y) k →
    zip_with f l1 k = zip_with g l2 k.
  Proof. intros <- Hk. revert l1. by induction Hk; intros [|??]; f_equal/=. Qed.
  Lemma zip_with_fmap_l {D} (g : D → A) lD k :
    zip_with f (g <$> lD) k = zip_with (λ z, f (g z)) lD k.
  Proof. revert k. by induction lD; intros [|??]; f_equal/=. Qed.
  Lemma zip_with_fmap_r {D} (g : D → B) l kD :
    zip_with f l (g <$> kD) = zip_with (λ x z, f x (g z)) l kD.
  Proof. revert kD. by induction l; intros [|??]; f_equal/=. Qed.
  Lemma zip_with_nil_inv l k : zip_with f l k = [] → l = [] ∨ k = [].
  Proof. destruct l, k; intros; simplify_eq/=; auto. Qed.
  Lemma zip_with_cons_inv l k z lC :
    zip_with f l k = z :: lC →
    ∃ x y l' k', z = f x y ∧ lC = zip_with f l' k' ∧ l = x :: l' ∧ k = y :: k'.
  Proof. intros. destruct l, k; simplify_eq/=; repeat eexists. Qed.
  Lemma zip_with_app_inv l k lC1 lC2 :
    zip_with f l k = lC1 ++ lC2 →
    ∃ l1 k1 l2 k2, lC1 = zip_with f l1 k1 ∧ lC2 = zip_with f l2 k2 ∧
      l = l1 ++ l2 ∧ k = k1 ++ k2 ∧ length l1 = length k1.
  Proof.
    revert l k. induction lC1 as [|z lC1 IH]; simpl.
    { intros l k ?. by eexists [], [], l, k. }
    intros [|x l] [|y k] ?; simplify_eq/=.
    destruct (IH l k) as (l1&k1&l2&k2&->&->&->&->&?); [done |].
    exists (x :: l1), (y :: k1), l2, k2; simpl; auto with congruence.
  Qed.
  Lemma zip_with_inj `{!Inj2 (=) (=) (=) f} l1 l2 k1 k2 :
    length l1 = length k1 → length l2 = length k2 →
    zip_with f l1 k1 = zip_with f l2 k2 → l1 = l2 ∧ k1 = k2.
  Proof.
    rewrite <-!Forall2_same_length. intros Hl. revert l2 k2.
    induction Hl; intros ?? [] ?; f_equal; naive_solver.
  Qed.
  Lemma length_zip_with l k :
    length (zip_with f l k) = min (length l) (length k).
  Proof. revert k. induction l; intros [|??]; simpl; auto with lia. Qed.
  Lemma length_zip_with_l l k :
    length l ≤ length k → length (zip_with f l k) = length l.
  Proof. rewrite length_zip_with; lia. Qed.
  Lemma length_zip_with_l_eq l k :
    length l = length k → length (zip_with f l k) = length l.
  Proof. rewrite length_zip_with; lia. Qed.
  Lemma length_zip_with_r l k :
    length k ≤ length l → length (zip_with f l k) = length k.
  Proof. rewrite length_zip_with; lia. Qed.
  Lemma length_zip_with_r_eq l k :
    length k = length l → length (zip_with f l k) = length k.
  Proof. rewrite length_zip_with; lia. Qed.
  Lemma length_zip_with_same_l P l k :
    Forall2 P l k → length (zip_with f l k) = length l.
  Proof. induction 1; simpl; auto. Qed.
  Lemma length_zip_with_same_r P l k :
    Forall2 P l k → length (zip_with f l k) = length k.
  Proof. induction 1; simpl; auto. Qed.
  Lemma lookup_zip_with l k i :
    zip_with f l k !! i = (x ← l !! i; y ← k !! i; Some (f x y)).
  Proof.
    revert k i. induction l; intros [|??] [|?]; f_equal/=; auto.
    by destruct (_ !! _).
  Qed.
  Lemma lookup_total_zip_with `{!Inhabited A, !Inhabited B, !Inhabited C} l k i :
    i < length l → i < length k → zip_with f l k !!! i = f (l !!! i) (k !!! i).
  Proof.
    intros [x Hx]%lookup_lt_is_Some_2 [y Hy]%lookup_lt_is_Some_2.
    by rewrite !list_lookup_total_alt, lookup_zip_with, Hx, Hy.
  Qed.
  Lemma lookup_zip_with_Some l k i z :
    zip_with f l k !! i = Some z
    ↔ ∃ x y, z = f x y ∧ l !! i = Some x ∧ k !! i = Some y.
  Proof. rewrite lookup_zip_with. destruct (l !! i), (k !! i); naive_solver. Qed.
  Lemma lookup_zip_with_None l k i  :
    zip_with f l k !! i = None
    ↔ l !! i = None ∨ k !! i = None.
  Proof. rewrite lookup_zip_with. destruct (l !! i), (k !! i); naive_solver. Qed.
  Lemma insert_zip_with l k i x y :
    <[i:=f x y]>(zip_with f l k) = zip_with f (<[i:=x]>l) (<[i:=y]>k).
  Proof. revert i k. induction l; intros [|?] [|??]; f_equal/=; auto. Qed.
  Lemma fmap_zip_with_l (g : C → A) l k :
    (∀ x y, g (f x y) = x) → length l ≤ length k → g <$> zip_with f l k = l.
  Proof. revert k. induction l; intros [|??] ??; f_equal/=; auto with lia. Qed.
  Lemma fmap_zip_with_r (g : C → B) l k :
    (∀ x y, g (f x y) = y) → length k ≤ length l → g <$> zip_with f l k = k.
  Proof. revert l. induction k; intros [|??] ??; f_equal/=; auto with lia. Qed.
  Lemma zip_with_zip l k : zip_with f l k = uncurry f <$> zip l k.
  Proof. revert k. by induction l; intros [|??]; f_equal/=. Qed.
  Lemma zip_with_fst_snd lk : zip_with f (lk.*1) (lk.*2) = uncurry f <$> lk.
  Proof. by induction lk as [|[]]; f_equal/=. Qed.
  Lemma zip_with_replicate n x y :
    zip_with f (replicate n x) (replicate n y) = replicate n (f x y).
  Proof. by induction n; f_equal/=. Qed.
  Lemma zip_with_replicate_l n x k :
    length k ≤ n → zip_with f (replicate n x) k = f x <$> k.
  Proof. revert n. induction k; intros [|?] ?; f_equal/=; auto with lia. Qed.
  Lemma zip_with_replicate_r n y l :
    length l ≤ n → zip_with f l (replicate n y) = flip f y <$> l.
  Proof. revert n. induction l; intros [|?] ?; f_equal/=; auto with lia. Qed.
  Lemma zip_with_replicate_r_eq n y l :
    length l = n → zip_with f l (replicate n y) = flip f y <$> l.
  Proof. intros; apply zip_with_replicate_r; lia. Qed.
  Lemma zip_with_take n l k :
    take n (zip_with f l k) = zip_with f (take n l) (take n k).
  Proof. revert n k. by induction l; intros [|?] [|??]; f_equal/=. Qed.
  Lemma zip_with_drop n l k :
    drop n (zip_with f l k) = zip_with f (drop n l) (drop n k).
  Proof.
    revert n k. induction l; intros [] []; f_equal/=; auto using zip_with_nil_r.
  Qed.
  Lemma zip_with_take_l' n l k :
    length l `min` length k ≤ n → zip_with f (take n l) k = zip_with f l k.
  Proof. revert n k. induction l; intros [] [] ?; f_equal/=; auto with lia. Qed.
  Lemma zip_with_take_l l k :
    zip_with f (take (length k) l) k = zip_with f l k.
  Proof. apply zip_with_take_l'; lia. Qed.
  Lemma zip_with_take_r' n l k :
    length l `min` length k ≤ n → zip_with f l (take n k) = zip_with f l k.
  Proof. revert n k. induction l; intros [] [] ?; f_equal/=; auto with lia. Qed.
  Lemma zip_with_take_r l k :
    zip_with f l (take (length l) k) = zip_with f l k.
  Proof. apply zip_with_take_r'; lia. Qed.
  Lemma zip_with_take_both' n1 n2 l k :
    length l `min` length k ≤ n1 → length l `min` length k ≤ n2 →
    zip_with f (take n1 l) (take n2 k) = zip_with f l k.
  Proof.
    intros.
    rewrite zip_with_take_l'; [apply zip_with_take_r' | rewrite length_take]; lia.
  Qed.
  Lemma zip_with_take_both l k :
    zip_with f (take (length k) l) (take (length l) k) = zip_with f l k.
  Proof. apply zip_with_take_both'; lia. Qed.
  Lemma Forall_zip_with_fst (P : A → Prop) (Q : C → Prop) l k :
    Forall P l → Forall (λ y, ∀ x, P x → Q (f x y)) k →
    Forall Q (zip_with f l k).
  Proof. intros Hl. revert k. induction Hl; destruct 1; simpl in *; auto. Qed.
  Lemma Forall_zip_with_snd (P : B → Prop) (Q : C → Prop) l k :
    Forall (λ x, ∀ y, P y → Q (f x y)) l → Forall P k →
    Forall Q (zip_with f l k).
  Proof. intros Hl. revert k. induction Hl; destruct 1; simpl in *; auto. Qed.

  Lemma elem_of_lookup_zip_with_1 l k (z : C) :
    z ∈ zip_with f l k → ∃ i x y, z = f x y ∧ l !! i = Some x ∧ k !! i = Some y.
  Proof.
    intros [i Hin]%list_elem_of_lookup. rewrite lookup_zip_with in Hin.
    simplify_option_eq; naive_solver.
  Qed.

  Lemma elem_of_lookup_zip_with_2 l k x y (z : C) i :
    l !! i = Some x → k !! i = Some y → f x y ∈ zip_with f l k.
  Proof.
    intros Hl Hk. rewrite list_elem_of_lookup.
    exists i. by rewrite lookup_zip_with, Hl, Hk.
  Qed.

  Lemma elem_of_lookup_zip_with l k (z : C) :
    z ∈ zip_with f l k ↔ ∃ i x y, z = f x y ∧ l !! i = Some x ∧ k !! i = Some y.
  Proof.
    naive_solver eauto using
                 elem_of_lookup_zip_with_1, elem_of_lookup_zip_with_2.
  Qed.

  Lemma elem_of_zip_with l k (z : C) :
    z ∈ zip_with f l k → ∃ x y, z = f x y ∧ x ∈ l ∧ y ∈ k.
  Proof.
    intros ?%elem_of_lookup_zip_with.
    naive_solver eauto using list_elem_of_lookup_2.
  Qed.

End zip_with.

Lemma zip_with_diag {A C} (f : A → A → C) l :
  zip_with f l l = (λ x, f x x) <$> l.
Proof. induction l as [|?? IH]; [done|]. simpl. rewrite IH. done. Qed.

(** The lemmas below are outside the section so the [_r] version can be derived
from the [_l] version. *)
Lemma NoDup_zip_with_l_strong {A B C} (f : A → B → C) l k :
  (∀ i1 i2 x1 x2 y1 y2,
    l !! i1 = Some x1 → k !! i1 = Some y1 →
    l !! i2 = Some x2 → k !! i2 = Some y2 →
    f x1 y1 = f x2 y2 → x1 = x2) →
  NoDup l →
  NoDup (zip_with f l k).
Proof.
  intros Hinj.
  induction 1 as [|x l Hxl Hl IHl] in k, Hinj |- *; [constructor|].
  destruct k as [|y k]; simpl; [by constructor|]. constructor.
  - intros (i & x' & y' & Hf & Hx & Hy)%elem_of_lookup_zip_with_1.
    assert (x = x') as -> by (by eapply (Hinj 0 (S i))).
    by apply list_elem_of_lookup_2 in Hx.
  - apply IHl. intros i1 i2 x1 x2 y1 y2 Hl1 Hk1 Hl2 Hk2 Hf.
    by eapply (Hinj (S i1) (S i2)).
Qed.
Lemma NoDup_zip_with_r_strong {A B C} (f : A → B → C) l k :
  (∀ i1 i2 x1 x2 y1 y2,
    l !! i1 = Some x1 → k !! i1 = Some y1 →
    l !! i2 = Some x2 → k !! i2 = Some y2 →
    f x1 y1 = f x2 y2 → y1 = y2) →
  NoDup k →
  NoDup (zip_with f l k).
Proof.
  intros Hinj. rewrite <-zip_with_flip.
  apply NoDup_zip_with_l_strong. naive_solver.
Qed.

Lemma NoDup_zip_with_l {A B C} (f : A → B → C) `{!Inj2 (=) (=) (=) f} l k :
  NoDup l → NoDup (zip_with f l k).
Proof. apply NoDup_zip_with_l_strong. naive_solver. Qed.
Lemma NoDup_zip_with_r {A B C} (f : A → B → C) `{!Inj2 (=) (=) (=) f} l k :
  NoDup k → NoDup (zip_with f l k).
Proof. apply NoDup_zip_with_r_strong. naive_solver. Qed.

Section zip.
  Context {A B : Type}.
  Implicit Types l : list A.
  Implicit Types k : list B.

  Lemma zip_nil_l k : zip [] k =@{list (A * B)} [].
  Proof. apply zip_with_nil_l. Qed.
  Lemma zip_nil_r l : zip l [] =@{list (A * B)} [].
  Proof. apply zip_with_nil_r. Qed.

  Lemma fst_zip l k : length l ≤ length k → (zip l k).*1 = l.
  Proof. by apply fmap_zip_with_l. Qed.
  Lemma snd_zip l k : length k ≤ length l → (zip l k).*2 = k.
  Proof. by apply fmap_zip_with_r. Qed.
  Lemma zip_fst_snd (lk : list (A * B)) : zip (lk.*1) (lk.*2) = lk.
  Proof. by induction lk as [|[]]; f_equal/=. Qed.
  Lemma Forall2_fst P l1 l2 k1 k2 :
    length l2 = length k2 → Forall2 P l1 k1 →
    Forall2 (λ x y, P (x.1) (y.1)) (zip l1 l2) (zip k1 k2).
  Proof.
    rewrite <-Forall2_same_length. intros Hlk2 Hlk1. revert l2 k2 Hlk2.
    induction Hlk1; intros ?? [|??????]; simpl; auto.
  Qed.
  Lemma Forall2_snd P l1 l2 k1 k2 :
    length l1 = length k1 → Forall2 P l2 k2 →
    Forall2 (λ x y, P (x.2) (y.2)) (zip l1 l2) (zip k1 k2).
  Proof.
    rewrite <-Forall2_same_length. intros Hlk1 Hlk2. revert l1 k1 Hlk1.
    induction Hlk2; intros ?? [|??????]; simpl; auto.
  Qed.

  Lemma elem_of_zip_l x1 x2 l k :
    (x1, x2) ∈ zip l k → x1 ∈ l.
  Proof. intros ?%elem_of_zip_with. naive_solver. Qed.
  Lemma elem_of_zip_r x1 x2 l k :
    (x1, x2) ∈ zip l k → x2 ∈ k.
  Proof. intros ?%elem_of_zip_with. naive_solver. Qed.
  Lemma length_zip l k :
    length (zip l k) = min (length l) (length k).
  Proof. by rewrite length_zip_with. Qed.
  Lemma zip_nil_inv l k :
    zip l k = [] → l = [] ∨ k = [].
  Proof. intros. by eapply zip_with_nil_inv. Qed.
  Lemma lookup_zip_Some l k i x y :
    zip l k !! i = Some (x, y) ↔ l !! i = Some x ∧ k !! i = Some y.
  Proof. rewrite lookup_zip_with_Some. naive_solver. Qed.
  Lemma lookup_zip_None l k i :
    zip l k !! i = None ↔ l !! i = None ∨ k !! i = None.
  Proof. by rewrite lookup_zip_with_None. Qed.

  Lemma prod_map_zip {A' B'} (f : A → A') (g : B → B') l k :
    prod_map f g <$> zip l k = zip (f <$> l) (g <$> k).
  Proof.
    rewrite zip_with_fmap_l, zip_with_fmap_r, (zip_with_zip (λ x z, (f x, g z))).
    apply list_fmap_ext. by intros i [x1 x2] _.
  Qed.

  Lemma NoDup_zip_l l k : NoDup l → NoDup (zip l k).
  Proof. apply (NoDup_zip_with_l _). Qed.
  Lemma NoDup_zip_r l k : NoDup k → NoDup (zip l k).
  Proof. apply (NoDup_zip_with_r _). Qed.
End zip.

Lemma zip_diag {A} (l : list A) :
  zip l l = (λ x, (x, x)) <$> l.
Proof. apply zip_with_diag. Qed.

Lemma elem_of_zipped_map {A B} (f : list A → list A → A → B) l k x :
  x ∈ zipped_map f l k ↔
    ∃ k' k'' y, k = k' ++ [y] ++ k'' ∧ x = f (reverse k' ++ l) k'' y.
Proof.
  split.
  - revert l. induction k as [|z k IH]; simpl; intros l; inv 1.
    { by eexists [], k, z. }
    destruct (IH (z :: l)) as (k'&k''&y&->&->); [done |].
    eexists (z :: k'), k'', y. by rewrite reverse_cons, <-(assoc_L (++)).
  - intros (k'&k''&y&->&->). revert l. induction k' as [|z k' IH]; [by left|].
    intros l; right. by rewrite reverse_cons, <-!(assoc_L (++)).
Qed.
Section zipped_list_ind.
  Context {A} (P : list A → list A → Prop).
  Context (Pnil : ∀ l, P l []) (Pcons : ∀ l k x, P (x :: l) k → P l (x :: k)).
  Fixpoint zipped_list_ind l k : P l k :=
    match k with
    | [] => Pnil _ | x :: k => Pcons _ _ _ (zipped_list_ind (x :: l) k)
    end.
End zipped_list_ind.
Lemma zipped_Forall_app {A} (P : list A → list A → A → Prop) l k k' :
  zipped_Forall P l (k ++ k') → zipped_Forall P (reverse k ++ l) k'.
Proof.
  revert l. induction k as [|x k IH]; simpl; [done |].
  inv 1. rewrite reverse_cons, <-(assoc_L (++)). by apply IH.
Qed.

End list.
