From Coq Require Export Permutation.
From stdpp Require Export numbers base option list_basics list_relations list_monad.
From stdpp Require Import options.

Module Export list.

(** * Reflection over lists *)
(** We define a simple data structure [rlist] to capture a syntactic
representation of lists consisting of constants, applications and the nil list.
Note that we represent [(x ::.)] as [rapp (rnode [x])]. For now, we abstract
over the type of constants, but later we use [nat]s and a list representing
a corresponding environment. *)
Inductive rlist (A : Type) :=
  rnil : rlist A | rnode : A → rlist A | rapp : rlist A → rlist A → rlist A.
Global Arguments rnil {_} : assert.
Global Arguments rnode {_} _ : assert.
Global Arguments rapp {_} _ _ : assert.

Module rlist.
Fixpoint to_list {A} (t : rlist A) : list A :=
  match t with
  | rnil => [] | rnode l => [l] | rapp t1 t2 => to_list t1 ++ to_list t2
  end.
Notation env A := (list (list A)) (only parsing).
Definition eval {A} (E : env A) : rlist nat → list A :=
  fix go t :=
  match t with
  | rnil => []
  | rnode i => default [] (E !! i)
  | rapp t1 t2 => go t1 ++ go t2
  end.

(** A simple quoting mechanism using type classes. [QuoteLookup E1 E2 x i]
means: starting in environment [E1], look up the index [i] corresponding to the
constant [x]. In case [x] has a corresponding index [i] in [E1], the original
environment is given back as [E2]. Otherwise, the environment [E2] is extended
with a binding [i] for [x]. *)
Section quote_lookup.
  Context {A : Type}.
  Class QuoteLookup (E1 E2 : list A) (x : A) (i : nat) := {}.
  Global Instance quote_lookup_here E x : QuoteLookup (x :: E) (x :: E) x 0 := {}.
  Global Instance quote_lookup_end x : QuoteLookup [] [x] x 0 := {}.
  Global Instance quote_lookup_further E1 E2 x i y :
    QuoteLookup E1 E2 x i → QuoteLookup (y :: E1) (y :: E2) x (S i) | 1000 := {}.
End quote_lookup.

Section quote.
  Context {A : Type}.
  Class Quote (E1 E2 : env A) (l : list A) (t : rlist nat) := {}.
  Global Instance quote_nil E1 : Quote E1 E1 [] rnil := {}.
  Global Instance quote_node E1 E2 l i:
    QuoteLookup E1 E2 l i → Quote E1 E2 l (rnode i) | 1000 := {}.
  Global Instance quote_cons E1 E2 E3 x l i t :
    QuoteLookup E1 E2 [x] i →
    Quote E2 E3 l t → Quote E1 E3 (x :: l) (rapp (rnode i) t) := {}.
  Global Instance quote_app E1 E2 E3 l1 l2 t1 t2 :
    Quote E1 E2 l1 t1 → Quote E2 E3 l2 t2 → Quote E1 E3 (l1 ++ l2) (rapp t1 t2) := {}.
End quote.

Section eval.
  Context {A} (E : env A).

  Lemma eval_alt t : eval E t = to_list t ≫= default [] ∘ (E !!.).
  Proof.
    induction t; csimpl.
    - done.
    - by rewrite (right_id_L [] (++)).
    - rewrite bind_app. by f_equal.
  Qed.
  Lemma eval_eq t1 t2 : to_list t1 = to_list t2 → eval E t1 = eval E t2.
  Proof. intros Ht. by rewrite !eval_alt, Ht. Qed.
  Lemma eval_Permutation t1 t2 :
    to_list t1 ≡ₚ to_list t2 → eval E t1 ≡ₚ eval E t2.
  Proof. intros Ht. by rewrite !eval_alt, Ht. Qed.
  Lemma eval_submseteq t1 t2 :
    to_list t1 ⊆+ to_list t2 → eval E t1 ⊆+ eval E t2.
  Proof. intros Ht. by rewrite !eval_alt, Ht. Qed.
End eval.
End rlist.

(** * Tactics *)
Ltac quote_Permutation :=
  match goal with
  | |- ?l1 ≡ₚ ?l2 =>
    match type of (_ : rlist.Quote [] _ l1 _) with rlist.Quote _ ?E2 _ ?t1 =>
    match type of (_ : rlist.Quote E2 _ l2 _) with rlist.Quote _ ?E3 _ ?t2 =>
      change (rlist.eval E3 t1 ≡ₚ rlist.eval E3 t2)
    end end
  end.
Ltac solve_Permutation :=
  quote_Permutation; apply rlist.eval_Permutation;
  compute_done.

Ltac quote_submseteq :=
  match goal with
  | |- ?l1 ⊆+ ?l2 =>
    match type of (_ : rlist.Quote [] _ l1 _) with rlist.Quote _ ?E2 _ ?t1 =>
    match type of (_ : rlist.Quote E2 _ l2 _) with rlist.Quote _ ?E3 _ ?t2 =>
      change (rlist.eval E3 t1 ⊆+ rlist.eval E3 t2)
    end end
  end.
Ltac solve_submseteq :=
  quote_submseteq; apply rlist.eval_submseteq;
  compute_done.

Ltac decompose_list_elem_of := repeat
  match goal with
  | H : ?x ∈ [] |- _ => by destruct (not_elem_of_nil x)
  | H : _ ∈ _ :: _ |- _ => apply elem_of_cons in H; destruct H
  | H : _ ∈ _ ++ _ |- _ => apply elem_of_app in H; destruct H
  end.
Ltac solve_length :=
  simplify_eq/=;
  repeat (rewrite length_fmap || rewrite length_app);
  repeat match goal with
  | H : _ =@{list _} _ |- _ => apply (f_equal length) in H
  | H : Forall2 _ _ _ |- _ => apply Forall2_length in H
  | H : context[length (_ <$> _)] |- _ => rewrite length_fmap in H
  end; done || congruence.
Ltac simplify_list_eq ::= repeat
  match goal with
  | _ => progress simplify_eq/=
  | H : [?x] !! ?i = Some ?y |- _ =>
    destruct i; [change (Some x = Some y) in H | discriminate]
  | H : _ <$> _ = [] |- _ => apply fmap_nil_inv in H
  | H : [] = _ <$> _ |- _ => symmetry in H; apply fmap_nil_inv in H
  | H : zip_with _ _ _ = [] |- _ => apply zip_with_nil_inv in H; destruct H
  | H : [] = zip_with _ _ _ |- _ => symmetry in H
  | |- context [(_ ++ _) ++ _] => rewrite <-(assoc_L (++))
  | H : context [(_ ++ _) ++ _] |- _ => rewrite <-(assoc_L (++)) in H
  | H : context [_ <$> (_ ++ _)] |- _ => rewrite fmap_app in H
  | |- context [_ <$> (_ ++ _)]  => rewrite fmap_app
  | |- context [_ ++ []] => rewrite (right_id_L [] (++))
  | H : context [_ ++ []] |- _ => rewrite (right_id_L [] (++)) in H
  | |- context [take _ (_ <$> _)] => rewrite <-fmap_take
  | H : context [take _ (_ <$> _)] |- _ => rewrite <-fmap_take in H
  | |- context [drop _ (_ <$> _)] => rewrite <-fmap_drop
  | H : context [drop _ (_ <$> _)] |- _ => rewrite <-fmap_drop in H
  | H : _ ++ _ = _ ++ _ |- _ =>
    repeat (rewrite <-app_comm_cons in H || rewrite <-(assoc_L (++)) in H);
    apply app_inj_1 in H; [destruct H|solve_length]
  | H : _ ++ _ = _ ++ _ |- _ =>
    repeat (rewrite app_comm_cons in H || rewrite (assoc_L (++)) in H);
    apply app_inj_2 in H; [destruct H|solve_length]
  | |- context [zip_with _ (_ ++ _) (_ ++ _)] =>
    rewrite zip_with_app by solve_length
  | |- context [take _ (_ ++ _)] => rewrite take_app_length' by solve_length
  | |- context [drop _ (_ ++ _)] => rewrite drop_app_length' by solve_length
  | H : context [zip_with _ (_ ++ _) (_ ++ _)] |- _ =>
    rewrite zip_with_app in H by solve_length
  | H : context [take _ (_ ++ _)] |- _ =>
    rewrite take_app_length' in H by solve_length
  | H : context [drop _ (_ ++ _)] |- _ =>
    rewrite drop_app_length' in H by solve_length
  | H : ?l !! ?i = _, H2 : context [(_ <$> ?l) !! ?i] |- _ =>
     rewrite list_lookup_fmap, H in H2
  end.
Ltac decompose_Forall_hyps :=
  repeat match goal with
  | H : Forall _ [] |- _ => clear H
  | H : Forall _ (_ :: _) |- _ => rewrite Forall_cons in H; destruct H
  | H : Forall _ (_ ++ _) |- _ => rewrite Forall_app in H; destruct H
  | H : Forall2 _ [] [] |- _ => clear H
  | H : Forall2 _ (_ :: _) [] |- _ => destruct (Forall2_cons_nil_inv _ _ _ H)
  | H : Forall2 _ [] (_ :: _) |- _ => destruct (Forall2_nil_cons_inv _ _ _ H)
  | H : Forall2 _ [] ?k |- _ => apply Forall2_nil_inv_l in H
  | H : Forall2 _ ?l [] |- _ => apply Forall2_nil_inv_r in H
  | H : Forall2 _ (_ :: _) (_ :: _) |- _ =>
    apply Forall2_cons_1 in H; destruct H
  | H : Forall2 _ (_ :: _) ?k |- _ =>
    let k_hd := fresh k "_hd" in let k_tl := fresh k "_tl" in
    apply Forall2_cons_inv_l in H; destruct H as (k_hd&k_tl&?&?&->);
    rename k_tl into k
  | H : Forall2 _ ?l (_ :: _) |- _ =>
    let l_hd := fresh l "_hd" in let l_tl := fresh l "_tl" in
    apply Forall2_cons_inv_r in H; destruct H as (l_hd&l_tl&?&?&->);
    rename l_tl into l
  | H : Forall2 _ (_ ++ _) ?k |- _ =>
    let k1 := fresh k "_1" in let k2 := fresh k "_2" in
    apply Forall2_app_inv_l in H; destruct H as (k1&k2&?&?&->)
  | H : Forall2 _ ?l (_ ++ _) |- _ =>
    let l1 := fresh l "_1" in let l2 := fresh l "_2" in
    apply Forall2_app_inv_r in H; destruct H as (l1&l2&?&?&->)
  | _ => progress simplify_eq/=
  | H : Forall3 _ _ (_ :: _) _ |- _ =>
    apply Forall3_cons_inv_m in H; destruct H as (?&?&?&?&?&?&?&?)
  | H : Forall2 _ (_ :: _) ?k |- _ =>
    apply Forall2_cons_inv_l in H; destruct H as (?&?&?&?&?)
  | H : Forall2 _ ?l (_ :: _) |- _ =>
    apply Forall2_cons_inv_r in H; destruct H as (?&?&?&?&?)
  | H : Forall2 _ (_ ++ _) (_ ++ _) |- _ =>
    apply Forall2_app_inv in H; [destruct H|solve_length]
  | H : Forall2 _ ?l (_ ++ _) |- _ =>
    apply Forall2_app_inv_r in H; destruct H as (?&?&?&?&?)
  | H : Forall2 _ (_ ++ _) ?k |- _ =>
    apply Forall2_app_inv_l in H; destruct H as (?&?&?&?&?)
  | H : Forall3 _ _ (_ ++ _) _ |- _ =>
    apply Forall3_app_inv_m in H; destruct H as (?&?&?&?&?&?&?&?)
  | H : Forall ?P ?l, H1 : ?l !! _ = Some ?x |- _ =>
    (* to avoid some stupid loops, not fool proof *)
    unless (P x) by auto using Forall_app_2, Forall_nil_2;
    let E := fresh in
    assert (P x) as E by (apply (Forall_lookup_1 P _ _ _ H H1)); lazy beta in E
  | H : Forall2 ?P ?l ?k |- _ =>
    match goal with
    | H1 : l !! ?i = Some ?x, H2 : k !! ?i = Some ?y |- _ =>
      unless (P x y) by done; let E := fresh in
      assert (P x y) as E by (by apply (Forall2_lookup_lr P l k i x y));
      lazy beta in E
    | H1 : l !! ?i = Some ?x |- _ =>
      try (match goal with _ : k !! i = Some _ |- _ => fail 2 end);
      destruct (Forall2_lookup_l P _ _ _ _ H H1) as (?&?&?)
    | H2 : k !! ?i = Some ?y |- _ =>
      try (match goal with _ : l !! i = Some _ |- _ => fail 2 end);
      destruct (Forall2_lookup_r P _ _ _ _ H H2) as (?&?&?)
    end
  | H : Forall3 ?P ?l ?l' ?k |- _ =>
    lazymatch goal with
    | H1:l !! ?i = Some ?x, H2:l' !! ?i = Some ?y, H3:k !! ?i = Some ?z |- _ =>
      unless (P x y z) by done; let E := fresh in
      assert (P x y z) as E by (by apply (Forall3_lookup_lmr P l l' k i x y z));
      lazy beta in E
    | H1 : l !! _ = Some ?x |- _ =>
      destruct (Forall3_lookup_l P _ _ _ _ _ H H1) as (?&?&?&?&?)
    | H2 : l' !! _ = Some ?y |- _ =>
      destruct (Forall3_lookup_m P _ _ _ _ _ H H2) as (?&?&?&?&?)
    | H3 : k !! _ = Some ?z |- _ =>
      destruct (Forall3_lookup_r P _ _ _ _ _ H H3) as (?&?&?&?&?)
    end
  end.
Ltac list_simplifier :=
  simplify_eq/=;
  repeat match goal with
  | _ => progress decompose_Forall_hyps
  | _ => progress simplify_list_eq
  | H : _ <$> _ = _ :: _ |- _ =>
    apply fmap_cons_inv in H; destruct H as (?&?&?&?&?)
  | H : _ :: _ = _ <$> _ |- _ => symmetry in H
  | H : _ <$> _ = _ ++ _ |- _ =>
    apply fmap_app_inv in H; destruct H as (?&?&?&?&?)
  | H : _ ++ _ = _ <$> _ |- _ => symmetry in H
  | H : zip_with _ _ _ = _ :: _ |- _ =>
    apply zip_with_cons_inv in H; destruct H as (?&?&?&?&?&?&?&?)
  | H : _ :: _ = zip_with _ _ _ |- _ => symmetry in H
  | H : zip_with _ _ _ = _ ++ _ |- _ =>
    apply zip_with_app_inv in H; destruct H as (?&?&?&?&?&?&?&?&?)
  | H : _ ++ _ = zip_with _ _ _ |- _ => symmetry in H
  end.
Ltac decompose_Forall := repeat
  match goal with
  | |- Forall _ _ => by apply Forall_true
  | |- Forall _ [] => constructor
  | |- Forall _ (_ :: _) => constructor
  | |- Forall _ (_ ++ _) => apply Forall_app_2
  | |- Forall _ (_ <$> _) => apply Forall_fmap
  | |- Forall _ (_ ≫= _) => apply Forall_bind
  | |- Forall2 _ _ _ => apply Forall_Forall2_diag
  | |- Forall2 _ [] [] => constructor
  | |- Forall2 _ (_ :: _) (_ :: _) => constructor
  | |- Forall2 _ (_ ++ _) (_ ++ _) => first
    [ apply Forall2_app; [by decompose_Forall |]
    | apply Forall2_app; [| by decompose_Forall]]
  | |- Forall2 _ (_ <$> _) _ => apply Forall2_fmap_l
  | |- Forall2 _ _ (_ <$> _) => apply Forall2_fmap_r
  | _ => progress decompose_Forall_hyps
  | H : Forall _ (_ <$> _) |- _ => rewrite Forall_fmap in H
  | H : Forall _ (_ ≫= _) |- _ => rewrite Forall_bind in H
  | |- Forall _ _ =>
    apply Forall_lookup_2; intros ???; progress decompose_Forall_hyps
  | |- Forall2 _ _ _ =>
    apply Forall2_same_length_lookup_2; [solve_length|];
    intros ?????; progress decompose_Forall_hyps
  end.

(** The [simplify_suffix] tactic removes [suffix] hypotheses that are
tautologies, and simplifies [suffix] hypotheses involving [(::)] and
[(++)]. *)
Ltac simplify_suffix := repeat
  match goal with
  | H : suffix (_ :: _) _ |- _ => destruct (suffix_cons_not _ _ H)
  | H : suffix (_ :: _) [] |- _ => apply suffix_nil_inv in H
  | H : suffix (_ ++ _) (_ ++ _) |- _ => apply suffix_app_inv in H
  | H : suffix (_ :: _) (_ :: _) |- _ =>
    destruct (suffix_cons_inv _ _ _ _ H); clear H
  | H : suffix ?x ?x |- _ => clear H
  | H : suffix ?x (_ :: ?x) |- _ => clear H
  | H : suffix ?x (_ ++ ?x) |- _ => clear H
  | _ => progress simplify_eq/=
  end.

(** The [solve_suffix] tactic tries to solve goals involving [suffix]. It
uses [simplify_suffix] to simplify hypotheses and tries to solve [suffix]
conclusions. This tactic either fails or proves the goal. *)
Ltac solve_suffix := by intuition (repeat
  match goal with
  | _ => done
  | _ => progress simplify_suffix
  | |- suffix [] _ => apply suffix_nil
  | |- suffix _ _ => reflexivity
  | |- suffix _ (_ :: _) => apply suffix_cons_r
  | |- suffix _ (_ ++ _) => apply suffix_app_r
  | H : suffix _ _ → False |- _ => destruct H
  end).

End list.
