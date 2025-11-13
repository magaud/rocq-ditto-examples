From stdpp Require Import strings sorting.
From Coq Require Ascii.

(** Check that the string notation works without [%string]. *)
Check "foo".

(** And also with [%string], which should not be pretty printed) *)
Check "foo"%string.

(** Check that importing [strings] does not override notations for [nat] and
[list]. *)
Check (10 =? 10).
Check ([10] ++ [12]).

Check ("foo" =? "bar")%string.

(** Check that append on strings is pretty printed correctly, and not as
[(_ ++ _)%string]. *)
Check ("foo" +:+ "bar").

(** Should print as [String.app] *)
Check String.app.

(** Test notations and type class instances for [≤] *)
Check ("a" ≤ "b")%string.
Compute bool_decide ("a" ≤ "b")%string.

(** Make sure [merge_sort] computes (which implies the [Decision] instances
are correct. *)
Compute merge_sort (≤)%string ["b"; "a"; "c"; "A"].

(** And that we can prove it actually sorts (which implies the order-related
instances are correct. *)
Lemma test_merge_sort l :
  StronglySorted (≤)%string (merge_sort (≤)%string l) ∧
  merge_sort (≤)%string l ≡ₚ l.
Proof.
  split.
  - apply (StronglySorted_merge_sort _).
  - apply merge_sort_Permutation.
Qed.
