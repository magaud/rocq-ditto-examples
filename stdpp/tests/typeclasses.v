From stdpp Require Import strings.

(* Should follow from [forall_inhabited] *)
Lemma impl_inhabited {A} `{Inhabited B} : Inhabited (A → B).
Proof. apply _. Qed.

Lemma tc_simpl_test_lemma (P : nat → Prop) x y :
  TCSimpl x y →
  P x → P y.
Proof. by intros ->%TCSimpl_eq. Qed.

Check "tc_simpl_test".
Lemma tc_simpl_test (P : nat → Prop) y : P (5 + S y).
Proof.
  apply (tc_simpl_test_lemma _ _ _ _). (* would be nicer with ssr [apply:] *)
  Show.
Abort.
