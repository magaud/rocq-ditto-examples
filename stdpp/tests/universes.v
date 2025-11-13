From stdpp Require Import gmap.

(** Make sure that [gmap] and [gset] do not bump the universe. Since [Z : Set],
the types [gmap Z Z] and [gset Z] should have universe [Set] too. *)

Check (gmap Z Z : Set).
Check (gset Z : Set).

(** Regression test for https://gitlab.mpi-sws.org/iris/stdpp/-/issues/207.
At least [gmap] should be imported to properly test this. *)
(* TODO (needs Rocq >= 9.0) *)
(* Definition test A := list (relation A). *)
