From stdpp Require Import strings.
From Coq Require Import Ascii.

Check "a". (* should be string *)

Check "a"%char. (* should be ascii *)

Open Scope char_scope.

Check "a". (* should be ascii *)
Check "a"%string. (* should be string *)
