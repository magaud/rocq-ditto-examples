(*=====================================================
=======================================================
AUGUST 2008 - 
CONTINUED MAY 2009
	      TOPOLOGICAL FMAPS, HMAPS -
               

      PART 1: BASES, FMAPS, HMAPS, 
              A, A_1, F AND CLOSURES, B
              top, bottom, Shift, Split

=======================================================
=====================================================*)

From Stdlib Require Import Arith.
From Stdlib Require Import EqNat.
From Stdlib Require Export Reals.
From Stdlib Require Export Lia Lra.

Open Scope R_scope.

Set Asymmetric Patterns.
(*=====================================================
                     DIMENSIONS
 ====================================================*)

(* Dimensions: *)
Inductive dim:Set := zero : dim | one : dim.

(* Decidability of dim equality: *)
Lemma eq_dim_dec :
 forall i k : dim, {i=k}+{~i=k}.
Proof.
intros i k; case i; case k; intros.
 tauto.
 right. discriminate.
 right. discriminate.
 tauto.
Defined.

Definition dim_opp(k:dim):dim:=
 match k with zero => one | one => zero end.

(*========================================================
          TAGS AS NATS
========================================================*)

Definition tag := nat.

(* Decidability of tag equality: *)

Definition eq_tag_dec := eq_nat_dec.

(*========================================================
       POINTS AS PAIRS OF REALS
========================================================*)

Definition point := (R * R)%type.

(* Equality of points : *)

Definition eq_point(p q :point):=
  fst p = fst q /\ snd p = snd q.

(* Decidability point equality: *)

(* Remainder, but DANGEREOUS ! :
Check Req_dec.
Req_dec
     : forall r1 r2 : R, r1 = r2 \/ r1 <> r2.
*)

(* Decidability of real equality : OK but DANGEREOUS ! *)

Lemma Req_dec_1
   : forall r1 r2 : R, {r1 = r2} + {r1 <> r2}.
Proof.
intros; generalize (total_order_T r1 r2) Rlt_dichotomy_converse;
 intuition eauto 3.
Qed.

(* Decidability of point equality: OK, but DANGEREOUS ! *)

Lemma eq_point_dec : forall (p q:point),
  {eq_point p q} + {~eq_point p q}.
Proof.
intros.
unfold eq_point in |- *.
elim p.
elim q.
simpl in |- *.
intros.
generalize (Req_dec_1 a0 a).
generalize (Req_dec_1 b0 b).
tauto.
Qed.

(*========================================================
                 DARTS AS NATURALS
========================================================*)

Open Scope nat_scope.

(* For simplicity, dart is nat, but it could be a deferred type: *)

Definition dart := nat.

(* Decidability of dart equality: *)

Definition eq_dart_dec := eq_nat_dec.

(* Nil dart: *)

Definition nil := 0.

(*=====================================================
   FREE MAPS, CONSTRUCTORS, OBSERVERS AND DESTRUCTORS
 ====================================================*)

Open Scope Z_scope.

(* Free maps: *)

Inductive fmap:Set :=
      V : fmap
    | I : fmap->dart->tag->point->fmap
    | L : fmap->dim->dart->dart->fmap.

(* Map emptiness: *)

Definition empty(m:fmap): Prop:=
 match m with
       V => True
    |  _ => False
 end.

(* Map emptiness is decidable: *)

Lemma empty_dec: forall (m:fmap),
  {empty m}+{~empty m}.
Proof.
intro m.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   tauto.
 right.
   intro.
   inversion H.
Defined.

(* A dart exists in an fmap:
CAUTION: (exd m nil) is possible for m <> V *)

Fixpoint exd(m:fmap)(x:dart){struct m} : Prop:=
 match m with
       V => False
    |  I m0 x0 _ _ => x0 = x \/ exd m0 x
    |  L m0 _ _ _  => exd m0 x
 end.

(* exd is decidable: *)

Lemma exd_dec: forall (m:fmap)(x:dart),
  {exd m x}+{~exd m x}.
Proof.
induction m. (*as [| m IHm d t p  | m IHm d0 d1].*)
 right.
   intro.
   inversion H.
   intro.
   simpl.
 elim (IHm x).
  left.
    simpl in |- *.
    tauto.
  intro.
    elim (eq_dart_dec d x).
   tauto.
   tauto.
   intro.
 elim (IHm x).
  left.
    simpl in |- *.
    assumption.
  simpl in |- *.
    tauto.
Defined.

(* Access to the tag of a dart: 0%nat is the nil tag *)

Fixpoint ftag(m:fmap)(x:dart){struct m}:tag:=
  match m with
      V => 0%nat
    | I m0 x0 t0 _ =>
         if eq_dart_dec x0 x then t0
	 else ftag m0 x
    | L m0 k x0 y0 => ftag m0 x
  end.

(* Access to the point of a dart: (0, 0) is the nil point *)

Fixpoint fpoint(m:fmap)(x:dart){struct m}:point:=
  match m with
      V => (0%R, 0%R)
    | I m0 x0 _ p0 =>
         if eq_dart_dec x0 x then p0
	 else fpoint m0 x
    | L m0 k x0 y0 => fpoint m0 x
  end.

(* A, for alpha, completed by nil when necessary:
designed for qhmaps: *)

Fixpoint A (m:fmap)(k:dim)(x:dart)
               {struct m}:dart:=
 match m with
     V => nil
    | I m0 x0 _ _ => A m0 k x
    | L m0 k0 x0 y0 =>
          if eq_dim_dec k0 k
          then if eq_dart_dec x0 x then y0
               else A m0 k x
          else A m0 k x
 end.

(* Auxiliary notion: a dart has a k-successor *)

Definition succ(m:fmap)(k:dim)(x:dart):=
  A m k x <> nil.

(* Thus, a nil successor is not considered as a true successor! *)

(* Decidability of succ: *)

Lemma succ_dec: forall (m:fmap)(k:dim)(x:dart),
  {succ m k x} + {~succ m k x}.
Proof.
intros.
unfold succ in |- *.
elim (eq_dart_dec (A m k x) nil).
 tauto.
 tauto.
Defined.

(* A's inverse; CAUTION: that is not the true inverse
 in an fmap, but it is in a true map (or qhmap...)! *)

Fixpoint A_1 (m:fmap)(k:dim)(y:dart)
  {struct m}:dart:=
  match m with
      V => nil
    | I m0 x0 _ _ => A_1 m0 k y
    | L m0 k0 x0 y0 =>
          if (eq_dim_dec k0 k)
          then if (eq_dart_dec y0 y) then x0
              else A_1 m0 k y
          else A_1 m0 k y
  end.

(* Idem: *)

Definition pred(m:fmap)(k:dim)(x:dart):=
  A_1 m k x <> nil.

(* Decidability of pred: *)

Lemma pred_dec: forall (m:fmap)(k:dim)(x:dart),
  {pred m k x} + {~pred m k x}.
Proof.
intros.
unfold pred in |- *.
elim (eq_dart_dec (A_1 m k x) nil).
 tauto.
 tauto.
Defined.

(* Deleting the last occurrence of a dart: *)

Fixpoint D(m:fmap)(x:dart){struct m}:fmap:=
  match m with
      V => V
    | I m0 x0 t0 p0 =>
         if eq_dart_dec x0 x then m0
         else (I (D m0 x) x0 t0 p0)
    | L m0 k0 x0 y0 => L (D m0 x) k0 x0 y0
 end.

(* Breaking the last k-link starting from a dart: *)

Fixpoint B(m:fmap)(k:dim)(x:dart){struct m}:fmap:=
  match m with
      V => V
    | I m0 x0 t0 p0 => (I (B m0 k x) x0 t0 p0)
    | L m0 k0 x0 y0 =>
         if (eq_dim_dec k0 k)
         then if (eq_dart_dec x0 x) then m0
              else (L (B m0 k x) k0 x0 y0)
         else (L (B m0 k x) k0 x0 y0)
  end.

(* Breaking the last k-link arriving on a dart: *)

Fixpoint B_1(m:fmap)(k:dim)(y:dart){struct m}:fmap:=
  match m with
      V => V
    | I m0 x0 t0 p0 =>(I (B_1 m0 k y) x0 t0 p0)
    | L m0 k0 x0 y0 =>
         if (eq_dim_dec k0 k)
         then if (eq_dart_dec y0 y) then m0
              else (L (B_1 m0 k y) k0 x0 y0)
         else (L (B_1 m0 k y) k0 x0 y0)
  end.

(* Here, the correctness of D, B and B_1 has to be proved:
 what they do is what they have to do. *)

(*=====================================================
                 CLOSURES OF A and A_1
 ====================================================*)

(* Closures of A and A_1, together designed for qhmaps,
mutually recursive: *)

Fixpoint cA(m:fmap)(k:dim)(z:dart){struct m}:dart:=
 match m with
     V => nil
  |  I m0 x _ _ =>
        if eq_dart_dec x z then z
	else cA m0 k z
  |  L m0 k0 x y  =>
      if (eq_dim_dec k0 k)
      then
         if (eq_dart_dec x z) then y
	 else
	   if (eq_dart_dec (cA_1 m0 k y) z)
	   then cA m0 k x
	   else cA m0 k z
      else cA m0 k z
 end
with cA_1(m:fmap)(k:dim)(z:dart){struct m}:dart:=
 match m with
     V => nil
  |  I m0 x _ _ =>
        if eq_dart_dec x z then z
	else cA_1 m0 k z
  |  L m0 k0 x y =>
      if (eq_dim_dec k0 k)
      then
         if (eq_dart_dec y z) then x
	 else
	   if (eq_dart_dec (cA m0 k x) z)
	   then cA_1 m0 k y
	   else cA_1 m0 k z
      else cA_1 m0 k z
 end.

(* Notations ?
Notation "A~" := cA.

Notation "A_1~" := cA_1.

Notation "A~" := cA.

Notation "A_1~" := cA_1.
*)

(*=====================================================
              I- AND L-PRECONDITIONS, HMAPS
=====================================================*)

(* For a unique insertion of a non nil dart
in a (future) hmap: *)

Definition prec_I (m:fmap)(x:dart):=
  x <> nil /\ ~exd m x .

(* For correctness of functional link insertion,
always incomplete, in a hmap: *)

Definition prec_L (m:fmap)(k:dim)(x y:dart) :=
  exd m x /\ exd m y /\ ~succ m k x /\ ~pred m k y
    /\ cA m k x <> y.

Fixpoint inv_hmap(m:fmap):Prop:=
  match m with
    V => True
    | I m0 x _ _ => inv_hmap m0 /\ prec_I m0 x
    | L m0 k0 x y => inv_hmap m0 /\ prec_L m0 k0 x y
  end.

(* Definition of the hmap type: (not used) *)

Definition hmap:Set := {m:fmap | inv_hmap m}.

(* Projection of a hmap to its fmap support: *)

Definition hmap_to_fmap(q:hmap):fmap:=
  match q with exist m _=> m end.

(* The projection is declared as a coercion: *)

Coercion hmap_to_fmap: hmap >-> fmap.

(* OK *)

Lemma inv_hmap_dec:forall(m:fmap),
 {inv_hmap m} + {~inv_hmap m}.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   unfold prec_I in |- *.
   generalize (eq_dart_dec d nil).
   generalize (exd_dec m d).
   tauto.
 simpl in |- *.
   unfold prec_L in |- *.
   generalize (exd_dec m d0).
   generalize (exd_dec m d1).
   generalize (succ_dec m d d0).
   generalize (pred_dec m d d1).
   generalize (eq_dart_dec (cA m d d0) d1).
   tauto.
Qed.

(*=====================================================
     A LOT OF PROPERTIES NEEDING inv_hmap ONLY
=====================================================*)

(* nil isn't in a qhmap: *)

Lemma not_exd_nil :
  forall m:fmap, inv_hmap m -> ~exd m nil.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   unfold prec_I in |- *.
   intros.
   intro.
   elim H0.
  intro.
    symmetry in H1.
    tauto.
  tauto.
 simpl in |- *.
   tauto.
Qed.

(* and the variant: *)

Lemma exd_not_nil :
  forall (m:fmap)(z:dart),
   inv_hmap m -> exd m z -> z <> nil.
Proof.
intros.
elim (eq_dart_dec z nil).
 intro.
   rewrite a in H0.
   assert (~ exd m nil).
  apply not_exd_nil.
    tauto.
  tauto.
 tauto.
Qed.

(* Relationship between succ and exd: *)

Lemma succ_exd :
  forall (m:fmap)(k:dim)(z:dart),
   inv_hmap m -> succ m k z -> exd m z.
Proof.
unfold succ in |- *.
induction m.
 simpl in |- *.
    tauto.
simpl in |- *.
  unfold prec_I in |- *.
  intros k z Hinv.
  elim (eq_dart_dec d z).
  tauto.
intros.
  right.
   eapply IHm.
    tauto.
  apply H.
  intros k z.
  simpl in |- *.
  unfold prec_L in |- *.
  elim (eq_dim_dec d k).
 elim (eq_dart_dec d0 z).
  intros.
    rewrite <- a in |- *.
     tauto.
 intros.
    eapply IHm.
     tauto.
   apply H0.
  intros.
   eapply IHm.
    tauto.
  apply H0.
Qed.

(* Idem: *)

Lemma pred_exd :
  forall (m:fmap)(k:dim)(z:dart),
   inv_hmap m -> pred m k z -> exd m z.
Proof.
unfold pred in |- *.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   unfold prec_I in |- *.
   intros k z Hinv.
   elim (eq_dart_dec d z).
  tauto.
  intros.
    right.
    eapply IHm.
   tauto.
   apply H.
 intros k z.
   simpl in |- *.
   unfold prec_L in |- *.
   elim (eq_dim_dec d k).
  elim (eq_dart_dec d1 z).
   intros.
     rewrite <-a.
     tauto.
   intros.
     eapply IHm.
    tauto.
    apply H0.
  intros.
    eapply IHm.
   tauto.
   apply H0.
Qed.

Lemma not_exd_A_nil:
  forall (m:fmap)(k:dim)(z:dart),
   inv_hmap m -> ~exd m z -> A m k z = nil.
Proof.
intros.
elim (eq_dart_dec (A m k z) nil).
 tauto.
 intros.
   generalize (succ_exd m k z).
   intro.
   unfold succ in H1.
   absurd (exd m z).
  tauto.
  eapply H1.
   tauto.
   assumption.
Qed.

(* Idem with: *)

Lemma not_exd_A_1_nil:
  forall (m:fmap)(k:dim)(z:dart),
   inv_hmap m -> ~exd m z -> A_1 m k z = nil.
Proof.
intros.
elim (eq_dart_dec (A_1 m k z) nil).
 tauto.
 intros.
   generalize (pred_exd m k z).
   intro.
   unfold pred in H1.
   absurd (exd m z).
  tauto.
  eapply H1.
   tauto.
   assumption.
Qed.

(* Note that, in a hmap m, 
we have neither
exd m z -> A m k z <> nil 
nor
exd m z -> A_1 m k z <> nil *)

(* Note also: *)

Lemma A_nil: forall (m:fmap)(k:dim),
   inv_hmap m -> A m k nil = nil.
Proof.
intros.
apply not_exd_A_nil.
 tauto.
 apply not_exd_nil.
   tauto.
Qed.

Lemma A_1_nil: forall (m:fmap)(k:dim),
   inv_hmap m -> A_1 m k nil = nil.
Proof.
intros.
apply not_exd_A_1_nil.
 tauto.
 apply not_exd_nil.
   tauto.
Qed.

Lemma succ_exd_A :
  forall (m:fmap)(k:dim)(z:dart),
   inv_hmap m -> succ m k z -> exd m (A m k z).
Proof.
induction m.
 simpl in |- *.
   unfold succ in |- *.
   simpl in |- *.
   tauto.
 simpl in |- *.
   unfold succ in |- *.
   unfold prec_I in |- *.
   intros k z Hinv Hx.
   simpl in Hx.
   generalize Hx.
   clear Hx.
   intro.
   right.
   apply IHm.
  tauto.
  unfold succ in |- *.
    tauto.
 unfold succ in |- *.
   simpl in |- *.
   unfold prec_L in |- *.
   intros k z.
   elim (eq_dim_dec d k).
  elim (eq_dart_dec d0 z).
   tauto.
   intros.
     apply IHm.
    tauto.
    unfold succ in |- *.
      tauto.
  intros.
    apply IHm.
   tauto.
   unfold succ in |- *.
     tauto.
Qed.

(* Idem: *)

Lemma pred_exd_A_1 :
  forall (m:fmap)(k:dim)(z:dart),
   inv_hmap m -> pred m k z -> exd m (A_1 m k z).
Proof.
induction m.
 simpl in |- *.
   unfold pred in |- *.
   simpl in |- *.
    tauto.
simpl in |- *.
  unfold pred in |- *.
  unfold prec_I in |- *.
  intros k z Hinv Hx.
  simpl in Hx.
  generalize Hx.
  clear Hx.
  intro.
  right.
  apply IHm.
  tauto.
unfold pred in |- *.
   tauto.
unfold pred in |- *.
  simpl in |- *.
  unfold prec_L in |- *.
  intros k z.
  elim (eq_dim_dec d k).
 elim (eq_dart_dec d1 z).
   tauto.
 intros.
   apply IHm.
   tauto.
 unfold pred in |- *.
    tauto.
intros.
  apply IHm.
  tauto.
unfold pred in |- *.
   tauto.
Qed.

Lemma exd_A_exd :
  forall (m : fmap) (k : dim) (z : dart),
   inv_hmap m -> exd m (A m k z) -> exd m z.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   unfold prec_I in |- *.
   unfold exd in |- *.
   fold exd in |- *.
   intros.
   elim H0.
  clear H0.
    intro.
    rewrite H0 in H.
    decompose [and] H.
    elim H4.
    apply succ_exd_A.
   tauto.
   unfold succ in |- *.
     tauto.
  intro.
    right.
    eapply IHm.
   tauto.
   apply H1.
 simpl in |- *.
   unfold prec_L in |- *.
   unfold succ in |- *; unfold pred in |- *.
   intros k z Invm.
   elim (eq_dim_dec d k).
  elim (eq_dart_dec d0 z).
   intros.
     rewrite <-a.
     tauto.
   intros.
     eapply IHm.
    tauto.
    apply H.
  intros.
    eapply IHm.
   tauto.
   apply H.
Qed.

(* IDEM: *)

Lemma exd_A_1_exd :
  forall (m : fmap) (k : dim) (z : dart),
   inv_hmap m -> exd m (A_1 m k z) -> exd m z.
Proof.
induction m.
 simpl in |- *.
    tauto.
simpl in |- *.
  unfold prec_I in |- *.
  unfold exd in |- *.
  fold exd in |- *.
  intros.
  elim H0.
 clear H0.
   intro.
   rewrite H0 in H.
   decompose [and] H.
   elim H4.
   apply pred_exd_A_1.
   tauto.
 unfold pred in |- *.
    tauto.
intro.
  right.
   eapply IHm.
    tauto.
  apply H1.
  simpl in |- *.
  unfold prec_L in |- *.
  unfold succ in |- *; unfold pred in |- *.
  intros k z Invm.
  elim (eq_dim_dec d k).
 elim (eq_dart_dec d1 z).
  intros.
    rewrite <- a in |- *.
     tauto.
 intros.
    eapply IHm.
     tauto.
   apply H.
  intros.
   eapply IHm.
    tauto.
  apply H.
Qed.

(*=====================================================
       A AND A_1 ARE INVERSES INJECTIONS IN A hmap:
=====================================================*)

(* In a qmap, A et A_1 are inverses: *)

Lemma A_1_A :
  forall (m:fmap)(k:dim)(z:dart),
     inv_hmap m -> succ m k z ->
        A_1 m k (A m k z) = z.
Proof.
induction m.
 simpl in |- *.
   simpl in |- *.
   unfold succ in |- *.
   unfold prec_I in |- *.
   simpl in |- *.
   tauto.
 unfold succ in |- *.
   simpl in |- *.
   intros.
   apply IHm.
  tauto.
  unfold succ in |- *.
    tauto.
 unfold succ in |- *.
   simpl in |- *.
   unfold prec_L in |- *.
   intros k z Inv.
   elim (eq_dim_dec d k).
  elim (eq_dart_dec d0 z).
   elim (eq_dart_dec d1 d1).
    tauto.
    tauto.
   elim (eq_dart_dec d1 (A m k z)).
    intros.
      assert (z = A_1 m k d1).
     rewrite a.
       symmetry  in |- *.
       apply IHm.
      tauto.
      unfold succ in |- *.
        tauto.
     unfold pred in Inv.
       rewrite a0 in Inv.
       rewrite <- H0 in Inv.
       assert (exd m z).
      eapply succ_exd.
       tauto.
       unfold succ in |- *.
         apply H.
      assert (z <> nil).
       apply exd_not_nil with m.
        tauto.
        tauto.
       tauto.
    intros.
      apply IHm.
     tauto.
     unfold succ in |- *.
       tauto.
  intros.
    apply IHm.
   tauto.
   unfold succ in |- *.
     tauto.
Qed.

(* Idem with A_1: *)

Lemma A_A_1 :
  forall (m:fmap)(k:dim)(z:dart),
   inv_hmap m -> pred m k z
     -> A m k (A_1 m k z) = z.
Proof.
induction m.
 simpl in |- *.
   simpl in |- *.
   unfold pred in |- *.
   unfold prec_I in |- *.
   simpl in |- *.
   tauto.
 unfold pred in |- *.
   simpl in |- *.
   intros.
   apply IHm.
  tauto.
  unfold pred in |- *.
    tauto.
 unfold pred in |- *.
   simpl in |- *.
   unfold prec_L in |- *.
   intros k z Inv.
   elim (eq_dim_dec d k).
  elim (eq_dart_dec d1 z).
   elim (eq_dart_dec d0 d0).
    tauto.
    tauto.
   elim (eq_dart_dec  d0 (A_1 m k z)).
    intros.
      assert (z = A m k d0).
     rewrite a.
       symmetry  in |- *.
       apply IHm.
      tauto.
      unfold pred in |- *.
        tauto.
     unfold succ in Inv.
       rewrite a0 in Inv.
       rewrite <- H0 in Inv.
       assert (exd m z).
      eapply pred_exd.
       tauto.
       unfold pred in |- *.
         apply H.
      assert (z <> nil).
       apply exd_not_nil with m.
        tauto.
        tauto.
       tauto.
    intros.
      apply IHm.
     tauto.
     unfold pred in |- *.
       tauto.
  intros.
    apply IHm.
   tauto.
   unfold pred in |- *.
     tauto.
Qed.

(* Partial injection on dart, Df giving the domain of f: *)

Definition inj_dart(Df:dart->Prop)(f:dart->dart):Prop:=
    forall x x':dart,
     (Df x)->(Df x')->(f x)=(f x')->x=x'.

(* (A m k) is an injection on (succ m k): OK *)

Lemma inj_A:
   forall (m:fmap)(k:dim), inv_hmap m ->
      inj_dart (succ m k) (A m k).
Proof.
intros m k Hinv.
unfold inj_dart in |- *.
intros x x' Hx Hx' Heg.
assert (x = A_1 m k (A m k x)).
 rewrite A_1_A.
  tauto.
  tauto.
  tauto.
 assert (x' = A_1 m k (A m k x')).
  rewrite A_1_A.
   tauto.
   tauto.
   tauto.
  rewrite Heg in H.
    rewrite H.
    rewrite <- Heg.
    rewrite H0.
    rewrite Heg.
    tauto.
Qed.

(* Idem, for pred and A_1: *)

Lemma inj_A_1 :
   forall (m:fmap)(k:dim), inv_hmap m ->
      inj_dart (pred m k) (A_1 m k).
Proof.
intros m k Hinv.
unfold inj_dart in |- *.
intros x x' Hx Hx' Heg.
assert (x = A m k (A_1 m k x)).
 rewrite A_A_1.
  tauto.
  tauto.
  tauto.
 assert (x' = A m k (A_1 m k x')).
  rewrite A_A_1.
   tauto.
   tauto.
   tauto.
  rewrite Heg in H.
    rewrite H.
    rewrite <- Heg.
    rewrite H0.
    rewrite Heg.
    tauto.
Qed.

(*=====================================================
           PROPERTIES of A and A_1 CLOSURES in hmap
=====================================================*)

(* Each existing dart has a succ in the k-closure : *)

Lemma succ_pred_clos :
   forall (m:fmap)(k:dim)(z:dart),
     inv_hmap m -> exd m z ->
       (cA m k z <> nil /\ cA_1 m k z <> nil).
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   elim (eq_dart_dec d z).
  intro.
    unfold prec_I in H.
    rewrite a in H.
    tauto.
  intro.
    apply IHm.
   tauto.
   tauto.
 simpl in |- *.
   unfold prec_L in |- *.
   intros.
   elim (eq_dim_dec d k).
  elim (eq_dart_dec d0 z).
   elim (eq_dart_dec d1 z).
    intros.
      split.
     intro.
       rewrite H1 in H.
       absurd (exd m nil).
      apply not_exd_nil.
        tauto.
      tauto.
     intro.
       rewrite H1 in H.
       absurd (exd m nil).
      apply not_exd_nil.
        tauto.
      tauto.
    intros.
      split.
     intro.
       rewrite H1 in H.
       absurd (exd m nil).
      apply not_exd_nil.
        tauto.
      tauto.
     rewrite a.
       elim (eq_dart_dec (cA m k z) z).
      intros.
        generalize (IHm k d1).
        tauto.
      intro.
        generalize (IHm k z).
        tauto.
   elim (eq_dart_dec (cA_1 m k d1) z).
    intros.
      split.
     generalize (IHm k d0).
       tauto.
     elim (eq_dart_dec d1 z).
      intros.
        intro.
        rewrite H1 in H.
        absurd (exd m nil).
       apply not_exd_nil.
         tauto.
       tauto.
      elim (eq_dart_dec (cA m k d0) z).
       intros.
         generalize (IHm k d1).
         tauto.
       intros.
         generalize (IHm k z).
         tauto.
    intros.
      split.
     generalize (IHm k z).
       tauto.
     elim (eq_dart_dec d1 z).
      intros.
        intro.
        rewrite H1 in H.
        absurd (exd m nil).
       apply not_exd_nil.
         tauto.
       tauto.
      elim (eq_dart_dec (cA m k d0) z).
       intros.
         generalize (IHm k d1).
         tauto.
       intros.
         generalize (IHm k z).
         tauto.
  intros.
    generalize (IHm k z).
    tauto.
Qed.

(* Each dart of a fmap has a succ
and a pred for the closure: *)

Lemma exd_cA_cA_1 :
   forall (m:fmap)(k:dim)(z:dart),
     inv_hmap m -> exd m z ->
       exd m (cA m k z) /\ exd m (cA_1 m k z).
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intro.
   unfold prec_I in |- *.
   intros.
   elim (eq_dart_dec d z).
  tauto.
  generalize (IHm k z).
    tauto.
 intros k z.
   simpl in |- *.
   unfold prec_L in |- *.
   intros.
   elim (eq_dim_dec d k).
  intro.
    elim (eq_dart_dec d0 z).
   intro.
     split.
    tauto.
    elim (eq_dart_dec d1 z).
     tauto.
     elim (eq_dart_dec (cA m k d0) z).
      intros.
        generalize (IHm k d1).
        tauto.
      generalize (IHm k z).
        tauto.
   intro.
     elim (eq_dart_dec (cA_1 m k d1) z).
    split.
     generalize (IHm k d0).
       tauto.
     elim (eq_dart_dec d1 z).
      tauto.
      elim (eq_dart_dec (cA m k d0) z).
       generalize (IHm k d1).
         tauto.
       generalize (IHm k z).
         tauto.
    split.
     generalize (IHm k z); tauto.
     elim (eq_dart_dec d1 z).
      tauto.
      elim (eq_dart_dec (cA m k d0) z).
       generalize (IHm k d1); tauto.
       generalize (IHm k z); tauto.
  generalize (IHm k z); tauto.
Qed.

(* If the succ for cA is in the hmap, the initial dart also: *)

Lemma cA_exd :
   forall (m:fmap)(k:dim)(z:dart),
     inv_hmap m -> cA m k z <> nil -> exd m z.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   unfold prec_I in |- *.
   intros k z.
   elim (eq_dart_dec d z).
  tauto.
  intros.
    right.
    apply (IHm k z).
   tauto.
   tauto.
 intros k z.
   simpl in |- *.
   unfold prec_L in |- *.
   elim (eq_dim_dec d k).
  elim (eq_dart_dec d0 z).
   intros.
     rewrite <- a.
     tauto.
   elim (eq_dart_dec (cA_1 m k d1) z).
    intros.
      rewrite <- a.
      generalize (exd_cA_cA_1 m k d1).
      tauto.
    intros.
      eapply IHm.
     tauto.
     apply H0.
  intros.
    eapply IHm.
   tauto.
   apply H0.
Qed.

(* Idem for cA_1: *)

Lemma cA_1_exd :
   forall (m:fmap)(k:dim)(z:dart),
     inv_hmap m -> cA_1 m k z <> nil -> exd m z.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   unfold prec_I in |- *.
   intros k z.
   elim (eq_dart_dec d z).
  tauto.
  intros.
    right.
    apply (IHm k z).
   tauto.
   tauto.
 intros k z.
   simpl in |- *.
   unfold prec_L in |- *.
   elim (eq_dim_dec d k).
  elim (eq_dart_dec d1 z).
   intros.
     rewrite <- a.
     tauto.
   elim (eq_dart_dec  (cA m k d0) z).
    intros.
      rewrite <- a.
      generalize (exd_cA_cA_1 m k d0).
      tauto.
    intros.
      eapply IHm.
     tauto.
     apply H0.
  intros.
    eapply IHm.
   tauto.
   apply H0.
Qed.

(* A non existing dart has a nil successor by cA: *)

Lemma not_exd_cA :
   forall (m:fmap)(k:dim)(z:dart),
     inv_hmap m -> ~exd m z -> 
        cA m k z = nil.
Proof.
intros.
elim (eq_dart_dec (cA m k z) nil).
 tauto.
 intro.
   elim H0.
   apply cA_exd with k.
  tauto.
  tauto.
Qed.

(* Idem for cA_1: *)

Lemma not_exd_cA_1 :
   forall (m:fmap)(k:dim)(z:dart),
     inv_hmap m -> ~exd m z -> 
        cA_1 m k z = nil.
Proof.
intros.
elim (eq_dart_dec (cA_1 m k z) nil).
 tauto.
 intro.
   elim H0.
   apply cA_1_exd with k.
  tauto.
  tauto.
Qed.

(* Inverse for exd: *)

Lemma exd_cA_exd :
   forall (m:fmap)(k:dim)(z:dart),
     inv_hmap m ->
       exd m (cA m k z) -> exd m z.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   unfold prec_I in |- *.
   intros k z.
   elim (eq_dart_dec d z).
  tauto.
  intros.
    right.
    elim H0.
   clear H0.
     intro.
     rewrite H0 in H.
     apply (cA_exd m k z).
    tauto.
    tauto.
   apply IHm.
     tauto.
 intros k z.
   simpl in |- *.
   unfold prec_L in |- *.
   elim (eq_dim_dec d k).
  elim (eq_dart_dec d0 z).
   intros.
     rewrite <- a.
     tauto.
   elim (eq_dart_dec (cA_1 m k d1) z).
    intros.
      rewrite <- a.
      generalize (exd_cA_cA_1 m k d1).
      tauto.
    intros.
      eapply IHm.
     tauto.
     apply H0.
  intros.
    eapply IHm.
   tauto.
   apply H0.
Qed.

(* Idem: *)

Lemma exd_cA_1_exd :
   forall (m:fmap)(k:dim)(z:dart),
     inv_hmap m ->
       exd m (cA_1 m k z) -> exd m z.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   unfold prec_I in |- *.
   intros k z.
   elim (eq_dart_dec d z).
  tauto.
  intros.
    right.
    elim H0.
   clear H0.
     intro.
     rewrite H0 in H.
     apply (cA_1_exd m k z).
    tauto.
    tauto.
   apply IHm.
     tauto.
 intros k z.
   simpl in |- *.
   unfold prec_L in |- *.
   elim (eq_dim_dec d k).
  elim (eq_dart_dec d1 z).
   intros.
     rewrite <- a.
     tauto.
   elim (eq_dart_dec (cA m k d0) z).
    intros.
      rewrite <- a.
      generalize (exd_cA_cA_1 m k d0).
      tauto.
    intros.
      eapply IHm.
     tauto.
     apply H0.
  intros.
    eapply IHm.
   tauto.
   apply H0.
Qed.

(* Specializations: *)

Lemma exd_cA:forall (m:fmap)(k:dim)(z:dart),
  inv_hmap m ->
     (exd m z <-> exd m (cA m k z)).
Proof.
intros.
generalize (exd_cA_exd m k z).
generalize (exd_cA_cA_1 m k z).
tauto.
Qed.

Lemma exd_cA_1:forall (m:fmap)(k:dim)(z:dart),
  inv_hmap m ->
     (exd m z <-> exd m (cA_1 m k z)).
Proof.
intros.
generalize (exd_cA_1_exd m k z).
generalize (exd_cA_cA_1 m k z).
tauto.
Qed.

(* cA and cA_1 are inverses of each other: *)

Lemma cA_1_cA :
   forall (m:fmap)(k:dim)(z:dart),
     inv_hmap m -> exd m z ->
       cA_1 m k (cA m k z) = z.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros k z.
   unfold prec_I in |- *.
   elim (eq_dart_dec d z).
  elim (eq_dart_dec d z).
   tauto.
   tauto.
  elim (eq_dart_dec d (cA m k z)).
   intros.
     rewrite a in H.
     absurd (exd m (cA m k z)).
    tauto.
    generalize (exd_cA_cA_1 m k z).
      tauto.
   intros.
     apply IHm.
    tauto.
    tauto.
 intros k z.
   simpl in |- *.
   unfold prec_L in |- *.
   intros.
   elim (eq_dim_dec d k).
  intros.
    elim (eq_dart_dec d0 z).
   intro.
     rewrite a0.
     elim (eq_dart_dec d1 d1).
    tauto.
    tauto.
   elim (eq_dart_dec (cA_1 m k d1) z).
    elim (eq_dart_dec d1 (cA m k d0)).
     intros.
       rewrite a0 in a1.
       generalize (IHm k d0).
       intros.
       rewrite a1 in H1.
       symmetry  in |- *.
       tauto.
     elim (eq_dart_dec (cA m k d0) (cA m k d0)).
      intros.
        tauto.
      tauto.
    elim (eq_dart_dec d1 (cA m k z)).
     intros.
       rewrite a0 in b.
       elim b.
       apply IHm.
      tauto.
      tauto.
     elim (eq_dart_dec (cA m k d0) (cA m k z)).
      intros.
        generalize (IHm k z).
        intros.
        rewrite <- a0 in H1.
        generalize (IHm k d0).
        intro.
        rewrite H2 in H1.
       tauto.
       tauto.
       tauto.
      intros.
        apply IHm.
       tauto.
       tauto.
  intro.
    apply IHm.
   tauto.
   tauto.
Qed.

(* IDEM: *)

Lemma cA_cA_1 :
   forall (m:fmap)(k:dim)(z:dart),
     inv_hmap m -> exd m z ->
       cA m k (cA_1 m k z) = z.
Proof.
induction m.
 simpl in |- *.
    tauto.
simpl in |- *.
  intros k z.
  unfold prec_I in |- *.
  elim (eq_dart_dec d z).
 elim (eq_dart_dec d z).
   tauto.
  tauto.
elim (eq_dart_dec d (cA_1 m k z)).
 intros.
   rewrite a in H.
    absurd (exd m (cA_1 m k z)).
   tauto.
 generalize (exd_cA_cA_1 m k z).
    tauto.
intros.
  apply IHm.
  tauto.
 tauto.
intros k z.
  simpl in |- *.
  unfold prec_L in |- *.
  intros.
  elim (eq_dim_dec d k).
 intros.
   elim (eq_dart_dec d1 z).
  intro.
    rewrite a0 in |- *.
    elim (eq_dart_dec d0 d0).
    tauto.
   tauto.
 elim (eq_dart_dec (cA m k d0) z).
  elim (eq_dart_dec d0 (cA_1 m k d1)).
   intros.
     rewrite a0 in a1.
     generalize (IHm k d1).
     intros.
     rewrite a1 in H1.
     symmetry  in |- *.
      tauto.
  elim (eq_dart_dec (cA_1 m k d1) (cA_1 m k d1)).
   intros.
      tauto.
   tauto.
 elim (eq_dart_dec d0 (cA_1 m k z)).
  intros.
    rewrite a0 in b.
    elim b.
    apply IHm.
    tauto.
   tauto.
 elim (eq_dart_dec (cA_1 m k d1) (cA_1 m k z)).
  intros.
    generalize (IHm k z).
    intros.
    rewrite <- a0 in H1.
    generalize (IHm k d1).
    intro.
    rewrite H2 in H1.
    tauto.
   tauto.
   tauto.
 intros.
   apply IHm.
   tauto.
  tauto.
intro.
  apply IHm.
  tauto.
 tauto.
Qed.

(* (cA m k) in an injection on (exd m): *)

Lemma inj_cA:
   forall (m:fmap)(k:dim), inv_hmap m ->
      inj_dart (exd m) (cA m k).
Proof.
intros m k Hinv.
unfold inj_dart in |- *.
intros x x' Hx Hx' Heg.
assert (x = cA_1 m k (cA m k x)).
 symmetry  in |- *.
   apply cA_1_cA.
  tauto.
  tauto.
 rewrite Heg in H.
   rewrite H.
   apply cA_1_cA.
  tauto.
  tauto; tauto.
Qed.

(* Idem: cA_1 is an injection on exd: *)

Lemma inj_cA_1:
   forall (m:fmap)(k:dim), inv_hmap m ->
      inj_dart (exd m) (cA_1 m k).
Proof.
intros m k Hinv.
unfold inj_dart in |- *.
intros x x' Hx Hx' Heg.
assert (x = cA m k (cA_1 m k x)).
 symmetry  in |- *.
   apply cA_cA_1.
  tauto.
  tauto.
 rewrite Heg in H.
   rewrite H.
   apply cA_cA_1.
  tauto.
  tauto; tauto.
Qed.

(* Isolated darts are fixpoints for the closure:*)

Lemma fixpt_cA_cA_1 :
   forall (m:fmap)(k:dim)(z:dart), inv_hmap m ->
      exd m z -> ~succ m k z -> ~pred m k z ->
         cA m k z = z /\ cA_1 m k z = z.
Proof.
induction m.
 simpl in |- *.
   tauto.
 unfold succ in |- *; unfold pred in |- *.
   simpl in |- *.
   intros k z.
   elim (eq_dart_dec d z).
  tauto.
  intros.
    apply IHm.
   tauto.
   tauto.
   unfold succ in |- *; tauto.
   unfold pred in |- *; tauto.
 intros k z.
   unfold succ in |- *; unfold pred in |- *.
   simpl in |- *.
   unfold prec_L in |- *.
   elim (eq_dim_dec d k).
  elim (eq_dart_dec d0 z).
   elim (eq_dart_dec d1 z).
    intros.
      rewrite a0; rewrite a.
      tauto.
    intros.
      absurd (d1 <> nil).
     tauto.
     intro.
       rewrite H3 in H.
       absurd (exd m nil).
      apply not_exd_nil.
        tauto.
      tauto.
   elim (eq_dart_dec d1 z).
    intros.
      absurd (d0 <> nil).
     tauto.
     intro.
       rewrite H3 in H.
       absurd (exd m nil).
      apply not_exd_nil.
        tauto.
      tauto.
    intros.
      elim (eq_dart_dec (cA_1 m k d1) z).
     intro.
       elim (eq_dart_dec (cA m k d0) z).
      intros.
        rewrite a0; rewrite a1.
        tauto.
      intros.
        split.
       assert (z = d1).
        assert (cA_1 m k z = z).
         generalize (IHm k z).
           tauto.
         symmetry  in H3.
           rewrite H3 in a0.
           assert (inj_dart (exd m) (cA_1 m k)).
          apply inj_cA_1.
            tauto.
          unfold inj_dart in H4.
            generalize (H4 z d1).
            intros.
            apply H5.
           tauto.
           tauto.
           symmetry  in |- *; tauto.
        symmetry  in H3.
          tauto.
       generalize (IHm k z).
         unfold pred in |- *; unfold succ in |- *.
         tauto.
     elim (eq_dart_dec (cA m k d0) z).
      intros.
        generalize (IHm k z).
        unfold pred in |- *; unfold succ in |- *.
        intros.
        assert (z = d0).
       assert (cA m k z = z).
        tauto.
        rewrite <- H4 in a0.
          assert (inj_dart (exd m) (cA m k)).
         apply inj_cA.
           tauto.
         unfold inj_dart in H5.
           generalize (H5 z d0).
           intros.
           symmetry  in a0.
           tauto.
       symmetry  in H4.
         tauto.
      intros.
        generalize (IHm k z).
        tauto.
  intros.
    generalize (IHm k z).
    tauto.
Qed.

(* Preservation of the existing successors in the closure: *)

Lemma A_cA :
   forall (m:fmap)(k:dim)(x y:dart), inv_hmap m ->
      exd m x -> exd m y -> A m k x = y ->
         cA m k x = y.
Proof.
induction m.
 simpl in |- *.
    tauto.
simpl in |- *.
  unfold prec_I in |- *.
  intros k x y.
  elim (eq_dart_dec d x).
  intuition.
    subst; tauto.
  rewrite H4 in H5.
    generalize (not_exd_A_nil m k x H3 H5).
    rewrite H2 in |- *.
    intro.
    rewrite H1 in H0.
     absurd (exd m nil).
   apply not_exd_nil.
      tauto.
   tauto.
 rewrite a in H5.
    tauto.
 rewrite a in H5.
    tauto.
 intuition.
  rewrite <- H0 in H2.
   absurd (exd m d).
  tauto.
rewrite <- H2 in |- *.
  apply succ_exd_A.
  tauto.
unfold succ in |- *.
  rewrite H2 in |- *.
   tauto.
intros k x y.
  simpl in |- *.
  unfold prec_L in |- *.
  elim (eq_dim_dec d k).
 elim (eq_dart_dec d0 x).
   tauto.
 elim (eq_dart_dec (cA_1 m k d1) x).
  intros.
    assert (cA m k x = y).
   apply IHm.
     tauto.
    tauto.
    tauto.
    tauto.
  assert (cA m k x = d1).
   rewrite <- a in |- *.
     apply (cA_cA_1 m k d1).
     tauto.
    tauto.
  rewrite H3 in H4.
    rewrite <- H4 in H.
    unfold pred in H.
    rewrite a0 in H.
    assert (x = A_1 m k y).
   rewrite <- H2 in |- *.
     rewrite A_1_A in |- *.
     tauto.
    tauto.
   unfold succ in |- *.
     rewrite H2 in |- *.
     apply (exd_not_nil m y).
     tauto.
    tauto.
  rewrite <- H5 in H.
    assert (x <> nil).
   apply (exd_not_nil m x).
     tauto.
    tauto.
   tauto.
 intros.
   apply IHm.
   tauto.
  tauto.
  tauto.
  tauto.
intros.
  apply IHm.
  tauto.
 tauto.
 tauto.
 tauto.
Qed.

(* IDEM: Preservation of the existing predecessors: *)

Lemma A_1_cA_1 :
   forall (m:fmap)(k:dim)(x y:dart), inv_hmap m ->
      exd m x -> exd m y -> A_1 m k x = y ->
         cA_1 m k x = y.
Proof.
induction m.
 simpl in |- *.
    tauto.
simpl in |- *.
  unfold prec_I in |- *.
  intros k x y.
  elim (eq_dart_dec d x).
  intuition; try (subst; tauto).
  rewrite <- H4 in H2.
    assert (A_1 m k d = nil).
   apply not_exd_A_1_nil.
     tauto.
    tauto.
  rewrite H1 in H2.
    rewrite <- H2 in H0.
     absurd (exd m nil).
   apply not_exd_nil.
      tauto.
   tauto.
 intuition.
  rewrite <- H0 in H2.
  elim H5.
  rewrite <- H2 in |- *.
  apply pred_exd_A_1.
  tauto.
unfold pred in |- *.
  rewrite H2 in |- *.
   tauto.
intros k x y.
  simpl in |- *.
  unfold prec_L in |- *.
  elim (eq_dim_dec d k).
 elim (eq_dart_dec d1 x).
   tauto.
 elim (eq_dart_dec (cA m k d0) x).
  intros.
    assert (cA_1 m k x = y).
   apply IHm.
     tauto.
    tauto.
    tauto.
    tauto.
  assert (cA_1 m k x = d0).
   rewrite <- a in |- *.
     apply (cA_1_cA m k d0).
     tauto.
    tauto.
  rewrite H3 in H4.
    rewrite <- H4 in H.
    unfold succ in H.
    rewrite a0 in H.
    assert (x = A m k y).
   rewrite <- H2 in |- *.
     rewrite A_A_1 in |- *.
     tauto.
    tauto.
   unfold pred in |- *.
     rewrite H2 in |- *.
     apply (exd_not_nil m y).
     tauto.
    tauto.
  rewrite <- H5 in H.
    assert (x <> nil).
   apply (exd_not_nil m x).
     tauto.
    tauto.
   tauto.
 intros.
   apply IHm.
   tauto.
  tauto.
  tauto.
  tauto.
intros.
  apply IHm.
  tauto.
 tauto.
 tauto.
 tauto.
Qed.

(* Definition of the notion of surjection on a domain: *)

Definition surj_dart(Df:dart->Prop)(f:dart->dart):Prop :=
   forall y:dart, Df y ->
     exists x : dart, Df x /\ f x = y.

(* (cA m k) is surjective on (exd m): *)

Lemma surj_cA : forall (m:fmap)(k:dim), inv_hmap m ->
  surj_dart (exd m) (cA m k).
Proof.
unfold surj_dart in |- *.
intros.
split with (cA_1 m k y).
split.
 generalize (exd_cA_cA_1 m k y).
   tauto.
 apply cA_cA_1.
  tauto.
  tauto.
Qed.

(* IDEM: *)

Lemma surj_cA_1 : forall (m:fmap)(k:dim), inv_hmap m ->
  surj_dart (exd m) (cA_1 m k).
Proof.
unfold surj_dart in |- *.
intros.
split with (cA m k y).
split.
 generalize (exd_cA_cA_1 m k y).
   tauto.
 apply cA_1_cA.
  tauto.
  tauto.
Qed.

(* Notion of bijection: *)

Definition bij_dart(Df:dart->Prop)(f:dart->dart):Prop:=             
  inj_dart Df f /\ surj_dart Df f.

(* (cA m k) is bijective on (exd m): *)

Theorem bij_cA : forall (m:fmap)(k:dim), inv_hmap m ->
  bij_dart (exd m) (cA m k).
Proof.
unfold bij_dart in |- *.
intros.
split.
 apply inj_cA.
   tauto.
 apply surj_cA.
   tauto.
Qed.

(* IDEM: *)

Theorem bij_cA_1 : forall (m:fmap)(k:dim), inv_hmap m ->
  bij_dart (exd m) (cA_1 m k).
Proof.
unfold bij_dart in |- *.
intros.
split.
 apply inj_cA_1.
   tauto.
 apply surj_cA_1.
   tauto.
Qed.

(*=====================================================
           exd, A, A_1 on D for hmap
=====================================================*)

(* Action of D on exd: *)

Lemma not_exd_D : forall (m:fmap)(x:dart),
  inv_hmap m -> ~exd (D m x) x.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intro.
   unfold prec_I in |- *.
   elim (eq_dart_dec d x).
  intros.
    rewrite <- a.
    tauto.
  simpl in |- *.
    intros.
    generalize (IHm x); tauto.
 simpl in |- *.
   intros.
   apply IHm.
   tauto.
Qed.

Lemma exd_D : forall (m:fmap)(x z:dart),
   inv_hmap m ->
     x <> z -> (exd m z <-> exd (D m x) z).
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   unfold prec_I in H.
   elim (eq_dart_dec d x).
  intro.
    rewrite a.
    tauto.
  simpl in |- *.
    generalize (IHm x z).
    tauto.
 intros.
   simpl in |- *.
   apply IHm.
  simpl in H.
    tauto.
  tauto.
Qed.

(*=====================================================
     PROPERTIES OF DESTRUCTORS B, B_1 on exd
 ====================================================*)

(* Action of B on exd: *)

Lemma exd_B : forall (m:fmap)(k:dim)(x z:dart),
   exd m z <-> exd (B m k x) z.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   generalize (IHm k x z).
   tauto.
 simpl in |- *.
   intros k x z.
   elim (eq_dim_dec d k).
  elim (eq_dart_dec d0 x).
   generalize (IHm k x z).
     tauto.
   simpl in |- *.
     generalize (IHm k x z).
     tauto.
  simpl in |- *.
    intro.
    apply IHm.
Qed.

(* Action of B_1 on exd: *)

Lemma exd_B_1 : forall (m:fmap)(k:dim)(x z:dart),
   exd m z <-> exd (B_1 m k x) z.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   generalize (IHm k x z).
   tauto.
 simpl in |- *.
   intros k x z.
   elim (eq_dim_dec d k).
  elim (eq_dart_dec d1 x).
   generalize (IHm k x z).
     tauto.
   simpl in |- *.
     generalize (IHm k x z).
     tauto.
  simpl in |- *.
    intro.
    apply IHm.
Qed.

Lemma not_succ_B:forall(m:fmap)(k:dim)(z:dart),
   inv_hmap m -> ~succ m k z -> B m k z = m.
Proof.
induction m.
 simpl in |- *.
   tauto.
 unfold succ in |- *.
   simpl in |- *.
   intros.
   unfold succ in IHm.
   rewrite IHm.
  tauto.
  tauto.
  tauto.
 unfold succ in |- *.
   simpl in |- *.
   unfold prec_L in |- *.
   intros.
   generalize H0.
   clear H0.
   elim (eq_dim_dec d k).
  elim (eq_dart_dec d0 z).
   intros.
     elim H0.
     apply exd_not_nil with m.
    tauto.
    tauto.
   unfold succ in IHm.
     intros.
     rewrite IHm.
    tauto.
    tauto.
    tauto.
  intros.
    rewrite IHm.
   tauto.
   tauto.
   unfold succ in |- *.
     tauto.
Qed.

(* IDEM: *)

Lemma not_pred_B_1:forall(m:fmap)(k:dim)(z:dart),
   inv_hmap m -> ~pred m k z -> B_1 m k z = m.
Proof.
induction m.
 simpl in |- *.
   tauto.
 unfold pred in |- *.
   simpl in |- *.
   intros.
   unfold pred in IHm.
   rewrite IHm.
  tauto.
  tauto.
  tauto.
 unfold pred in |- *.
   simpl in |- *.
   unfold prec_L in |- *.
   intros.
   generalize H0.
   clear H0.
   elim (eq_dim_dec d k).
  elim (eq_dart_dec d1 z).
   intros.
     elim H0.
     apply exd_not_nil with m.
    tauto.
    tauto.
   unfold pred in IHm.
     intros.
     rewrite IHm.
    tauto.
    tauto.
    tauto.
  intros.
    rewrite IHm.
   tauto.
   tauto.
   unfold pred in |- *.
     tauto.
Qed.

(*=====================================================
           A, A_1 on B, B_1 for hmap : OK
=====================================================*)

Lemma A_B : forall (m:fmap)(k:dim)(x:dart),
  inv_hmap m ->
     A (B m k x) k x = nil.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   apply IHm.
   tauto.
 simpl in |- *.
   intros k x.
   elim (eq_dim_dec d k).
  elim (eq_dart_dec d0 x).
   intros.
     unfold prec_L in H.
     rewrite <-a.
     rewrite <-a0.
     unfold succ in H.
     elim (eq_nat_dec (A m d d0) nil).
    tauto.
    intro.
      tauto.
   simpl in |- *.
     elim (eq_dim_dec d k).
    elim (eq_dart_dec d0 x).
     tauto.
     intros.
       apply IHm.
       tauto.
    tauto.
  simpl in |- *.
    elim (eq_dim_dec d k).
   tauto.
   intros.
     apply IHm.
     tauto.
Qed.

(* Action_bis of B on A: OK *)

Lemma A_B_bis : forall (m:fmap)(k:dim)(x y:dart),
   y<>x -> A (B m k x) k y = A m k y.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   apply IHm.
   tauto.
 intros k x y.
   simpl in |- *.
   elim (eq_dim_dec d k).
  elim (eq_dart_dec d0 x).
   elim (eq_dart_dec d0 y).
    intros.
      rewrite <-a0 in H.
      rewrite <-a in H.
      tauto.
    tauto.
   simpl in |- *.
     elim (eq_dim_dec d k).
    elim (eq_dart_dec d0 y).
     tauto.
     intros.
       apply IHm.
       tauto.
    tauto.
  simpl in |- *.
    elim (eq_dim_dec d k).
   tauto.
   intros.
     apply IHm.
     tauto.
Qed.

(* Action_ter of B on A: OK *)

Lemma A_B_ter : forall (m:fmap)(k j:dim)(x y:dart),
   k<>j -> A (B m k x) j y = A m j y.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   tauto.
 intros k j x y.
   simpl in |- *.
   elim (eq_dim_dec d k).
  elim (eq_dart_dec d0 x).
   elim (eq_dim_dec d j).
    elim (eq_dart_dec d0 y).
     intros.
       rewrite <-a0 in H; rewrite <-a2 in H.
       tauto.
     tauto.
    tauto.
   simpl in |- *.
     elim (eq_dim_dec d j).
    intros.
      rewrite <-a in H; rewrite <-a0 in H; tauto.
    intros; apply IHm; tauto.
  simpl in |- *.
    elim (eq_dim_dec d j).
   elim (eq_dart_dec d0 y).
    tauto.
    intros; apply IHm; tauto.
   intros; apply IHm; tauto.
Qed.

 (* USEFUL LEMMAS *)

(* Deleting a link from an inexisting dart has no effect: *)

Lemma B_not_exd : forall (m:fmap)(k:dim)(x:dart),
  inv_hmap m -> ~exd m x -> B m k x = m.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   rewrite IHm.
  tauto.
  tauto.
  tauto.
 unfold B in |- *.
   fold B in |- *.
   unfold inv_hmap in |- *.
   fold inv_hmap in |- *.
   intros.
   simpl in H0.
   elim (eq_dim_dec d k).
  elim (eq_dart_dec d0 x).
   intros.
     unfold prec_L in H.
     rewrite a in H.
     tauto.
   rewrite IHm.
    tauto.
    tauto.
    tauto.
  rewrite IHm.
   tauto.
   tauto.
   tauto.
Qed.

Lemma not_exd_B : forall (m:fmap)(k:dim)(x:dart),
  inv_hmap m -> ~exd m x -> B m k x = m.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   rewrite IHm.
  tauto.
  tauto.
  tauto.
 unfold B in |- *.
   fold B in |- *.
   unfold inv_hmap in |- *.
   fold inv_hmap in |- *.
   intros.
   simpl in H0.
   elim (eq_dim_dec d k).
  elim (eq_dart_dec d0 x).
   intros.
     unfold prec_L in H.
     rewrite a in H.
     tauto.
   rewrite IHm.
    tauto.
    tauto.
    tauto.
  rewrite IHm.
   tauto.
   tauto.
   tauto.
Qed.

(* Corollary: deleting a link from nil has no effect: *)

Lemma B_nil : forall (m:fmap)(k:dim),
  inv_hmap m -> B m k nil = m.
Proof.
intros.
apply B_not_exd.
 tauto.
 apply not_exd_nil.
   tauto.
Qed.

(* IDEM: : *)

Lemma B_1_not_exd : forall (m:fmap)(k:dim)(x:dart),
  inv_hmap m -> ~exd m x -> B_1 m k x = m.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   rewrite IHm.
  tauto.
  tauto.
  tauto.
 unfold B_1 in |- *.
   fold B_1 in |- *.
   unfold inv_hmap in |- *.
   fold inv_hmap in |- *.
   intros.
   simpl in H0.
   elim (eq_dim_dec d k).
  elim (eq_dart_dec d1 x).
   intros.
     unfold prec_L in H.
     rewrite a in H.
     tauto.
   rewrite IHm.
    tauto.
    tauto.
    tauto.
  rewrite IHm.
   tauto.
   tauto.
   tauto.
Qed.

Lemma not_exd_B_1 : forall (m:fmap)(k:dim)(x:dart),
  inv_hmap m -> ~exd m x -> B_1 m k x = m.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   rewrite IHm.
  tauto.
  tauto.
  tauto.
 unfold B_1 in |- *.
   fold B_1 in |- *.
   unfold inv_hmap in |- *.
   fold inv_hmap in |- *.
   intros.
   simpl in H0.
   elim (eq_dim_dec d k).
  elim (eq_dart_dec d1 x).
   intros.
     unfold prec_L in H.
     rewrite a in H.
     tauto.
   rewrite IHm.
    tauto.
    tauto.
    tauto.
  rewrite IHm.
   tauto.
   tauto.
   tauto.
Qed.

Lemma B_1_nil : forall (m:fmap)(k:dim),
  inv_hmap m -> B_1 m k nil = m.
Proof.
intros.
apply B_1_not_exd.
 tauto.
 apply not_exd_nil.
   tauto.
Qed.

(* Action of B on A_1: OK *)

Lemma A_1_B : forall (m:fmap)(k:dim)(x:dart),
  inv_hmap m ->
     A_1 (B m k x) k (A m k x) = nil.
Proof.
intros m k x.
elim (eq_dart_dec x nil).
 intros.
   rewrite a.
   rewrite B_nil.
  rewrite A_nil.
   rewrite A_1_nil.
    tauto.
    tauto.
   tauto.
  tauto.
 intro.
   induction m.
  simpl in |- *.
    tauto.
  simpl in |- *.
    intros.
    apply IHm.
    tauto.
  simpl in |- *.
    elim (eq_dim_dec d k).
   elim (eq_dart_dec d0 x).
    intros.
      unfold prec_L in H.
      unfold pred in H.
      elim (eq_dart_dec (A_1 m d d1) nil).
     rewrite a0.
       tauto.
     tauto.
    simpl in |- *.
      elim (eq_dim_dec d k).
     elim (eq_dart_dec d1 (A m k x)).
      intros.
        unfold prec_L in H.
        assert (x = A_1 m k d1).
       rewrite a.
         symmetry  in |- *.
         apply A_1_A.
        tauto.
        unfold succ in |- *.
          rewrite <- a.
          apply (exd_not_nil m d1).
         tauto.
         tauto.
       unfold pred in H.
         rewrite a0 in H.
         rewrite <- H0 in H.
         tauto.
      intros.
        apply IHm.
        tauto.
     tauto.
   simpl in |- *.
     elim (eq_dim_dec d k).
    tauto.
    tauto.
Qed.

(* Action_bis of B on A_1 : OK*)

Lemma A_1_B_bis : forall (m:fmap)(k:dim)(x y:dart),
  inv_hmap m -> y <> A m k x ->
     A_1 (B m k x) k y = A_1 m k y.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   apply IHm.
  tauto.
  tauto.
 intros k x y.
   simpl in |- *.
   elim (eq_dim_dec d k).
  elim (eq_dart_dec d0 x).
   elim (eq_dart_dec d1 y).
    intro.
      symmetry  in a.
      tauto.
    tauto.
   simpl in |- *.
     elim (eq_dim_dec d k).
    elim (eq_dart_dec d1 y).
     tauto.
     intros.
       apply IHm.
      tauto.
      tauto.
    tauto.
  simpl in |- *.
    elim (eq_dim_dec d k).
   tauto.
   intros.
     apply IHm.
    tauto.
    tauto.
Qed.

(* Action_ter of B on A_1: IDEM *)

Lemma A_1_B_ter : forall (m:fmap)(k j:dim)(x y:dart),
  k<>j -> A_1 (B m k x) j y = A_1 m j y.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   tauto.
 intros k j x y.
   simpl in |- *.
   elim (eq_dim_dec d k).
  elim (eq_dart_dec d0 x).
   elim (eq_dim_dec d j).
    elim (eq_dart_dec d1 y).
     intros.
       rewrite <- a0 in H; rewrite <- a2 in H.
       tauto.
     tauto.
    tauto.
   simpl in |- *.
     elim (eq_dim_dec d j).
    intros.
      rewrite IHm.
     tauto.
     tauto.
    intros.
      apply IHm.
      tauto.
  simpl in |- *.
    elim (eq_dim_dec d j).
   elim (eq_dart_dec d1 y).
    tauto.
    intros.
      apply IHm.
      tauto.
   intros.
     apply IHm.
     tauto.
Qed.

(* SYMMETRICALLY, WE HAVE: *)

(* Action of B_1 on A_1: IDEM *)

Lemma A_1_B_1 : forall (m:fmap)(k:dim)(x:dart),
  inv_hmap m ->
     A_1 (B_1 m k x) k x = nil.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   apply IHm.
   tauto.
 simpl in |- *.
   intros k x.
   elim (eq_dim_dec d k).
  elim (eq_dart_dec d1 x).
   intros.
     unfold prec_L in H.
     rewrite <-a.
     rewrite <-a0.
     unfold pred in H.
     elim (eq_nat_dec (A_1 m d d1) nil).
    tauto.
    intro.
      tauto.
   simpl in |- *.
     elim (eq_dim_dec d k).
    elim (eq_dart_dec d1 x).
     tauto.
     intros.
       apply IHm.
       tauto.
    tauto.
  simpl in |- *.
    elim (eq_dim_dec d k).
   tauto.
   intros.
     apply IHm.
     tauto.
Qed.

(* Action_bis of B_1 on A_1: IDEM *)

Lemma A_1_B_1_bis : forall (m:fmap)(k:dim)(x y:dart),
  inv_hmap m -> y <> x ->
     A_1 (B_1 m k x) k y = A_1 m k y.
Proof.
induction m.
 simpl in |- *.
    tauto.
simpl in |- *.
  intros.
  apply IHm.
  tauto.
 tauto.
intros k x y.
  simpl in |- *.
  elim (eq_dim_dec d k).
 elim (eq_dart_dec d1 x).
  elim (eq_dart_dec d1 y).
   intros.
     rewrite a in a0.
      tauto.
   tauto.
 simpl in |- *.
   elim (eq_dim_dec d k).
  elim (eq_dart_dec d1 y).
    tauto.
  intros.
    apply IHm.
    tauto.
   tauto.
 simpl in |- *.
   elim (eq_dim_dec d k).
   tauto.
 intros.
    tauto.
simpl in |- *.
  elim (eq_dim_dec d k).
 elim (eq_dart_dec d1 y).
   tauto.
  tauto.
intros.
  apply IHm.
  tauto.
 tauto.
Qed.

(* TEST: OK: ALL CAN BE REVISED MORE SIMPLY ?...

Lemma A_1_B_1_bis_bis :
  forall (m:fmap)(k:dim)(x y:dart),
  y <> x ->
     A_1 (B_1 m k x) k y = A_1 m k y.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   apply IHm.
   tauto.
 intros k x y.
   simpl in |- *.
   elim (eq_dim_dec d k).
  elim (eq_dart_dec d1 x).
   elim (eq_dart_dec d1 y).
    intros.
      rewrite <- a0 in H.
      rewrite <- a in H.
      tauto.
    tauto.
   simpl in |- *.
     elim (eq_dim_dec d k).
    elim (eq_dart_dec d1 y).
     tauto.
     intros.
       apply IHm.
       tauto.
    tauto.
  simpl in |- *.
    elim (eq_dim_dec d k).
   tauto.
   intros.
     apply IHm.
     tauto.
Qed.

*)

(* Action_ter of B_1 on A: *)

Lemma A_1_B_1_ter : forall (m:fmap)(k j:dim)(x y:dart),
  k<>j -> A_1 (B_1 m k x) j y = A_1 m j y.
Proof.
induction m.
 simpl in |- *.
    tauto.
simpl in |- *.
   tauto.
intros k j x y.
  simpl in |- *.
  elim (eq_dim_dec d k).
 elim (eq_dart_dec d1 x).
  elim (eq_dim_dec d j).
   elim (eq_dart_dec d1 y).
    intros.
      rewrite <- a0 in H; rewrite <- a2 in H.
       tauto.
    tauto.
   tauto.
 simpl in |- *.
   elim (eq_dim_dec d j).
  intros.
    rewrite <- a in H; rewrite <- a0 in H;  tauto.
 intros; apply IHm;  tauto.
simpl in |- *.
  elim (eq_dim_dec d j).
 elim (eq_dart_dec d1 y).
   tauto.
 intros; apply IHm;  tauto.
intros; apply IHm;  tauto.
Qed.

(* Action of B_1 on A: IDEM *)

Lemma A_B_1 : forall (m:fmap)(k:dim)(x:dart),
  inv_hmap m ->
     A (B_1 m k x) k (A_1 m k x) = nil.
Proof.
intros m k x.
elim (eq_dart_dec x nil).
 intros.
   rewrite a in |- *.
   rewrite B_1_nil in |- *.
  rewrite A_1_nil in |- *.
   rewrite A_nil in |- *.
     tauto.
    tauto.
   tauto.
  tauto.
intro.
  induction m.
 simpl in |- *.
    tauto.
simpl in |- *.
  intros.
  apply IHm.
   tauto.
simpl in |- *.
  elim (eq_dim_dec d k).
 elim (eq_dart_dec d1 x).
  intros.
    unfold prec_L in H.
    unfold succ in H.
    elim (eq_dart_dec (A m d d0) nil).
   rewrite a0 in |- *.
      tauto.
   tauto.
 simpl in |- *.
   elim (eq_dim_dec d k).
  elim (eq_dart_dec d0 (A_1 m k x)).
   intros.
     unfold prec_L in H.
     assert (x = A m k d0).
    rewrite a in |- *.
      symmetry  in |- *.
      apply A_A_1.
      tauto.
    unfold pred in |- *.
      rewrite <- a in |- *.
      apply (exd_not_nil m d0).
      tauto.
     tauto.
   unfold succ in H.
     rewrite a0 in H.
     rewrite <- H0 in H.
      tauto.
  intros.
    apply IHm.
     tauto.
  tauto.
simpl in |- *.
  elim (eq_dim_dec d k).
  tauto.
 tauto.
Qed.

(* Action_bis of B_1 on A: IDEM: A FAIRE *)

Lemma A_B_1_bis : forall (m:fmap)(k:dim)(x y:dart),
  inv_hmap m -> y <> A_1 m k x ->
     A (B_1 m k x) k y = A m k y.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   apply IHm.
  tauto.
  tauto.
 intros k x y.
   simpl in |- *.
   elim (eq_dim_dec d k).
  elim (eq_dart_dec d1 x).
   elim (eq_dart_dec d0 y).
    intro.
      symmetry  in a.
      tauto.
    tauto.
   simpl in |- *.
     elim (eq_dim_dec d k).
    elim (eq_dart_dec d0 y).
     tauto.
     intros.
       apply IHm.
      tauto.
      tauto.
    tauto.
  simpl in |- *.
    elim (eq_dim_dec d k).
   tauto.
   intros.
     apply IHm.
    tauto.
    tauto.
Qed.

(* Action_ter of B_1 on A: IDEM: *)

Lemma A_B_1_ter : forall (m:fmap)(k j:dim)(x y:dart),
  k<>j -> A (B_1 m k x) j y = A m j y.
Proof.
induction m.
 simpl in |- *.
    tauto.
simpl in |- *.
   tauto.
intros k j x y.
  simpl in |- *.
  elim (eq_dim_dec d k).
 elim (eq_dart_dec d1 x).
  elim (eq_dim_dec d j).
   elim (eq_dart_dec d0 y).
    intros.
      rewrite <- a0 in H; rewrite <- a2 in H.
       tauto.
    tauto.
   tauto.
 simpl in |- *.
   elim (eq_dim_dec d j).
  intros.
    rewrite <- a0 in H.
     tauto.
 intros.
   rewrite IHm in |- *.
   tauto.
  tauto.
simpl in |- *.
  elim (eq_dim_dec d j).
 elim (eq_dart_dec d0 y).
   tauto.
 intros.
   apply IHm.
    tauto.
intros.
  apply IHm.
   tauto.
Qed.

(*=====================================================
                   top, bottom
====================================================*)

(* top AND bottom :*)

Fixpoint top
   (m:fmap)(k:dim)(z:dart){struct m}:dart:=
 match m with
     V => nil
  |  I m0 x _ _ =>
       if eq_dart_dec x z then z
       else top m0 k z
  |  L m0 k0 x y =>
       if eq_dim_dec k0 k
       then
         if eq_dart_dec x (top m0 k0 z) 
         then top m0 k0 y
	 else top m0 k0 z
       else top m0 k z
 end.

Fixpoint bottom
   (m:fmap)(k:dim)(z:dart){struct m}:dart:=
 match m with
     V => nil
  |  I m0 x _ _ =>
       if eq_dart_dec x z then z
       else bottom m0 k z
  |  L m0 k0 x y =>
       if (eq_dim_dec k0 k)
       then
         if eq_dart_dec y (bottom m0 k0 z)
         then bottom m0 k0 x
	 else bottom m0 k0 z
       else bottom m0 k z
 end.

(* OK : *)

Lemma top_nil : forall (m:fmap)(k:dim),
   inv_hmap m -> top m k nil = nil.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   elim (eq_dart_dec d nil).
  tauto.
  intro.
    apply IHm.
    tauto.
 simpl in |- *.
   unfold prec_L in |- *.
   intros.
   elim (eq_dim_dec d k).
  elim (eq_dart_dec d0 (top m d nil)).
   intros.
 rewrite IHm in a.
    absurd (d0 = nil).
     apply exd_not_nil with m.
      tauto; tauto.
      tauto.
     tauto.
    tauto.
   intros.
     rewrite IHm.
    tauto.
    tauto.
  intro.
    rewrite IHm.
   tauto.
   tauto.
Qed.

(* IDEM: A FAIRE *)

Lemma bottom_nil : forall (m:fmap)(k:dim),
  inv_hmap m -> bottom m k nil = nil.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   elim (eq_dart_dec d nil).
  tauto.
  intro.
    apply IHm.
    tauto.
 simpl in |- *.
   unfold prec_L in |- *.
   intros.
   elim (eq_dim_dec d k).
  elim (eq_dart_dec d1 (bottom m d nil)).
   intros.
 rewrite IHm in a.
    absurd (d1 = nil).
     apply exd_not_nil with m.
      tauto; tauto.
      tauto.
     tauto.
    tauto.
   intros.
     rewrite IHm.
    tauto.
    tauto.
  intro.
    rewrite IHm.
   tauto.
   tauto.
Qed.

(* OK: *)

Lemma not_exd_top : forall (m:fmap)(k:dim)(z:dart),
  inv_hmap m -> ~exd m z -> 
    top m k z = nil.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   elim (eq_dart_dec d nil).
  intro.
    elim (eq_dart_dec d z).
   tauto.
   intro.
     apply IHm.
    tauto.
    tauto.
  intro.
    elim (eq_dart_dec d z).
   tauto.
   intro.
     apply IHm.
    tauto.
    tauto.
 simpl in |- *.
   unfold prec_L in |- *.
   intros.
   elim (eq_dim_dec d k).
  elim (eq_dart_dec d0 (top m d z)).
   intros.
     rewrite IHm in a.
    absurd (d0 = nil).
     apply exd_not_nil with m.
      tauto.
      tauto.
     tauto.
    tauto.
    tauto.
   intros.
     apply IHm.
    tauto.
    tauto.
  intro.
    apply IHm.
   tauto.
   tauto.
Qed.

(* IDEM: A FAIRE *)

Lemma not_exd_bottom : forall (m:fmap)(k:dim)(z:dart),
  inv_hmap m -> ~exd m z -> 
    bottom m k z = nil.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   elim (eq_dart_dec d nil).
  intro.
    elim (eq_dart_dec d z).
   tauto.
   intro.
     apply IHm.
    tauto.
    tauto.
  intro.
    elim (eq_dart_dec d z).
   tauto.
   intro.
     apply IHm.
    tauto.
    tauto.
 simpl in |- *.
   unfold prec_L in |- *.
   intros.
   elim (eq_dim_dec d k).
  elim (eq_dart_dec d1 (bottom m d z)).
   intros.
     rewrite IHm in a.
    absurd (d1 = nil).
     apply exd_not_nil with m.
      tauto.
      tauto.
     tauto.
    tauto.
    tauto.
   intros.
     apply IHm.
    tauto.
    tauto.
  intro.
    apply IHm.
   tauto.
   tauto.
Qed.

(* OK: *)

Lemma exd_top:forall (m:fmap)(k:dim)(z:dart),
  inv_hmap m -> exd m z -> 
     exd m (top m k z).
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   unfold prec_I in |- *.
   intros.
   elim (eq_dart_dec d z).
  tauto.
  intros.
    generalize (IHm k z).
    tauto.
 simpl in |- *.
   unfold prec_L in |- *.
   intros.
   elim (eq_dim_dec d k).
  elim (eq_dart_dec d0 (top m d z)).
   intros.
     apply IHm.
    tauto.
    tauto.
   intros.
     apply IHm.
    tauto.
    tauto.
  intro.
    apply IHm.
   tauto.
   tauto.
Qed.

Lemma exd_bottom:forall (m:fmap)(k:dim)(z:dart),
  inv_hmap m -> exd m z -> 
     exd m (bottom m k z).
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   unfold prec_I in |- *.
   intros.
   elim (eq_dart_dec d z).
  tauto.
  intros.
    generalize (IHm k z).
    tauto.
 simpl in |- *.
   unfold prec_L in |- *.
   intros.
   elim (eq_dim_dec d k).
   elim (eq_dart_dec d1 (bottom m d z)).
   intros.
     apply IHm.
    tauto.
    tauto.
   intros.
     apply IHm.
    tauto.
    tauto.
  intro.
    apply IHm.
   tauto.
   tauto.
Qed.

(* OK: *)

Lemma nosucc_top : forall (m:fmap)(k:dim)(z:dart),
  inv_hmap m -> exd m z -> ~succ m k z -> 
    top m k z = z.
Proof.
induction m.
 unfold succ in |- *.
   simpl in |- *.
   tauto.
 unfold succ in |- *.
   simpl in |- *.
   intros.
   elim (eq_dart_dec d z).
  tauto.
  intro.
    unfold succ in IHm.
    apply IHm.
   tauto.
   tauto.
   tauto.
 unfold succ in |- *.
   simpl in |- *.
   unfold prec_L in |- *.
   intros k z Inv E.
   elim (eq_dim_dec d k).
  intro.
    rewrite a.
    elim (eq_dart_dec d0 z).
   elim (eq_dart_dec d0 (top m k z)).
    intros.
      absurd (d1 <> nil).
     tauto.
     apply exd_not_nil with m.
      tauto.
      tauto.
    intros.
      absurd (d1 <> nil).
     tauto.
     apply exd_not_nil with m.
      tauto.
      tauto.
   elim (eq_dart_dec d0 (top m k z)).
    intros.
      decompose [and] Inv.
      generalize (IHm k z H0 E).
      unfold succ in |- *.
      intro.
      rewrite H5 in a0.
     tauto; tauto.
     tauto.
    intros.
      apply IHm.
     tauto.
     tauto.
     unfold succ in |- *.
       tauto.
  intros.
    apply IHm.
   tauto.
   tauto.
   unfold succ in |- *; tauto.
Qed.

(* IDEM: *)

Lemma nopred_bottom : forall (m:fmap)(k:dim)(z:dart),
  inv_hmap m -> exd m z -> ~pred m k z -> 
     bottom m k z = z.
Proof.
induction m.
 unfold pred in |- *.
   simpl in |- *.
   tauto.
 unfold pred in |- *.
   simpl in |- *.
   intros.
   elim (eq_dart_dec d z).
  tauto.
  intro.
    unfold pred in IHm.
    apply IHm.
   tauto.
   tauto.
   tauto.
 unfold pred in |- *.
   simpl in |- *.
   unfold prec_L in |- *.
   intros k z Inv E.
   elim (eq_dim_dec d k).
  intro.
    rewrite a.
    elim (eq_dart_dec d1 z).
   elim (eq_dart_dec d1 (bottom m k z)).
    intros.
      absurd (d0 <> nil).
     tauto.
     apply exd_not_nil with m.
      tauto.
      tauto.
    intros.
      absurd (d0 <> nil).
     tauto.
     apply exd_not_nil with m.
      tauto.
      tauto.
   elim (eq_dart_dec d1 (bottom m k z)).
    intros.
      decompose [and] Inv.
      generalize (IHm k z H0 E).
      unfold pred in |- *.
      intro.
      rewrite H5 in a0.
     tauto; tauto.
     tauto.
    intros.
      apply IHm.
     tauto.
     tauto.
     unfold pred in |- *.
       tauto.
  intros.
    apply IHm.
   tauto.
   tauto.
   unfold pred in |- *; tauto.
Qed.

(* OK: top_bottom is a COROLLARY.. CHANGING NAMES ?... *)

Lemma top_bottom_bis:forall(m:fmap)(k:dim)(z:dart),
  inv_hmap m -> exd m z -> 
     top m k (bottom m k z) = top m k z.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   unfold prec_I in |- *.
   unfold succ in |- *.
   simpl in |- *.
   intros.
   elim (eq_dart_dec d z).
  elim (eq_dart_dec d z).
   tauto.
   tauto.
  elim (eq_dart_dec d (bottom m k z)).
   intros.
     rewrite a in H.
     generalize (exd_bottom m k z).
     tauto.
   intros.
     apply IHm.
    tauto.
    tauto.
 unfold succ in |- *.
   simpl in |- *.
   unfold prec_L in |- *.
   unfold succ in |- *.
   simpl in |- *.
   intros.
   elim (eq_dim_dec d k).
  elim (eq_dart_dec d1 (bottom m d z)).
   elim (eq_dart_dec d0 (top m d (bottom m d d0))).
    intros.
      elim (eq_dart_dec d0 (top m d z)).
     intro.
       tauto.
     intro.
       rewrite a0.
       rewrite IHm.
      tauto.
      tauto.
      tauto.
    elim (eq_dart_dec d0 (top m d z)).
     intros.
       rewrite IHm in b.
      rewrite nosucc_top in b.
       tauto.
       tauto; tauto.
       tauto.
       unfold succ in |- *.
         tauto.
      tauto.
      tauto.
     intros.
       rewrite IHm in b0.
      rewrite nosucc_top in b0.
       tauto.
       tauto.
       tauto.
       unfold succ in |- *.
         tauto.
      tauto.
      tauto.
   elim (eq_dart_dec d0 (top m d (bottom m d z))).
    intros.
      elim (eq_dart_dec d0 (top m d z)).
     tauto.
     intros.
       rewrite IHm in a.
      tauto.
      tauto.
      tauto.
    intros.
      elim (eq_dart_dec d0 (top m d z)).
     intros.
       rewrite IHm in b.
      tauto.
      tauto.
      tauto.
     intro.
       rewrite IHm.
      tauto.
      tauto.
      tauto.
  intro.
    rewrite IHm.
   tauto.
   tauto.
tauto.
Qed.

(* IDEM: *)

Lemma bottom_top_bis:forall(m:fmap)(k:dim)(z:dart),
  inv_hmap m -> exd m z -> 
     bottom m k (top m k z) = bottom m k z.
Proof.
induction m.
 simpl in |- *.
    tauto.
simpl in |- *.
  unfold prec_I in |- *.
  unfold pred in |- *.
  simpl in |- *.
  intros.
  elim (eq_dart_dec d z).
 elim (eq_dart_dec d z).
   tauto.
  tauto.
elim (eq_dart_dec d (top m k z)).
 intros.
   rewrite a in H.
   generalize (exd_top m k z).
    tauto.
intros.
  apply IHm.
  tauto.
 tauto.
simpl in |- *.
  unfold prec_L in |- *.
  unfold pred in |- *.
  unfold succ in |- *.
  simpl in |- *.
  intros.
  elim (eq_dim_dec d k).
 elim (eq_dart_dec d0 (top m d z)).
  elim (eq_dart_dec d1 (bottom m d (top m d d1))).
   intros.
     elim (eq_dart_dec d1 (bottom m d z)).
    intro.
       tauto.
   intro.
     rewrite a0 in |- *.
     rewrite IHm in |- *.
     tauto.
    tauto.
    tauto.
  elim (eq_dart_dec d1 (bottom m d z)).
   intros.
     rewrite IHm in b.
    rewrite nopred_bottom in b.
      tauto.
     tauto;  tauto.
     tauto.
    unfold pred in |- *.
       tauto.
    tauto.
    tauto.
  intros.
    rewrite IHm in b0.
   rewrite nopred_bottom in b0.
     tauto.
    tauto.
    tauto.
   unfold pred in |- *.
      tauto.
   tauto.
   tauto.
 elim (eq_dart_dec d1 (bottom m d (top m d z))).
  intros.
    elim (eq_dart_dec d1 (bottom m d z)).
    tauto.
  intros.
    rewrite IHm in a.
    tauto.
   tauto.
   tauto.
 intros.
   elim (eq_dart_dec d1 (bottom m d z)).
  intros.
    rewrite IHm in b.
    tauto.
   tauto.
   tauto.
 intro.
   rewrite IHm in |- *.
   tauto.
  tauto.
  tauto.
intro.
  rewrite IHm in |- *.
  tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma cA_bottom : forall (m:fmap)(k:dim)(z:dart),
  inv_hmap m -> exd m z -> ~succ m k z ->
     cA m k z = bottom m k z. 
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   unfold prec_I in |- *.
   unfold succ in |- *.
   simpl in |- *.
   intros.
   elim (eq_dart_dec d z).
  tauto.
  intro.
    apply IHm; tauto.
 unfold succ in |- *.
   simpl in |- *.
   unfold prec_L in |- *.
   intros k z Inv E.
   decompose [and] Inv.
   elim (eq_dim_dec d k).
  elim (eq_dart_dec d0 z).
   intros.
     absurd (d1 <> nil).
    tauto.
    apply exd_not_nil with m.
     tauto.
     tauto.
   elim (eq_dart_dec (cA_1 m k d1) z).
    intros.
      clear Inv.
      elim (eq_dart_dec d1 (bottom m d z)).
     intro.
       rewrite a0.
       apply IHm.
      tauto.
      tauto.
      rewrite a0 in H2.
        tauto.
     intro.
       rewrite <- IHm in b0.
      rewrite <- a in b0.
        rewrite a0 in b0.
        rewrite cA_cA_1 in b0.
       tauto.
       tauto.
       tauto.
      tauto.
      tauto.
      unfold succ in |- *.
        rewrite a0.
        tauto.
    intros.
      elim (eq_dart_dec d1 (bottom m d z)).
     intro.
       clear Inv.
       rewrite a in a0.
       rewrite <- IHm in a0.
      rewrite a.
        rewrite a0 in b.
        rewrite cA_1_cA in b.
       tauto.
       tauto.
       tauto.
      tauto.
      tauto.
      unfold succ in |- *.
        tauto.
     intro.
       rewrite a.
       apply IHm.
      tauto.
      tauto.
      unfold succ in |- *.
        tauto.
  intros.
    apply IHm.
   tauto.
   tauto.
   unfold succ in |- *.
     tauto.
Qed.

(* IDEM: *)

Lemma cA_1_top : forall (m:fmap)(k:dim)(z:dart),
  inv_hmap m -> exd m z -> ~pred m k z ->
     cA_1 m k z = top m k z. 
Proof.
 induction m.
 simpl in |- *.
    tauto.
simpl in |- *.
  unfold prec_I in |- *.
  unfold pred in |- *.
  simpl in |- *.
  intros.
  elim (eq_dart_dec d z).
  tauto.
intro.
  apply IHm;  tauto.
unfold pred in |- *.
  simpl in |- *.
  unfold prec_L in |- *.
  intros k z Inv E.
  decompose [and] Inv.
  elim (eq_dim_dec d k).
 elim (eq_dart_dec d1 z).
  intros.
     absurd (d0 <> nil).
    tauto.
  apply exd_not_nil with m.
    tauto.
   tauto.
 elim (eq_dart_dec (cA m k d0) z).
  intros.
    clear Inv.
    elim (eq_dart_dec d0 (top m d z)).
   intro.
     rewrite a0 in |- *.
     apply IHm.
     tauto.
    tauto.
   rewrite a0 in H3.
      tauto.
  intro.
    rewrite <- IHm in b0.
   rewrite <- a in b0.
     rewrite a0 in b0.
     rewrite cA_1_cA in b0.
     tauto.
    tauto.
    tauto.
   tauto.
   tauto.
  unfold pred in |- *.
    rewrite a0 in |- *.
     tauto.
 intros.
   elim (eq_dart_dec d0 (top m d z)).
  intro.
    clear Inv.
    rewrite a in a0.
    rewrite <- IHm in a0.
   rewrite a in |- *.
     rewrite a0 in b.
     rewrite cA_cA_1 in b.
     tauto.
    tauto.
    tauto.
   tauto.
   tauto.
  unfold pred in |- *.
     tauto.
 intro.
   rewrite a in |- *.
   apply IHm.
   tauto.
  tauto.
 unfold pred in |- *.
    tauto.
intros.
  apply IHm.
  tauto.
 tauto.
unfold pred in |- *.
   tauto.
Qed.

(* OK: *)

Lemma cA_eq_aux : forall(m:fmap)(k:dim)(z:dart),
  inv_hmap m -> exd m z -> 
    cA m k z = 
       if succ_dec m k z then A m k z
       else bottom m k z.  
Proof.
intros.
elim (succ_dec m k z).
 intro.
   generalize (A_cA m k z (A m k z) H H0).
   intros.
   apply H1.
  apply succ_exd_A.
   tauto.
   tauto.
  tauto.
 apply cA_bottom.
  tauto.
  tauto.
Qed.

(* OK, WITHOUT exd m z : *)

Lemma cA_eq : forall(m:fmap)(k:dim)(z:dart),
  inv_hmap m ->  
    cA m k z = 
       if succ_dec m k z then A m k z
       else bottom m k z.  
Proof.
intros.
elim (succ_dec m k z).
 intro.
   assert (exd m z).
  apply succ_exd with k.
   tauto.
   tauto.
  generalize (A_cA m k z (A m k z) H H0).
    intros.
    apply H1.
   apply succ_exd_A.
    tauto.
    tauto.
   tauto.
 intro.
   elim (exd_dec m z).
  intro.
    apply cA_bottom.
   tauto.
   tauto.
   tauto.
  intro.
    rewrite not_exd_bottom.
   rewrite not_exd_cA.
    tauto.
    tauto.
    tauto.
   tauto.
   tauto.
Qed.

(* IDEM: *)

Lemma cA_1_eq_aux : forall(m:fmap)(k:dim)(z:dart),
  inv_hmap m -> exd m z -> 
    cA_1 m k z = 
       if pred_dec m k z then A_1 m k z
       else top m k z.  
Proof.
intros.
elim (pred_dec m k z).
 intro.
   generalize (A_1_cA_1 m k z (A_1 m k z) H H0).
   intros.
   apply H1.
  apply pred_exd_A_1.
   tauto.
   tauto.
  tauto.
 apply cA_1_top.
  tauto.
  tauto.
Qed.

(* IDEM: WITHOUT exd m z: *)

Lemma cA_1_eq : forall(m:fmap)(k:dim)(z:dart),
  inv_hmap m ->  
    cA_1 m k z = 
       if pred_dec m k z then A_1 m k z
       else top m k z.  
Proof.
intros.
elim (pred_dec m k z).
 intro.
   assert (exd m z).
  apply pred_exd with k.
   tauto.
   tauto.
  generalize (A_1_cA_1 m k z (A_1 m k z) H H0).
    intros.
    apply H1.
   apply pred_exd_A_1.
    tauto.
    tauto.
   tauto.
 intro.
   elim (exd_dec m z).
  intro.
    apply cA_1_top.
   tauto.
   tauto.
   tauto.
  intro.
    rewrite not_exd_top.
   rewrite not_exd_cA_1.
    tauto.
    tauto.
    tauto.
   tauto.
   tauto.
Qed.

(* OK: *)

Lemma top_bottom : forall (m:fmap)(k:dim)(z:dart),
  inv_hmap m -> exd m z -> ~succ m k z ->  
     top m k (bottom m k z) = z.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   unfold prec_I in |- *.
   unfold succ in |- *.
   simpl in |- *.
   intros.
   elim (eq_dart_dec d z).
  elim (eq_dart_dec d z).
   tauto.
   tauto.
  elim (eq_dart_dec d (bottom m k z)).
   intros.
     rewrite a in H.
     generalize (exd_bottom m k z).
     tauto.
   intros.
     apply IHm.
    tauto.
    tauto.
    unfold succ in |- *.
      tauto.
 simpl in |- *.
   unfold prec_L in |- *.
   unfold succ in |- *.
   simpl in |- *.
   intros.
   generalize H1.
   elim (eq_dim_dec d k).
  clear H1.
    elim (eq_dart_dec d0 z).
   intros.
     absurd (d1 <> nil).
    tauto.
    apply exd_not_nil with m.
     tauto.
     tauto.
   elim (eq_dart_dec d1 (bottom m d z)).
    elim (eq_dart_dec d0 (top m d (bottom m d d0))).
     intros.
       rewrite a0.
       apply IHm.
      tauto.
      tauto.
      unfold succ in |- *.
        rewrite a1.
        tauto.
     intros.
       rewrite IHm in b.
      tauto.
      tauto.
      tauto.
      tauto.
    elim (eq_dart_dec d0 (top m d (bottom m d z))).
     intros.
       rewrite IHm in a.
      tauto.
      tauto.
      tauto.
      unfold succ in |- *.
        rewrite a0.
        tauto.
     intros.
       apply IHm.
      tauto.
      tauto.
      unfold succ in |- *.
        rewrite a.
        tauto.
  intros.
    apply IHm.
   tauto.
   tauto.
   unfold succ.
tauto.
Qed.

(* IDEM: *)

Lemma bottom_top : forall (m:fmap)(k:dim)(z:dart),
  inv_hmap m -> exd m z -> ~pred m k z ->  
     bottom m k (top m k z) = z.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   unfold prec_I in |- *.
   unfold pred in |- *.
   simpl in |- *.
   intros.
   elim (eq_dart_dec d z).
  elim (eq_dart_dec d z).
   tauto.
   tauto.
  elim (eq_dart_dec d (top m k z)).
   intros.
     rewrite a in H.
     generalize (exd_top m k z).
     tauto.
   intros.
     apply IHm.
    tauto.
    tauto.
    unfold pred in |- *.
      tauto.
 simpl in |- *.
   unfold prec_L in |- *.
   unfold pred in |- *.
   simpl in |- *.
   intros.
   generalize H1.
   elim (eq_dim_dec d k).
  clear H1.
    elim (eq_dart_dec d1 z).
   intros.
     absurd (d0 <> nil).
    tauto.
    apply exd_not_nil with m.
     tauto.
     tauto.
   elim (eq_dart_dec d0 (top m d z)).
    elim (eq_dart_dec d1 (bottom m d (top m d d1))).
     intros.
       rewrite a0.
       apply IHm.
      tauto.
      tauto.
      unfold pred in |- *.
        rewrite a1.
        tauto.
     intros.
       rewrite IHm in b.
      tauto.
      tauto.
      tauto.
      tauto.
    elim (eq_dart_dec d1 (bottom m d (top m d z))).
     intros.
       rewrite IHm in a.
      tauto.
      tauto.
      tauto.
      unfold pred in |- *.
        rewrite a0.
        tauto.
     intros.
       apply IHm.
      tauto.
      tauto.
      unfold pred in |- *.
        rewrite a.
        tauto.
  intros.
    apply IHm.
   tauto.
   tauto.
   unfold pred.
tauto.
Qed.

(* OK: *)

Lemma top_A : forall (m:fmap)(k:dim)(z:dart),
  inv_hmap m -> succ m k z -> 
    top m k (A m k z) = top m k z.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   unfold prec_I in |- *.
   unfold succ in |- *.
   simpl in |- *.
   intros.
   elim (eq_dart_dec d (A m k z)).
  intro.
    rewrite a in H.
    absurd (exd m (A m k z)).
   tauto.
   apply succ_exd_A.
    tauto.
    unfold succ in |- *.
      tauto.
  elim (eq_dart_dec d z).
   intros.
     rewrite a in H.
     absurd (exd m z).
    tauto.
    apply succ_exd with k.
     tauto.
     unfold succ in |- *.
       tauto.
   intros.
     apply IHm.
    tauto.
    tauto.
 unfold succ in |- *.
   simpl in |- *.
   unfold prec_L in |- *.
   intros.
   generalize H0.
   clear H0.
   elim (eq_dim_dec d k).
  elim (eq_dart_dec d0 z).
   elim (eq_dart_dec d0 (top m d d1)).
    elim (eq_dart_dec d0 (top m d z)).
     tauto.
     intros.
       rewrite cA_eq in H.
      generalize H.
        clear H.
        elim (succ_dec m d d0).
       tauto.
       intros.
         rewrite a in H.
         rewrite bottom_top in H.
        tauto.
        tauto.
        tauto.
        tauto.
      tauto.
    elim (eq_dart_dec d0 (top m d z)).
     tauto.
     intros.
       rewrite <- a in b.
       rewrite nosucc_top in b.
      tauto.
      tauto.
      tauto.
      tauto.
   elim (eq_dart_dec d0 (top m d (A m k z))).
    elim (eq_dart_dec d0 (top m d z)).
     tauto.
     intros.
       rewrite a0 in a.
       rewrite IHm in a.
      rewrite a0 in b.
        tauto.
      tauto.
      unfold succ in |- *.
        tauto.
    elim (eq_dart_dec d0 (top m d z)).
     intros.
       rewrite a0 in b.
       rewrite IHm in b.
      rewrite a0 in a.
        tauto.
      tauto.
      unfold succ in |- *; tauto.
     intros.
       rewrite a.
       apply IHm.
      tauto.
      unfold succ in |- *.
        tauto.
  intros.
    apply IHm.
   tauto.
   unfold succ in |- *.
     tauto.
Qed.

Lemma bottom_A : forall (m:fmap)(k:dim)(z:dart),
  inv_hmap m -> succ m k z -> 
    bottom m k (A m k z) = bottom m k z.
Proof.
 induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   unfold prec_I in |- *.
   unfold succ in |- *.
   simpl in |- *.
   intros.
   elim (eq_dart_dec d (A m k z)).
  intro.
    rewrite a in H.
    absurd (exd m (A m k z)).
   tauto.
   apply succ_exd_A.
    tauto.
    unfold succ in |- *.
      tauto.
  elim (eq_dart_dec d z).
   intros.
     rewrite a in H.
     absurd (exd m z).
    tauto.
    apply succ_exd with k.
     tauto.
     unfold succ in |- *.
       tauto.
   intros.
     apply IHm.
    tauto.
    tauto.
 unfold succ in |- *.
   simpl in |- *.
   unfold prec_L in |- *.
   intros.
   generalize H0.
   clear H0.
   elim (eq_dim_dec d k).
  elim (eq_dart_dec d0 z).
   elim (eq_dart_dec d1 (bottom m d d1)).
    elim (eq_dart_dec d1 (bottom m d z)).
     tauto.
     intros.
       rewrite a0.
       tauto.
    elim (eq_dart_dec d1 (bottom m d z)).
     intros.
       rewrite cA_eq in H.
      generalize H.
        clear H.
        elim (succ_dec m d d0).
       tauto.
       intros.
         rewrite a0 in H.
         symmetry  in a.
         tauto.
      tauto.
     intros.
       rewrite nopred_bottom in b0.
      tauto.
      tauto.
      tauto.
      tauto.
   elim (eq_dart_dec d1 (bottom m d (A m k z))).
    elim (eq_dart_dec d1 (bottom m d z)).
     tauto.
     intros.
       rewrite a0 in a.
       rewrite a0 in b.
       rewrite IHm in a.
      tauto.
      tauto.
      unfold succ in |- *.
        tauto.
    elim (eq_dart_dec d1 (bottom m d z)).
     intros.
       rewrite a0 in b.
       rewrite a0 in a.
       rewrite IHm in b.
      tauto.
      tauto.
      unfold succ in |- *.
        tauto.
     intros.
       rewrite a.
       apply IHm.
      tauto.
      unfold succ in |- *.
        tauto.
  intros.
    apply IHm.
   tauto.
   unfold succ in |- *.
     tauto.
Qed.

(* IDEM: *)

Lemma bottom_A_1 : forall (m:fmap)(k:dim)(z:dart),
  inv_hmap m -> pred m k z -> 
    bottom m k (A_1 m k z) = bottom m k z.
Proof.
induction m.
 simpl in |- *.
    tauto.
simpl in |- *.
  unfold prec_I in |- *.
  unfold pred in |- *.
  simpl in |- *.
  intros.
  elim (eq_dart_dec d (A_1 m k z)).
 intro.
   rewrite a in H.
    absurd (exd m (A_1 m k z)).
   tauto.
 apply pred_exd_A_1.
   tauto.
 unfold pred in |- *.
    tauto.
elim (eq_dart_dec d z).
 intros.
   rewrite a in H.
    absurd (exd m z).
   tauto.
 apply pred_exd with k.
   tauto.
 unfold pred in |- *.
    tauto.
intros.
  apply IHm.
  tauto.
 tauto.
unfold pred in |- *.
  simpl in |- *.
  unfold prec_L in |- *.
  intros.
  generalize H0.
  clear H0.
  elim (eq_dim_dec d k).
 elim (eq_dart_dec d1 z).
  elim (eq_dart_dec d1 (bottom m d d0)).
   elim (eq_dart_dec d1 (bottom m d z)).
     tauto.
   intros.
     rewrite cA_eq in H.
    generalize H.
      clear H.
      elim (succ_dec m d d0).
      tauto.
    intros.
      rewrite a in H.
       tauto.
    tauto.
  intros.
    elim (eq_dart_dec d1 (bottom m d z)).
    tauto.
  intro.
    rewrite <- a in b0.
    elim b0.
    rewrite nopred_bottom in |- *.
    tauto.
   tauto.
   tauto.
   tauto.
 elim (eq_dart_dec d1 (bottom m d (A_1 m k z))).
  elim (eq_dart_dec d1 (bottom m d z)).
    tauto.
  intros.
    rewrite a0 in a.
    rewrite IHm in a.
   rewrite a0 in b.
      tauto.
   tauto.
  unfold pred in |- *.
     tauto.
 elim (eq_dart_dec d1 (bottom m d z)).
  intros.
    rewrite a0 in b.
    rewrite IHm in b.
   rewrite a0 in a.
      tauto.
   tauto.
  unfold pred in |- *;  tauto.
 intros.
   rewrite a in |- *.
   apply IHm.
   tauto.
 unfold pred in |- *.
    tauto.
intros.
  apply IHm.
  tauto.
unfold pred in |- *.
   tauto.
Qed.

(* IDEM: *)

Lemma top_A_1 : forall (m:fmap)(k:dim)(z:dart),
  inv_hmap m -> pred m k z -> 
    top m k (A_1 m k z) = top m k z.
Proof.
induction m.
 simpl in |- *.
    tauto.
simpl in |- *.
  unfold prec_I in |- *.
  unfold pred in |- *.
  simpl in |- *.
  intros.
  elim (eq_dart_dec d (A_1 m k z)).
 intro.
   rewrite a in H.
    absurd (exd m (A_1 m k z)).
   tauto.
 apply pred_exd_A_1.
   tauto.
 unfold pred in |- *.
    tauto.
elim (eq_dart_dec d z).
 intros.
   rewrite a in H.
    absurd (exd m z).
   tauto.
 apply pred_exd with k.
   tauto.
 unfold pred in |- *.
    tauto.
intros.
  apply IHm.
  tauto.
 tauto.
unfold pred in |- *.
  simpl in |- *.
  unfold prec_L in |- *.
  intros.
  generalize H0.
  clear H0.
  elim (eq_dim_dec d k).
 elim (eq_dart_dec d1 z).
  elim (eq_dart_dec d0 (top m d d0)).
   elim (eq_dart_dec d0 (top m d z)).
     tauto.
   intros.
     rewrite a0 in |- *.
      tauto.
  intros.
    rewrite nosucc_top in b.
    tauto.
   tauto.
   tauto.
   tauto.
 elim (eq_dart_dec d0 (top m d (A_1 m k z))).
  elim (eq_dart_dec d0 (top m d z)).
    tauto.
  intros.
    rewrite a0 in a.
    rewrite a0 in b.
    rewrite IHm in a.
    tauto.
   tauto.
  unfold pred in |- *.
     tauto.
 elim (eq_dart_dec d0 (top m d z)).
  intros.
    rewrite a0 in b.
    rewrite a0 in a.
    rewrite IHm in b.
    tauto.
   tauto.
  unfold pred in |- *.
     tauto.
 intros.
   rewrite a in |- *.
   apply IHm.
   tauto.
 unfold pred in |- *.
    tauto.
intros.
  apply IHm.
  tauto.
unfold pred in |- *.
   tauto.
Qed.

(* OK: *)

Lemma not_succ_top : forall (m:fmap)(k:dim)(z:dart),
  inv_hmap m ->  
     ~succ m k (top m k z).
Proof.
unfold succ in |- *.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   unfold prec_I in |- *.
   intros k z Inv.
   elim (eq_dart_dec d z).
  intros.
    assert (A m k z = nil).
   apply not_exd_A_nil.
    tauto.
    rewrite <- a.
      tauto.
   rewrite H.
     tauto.
  intro.
    apply IHm.
    tauto.
 simpl in |- *.
   unfold prec_L in |- *.
   intros k z Inv.
   elim (eq_dim_dec d k).
  intros.
    elim (eq_dart_dec d0 (top m d z)).
   intro.
     elim (eq_dart_dec d0 (top m d d1)).
    intro.
      generalize Inv.
      rewrite cA_eq.
     elim (succ_dec m d d0).
      tauto.
      rewrite a1.
        rewrite bottom_top.
       tauto.
       tauto.
       tauto.
       tauto.
     tauto.
    intros.
      rewrite a.
      apply IHm.
      tauto.
   elim (eq_dart_dec d0 (top m d z)).
    tauto.
    intros.
      rewrite a.
      apply IHm.
      tauto.
  intro.
    apply IHm.
    tauto.
Qed.

(* IDEM: *)

Lemma not_pred_bottom : forall (m:fmap)(k:dim)(z:dart),
  inv_hmap m ->  
     ~pred m k (bottom m k z).
Proof.
unfold pred in |- *.
induction m.
 simpl in |- *.
    tauto.
simpl in |- *.
  unfold prec_I in |- *.
  intros k z Inv.
  elim (eq_dart_dec d z).
 intros.
   assert (A_1 m k z = nil).
  apply not_exd_A_1_nil.
    tauto.
  rewrite <- a in |- *.
     tauto.
 rewrite H in |- *.
    tauto.
intro.
  apply IHm.
   tauto.
simpl in |- *.
  unfold prec_L in |- *.
  intros k z Inv.
  elim (eq_dim_dec d k).
 intros.
   elim (eq_dart_dec d1 (bottom m d z)).
  intro.
    elim (eq_dart_dec d1 (bottom m d d0)).
   intro.
     generalize Inv.
     rewrite cA_eq in |- *.
    elim (succ_dec m d d0).
      tauto.
    rewrite a1 in |- *.
       tauto.
    tauto.
  intros.
    rewrite a in |- *.
    apply IHm.
     tauto.
 elim (eq_dart_dec d1 (bottom m d z)).
   tauto.
 rewrite a in |- *.
   intros.
   apply IHm.
    tauto.
intro.
  apply IHm.
   tauto.
Qed.

(* OK: *)

Lemma top_top_1 : forall (m:fmap)(k:dim)(z:dart),
  inv_hmap m -> ~ succ m k z ->
    top m k (top m k z) = top m k z.
Proof.
intros.
 elim (exd_dec m z).
  intros.
    rewrite nosucc_top.
   tauto.
   tauto.
   apply exd_top.
    tauto.
    tauto.
   rewrite nosucc_top.
    tauto.
    tauto.
    tauto.
    tauto.
  intros.
    rewrite not_exd_top.
   rewrite not_exd_top.
    tauto.
    tauto.
    tauto.
   tauto.
   rewrite not_exd_top.
    apply not_exd_nil.
      tauto.
    tauto.
    tauto.
Qed.

Lemma top_top_2 : forall (m:fmap)(k:dim)(z:dart),
  inv_hmap m -> succ m k z ->
    top m k (top m k z) = top m k z.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   unfold succ in |- *.
   simpl in |- *.
   intros.
   elim (eq_dart_dec d z).
  intro.
    elim (eq_dart_dec d z).
   tauto.
   tauto.
  elim (eq_dart_dec d (top m k z)).
   tauto.
   intros.
     apply IHm.
    tauto.
    unfold succ in |- *.
      tauto.
 simpl in |- *.
   unfold prec_L in |- *.
   unfold succ in |- *.
   unfold pred in |- *.
   simpl in |- *.
   intros.
   generalize H0.
   clear H0.
   elim (eq_dim_dec d k).
  intro.
    rewrite a.
    elim (eq_dart_dec d0 z).
   intros.
     elim (eq_dart_dec d0 (top m k z)).
    elim (eq_dart_dec d0 (top m k (top m k d1))).
     tauto.
     intros.
       elim (succ_dec m k d1).
      apply IHm.
        tauto.
      apply top_top_1.
        tauto.
    elim (eq_dart_dec d0 (top m k (top m k z))).
     intros.
       rewrite a1 in b.
       elim b.
       rewrite <- a0.
       apply top_top_1.
      tauto.
      unfold succ in |- *.
        rewrite <- a.
        tauto.
     intros.
       rewrite <- a0 in b0.
       rewrite nosucc_top in b0.
      tauto.
      tauto.
      tauto.
      unfold succ in |- *.
        rewrite <- a.
        tauto.
   elim (eq_dart_dec d0 (top m k z)).
    elim (eq_dart_dec d0 (top m k (top m k d1))).
     tauto.
     intros.
       elim (succ_dec m k d1).
      apply IHm.
        tauto.
      apply top_top_1.
        tauto.
    elim (eq_dart_dec d0 (top m k (top m k z))).
     intros.
       rewrite IHm in a0.
      tauto.
      tauto.
      unfold succ in |- *.
        tauto.
     intros.
       apply IHm.
      tauto.
      unfold succ in |- *.
        tauto.
  intros.
    apply IHm.
   tauto.
   unfold succ in |- *.
     tauto.
Qed.

Lemma top_top : forall (m:fmap)(k:dim)(z:dart),
  inv_hmap m -> 
    top m k (top m k z) = top m k z.
Proof.
intros.
elim (succ_dec m k z).
 apply top_top_2.
   tauto.
 apply top_top_1.
   tauto.
Qed.

(* IDEM: *)

Lemma bottom_bottom_1 : forall (m:fmap)(k:dim)(z:dart),
  inv_hmap m -> ~ pred m k z ->
    bottom m k (bottom m k z) = bottom m k z.
Proof.
intros.
 elim (exd_dec m z).
  intros.
    rewrite nopred_bottom.
   tauto.
   tauto.
   apply exd_bottom.
    tauto.
    tauto.
   rewrite nopred_bottom.
    tauto.
    tauto.
    tauto.
    tauto.
  intros.
    rewrite not_exd_bottom.
   rewrite not_exd_bottom.
    tauto.
    tauto.
    tauto.
   tauto.
   rewrite not_exd_bottom.
    apply not_exd_nil.
      tauto.
    tauto.
    tauto.
Qed.

Lemma bottom_bottom_2 : forall (m:fmap)(k:dim)(z:dart),
  inv_hmap m -> pred m k z ->
    bottom m k (bottom m k z) = bottom m k z.
Proof.
 induction m.
 simpl in |- *.
    tauto.
simpl in |- *.
  unfold pred in |- *.
  simpl in |- *.
  intros.
  elim (eq_dart_dec d z).
 intro.
   elim (eq_dart_dec d z).
   tauto.
  tauto.
elim (eq_dart_dec d (bottom m k z)).
  tauto.
intros.
  apply IHm.
  tauto.
unfold pred in |- *.
   tauto.
simpl in |- *.
  unfold prec_L in |- *.
  unfold succ in |- *.
  unfold pred in |- *.
  simpl in |- *.
  intros.
  generalize H0.
  clear H0.
  elim (eq_dim_dec d k).
 intro.
   rewrite a in |- *.
   elim (eq_dart_dec d1 z).
  intros.
    elim (eq_dart_dec d1 (bottom m k z)).
   elim (eq_dart_dec d1 (bottom m k (bottom m k d0))).
     tauto.
   intros.
     elim (pred_dec m k d0).
    apply IHm.
       tauto.
   apply bottom_bottom_1.
      tauto.
  elim (eq_dart_dec d1 (bottom m k (bottom m k z))).
   intros.
     rewrite a1 in b.
     elim b.
     rewrite <- a0 in |- *.
     apply bottom_bottom_1.
     tauto.
   unfold pred in |- *.
     rewrite <- a in |- *.
      tauto.
  intros.
    rewrite <- a0 in b0.
    rewrite nopred_bottom in b0.
    tauto.
   tauto.
   tauto.
  unfold pred in |- *.
    rewrite <- a in |- *.
     tauto.
 elim (eq_dart_dec d1 (bottom m k z)).
  elim (eq_dart_dec d1 (bottom m k (bottom m k d0))).
    tauto.
  intros.
    elim (pred_dec m k d0).
   apply IHm.
      tauto.
  apply bottom_bottom_1.
     tauto.
 elim (eq_dart_dec d1 (bottom m k (bottom m k z))).
  intros.
    rewrite IHm in a0.
    tauto.
   tauto.
  unfold pred in |- *.
     tauto.
 intros.
   apply IHm.
   tauto.
 unfold pred in |- *.
    tauto.
intros.
  apply IHm.
  tauto.
unfold pred in |- *.
   tauto.
Qed.

(* IDEM:*)

Lemma bottom_bottom : forall (m:fmap)(k:dim)(z:dart),
  inv_hmap m -> 
    bottom m k (bottom m k z) = bottom m k z.
Proof.
intros.
elim (pred_dec m k z).
 apply bottom_bottom_2.
   tauto.
 apply bottom_bottom_1.
   tauto.
Qed.

(* OK: *)

Lemma succ_bottom:forall (m:fmap)(k:dim)(x:dart), 
 inv_hmap m -> succ m k x ->
   bottom m k x <> A m k x. 
Proof.
induction m.
 simpl in |- *.
   unfold succ in |- *.
   simpl in |- *.
   tauto.
 simpl in |- *.
   unfold succ in |- *.
   unfold prec_I in |- *.
   simpl in |- *.
   intros.
   elim (eq_dart_dec d x).
  intro.
    rewrite a in H.
    elim H0.
    apply not_exd_A_nil.
   tauto.
   tauto.
  intro.
    apply IHm.
   tauto.
   unfold succ in |- *.
     tauto.
 unfold succ in |- *.
   simpl in |- *.
   unfold prec_L in |- *.
   unfold succ in |- *.
   unfold pred in |- *.
   intros.
   generalize H0.
   clear H0.
   elim (eq_dim_dec d k).
  intro.
    rewrite a.
    elim (eq_dart_dec d0 x).
   intros.
     rewrite a0.
     elim (eq_dart_dec d1 (bottom m k x)).
    intro.
      rewrite a1 in H.
      rewrite a0 in H.
      rewrite a in H.
      generalize (cA_eq m k x).
      elim (succ_dec m k x).
     unfold succ in |- *.
       tauto.
     unfold succ in |- *.
       tauto.
    intro.
      intro.
      symmetry  in H1.
      tauto.
   elim (eq_dart_dec d1 (bottom m k x)).
    intros.
      rewrite <- bottom_A in a0.
     intro.
       rewrite <- H1 in a0.
       rewrite bottom_bottom in a0.
      generalize H.
        rewrite cA_eq.
       elim (succ_dec m d d0).
        unfold succ in |- *.
          tauto.
        symmetry  in a0.
          rewrite a.
          tauto.
       tauto.
      tauto.
     tauto.
     unfold succ in |- *.
       tauto.
    intros.
      apply IHm.
     tauto.
     unfold succ in |- *.
       tauto.
  intros.
    apply IHm.
   tauto.
   unfold succ in |- *.
     tauto.
Qed.

(* IDEM: *)

Lemma pred_top :forall (m:fmap)(k:dim)(x:dart), 
 inv_hmap m -> pred m k x ->
   top m k x <> A_1 m k x.
Proof.
induction m.
 simpl in |- *.
   unfold pred in |- *.
   simpl in |- *.
    tauto.
simpl in |- *.
  unfold pred in |- *.
  unfold prec_I in |- *.
  simpl in |- *.
  intros.
  elim (eq_dart_dec d x).
 intro.
   rewrite a in H.
   elim H0.
   apply not_exd_A_1_nil.
   tauto.
  tauto.
intro.
  apply IHm.
  tauto.
unfold pred in |- *.
   tauto.
unfold pred in |- *.
  simpl in |- *.
  unfold prec_L in |- *.
  unfold succ in |- *.
  unfold pred in |- *.
  intros.
  generalize H0.
  clear H0.
  elim (eq_dim_dec d k).
 intro.
   rewrite a in |- *.
   elim (eq_dart_dec d1 x).
  intros.
    rewrite a0 in |- *.
    elim (eq_dart_dec d0 (top m k x)).
   intro.
     rewrite a1 in H.
     rewrite a0 in H.
     rewrite a in H.
     generalize (cA_1_eq m k x).
     elim (pred_dec m k x).
    unfold pred in |- *.
       tauto.
   unfold pred in |- *.
     intros.
     rewrite <- a1 in H1.
     rewrite <- a1 in H.
     rewrite <- H1 in H.
    rewrite cA_cA_1 in H.
      tauto.
     tauto.
     tauto.
    tauto.
  intro.
    intro.
    symmetry  in H1.
     tauto.
 elim (eq_dart_dec d0 (top m k x)).
  intros.
    rewrite <- top_A_1 in a0.
   intro.
     rewrite <- H1 in a0.
     rewrite top_top in a0.
    rewrite <- a0 in H1.
      assert (x = A m k d0).
     rewrite H1 in |- *.
       rewrite A_A_1 in |- *.
       tauto.
      tauto.
     unfold pred in |- *.
        tauto.
    rewrite a in H.
      rewrite <- H2 in H.
       absurd (x = nil).
     assert (exd m x).
       eapply pred_exd.
          tauto.
        unfold pred in |- *.
        apply H0.
       apply exd_not_nil with m.
       tauto.
      tauto.
      elim (eq_nat_dec x nil).
      tauto.
     tauto.
      tauto.
     tauto.
    unfold pred in |- *.
     tauto.
   intros.
   apply IHm.
   tauto.
 unfold pred in |- *.
    tauto.
  intros.
  apply IHm.
  tauto.
unfold pred in |- *.
   tauto.
Qed.

(* OK:*)

Lemma cA_top:forall (m:fmap)(k:dim)(z:dart),
  inv_hmap m -> exd m z ->
    cA m k (top m k z) = bottom m k z.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   unfold prec_I in |- *.
   intros.
   elim (eq_dart_dec d z).
  elim (eq_dart_dec d z).
   tauto.
   tauto.
  intro.
    elim (eq_dart_dec d (top m k z)).
   intro.
     rewrite a in H.
     absurd (exd m (top m k z)).
    tauto.
    apply exd_top.
     tauto.
     tauto.
   intro.
     apply IHm.
    tauto.
    tauto.
 simpl in |- *.
   unfold prec_L in |- *.
   intros.
   elim (eq_dim_dec d k).
  elim (eq_dart_dec d0 (top m d z)).
   elim (eq_dart_dec d0 (top m d d1)).
    intros.
      rewrite a in H.
      rewrite IHm in H.
     rewrite nopred_bottom in H.
      tauto.
      tauto.
      tauto.
      tauto.
     tauto.
     tauto.
    elim (eq_dart_dec (cA_1 m k d1) (top m d d1)).
     elim (eq_dart_dec d1 (bottom m d z)).
      intros.
        rewrite <- a2.
        apply cA_bottom.
       tauto.
       tauto.
       tauto.
      intros.
        rewrite a0.
        rewrite a1.
        apply IHm.
       tauto.
       tauto.
     intros.
       elim b.
       rewrite <- a0.
       apply cA_1_top.
      tauto.
      tauto.
      tauto.
   elim (eq_dart_dec d0 (top m d z)).
    tauto.
    intros.
      elim (eq_dart_dec (cA_1 m k d1) (top m d z)).
     intros.
       elim (eq_dart_dec d1 (bottom m d z)).
      intro.
        rewrite <- a.
        apply cA_bottom.
       tauto.
       tauto.
       tauto.
      intro.
        rewrite <- a in a0.
        assert (d1 = cA m d (top m d z)).
       rewrite <- a0.
         rewrite cA_cA_1.
        tauto.
        tauto.
        tauto.
       rewrite IHm in H1.
        tauto.
        tauto.
        tauto.
     intros.
       elim (eq_dart_dec d1 (bottom m d z)).
      intros.
        rewrite <- IHm in a0.
       assert (cA_1 m k d1 = top m d z).
        rewrite a0.
          rewrite <- a.
          rewrite cA_1_cA.
         tauto.
         tauto.
         apply exd_top.
          tauto.
          tauto.
        tauto.
       tauto.
       tauto.
      intro.
        rewrite a.
        apply IHm.
       tauto.
       tauto.
  intro.
    apply IHm.
   tauto.
   tauto.
Qed.

(* IDEM: *)

Lemma cA_1_bottom:forall (m:fmap)(k:dim)(z:dart),
  inv_hmap m ->  exd m z ->
    cA_1 m k (bottom m k z) = top m k z.
induction m.
 simpl in |- *.
    tauto.
simpl in |- *.
  unfold prec_I in |- *.
  intros.
  elim (eq_dart_dec d z).
 elim (eq_dart_dec d z).
   tauto.
  tauto.
intro.
  elim (eq_dart_dec d (bottom m k z)).
 intro.
   rewrite a in H.
    absurd (exd m (bottom m k z)).
   tauto.
 apply exd_bottom.
   tauto.
  tauto.
intro.
  apply IHm.
  tauto.
 tauto.
simpl in |- *.
  unfold prec_L in |- *.
  intros.
  elim (eq_dim_dec d k).
 elim (eq_dart_dec d1 (bottom m d z)).
  elim (eq_dart_dec d1 (bottom m d d0)).
   intros.
     decompose [and] H.
     clear H.
     generalize H7.
     rewrite cA_eq in |- *.
    elim (succ_dec m d d0).
      tauto.
    symmetry  in a.
       tauto.
    tauto.
  elim (eq_dart_dec (cA m k d0) (bottom m d d0)).
   elim (eq_dart_dec d0 (top m d z)).
    intros.
      rewrite <- a2 in |- *.
      apply cA_1_top.
      tauto.
     tauto.
     tauto.
   intros.
     rewrite a0 in |- *.
     rewrite a1 in |- *.
     apply IHm.
     tauto.
    tauto.
  intros.
    elim b.
    rewrite <- a0 in |- *.
    apply cA_bottom.
    tauto.
   tauto.
   tauto.
 elim (eq_dart_dec d1 (bottom m d z)).
   tauto.
 intros.
   elim (eq_dart_dec (cA m k d0) (bottom m d z)).
  intros.
    elim (eq_dart_dec d0 (top m d z)).
   intro.
     rewrite <- a in |- *.
     apply cA_1_top.
     tauto.
    tauto.
    tauto.
  intro.
    rewrite <- a in a0.
    assert (d0 = cA_1 m d (bottom m d z)).
   rewrite <- a0 in |- *.
     rewrite cA_1_cA in |- *.
     tauto.
    tauto.
    tauto.
  rewrite IHm in H1.
    tauto.
   tauto.
   tauto.
 intros.
   elim (eq_dart_dec d0 (top m d z)).
  intros.
    rewrite <- IHm in a0.
   assert (cA m k d0 = bottom m d z).
    rewrite a0 in |- *.
      rewrite <- a in |- *.
      rewrite cA_cA_1 in |- *.
      tauto.
     tauto.
    apply exd_bottom.
      tauto.
     tauto.
    tauto.
   tauto.
   tauto.
 intro.
   rewrite a in |- *.
   apply IHm.
   tauto.
  tauto.
intro.
  apply IHm.
  tauto.
 tauto.
Qed.

Lemma top_top_bottom:forall(m:fmap)(k:dim)(x y:dart),
 inv_hmap m -> exd m x -> exd m y -> 
   ~pred m k y -> top m k x = top m k y ->
      bottom m k x = y. 
Proof.
intros.
assert (bottom m k (top m k x) = bottom m k (top m k y)).
 rewrite H3 in |- *.
    tauto.
rewrite bottom_top_bis in H4.
 rewrite bottom_top_bis in H4.
  rewrite (nopred_bottom m k y) in H4.
   auto.
  auto.
  auto.
  auto.
 auto.
 auto.
auto.
auto.
Qed.

(* IDEM: *)

Lemma bottom_bottom_top:
 forall(m:fmap)(k:dim)(x y:dart),
   inv_hmap m -> exd m x -> exd m y -> 
     ~succ m k y -> bottom m k x = bottom m k y ->
       top m k x = y. 
Proof.
intros.
assert (top m k (bottom m k x) = top m k (bottom m k y)).
 rewrite H3 in |- *.
    tauto.
rewrite top_bottom_bis in H4.
 rewrite top_bottom_bis in H4.
  rewrite (nosucc_top m k y) in H4.
   auto.
  auto.
  auto.
  auto.
 auto.
 auto.
auto.
auto.
Qed.

Lemma top_top_bottom_bottom:
 forall(m:fmap)(k:dim)(x y:dart),
   inv_hmap m -> exd m x -> exd m y -> 
     top m k x = top m k y ->
       bottom m k x = bottom m k y. 
Proof.
intros.
assert (exd m (bottom m k y)).
 apply exd_bottom.
   tauto.
  tauto.
assert (~ pred m k (bottom m k y)).
 apply not_pred_bottom.
    tauto.
assert (top m k x = top m k (bottom m k y)).
 rewrite top_bottom_bis in |- *.
   tauto.
  tauto.
  tauto.
apply (top_top_bottom m k x (bottom m k y) H H0 H3 H4 H5).
Qed.

Lemma bottom_bottom_top_top:
 forall(m:fmap)(k:dim)(x y:dart),
  inv_hmap m -> exd m x -> exd m y -> 
    bottom m k x = bottom m k y -> 
      top m k x = top m k y. 
Proof.
intros.
assert (exd m (top m k y)).
 apply exd_top.
   tauto.
  tauto.
assert (~ succ m k (top m k y)).
 apply not_succ_top.
    tauto.
assert (bottom m k x = bottom m k (top m k y)).
 rewrite bottom_top_bis in |- *.
   tauto.
  tauto.
  tauto.
apply (bottom_bottom_top m k x (top m k y) H H0 H3 H4 H5).
Qed.

Lemma bottom_top_bottom:
 forall(m:fmap)(k:dim)(x:dart),
  inv_hmap m -> exd m x ->  
    bottom m k (top m k x) = bottom m k x. 
Proof.
intros.
generalize (cA_top m k x H H0).
rewrite cA_eq in |- *.
 elim (succ_dec m k (top m k x)).
  intro.
     absurd (succ m k (top m k x)).
   apply not_succ_top.
      tauto.
   tauto.
  tauto.
 tauto.
Qed.

Lemma top_bottom_top:
 forall(m:fmap)(k:dim)(x:dart),
  inv_hmap m -> exd m x ->  
    top m k (bottom m k x) = top m k x. 
Proof.
intros.
generalize (cA_1_bottom m k x H H0).
rewrite cA_1_eq in |- *.
 elim (pred_dec m k (bottom m k x)).
  intros.
     absurd (pred m k (bottom m k x)).
   apply not_pred_bottom.
      tauto.
   tauto.
  tauto.
 tauto.
Qed.

(*=====================================================
                B, B_1 ON cA, cA_1
=====================================================*)

(* OK: VERY LONG *)

Lemma cA_cA_1_B : forall (m:fmap)(k:dim)(x z:dart),
 inv_hmap m -> succ m k x ->
    cA (B m k x) k z =
     (if eq_dart_dec x z then bottom m k x
      else if eq_dart_dec (top m k x) z then A m k x
           else cA m k z) 
/\  cA_1 (B m k x) k z =
     (if eq_dart_dec (A m k x) z then top m k x
      else if eq_dart_dec (bottom m k x) z then x
           else cA_1 m k z).
Proof.
induction m.
 unfold succ in |- *.
   simpl in |- *.
   tauto.
 simpl in |- *.
   unfold prec_I in |- *.
   unfold succ in |- *.
   simpl in |- *.
   intros.
   elim (eq_dart_dec d x).
  intro.
    rewrite a in H.
    absurd (exd m x).
   tauto.
   apply succ_exd with k.
    tauto.
    unfold succ in |- *.
      tauto.
  intro.
    elim (eq_dart_dec d z).
   intro.
     elim (eq_dart_dec x z).
    intro.
      rewrite a0 in b.
      tauto.
    intro.
      split.
     elim (eq_dart_dec (top m k x) z).
      intro.
        rewrite a in H.
        rewrite <- a0 in H.
        absurd (exd m (top m k x)).
       tauto.
       apply exd_top.
        tauto.
        apply succ_exd with k.
         tauto.
         unfold succ in |- *.
           tauto.
      tauto.
     elim (eq_dart_dec (A m k x) z).
      intro.
        rewrite <- a in a0.
        rewrite <- a0 in H.
        absurd (exd m (A m k x)).
       tauto.
       apply succ_exd_A.
        tauto.
        unfold succ in |- *.
          tauto.
      intro.
        elim (eq_dart_dec (bottom m k x) z).
       intro.
         rewrite <- a in a0.
         rewrite <- a0 in H.
         absurd (exd m (bottom m k x)).
        tauto.
        apply exd_bottom.
         tauto.
         apply succ_exd with k.
          tauto.
          unfold succ in |- *.
            tauto.
       tauto.
   intro.
     apply IHm.
    tauto.
    unfold succ in |- *.
      tauto.
 unfold succ in |- *.
   simpl in |- *.
   unfold prec_L in |- *.
   intros.
   decompose [and] H.
   clear H.
   generalize H0.
   clear H0.
   rename d into i.
   elim (eq_dim_dec i k).
  intro.
    rewrite <- a.
    elim (eq_dart_dec d0 x).
   intro.
     rewrite <- a0.
     intro.
     elim (eq_dart_dec d1 (bottom m i d0)).
    intro.
      rewrite a1 in H7.
      generalize H7.
      clear H7.
      rewrite cA_eq.
     elim (succ_dec m i d0).
      tauto.
      tauto.
     tauto.
    intro.
      elim (eq_dart_dec d0 (top m i d0)).
     intro.
       split.
      elim (eq_dart_dec d0 z).
       intro.
         rewrite <- a2.
         rewrite cA_eq.
        elim (succ_dec m i d0).
         tauto.
         tauto.
        tauto.
       intro.
         elim (eq_dart_dec (top m i d1) z).
        intro.
          assert (~ succ m i z).
         rewrite <- a2.
           apply not_succ_top.
           tauto.
         rewrite cA_eq.
          elim (succ_dec m i z).
           tauto.
           intro.
             rewrite <- a2.
             apply bottom_top.
            tauto.
            tauto.
            tauto.
          tauto.
        intro.
          elim (eq_dart_dec (cA_1 m i d1) z).
         rewrite cA_1_eq.
          elim (pred_dec m i d1).
           tauto.
           tauto.
          tauto.
         tauto.
      elim (eq_dart_dec d1 z).
       intro.
         rewrite <- a2.
         rewrite cA_1_eq.
        elim (pred_dec m i d1).
         tauto.
         tauto.
        tauto.
       intro.
         elim (eq_dart_dec (bottom m i d0) z).
        intro.
          assert (~ pred m i z).
         rewrite <- a2.
           apply not_pred_bottom.
           tauto.
         rewrite cA_1_eq.
          elim (pred_dec m i z).
           tauto.
           intro.
             rewrite <- a2.
             apply top_bottom.
            tauto.
            tauto.
            tauto.
          tauto.
        intro.
          elim (eq_dart_dec (cA m i d0) z).
         rewrite cA_eq.
          elim (succ_dec m i d0).
           tauto.
           tauto.
          tauto.
         tauto.
     intro.
       elim b0.
       rewrite nosucc_top.
      tauto.
      tauto.
      tauto.
      tauto.
   intros.
     fold (succ m i x) in H0.
     elim (eq_dart_dec d0 (top m i x)).
    intro.
      elim (eq_dart_dec d1 (bottom m i x)).
     intro.
       rewrite a1 in H7.
       rewrite a0 in H7.
       elim H7.
       apply cA_top.
      tauto.
      apply succ_exd with i.
       tauto.
       unfold succ in |- *.
         unfold succ in H0.
         tauto.
     intro.
       split.
      simpl in |- *.
        elim (eq_dim_dec i i).
       intro.
         clear a1.
         elim (eq_dart_dec d0 z).
        intro.
          elim (eq_dart_dec x z).
         intro.
           rewrite <- a2 in a1.
           tauto.
         elim (eq_dart_dec (top m i d1) z).
          intros.
            rewrite <- a2 in a1.
            rewrite a1 in a0.
            elim b0.
            symmetry  in |- *.
            apply top_top_bottom.
           tauto.
           apply succ_exd with i.
            tauto.
            tauto.
           tauto.
           tauto.
           symmetry  in |- *.
             tauto.
          tauto.
        intro.
          elim (eq_dart_dec (cA_1 (B m i x) i d1) z).
         intro.
           generalize (IHm i x d0 H1 H0).
           intros.
           elim H.
           clear H.
           intros.
           generalize (IHm i x d1 H1 H0).
           intros.
           elim H8.
           clear H8.
           intros.
           generalize H.
           clear H.
           elim (eq_dart_dec x z).
          intro.
            elim (eq_dart_dec x d0).
           tauto.
           intro.
             elim (eq_dart_dec (top m i x) d0).
            intros.
              rewrite <- a2 in a1.
              generalize a1.
              clear a1.
              rewrite H9.
              clear H9.
              elim (eq_dart_dec (A m i x) d1).
             intros.
               rewrite a4 in a0.
               tauto.
             intro.
               elim (eq_dart_dec (bottom m i x) d1).
              intros.
                symmetry  in a1.
                tauto.
              intros.
                rewrite cA_1_eq in a1.
               generalize a1.
                 clear a1.
                 elim (pred_dec m i d1).
                tauto.
                intros.
                  rewrite <- a1 in b4.
                  rewrite bottom_top in b4.
                 tauto.
                 tauto.
                 tauto.
                 tauto.
               tauto.
            intros.
              rewrite H.
              rewrite cA_eq.
             elim (succ_dec m i d0).
              tauto.
              intro.
                rewrite a0.
                apply bottom_top_bis.
               tauto.
               apply succ_exd with i.
                tauto.
                tauto.
             tauto.
          intro.
            elim (eq_dart_dec x d0).
           intro.
             symmetry  in a2.
             tauto.
           intro.
             elim (eq_dart_dec (top m i x) d0).
            intros.
              elim (eq_dart_dec (top m i d1) z).
             intros.
               tauto.
             intro.
               elim (eq_dart_dec (cA_1 m i d1) z).
              intro.
                rewrite cA_1_eq in a3.
               generalize a3.
                 elim (pred_dec m i d1).
                tauto.
                tauto.
               tauto.
              intro.
                rewrite H.
                generalize H9.
                clear H9.
                elim (eq_dart_dec (A m i x) d1).
               intros.
                 rewrite <- a3 in H5.
                 unfold pred in H5.
                 rewrite A_1_A in H5.
                absurd (x <> nil).
                 tauto.
                 apply exd_not_nil with m.
                  tauto.
                  apply succ_exd with i.
                   tauto.
                   tauto.
                tauto.
                tauto.
               intro.
                 elim (eq_dart_dec (bottom m i x) d1).
                intros.
                  symmetry  in a3.
                  tauto.
                intros.
                  rewrite a1 in H9.
                  symmetry  in H9.
                  tauto.
            symmetry  in a0.
              tauto.
         intro.
           generalize (IHm i x z H1 H0).
           intros.
           elim H.
           clear H.
           intros.
           generalize (IHm i x d1 H1 H0).
           intros.
           elim H8.
           clear H8.
           intros.
           generalize H.
           clear H.
           elim (eq_dart_dec x z).
          tauto.
          elim (eq_dart_dec (top m i x) z).
           intros.
             rewrite a1 in a0.
             tauto.
           intros.
             elim (eq_dart_dec (top m i d1) z).
            intros.
              generalize H9.
              clear H9.
              elim (eq_dart_dec (A m i x) d1).
             intro.
               rewrite <- a2 in a1.
               rewrite top_A in a1.
              tauto.
              tauto.
              tauto.
             elim (eq_dart_dec (bottom m i x) d1).
              intros.
                symmetry  in a2.
                tauto.
              intros.
                rewrite H9 in b2.
                generalize b2.
                rewrite cA_1_eq.
               elim (pred_dec m i d1).
                tauto.
                tauto.
               tauto.
            elim (eq_dart_dec (cA_1 m i d1) z).
             intros.
               rewrite cA_1_eq in a1.
              generalize a1.
                elim (pred_dec m i d1).
               tauto.
               tauto.
              tauto.
             intros.
               tauto.
       tauto.
      simpl in |- *.
        elim (eq_dim_dec i i).
       intro.
         elim (eq_dart_dec d1 z).
        intro.
          rewrite <- a2.
          elim (eq_dart_dec (A m i x) d1).
         intros.
           assert (d0 = top m i d1).
          rewrite <- a3.
            rewrite top_A.
           tauto.
           tauto.
           tauto.
          tauto.
         elim (eq_dart_dec (bottom m i x) d1).
          intros.
            symmetry  in a3.
            tauto.
          tauto.
        intro.
          elim (eq_dart_dec (cA (B m i x) i d0) z).
         intro.
           generalize (IHm i x d0 H1 H0).
           intro.
           elim H.
           clear H.
           intros.
           generalize (IHm i x d1 H1 H0).
           intro.
           elim H8.
           clear H8.
           intros.
           generalize H9.
           clear H9.
           generalize H.
           clear H.
           elim (eq_dart_dec x d0).
          intro.
            symmetry  in a3.
            tauto.
          elim (eq_dart_dec (top m i x) d0).
           intros.
             generalize H9.
             clear H9.
             clear b2 a3.
             elim (eq_dart_dec (A m i x) d1).
            intros.
              rewrite <- a3 in H5.
              unfold pred in H5.
              rewrite A_1_A in H5.
             absurd (x <> nil).
              tauto.
              apply exd_not_nil with m.
               tauto.
               apply succ_exd with i.
                tauto.
                tauto.
             tauto.
             tauto.
            intro.
              elim (eq_dart_dec (bottom m i x) d1).
             intro.
               symmetry  in |- *.
               symmetry  in a3.
               tauto.
             intros.
               elim (eq_dart_dec (A m i x) z).
              intro.
                rewrite H9.
                rewrite cA_1_eq.
               elim (pred_dec m i d1).
                tauto.
                tauto.
               tauto.
              intro.
                rewrite H in a2.
                tauto.
           intros.
             generalize H9.
             clear H9.
             elim (eq_dart_dec (A m i x) d1).
            intros.
              rewrite <- a3 in H5.
              unfold pred in H5.
              rewrite A_1_A in H5.
             absurd (x <> nil).
              tauto.
              apply exd_not_nil with m.
               tauto.
               apply succ_exd with i.
                tauto.
                tauto.
             tauto.
             tauto.
            intro.
              elim (eq_dart_dec (bottom m i x) d1).
             intro.
               symmetry  in a3.
               tauto.
             intros.
               elim (eq_dart_dec (A m i x) z).
              intro.
                rewrite H9.
                rewrite cA_1_eq.
               elim (pred_dec m i d1).
                tauto.
                tauto.
               tauto.
              intro.
                symmetry  in a0.
                tauto.
         intro.
           generalize (IHm i x d0 H1 H0).
           intro.
           elim H.
           clear H.
           intros.
           generalize (IHm i x z H1 H0).
           intro.
           elim H8.
           clear H8.
           intros.
           generalize H9.
           clear H9.
           elim (eq_dart_dec (A m i x) z).
          intros.
            rewrite <- a0 in H9.
            rewrite H in b2.
            generalize b2.
            clear b2.
            elim (eq_dart_dec x d0).
           intro.
             symmetry  in a3.
             tauto.
           elim (eq_dart_dec (top m i x) d0).
            intros.
              tauto.
            intro.
              symmetry  in a0.
              tauto.
          intro.
            elim (eq_dart_dec (bottom m i x) z).
           tauto.
           intros.
             elim (eq_dart_dec (cA m i d0) z).
            intro.
              generalize a2.
              rewrite cA_eq.
             elim (succ_dec m i d0).
              tauto.
              intros.
                rewrite a0 in a3.
                rewrite bottom_top_bis in a3.
               tauto.
               tauto.
               apply succ_exd with i.
                tauto.
                tauto.
             tauto.
            tauto.
       tauto.
    intro.
      simpl in |- *.
      elim (eq_dim_dec i i).
     intro.
       split.
      elim (eq_dart_dec d0 z).
       intro.
         rewrite <- a1.
         elim (eq_dart_dec x d0).
        intro.
          symmetry  in a2.
          tauto.
        intro.
          elim (eq_dart_dec (top m i x) d0).
         intro.
           symmetry  in a2.
           tauto.
         tauto.
       intro.
         elim (eq_dart_dec x z).
        intro.
          rewrite <- a1.
          generalize (IHm i x d1 H1 H0).
          intro.
          elim H.
          clear H.
          intros.
          elim (eq_dart_dec (cA_1 (B m i x) i d1) x).
         intros.
           generalize (IHm i x d0 H1 H0).
           intro.
           elim H8.
           clear H8.
           intros.
           rewrite H8.
           elim (eq_dart_dec x d0).
          intro.
            symmetry  in a3.
            tauto.
          intro.
            elim (eq_dart_dec (top m i x) d0).
           intro.
             symmetry  in a3.
             tauto.
           intro.
             clear H8.
             elim (eq_dart_dec d1 (bottom m i x)).
            intro.
              rewrite cA_eq.
             elim (succ_dec m i d0).
              tauto.
              tauto.
             tauto.
            intros.
              rewrite H6 in a2.
              generalize a2.
              elim (eq_dart_dec (A m i x) d1).
             intro.
               rewrite <- a3 in H5.
               unfold pred in H5.
               rewrite A_1_A in H5.
              absurd (x <> nil).
               tauto.
               apply exd_not_nil with m.
                tauto.
                apply succ_exd with i.
                 tauto.
                 tauto.
              tauto.
              tauto.
             intro.
               elim (eq_dart_dec (bottom m i x) d1).
              intro.
                symmetry  in a3.
                tauto.
              intros.
                rewrite cA_1_eq in a3.
               generalize a3.
                 elim (pred_dec m i d1).
                tauto.
                intros.
                  rewrite <- a4 in H0.
                  absurd (succ m i (top m i d1)).
                 apply not_succ_top.
                   tauto.
                 tauto.
               tauto.
         rewrite H6.
           clear H6.
           elim (eq_dart_dec (A m i x) d1).
          intro.
            rewrite <- a2 in H5.
            unfold pred in H5.
            rewrite A_1_A in H5.
           absurd (x <> nil).
            tauto.
            apply exd_not_nil with m.
             tauto.
             apply succ_exd with i.
              tauto.
              tauto.
           tauto.
           tauto.
          intro.
            elim (eq_dart_dec (bottom m i x) d1).
           intros.
             tauto.
           elim (eq_dart_dec d1 (bottom m i x)).
            intros.
              symmetry  in a2.
              tauto.
            intros.
              generalize (IHm i x x H1 H0).
              intro.
              elim H6.
              clear H6.
              intros.
              rewrite H6.
              clear H6.
              elim (eq_dart_dec x x).
             tauto.
             tauto.
        intro.
          generalize (IHm i x z H1 H0).
          intro.
          elim H.
          clear H.
          intros.
          generalize (IHm i x d1 H1 H0).
          intro.
          elim H8.
          clear H8.
          intros.
          generalize H9.
          elim (eq_dart_dec (A m i x) d1).
         intro.
           rewrite <- a1 in H5.
           unfold pred in H5.
           rewrite A_1_A in H5.
          absurd (x <> nil).
           tauto.
           apply exd_not_nil with m.
            tauto.
            apply succ_exd with i.
             tauto.
             tauto.
          tauto.
          tauto.
         elim (eq_dart_dec (bottom m i x) d1).
          intros.
            rewrite H10.
            elim (eq_dart_dec x z).
           tauto.
           intro.
             rewrite H.
             clear H.
             elim (eq_dart_dec x z).
            tauto.
            elim (eq_dart_dec (top m i x) z).
             tauto.
             elim (eq_dart_dec (cA_1 m i d1) z).
              intros.
                rewrite cA_1_eq in a2.
               generalize a2; clear a2.
                 elim (pred_dec m i d1).
                tauto.
                intros.
                  rewrite cA_eq.
                 elim (succ_dec m i z).
                  intro.
                    rewrite <- a2 in a3.
                    absurd (succ m i (top m i d1)).
                   apply not_succ_top.
                     tauto.
                   tauto.
                  rewrite cA_eq.
                   elim (succ_dec m i d0).
                    tauto.
                    intros.
                      rewrite <- a1 in a2.
                      rewrite top_bottom_bis in a2.
                     tauto.
                     tauto.
                     apply succ_exd with i.
                      tauto.
                      tauto.
                   tauto.
                 tauto.
               tauto.
              tauto.
          intro.
            intros.
            elim (eq_dart_dec (cA_1 (B m i x) i d1) z).
           intros.
             generalize (IHm i x d0 H1 H0).
             intro.
             elim H11.
             clear H11.
             intros.
             rewrite H11.
             clear H11.
             elim (eq_dart_dec x d0).
            intro.
              symmetry  in a2.
              tauto.
            elim (eq_dart_dec (top m i x) d0).
             intro.
               symmetry  in a2.
               tauto.
             intros.
               elim (eq_dart_dec (top m i x) z).
              intro.
                rewrite H10 in a1.
                generalize a1.
                rewrite cA_1_eq.
               elim (pred_dec m i d1).
                tauto.
                intros.
                  rewrite <- a3 in a2.
                  assert (bottom m i x = d1).
                 apply top_top_bottom.
                  tauto.
                  apply succ_exd with i.
                   tauto.
                   tauto.
                  tauto.
                  tauto.
                  tauto.
                 tauto.
               tauto.
              elim (eq_dart_dec (cA_1 m i d1) z).
               tauto.
               intros.
                 rewrite H10 in a1.
                 tauto.
           intro.
             rewrite H.
             clear H.
             elim (eq_dart_dec x z).
            tauto.
            elim (eq_dart_dec (top m i x) z).
             intros.
               tauto.
             elim (eq_dart_dec (cA_1 m i d1) z).
              rewrite H10 in b5.
                tauto.
              tauto.
      generalize (IHm i x d0 H1 H0).
        intro.
        elim H.
        clear H.
        intros.
        generalize H.
        clear H.
        elim (eq_dart_dec x d0).
       intro.
         symmetry  in a1.
         tauto.
       elim (eq_dart_dec (top m i x) d0).
        intro.
          symmetry  in a1.
          tauto.
        intros.
          elim (eq_dart_dec d1 z).
         intro.
           rewrite <- a1.
           elim (eq_dart_dec (A m i x) d1).
          intro.
            rewrite <- a2 in H5.
            unfold pred in H5.
            rewrite A_1_A in H5.
           absurd (x <> nil).
            tauto.
            apply exd_not_nil with m.
             tauto.
             apply succ_exd with i.
              tauto.
              tauto.
           tauto.
           tauto.
          elim (eq_dart_dec d1 (bottom m i x)).
           intros.
             elim (eq_dart_dec (bottom m i d0) d1).
            intros.
              rewrite <- a3 in a2.
              symmetry  in a2.
              assert (top m i x = d0).
             apply bottom_bottom_top.
              tauto.
              apply succ_exd with i.
               tauto.
               tauto.
              tauto.
              tauto.
              tauto.
             symmetry  in H8.
               tauto.
            tauto.
           elim (eq_dart_dec (bottom m i x) d1).
            intro.
              symmetry  in a2.
              tauto.
            tauto.
         intro.
           elim (eq_dart_dec (cA (B m i x) i d0) z).
          intro.
            generalize (IHm i x d1 H1 H0).
            intro.
            elim H8.
            clear H8.
            intros.
            rewrite H9.
            clear H9.
            elim (eq_dart_dec (A m i x) d1).
           intro.
             rewrite <- a2 in H5.
             unfold pred in H5.
             rewrite A_1_A in H5.
            absurd (x <> nil).
             tauto.
             apply exd_not_nil with m.
              tauto.
              apply succ_exd with i.
               tauto.
               tauto.
            tauto.
            tauto.
           elim (eq_dart_dec (bottom m i x) d1).
            intros.
              assert (cA m i d0 = bottom m i d0).
             rewrite cA_eq.
              elim (succ_dec m i d0).
               tauto.
               tauto.
              tauto.
             elim (eq_dart_dec (A m i x) z).
              intro.
                assert (pred m i z).
               unfold pred in |- *.
                 rewrite <- a3.
                 rewrite A_1_A.
                apply exd_not_nil with m.
                 tauto.
                 apply succ_exd with i.
                  tauto.
                  tauto.
                tauto.
                tauto.
               rewrite <- a1 in H10.
                 rewrite H in H10.
                 rewrite H9 in H10.
                 absurd (pred m i (bottom m i d0)).
                apply not_pred_bottom.
                  tauto.
                tauto.
              intro.
                elim (eq_dart_dec d1 (bottom m i x)).
               intro.
                 elim (eq_dart_dec (bottom m i d0) z).
                tauto.
                elim (eq_dart_dec (cA m i d0) z).
                 intros.
                   rewrite H9 in a4.
                   tauto.
                 intros.
                   rewrite H in a1.
                   tauto.
               intro.
                 elim (eq_dart_dec (bottom m i x) z).
                tauto.
                elim (eq_dart_dec (cA m i d0) z).
                 intros.
                   rewrite cA_1_eq.
                  elim (pred_dec m i d1).
                   tauto.
                   intro.
                     symmetry  in a2.
                     tauto.
                  tauto.
                 rewrite H in a1.
                   tauto.
            intros.
              elim (eq_dart_dec (A m i x) z).
             intro.
               rewrite cA_1_eq.
              rewrite H in a1.
                generalize a1.
                rewrite cA_eq.
               elim (succ_dec m i d0).
                tauto.
                intros.
                  assert (pred m i z).
                 rewrite <- a2.
                   unfold pred in |- *.
                   rewrite A_1_A.
                  apply exd_not_nil with m.
                   tauto.
                   apply succ_exd with i.
                    tauto.
                    tauto.
                  tauto.
                  tauto.
                 rewrite <- a3 in H9.
                   absurd (pred m i (bottom m i d0)).
                  apply not_pred_bottom.
                    tauto.
                  tauto.
               tauto.
              tauto.
             intro.
               elim (eq_dart_dec d1 (bottom m i x)).
              intro.
                symmetry  in a2.
                tauto.
              elim (eq_dart_dec (bottom m i x) z).
               intros.
                 rewrite H in a1.
                 generalize a1.
                 rewrite cA_eq.
                elim (succ_dec m i d0).
                 intros.
                   tauto.
                 intros.
                   rewrite <- a3 in a2.
                   elim b1.
                   apply bottom_bottom_top.
                  tauto.
                  apply succ_exd with i.
                   tauto.
                   tauto.
                  tauto.
                  tauto.
                  tauto.
                tauto.
               elim (eq_dart_dec (cA m i d0) z).
                tauto.
                intros.
                  rewrite H in a1.
                  tauto.
          intro.
            generalize (IHm i x z H1 H0).
            intro.
            elim H8.
            clear H8.
            intros.
            rewrite H9.
            clear H9.
            elim (eq_dart_dec (A m i x) z).
           tauto.
           elim (eq_dart_dec (bottom m i x) z).
            intros.
              elim (eq_dart_dec d1 (bottom m i x)).
             intro.
               rewrite a1 in a2.
               tauto.
             elim (eq_dart_dec (bottom m i x) z).
              tauto.
              tauto.
            elim (eq_dart_dec d1 (bottom m i x)).
             intros.
               elim (eq_dart_dec (bottom m i d0) z).
              intros.
                rewrite H in b4.
                generalize b4.
                rewrite cA_eq.
               elim (succ_dec m i d0).
                tauto.
                tauto.
               tauto.
              elim (eq_dart_dec (cA m i d0) z).
               rewrite H in b4.
                 tauto.
               tauto.
             intros.
               elim (eq_dart_dec (bottom m i x) z).
              intro.
                tauto.
              elim (eq_dart_dec (cA m i d0) z).
               intros.
                 rewrite H in b4.
                 tauto.
               tauto.
     tauto.
  simpl in |- *.
    elim (eq_dim_dec i k).
   tauto.
   intros.
     fold succ in H0.
     fold (succ m k x) in H0.
     apply IHm.
    tauto.
    tauto.
Qed.
(* cA_cA_1_B is defined *)

(* COROLLARIES : *)

Lemma cA_B : forall (m:fmap)(k:dim)(x z:dart),
 inv_hmap m -> succ m k x ->
    cA (B m k x) k z =
     (if eq_dart_dec x z then bottom m k x
      else if eq_dart_dec (top m k x) z then A m k x
           else cA m k z).
Proof.
intros.
generalize (cA_cA_1_B m k x z H H0).
tauto.
Qed.

Lemma cA_1_B : forall (m:fmap)(k:dim)(x z:dart),
 inv_hmap m -> succ m k x ->
    cA_1 (B m k x) k z =
     (if eq_dart_dec (A m k x) z then top m k x
      else if eq_dart_dec (bottom m k x) z then x
           else cA_1 m k z).
Proof.
intros.
generalize (cA_cA_1_B m k x z H H0).
tauto.
Qed.

Lemma cA_cA_1_B_bis : forall (m:fmap)(k:dim)(x z:dart),
 inv_hmap m -> ~succ m k x ->
    cA (B m k x) k z = cA m k z
  /\ cA_1 (B m k x) k z = cA_1 m k z.
Proof.
induction m.
 simpl in |- *.
   tauto.
 unfold prec_L in |- *.
   unfold succ in |- *.
   simpl in |- *.
   unfold prec_I in |- *.
   intros.
   elim (eq_dart_dec d z).
  tauto.
  intro.
    apply IHm.
   tauto.
   unfold succ in |- *.
     tauto.
 simpl in |- *.
   unfold succ in |- *.
   unfold prec_L in |- *.
   simpl in |- *.
   intros.
   decompose [and] H.
   clear H.
   unfold succ in IHm.
   generalize H0.
   clear H0.
   elim (eq_dim_dec d k).
  elim (eq_dart_dec d0 x).
   intros.
     elim H0.
     apply exd_not_nil with m.
    tauto.
    tauto.
   intros.
     simpl in |- *.
     elim (eq_dim_dec d k).
    split.
     elim (eq_dart_dec d0 z).
      tauto.
      elim (eq_dart_dec (cA_1 (B m k x) k d1) z).
       intros.
         elim (eq_dart_dec (cA_1 m k d1) z).
        intro.
          generalize (IHm k x d0 H1 H0).
          tauto.
        intro.
          decompose [and] (IHm k x d1 H1 H0).
          rewrite a1 in H6.
          symmetry  in H6.
          tauto.
       intros.
         elim (eq_dart_dec (cA_1 m k d1) z).
        intro.
          decompose [and] (IHm k x d1 H1 H0).
          rewrite a1 in H6.
          tauto.
        intro.
          decompose [and] (IHm k x z H1 H0).
          tauto.
     elim (eq_dart_dec d1 z).
      tauto.
      elim (eq_dart_dec (cA (B m k x) k d0) z).
       intros.
         elim (eq_dart_dec (cA m k d0) z).
        intro.
          decompose [and] (IHm k x d1 H1 H0).
          tauto.
        intro.
          decompose [and] (IHm k x d0 H1 H0).
          rewrite H in a1.
          tauto.
       elim (eq_dart_dec (cA m k d0) z).
        intros.
          decompose [and] (IHm k x d0 H1 H0).
          rewrite H in b0.
          tauto.
        intros.
          decompose [and] (IHm k x z H1 H0).
          tauto.
    tauto.
  intros.
    simpl in |- *.
    elim (eq_dim_dec d k).
   tauto.
   intro.
     apply IHm.
    tauto.
    tauto.
Qed.

(* COROLLARIES: *)

Lemma cA_B_bis : forall (m:fmap)(k:dim)(x z:dart),
 inv_hmap m -> ~succ m k x ->
    cA (B m k x) k z = cA m k z.
Proof.
intros.
generalize (cA_cA_1_B_bis m k x z H H0).
tauto.
Qed.

Lemma cA_1_B_bis : forall (m:fmap)(k:dim)(x z:dart),
 inv_hmap m -> ~succ m k x ->
    cA_1 (B m k x) k z = cA_1 m k z.
Proof.
intros.
generalize (cA_cA_1_B_bis m k x z H H0).
tauto.
Qed.

Lemma cA_cA_1_B_ter : forall (m:fmap)(k j:dim)(x z:dart),
 inv_hmap m -> k <> j -> 
    cA (B m k x) j z = cA m j z
  /\ cA_1 (B m k x) j z = cA_1 m j z.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   unfold prec_I in |- *.
   intros.
   elim (eq_dart_dec d z).
  tauto.
  intros.
    apply IHm.
   tauto.
   tauto.
 simpl in |- *.
   unfold prec_L in |- *.
   intros.
   decompose [and] H.
   clear H.
   elim (eq_dim_dec d k).
  elim (eq_dim_dec d j).
   intros.
     rewrite <- a0 in H0.
     tauto.
   elim (eq_dart_dec d0 x).
    tauto.
    simpl in |- *.
      elim (eq_dim_dec d j).
     tauto.
     intros.
       apply IHm.
      tauto.
      tauto.
  simpl in |- *.
    elim (eq_dim_dec d j).
   intros.
     assert (k <> j).
    rewrite <- a.
      intro.
      symmetry  in H.
      tauto.
    decompose [and] (IHm k j x d0 H1 H).
      split.
     elim (eq_dart_dec d0 z).
      tauto.
      elim (eq_dart_dec d1 z).
       elim (eq_dart_dec (cA_1 (B m k x) j d1) z).
        elim (eq_dart_dec (cA_1 m j d1) z).
         intros.
           decompose [and] (IHm k j x d0 H1).
           tauto.
         intros.
           decompose [and] (IHm k j x d1 H1 H).
           rewrite H10 in a0.
           tauto.
        elim (eq_dart_dec (cA_1 m j d1) z).
         intros.
           decompose [and] (IHm k j x d1 H1 H).
           rewrite H10 in b0.
           tauto.
         intros.
           decompose [and] (IHm k j x z H1 H).
           tauto.
       elim (eq_dart_dec (cA_1 (B m k x) j d1) z).
        elim (eq_dart_dec (cA_1 m j d1) z).
         tauto.
         intros.
           decompose [and] (IHm k j x d1 H1 H).
           rewrite H10 in a0.
           tauto.
        elim (eq_dart_dec (cA_1 m j d1) z).
         intros.
           decompose [and] (IHm k j x d1 H1 H).
           rewrite H10 in b0.
           tauto.
         intros.
           decompose [and] (IHm k j x z H1 H).
           tauto.
     elim (eq_dart_dec d1 z).
      tauto.
      elim (eq_dart_dec (cA (B m k x) j d0) z).
       elim (eq_dart_dec (cA m j d0) z).
        decompose [and] (IHm k j x d1 H1 H).
          tauto.
        intros.
          rewrite H6 in a0.
          tauto.
       elim (eq_dart_dec (cA m j d0) z).
        decompose [and] (IHm k j x d1 H1 H).
          rewrite H6.
          tauto.
        decompose [and] (IHm k j x z H1 H).
          tauto.
   intros.
     apply IHm.
    tauto.
    tauto.
Qed.

(* COROLLARIES : *)

Lemma cA_B_ter : forall (m:fmap)(k j:dim)(x z:dart),
 inv_hmap m -> k <> j -> 
    cA (B m k x) j z = cA m j z.
Proof.
intros.
generalize (cA_cA_1_B_ter m k j x z).
tauto.
Qed.

Lemma cA_1_B_ter : forall (m:fmap)(k j:dim)(x z:dart),
 inv_hmap m -> k <> j -> 
    cA_1 (B m k x) j z = cA_1 m j z.
Proof.
intros.
generalize (cA_cA_1_B_ter m k j x z).
tauto.
Qed.

(*=====================================================
              B and B_1 PRESERVE inv_hmap:
=====================================================*)

(* OK : *)

Lemma inv_hmap_B : forall (m:fmap)(k:dim)(z:dart),
  inv_hmap m -> inv_hmap (B m k z).
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   split.
  apply IHm.
    tauto.
  unfold prec_I in |- *.
    split.
   unfold prec_I in H.
     tauto.
   unfold prec_I in H.
     generalize (exd_B m k z d).
     tauto.
 simpl in |- *.
   unfold prec_L in |- *.
   intros.
   decompose [and] H.
   clear H.
   elim (eq_dim_dec d k).
  elim (eq_dart_dec d0 z).
   tauto.
   simpl in |- *.
     intros.
     split.
    apply IHm.
      tauto.
    unfold prec_L in |- *.
      split.
     generalize (exd_B m k z d0).
       tauto.
     split.
      generalize (exd_B m k z d1).
        tauto.
      split.
       rewrite <- a.
         unfold succ in |- *.
         rewrite A_B_bis.
        tauto.
        tauto.
       unfold pred in |- *.
         split.
        unfold pred in H4.
          rewrite <- a.
          elim (eq_dart_dec d1 (A m d z)).
         intro.
           rewrite a0.
           rewrite A_1_B.
          tauto.
          tauto.
         intro.
           rewrite A_1_B_bis.
          tauto.
          tauto.
          tauto.
        rewrite a.
          elim (succ_dec m k z).
         intro.
           rewrite cA_B.
          elim (eq_dart_dec z d0).
           intro.
             elim (eq_dart_dec (top m k z) d0).
            intros.
              generalize H6.
              rewrite cA_eq.
             elim (succ_dec m d d0).
              tauto.
              intros.
                rewrite a1.
                rewrite <- a.
                tauto.
             tauto.
            intro.
              rewrite a1 in a0.
              rewrite <- a in a0.
              tauto.
           elim (eq_dart_dec (top m k z) d0).
            intros.
              intro.
              unfold pred in H4.
              rewrite <- H in H4.
              rewrite a in H4.
              rewrite A_1_A in H4.
             absurd (z <> nil).
              tauto.
              apply exd_not_nil with m.
               tauto.
               apply succ_exd with k.
                tauto.
                tauto.
             tauto.
             tauto.
            intros.
              rewrite <- a.
              tauto.
          tauto.
          tauto.
         intro.
           rewrite cA_B_bis.
          rewrite <- a.
            tauto.
          tauto.
          tauto.
  intro.
    simpl in |- *.
    split.
   apply IHm.
     tauto.
   unfold prec_L in |- *.
     simpl in |- *.
     split.
    generalize (exd_B m k z d0).
      tauto.
    split.
     generalize (exd_B m k z d1).
       tauto.
     split.
      unfold succ in |- *.
        rewrite A_B_ter.
       unfold succ in H3.
         tauto.
       intro.
         symmetry  in H.
         tauto.
      split.
       unfold pred in |- *.
         rewrite A_1_B_ter.
        unfold pred in H4.
          tauto.
        intro.
          symmetry  in H.
          tauto.
       rewrite cA_B_ter.
        tauto.
        tauto.
        intro.
          symmetry  in H.
          tauto.
Qed.

(* B_1 is defined from B: *)

Lemma B_1_eq : forall (m:fmap)(k:dim)(x:dart),
  inv_hmap m -> B_1 m k x = B m k (A_1 m k x).
Proof.
induction m.
 simpl in |- *.
    tauto.
simpl in |- *.
  intros.
  decompose [and] H.
  clear H.
  rewrite IHm in |- *.
 auto.
assumption.
simpl in |- *.
  unfold prec_L in |- *.
  unfold pred in |- *.
  unfold succ in |- *.
  intros.
  decompose [and] H.
  clear H.
  elim (eq_dim_dec d k).
 elim (eq_dart_dec d1 x).
  elim (eq_dart_dec d0 d0).
   auto.
   tauto.
 elim (eq_dart_dec d0 (A_1 m k x)).
  intros.
    assert (pred m k x).
   unfold pred in |- *.
     rewrite <- a in |- *.
      eapply exd_not_nil.
      apply H0.
      tauto.
    rewrite a in H3.
    rewrite a0 in H3.
    rewrite A_A_1 in H3.
    absurd (x <> nil).
     tauto.
   assert (exd m x).
    apply pred_exd with k.
      tauto.
     tauto.
    eapply exd_not_nil.
      apply H0.
      tauto.
     tauto.
     tauto.
   intros.
   rewrite IHm in |- *.
   tauto.
  tauto.
  intro.
  rewrite IHm in |- *.
  tauto.
 tauto.
Qed.

(* IDEM: B_1 preserves inv_hmap: *)

Lemma inv_hmap_B_1 : forall (m:fmap)(k:dim)(x:dart),
  inv_hmap m -> inv_hmap (B_1 m k x).
Proof.
intros.
rewrite B_1_eq in |- *.
 apply inv_hmap_B.
    tauto.
 tauto.
Qed.

(* OK: *)

Lemma bottom_B: forall(m:fmap)(k:dim)(z:dart),
  inv_hmap m -> exd m z ->
    bottom (B m k z) k z = bottom m k z.
Proof.
intros.
assert (inv_hmap (B m k z)).
 apply inv_hmap_B.
   tauto.
 generalize (cA_eq (B m k z) k z H1).
   intro.
   elim (succ_dec m k z).
  intro.
    generalize (cA_B m k z z H a).
    elim (eq_dart_dec z z).
   intros.
     generalize H2.
     elim (succ_dec (B m k z) k z).
    unfold succ in |- *.
      rewrite A_B.
     tauto.
     tauto.
    intros.
      rewrite H4 in H3.
      tauto.
   tauto.
  intro.
    rewrite not_succ_B.
   tauto.
   tauto.
   tauto.
Qed.

Lemma no_fixpt_A:forall(m:fmap)(k:dim)(z:dart),
 inv_hmap m -> exd m z -> A m k z <> z.
Proof.
induction m.
 simpl in |- *.
    tauto.
simpl in |- *.
  intros.
  elim H0.
 intro.
   rewrite <- H1 in |- *.
   unfold prec_I in H.
   assert (A m k d = nil).
  apply not_exd_A_nil.
    tauto.
   tauto.
 rewrite H2 in |- *.
   intro.
   symmetry  in H3.
    tauto.
apply IHm.
   tauto.
simpl in |- *.
  unfold prec_L in |- *.
  intros.
  decompose [and] H.
  clear H.
  elim (eq_dim_dec d k).
 intro.
   rewrite <- a in |- *.
   elim (eq_dart_dec d0 z).
  intros.
    intro.
    generalize H7.
    rewrite cA_eq in |- *.
   elim (succ_dec m d d0).
     tauto.
   intros.
     rewrite a0 in H6.
     rewrite <- H in H6.
     apply H6.
     apply nopred_bottom.
     tauto.
    tauto.
    tauto.
   tauto.
 intro.
   apply IHm.
   tauto.
  tauto.
intro.
  apply IHm.
  tauto.
 tauto.
Qed.

Lemma no_fixpt_A_1:forall(m:fmap)(k:dim)(z:dart),
 inv_hmap m -> exd m z -> A_1 m k z <> z.
Proof.
intros.
intro.
elim (pred_dec m k z).
 intro.
   assert (A m k z = z).
  rewrite <- H1 in |- *.
    rewrite A_A_1 in |- *.
   symmetry  in |- *.
      tauto.
   tauto.
   tauto.
 generalize H2.
   apply no_fixpt_A.
   tauto.
  tauto.
unfold pred in |- *.
  rewrite H1 in |- *.
  intro.
  apply b.
  intro.
  rewrite H2 in H0.
  generalize H0.
  apply not_exd_nil.
   tauto.
Qed.

Lemma top_B: forall(m:fmap)(k:dim)(z:dart),
  inv_hmap m -> exd m z ->
    top (B m k z) k z = z.
Proof.
induction m.
 simpl in |- *.
    tauto.
simpl in |- *.
  intros.
  elim (eq_dart_dec d z).
  tauto.
intro.
  apply IHm.
  tauto.
 tauto.
simpl in |- *.
  unfold prec_L in |- *.
  intros.
  decompose [and] H.
  clear H.
  elim (eq_dim_dec d k).
 intro.
   elim (eq_dart_dec d0 z).
  intro.
    rewrite <- a0 in |- *.
    rewrite <- a in |- *.
    apply nosucc_top.
    tauto.
   tauto.
   tauto.
 intro.
   simpl in |- *.
   elim (eq_dim_dec d k).
  elim (eq_dart_dec d0 (top (B m k z) d z)).
   intros.
     rewrite a1 in a0.
     rewrite IHm in a0.
     tauto.
    tauto.
    tauto.
  intros.
    rewrite a0 in |- *; apply IHm.
    tauto.
   tauto.
 intro.
   apply IHm.
   tauto.
  tauto.
intro.
  simpl in |- *.
  elim (eq_dim_dec d k).
  tauto.
intro.
  apply IHm.
  tauto.
 tauto.
Qed.

(*====================================================
       FACE OPERATIONS IN HMAPS: F, F_1, cF, cF_1
=====================================================*)

(* Following operations are designed for hmaps,
but are defined on fmap for convenience *)

(* Successor F in a face - direct version, 
designed for hmaps: *)

Definition F(m:fmap)(z:dart):=
  A_1 m one (A_1 m zero z).

(* To have a successor in a (direct) face for x: *)

Definition succf(m:fmap)(z:dart):Prop:=
  pred m zero z /\ pred m one (A_1 m zero z).

(* Decidability of succf:*)

Lemma succf_dec :
  forall (m:fmap)(z:dart),
    {succf m z}+{~succf m z}.
Proof.
intros.
unfold succf in |- *.
elim (pred_dec m one (A_1 m zero z)).
 elim (pred_dec m zero z).
  tauto.
  tauto.
 tauto.
Qed.

(* OK: *)

Lemma succf_exd : forall (m:fmap)(z:dart),
  inv_hmap m -> succf m z -> exd m z.
Proof.
unfold succf in |- *.
intros.
unfold pred in H0.
elim (exd_dec m z).
 tauto.
 intro.
   elim H0.
   intros.
   clear H0.
   elim H1.
   apply not_exd_A_1_nil.
  tauto.
  tauto.
Qed.

(* Predecessor in a face - direct version: *)

Definition F_1 (m:fmap)(z:dart):=
  A m zero (A m one z).

(* To have a predecessor in a (direct) face for z: *)

Definition predf(m:fmap)(z:dart):Prop:=
  succ m one z /\ succ m zero (A m one z).

(* Decidability of succf: *)

Lemma predf_dec :
  forall (m:fmap)(z:dart),
    {predf m z}+{~predf m z}.
Proof.
unfold predf in |- *.
intros.
generalize (succ_dec m one z).
generalize (succ_dec m zero (A m one z)).
 tauto.
Qed.

Lemma predf_exd : forall (m:fmap)(z:dart),
  inv_hmap m -> predf m z -> exd m z.
Proof.
unfold predf in |- *.
intros.
apply succ_exd with one.
  tauto.
 tauto.
Qed.

(* OK: *)

Lemma F_nil : forall m:fmap,
    inv_hmap m -> F m nil = nil.
Proof.
intros.
unfold F in |- *.
assert (A_1 m zero nil = nil).
 apply A_1_nil.
   tauto.
 rewrite H0.
   apply A_1_nil.
   tauto.
Qed.

(* IDEM: *)

Lemma F_1_nil : forall m:fmap,
    inv_hmap m -> F_1 m nil = nil.
Proof.
intros.
unfold F_1 in |- *.
assert (A m one nil = nil).
 apply A_nil.
   tauto.
 rewrite H0.
   apply A_nil.
   tauto.
Qed.

(* OK: *)

Lemma succf_exd_F : forall (m:fmap)(z:dart),
  inv_hmap m -> succf m z -> exd m (F m z).
Proof.
unfold succf in |- *.
unfold F in |- *.
intros.
apply pred_exd_A_1.
 tauto.
 tauto.
Qed.

(* IDEM: *)

Lemma predf_exd_F_1 : forall (m:fmap)(z:dart),
    inv_hmap m -> predf m z -> exd m (F_1 m z).
Proof.
unfold predf in |- *.
unfold F_1 in |- *.
intros.
apply succ_exd_A.
 tauto.
 tauto.
Qed.

(* IDEM: *)

Lemma succf_F: forall (m:fmap)(z:dart),
  inv_hmap m -> (succf m z <-> F m z <> nil).
Proof.
intros.
unfold succf in |- *.
unfold F in |- *.
unfold pred in |- *.
 intuition.
rewrite H1 in H0.
apply H0.
apply A_1_nil.
 tauto.
Qed.

Lemma predf_F_1: forall (m:fmap)(z:dart),
  inv_hmap m -> (predf m z <-> F_1 m z <> nil).
Proof.
intros.
unfold predf in |- *.
unfold F_1 in |- *.
unfold succ in |- *.
 intuition.
rewrite H1 in H0.
apply H0.
apply A_nil.
 tauto.
Qed.

(* OK: *)

Lemma not_exd_F_nil : forall (m:fmap)(z:dart),
    inv_hmap m -> ~exd m z -> F m z = nil.
Proof.
unfold F in |- *.
intros.
apply not_exd_A_1_nil.
 tauto.
 assert (A_1 m zero z = nil).
  apply not_exd_A_1_nil.
   tauto.
   tauto.
  rewrite H1.
    apply not_exd_nil.
    tauto.
Qed.

Lemma not_exd_F_1_nil : forall (m:fmap)(z:dart),
    inv_hmap m -> ~exd m z -> F_1 m z = nil.
Proof.
unfold F_1 in |- *.
intros.
apply not_exd_A_nil.
 tauto.
 assert (A m one z = nil).
  apply not_exd_A_nil.
   tauto.
   tauto.
  rewrite H1.
    apply not_exd_nil.
    tauto.
Qed.

(* F and F_1 are inverses: *)

Lemma F_F_1 : forall (m:fmap)(z:dart),
  inv_hmap m -> exd m z -> exd m (F_1 m z) ->
     F m (F_1 m z) = z.
Proof.
unfold F in |- *; unfold F_1 in |- *.
intros.
rewrite A_1_A.
 rewrite A_1_A.
  tauto.
  tauto.
  unfold succ in |- *.
    intro.
    rewrite H2 in H1.
    rewrite A_nil in H1.
   absurd (exd m nil).
    apply not_exd_nil.
      tauto.
    tauto.
   tauto.
 tauto.
 unfold succ in |- *.
   intro.
   rewrite H2 in H1.
   absurd (exd m nil).
  apply not_exd_nil.
    tauto.
  tauto.
Qed.

(* IDEM: *)

(* CAUTION !! PROPAGATION OF exd m (F_1 m z) IN PLACE OF
exd m (F m z) *)

Lemma F_1_F : forall (m:fmap)(z:dart),
  inv_hmap m -> exd m z -> exd m (F m z) ->
    F_1 m (F m z) = z.
Proof.
unfold F in |- *; unfold F_1 in |- *.
intros.
rewrite A_A_1.
 rewrite A_A_1.
  tauto.
  tauto.
  unfold pred in |- *.
    intro.
    rewrite H2 in H1.
    rewrite A_1_nil in H1.
   absurd (exd m nil).
    apply not_exd_nil.
      tauto.
    tauto.
   tauto.
 tauto.
 unfold pred in |- *.
   intro.
   rewrite H2 in H1.
   absurd (exd m nil).
  apply not_exd_nil.
    tauto.
  tauto.
Qed.

(* OK: *)

Lemma inj_F_succf :
   forall m:fmap, inv_hmap m ->
      inj_dart (succf m) (F m).
Proof.
intros.
unfold inj_dart in |- *.
unfold succf in |- *.
unfold F in |- *.
intros.
 intuition.
generalize (inj_A_1 m zero H).
unfold inj_dart in |- *.
intro.
apply H1.
  tauto.
 tauto.
generalize (inj_A_1 m one H).
  unfold inj_dart in |- *.
  intro.
  apply H6.
  tauto.
 tauto.
 tauto.
Qed.

(* IDEM:*)

Lemma inj_F_1_predf :
 forall m:fmap, inv_hmap m ->
      inj_dart (predf m) (F_1 m).
Proof.
intros.
unfold inj_dart in |- *.
unfold predf in |- *.
unfold F_1 in |- *.
intros.
 intuition.
generalize (inj_A m one H).
unfold inj_dart in |- *.
intro.
apply H1.
  tauto.
 tauto.
generalize (inj_A m zero H).
  unfold inj_dart in |- *.
  intro.
  apply H6.
  tauto.
 tauto.
 tauto.
Qed.

(*=====================================================
              CLOSURES cF, cF_1 OF F, F_1 :
=====================================================*)

(* SUCCESSOR IN A COMPLETED FACE: *)

Definition cF (m:fmap)(z:dart):=
  cA_1 m one (cA_1 m zero z).

Definition cF_1 (m:fmap)(z:dart):=
  cA m zero (cA m one z).

Lemma exd_cF_not_nil : forall (m:fmap)(z:dart),
  inv_hmap m -> (exd m z <-> cF m z <> nil).
Proof.
unfold cF in |- *.
intros.
split.
 intro.
   assert (cA_1 m zero z <> nil).
  generalize (succ_pred_clos m zero z H H0).
    tauto.
  generalize (succ_pred_clos m one (cA_1 m zero z) H).
    intros.
    assert (exd m (cA_1 m zero z)).
   generalize (exd_cA_cA_1 m zero z H H0).
     tauto.
   tauto.
intro.
   assert (exd m (cA_1 m zero z)).
  eapply cA_1_exd.
   tauto.
   apply H0.
  eapply exd_cA_1_exd.
   tauto.
   apply H1.
Qed.

(* IDEM: *)

Lemma exd_cF_1_not_nil : forall (m:fmap)(z:dart),
  inv_hmap m -> (exd m z <-> cF_1 m z <> nil).
Proof.
intros.
split.
 intro.
   assert (cA m one z <> nil).
  generalize (exd_cA m one z).
    intro.
    apply exd_not_nil with m.
    tauto.
   tauto.
 assert (exd m (cA m one z)).
  generalize (exd_cA_cA_1 m one z H H0).
     tauto.
 generalize (succ_pred_clos m zero (cA m one z) H H2).
    tauto.
intro.
  unfold cF_1 in H0.
  apply exd_cA_exd with one.
  tauto.
 eapply cA_exd.
    tauto.
  apply H0.
Qed.

Lemma exd_cF : forall (m:fmap)(z:dart),
  inv_hmap m -> (exd m z <-> exd m (cF m z)).
Proof.
unfold cF in |- *.
intros.
split.
 intro.
   assert (exd m (cA_1 m zero z)).
  generalize (exd_cA_cA_1 m zero z H H0).
    tauto.
  generalize (exd_cA_cA_1 m one (cA_1 m zero z) H H1).
    tauto.
 intro.
   assert (exd m (cA_1 m zero z)).
  eapply exd_cA_1_exd.
   tauto.
   apply H0.
  eapply exd_cA_1_exd.
   tauto.
   apply H1.
Qed.

(* IDEM: *)

Lemma exd_cF_1 : forall (m:fmap)(z:dart),
  inv_hmap m -> (exd m z <-> exd m (cF_1 m z)).

Proof.
unfold cF_1 in |- *.
intros.
split.
 intro.
   assert (exd m (cA m one z)).
  generalize (exd_cA_cA_1 m one z H H0).
    tauto.
  generalize (exd_cA_cA_1 m zero (cA m one z) H H1).
    tauto.
 intro.
   assert (exd m (cA m one z)).
  eapply exd_cA_exd.
   tauto.
   apply H0.
  eapply exd_cA_exd.
   tauto.
   apply H1.
Qed.

Lemma inj_cF :
  forall (m:fmap), inv_hmap m ->
      inj_dart (exd m) (cF m).
Proof.
unfold inj_dart in |- *.
unfold cF in |- *.
intros.
generalize inj_cA_1.
intros.
generalize (H3 m zero H).
unfold inj_dart in |- *.
intros.
eapply H4.
 tauto.
 tauto.
generalize (H3 m one H).
unfold inj_dart in |- *.
intro.
 eapply H5.
  generalize (exd_cA_cA_1 m zero x).
    tauto.
  generalize (exd_cA_cA_1 m zero x').
    tauto.
tauto.
Qed.

(* IDEM: *)

Lemma inj_cF_1 :
  forall (m:fmap), inv_hmap m ->
    inj_dart (exd m) (cF_1 m).
Proof.
unfold inj_dart in |- *.
unfold cF_1 in |- *.
intros.
generalize inj_cA.
intros.
generalize (H3 m one H).
unfold inj_dart in |- *.
intros.
eapply H4.
 tauto.
 tauto.
generalize (H3 m zero H).
unfold inj_dart in |- *.
intro.
 eapply H5.
  generalize (exd_cA_cA_1 m one x).
    tauto.
  generalize (exd_cA_cA_1 m one x').
    tauto.
tauto.
Qed.

Lemma cF_cF_1:forall (m:fmap)(z:dart),
  inv_hmap m -> exd m z -> cF m (cF_1 m z) = z.
Proof.
intros.
unfold cF in |- *.
unfold cF_1 in |- *.
rewrite cA_1_cA.
 rewrite cA_1_cA.
  tauto.
  tauto.
  tauto.
 tauto.
 generalize (exd_cA_cA_1 m one z H H0).
   tauto.
Qed.

Lemma cF_1_cF:forall (m:fmap)(z:dart),
  inv_hmap m -> exd m z -> cF_1 m (cF m z) = z.
Proof.
intros.
unfold cF in |- *.
unfold cF_1 in |- *.
rewrite cA_cA_1.
 rewrite cA_cA_1.
  tauto.
  tauto.
  tauto.
 tauto.
 generalize (exd_cA_cA_1 m zero z H H0).
   tauto.
Qed.

Lemma surj_cF :
  forall (m:fmap), inv_hmap m ->
      surj_dart (exd m) (cF m).
Proof.
unfold surj_dart in |- *.
intros.
split with (cF_1 m y).
rewrite cF_cF_1.
 split.
  generalize (exd_cF_1 m y).
    tauto.
  tauto.
 tauto.
 tauto.
Qed.

Lemma bij_cF :
  forall (m:fmap), inv_hmap m ->
      bij_dart (exd m) (cF m).
Proof.
unfold bij_dart in |- *.
intros.
split.
 apply inj_cF.
   tauto.
 apply surj_cF.
   tauto.
Qed.

(* IDEM: *)

Lemma surj_cF_1 :
  forall (m:fmap), inv_hmap m ->
      surj_dart (exd m) (cF_1 m).
Proof.
unfold surj_dart in |- *.
intros.
split with (cF m y).
rewrite cF_1_cF.
 split.
  generalize (exd_cF m y).
    tauto.
  tauto.
 tauto.
 tauto.
Qed.

(* IDEM: *)

Lemma bij_cF_1 :
  forall (m:fmap), inv_hmap m ->
      bij_dart (exd m) (cF_1 m).
Proof.
unfold bij_dart in |- *.
intros.
split.
 apply inj_cF_1.
   tauto.
 apply surj_cF_1.
   tauto.
Qed.

(* =================================================
        CHANGING AN OPENING IN AN ORBIT: Shift
====================================================*)

(* SHIFT OF THE OPENING IN AN ORBIT: *)

Definition Shift(m:fmap)(k:dim)(x:dart):=
  L (B m k x) k (top m k x) (bottom m k x).

(* cA_Shift : OK! *)

Lemma cA_Shift:forall(m:fmap)(k:dim)(x z:dart),
 inv_hmap m -> succ m k x -> 
   cA (Shift m k x) k z = cA m k z.
Proof.
unfold Shift.
induction k.
 simpl in |- *.
   intros.
   elim (eq_dart_dec (top m zero x) z).
  intro.
    rewrite <- a in |- *.
    rewrite cA_top in |- *.
    tauto.
   tauto.
  apply succ_exd with zero.
    tauto.
   tauto.
 elim (eq_dart_dec (cA_1 (B m zero x) zero 
          (bottom m zero x)) z).
  intros.
    generalize a.
    clear a.
    rewrite cA_B in |- *.
   rewrite cA_1_B in |- *.
    elim (eq_dart_dec (A m zero x) (bottom m zero x)).
     intro.
       symmetry  in a.
        absurd (bottom m zero x = A m zero x).
      apply succ_bottom.
        tauto.
       tauto.
      tauto.
    elim (eq_dart_dec (bottom m zero x) 
        (bottom m zero x)).
     elim (eq_dart_dec x (top m zero x)).
      intros.
        rewrite <- a in b.
         tauto.
     elim (eq_dart_dec (top m zero x) (top m zero x)).
      rewrite cA_eq in |- *.
       elim (succ_dec m zero z).
        intros.
          rewrite a2 in |- *.
           tauto.
       intros.
         rewrite a1 in H0.
          tauto.
       tauto.
      tauto.
     tauto.
    tauto.
    tauto.
   tauto.
   tauto.
 intros.
   rewrite cA_B in |- *.
  elim (eq_dart_dec x z).
   intros.
     rewrite cA_eq in |- *.
    elim (succ_dec m zero z).
     intro.
       generalize b.
       rewrite cA_1_B in |- *.
      elim (eq_dart_dec (A m zero x) 
       (bottom m zero x)).
       intro.
         symmetry  in a1.
          absurd (bottom m zero x = A m zero x).
        apply succ_bottom.
          tauto.
         tauto.
        tauto.
      elim (eq_dart_dec (bottom m zero x)
     (bottom m zero x)).
       intros.
          tauto.
       tauto.
      tauto.
      tauto.
    rewrite a in |- *.
       tauto.
    tauto.
  elim (eq_dart_dec (top m zero x) z).
    tauto.
   tauto.
  tauto.
  tauto.
intros.
  assert (exd m x).
 apply succ_exd with one.
   tauto.
  tauto.
simpl in |- *.
  intros.
  elim (eq_dart_dec (top m one x) z).
 intro.
   rewrite <- a in |- *.
   rewrite cA_top in |- *.
   tauto.
  tauto.
  tauto.
elim (eq_dart_dec (cA_1 (B m one x) one (bottom m one x)) z).
 intros.
   generalize a.
   clear a.
   rewrite cA_B in |- *.
  rewrite cA_1_B in |- *.
   elim (eq_dart_dec (A m one x) (bottom m one x)).
    elim (eq_dart_dec x (top m one x)).
     intros.
       symmetry  in a0.
        absurd (bottom m one x = A m one x).
      apply succ_bottom.
        tauto.
       tauto.
      tauto.
    elim (eq_dart_dec (top m one x) (top m one x)).
     intros.
        tauto.
    intros.
      rewrite a0 in |- *.
       tauto.
   elim (eq_dart_dec (bottom m one x) 
       (bottom m one x)).
    elim (eq_dart_dec x (top m one x)).
     intros.
       rewrite cA_eq in |- *.
      elim (succ_dec m one z).
       rewrite <- a1 in b.
         symmetry  in a.
          tauto.
      rewrite a1 in |- *.
         tauto.
      tauto.
    elim (eq_dart_dec (top m one x) (top m one x)).
     rewrite cA_eq in |- *.
      intros.
        elim (succ_dec m one z).
       rewrite a1 in |- *.
          tauto.
      rewrite <- a1 in |- *.
         tauto.
      tauto.
     tauto.
    tauto.
   tauto.
   tauto.
  tauto.
  tauto.
rewrite cA_B in |- *.
 rewrite cA_1_B in |- *.
  elim (eq_dart_dec (A m one x) (bottom m one x)).
   intro.
     symmetry  in a.
      absurd (bottom m one x = A m one x).
    apply succ_bottom.
      tauto.
     tauto.
    tauto.
  elim (eq_dart_dec (bottom m one x) (bottom m one x)).
   elim (eq_dart_dec x z).
     tauto.
   elim (eq_dart_dec (top m one x) z).
    rewrite cA_eq in |- *.
     intros.
       rewrite a in b2.
        tauto.
     tauto.
    tauto.
   tauto.
  tauto.
  tauto.
 tauto.
 tauto.
Qed.

(* cA_Shift_ter: OK! *)

Lemma cA_Shift_ter:forall(m:fmap)(k:dim)(x z:dart),
 inv_hmap m -> succ m k x -> 
  let k1 := dim_opp k in
   cA (Shift m k x) k1 z = cA m k1 z.
Proof.
unfold Shift.
intros.
induction k.
 simpl in |- *.
   rewrite cA_B_ter in |- *.
   tauto.
  tauto.
 intro.
   inversion H1.
simpl in |- *.
  rewrite cA_B_ter in |- *.
  tauto.
 tauto.
intro.
  inversion H1.
Qed.

(* A_Shift: *)

Lemma A_Shift:forall(m:fmap)(k:dim)(x z:dart),
 inv_hmap m -> succ m k x -> 
   A (Shift m k x) k z =
     if eq_dart_dec x z then nil 
     else if eq_dart_dec (top m k x) z 
          then (bottom m k x) 
          else A m k z.
Proof.
unfold Shift.
intros.
simpl in |- *.
elim (eq_dim_dec k k).
 elim (eq_dart_dec (top m k x) z).
  intros.
    elim (eq_dart_dec x z).
   intro.
     rewrite <- a1 in a.
     rewrite <- a in H0.
      absurd (succ m k (top m k x)).
    apply not_succ_top.
       tauto.
    tauto.
   tauto.
 intros.
   elim (eq_dart_dec x z).
  intro.
    rewrite <- a0 in |- *.
    rewrite A_B in |- *.
    tauto.
   tauto.
 intro.
   rewrite A_B_bis in |- *.
   tauto.
 intro.
   symmetry  in H1.
    tauto.
 tauto.
Qed.

(* A_Shift_ter: *)

Lemma A_Shift_ter:forall(m:fmap)(k:dim)(x z:dart),
 inv_hmap m -> succ m k x -> let k1:=dim_opp k in
   A (Shift m k x) k1 z = A m k1 z.
Proof.
  unfold Shift.
   intros.
induction k.
 simpl.
   simpl in |- *.
   apply A_B_ter.
   intro.
   inversion H1.
  simpl in |- *.
  rewrite A_B_ter in |- *.
  tauto.
intro.
  inversion H1.
Qed.

(* IDEM, SYMMETRIC: cA_1_Shift *)

Lemma cA_1_Shift:forall(m:fmap)(k:dim)(x z:dart),
 inv_hmap m -> succ m k x -> 
   cA_1 (Shift m k x) k z = cA_1 m k z.
Proof.
unfold Shift.
induction k.
 simpl in |- *.
   intros.
   assert (exd m x).
  apply succ_exd with zero.
    tauto.
   tauto.
 rename H1 into Exx.
   elim (eq_dart_dec (bottom m zero x) z).
  intro.
    rewrite <- a in |- *.
    rewrite cA_1_bottom in |- *.
    tauto.
   tauto.
   tauto.
 elim (eq_dart_dec 
   (cA (B m zero x) zero (top m zero x)) z).
  intros.
    generalize a.
    clear a.
    rewrite cA_B in |- *.
   rewrite cA_1_B in |- *.
    elim (eq_dart_dec x (top m zero x)).
      tauto.
    elim (eq_dart_dec (top m zero x) (top m zero x)).
     elim (eq_dart_dec (A m zero x) (bottom m zero x)).
      intros.
        rewrite <- a in b.
         tauto.
     elim (eq_dart_dec
    (bottom m zero x) (bottom m zero x)).
      intros.
        generalize (cA_eq m zero x H).
        elim (succ_dec m zero x).
       intros.
         rewrite <- a1 in |- *.
         rewrite <- H1 in |- *.
         rewrite cA_1_cA in |- *.
         tauto.
        tauto.
        tauto.
       tauto.
      tauto.
     tauto.
    tauto.
    tauto.
   tauto.
   tauto.
 intros.
   rewrite cA_1_B in |- *.
  elim (eq_dart_dec (A m zero x) z).
   intro.
     generalize b.
     rewrite cA_B in |- *.
    elim (eq_dart_dec x (top m zero x)).
     intros.
       rewrite a0 in H0.
        absurd (succ m zero (top m zero x)).
      apply not_succ_top.
         tauto.
      tauto.
    elim (eq_dart_dec (top m zero x) (top m zero x)).
      tauto.
     tauto.
    tauto.
    tauto.
  elim (eq_dart_dec (bottom m zero x) z).
    tauto.
   tauto.
  tauto.
  tauto.
intros.
  assert (exd m x).
 apply succ_exd with one.
   tauto.
  tauto.
simpl in |- *.
  elim (eq_dart_dec (bottom m one x) z).
 intros.
   rewrite <- a in |- *.
   rewrite cA_1_bottom in |- *.
   tauto.
  tauto.
  tauto.
elim (eq_dart_dec (cA (B m one x) one (top m one x)) z).
 intros.
   generalize a.
   rewrite cA_B in |- *.
  elim (eq_dart_dec x (top m one x)).
   intro.
     rewrite a0 in H0.
      absurd (succ m one (top m one x)).
    apply not_succ_top.
       tauto.
    tauto.
  elim (eq_dart_dec (top m one x) (top m one x)).
   intros.
     rewrite cA_1_B in |- *.
    elim (eq_dart_dec (A m one x) (bottom m one x)).
     intro.
       rewrite a2 in a1.
        tauto.
    elim (eq_dart_dec (bottom m one x) 
        (bottom m one x)).
     intros.
       generalize (cA_eq m one x H).
       elim (succ_dec m one x).
      intros.
        rewrite <- a1 in |- *.
        rewrite <- H2 in |- *.
        rewrite cA_1_cA in |- *.
        tauto.
       tauto.
       tauto.
      tauto.
     tauto.
    tauto.
    tauto.
   tauto.
  tauto.
  tauto.
rewrite cA_B in |- *.
 rewrite cA_1_B in |- *.
  elim (eq_dart_dec x (top m one x)).
   intro.
     rewrite a in H0.
      absurd (succ m one (top m one x)).
    apply not_succ_top.
       tauto.
    tauto.
  elim (eq_dart_dec (top m one x) (top m one x)).
   elim (eq_dart_dec (A m one x) z).
     tauto.
   elim (eq_dart_dec (bottom m one x) z).
     tauto.
    tauto.
   tauto.
  tauto.
  tauto.
 tauto.
 tauto.
Qed.

(* cA_1_Shift_ter: *)

Lemma cA_1_Shift_ter:forall(m:fmap)(k:dim)(x z:dart),
 inv_hmap m -> succ m k x -> 
  let k1 := dim_opp k in
   cA_1 (Shift m k x) k1 z =
   cA_1 m k1 z.
Proof.
unfold Shift.
intros.
induction k.
 simpl in |- *.
   rewrite cA_1_B_ter in |- *.
   tauto.
  tauto.
 intro.
   inversion H1.
simpl in |- *.
  rewrite cA_1_B_ter in |- *.
  tauto.
 tauto.
intro.
  inversion H1.
Qed.

(* A_1_S: *)

Lemma A_1_Shift:forall(m:fmap)(k:dim)(x z:dart),
 inv_hmap m -> succ m k x -> 
   A_1 (Shift m k x) k z =
     if eq_dart_dec (A m k x) z then nil 
     else if eq_dart_dec (bottom m k x) z 
          then (top m k x) 
          else A_1 m k z.
Proof.
intros.
simpl in |- *.
elim (eq_dim_dec k k).
 elim (eq_dart_dec (bottom m k x) z).
  elim (eq_dart_dec (A m k x) z).
   intros.
     rewrite <- a in a0.
      absurd (bottom m k x = A m k x).
    apply succ_bottom.
      tauto.
     tauto.
    tauto.
   tauto.
 elim (eq_dart_dec (A m k x) z).
  intros.
    rewrite <- a in |- *.
    apply A_1_B.
     tauto.
 intros.
   rewrite A_1_B_bis in |- *.
   tauto.
  tauto.
 intro.
   symmetry in H1.
    tauto.
 tauto.
Qed.

(* A_1_Shift_ter: *)

Lemma A_1_Shift_ter:forall(m:fmap)(k:dim)(x z:dart),
 inv_hmap m -> succ m k x -> let k1:=dim_opp k in
   A_1 (Shift m k x) k1 z = A_1 m k1 z.
Proof.
  unfold Shift.
   intros.
induction k.
   simpl in |- *.
   apply A_1_B_ter.
   intro.
   inversion H1.
  simpl in |- *.
  rewrite A_1_B_ter in |- *.
  tauto.
intro.
  inversion H1.
Qed.

(* BOTH, OK: USEFUL?
Lemma cA_cA_1_Shift:forall(m:fmap)(k:dim)(x:dart),
 inv_hmap m -> succ m k x -> 
  (forall z:dart, exd m z -> 
     cA (Shift m k x) k z = cA m k z) ->
  (forall z:dart, exd m z ->
     cA_1 (Shift m k x) k z = cA_1 m k z).
Proof.
unfold Shift.
intros.
set (t := cA_1 (L (B m k x) k (top m k x) 
         (bottom m k x)) k z) in |- *.
assert (exd m x).
 apply succ_exd with k.
   tauto.
  tauto.
assert (prec_L (B m k x) k (top m k x) (bottom m k x)).
 unfold prec_L in |- *.
   split.
  generalize (exd_B m k x (top m k x)).
    generalize (exd_top m k x).
     tauto.
 split.
  generalize (exd_B m k x (bottom m k x)).
    generalize (exd_bottom m k x).
     tauto.
 split.
  unfold succ in |- *.
    rewrite A_B_bis in |- *.
   fold (succ m k (top m k x)) in |- *.
     apply not_succ_top.
      tauto.
  intro.
    rewrite <- H4 in H0.
    generalize H0.
    apply not_succ_top.
     tauto.
 split.
  unfold pred in |- *.
    rewrite A_1_B_bis in |- *.
   fold (pred m k (bottom m k x)) in |- *.
     apply not_pred_bottom.
      tauto.
   tauto.
  apply succ_bottom.
    tauto.
   tauto.
 rewrite cA_B in |- *.
  elim (eq_dart_dec x (top m k x)).
   intro.
     rewrite a in H0.
      absurd (succ m k (top m k x)).
    apply not_succ_top.
       tauto.
    tauto.
  elim (eq_dart_dec (top m k x) (top m k x)).
   intros.
     generalize (succ_bottom m k x).
     intros.
     intro.
     symmetry  in H5.
      tauto.
   tauto.
  tauto.
  tauto.
assert (z = cA (L (B m k x) k (top m k x) 
     (bottom m k x)) k t).
 unfold t in |- *.
   rewrite cA_cA_1 in |- *.
   tauto.
 simpl in |- *.
   split.
  apply inv_hmap_B.
     tauto.
  tauto.
 simpl in |- *.
   generalize (exd_B m k x z).
    tauto.
assert (exd m t).
 unfold t in |- *.
   simpl in |- *.
   elim (eq_dim_dec k k).
  elim (eq_dart_dec (bottom m k x) z).
   intros.
     generalize (exd_top m k x).
      tauto.
  elim (eq_dart_dec (cA (B m k x) k (top m k x)) z).
   intros.
     generalize (exd_cA_1 (B m k x) k (bottom m k x)).
     generalize (inv_hmap_B m k x).
     generalize (exd_B m k x (bottom m k x)).
     generalize (exd_bottom m k x).
     generalize 
   (exd_B m k x (cA_1 (B m k x) k (bottom m k x))).
      tauto.
  intros.
    rewrite cA_1_B in |- *.
   elim (eq_dart_dec (A m k x) z).
    intro.
      apply exd_top.
      tauto.
     tauto.
   elim (eq_dart_dec (bottom m k x) z).
     tauto.
   intros.
     generalize (exd_cA_1 m k z).
      tauto.
   tauto.
   tauto.
  tauto.
assert (z = cA m k t).
 generalize (H1 t H6).
   rewrite H5 in |- *.
    tauto.
rewrite H7 in |- *.
  rewrite cA_1_cA in |- *.
  tauto.
 tauto.
 tauto.
Qed.
*)

(* inv_hmap_Shift: *)

Lemma inv_hmap_Shift:forall(m:fmap)(k:dim)(x:dart),
  inv_hmap m -> succ m k x -> 
    inv_hmap (Shift m k x).
Proof.
unfold Shift.
intros.
simpl in |- *.
split.
 apply inv_hmap_B.
    tauto.
assert (exd m x).
 apply succ_exd with k.
   tauto.
  tauto.
unfold prec_L in |- *.
  split.
 generalize (exd_B m k x (top m k x)).
   generalize (exd_top m k x).
   generalize (succ_exd m k x).
    tauto.
split.
 generalize (exd_B m k x (bottom m k x)).
   generalize (exd_bottom m k x).
   generalize (succ_exd m k x).
    tauto.
split.
 unfold succ in |- *.
   rewrite A_B_bis in |- *.
  fold (succ m k (top m k x)) in |- *.
    apply not_succ_top.
     tauto.
 intro.
   rewrite <- H2 in H0.
   generalize H0.
   apply not_succ_top.
    tauto.
split.
 unfold pred in |- *.
   rewrite A_1_B_bis in |- *.
  fold (pred m k (bottom m k x)) in |- *.
    apply not_pred_bottom.
     tauto.
  tauto.
 apply succ_bottom.
   tauto.
  tauto.
rewrite cA_B in |- *.
 elim (eq_dart_dec x (top m k x)).
  intro.
    rewrite a in H0.
     absurd (succ m k (top m k x)).
   apply not_succ_top.
      tauto.
   tauto.
 elim (eq_dart_dec (top m k x) (top m k x)).
  intros.
    intro.
    symmetry  in H2.
    generalize H2.
    apply succ_bottom.
    tauto.
   tauto.
  tauto.
 tauto.
 tauto.
Qed.

(* OK: exd_Shift: *)

Lemma exd_Shift: forall(m:fmap)(k:dim)(x z:dart),
  exd m z <-> exd (Shift m k x) z.
Proof.
unfold Shift.
intros.
simpl in |- *.
generalize (exd_B m k x z).
 tauto.
Qed.

(* OK: cF_Shift *)

Lemma cF_Shift:forall(m:fmap)(k:dim)(x z:dart),
 inv_hmap m -> succ m k x -> 
   cF (Shift m k x) z = cF m z.
Proof.
intros.
unfold cF in |- *.
induction k.
 rewrite cA_1_Shift in |- *.
  rewrite (cA_1_Shift_ter m zero x) in |- *.
   simpl in |- *.
      tauto.
   tauto.
   tauto.
  tauto.
  tauto.
rewrite (cA_1_Shift_ter m one x) in |- *.
 rewrite cA_1_Shift in |- *.
  simpl in |- *.
     tauto.
  tauto.
  tauto.
 tauto.
 tauto.
Qed.

(* OK: cF_1_Shift *)

Lemma cF_1_Shift:forall(m:fmap)(k:dim)(x z:dart),
 inv_hmap m -> succ m k x -> 
   cF_1 (Shift m k x) z = cF_1 m z.
Proof.
intros.
unfold cF_1 in |- *.
induction k.
 rewrite (cA_Shift_ter m zero x) in |- *.
  rewrite cA_Shift in |- *.
   simpl in |- *.
      tauto.
   tauto.
   tauto.
  tauto.
  tauto.
rewrite (cA_Shift m one x) in |- *.
 rewrite (cA_Shift_ter m one x) in |- *.
  simpl in |- *.
     tauto.
  tauto.
  tauto.
 tauto.
 tauto.
Qed.

(*====================================================
      CUTTING k-ORBITS: OPERATION Split (1st VERSION)
=====================================================*)

(* CUTTING A k-ORBIT AT (x x'): GENERAL (Split) *) 

Definition Split(m:fmap)(k:dim)(x x':dart):fmap:=
  if succ_dec m k x 
  then if succ_dec m k x' 
        then B (L (B m k x) 
                k (top m k x) (bottom m k x)) k x'
        else B m k x
  else B m k x'.

(* OK: *)

Lemma exd_Split:forall(m:fmap)(k:dim)(x x' z:dart),
  exd m z <-> exd (Split m k x x') z.
Proof.
unfold Split in |- *.
intros.
elim (succ_dec m k x).
 elim (succ_dec m k x').
  intros.
    generalize 
 (exd_B (L (B m k x) k (top m k x) 
     (bottom m k x)) k x' z).
    assert
 (exd (L (B m k x) k (top m k x) (bottom m k x)) z
   <-> exd (B m k x) z).
   simpl in |- *.
      tauto.
  generalize (exd_B m k x z).
    intro.
    intro.
tauto.
 generalize (exd_B m k x z).
    tauto.
generalize (exd_B m k x' z).
   tauto.
Qed.

Lemma exd_Split_bis:forall(m:fmap)(k:dim)(x x' z:dart),
  inv_hmap m -> (exd m z <-> exd (Split m k x x') z).
Proof. intros. apply exd_Split. Qed.

(* OK: *)

Lemma inv_hmap_Split:forall(m:fmap)(k:dim)(x x':dart),
   inv_hmap m -> inv_hmap (Split m k x x').
Proof.
unfold Split in |- *.
intros.
elim (succ_dec m k x).
 intro.
   elim (succ_dec m k x').
  intros.
    apply inv_hmap_B.
    fold (Shift m k x) in |- *.
    apply inv_hmap_Shift.
    tauto.
   tauto.
 intro.
   apply inv_hmap_B.
    tauto.
intro.
  elim (succ_dec m k x').
 intro.
   apply inv_hmap_B.
    tauto.
intro.
  rewrite not_succ_B in |- *.
  tauto.
 tauto.
 tauto.
Qed.

(*====================================================
     CUTTING k-ORBITS: OPERATION Split (2nd VERSION)
====================================================

(* CUTTING A k-ORBIT AT (x y): GENERAL (Split) *) 

Definition Split(m:fmap)(k:dim)(x y:dart):fmap:=
  if succ_dec m k x 
  then if pred_dec m k y 
        then B (Shift m k x) k (cA_1 m k y)
        else B m k x
  else B m k (cA_1 m k y).

(* OK: *)

Lemma exd_Split:forall(m:fmap)(k:dim)(x y z:dart),
  exd m z <-> exd (Split m k x y) z.
Proof.
unfold Split in |- *.
intros.
elim (succ_dec m k x).
 elim (pred_dec m k y).
  intros.
    generalize 
 (exd_B (Shift m k x) k (cA_1  m k y) z).
  generalize (exd_Shift m k x z).
  tauto. 
  generalize (exd_B m k x z). tauto. 
 generalize (exd_B m k (cA_1 m k y) z).
    tauto.
Qed.

Lemma exd_Split_bis:forall(m:fmap)(k:dim)(x x' z:dart),
  inv_hmap m -> (exd m z <-> exd (Split m k x x') z).
Proof. intros. apply exd_Split. Qed.

(* OK: *)

Lemma inv_hmap_Split:forall(m:fmap)(k:dim)(x y:dart),
   inv_hmap m -> inv_hmap (Split m k x y).
Proof.
unfold Split in |- *.
intros.
elim (succ_dec m k x).
 intro.
   elim (pred_dec m k y).
  intros.
    apply inv_hmap_B.
    apply inv_hmap_Shift.
    tauto.
   tauto.
 intro.
   apply inv_hmap_B.
    tauto.
intro.
  elim (pred_dec m k y).
 intro.
   apply inv_hmap_B.
    tauto.
intro. apply inv_hmap_B.
 tauto.
Qed.
*)

(*==================================================
               MERGING 
        k-ORBITS: OPERATION Merge (essai)
====================================================*)

(* MEGING 2 k-ORBITS AT (x y): GENERAL*) 

Definition Merge(m:fmap)(k:dim)(x y:dart):=
   let m1:= if succ_dec m k x then Shift m k x else m in
   let m2:= if pred_dec m k y then Shift m1 k (cA_1 m k y) else m in
   L (L m2 k x y) k (cA_1 m k y) (cA m k x).

Lemma exd_Merge:forall(m:fmap)(k:dim)(x y z:dart),
  exd m z <-> exd (Merge m k x y) z.
Proof.
unfold Merge in |- *. 
intros. simpl. 
elim (succ_dec m k x).
 elim (pred_dec m k y).
  intros.
    generalize 
 (exd_Shift (Shift m k x) k (cA_1  m k y) z).
  generalize (exd_Shift m k x z).
  tauto. tauto. 
 elim (pred_dec m k y).
  intros. 
 generalize (exd_Shift m k (cA_1 m k y) z).
  tauto. tauto.
Qed.

Lemma exd_Merge_bis:forall(m:fmap)(k:dim)(x y z:dart),
  inv_hmap m -> (exd m z <-> exd (Merge m k x y) z).
Proof. intros. apply exd_Merge. Qed.

(* OK: *)

(* PB D'EXPRESSION AVEC expo PAS ENCORE CONNU...

Lemma inv_hmap_Merge:forall(m:fmap)(k:dim)(x y:dart),
   ~MfcAk.expo m x y ->
        inv_hmap m -> inv_hmap (Merge m k x y).
Proof.
unfold Merge in |- *.
intros.
elim (succ_dec m k x).
 intro.
   elim (pred_dec m k y). intro. 
   assert (inv_hmap (Shift m k x)). 
    apply inv_hmap_Shift. tauto. tauto. 
   assert (inv_hmap (Shift (Shift m k x) k (cA_1 m k y))). 
    apply inv_hmap_Shift. tauto. 
   unfold succ. rewrite A_Shift. 

  intros.
    apply inv_hmap_B.
    apply inv_hmap_Shift.
    tauto.
   tauto.
 intro.
   apply inv_hmap_B.
    tauto.
intro.
  elim (pred_dec m k y).
 intro.
   apply inv_hmap_B.
    tauto.
intro. apply inv_hmap_B.
 tauto.
Qed.
*)

(*=====================================================
=======================================================
                     END OF PART 1
=======================================================
=====================================================*)











