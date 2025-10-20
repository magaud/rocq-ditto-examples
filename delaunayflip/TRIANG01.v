(*=====================================================
=======================================================
               TOPOLOGICAL HMAPS, MAPS -
               WITH TAGS AND EMBEDDINGS

            TRIANGULATION, BAR, HEXA, QUAD 
                      
                 FLIP (BEGINNING)

                 PART 1, COMPILED

OCTOBER 2008, REVIEWED MAY 2009
=======================================================
=====================================================*)

Require Export Del13.
From Stdlib Require Import Lia.

(*===================================================
         NOTION OF (TOPOLOGICAL) TRIANGULATION  
====================================================*)

(* OBSERVATIONAL POINT OF VIEW ONLY *)

Open Scope nat_scope.

(* OK: *)

Lemma degreee_fixpt: forall(m:fmap)(z:dart),
 inv_hmap m -> exd m z -> 
   (degreee m z = 1 <-> cA m zero z = z).
Proof.
intros.
assert (0 < ndN m)%nat.
 apply MA1.MfcA.ndN_pos with z.
    tauto.
rename H1 into npos.
  generalize (MA0.MfcA.degree_per m z H H0).
  assert (MA0.MfcA.degree = degreee).
  tauto.
rewrite H1 in |- *.
  intro.
  split.
 intro.
   rewrite H3 in H2.
   simpl in H2.
    tauto.
intro.
  unfold degreee in |- *.
  unfold MA0Tr.MfM.degree in |- *.
  rewrite MA0Tr.MfM.degree_aux_equation in |- *.
  elim (Arith.Compare_dec.le_lt_dec 1 (ndN m)).
 elim (eq_dart_dec z (Iter (MA0Tr.MfM.f m) 1 z)).
   tauto.
 intro.
   simpl in b.
   symmetry  in H3.
    tauto.
intro.
   lia.
Qed.

(* OK: *)

Lemma degreev_fixpt: forall(m:fmap)(z:dart),
 inv_hmap m -> exd m z -> 
    (degreev m z = 1 <-> cA m one z = z).
Proof.
intros.
assert (0 < ndN m)%nat.
 apply MA1.MfcA.ndN_pos with z.
    tauto.
rename H1 into npos.
  generalize (MA1.MfcA.degree_per m z H H0).
  assert (MA1.MfcA.degree = degreev).
  tauto.
rewrite H1 in |- *.
  intro.
  split.
 intro.
   rewrite H3 in H2.
   simpl in H2.
    tauto.
intro.
  unfold degreev in |- *.
  unfold MA1Tr.MfM.degree in |- *.
  rewrite MA1Tr.MfM.degree_aux_equation in |- *.
  elim (Arith.Compare_dec.le_lt_dec 1 (ndN m)).
 elim (eq_dart_dec z (Iter (MA1Tr.MfM.f m) 1 z)).
   tauto.
 intro.
   simpl in b.
   symmetry  in H3.
    tauto.
intro.
   lia.
Qed.

(* OK: *)

Lemma degreef_fixpt: forall(m:fmap)(z:dart),
 inv_hmap m -> exd m z -> 
    (degreef m z = 1 <-> cF m z = z).
Proof.
intros.
assert (0 < ndN m).
 apply MA1.MfcA.ndN_pos with z.
    tauto.
rename H1 into npos.
  generalize (MF.degree_per m z H H0).
  assert (MF.degree = degreef).
  tauto.
rewrite H1 in |- *.
  intro.
  split.
 intro.
   rewrite H3 in H2.
   simpl in H2.
    tauto.
intro.
  unfold degreef in |- *.
  unfold MF0Tr.MfM.degree in |- *.
  rewrite MF0Tr.MfM.degree_aux_equation in |- *.
  elim (Arith.Compare_dec.le_lt_dec 1 (ndN m)).
 elim (eq_dart_dec z (Iter (MF0Tr.MfM.f m) 1 z)).
   tauto.
 intro.
   simpl in b.
   elim b.
   symmetry  in |- *.
    tauto.
intro.
   lia.
Qed.

(* OK: *)

Lemma degreee_invol_nofixpt: 
forall(m:fmap)(z:dart),
 inv_hmap m -> exd m z -> 
   (degreee m z = 2 <-> 
 (cA m zero z <> z /\ cA m zero (cA m zero z) = z)).
Proof.
intros.
assert (0 < ndN m).
 apply MA0.MfcA.ndN_pos with z.
    tauto.
rename H1 into npos.
  generalize (MA0.MfcA.degree_per m z H H0).
  assert (MA0.MfcA.degree = degreee).
  tauto.
rewrite H1 in |- *.
  intro.
  split.
 intro.
   rewrite H3 in H2.
   simpl in H2.
   generalize (degreee_fixpt m z H H0).
   intro.
   rewrite H3 in H4.
   assert (2 <> 1). clear H4. 
   lia.
 split.
   tauto.
  tauto.
intros.
  unfold degreee in |- *.
  unfold MA0Tr.MfM.degree in |- *.
  rewrite MA0Tr.MfM.degree_aux_equation in |- *.
  elim (Arith.Compare_dec.le_lt_dec 1 (ndN m)).
 elim (eq_dart_dec z (Iter (MA0Tr.MfM.f m) 1 z)).
  simpl in |- *.
    intro.
    symmetry  in a.
     tauto.
 elim (Nat.eq_dec 1 (ndN m)).
  intros.
     lia.
 intros.
   rewrite MA0Tr.MfM.degree_aux_equation in |- *.
   elim (Arith.Compare_dec.le_lt_dec (1 + 1) (ndN m)).
  elim (eq_dart_dec z (Iter (MA0Tr.MfM.f m) 
   (1 + 1) z)).
   intros.
      lia.
  intro.
    assert (1 + 1 = 2).
    lia.
  rewrite H4 in b1.
    simpl in b1.
    elim b1.
    symmetry  in |- *.
     tauto.
 intro.
    lia.
intro.
   lia.
Qed.

(* OK: *)

Lemma degreev_invol_nofixpt: 
forall(m:fmap)(z:dart),
 inv_hmap m -> exd m z -> 
   (degreev m z = 2 <-> 
 (cA m one z <> z /\ cA m one (cA m one z) = z)).
Proof.
intros.
assert (0 < ndN m).
 apply MA1.MfcA.ndN_pos with z.
    tauto.
rename H1 into npos.
  generalize (MA1.MfcA.degree_per m z H H0).
  assert (MA1.MfcA.degree = degreev).
  tauto.
rewrite H1 in |- *.
  intro.
  split.
 intro.
   rewrite H3 in H2.
   simpl in H2.
   generalize (degreev_fixpt m z H H0).
   intro.
   rewrite H3 in H4.
   assert (2 <> 1)%nat. clear H4. 
   lia.
 split.
   tauto.
  tauto.
intros.
  unfold degreev in |- *.
  unfold MA1Tr.MfM.degree in |- *.
  rewrite MA1Tr.MfM.degree_aux_equation in |- *.
  elim (Arith.Compare_dec.le_lt_dec 1 (ndN m)).
 elim (eq_dart_dec z (Iter (MA1Tr.MfM.f m) 1 z)).
  simpl in |- *.
    intro.
    symmetry  in a.
     tauto.
 elim (Nat.eq_dec 1 (ndN m)).
  intros.
     lia.
 intros.
   rewrite MA1Tr.MfM.degree_aux_equation in |- *.
   elim (Arith.Compare_dec.le_lt_dec (1 + 1) (ndN m)).
  elim (eq_dart_dec z (Iter (MA1Tr.MfM.f m) 
   (1 + 1) z)).
   intros.
      lia.
  intro.
    assert (1 + 1 = 2).
    lia.
  rewrite H4 in b1.
    simpl in b1.
    elim b1.
    symmetry  in |- *.
     tauto.
 intro.
    lia.
intro.
   lia.
Qed.

(* OK: *)

Lemma degreef_invol_nofixpt: 
forall(m:fmap)(z:dart),
 inv_hmap m -> exd m z -> 
   (degreef m z = 2 <-> 
 (cF m z <> z /\ cF m (cF m z) = z)).
Proof.
intros.
assert (0 < ndN m).
 apply MA1.MfcA.ndN_pos with z.
    tauto.
generalize (MF.degree_per m z H H0).
  assert (MF.degree = degreef).
  tauto.
intro.
  split.
 intro.
   rewrite <- H2 in H4.
   rewrite H4 in H3.
   generalize (degreef_fixpt m z H H0).
   intro.
   simpl in H3.
   rewrite H2 in H4.
   split.
  intro.
    assert (degreef m z = 1).
    tauto. rewrite H4 in H7. 
   generalize H7. clear H3 H5 H6. inversion H7.
  tauto.
intros.
  unfold degreef in |- *.
  unfold MF0Tr.MfM.degree in |- *.
  rewrite MF0Tr.MfM.degree_aux_equation in |- *.
  elim (Arith.Compare_dec.le_lt_dec 1 (ndN m)).
 elim (eq_dart_dec z (Iter (MF0Tr.MfM.f m) 1 z)).
  simpl in |- *.
    intro.
    symmetry  in a.
     tauto.
 elim (Nat.eq_dec 1 (ndN m)).
  intros.
     lia.
 intros.
   rewrite MF0Tr.MfM.degree_aux_equation in |- *.
   elim (Arith.Compare_dec.le_lt_dec (1 + 1) (ndN m)).
  elim (eq_dart_dec z
    (Iter (MF0Tr.MfM.f m) (1 + 1) z)).
   intros.
      lia.
  intro.
    assert (1 + 1 = 2).
    lia.
  rewrite H5 in b1.
    simpl in b1.
    elim b1.
    symmetry  in |- *.
     tauto.
 intro.
    lia.
intro.
   lia.
Qed.

(* OK: *)

Lemma invol_inverse: 
forall(m:fmap)(k:dim)(z:dart),
 inv_hmap m -> exd m z -> 
  (cA m k (cA m k z) = z <-> cA m k z = cA_1 m k z).
Proof.
intros.
split.
 intro.
   rewrite <- H1 in |- *.
   rewrite cA_1_cA in |- *.
  rewrite H1 in |- *.
     tauto.
  tauto.
 generalize (exd_cA m k z).
    tauto.
intro.
  rewrite H1 in |- *.
  rewrite cA_cA_1 in |- *.
  tauto.
 tauto.
 tauto.
Qed.

(* COMBINATORIAL MAP: inv_map m EXTRACTED,
FOR TECHNICAL REASONS: *)

Definition isMap(m:fmap):Prop:=
  forall z:dart, exd m z -> degreee m z = 2.

(* TO BE COMPOSED OF TRUE POLYGONS, NOT
OF POLYGONAL LINES *) 

Definition isPoly(m:fmap):Prop:=
  forall z:dart, exd m z -> 2 <= degreev m z. 

(* TO BE A TRIANGLE, ETC.:
REDUCED TO THE MINIMUM *)

Definition isTri(m:fmap)(z:dart):Prop:=
  degreef m z = 3.

Definition isQuad(m:fmap)(z:dart):Prop:=
  degreef m z = 4.

Definition isHexa(m:fmap)(z:dart):Prop:=
  degreef m z = 6.

(* TO BE A TRIANGULATION FOR A MAP: *)

Definition isTriangulation(m:fmap):Prop:=
  forall z:dart, exd m z -> isTri m z.

(* TO BE AN ISOLATED BAR IN A MAP *)

Definition isBar(m:fmap)(z:dart):Prop:=
 degreee m z = 2 /\ degreev m z = 1 /\ 
   degreef m z = 2.

(* OK: *)

Lemma isBar_symm:forall(m:fmap)(z:dart),
 inv_hmap m -> exd m z -> 
  isBar m z -> isBar m (cA m zero z).
Proof.
intros.
unfold isBar in H1.
assert (cA m zero z <> z /\ cA m zero (cA m zero z) = z).
 generalize (degreee_invol_nofixpt m z H H0).
    tauto.
generalize (degreev_fixpt m z H H0).
  intro.
  assert (cA m one z = z).
  tauto.
clear H3.
  assert (exd m (cA m zero z)).
 generalize (exd_cA m zero z).
    tauto.
generalize (degreef_invol_nofixpt m z H H0).
  intro.
  assert (cF m z <> z /\ cF m (cF m z) = z).
  tauto.
clear H5.
  elim H2.
  clear H2.
  intros.
  elim H6.
  clear H6; intros.
  set (t := cA m zero z) in |- *.
  fold t in H5.
  fold t in H3.
  unfold isBar in |- *.
  generalize (degreee_invol_nofixpt m t H H3).
  intros.
  assert (cA m zero t <> t).
 rewrite H5 in |- *.
   unfold t in |- *.
   intro.
   symmetry  in H9.
    tauto.
split.
 assert (cA m zero (cA m zero t) = t).
  unfold t in |- *.
    fold t in |- *.
    rewrite H5 in |- *.
    fold t in |- *.
     tauto.
  tauto.
split.
 generalize (degreev_fixpt m t H H3).
   intro.
   assert (cA m one t = t).
  unfold t in |- *.
    assert (cF m z = cF_1 m z).
   rewrite <- H7 in |- *.
     rewrite cF_1_cF in |- *.
    rewrite H7 in |- *.
       tauto.
    tauto.
   generalize (exd_cF m z).
      tauto.
  generalize (invol_inverse m zero z H H0).
    fold t in |- *.
    intro.
    assert (t = cA_1 m zero z).
    tauto.
  clear H12.
    unfold cF in H11.
    unfold cF_1 in H11.
    rewrite H4 in H11.
    fold t in H11.
    rewrite <- H13 in H11.
    rewrite <- H11 in |- *.
    rewrite cA_cA_1 in |- *.
   symmetry  in |- *.
      tauto.
   tauto.
   tauto.
  tauto.
generalize (degreef_invol_nofixpt m t H H3).
  intros.
  assert (cF m t <> t).
 intro.
   unfold cF in H11.
   unfold t in H11.
   rewrite cA_1_cA in H11.
  rewrite <- H4 in H11.
    rewrite cA_1_cA in H11.
   rewrite H4 in H11.
     symmetry  in H11.
      tauto.
   tauto.
   tauto.
  tauto.
  tauto.
assert (cF m (cF m t) = t).
 unfold cF in |- *.
   unfold t in |- *.
   rewrite cA_1_cA in |- *.
  rewrite <- H4 in |- *.
    rewrite cA_1_cA in |- *.
   fold (cF m z) in |- *.
     fold (cF_1 m z) in |- *.
     rewrite <- H7 in |- *.
     rewrite cF_1_cF in |- *.
    rewrite H7 in |- *.
       tauto.
    tauto.
   generalize (exd_cF m z).
      tauto.
   tauto.
   tauto.
  tauto.
  tauto.
 tauto.
Qed.

(* TO BE AN ISTHMUS IN A MAP: *) 

Definition isIsthmus(m:fmap)(z:dart):Prop:=
   expf m z (cA m zero z).

(* OK: *)

Lemma isIsthmus_symm:forall(m:fmap)(z:dart),
  inv_hmap m -> isMap m -> exd m z ->
    (isIsthmus m z <-> isIsthmus m (cA m zero z)).
Proof.
intros.
unfold isMap in H0.
assert (degreee m z = 2).
  intuition.
unfold isIsthmus in |- *.
  generalize (degreee_invol_nofixpt m z).
  intros.
  assert (cA m zero (cA m zero z) = z).
  tauto.
rewrite H4 in |- *.
  split.
 apply expf_symm.
apply expf_symm.
Qed.

(* OK: *)

Lemma degreev_crackv: forall(m:fmap)(x:dart), 
 inv_hmap m -> exd m x -> 2 <= degreev m x ->
    crackv m x (cA_1 m one x).
Proof.
intros.
unfold crackv in |- *.
unfold MA1.crack in |- *.
split.
 intro.
   assert (cA m one x = x).
  rewrite H2 in |- *.
    rewrite cA_cA_1 in |- *.
    tauto.
   tauto.
   tauto.
 generalize (degreev_fixpt m x H H0).
   intro.
   assert (degreev m x = 1).
   tauto. 
    rewrite H5 in H1. 
        absurd (2<=1). clear H1 H2 H3 H4 H5. 
  lia. tauto. 
apply MA1.MfcA.expo_symm.
  tauto.
unfold MA1.MfcA.expo in |- *.
  split.
 generalize (exd_cA_1 m one x).
    tauto.
split with 1.
  simpl in |- *.
  assert (MA1.MfcA.f m (cA_1 m one x) = 
    cA m one (cA_1 m one x)).
  tauto.
rewrite H2 in |- *.
  rewrite cA_cA_1 in |- *.
  tauto.
 tauto.
 tauto.
Qed.

(* TOPOLOGICAL TRIANGULATION: *)

Definition inv_Triangulation(m:fmap):Prop:=
 inv_hmap m /\ 
   isMap m /\ isPoly m /\ isTriangulation m.

(*====================================================
         FLIPPING AN EXISTING EDGE (REP. BY x)
             IN A TRIANGULATION  
=====================================================*)

(* TOPOLOGICAL FLIP WITH Split and Merge:

Definition Flip(m:fmap)(x:dart):fmap:=
  let x_1 := cA_1 m one x in
  let y := cA m zero x in
  let y_1 := cA_1 m one y in
  let xf := cF m x in
  let xff := cF m xf in
  let yf := cF m y in
  let yff := cF m yf in
  let pxff := fpoint m xff in
  let pyff := fpoint m yff in
  let m1 := Split m one x x_1 in
  let m2 := Split m1 one y y_1 in 
  let m3 := Merge m2 one xff x in 
  let m4 := Merge m3 one yff y in
  let m5 := Chp m4 x pxff in
  Chp m5 y pyff.

*)

(*==================================================
  Flip1: MERGES 2 TRIANGLES INTO A HEXAHEDRAL FACE
===================================================*)

(*=== PRELIMINARIES ===*)

(* NEW: OK: *)

Lemma Map_diff_edge: forall(m:fmap)(x:dart),
  inv_hmap m -> exd m x -> degreee m x = 2 -> 
  let y := cA m zero x in
  let x_0:= cA_1 m zero x in
  let y0:= cA m zero y in
  y <> x /\ y = x_0 /\ y0 = x.
Proof.
simpl in |- *.
intros.
generalize (degreee_invol_nofixpt m x H H0).
generalize (invol_inverse m zero x H H0).
generalize (degreee_fixpt m x H H0).
assert (degreee m x <> 1).
  lia.
 tauto.
Qed.

(* OK: *)

Lemma Poly_diff_vertex: forall(m:fmap)(x:dart),
 inv_hmap m -> exd m x -> 2 <= degreev m x -> 
  let x1 := cA m one x in
  let x_1:= cA_1 m one x in
  x <> x1 /\ x <> x_1.
Proof.
intros.
assert (degreev m x <> 1).
  lia.
assert (x <> cA m one x).
 generalize (degreev_fixpt m x H H0).
   intros.
   intro.
   symmetry  in H4.
    tauto.
split.
  tauto.
intro.
  elim H3.
  clear H3.
  rewrite H4 in |- *.
  unfold x_1 in |- *.
  rewrite cA_cA_1 in |- *.
 fold x_1 in |- *.
   symmetry  in |- *.
    tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma Tri_diff_face: forall(m:fmap)(x:dart),
  inv_hmap m -> exd m x -> isTri m x -> 
  let xf := cF m x in
  let xff:= cF m xf in
  x <> xf /\ x <> xff /\ xf <> xff.
Proof.
simpl in |- *.
intros.
unfold isTri in H1.
assert (degreef m x = 3).
  tauto.
clear H1.
  assert (x = Iter (cF m) 0 x).
 simpl in |- *.
    tauto.
assert (cF m (cF m x) = Iter (cF m) 2 x).
 simpl in |- *.
    tauto.
assert (cF m x = Iter (cF m) 1 x).
 simpl in |- *.
    tauto.
assert (MF0Tr.MfM.degree = degreef).
  tauto.
assert (MF.degree = MF0Tr.MfM.degree).
  tauto.
unfold degreef in H2.
  rewrite <- H6 in H2.
  split.
 intro.
   assert (0 = 1).
  apply (MF.degree_unicity m x 0 1 H H0).
    lia.
   lia.
  simpl in |- *.
     tauto.
 inversion H8.
 split.
 intro.
   assert (0 = 2).
  apply (MF.degree_unicity m x 0 2 H H0).
    lia.
   lia.
  simpl in |- *.
     tauto.
 inversion H8.
 intro.
   assert (1 = 2).
  apply (MF.degree_unicity m x 1 2 H H0).
    lia.
   lia.
  simpl in |- *.
     tauto.
 inversion H8.
Qed.

(* OK: *)

Lemma Tri_diff_2faces: forall(m:fmap)(x y:dart),
 inv_hmap m -> exd m x -> exd m y -> 
   isTri m x -> isTri m y ->
     ~ expf m x y ->
  let xf := cF m x in
  let xff:= cF m xf in
  let yf := cF m y in
  let yff := cF m yf in
  (x <> y /\ x <> yf /\ x <> yff) /\
  (xf <> y /\ xf <> yf /\ xf <> yff) /\
  (xff <> y /\ xff <> yf /\ xff <> yff).
Proof.
intros.
assert (x <> xf /\ x <> xff /\ xf <> xff).
 unfold xff in |- *.
   unfold xf in |- *.
   apply (Tri_diff_face m x H H0 H2).
assert (y <> yf /\ y <> yff /\ yf <> yff).
 unfold yff in |- *.
   unfold yf in |- *.
   apply (Tri_diff_face m y H H1 H3).
assert (expf m x xf).
 unfold xf in |- *.
   unfold expf in |- *.
   split.
   tauto.
 unfold MF.expo in |- *.
   split.
   tauto.
 split with 1.
   simpl in |- *.
    tauto.
assert (expf m x xff).
 unfold xff in |- *.
   unfold xf in |- *.
   unfold expf in |- *.
   split.
   tauto.
 unfold MF.expo in |- *.
   split.
   tauto.
 split with 2.
   simpl in |- *.
    tauto.
assert (expf m y yf).
 unfold yf in |- *.
   unfold expf in |- *.
   split.
   tauto.
 unfold MF.expo in |- *.
   split.
   tauto.
 split with 1.
   simpl in |- *.
    tauto.
assert (expf m y yff).
 unfold yff in |- *.
   unfold yf in |- *.
   unfold expf in |- *.
   split.
   tauto.
 unfold MF.expo in |- *.
   split.
   tauto.
 split with 2.
   simpl in |- *.
    tauto.
split.
 split.
  intro.
    elim H4.
    rewrite H11 in |- *.
    apply expf_refl.
    tauto.
   tauto.
 split.
  intro.
    elim H4.
    rewrite H11 in |- *.
    apply expf_symm.
     tauto.
 intro.
   elim H4.
   rewrite H11 in |- *.
   apply expf_symm.
    tauto.
split.
 split.
  intro.
    elim H4.
    rewrite <- H11 in |- *.
     tauto.
 split.
  intro.
    elim H4.
    apply expf_trans with xf.
    tauto.
  rewrite H11 in |- *.
    apply expf_symm.
     tauto.
 intro.
   elim H4.
   apply expf_trans with xf.
   tauto.
 rewrite H11 in |- *.
   apply expf_symm.
    tauto.
split.
 intro.
   elim H4.
   rewrite <- H11 in |- *.
    tauto.
split.
 intro.
   elim H4.
   apply expf_trans with xff.
   tauto.
 rewrite H11 in |- *.
   apply expf_symm.
    tauto.
intro.
  elim H4.
  apply expf_trans with xff.
  tauto.
rewrite H11 in |- *.
  apply expf_symm.
   tauto.
Qed.

(* OK: *)

Lemma Hexa_diff_face: forall(m:fmap)(x:dart),
  inv_hmap m -> exd m x -> isHexa m x -> 
  let xf1  := cF m x in
  let xf2 := cF m xf1 in
  let xf3 := cF m xf2 in
  let xf4 := cF m xf3 in
  let xf5 := cF m xf4 in
  x <> xf1 /\ x <> xf2 /\ x <> xf3 /\ 
     x <> xf4 /\ x <> xf5 /\ 
  xf1 <> xf2 /\ xf1 <> xf3 /\ xf1 <> xf4 /\ 
     xf1 <> xf5 /\
  xf2 <> xf3 /\ xf2 <> xf4 /\ xf2 <> xf5 /\ 
  xf3 <> xf4 /\ xf3 <> xf5 /\ 
  xf4 <> xf5.
Proof.
intros.
unfold isHexa in H1.
assert (x = Iter (cF m) 0 x).
 simpl in |- *.
    tauto.
assert (xf1 = Iter (cF m) 1 x).
 simpl in |- *.
   fold xf1 in |- *.
    tauto.
assert (xf2 = Iter (cF m) 2 x).
 simpl in |- *.
   fold xf1 in |- *.
   fold xf2 in |- *.
    tauto.
assert (xf3 = Iter (cF m) 3 x).
 simpl in |- *; fold xf1 in |- *; fold xf2 in |- *.
   fold xf3 in |- *.
    tauto.
assert (xf4 = Iter (cF m) 4 x).
 simpl in |- *.
   fold xf1 in |- *; fold xf2 in |- *;
    fold xf3 in |- *; fold xf4 in |- *.
      tauto.
assert (xf5 = Iter (cF m) 5 x).
 simpl in |- *.
   fold xf1 in |- *; fold xf2 in |- *; 
    fold xf3 in |- *; fold xf4 in |- *;
     fold xf5 in |- *.
       tauto.
assert (MF0Tr.MfM.degree = degreef).
  tauto.
assert (MF.degree = MF0Tr.MfM.degree).
  tauto.
unfold degreef in H1.
  rewrite <- H9 in H1.
assert (MF.f = cF).
  tauto.
split.
 intro.
   assert (0 = 1).
  apply (MF.degree_unicity m x 0 1 H H0).
    lia.
   lia.
  simpl in |- *.
     tauto.
 inversion H12.
split.
 intro.
   assert (0 = 2).
  apply (MF.degree_unicity m x 0 2 H H0).
    lia.
   lia.
  simpl in |- *.
    rewrite H10 in |- *.
    fold xf1 in |- *; fold xf2 in |- *.
     tauto.
 inversion H12.
split.
 intro.
   assert (0 = 3).
  apply (MF.degree_unicity m x 0 3 H H0).
    lia.
   lia.
  simpl in |- *.
    rewrite H10 in |- *.
    fold xf1 in |- *; fold xf2 in |- *; fold xf3.
     tauto.
 inversion H12.
split.
 intro.
   assert (0 = 4).
  apply (MF.degree_unicity m x 0 4 H H0).
    lia.
   lia.
  simpl in |- *.
    rewrite H10 in |- *.
    fold xf1 in |- *; fold xf2 in |- *; fold xf3;
fold xf4.
     tauto.
 inversion H12.
split.
 intro.
   assert (0 = 5).
  apply (MF.degree_unicity m x 0 5 H H0).
    lia.
   lia.
  simpl in |- *.
    rewrite H10 in |- *.
    fold xf1 in |- *; fold xf2 in |- *; fold xf3;
fold xf4; fold xf5.
     tauto.
 inversion H12.
split.
 intro.
   assert (1 = 2).
  apply (MF.degree_unicity m x 1 2 H H0).
    lia.
   lia.
  simpl in |- *.
    rewrite H10 in |- *.
    fold xf1 in |- *; fold xf2 in |- *.
     tauto.
 inversion H12.
split.
 intro.
   assert (1 = 3).
  apply (MF.degree_unicity m x 1 3 H H0).
    lia.
   lia.
  simpl in |- *.
    rewrite H10 in |- *.
    fold xf1 in |- *; fold xf2 in |- *; fold xf3.
     tauto.
 inversion H12.
split.
 intro.
   assert (1 = 4).
  apply (MF.degree_unicity m x 1 4 H H0).
    lia.
   lia.
  simpl in |- *.
    rewrite H10 in |- *.
    fold xf1 in |- *; fold xf2 in |- *; fold xf3;
   fold xf4.
     tauto.
 inversion H12.
split.
 intro.
   assert (1 = 5).
  apply (MF.degree_unicity m x 1 5 H H0).
    lia.
   lia.
  simpl in |- *.
    rewrite H10 in |- *.
    fold xf1 in |- *; fold xf2 in |- *; fold xf3;
   fold xf4; fold xf5.
     tauto.
 inversion H12.
split.
 intro.
   assert (2 = 3).
  apply (MF.degree_unicity m x 2 3 H H0).
    lia.
   lia.
  simpl in |- *.
    rewrite H10 in |- *.
    fold xf1 in |- *; fold xf2 in |- *; fold xf3.
     tauto.
 inversion H12.
split.
 intro.
   assert (2 = 4).
  apply (MF.degree_unicity m x 2 4 H H0).
    lia.
   lia.
  simpl in |- *.
    rewrite H10 in |- *.
    fold xf1 in |- *; fold xf2 in |- *; fold xf3; 
 fold xf4.
     tauto.
inversion H12.
split.
 intro.
   assert (2 = 5).
  apply (MF.degree_unicity m x 2 5 H H0).
    lia.
   lia.
  simpl in |- *.
    rewrite H10 in |- *.
    fold xf1 in |- *; fold xf2 in |- *; fold xf3; 
 fold xf4; fold xf5.
     tauto.
inversion H12.
split.
 intro.
   assert (3 = 4).
  apply (MF.degree_unicity m x 3 4 H H0).
    lia.
   lia.
  simpl in |- *.
    rewrite H10 in |- *.
    fold xf1 in |- *; fold xf2 in |- *; fold xf3; 
 fold xf4.
     tauto.
inversion H12.
split.
 intro.
   assert (3 = 5).
  apply (MF.degree_unicity m x 3 5 H H0).
    lia.
   lia.
  simpl in |- *.
    rewrite H10 in |- *.
    fold xf1 in |- *; fold xf2 in |- *; fold xf3; 
 fold xf4; fold xf5.
     tauto.
inversion H12.
 intro.
   assert (4 = 5).
  apply (MF.degree_unicity m x 4 5 H H0).
    lia.
   lia.
  simpl in |- *.
    rewrite H10 in |- *.
    fold xf1 in |- *; fold xf2 in |- *; fold xf3; 
 fold xf4; fold xf5.
     tauto.
inversion H12.
Qed.

(* -- cA0, degreee -- *)

(* OK: *)

Lemma cA0_Flip1: forall(m:fmap)(x:dart)(z:dart),
 inv_hmap m -> exd m x -> exd m z ->
  let x_1 := cA_1 m one x in
  let m1 := Split m one x x_1 in
  cA m1 zero z = cA m zero z.
Proof.
intros.
unfold m1 in |- *.
rewrite MA1.cA_Split_opp in |- *.
 simpl in |- *.
    tauto.
 tauto.
Qed.

(* OK, IDEM: *)

Lemma cA0_1_Flip1: forall(m:fmap)(x:dart)(z:dart),
 inv_hmap m -> exd m x -> exd m z ->
  let x_1 := cA_1 m one x in
  let m1 := Split m one x x_1 in
  cA_1 m1 zero z = cA_1 m zero z.
Proof.
intros.
unfold m1 in |- *.
rewrite MA1.cA_1_Split_opp in |- *.
 simpl in |- *.
    tauto.
 tauto.
Qed.

(* NEW, OK: *)

Lemma degreee_Flip1_aux:    forall(m:fmap)(x:dart)(z:dart),
 inv_hmap m -> exd m x -> exd m z ->
  let x_1 := cA_1 m one x in
  let m1 := Split m one x x_1 in
 degreee m1 z = degreee m z.
Proof.
intros.
unfold m1 in |- *.
apply degreee_Split1_summary.
  tauto.
 tauto.
Qed.

(* OK: WITH NUMBERS *)

Lemma degreee_Flip1:
forall(m:fmap)(x:dart)(z:dart), 
 inv_hmap m -> isMap m -> 
   exd m x -> exd m z ->
  let x_1 := cA_1 m one x in
  let m1 := Split m one x x_1 in
 degreee m1 z = 2.
Proof.
unfold isMap in |- *.
intros.
decompose [and] H.
rewrite (degreee_Flip1_aux m x z H H1) in |- *.
 apply (H0 z H2).
 tauto.
Qed.

(* -- DIMENSION 1 -- *)

Lemma cA1_Flip1: forall(m:fmap)(x:dart)(z:dart), 
  inv_hmap m -> 2 <= degreev m x -> 
  exd m x -> exd m z ->
  let x_1 := cA_1 m one x in
  let x1 := cA m one x in 
  let m1 := Split m one x x_1 in
    cA m1 one z = 
      if eq_dart_dec x z then x
      else if eq_dart_dec x_1 z then x1
           else cA m one z.
Proof.
intros.
unfold m1 in |- *.
rewrite MA1.cA_Split in |- *.
 unfold x_1 in |- *.
   rewrite cA_cA_1 in |- *.
  fold x_1 in |- *.
     tauto.
  tauto.
  tauto.
 tauto.
apply (degreev_crackv m x H H1 H0).
Qed.

(* OK:*)

Lemma cA1_1_Flip1: forall(m:fmap)(x:dart)(z:dart),
 inv_hmap m -> 2 <= degreev m x ->
 exd m x -> exd m z ->
  let x_1 := cA_1 m one x in
  let x1 := cA m one x in 
  let m1 := Split m one x x_1 in
    cA_1 m1 one z = 
      if eq_dart_dec x1 z then x_1
      else if eq_dart_dec x z then x
           else cA_1 m one z.
Proof.
intros.
unfold m1 in |- *.
rewrite MA1.cA_1_Split in |- *.
 unfold x_1 in |- *.
   rewrite cA_cA_1 in |- *.
  unfold x1 in |- *.
     tauto.
  tauto.
  tauto.
 tauto.
apply (degreev_crackv m x H H1 H0).
Qed.

(* OK: *)

Lemma degreev_Flip1: 
forall(m:fmap)(x:dart)(z:dart)(H:inv_hmap m),
 exd m x -> exd m z ->
  let x_1 := cA_1 m one x in
  let m1 := Split m one x x_1 in
 2 <= degreev m x ->
  degreev m1 z =
    if eq_dart_dec x z then 1
    else if expv_dec m x_1 z H 
          then degreev m x - 1
          else degreev m z.
Proof.
intros.
assert (exd m x_1).
 unfold x_1 in |- *.
   generalize (exd_cA_1 m one x).
    tauto.
assert (crackv m x x_1).
 apply (degreev_crackv m x H H0 H2).
assert (x = cA m one x_1).
 unfold x_1 in |- *.
   rewrite cA_cA_1 in |- *.
   tauto.
  tauto.
  tauto.
set (dx := degreev m x) in |- *.
  assert (x = Iter (cA m one) dx x).
 unfold dx in |- *.
   rewrite <- MA1Tr_cA1_Iter in |- *.
   unfold degreev in |- *.
   rewrite MA1Tr.MfM.degree_per in |- *.
   tauto.
  tauto.
  tauto.
assert (2 <= dx <= degreev m x).
 unfold dx in |- *.
    lia.
assert (cA m one x_1 = Iter (cA m one) dx x).
 rewrite <- H5 in |- *.
    tauto.
rewrite H5 in H7.
  generalize
   (degreev_Split1_summary_bis m x x_1 z 
      (degreev m x) H H4 H1 H8 H7).
  fold m1 in |- *.
  rewrite <- H5 in |- *.
  set (x1 := cA m one x) in |- *.
  intros.
  decompose [and] H9.
  clear H9.
  assert (expv m x x).
 apply expv_refl.
    tauto.
elim (expv_dec m x z H).
 intro.
   assert (MA1.MfcA.expo1 m x x).
  unfold expv in H9.
    generalize (MA1.MfcA.expo_expo1 m x x).
     tauto.
 assert (MA1.MfcA.expo1 m x z).
  generalize (MA1.MfcA.expo_expo1 m x z).
     tauto.
 assert (betweenv m x z x \/ betweenv m x1 z x_1).
  unfold x1 in |- *.
    unfold x_1 in |- *.
    apply (MA1.MfcA.expo_between_3 m x x z H H11 H14).
 assert (x = z <-> betweenv m x z x).
  split.
   intro.
     rewrite <- H16 in |- *.
     unfold betweenv in |- *.
     generalize (MA1.MfcA.between_expo_refl_1 m x x).
      tauto.
  intro.
    unfold betweenv in H16.
    unfold MA1.MfcA.between in H16.
    elim H16.
   intros i Hi.
     clear H16.
     elim Hi.
     clear Hi.
     intros j Hj.
     decompose [and] Hj.
     clear Hj.
     assert (j = 0).
    apply (MA1.MfcA.unicity_mod_p m x j 0 H H0).
      tauto.
     lia.
    simpl in |- *.
       tauto.
   assert (i = 0).
     lia.
   rewrite H21 in H16.
     simpl in H16.
      tauto.
   tauto.
   tauto.
 elim (eq_dart_dec x z).
  intro.
    rewrite H10 in |- *.
   clear a0 H16 H8 H6.
    lia.
   tauto.
 intro.
   elim (expv_dec m x_1 z H).
  intro.
    unfold dx in |- *.
    apply H12.
     tauto.
 intro.
   apply H13.
   intro.
   elim b0.
   apply MA1.MfcA.expo_trans with x.
  apply MA1.MfcA.expo_symm.
    tauto.
  unfold crackv in H4.
    unfold MA1.crack in H4.
     tauto.
  tauto.
intro.
  elim (eq_dart_dec x z).
 intro.
   elim b.
   rewrite <- a in |- *.
   apply MA1.MfcA.expo_refl.
    tauto.
elim (expv_dec m x_1 z).
 intros.
   elim b.
   apply MA1.MfcA.expo_trans with x_1.
  unfold crackv in H4.
    unfold MA1.crack in H4.
     tauto.
  tauto.
intros.
  apply H13.
  unfold expv in |- *.
   tauto.
Qed.

(* -- FACES -- *)

(* OK: *)

Lemma cF_Flip1: 
forall(m:fmap)(x:dart)(z:dart),
 inv_hmap m -> 2 <= degreev m x -> 
 exd m x -> exd m z ->
  let x_1 := cA_1 m one x in
  let y := cA m zero x in
  let x_f := cF_1 m x in 
  let m1 := Split m one x x_1 in
    cF m1 z = 
      if eq_dart_dec x_f z then x_1
      else if eq_dart_dec y z then x
           else cF m z.
Proof.
intros.
unfold m1 in |- *.
rewrite cF_Split1 in |- *.
 fold x_f in |- *.
   unfold x_1 in |- *.
   unfold cF_1 in |- *.
   rewrite cA_cA_1 in |- *.
  fold y in |- *.
     tauto.
  tauto.
  tauto.
 tauto.
apply (degreev_crackv m x H H1 H0).
 tauto.
Qed.

(* OK: *)

Lemma cF_1_Flip1: 
forall(m:fmap)(x:dart)(z:dart),
 inv_hmap m -> 2 <= degreev m x -> 
 exd m x -> exd m z ->
  let x_1 := cA_1 m one x in
  let y := cA m zero x in
  let x_f := cF_1 m x in 
  let m1 := Split m one x x_1 in
    cF_1 m1 z = 
      if eq_dart_dec x_1 z then x_f
      else if eq_dart_dec x z then y
           else cF_1 m z.
Proof.
intros.
unfold m1 in |- *.
rewrite cF_1_Split1 in |- *.
 fold x_f in |- *.
   unfold x_1 in |- *.
   unfold cF_1 in |- *.
   rewrite cA_cA_1 in |- *.
  fold y in |- *.
     tauto.
  tauto.
  tauto.
 tauto.
apply (degreev_crackv m x H H1 H0).
 tauto.
Qed.

(* degreef: *)

Lemma degreef_Flip1_aux:
 forall(m:fmap)(x z:dart)(H:inv_hmap m),
 exd m x -> exd m z ->
  let y := cA m zero x in
  let x_1 := cA_1 m one x in
  let m1 := Split m one x x_1 in
 x <> x_1 -> ~ expf m x y ->
  degreef m1 z = 
     if expf_dec m x z 
     then degreef m x + degreef m x_1
     else if expf_dec m x_1 z 
           then degreef m x + degreef m x_1
           else degreef m z.
Proof.
intros.
rename H3 into Nex.
assert (exd m x_1).
 unfold x_1 in |- *.
   generalize (exd_cA_1 m one x).
    tauto.
assert (crackv m x x_1).
 unfold crackv in |- *.
   unfold MA1.crack in |- *.
   split.
   tauto.
 apply MA1.MfcA.expo_symm.
   tauto.
 unfold MA1.MfcA.expo in |- *.
   split.
   tauto.
 split with 1.
   simpl in |- *.
   assert (MA1.MfcA.f m x_1 = cA m one x_1).
   tauto.
 rewrite H4 in |- *.
   unfold x_1 in |- *.
   rewrite cA_cA_1 in |- *.
   tauto.
  tauto.
  tauto.
assert (expf m (cF_1 m x) x).
 unfold expf in |- *.
   split.
   tauto.
 unfold MF.expo in |- *.
   split.
  generalize (exd_cF_1 m x).
     tauto.
 split with 1.
   simpl in |- *.
   rewrite cF_cF_1 in |- *.
   tauto.
  tauto.
  tauto.
assert (degreef m (cF_1 m x) = degreef m x).
 unfold degreef in |- *.
   apply MF0Tr.MfM.expo_degree.
   tauto.
 unfold expf in H5.
    tauto.
assert (x_1 = cF m y).
 unfold cF in |- *.
   unfold y in |- *.
   rewrite cA_1_cA in |- *.
  fold x_1 in |- *.
     tauto.
  tauto.
  tauto.
assert (~ expof m (cF_1 m x) x_1).
 intro.
   elim Nex.
   apply expf_symm.
   apply expf_trans with x_1.
  rewrite H7 in |- *.
    unfold expf in |- *.
    split.
    tauto.
  unfold MF.expo in |- *.
    split.
   unfold y in |- *.
     generalize (exd_cA m zero x).
      tauto.
  split with 1.
    simpl in |- *.
     tauto.
 apply expf_trans with (cF_1 m x).
  apply expf_symm.
    unfold expf in |- *.
     tauto.
  tauto.
generalize (degreef_Split1_merge_summary m x x_1 z H H4 H1 H8).
  fold m1 in |- *.
  rewrite H6 in |- *.
  elim (expof_dec m (cF_1 m x) z H).
 elim (expf_dec m x z).
   tauto.
 intros.
   elim (expf_dec m x_1 z).
   tauto.
 intro.
   elim b.
   apply expf_trans with (cF_1 m x).
  apply expf_symm.
     tauto.
 unfold expf in |- *.
    tauto.
elim (expf_dec m x z).
 elim (expof_dec m x_1 z H).
   tauto.
 intros.
   elim b0.
   apply expof_trans with x.
  unfold expf in H5.
     tauto.
 unfold expf in a.
    tauto.
elim (expof_dec m x_1 z H).
 elim (expf_dec m x_1 z).
   tauto.
 unfold expf in |- *.
    tauto.
elim (expf_dec m x_1 z).
 unfold expf in |- *.
    tauto.
 tauto.
Qed.

(* OK, WITH NUMBERS: *)

Lemma degreef_Flip1:
 forall(m:fmap)(x z:dart)(H:inv_hmap m),
 exd m x -> exd m z ->
  let y := cA m zero x in
  let x_1 := cA_1 m one x in
  let m1 := Split m one x x_1 in
 x <> x_1 -> ~ expf m x y -> 
  isTri m x -> isTri m y ->
   degreef m1 z = 
     if expf_dec m x z then 6
     else if expf_dec m x_1 z then 6
           else degreef m z.
Proof.
intros.
unfold isTri in H4.
unfold isTri in H5.
assert (x_1 = cF m y).
 unfold y in |- *.
   unfold cF in |- *.
   rewrite cA_1_cA in |- *.
  fold x_1 in |- *.
     tauto.
  tauto.
  tauto.
assert (degreef m y = degreef m x_1).
 rewrite H6 in |- *.
   unfold degreef in |- *.
   apply MF0Tr.MfM.expo_degree.
   tauto.
 unfold MF0Tr.MfM.expo in |- *.
   split.
  unfold y in |- *.
    generalize (exd_cA m zero x).
     tauto.
 split with 1.
   simpl in |- *.
    tauto.
unfold m1 in |- *.
  unfold x_1 in |- *.
  rewrite (degreef_Flip1_aux m x z H H0 H1 H2 H3)
      in |- *.
  fold x_1 in |- *.
  rewrite <- H7 in |- *.
  rewrite H4 in |- *.
  rewrite H5 in |- *.
  assert (3 + 3 = 6).
  lia.
rewrite H8 in |- *.
   tauto.
Qed.

(* OK: THE FACE OF x IN m1 IS AN HEXAGON: *)

Theorem isHexa_Flip1: forall(m:fmap)(x:dart),
 inv_hmap m -> exd m x -> 
  let y := cA m zero x in
  let x_1 := cA_1 m one x in
  let m1 := Split m one x x_1 in
 x <> x_1 -> ~ expf m x y -> 
   isTri m x -> isTri m y ->
      isHexa m1 x.
Proof.
intros.
generalize (degreef_Flip1 m x x H H0 H0 H1 H2 H3 H4).
fold x_1 in |- *.
fold m1 in |- *.
unfold isHexa in |- *.
elim (expf_dec m x x).
  tauto.
intro.
  elim b.
  apply expf_refl.
  tauto.
 tauto.
Qed.

(* THE OTHER FACES IN m1 ARE ALWAYS TRIANGULAR:  *)

Theorem isTri_Flip1: forall(m:fmap)(x z:dart),
 inv_hmap m -> isTriangulation m ->
 exd m x -> exd m z ->
  let y := cA m zero x in
  let x_1 := cA_1 m one x in
  let m1 := Split m one x x_1 in
 x <> x_1 -> ~ expf m x y -> 
     ~ expf m1 x z -> isTri m1 z.
Proof.
intros.
unfold isTriangulation in H0.
generalize (H0 z H2).
intro Tz.
generalize (H0 x H1).
intro Tx.
assert (exd m y).
 unfold y in |- *.
   generalize (exd_cA m zero x).
    tauto.
generalize (H0 y H6).
  intro Ty.
  generalize (degreef_Flip1 m x z H H1 H2 H3 H4 Tx Ty).
  fold x_1 in |- *.
  fold m1 in |- *.
  unfold isTri in |- *.
  assert (inv_hmap m1).
 unfold m1 in |- *.
   apply inv_hmap_Split.
    tauto.
assert (exd m1 x).
 unfold m1 in |- *.
   generalize (exd_Split m one x x_1 x).
    tauto.
assert (exd m x_1).
 unfold x_1 in |- *.
   generalize (exd_cA_1 m one x).
    tauto.
assert (crackv m x x_1).
 unfold crackv in |- *.
   unfold MA1.crack in |- *.
   split.
   tauto.
 apply MA1.MfcA.expo_symm.
   tauto.
 unfold MA1.MfcA.expo in |- *.
   split.
   tauto.
 split with 1.
   simpl in |- *.
   unfold x_1 in |- *.
   assert (MA1.MfcA.f m (cA_1 m one x) = 
      cA m one (cA_1 m one x)).
   tauto.
 rewrite cA_cA_1 in H10.
   tauto.
  tauto.
  tauto.
generalize (expof_Split1_CNS m x x_1 x z H H10 H1).
  simpl in |- *.
  fold m1 in |- *.
  intros.
  assert (x_1 = cF m y).
 unfold cF in |- *.
   unfold y in |- *.
   rewrite cA_1_cA in |- *.
  fold x_1 in |- *.
     tauto.
  tauto.
  tauto.
assert (expf m (cF_1 m x) x).
 unfold expf in |- *.
   split.
   tauto.
 unfold MF.expo in |- *.
   split.
  generalize (exd_cF_1 m x).
     tauto.
 split with 1.
   simpl in |- *.
   rewrite cF_cF_1 in |- *.
   tauto.
  tauto.
  tauto.
assert (~ expf m (cF_1 m x) x_1).
 intro.
   elim H4.
   apply expf_trans with (cF_1 m x).
  apply expf_symm.
     tauto.
 apply expf_trans with x_1.
   tauto.
 apply expf_symm.
   unfold expf in |- *.
   split.
   tauto.
 unfold MF.expo in |- *.
   split.
   tauto.
 rewrite H13 in |- *.
   split with 1.
   simpl in |- *.
    tauto.
generalize H11; clear H11.
  elim (expof_dec m (cF_1 m x) x_1 H).
 unfold expof in |- *.
   unfold expf in H15.
    tauto.
intros.
  clear H15.
  assert
   (~
    (expof m x z \/
     expof m (cF_1 m x) x /\ expof m x_1 z \/
     expof m (cF_1 m x) z /\ expof m x_1 x)).
 unfold expf in H6.
   unfold expf in H5.
    tauto.
clear H11.
  generalize H12; clear H12.
  elim (expf_dec m x z).
 unfold expf in |- *.
    tauto.
elim (expf_dec m x_1 z).
 unfold expf in |- *.
   intros.
   unfold expf in H14.
    tauto.
intros.
  rewrite H12 in |- *.
  unfold isTri in Tz.
   tauto.
Qed.

(* OK: *)

Lemma isMap_Flip1: forall(m:fmap)(x:dart),
 inv_hmap m -> isMap m -> exd m x -> 
   let x_1 := cA_1 m one x in
   let m1 := Split m one x x_1 in
      isMap m1.
Proof.
intros.
unfold isMap in |- *.
intros.
unfold m1 in |- *.
unfold x_1 in |- *.
rewrite degreee_Flip1 in |- *.
  tauto.
 tauto.
 tauto.
 tauto.
generalize (exd_Split m one x x_1 z).
  fold m1 in |- *.
   tauto.
Qed.

(* OK: *)

Lemma cF_Flip1_detail:
forall(m:fmap)(x:dart)(z:dart),
inv_hmap m -> isMap m -> 
 exd m x -> exd m z ->
  let x_1 := cA_1 m one x in
  let y := cA m zero x in
  let y_1:= cA_1 m one y in
  let xff:= cF m y_1 in
  let yff:= cF m x_1 in
  let m1 := Split m one x x_1 in
 2 <= degreev m x -> 2 <= degreev m y -> 
  ~ expv m x y -> ~ expf m x y -> 
    isTri m x -> isTri m y -> 
  (cF m1 y = x /\
   cF m1 x = y_1 /\
   cF m1 y_1 = xff /\
   cF m1 xff = x_1 /\
   cF m1 x_1 = yff /\
   cF m1 yff = y /\
  (x <> z -> y <> z -> y_1 <> z -> 
     xff <> z -> x_1 <> z -> yff <> z -> 
       cF m1 z = cF m z)).
Proof.
intros.
assert (degreee m x = 2).
 unfold isMap in H0.
   apply (H0 x H1).
assert (exd m y).
 unfold y in |- *.
   generalize (exd_cA m zero x).
    tauto.
simpl in |- *.
  fold y in |- *.
  intros.
  generalize (Poly_diff_vertex m x H H1 H3).
  simpl in |- *.
  fold x_1 in |- *.
  set (x1 := cA m one x) in |- *.
  intro.
  generalize (Poly_diff_vertex m y H H10 H4).
  simpl in |- *.
  fold y_1 in |- *.
  set (y1 := cA m one y) in |- *.
  intro.
  generalize (Tri_diff_face m x H H1 H7).
  simpl in |- *.
  intros.
  assert (y_1 = cF m x).
 unfold y_1 in |- *.
   unfold isMap in H0.
   generalize (H0 x H1).
   intro.
   generalize (degreee_invol_nofixpt m x H H1).
   intro.
   generalize (invol_inverse m zero x H H1).
   fold y in |- *.
   intros.
   assert (y = cA_1 m zero x).
  fold y in H15.
     tauto.
 rewrite H17 in |- *.
   fold (cF m x) in |- *.
    tauto.
rewrite <- H14 in H13.
  fold xff in H13.
  generalize (Tri_diff_face m y H H10 H8).
  simpl in |- *.
  assert (x_1 = cF m y).
 unfold x_1 in |- *.
   assert (x = cA_1 m zero y).
  unfold y in |- *.
    rewrite cA_1_cA in |- *.
    tauto.
   tauto.
   tauto.
 rewrite H15 in |- *.
   fold (cF m y) in |- *.
    tauto.
rewrite <- H15 in |- *.
  intro.
  generalize (Tri_diff_2faces m x y H H1 H10 H7 H8 H6).
  simpl in |- *.
  rewrite <- H14 in |- *.
  rewrite <- H15 in |- *.
  intros.
  assert (xff = cF_1 m x).
 unfold xff in |- *.
   rewrite H14 in |- *.
   assert (Iter (cF m) 3 x = x).
  unfold isTri in H7.
    rewrite <- H7 in |- *.
    unfold degreef in |- *.
    assert (cF = MF0Tr.MfM.f).
    tauto.
  rewrite H18 in |- *.
    apply MF0Tr.MfM.degree_per.
    tauto.
   tauto.
 simpl in H18.
   rewrite <- H18 in |- *.
   rewrite cF_1_cF in |- *.
  rewrite H18 in |- *.
     tauto.
  tauto.
 generalize (exd_cF m x).
   generalize (exd_cF m (cF m x)).
    tauto.
assert (yff = cF_1 m y).
 unfold yff in |- *.
   rewrite H15 in |- *.
   assert (Iter (cF m) 3 y = y).
  unfold isTri in H8.
    rewrite <- H8 in |- *.
    unfold degreef in |- *.
    assert (cF = MF0Tr.MfM.f).
    tauto.
  rewrite H19 in |- *.
    apply MF0Tr.MfM.degree_per.
    tauto.
   tauto.
 simpl in H19.
   rewrite <- H19 in |- *.
   rewrite cF_1_cF in |- *.
  rewrite H19 in |- *.
     tauto.
  tauto.
 generalize (exd_cF m y).
   generalize (exd_cF m (cF m y)).
    tauto.
split.
 unfold m1 in |- *; unfold x_1 in |- *.
   rewrite cF_Flip1 in |- *.
  rewrite <- H18 in |- *.
    fold y in |- *.
    elim (eq_dart_dec xff y).
   fold xff in H17.
     fold yff in H17.
      tauto.
  elim (eq_dart_dec y y).
    tauto.
   tauto.
  tauto.
  tauto.
  tauto.
  tauto.
split.
 unfold m1 in |- *; unfold x_1 in |- *.
   rewrite cF_Flip1 in |- *.
  rewrite <- H18 in |- *.
    fold y in |- *.
    elim (eq_dart_dec xff x).
   intro.
     symmetry  in a.
      tauto.
  elim (eq_dart_dec y x).
   intro.
     symmetry  in a.
      tauto.
  symmetry  in |- *.
     tauto.
  tauto.
  tauto.
  tauto.
  tauto.
split.
 unfold m1 in |- *; unfold x_1 in |- *.
   rewrite cF_Flip1 in |- *.
  rewrite <- H18 in |- *.
    fold y in |- *.
    elim (eq_dart_dec xff y_1).
   unfold xff in |- *.
     intros.
     symmetry  in a.
      tauto.
  elim (eq_dart_dec y y_1).
    tauto.
  unfold xff in |- *.
     tauto.
  tauto.
  tauto.
  tauto.
 unfold y_1 in |- *.
   generalize (exd_cA_1 m one y).
    tauto.
split.
 unfold m1 in |- *; unfold x_1 in |- *.
   rewrite cF_Flip1 in |- *.
  rewrite <- H18 in |- *.
    fold y in |- *.
    elim (eq_dart_dec xff xff).
    tauto.
   tauto.
  tauto.
  tauto.
  tauto.
 unfold xff in |- *.
   generalize (exd_cF m y_1).
   generalize (exd_cA_1 m one y).
   fold y_1 in |- *.
    tauto.
split.
 unfold m1 in |- *; unfold x_1 in |- *.
   rewrite cF_Flip1 in |- *.
  rewrite <- H18 in |- *.
    fold y in |- *.
    fold x_1 in |- *.
    elim (eq_dart_dec xff x_1).
   intros.
     unfold xff in a.
      tauto.
  elim (eq_dart_dec y x_1).
    tauto.
  unfold yff in |- *.
     tauto.
  tauto.
  tauto.
  tauto.
 generalize (exd_cA_1 m one x).
    tauto.
split.
 unfold m1 in |- *; unfold x_1 in |- *.
   rewrite cF_Flip1 in |- *.
  rewrite <- H18 in |- *.
    fold y in |- *.
    elim (eq_dart_dec xff yff).
   unfold xff in |- *; unfold yff in |- *.
      tauto.
  elim (eq_dart_dec y yff).
   unfold xff in |- *.
      tauto.
  rewrite H19 in |- *.
    rewrite cF_cF_1 in |- *.
    tauto.
   tauto.
   tauto.
  tauto.
  tauto.
  tauto.
 rewrite H19 in |- *.
   generalize (exd_cF_1 m y).
    tauto.
intros.
  unfold m1 in |- *; unfold x_1 in |- *.
  rewrite cF_Flip1 in |- *.
 elim (eq_dart_dec (cF_1 m x) z).
  rewrite <- H18 in |- *.
     tauto.
 fold y in |- *.
   elim (eq_dart_dec y z).
   tauto.
  tauto.
 tauto.
 tauto.
 tauto.
 tauto.
Qed. 

(* PARTICULAR CASE: OK *)

Lemma cF_Flip1_detail_1:
forall(m:fmap)(x:dart),
inv_hmap m -> isMap m -> exd m x -> 
  let x_1 := cA_1 m one x in
  let y := cA m zero x in
  let y_1:= cA_1 m one y in
  let xff:= cF m y_1 in
  let yff:= cF m x_1 in
  let m1 := Split m one x x_1 in
 2 <= degreev m x -> 2 <= degreev m y -> 
  ~ expv m x y -> ~expf m x y -> 
    isTri m x -> isTri m y -> 
  (cF m1 y = x /\
   cF m1 x = y_1 /\
   cF m1 y_1 = xff /\
   cF m1 xff = x_1 /\
   cF m1 x_1 = yff /\
   cF m1 yff = y).
Proof.
intros.
assert (degreee m x = 2).
 unfold isMap in H0.
   apply (H0 x H1).
assert (exd m y).
 unfold y in |- *.
   generalize (exd_cA m zero x).
    tauto.
simpl in |- *.
  fold y in |- *.
  intros.
  generalize (Poly_diff_vertex m x H H1 H2).
  simpl in |- *.
  fold x_1 in |- *.
  set (x1 := cA m one x) in |- *.
  intro.
  generalize (Poly_diff_vertex m y H H9 H3).
  simpl in |- *.
  fold y_1 in |- *.
  set (y1 := cA m one y) in |- *.
  intro.
  generalize (Tri_diff_face m x H H1 H6).
  simpl in |- *.
  intros.
  assert (y_1 = cF m x).
 unfold y_1 in |- *.
   unfold isMap in H0.
   generalize (H0 x H1).
   intro.
   generalize (degreee_invol_nofixpt m x H H1).
   intro.
   generalize (invol_inverse m zero x H H1).
   fold y in |- *.
   intros.
   assert (y = cA_1 m zero x).
  fold y in H15.
     tauto.
 rewrite H16 in |- *.
   fold (cF m x) in |- *.
    tauto.
rewrite <- H13 in H12.
  fold yff in H12.
  generalize (Tri_diff_face m y H H9 H7).
  simpl in |- *.
  assert (x_1 = cF m y).
 unfold x_1 in |- *.
   assert (x = cA_1 m zero y).
  unfold y in |- *.
    rewrite cA_1_cA in |- *.
    tauto.
   tauto.
   tauto.
 rewrite H14 in |- *.
   fold (cF m y) in |- *.
    tauto.
rewrite <- H14 in |- *.
  intro.
  generalize (Tri_diff_2faces m x y H H1 H9 H6 H7 H5).
  simpl in |- *.
  rewrite <- H13 in |- *.
  rewrite <- H14 in |- *.
  intros.
  assert (xff = cF_1 m x).
 unfold xff in |- *.
   rewrite H13 in |- *.
   assert (Iter (cF m) 3 x = x).
  unfold isTri in H6.
    rewrite <- H6 in |- *.
    unfold degreef in |- *.
    assert (cF = MF0Tr.MfM.f).
    tauto.
  rewrite H17 in |- *.
    apply MF0Tr.MfM.degree_per.
    tauto.
   tauto.
 simpl in H17.
   rewrite <- H17 in |- *.
   rewrite cF_1_cF in |- *.
  rewrite H17 in |- *.
     tauto.
  tauto.
 generalize (exd_cF m x).
   generalize (exd_cF m (cF m x)).
    tauto.
assert (yff = cF_1 m y).
 unfold yff in |- *.
   rewrite H14 in |- *.
   assert (Iter (cF m) 3 y = y).
  unfold isTri in H7.
    rewrite <- H7 in |- *.
    unfold degreef in |- *.
    assert (cF = MF0Tr.MfM.f).
    tauto.
  rewrite H18 in |- *.
    apply MF0Tr.MfM.degree_per.
    tauto.
   tauto.
 simpl in H18.
   rewrite <- H18 in |- *.
   rewrite cF_1_cF in |- *.
  rewrite H18 in |- *.
     tauto.
  tauto.
 generalize (exd_cF m y).
   generalize (exd_cF m (cF m y)).
    tauto.
split.
 unfold m1 in |- *; unfold x_1 in |- *.
   rewrite cF_Flip1 in |- *.
  rewrite <- H17 in |- *.
    fold y in |- *.
    elim (eq_dart_dec xff y).
   fold xff in H16.
     fold yff in H16.
      tauto.
  elim (eq_dart_dec y y).
    tauto.
   tauto.
  tauto.
  tauto.
  tauto.
  tauto.
split.
 unfold m1 in |- *; unfold x_1 in |- *.
   rewrite cF_Flip1 in |- *.
  rewrite <- H17 in |- *.
    fold y in |- *.
    elim (eq_dart_dec xff x).
   intro.
     symmetry  in a.
     fold xff in H13.
      tauto.
  elim (eq_dart_dec y x).
   rewrite H13 in |- *.
     intros.
     symmetry  in a.
      tauto.
  symmetry  in |- *.
     tauto.
  tauto.
  tauto.
  tauto.
  tauto.
split.
 unfold m1 in |- *; unfold x_1 in |- *.
   rewrite cF_Flip1 in |- *.
  rewrite <- H17 in |- *.
    fold y in |- *.
    elim (eq_dart_dec xff y_1).
   unfold xff in |- *.
     intros.
     symmetry  in a.
      tauto.
  elim (eq_dart_dec y y_1).
    tauto.
  unfold xff in |- *.
     tauto.
  tauto.
  tauto.
  tauto.
 unfold y_1 in |- *.
   generalize (exd_cA_1 m one y).
    tauto.
split.
 unfold m1 in |- *; unfold x_1 in |- *.
   rewrite cF_Flip1 in |- *.
  rewrite <- H17 in |- *.
    fold y in |- *.
    elim (eq_dart_dec xff xff).
    tauto.
   tauto.
  tauto.
  tauto.
  tauto.
 unfold xff in |- *.
   generalize (exd_cF m y_1).
   generalize (exd_cA_1 m one y).
   fold y_1 in |- *.
    tauto.
split.
 unfold m1 in |- *; unfold x_1 in |- *.
   rewrite cF_Flip1 in |- *.
  rewrite <- H17 in |- *.
    fold y in |- *.
    fold x_1 in |- *.
    elim (eq_dart_dec xff x_1).
   intros.
     unfold xff in a.
      tauto.
  elim (eq_dart_dec y x_1).
    tauto.
  unfold yff in |- *.
     tauto.
  tauto.
  tauto.
  tauto.
 generalize (exd_cA_1 m one x).
    tauto.
unfold m1 in |- *; unfold x_1 in |- *.
  rewrite cF_Flip1 in |- *.
 rewrite <- H17 in |- *.
   fold y in |- *.
   elim (eq_dart_dec xff yff).
  unfold xff in |- *; unfold yff in |- *.
     tauto.
 elim (eq_dart_dec y yff).
  unfold xff in |- *.
     tauto.
 rewrite H18 in |- *.
   rewrite cF_cF_1 in |- *.
   tauto.
  tauto.
  tauto.
 tauto.
 tauto.
 tauto.
rewrite H18 in |- *.
  generalize (exd_cF_1 m y).
   tauto.
Qed.

(* PARTICULAR CASE: OK *)

Lemma cF_Flip1_detail_2:
forall(m:fmap)(x:dart)(z:dart),
inv_hmap m -> isMap m -> 
 exd m x -> exd m z ->
  let x_1 := cA_1 m one x in
  let y := cA m zero x in
  let y_1:= cA_1 m one y in
  let xff:= cF m y_1 in
  let yff:= cF m x_1 in
  let m1 := Split m one x x_1 in
 2 <= degreev m x -> 2 <= degreev m y -> 
  ~ expv m x y -> ~ expf m x y -> 
    isTri m x -> isTri m y -> 
  x <> z -> y <> z -> y_1 <> z -> 
     xff <> z -> x_1 <> z -> yff <> z -> 
       cF m1 z = cF m z.
Proof.
intros.
assert (degreee m x = 2).
 unfold isMap in H0.
   apply (H0 x H1).
assert (exd m y).
 unfold y in |- *.
   generalize (exd_cA m zero x).
    tauto.
simpl in |- *.
  fold y in |- *.
  intros.
  assert (y_1 = cF m x).
 unfold y_1 in |- *.
   unfold isMap in H0.
   generalize (H0 x H1).
   intro.
   generalize (degreee_invol_nofixpt m x H H1).
   intro.
   generalize (invol_inverse m zero x H H1).
   fold y in |- *.
   intros.
   assert (y = cA_1 m zero x).
  fold y in H18.
     tauto.
 rewrite H20 in |- *.
   fold (cF m x) in |- *.
    tauto.
assert (xff = cF_1 m x).
 unfold xff in |- *.
   rewrite H17 in |- *.
   assert (Iter (cF m) 3 x = x).
  unfold isTri in H7.
    rewrite <- H7 in |- *.
    unfold degreef in |- *.
    assert (cF = MF0Tr.MfM.f).
    tauto.
  rewrite H18 in |- *.
    apply MF0Tr.MfM.degree_per.
    tauto.
   tauto.
 simpl in H18.
   rewrite <- H18 in |- *.
   rewrite cF_1_cF in |- *.
  rewrite H18 in |- *.
     tauto.
  tauto.
 generalize (exd_cF m x).
   generalize (exd_cF m (cF m x)).
    tauto.
unfold m1 in |- *; unfold x_1 in |- *.
  rewrite cF_Flip1 in |- *.
 elim (eq_dart_dec (cF_1 m x) z).
  rewrite <- H18 in |- *.
     tauto.
 fold y in |- *.
   elim (eq_dart_dec y z).
   tauto.
  tauto.
 tauto.
 tauto.
 tauto.
 tauto.
Qed.

(* OK!!, SYSTEMATIC, BUT RATHER LONG...: *)

Lemma degreef_Flip1_detail_1:
forall(m:fmap)(x:dart),
inv_hmap m -> isMap m -> exd m x -> 
  let x_1 := cA_1 m one x in
  let y := cA m zero x in
  let y_1:= cA_1 m one y in
  let xff:= cF m y_1 in
  let yff:= cF m x_1 in
  let m1 := Split m one x x_1 in
 2 <= degreev m x -> 2 <= degreev m y -> 
  ~ expv m x y -> ~ expf m x y -> 
    isTri m x -> isTri m y ->
 degreef m1 x = 6.
Proof.
intros.
assert (degreee m x = 2).
 unfold isMap in H0.
   apply (H0 x H1).
assert (exd m y).
 unfold y in |- *.
   generalize (exd_cA m zero x).
    tauto.
simpl in |- *.
  fold y in |- *.
  intros.
  generalize (Poly_diff_vertex m x H H1 H2).
  simpl in |- *.
  fold x_1 in |- *.
  set (x1 := cA m one x) in |- *.
  intro.
  generalize (Poly_diff_vertex m y H H9 H3).
  simpl in |- *.
  fold y_1 in |- *.
  set (y1 := cA m one y) in |- *.
  intro.
  generalize (Tri_diff_face m x H H1 H6).
  simpl in |- *.
  intros.
  assert (y_1 = cF m x).
 unfold y_1 in |- *.
   unfold isMap in H0.
   generalize (H0 x H1).
   intro.
   generalize (degreee_invol_nofixpt m x H H1).
   intro.
   generalize (invol_inverse m zero x H H1).
   fold y in |- *.
   intros.
   assert (y = cA_1 m zero x).
  fold y in H14.
     tauto.
 rewrite H16 in |- *.
   fold (cF m x) in |- *.
    tauto.
rewrite <- H13 in H12.
  fold yff in H12.
  generalize (Tri_diff_face m y H H9 H7).
  simpl in |- *.
  assert (x_1 = cF m y).
 unfold x_1 in |- *.
   assert (x = cA_1 m zero y).
  unfold y in |- *.
    rewrite cA_1_cA in |- *.
    tauto.
   tauto.
   tauto.
 rewrite H14 in |- *.
   fold (cF m y) in |- *.
    tauto.
rewrite <- H14 in |- *.
  intro.
  generalize (Tri_diff_2faces m x y H H1 H9 H6 H7 H5).
  simpl in |- *.
  rewrite <- H13 in |- *.
  rewrite <- H14 in |- *.
  intros.
  assert (xff = cF_1 m x).
 unfold xff in |- *.
   rewrite H13 in |- *.
   assert (Iter (cF m) 3 x = x).
  unfold isTri in H6.
    rewrite <- H6 in |- *.
    unfold degreef in |- *.
    assert (cF = MF0Tr.MfM.f).
    tauto.
  rewrite H17 in |- *.
    apply MF0Tr.MfM.degree_per.
    tauto.
   tauto.
 simpl in H17.
   rewrite <- H17 in |- *.
   rewrite cF_1_cF in |- *.
  rewrite H17 in |- *.
     tauto.
  tauto.
 generalize (exd_cF m x).
   generalize (exd_cF m (cF m x)).
    tauto.
assert (yff = cF_1 m y).
 unfold yff in |- *.
   rewrite H14 in |- *.
   assert (Iter (cF m) 3 y = y).
  unfold isTri in H7.
    rewrite <- H7 in |- *.
    unfold degreef in |- *.
    assert (cF = MF0Tr.MfM.f).
    tauto.
  rewrite H18 in |- *.
    apply MF0Tr.MfM.degree_per.
    tauto.
   tauto.
 simpl in H18.
   rewrite <- H18 in |- *.
   rewrite cF_1_cF in |- *.
  rewrite H18 in |- *.
     tauto.
  tauto.
 generalize (exd_cF m y).
   generalize (exd_cF m (cF m y)).
    tauto.
assert (inv_hmap m1).
 unfold m1 in |- *.
   apply inv_hmap_Split.
    tauto.
assert (exd m1 x).
 unfold m1 in |- *.
   generalize (exd_Split m one x x_1 x).
    tauto.
assert (0 < ndN m1).
 apply MF.ndN_pos with x.
    tauto.
assert (MF0Tr.MfM.f = cF).
  tauto.
assert (MF0Tr.MfM.degree m1 x <= ndN m1).
 apply MF0Tr.MfM.degree_bound.
   tauto.
  tauto.
assert (x = Iter (cF m1) (degreef m1 x) x).
 unfold degreef in |- *.
   rewrite <- H22 in |- *.
   rewrite MF0Tr.MfM.degree_per in |- *.
   tauto.
  tauto.
  tauto.
assert (0 < MF0Tr.MfM.degree m1 x).
 apply MF0Tr.MfM.degree_pos.
    tauto.
generalize (cF_Flip1_detail_1 m x H H0 H1 H2 H3 H4 H5 H6 H7).
  fold y in |- *.
  fold x_1 in |- *.
  fold m1 in |- *.
  fold y_1 in |- *.
  fold xff in |- *.
  fold yff in |- *.
  intros.
  decompose [and] H26.
  clear H26.
  elim (Nat.eq_dec (degreef m1 x) 1).
 intro.
   rewrite a in H24.
   simpl in H24.
   rewrite H29 in H24.
    tauto.
intro.
  elim (Nat.eq_dec (degreef m1 x) 2).
 intro.
   rewrite a in H24.
   simpl in H24.
   rewrite H29 in H24.
   rewrite H28 in H24.
    tauto.
intro.
  elim (Nat.eq_dec (degreef m1 x) 3).
 intro.
   rewrite a in H24.
   simpl in H24.
   rewrite H29 in H24.
   rewrite H28 in H24.
   rewrite H30 in H24.
    tauto.
intro.
  elim (Nat.eq_dec (degreef m1 x) 4).
 intro.
   rewrite a in H24.
   simpl in H24.
   rewrite H29 in H24.
   rewrite H28 in H24.
   rewrite H30 in H24.
   rewrite H31 in H24.
   unfold yff in H24.
    tauto.
intro.
  elim (Nat.eq_dec (degreef m1 x) 5).
 intro.
   rewrite a in H24.
   simpl in H24.
   rewrite H29 in H24.
   rewrite H28 in H24.
   rewrite H30 in H24.
   rewrite H31 in H24.
   rewrite H33 in H24.
    tauto.
intro.
  fold degreef in H23.
  fold degreef in H25.
  unfold degreef in |- *.
  unfold MF0Tr.MfM.degree in |- *.
  rewrite MF0Tr.MfM.degree_aux_equation in |- *.
  elim (Arith.Compare_dec.le_lt_dec 1 (ndN m1)).
 elim (eq_dart_dec x (Iter (MF0Tr.MfM.f m1) 1 x)).
  simpl in |- *.
    rewrite H22 in |- *.
    rewrite H29 in |- *.
     tauto.
 elim (Nat.eq_dec 1 (ndN m1)).
  intros.
     absurd (1 = ndN m1).
    (* lia alone fails with stack overflow here. *)
    clear -H23 b H25 a.
    lia.
   tauto.
 intros.
   clear b5.
   rewrite MF0Tr.MfM.degree_aux_equation in |- *.
   assert (1 + 1 = 2).
   lia.
 rewrite H26 in |- *.
   clear H26.
   elim (Arith.Compare_dec.le_lt_dec 2 (ndN m1)).
  elim (eq_dart_dec x (Iter (MF0Tr.MfM.f m1) 2 x)).
   rewrite H22 in |- *.
     simpl in |- *.
     rewrite H29 in |- *.
     rewrite H28 in |- *.
     unfold xff in |- *.
      tauto.
  assert (dxge6 : 6 <= degreef m1 x).
    (*match goal with id : 0 < degreef m1 x |- _ => revert id end.
    repeat (match goal with id : degreef m1 x <> _ |-  _ => revert id end).*)
    (*clear; *) lia.
  elim (Nat.eq_dec 2 (ndN m1)).
   intros ndNm1_is2; intros; revert ndNm1_is2 dxge6.
   revert H23. (*match goal with id : degreef m1 x <= ndN m1 |- _ => revert id end.*)
   clear; lia.   
  intros.
    clear b6.
    assert (2 + 1 = 3).
    lia.
  rewrite H26 in |- *.
    clear H26.
    rewrite MF0Tr.MfM.degree_aux_equation in |- *.
    elim (Arith.Compare_dec.le_lt_dec 3 (ndN m1)).
   rewrite H22 in |- *.
     elim (eq_dart_dec x (Iter (cF m1) 3 x)).
    simpl in |- *.
      rewrite H29 in |- *.
      rewrite H28 in |- *.
      rewrite H30 in |- *.
       tauto.
   elim (Nat.eq_dec 3 (ndN m1)).
    intros.
       absurd (3 = ndN m1).
      (* lia alone fails with stack overflow here. *)
      clear -H23 H25 b b0 b1.
      lia.
     tauto.
   intros.
     clear b7.
     assert (3 + 1 = 4).
     lia.
   rewrite H26 in |- *.
     clear H26.
     clear a a0.
     rewrite MF0Tr.MfM.degree_aux_equation in |- *.
     elim (Arith.Compare_dec.le_lt_dec 4 (ndN m1)).
    rewrite H22 in |- *.
      elim (eq_dart_dec x (Iter (cF m1) 4 x)).
     simpl in |- *.
       rewrite H29 in |- *.
       rewrite H28 in |- *.
       rewrite H30 in |- *.
       rewrite H31 in |- *.
        tauto.
    elim (Nat.eq_dec 4 (ndN m1)).
     intros.
       clear b7.
        absurd (4 = ndN m1).
       clear -H23 H25 b b0 b1 b2 a.
       lia.
      tauto.
    intros.
      clear b8.
      assert (4 + 1 = 5).
      lia.
    rewrite H26 in |- *.
      clear H26.
      rewrite MF0Tr.MfM.degree_aux_equation in |- *.
      elim (Arith.Compare_dec.le_lt_dec 5 (ndN m1)).
     rewrite H22 in |- *.
       elim (eq_dart_dec x (Iter (cF m1) 5 x)).
      simpl in |- *.
        rewrite H29 in |- *.
        rewrite H28 in |- *.
        rewrite H30 in |- *.
        rewrite H31 in |- *.
        rewrite H33 in |- *.
         tauto.
     elim (Nat.eq_dec 5 (ndN m1)).
      intros.
        clear b8.
         absurd (5 = ndN m1). 
        (* lia alone fails with stack overflow here. *)
        clear -H23 H25 b b0 b1 b2 b3 a0.
        lia.
       tauto.
     intros.
       clear b9.
       rewrite MF0Tr.MfM.degree_aux_equation in |- *.
       assert (5 + 1 = 6).
       lia.
     rewrite H26 in |- *.
       clear H26.
       elim (Arith.Compare_dec.le_lt_dec 6 (ndN m1)).
      rewrite H22 in |- *.
        elim (eq_dart_dec x (Iter (cF m1) 6 x)).
        tauto.
      intros.
        simpl in b9.
        rewrite H29 in b9.
        rewrite H28 in b9.
        rewrite H30 in b9.
        rewrite H31 in b9.
        rewrite H33 in b9.
        rewrite H27 in b9.
         tauto.
     intro.
        lia.
    intro.
       lia.
   intro.
      lia.
  intro.
     lia.
 intro.
    lia.
intro.
   lia.
Qed.

(*=================================================
    Flip2 : SPLITS A HEXAHEDRAL FACE  
       INTO A BAR AND A QUADRILATERAL
==================================================*)

(* Flip2: NEVER USED ? *)

Definition Flip2(m:fmap)(x:dart):=
  let x_1 := cA_1 m one x in
  let y := cA m zero x in
  let y_1:= cA_1 m one y in
  let m1 := Split m one x x_1 in
  Split m1 one y y_1.

(* MUST BE CHANGED INTO: 

Definition Flip2(m1:fmap)(y:dart):=
  let y_1:= cA_1 m1 one y in
  Split m1 one y y_1.

*)

(* cA0: *)

Lemma cA0_Flip2:forall(m1:fmap)(y:dart)(z:dart),
   inv_hmap m1 -> exd m1 y -> exd m1 z ->
  let y_1:= cA_1 m1 one y in
  let m2 := Split m1 one y y_1 in
  cA m2 zero z = cA m1 zero z.
Proof.
intros.
unfold m2 in |- *.
rewrite MA1.cA_Split_opp in |- *.
 simpl in |- *.
    tauto.
 tauto.
Qed.

(* cA0_1: *)

Lemma cA0_1_Flip2:forall(m1:fmap)(y:dart)(z:dart),
   inv_hmap m1 -> exd m1 y -> exd m1 z ->
  let y_1:= cA_1 m1 one y in
  let m2 := Split m1 one y y_1 in
  cA_1 m2 zero z = cA_1 m1 zero z.
Proof.
intros.
unfold m2 in |- *.
rewrite MA1.cA_1_Split_opp in |- *.
 simpl in |- *.
    tauto.
 tauto.
Qed.

(* degreee: *)

Lemma degreee_Flip2:
forall(m1:fmap)(y:dart)(z:dart), 
 inv_hmap m1 -> isMap m1 -> 
   exd m1 y -> exd m1 z ->
  let y_1:= cA_1 m1 one y in
  let m2 := Split m1 one y y_1 in
    degreee m2 z = 2.
Proof.
intros.
unfold m2 in |- *.
rewrite degreee_Split1_summary in |- *.
 unfold isMap in H0.
   apply (H0 z H2).
 tauto.
 tauto.
Qed.

(* -- DIMENSION 1 -- *)

(* cA1: *)

Lemma cA1_Flip2: forall(m1:fmap)(y:dart)(z:dart),   
 inv_hmap m1 -> exd m1 y -> exd m1 z ->
  let y_1:= cA_1 m1 one y in
  let y1:= cA m1 one y in
  let m2 := Split m1 one y y_1 in
 2 <= degreev m1 y -> 
  cA m2 one z = 
    if eq_dart_dec y z then y
    else if eq_dart_dec y_1 z then y1
          else cA m1 one z. 
Proof.
intros.
unfold m2 in |- *.
unfold y_1 in |- *.
rewrite cA1_Flip1 in |- *.
 fold y1 in |- *.
    tauto.
 tauto.
 tauto.
 tauto.
 tauto.
Qed.

(* cA1_1: *)

Lemma cA1_1_Flip2: forall(m1:fmap)(y:dart)(z:dart),    
 inv_hmap m1 -> exd m1 y -> exd m1 z ->
  let y_1:= cA_1 m1 one y in
  let y1:= cA m1 one y in
  let m2 := Split m1 one y y_1 in
 2 <= degreev m1 y -> 
  cA_1 m2 one z = 
    if eq_dart_dec y1 z then y_1
    else if eq_dart_dec y z then y
         else cA_1 m1 one z. 
Proof.
intros.
unfold m2 in |- *.
unfold y_1 in |- *.
rewrite cA1_1_Flip1 in |- *.
 fold y1 in |- *.
    tauto.
 tauto.
 tauto.
 tauto.
 tauto.
Qed.

(* degreev: *)

Lemma degreev_Flip2: 
forall(m1:fmap)(y:dart)(z:dart)(H:inv_hmap m1),
 exd m1 y -> exd m1 z ->
  let y_1:= cA_1 m1 one y in
  let m2 := Split m1 one y y_1 in
    2 <= degreev m1 y -> 
  degreev m2 z = 
    if eq_dart_dec y z then 1
    else if expv_dec m1 y_1 z H 
         then degreev m1 y - 1
         else degreev m1 z.
Proof.
intros.
unfold m2 in |- *.
unfold y_1 in |- *.
apply (degreev_Flip1 m1 y z H H0 H1 H2).
Qed.

(* cF: *)

Lemma cF_Flip2:
forall(m1:fmap)(y:dart)(z:dart)(H:inv_hmap m1),
 exd m1 y -> exd m1 z ->
  let y_1:= cA_1 m1 one y in
  let y_f:= cF_1 m1 y in
  let x := cA m1 zero y in
  let m2 := Split m1 one y y_1 in
    2 <= degreev m1 y -> 
   cF m2 z = 
    if eq_dart_dec y_f z then y_1
    else if eq_dart_dec x z then y 
         else cF m1 z. 
Proof.
intros.
unfold m2 in |- *.
unfold y_1 in |- *.
rewrite cF_Split1 in |- *.
 fold y_f in |- *.
   unfold cF_1 in |- *.
   rewrite cA_cA_1 in |- *.
  fold x in |- *.
     tauto.
  tauto.
  tauto.
 tauto.
generalize (degreev_crackv m1 y).
   tauto.
 tauto.
Qed.

(* cF_1: *)

Lemma cF_1_Flip2:
forall(m1:fmap)(y:dart)(z:dart)(H:inv_hmap m1),
 exd m1 y -> exd m1 z ->
  let y_1:= cA_1 m1 one y in
  let y_f:= cF_1 m1 y in
  let x := cA m1 zero y in
  let m2 := Split m1 one y y_1 in
    2 <= degreev m1 y -> 
   cF_1 m2 z = 
    if eq_dart_dec y_1 z then y_f
    else if eq_dart_dec y z then x 
         else cF_1 m1 z. 
Proof.
intros.
unfold m2 in |- *.
unfold y_1 in |- *.
rewrite cF_1_Split1 in |- *.
 fold y_f in |- *.
   unfold cF_1 in |- *.
   rewrite cA_cA_1 in |- *.
  fold x in |- *.
     tauto.
  tauto.
  tauto.
 tauto.
generalize (degreev_crackv m1 y).
   tauto.
 tauto.
Qed.

(* degreef: OK *)

Lemma degreef_Flip2: 
forall(m1:fmap)(y:dart)(z:dart)(H:inv_hmap m1),
 exd m1 y -> exd m1 z ->
  let y_1:= cA_1 m1 one y in
  let y_f:= cF_1 m1 y in
  let x := cA m1 zero y in
  let m2 := Split m1 one y y_1 in
   degreee m1 y = 2 ->
     degreev m1 x = 1 -> 
       2 <= degreev m1 y -> 
         isHexa m1 x ->
 degreef m2 z = 
    if eq_dart_dec x z then 2
    else if eq_dart_dec y z then 2
         else if expf_dec m1 x z then 4
              else degreef m1 z.
Proof.
intros.
unfold m2 in |- *.
assert (crackv m1 y y_1).
 unfold y_1 in |- *.
   apply degreev_crackv.
   tauto.
  tauto.
  tauto.
assert (exd m1 x).
 unfold x in |- *.
   generalize (exd_cA m1 zero y).
    tauto.
generalize (degreev_fixpt m1 x H H7).
  intro.
  assert (cA m1 one x = x).
  tauto.
clear H8.
  generalize (degreee_invol_nofixpt m1 y H H0).
  intros.
  assert (cA m1 zero y <> y).
  tauto.
assert (cA m1 zero (cA m1 zero y) = y).
  tauto.
clear H8.
  fold x in H11.
  generalize (invol_inverse m1 zero y H H0).
  fold x in |- *.
  intros.
  assert (x = cA_1 m1 zero y).
  tauto.
clear H8.
  assert (x = cF m1 y).
 assert (x = cA_1 m1 one x).
  rewrite <- H9 in |- *.
    rewrite cA_1_cA in |- *.
    tauto.
   tauto.
   tauto.
 rewrite H8 in |- *.
   rewrite H12 in |- *.
   fold (cF m1 y) in |- *.
    tauto.
assert (y_1 = cF m1 x).
 unfold cF in |- *.
   unfold x in |- *.
   rewrite cA_1_cA in |- *.
  fold y_1 in |- *.
     tauto.
  tauto.
  tauto.
assert (y_1 = Iter (cF m1) 3 (cF_1 m1 y)).
 simpl in |- *.
   rewrite cF_cF_1 in |- *.
  rewrite <- H8 in |- *.
     tauto.
  tauto.
  tauto.
unfold isHexa in H5.
  set (dy_1 := degreef m1 y_1) in |- *.
  assert (degreef m1 x = dy_1).
 unfold dy_1 in |- *.
   unfold degreef in |- *.
   apply MF0Tr.MfM.expo_degree.
   tauto.
 rewrite H13 in |- *.
   unfold MF0Tr.MfM.expo in |- *.
   split.
   tauto.
 split with 1.
   simpl in |- *.
    tauto.
assert (2 <= 3 <= dy_1).
 rewrite <- H15 in |- *.
   rewrite H5 in |- *.
    lia.
generalize (degreef_Split1_split_summary_bis m1 y y_1 z 3 H H6 H1 H14 H16).
  fold m2 in |- *.
  fold dy_1 in |- *.
  rewrite <- H15 in |- *.
  rewrite H5 in |- *.
  fold y_f in |- *.
  assert (y = cF m1 y_f).
 unfold y_f in |- *.
   rewrite cF_cF_1 in |- *.
   tauto.
  tauto.
  tauto.
rewrite H13 in |- *.
  rewrite cF_1_cF in |- *.
 intros.
   decompose [and] H18.
   clear H18.
   assert (expf m1 y x).
  rewrite H8 in |- *.
    unfold expf in |- *.
    split.
    tauto.
  unfold MF.expo in |- *.
    split.
    tauto.
  split with 1.
    simpl in |- *.
     tauto.
 assert (MF.expo1 m1 y x).
  unfold expf in H18.
    generalize (MF.expo_expo1 m1 y x).
     tauto.
 elim (eq_dart_dec x z).
  intro.
    rewrite H21 in |- *.
    lia.
  rewrite <- a in |- *.
    unfold betweenf in |- *.
    generalize (MF.between_expo_refl_2 m1 y x H H0).
     tauto.
 elim (eq_dart_dec y z).
  intros.
    rewrite H21 in |- *.
    lia.
  rewrite <- a in |- *.
    unfold betweenf in |- *.
    generalize (MF.between_expo_refl_1 m1 y x H H0).
     tauto.
 intros.
   elim (expf_dec m1 x z).
  intro.
    assert (expf m1 y z).
   apply expf_trans with x.
     tauto.
    tauto.
  assert (MF.expo1 m1 y z).
   unfold expf in H23.
     generalize (MF.expo_expo1 m1 y z).
      tauto.
  generalize (MF.expo_between_3 m1 y x z H H20 H24).
    intro.
    assert (MF.between = betweenf).
    tauto.
  rewrite H26 in H25.
    assert (MF.f = cF).
    tauto.
  assert (MF.f_1 = cF_1).
    tauto.
  rewrite H27 in H25.
    rewrite H28 in H25.
    assert (~ betweenf m1 y z x).
   unfold betweenf in |- *.
     unfold MF.between in |- *.
     intros.
     intro.
     elim H29.
    intros i Hi.
      clear H29.
      elim Hi.
      intros j Hj.
      clear Hi.
      decompose [and] Hj.
      clear Hj.
      rewrite MF.upb_eq_degree in H33.
     assert (MF.degree m1 y = MF.degree m1 x).
      apply MF.expo_degree.
        tauto.
      unfold expf in H18.
         tauto.
     rewrite H32 in H33.
       unfold degreef in H5.
       assert (MF.degree = MF0Tr.MfM.degree).
       tauto.
     rewrite H34 in H33.
       rewrite H5 in H33.
       assert (j = 1).
      rewrite <- H34 in H5.
        rewrite H5 in H32.
        apply (MF.degree_unicity m1 y j 1 H H0).
        lia.
       lia.
      simpl in |- *.
        rewrite H31 in |- *.
        rewrite H8 in |- *.
         tauto.
     elim (Nat.eq_dec i 0).
      intro.
        rewrite a0 in H29.
        simpl in H29.
         tauto.
     intro.
       assert (i = 1).
       lia.
     rewrite H36 in H29.
       simpl in H29.
       rewrite H27 in H29.
       rewrite <- H8 in H29.
        tauto.
     tauto.
     tauto.
    tauto.
    tauto.
  rewrite H19 in |- *.
    lia.
  unfold y_f in |- *.
     tauto.
 intro.
   apply H22.
   intro.
   elim b1.
   clear b1.
   apply expf_trans with y.
  apply expf_symm.
     tauto.
 apply expf_trans with y_f.
  apply expf_symm.
    unfold expf in |- *.
    split.
    tauto.
  unfold MF.expo in |- *.
    split.
   unfold y_f in |- *.
     generalize (exd_cF_1 m1 y).
      tauto.
  split with 1.
    simpl in |- *.
    unfold y_f in |- *.
    rewrite cF_cF_1 in |- *.
    tauto.
   tauto.
   tauto.
 unfold expf in |- *.
    tauto.
 tauto.
 tauto.
Qed.

(* isBar: *)

Lemma isBar_Flip2: 
forall(m1:fmap)(y:dart)(H:inv_hmap m1),
  isMap m1 -> exd m1 y -> 
  let y_1:= cA_1 m1 one y in
  let x := cA m1 zero y in
  let m2 := Split m1 one y y_1 in
   degreev m1 x = 1 -> 
       2 <= degreev m1 y -> 
         isHexa m1 x ->
       isBar m2 x.
Proof.
intros.
unfold isBar in |- *.
split.
 unfold m2 in |- *.
   unfold y_1 in |- *.
   rewrite degreee_Flip2 in |- *.
   tauto.
  tauto.
  tauto.
  tauto.
 unfold x in |- *.
   generalize (exd_cA m1 zero y).
    tauto.
split.
 unfold m2 in |- *.
   unfold y_1 in |- *.
   rewrite (degreev_Flip2 m1 y x H) in |- *.
  fold y_1 in |- *.
    elim (eq_dart_dec y x).
    tauto.
  elim (expv_dec m1 y_1 x).
   intros.
     assert (MA1.MfcA.expo m1 y_1 y).
    unfold MA1.MfcA.expo in |- *.
      split.
     generalize (exd_cA_1 m1 one y).
       fold y_1 in |- *.
        tauto.
    split with 1.
      simpl in |- *.
      unfold y_1 in |- *.
      assert (MA1.MfcA.f m1 (cA_1 m1 one y) =
      cA m1 one (cA_1 m1 one y)).
      tauto.
    rewrite H5 in |- *.
      rewrite cA_cA_1 in |- *.
      tauto.
     tauto.
     tauto.
   assert (MA1.MfcA.expo m1 y x).
    apply MA1.MfcA.expo_trans with y_1.
     apply MA1.MfcA.expo_symm.
       tauto.
      tauto.
     tauto.
   assert (degreev m1 y = degreev m1 x).
    unfold degreev in |- *.
      apply MA1Tr.MfM.expo_degree.
      tauto.
     tauto.
    lia.
  rewrite H2 in |- *.
     tauto.
  tauto.
 unfold x in |- *.
   generalize (exd_cA m1 zero y).
    tauto.
  tauto.
unfold m2 in |- *.
  unfold y_1 in |- *.
  rewrite degreef_Flip2 in |- *.
 fold x in |- *.
   elim (eq_dart_dec x x).
   tauto.
  tauto.
 tauto.
 tauto.
unfold x in |- *.
  generalize (exd_cA m1 zero y).
   tauto.
unfold isMap in H0.
  apply H0.
   tauto.
fold x in |- *.
   tauto.
 tauto.
fold x in |- *.
   tauto.
Qed.

(* isQuad: *)

Lemma isQuad_Flip2: 
forall(m1:fmap)(y:dart)(H:inv_hmap m1),
  isMap m1 -> exd m1 y -> 
  let y_1:= cA_1 m1 one y in
  let x := cA m1 zero y in
  let m2 := Split m1 one y y_1 in
     degreev m1 x = 1 -> 
       2 <= degreev m1 y -> 
         isHexa m1 x ->
       isQuad m2 y_1.
Proof.
intros.
unfold isQuad in |- *.
unfold m2 in |- *.
unfold y_1 in |- *.
rewrite degreef_Flip2 in |- *.
 fold x in |- *.
   fold y_1 in |- *.
   assert (MA1.MfcA.expo m1 y_1 y).
  unfold MA1.MfcA.expo in |- *.
    split.
   generalize (exd_cA_1 m1 one y).
     fold y_1 in |- *.
      tauto.
  split with 1.
    simpl in |- *.
    unfold y_1 in |- *.
    assert (MA1.MfcA.f m1 (cA_1 m1 one y) =
    cA m1 one (cA_1 m1 one y)).
    tauto.
  rewrite H5 in |- *.
    rewrite cA_cA_1 in |- *.
    tauto.
   tauto.
   tauto.
 assert (degreev m1 y_1 = degreev m1 y).
  unfold degreev in |- *.
    apply MA1Tr.MfM.expo_degree.
    tauto.
   tauto.
 elim (eq_dart_dec x y_1).
  intros.
    rewrite a in H2.
     lia.
 elim (eq_dart_dec y y_1).
  intros.
    generalize (degreev_crackv m1 y H H1 H3).
    unfold crackv in |- *.
    unfold MA1.crack in |- *.
    fold y_1 in |- *.
     tauto.
 elim (expf_dec m1 x y_1).
   tauto.
 intros.
   assert (exd m1 x).
  unfold x in |- *.
    generalize (exd_cA m1 zero y).
     tauto.
 assert (y = cA_1 m1 zero x).
  unfold x in |- *.
    rewrite cA_1_cA in |- *.
    tauto.
   tauto.
   tauto.
 assert (y_1 = cF m1 x).
  unfold cF in |- *.
    rewrite <- H8 in |- *.
    fold y_1 in |- *.
     tauto.
 elim b.
   unfold expf in |- *.
   split.
   tauto.
 unfold MF.expo in |- *.
   split.
   tauto.
 split with 1.
   simpl in |- *.
   rewrite H9 in |- *.
    tauto.
 tauto.
 tauto.
generalize (exd_cA_1 m1 one y).
   tauto.
unfold isMap in H0.
  apply H0.
   tauto.
fold x in |- *.
   tauto.
 tauto.
fold x in |- *.
   tauto.
Qed.

(* isTri: *)

Lemma isTri_Flip2: 
forall(m1:fmap)(y z:dart)(H:inv_hmap m1),
  isMap m1 -> exd m1 y -> exd m1 z ->
  let y_1:= cA_1 m1 one y in
  let x := cA m1 zero y in
  let m2 := Split m1 one y y_1 in
   degreev m1 x = 1 -> 
       2 <= degreev m1 y -> 
         ~ expf m1 x z -> 
           isHexa m1 x -> isTri m1 z -> 
       isTri m2 z.
Proof.
intros.
unfold isTri in |- *.
unfold m2 in |- *.
unfold y_1 in |- *.
rewrite degreef_Flip2 in |- *.
 fold x in |- *.
   generalize (degreee_invol_nofixpt m1 y H H1).
   intros.
   generalize (invol_inverse m1 zero y H H1).
   intros.
   assert (degreee m1 y = 2).
  unfold isMap in H0.
    apply H0.
     tauto.
 assert (cA m1 zero y = cA_1 m1 zero y).
   tauto.
 clear H9.
   fold x in H11.
   assert (exd m1 x).
  unfold x in |- *.
    generalize (exd_cA m1 zero y).
     tauto.
 generalize (degreev_fixpt m1 x H H9).
   intro.
   assert (cA m1 one x = x).
   tauto.
 clear H12.
   assert (x = cA_1 m1 one x).
  rewrite <- H13 in |- *.
    rewrite cA_1_cA in |- *.
    tauto.
   tauto.
   tauto.
 assert (x = cF m1 y).
  unfold cF in |- *.
    rewrite <- H11 in |- *.
     tauto.
 elim (eq_dart_dec x z).
  intro.
    elim H5.
    rewrite <- a in |- *.
    apply expf_refl.
    tauto.
   tauto.
 elim (eq_dart_dec y z).
  intros.
    elim H5.
    rewrite <- a in |- *.
    apply expf_symm.
    rewrite H14 in |- *.
    unfold expf in |- *.
    split.
    tauto.
  unfold MF.expo in |- *.
    split.
    tauto.
  split with 1.
    simpl in |- *.
     tauto.
 elim (expf_dec m1 x z).
   tauto.
 unfold isTri in H7.
    tauto.
 tauto.
 tauto.
 tauto.
unfold isMap in H0.
  apply H0.
   tauto.
fold x in |- *.
   tauto.
 tauto.
fold x in |- *.
   tauto.
Qed.

(* isMap: *)

Lemma isMap_Flip2: 
forall(m1:fmap)(y:dart)(H:inv_hmap m1),
  isMap m1 -> exd m1 y -> 
  let y_1:= cA_1 m1 one y in
  let x := cA m1 zero y in
  let m2 := Split m1 one y y_1 in
     degreev m1 x = 1 -> 
       2 <= degreev m1 y -> 
     isMap m2.
Proof.
intros.
unfold isMap in |- *.
intros.
unfold m2 in |- *.
unfold y_1 in |- *.
rewrite degreee_Flip2 in |- *.
  tauto.
 tauto.
 tauto.
 tauto.
unfold m2 in H4.
  generalize (exd_Split m1 one y y_1 z).
   tauto.
Qed.

(* inv_hmap: *)

Lemma inv_hmap_Flip2: 
forall(m1:fmap)(y:dart)(H:inv_hmap m1),
  let y_1:= cA_1 m1 one y in
  let m2 := Split m1 one y y_1 in
     inv_hmap m2.
Proof.
intros.
unfold m2 in |- *.
apply inv_hmap_Split.
 tauto.
Qed.

(* cF_detail_1: *)

Lemma cF_Flip2_detail_1:
forall(m1:fmap)(y:dart),
  let x := cF m1 y in
  let y_1:= cF m1 x in
  let xff:= cF m1 y_1 in 
  let x_1 := cF m1 xff in
  let yff:= cF m1 x_1 in
  let m2 := Split m1 one y y_1 in
 inv_hmap m1 -> isMap m1 -> 
  exd m1 y ->
   isHexa m1 x -> 
    degreev m1 x = 1 -> 
     2 <= degreev m1 y ->
   (x = cF m2 y /\ y = cF m2 x /\
      y_1 = cF m2 yff /\
         xff = cF m2 y_1 /\
            x_1 = cF m2 xff /\
               yff = cF m2 x_1).
Proof.
intros.
assert (exd m1 x).
 unfold x in |- *.
   generalize (exd_cF m1 y).
    tauto.
unfold isMap in H0.
  generalize (H0 x H5).
  intro.
  generalize (degreee_invol_nofixpt m1 x H H5).
  intros.
  assert (cA m1 zero x <> x).
  tauto.
assert (cA m1 zero (cA m1 zero x) = x).
  tauto.
clear H7.
  generalize (degreev_fixpt m1 x H H5).
  intros.
  assert (cA m1 one x = x).
  tauto.
clear H7.
  assert (degreee m1 y = 2).
 apply (H0 y H1).
generalize (degreee_invol_nofixpt m1 y H H1).
  intros.
  assert (cA m1 zero y <> y).
  tauto.
assert (cA m1 zero (cA m1 zero y) = y).
  tauto.
clear H11.
  generalize (invol_inverse m1 zero x H H5).
  intro.
  assert (cA m1 zero x = cA_1 m1 zero x).
  tauto.
clear H11.
  generalize (invol_inverse m1 zero y H H1).
  intro.
  assert (cA m1 zero y = cA_1 m1 zero y).
  tauto.
clear H11.
  generalize (degreev_fixpt m1 x H H5).
  intros.
  assert (cA m1 one x = x).
  tauto.
clear H11.
  assert (cA_1 m1 one x = x).
 rewrite <- H10 in |- *.
   rewrite cA_1_cA in |- *.
  symmetry  in |- *.
     tauto.
  tauto.
  tauto.
assert (y = cF_1 m1 x).
 unfold x in |- *.
   rewrite cF_1_cF in |- *.
   tauto.
  tauto.
  tauto.
assert (y = cA m1 zero x).
 rewrite H17 in |- *.
   unfold cF_1 in |- *.
   rewrite H16 in |- *.
    tauto.
assert (expf m1 y x).
 rewrite H17 in |- *.
   unfold expf in |- *.
   split.
   tauto.
 unfold MF.expo in |- *.
   split.
  generalize (exd_cF_1 m1 x).
     tauto.
 split with 1.
   simpl in |- *.
   rewrite cF_cF_1 in |- *.
   tauto.
  tauto.
  tauto.
assert (degreef m1 y = degreef m1 x).
 unfold degreef in |- *.
   apply MF0Tr.MfM.expo_degree.
   tauto.
 unfold expf in H19.
    tauto.
assert (degreef m1 y = 6).
 rewrite H20 in |- *.
   unfold isHexa in H2.
    tauto.
assert (y = Iter (cF m1) 6 y).
 rewrite <- H21 in |- *.
   unfold degreef in |- *.
   assert (cF = MF.f).
   tauto.
 assert (MF0Tr.MfM.degree = MF.degree).
   tauto.
 rewrite H23 in |- *.
   rewrite H22 in |- *.
   rewrite MF.degree_per in |- *.
   tauto.
  tauto.
  tauto.
assert (y = cF m1 yff).
 unfold yff in |- *.
   unfold x_1 in |- *.
   unfold xff in |- *.
   unfold y_1 in |- *.
   unfold x in |- *.
   simpl in H22.
    tauto.
assert (isHexa m1 y).
 unfold isHexa in |- *.
    tauto.
generalize (Hexa_diff_face m1 y H H1 H24).
  simpl in |- *.
  fold x in |- *.
  fold y_1 in |- *.
  fold xff in |- *.
  fold x_1 in |- *.
  fold yff in |- *.
  intros.
  assert (cF_1 m1 y = yff).
 rewrite H23 in |- *.
   rewrite cF_1_cF in |- *.
   tauto.
  tauto.
 generalize (exd_cF m1 yff).
   rewrite <- H23 in |- *.
    tauto.
assert (y_1 = cA_1 m1 one y).
 unfold y_1 in |- *.
   unfold cF in |- *.
   rewrite <- H14 in |- *.
   rewrite <- H18 in |- *.
    tauto.
split.
 unfold m2 in |- *.
   rewrite H27 in |- *.
   rewrite cF_Flip2 in |- *.
  rewrite H26 in |- *.
    elim (eq_dart_dec yff y).
   intro.
     symmetry  in a.
      tauto.
  rewrite H18 in |- *.
    rewrite H9 in |- *.
    rewrite <- H18 in |- *.
    elim (eq_dart_dec x y).
    tauto.
  fold x in |- *.
     tauto.
  tauto.
  tauto.
  tauto.
  lia.
split.
 unfold m2 in |- *.
   rewrite H27 in |- *.
   rewrite cF_Flip2 in |- *.
  rewrite H26 in |- *.
    elim (eq_dart_dec yff x).
   intros.
     symmetry  in a.
      tauto.
  rewrite H18 in |- *.
    rewrite H9 in |- *.
    elim (eq_dart_dec x x).
    tauto.
   tauto.
  tauto.
  tauto.
  tauto.
  lia.
split.
 unfold m2 in |- *.
   rewrite H27 in |- *.
   rewrite cF_Flip2 in |- *.
  rewrite H26 in |- *.
    elim (eq_dart_dec yff yff).
    tauto.
   tauto.
  tauto.
  tauto.
 rewrite <- H26 in |- *.
   generalize (exd_cF_1 m1 y).
    tauto.
  lia.
split.
 unfold m2 in |- *.
   rewrite H27 in |- *.
   rewrite cF_Flip2 in |- *.
  rewrite H26 in |- *.
    rewrite <- H27 in |- *.
    elim (eq_dart_dec yff y_1).
   intro.
     symmetry  in a.
      tauto.
  rewrite H18 in |- *.
    rewrite H9 in |- *.
    elim (eq_dart_dec x y_1).
    tauto.
  fold xff in |- *.
     tauto.
  tauto.
  tauto.
 generalize (exd_cA_1 m1 one y).
    tauto.
  lia.
split.
 unfold m2 in |- *.
   rewrite H27 in |- *.
   rewrite cF_Flip2 in |- *.
  rewrite H26 in |- *.
    elim (eq_dart_dec yff xff).
   intro.
     symmetry  in a.
      tauto.
  rewrite H18 in |- *.
    rewrite H9 in |- *.
    elim (eq_dart_dec x xff).
    tauto.
  fold x_1 in |- *.
     tauto.
  tauto.
  tauto.
 unfold xff in |- *.
   generalize (exd_cF m1 y_1).
   unfold y_1 in |- *.
   generalize (exd_cF m1 x).
    tauto.
  lia.
unfold m2 in |- *.
  rewrite H27 in |- *.
  rewrite cF_Flip2 in |- *.
 rewrite H26 in |- *.
   elim (eq_dart_dec yff x_1).
  intro.
    symmetry  in a.
     tauto.
 rewrite H18 in |- *.
   rewrite H9 in |- *.
   elim (eq_dart_dec x x_1).
   tauto.
 fold yff in |- *.
    tauto.
 tauto.
 tauto.
unfold x_1 in |- *.
  unfold xff in |- *.
  generalize (exd_cF m1 (cF m1 y_1)).
  generalize (exd_cF m1 y_1).
  unfold y_1 in |- *.
  generalize (exd_cF m1 x).
   tauto.
 lia.
Qed.

(* cF_detail_2: *)

Lemma cF_Flip2_detail_2:
forall(m1:fmap)(y:dart)(z :dart),
  let x := cF m1 y in
  let y_1:= cF m1 x in
  let xff:= cF m1 y_1 in 
  let x_1 := cF m1 xff in
  let yff:= cF m1 x_1 in
  let m2 := Split m1 one y y_1 in
 inv_hmap m1 -> isMap m1 -> 
  exd m1 y -> exd m1 z ->
   isHexa m1 x -> 
    degreev m1 x = 1 -> 
     2 <= degreev m1 y ->
  x <> z -> y <> z -> y_1 <> z -> 
     xff <> z -> x_1 <> z -> yff <> z -> 
       cF m2 z = cF m1 z.
Proof.
intros.
assert (exd m1 x).
 unfold x in |- *.
   generalize (exd_cF m1 y).
    tauto.
unfold isMap in H0.
  generalize (H0 x H12).
  intro.
  generalize (degreee_invol_nofixpt m1 x H H12).
  intros.
  assert (cA m1 zero x <> x).
  tauto.
assert (cA m1 zero (cA m1 zero x) = x).
  tauto.
clear H14.
  generalize (degreev_fixpt m1 x H H12).
  intros.
  assert (cA m1 one x = x).
  tauto.
clear H14.
  assert (degreee m1 y = 2).
 apply (H0 y H1).
generalize (degreee_invol_nofixpt m1 y H H1).
  intros.
  assert (cA m1 zero y <> y).
  tauto.
assert (cA m1 zero (cA m1 zero y) = y).
  tauto.
clear H18.
  generalize (invol_inverse m1 zero x H H12).
  intro.
  assert (cA m1 zero x = cA_1 m1 zero x).
  tauto.
clear H18.
  generalize (invol_inverse m1 zero y H H1).
  intro.
  assert (cA m1 zero y = cA_1 m1 zero y).
  tauto.
clear H18.
  generalize (degreev_fixpt m1 x H H12).
  intros.
  assert (cA m1 one x = x).
  tauto.
clear H18.
  assert (cA_1 m1 one x = x).
 rewrite <- H23 in |- *.
   rewrite cA_1_cA in |- *.
  symmetry  in |- *.
     tauto.
  tauto.
  tauto.
assert (y = cF_1 m1 x).
 unfold x in |- *.
   rewrite cF_1_cF in |- *.
   tauto.
  tauto.
  tauto.
assert (y = cA m1 zero x).
 unfold cF_1 in |- *.
   rewrite H24 in |- *.
   unfold cF_1 in |- *.
   rewrite H23 in |- *.
    tauto.
assert (expf m1 y x).
 rewrite H24 in |- *.
   unfold expf in |- *.
   split.
   tauto.
 unfold MF.expo in |- *.
   split.
  generalize (exd_cF_1 m1 x).
     tauto.
 split with 1.
   simpl in |- *; rewrite cF_cF_1 in |- *.
   tauto.
  tauto.
  tauto.
assert (degreef m1 y = degreef m1 x).
 unfold degreef in |- *.
   apply MF0Tr.MfM.expo_degree.
   tauto.
 unfold expf in H26.
    tauto.
assert (degreef m1 y = 6).
 rewrite H27 in |- *.
   unfold isHexa in H2.
    tauto.
assert (y = Iter (cF m1) 6 y).
 rewrite <- H28 in |- *.
   unfold degreef in |- *.
   assert (cF = MF.f).
   tauto.
 assert (MF0Tr.MfM.degree = MF.degree).
   tauto.
 rewrite H30 in |- *.
   rewrite MF.degree_per in |- *.
   tauto.
  tauto.
  tauto.
assert (y = cF m1 yff).
 unfold yff in |- *.
   unfold x_1 in |- *.
   unfold xff in |- *.
   unfold y_1 in |- *.
   unfold x in |- *.
   simpl in H29.
    tauto.
assert (yff = cF_1 m1 y).
 rewrite H30 in |- *.
   rewrite cF_1_cF in |- *.
   tauto.
  tauto.
 generalize (exd_cF m1 yff).
   rewrite <- H30 in |- *.
    tauto.
assert (y_1 = cA_1 m1 one y).
 unfold y_1 in |- *.
   unfold cF in |- *.
   rewrite <- H21 in |- *.
   rewrite <- H25 in |- *.
    tauto.
unfold m2 in |- *.
  rewrite H32 in |- *.
  rewrite cF_Flip2 in |- *.
 rewrite <- H31 in |- *.
   elim (eq_dart_dec yff z).
   tauto.
 rewrite H25 in |- *.
   rewrite H16 in |- *.
   elim (eq_dart_dec x z).
   tauto.
  tauto.
 tauto.
 tauto.
 tauto.
 lia.
Qed.

(* ANC, OK: 

Lemma cF_Flip2_detail_2:
forall(m1:fmap)(y:dart)(z :dart),
  let x := cA m1 zero y in
  let y_1:= cA_1 m1 one y in
  let xff:= cF m1 y_1 in 
  let x_1 := cF m1 xff in
  let yff:= cF m1 x_1 in
  let m2 := Split m1 one y y_1 in
 inv_hmap m1 -> isMap m1 -> 
  exd m1 y -> exd m1 z ->
   isHexa m1 x -> 
    degreev m1 x = 1 -> 
     2 <= degreev m1 y ->
  x <> z -> y <> z -> y_1 <> z -> 
     xff <> z -> x_1 <> z -> yff <> z -> 
       cF m2 z = cF m1 z.
Proof.
intros.
assert (exd m1 x).
 unfold x in |- *.
   generalize (exd_cA m1 zero y).
    tauto.
unfold isMap in H0.
  generalize (H0 x H12).
  intro.
  generalize (degreee_invol_nofixpt m1 x H H12).
  intros.
  assert (cA m1 zero x <> x).
  tauto.
assert (cA m1 zero (cA m1 zero x) = x).
  tauto.
clear H14.
  generalize (degreev_fixpt m1 x H H12).
  intro.
  assert (cA m1 one x = x).
  tauto.
clear H14.
  assert (y = cA_1 m1 zero x).
 unfold x in |- *.
   rewrite cA_1_cA in |- *.
   tauto.
  tauto.
  tauto.
assert (y = cA m1 zero x).
 rewrite <- H16 in H14.
   rewrite cA_1_cA in H14.
   tauto.
  tauto.
 generalize (exd_cA m1 zero x).
    tauto.
assert (x = cF m1 y).
 unfold cF in |- *.
   rewrite H18 in |- *.
   rewrite cA_1_cA in |- *.
  rewrite <- H17 in |- *.
    rewrite cA_1_cA in |- *.
    tauto.
   tauto.
   tauto.
  tauto.
  tauto.
assert (expf m1 y x).
 rewrite H19 in |- *.
   unfold expf in |- *.
   split.
   tauto.
 unfold MF.expo in |- *.
   split.
   tauto.
 split with 1.
   simpl in |- *;  tauto.
assert (degreef m1 y = degreef m1 x).
 unfold degreef in |- *.
   apply MF0Tr.MfM.expo_degree.
   tauto.
 unfold expf in H20.
    tauto.
assert (degreef m1 y = 6).
 rewrite H21 in |- *.
   unfold isHexa in H2.
    tauto.
assert (y = Iter (cF m1) 6 y).
 rewrite <- H22 in |- *.
   unfold degreef in |- *.
   assert (cF = MF.f).
   tauto.
 assert (MF0Tr.MfM.degree = MF.degree).
   tauto.
 rewrite H24 in |- *.
   rewrite H23 in |- *.
   rewrite MF.degree_per in |- *.
   tauto.
  tauto.
  tauto.
assert (y_1 = cF m1 x).
 unfold cF in |- *.
   rewrite <- H14 in |- *.
   fold y_1 in |- *.
    tauto.
assert (y = cF m1 yff).
 unfold yff in |- *.
   unfold x_1 in |- *.
   unfold xff in |- *.
   rewrite H24 in |- *.
   rewrite H19 in |- *.
   simpl in H23.
    tauto.
assert (yff = cF_1 m1 y).
 rewrite H25 in |- *.
   rewrite cF_1_cF in |- *.
   tauto.
  tauto.
 generalize (exd_cF m1 yff).
   rewrite <- H25 in |- *.
    tauto.
unfold m2 in |- *.
  unfold y_1 in |- *.
  rewrite cF_Flip2 in |- *.
 rewrite <- H26 in |- *.
   elim (eq_dart_dec yff z).
   tauto.
 fold x in |- *.
   elim (eq_dart_dec x z).
   tauto.
  tauto.
 tauto.
 tauto.
 tauto.
 lia.
Qed.
*)

(*=====================================================
              Flip3: MERGES 2 FACES
=====================================================*)

(*=== GENERAL PROPERTIES ===*)

Lemma Bar_diff_face: forall(m:fmap)(x:dart),
  inv_hmap m -> exd m x -> isBar m x -> 
  let xf := cF m x in 
  x <> xf.
Proof.
intros.
unfold isBar in H1.
generalize (degreef_invol_nofixpt m x H H0).
fold xf in |- *.
intros.
intro.
symmetry  in H3.
 tauto.
Qed.

Lemma Quad_diff_face: forall(m:fmap)(x:dart),
  inv_hmap m -> exd m x -> isQuad m x -> 
  let xf := cF m x in
  let xff:= cF m xf in
  let xfff:=cF m xff in
  x <> xf /\ x <> xff /\ x <> xfff /\
  xf <> xff /\ xf <> xfff /\
  xff <> xfff.
Proof.
intros.
assert (MF.degree = MF0Tr.MfM.degree).
  tauto.
unfold isQuad in H1.
unfold degreef in H1.
  rewrite <- H2 in H1.
  clear H2.
  split.
 intro.
   assert (0 = 1).
  apply (MF.degree_unicity m x 0 1 H H0).
   simpl in |- *.
      lia.
   lia.
  simpl in |- *.
     tauto.
 inversion H3.
split.
 intro.
   assert (0 = 2).
  apply (MF.degree_unicity m x 0 2 H H0).
    lia.
   lia.
  simpl in |- *.
     tauto.
 inversion H3.
split.
 intro.
   assert (0 = 3).
  apply (MF.degree_unicity m x 0 3 H H0).
    lia.
   lia.
  simpl in |- *.
     tauto.
 inversion H3.
split.
 intro.
   assert (1 = 2).
  apply (MF.degree_unicity m x 1 2 H H0).
    lia.
   lia.
  simpl in |- *.
     tauto.
 inversion H3.
split.
 intro.
   assert (1 = 3).
  apply (MF.degree_unicity m x 1 3 H H0).
    lia.
   lia.
  simpl in |- *.
     tauto.
 inversion H3.
intro.
  assert (2 = 3).
 apply (MF.degree_unicity m x 2 3 H H0).
   lia.
  lia.
 simpl in |- *.
    tauto.
inversion H3.
Qed.

(*=== Dim 0: ===*)

(* cA0, cA0_1, FROM m2: *)

Lemma cA0_Flip3: 
forall(m2:fmap)(xff x:dart)(z:dart),
inv_hmap m2 -> 
 exd m2 x -> exd m2 xff -> exd m2 z ->
 let m3 := Merge m2 one xff x in
  cA m3 zero z = cA m2 zero z.
Proof.
intros.
unfold m3 in |- *.
assert (zero = dim_opp one).
 simpl in |- *.
    tauto.
rewrite H3 in |- *.
  rewrite cA_Merge in |- *.
elim (eq_dim_dec one (dim_opp one)). 
simpl. intro. inversion a.
  tauto.
 tauto.
Qed.

Lemma cA0_1_Flip3: 
forall(m2:fmap)(xff x:dart)(z:dart),
inv_hmap m2 ->
 exd m2 x -> exd m2 xff -> exd m2 z ->
 let m3 := Merge m2 one xff x in
  cA_1 m3 zero z = cA_1 m2 zero z.
Proof.
intros.
unfold m3 in |- *.
assert (zero = dim_opp one).
 simpl in |- *.
    tauto.
rewrite H3 in |- *.
  rewrite cA_1_Merge.
elim (eq_dim_dec one (dim_opp one)). 
simpl. intro. inversion a. 
  tauto.
 tauto.
Qed.
 
(* degreee: *)

Lemma degreee_Flip3_aux: 
forall(m2:fmap)(xff x:dart)(z:dart),
inv_hmap m2 ->
 exd m2 x -> exd m2 xff -> exd m2 z ->
 let m3 := Merge m2 one xff x in
  degreee m3 z = degreee m2 z.
Proof.
intros.
unfold m3 in |- *.
rewrite degreee_Merge1_summary in |- *.
  tauto.
 tauto.
 tauto.
 tauto.
 tauto.
Qed.

(* degreee, WITH NUMBERS: *)

Lemma degreee_Flip3: 
forall(m2:fmap)(xff x:dart)(z:dart),
inv_hmap m2 -> isMap m2 ->
 exd m2 x -> exd m2 xff -> exd m2 z ->
 let m3 := Merge m2 one xff x in
  degreee m3 z = 2.
Proof.
intros.
unfold m3 in |- *.
rewrite degreee_Merge1_summary in |- *.
 unfold isMap in H0.
   apply (H0 z H3).
 tauto.
 tauto.
 tauto.
 tauto.
Qed.

(* cA1, cA1_1: *)

Lemma cA1_Flip3: 
forall(m2:fmap)(xff x:dart)(z:dart),
inv_hmap m2 -> exd m2 x -> exd m2 xff ->
 cA m2 one x = x -> exd m2 z ->
    let xf0 := cA m2 one xff in   
    let m3 := Merge m2 one xff x in
  cA m3 one z = 
     if eq_dart_dec xff z then x
     else if eq_dart_dec x z then xf0
          else cA m2 one z.
Proof.
intros.
unfold m3 in |- *.
rewrite cA_Merge in |- *.
 assert (cA_1 m2 one x = x).
  rewrite <- H2 in |- *.
    rewrite cA_1_cA in |- *.
   symmetry  in |- *.
      tauto.
   tauto.
   tauto.
 rewrite H4 in |- *.
   fold xf0 in |- *.
    tauto.
 tauto.
Qed.

(* OK: *)

Lemma cA1_1_Flip3: 
forall(m2:fmap)(xff x:dart)(z:dart),
inv_hmap m2 -> exd m2 x -> exd m2 xff ->
  cA m2 one x = x -> exd m2 z ->
    let xf0 := cA m2 one xff in   
    let m3 := Merge m2 one xff x in
  cA_1 m3 one z = 
     if eq_dart_dec x z then xff
     else if eq_dart_dec xf0 z then x
          else cA_1 m2 one z.
Proof.
intros.
unfold m3 in |- *.
rewrite cA_1_Merge in |- *.
 assert (cA_1 m2 one x = x).
  rewrite <- H2 in |- *.
    rewrite cA_1_cA in |- *.
   symmetry  in |- *.
      tauto.
   tauto.
   tauto.
 rewrite H4 in |- *.
   fold xf0 in |- *.
    tauto.
 tauto.
Qed.

(* degreev: *)

Lemma degreev_Flip3_aux: 
forall(m2:fmap)(xff x:dart)(z:dart)(H:inv_hmap m2),
exd m2 x -> exd m2 xff ->  
 degreev m2 x = 1 -> ~ expv m2 xff x -> exd m2 z ->
 let m3 := Merge m2 one xff x in
  degreev m3 z = 
    if expv_dec m2 xff z H then degreev m2 xff + 1 
    else if expv_dec m2 x z H 
         then degreev m2 xff + 1 
    else degreev m2 z.
Proof.
intros.
unfold m3 in |- *.
rewrite (degreev_Merge1_summary m2 xff x z H) in |- *.
 rewrite H2 in |- *.
    tauto.
 tauto.
 tauto.
 tauto.
 tauto.
Qed.

(* degreev, SIMPLIFIED: *)

Lemma degreev_Flip3: 
forall(m2:fmap)(xff x:dart)(z:dart)(H:inv_hmap m2),
 exd m2 x -> exd m2 xff ->  
 degreev m2 x = 1 -> ~ expv m2 xff x -> exd m2 z ->
 let m3 := Merge m2 one xff x in
  degreev m3 z = 
    if expv_dec m2 xff z H then degreev m2 xff + 1 
    else if eq_dart_dec x z  
          then degreev m2 xff + 1 
          else degreev m2 z.
Proof.
intros.
assert (expv m2 x z <-> x = z).
 generalize (degreev_fixpt m2 x H H0).
   intros.
   assert (cA m2 one x = x).
   tauto.
 clear H5.
   split.
  intro.
    unfold expv in H5.
    assert (MA1.MfcA.expo2 m2 x z).
   generalize (MA1.MfcA.expo_expo2 m2 x z).
      tauto.
  unfold MA1.MfcA.expo2 in H7.
    elim H7.
    intros.
    clear H7.
    elim H9.
    intros i Hi.
    elim Hi.
    clear Hi.
    intros.
    unfold degreev in H2.
    assert (MA1.MfcA.degree = MA1Tr.MfM.degree).
    tauto.
  rewrite <- H11 in H2.
    rewrite H2 in H7.
    assert (i = 0).
    lia.
  rewrite H12 in H10.
    simpl in H10.
     tauto.
 intro.
   rewrite <- H5 in |- *.
   apply expv_refl.
    tauto.
unfold m3 in |- *.
  rewrite 
 (degreev_Flip3_aux m2 xff x z H H0 H1 H2 H3 H4)
    in |- *.
  elim (expv_dec m2 xff z H).
  tauto.
elim (expv_dec m2 x z H).
 elim (eq_dart_dec x z).
   tauto.
 unfold expv in H5.
    tauto.
elim (eq_dart_dec x z).
 unfold expv in H5.
    tauto.
 tauto.
Qed.

(* cF, cF_1: *)

Lemma cF_Flip3: 
forall(m2:fmap)(xff x:dart)(z:dart),
inv_hmap m2 -> exd m2 x -> exd m2 xff -> 
  cA m2 one x = x -> exd m2 z ->
   let y := cA m2 zero x in
   let xf := cF_1 m2 xff in
   let m3 := Merge m2 one xff x in
  cF m3 z = 
     if eq_dart_dec y z then xff
     else if eq_dart_dec xf z then x
          else cF m2 z.
Proof.
intros.
unfold m3 in |- *.
rewrite cF_Merge1 in |- *.
 fold y in |- *.
   fold xf in |- *.
   assert (cA_1 m2 one x = x).
  rewrite <- H2 in |- *.
    rewrite cA_1_cA in |- *.
   symmetry  in |- *.
      tauto.
   tauto.
   tauto.
 rewrite H4 in |- *.
    tauto.
 tauto.
 tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma cF_1_Flip3: 
forall(m2:fmap)(xff x:dart)(z:dart),
inv_hmap m2 -> exd m2 x -> exd m2 xff -> 
  cA m2 one x = x -> exd m2 z ->
   let y := cA m2 zero x in
   let xf := cF_1 m2 xff in
   let m3 := Merge m2 one xff x in
  cF_1 m3 z = 
     if eq_dart_dec xff z then y
     else if eq_dart_dec x z then xf
           else cF_1 m2 z.
Proof.
intros.
unfold m3 in |- *.
rewrite cF_1_Merge1 in |- *.
 fold y in |- *.
   fold xf in |- *.
   assert (cA_1 m2 one x = x).
  rewrite <- H2 in |- *.
    rewrite cA_1_cA in |- *.
   symmetry  in |- *.
      tauto.
   tauto.
   tauto.
 rewrite H4 in |- *.
    tauto.
 tauto.
 tauto.
 tauto.
 tauto.
Qed.

(* degreef: *)

Lemma degreef_Flip3: 
forall(m2:fmap)(xff x:dart)(z:dart)(H:inv_hmap m2),
 isMap m2 -> isBar m2 x -> isQuad m2 xff ->
  exd m2 x -> exd m2 xff -> exd m2 z ->
    let y := cA m2 zero x in
    let m3 := Merge m2 one xff x in
   degreef m3 z =
     if expof_dec m2 y z H then 6
     else
       if expof_dec m2 xff z H then 6 
       else degreef m2 z.
Proof.
intros.
unfold isQuad in H2.
unfold isBar in H1.
generalize (degreev_fixpt m2 x H H3).
intro.
assert (cA m2 one x = x).
  tauto.
clear H6.
  assert (x <> xff).
 intro.
   rewrite <- H6 in H2.
    absurd (degreef m2 x = 2).
   lia.
  tauto.
decompose [and] H1.
  clear H1.
  assert (~ expv m2 xff x).
 intro.
   assert (expv m2 x xff).
  apply expv_symm.
    tauto.
   tauto.
 unfold expv in H9.
   assert (MA1.MfcA.expo2 m2 x xff).
  generalize (MA1.MfcA.expo_expo2 m2 x xff).
     tauto.
 unfold MA1.MfcA.expo2 in H12.
   elim H12.
   intros.
   clear H13 H12.
   elim H14.
   intros i Hi.
   clear H14.
   elim Hi.
   clear Hi.
   intros.
   assert (MA1.MfcA.degree = MA1Tr.MfM.degree).
   tauto.
 unfold degreev in H10.
   rewrite <- H14 in H10.
   assert (i = 0).
   lia.
 rewrite H15 in H13.
   simpl in H13.
    tauto.
assert (isBar m2 y).
 unfold y in |- *.
   apply isBar_symm.
   tauto.
  tauto.
 unfold isBar in |- *;  tauto.
assert (~ expof m2 y xff).
 intro.
   unfold expof in H9.
   assert (degreef m2 y = degreef m2 xff).
  unfold degreef in |- *.
    apply (MF0Tr.MfM.expo_degree m2 y xff).
    tauto.
   tauto.
 unfold isBar in H9.
   rewrite <- H13 in H2.
    absurd (degreef m2 y = 4).
   lia.
  tauto.
unfold m3 in |- *.
  rewrite 
(degreef_Merge1_merge_summary m2 xff x z H) in |- *.
 fold y in |- *.
   rewrite H2 in |- *.
   unfold isBar in H9.
   assert (degreef m2 y = 2).
   tauto.
 rewrite H13 in |- *.
   assert (2 + 4 = 6).
   lia.
 rewrite H14 in |- *.
    tauto.
 tauto.
 tauto.
 tauto.
 tauto.
fold y in |- *.
tauto.
Qed.

(* isHexa: *)

Lemma isHexa_Flip3: 
forall(m2:fmap)(xff x:dart)(H:inv_hmap m2),
 isMap m2 -> isBar m2 x -> isQuad m2 xff ->
  exd m2 x -> exd m2 xff -> 
    let y := cA m2 zero x in
    let m3 := Merge m2 one xff x in
       isHexa m3 y.
Proof.
intros.
unfold isHexa in |- *.
unfold m3 in |- *.
assert (exd m2 y).
 unfold y in |- *.
   generalize (exd_cA m2 zero x).
    tauto.
rewrite (degreef_Flip3 m2 xff x y H H0 H1 H2 H3 H4 H5) in |- *.
  fold y in |- *.
  elim (expof_dec m2 y y H).
  tauto.
intro.
  elim b.
  apply expof_refl.
   tauto.
Qed.

(* isTri: *)

Lemma isTri_Flip3: 
forall(m2:fmap)(xff x z:dart)(H:inv_hmap m2),
 isMap m2 -> 
   isBar m2 x -> isQuad m2 xff -> isTri m2 z ->
  exd m2 x -> exd m2 xff -> exd m2 z ->
    let y := cA m2 zero x in
    let m3 := Merge m2 one xff x in
  ~ expof m2 y z -> ~ expof m2 xff z ->
      isTri m3 z.
Proof.
intros.
unfold isTri in |- *.
unfold m3 in |- *.
rewrite (degreef_Flip3 m2 xff x z H H0 H1 H2 H4 H5 H6) in |- *.
fold y in |- *.
elim (expof_dec m2 y z H).
  tauto.
elim (expof_dec m2 xff z H).
  tauto.
unfold isTri in H3.
   tauto.
Qed.

(* isMap: *)

Lemma isMap_Flip3: 
forall(m2:fmap)(xff x:dart)(H:inv_hmap m2),
 isMap m2 -> exd m2 x -> exd m2 xff -> 
 let y := cA m2 zero x in
    let m3 := Merge m2 one xff x in
      isMap m3.
Proof.
intros.
unfold isMap in |- *.
intros.
unfold m3 in |- *.
rewrite degreee_Flip3 in |- *.
  tauto.
 tauto.
 tauto.
 tauto.
 tauto.
unfold m3 in H3.
  generalize (exd_Merge m2 one xff x z).
   tauto.
Qed.

(* cF_detail_1: *)

Lemma cF_Flip3_detail_1:
forall(m2:fmap)(xff x:dart), 
inv_hmap m2 -> isMap m2 -> 
 isBar m2 x -> isQuad m2 xff ->
  exd m2 x -> exd m2 xff -> 
    let y := cF m2 x in
    let x_1 := cF m2 xff in
    let yff := cF m2 x_1 in
    let y_1 := cF m2 yff in
    let m3 := Merge m2 one xff x in
  (y = cF m3 x /\
     xff = cF m3 y /\
       x_1 = cF m3 xff /\
         yff = cF m3 x_1 /\
           y_1 = cF m3 yff /\
              x = cF m3 y_1). 
Proof.
intros.
assert (exd m2 y).
 unfold y in |- *.
   generalize (exd_cF m2 x).
    tauto.
unfold isBar in H1.
  generalize (degreee_invol_nofixpt m2 x H H3).
  intros.
  assert (cA m2 zero x <> x).
  tauto.
assert (cA m2 zero (cA m2 zero x) = x).
  tauto.
clear H6.
  generalize (invol_inverse m2 zero x H H3).
  intros.
  assert (cA m2 zero x = cA_1 m2 zero x).
  tauto.
clear H6.
  generalize (degreev_fixpt m2 x H H3).
  intro.
  assert (cA m2 one x = x).
  tauto.
clear H6.
  assert (cA_1 m2 one x = x).
 rewrite <- H10 in |- *.
   rewrite cA_1_cA in |- *.
  symmetry  in |- *.
     tauto.
  tauto.
  tauto.
assert (Iter (cF m2) 2 x = x).
 assert (degreef m2 x = 2).
   tauto.
 rewrite <- H11 in |- *.
   assert (cF = MF.f).
   tauto.
 assert (degreef = MF.degree).
   tauto.
 rewrite H12 in |- *.
   rewrite H13 in |- *.
   apply MF.degree_per.
   tauto.
  tauto.
simpl in H11.
  fold y in H11.
  assert (y = cF_1 m2 x).
 rewrite <- H11 in |- *.
   rewrite cF_1_cF in |- *.
   tauto.
  tauto.
  tauto.
assert (y = cA m2 zero x).
 rewrite H12 in |- *.
   unfold cF_1 in |- *.
   rewrite H10 in |- *.
    tauto.
assert (isBar m2 y).
 rewrite H13 in |- *.
   apply isBar_symm.
   tauto.
  tauto.
 unfold isBar in |- *.
    tauto.
generalize (degreee_invol_nofixpt m2 y H H5).
  intros.
  unfold isBar in H14.
  assert (cA m2 zero y <> y).
  tauto.
assert (cA m2 zero (cA m2 zero y) = y).
  tauto.
clear H15.
  generalize (invol_inverse m2 zero y H H5).
  intros.
  assert (cA m2 zero y = cA_1 m2 zero y).
  tauto.
clear H15.
  generalize (degreev_fixpt m2 y H H5).
  intro.
  assert (cA m2 one y = y).
  tauto.
clear H15.
  generalize (Quad_diff_face m2 xff H H4 H2).
  (*simpl in |- *.*)
  fold x_1 in |- *.
  fold yff in |- *.
  fold y_1 in |- *.
  intro.
  assert (degreef = MF.degree).
  tauto.
assert (cF = MF.f).
  tauto.
assert (Iter (cF m2) 4 xff = xff).
 unfold isQuad in H2.
   rewrite <- H2 in |- *.
   rewrite H20 in |- *.
   rewrite H21 in |- *.
   apply MF.degree_per.
   tauto.
  tauto.
assert (exd m2 x_1).
 unfold x_1 in |- *.
   generalize (exd_cF m2 xff).
    tauto.
assert (exd m2 yff).
 unfold yff in |- *.
   generalize (exd_cF m2 x_1).
    tauto.
assert (exd m2 y_1).
 unfold y_1 in |- *.
   generalize (exd_cF m2 yff).
    tauto.
assert (y_1 = cF_1 m2 xff).
 rewrite <- H22 in |- *.
   simpl in |- *.
   fold x_1 in |- *.
   fold yff in |- *.
   fold y_1 in |- *.
   rewrite cF_1_cF in |- *.
   tauto.
  tauto.
  tauto.
split.
 unfold m3 in |- *.
   rewrite cF_Flip3 in |- *.
  elim (eq_dart_dec (cA m2 zero x) x).
    tauto.
  rewrite <- H26 in |- *.
    elim (eq_dart_dec y_1 x).
   intros.
     assert (~ expf m2 x xff).
    intro.
      assert (degreef m2 x = degreef m2 xff).
     unfold degreef in |- *.
       apply MF0Tr.MfM.expo_degree.
       tauto.
     unfold expf in H27.
        tauto.
    unfold isQuad in H2.
      rewrite H2 in H28.
      rewrite H28 in H1.
       absurd (4 = 2).
      lia.
     tauto.
   elim H27.
     rewrite <- a in |- *.
     rewrite H26 in |- *.
     unfold expf in |- *.
     split.
     tauto.
   unfold MF.expo in |- *.
     split.
    generalize (exd_cF_1 m2 xff).
       tauto.
   split with 1.
     simpl in |- *.
     rewrite cF_cF_1 in |- *.
     tauto.
    tauto.
    tauto.
  symmetry  in |- *.
     tauto.
  tauto.
  tauto.
  tauto.
  tauto.
  tauto.
split.
 unfold m3 in *.
   rewrite cF_Flip3 in  *.
  rewrite <- H13 in  *.
    elim (eq_dart_dec y y).
    tauto.
   tauto.
  tauto.
  tauto.
  tauto.
  tauto.
  tauto.
split.
 unfold m3 in  *.
   rewrite cF_Flip3 in *.
  rewrite <- H13 in *.
    elim (eq_dart_dec y xff).
   intro.
     unfold isQuad in H2.
     rewrite a in H14.
     rewrite H2 in H14.
      absurd (4 = 2).
     lia.
    tauto.
  rewrite <- H26 in |- *.
    elim (eq_dart_dec y_1 xff).
   intros.
     symmetry  in a.
      tauto.
  fold x_1 in |- *.
     tauto.
  tauto.
  tauto.
  tauto.
  tauto.
  tauto.
split.
 unfold m3 in *.
   rewrite cF_Flip3 in |- *.
  rewrite <- H13 in |- *.
    elim (eq_dart_dec y x_1).
   intro.
     unfold x_1 in a.
     assert (expf m2 xff y).
    unfold expf in |- *.
      split.
      tauto.
    unfold MF.expo in |- *.
      split.
      tauto.
    split with 1.
      simpl in *.
      symmetry  in |- *.
       tauto.
   assert (degreef m2 xff = degreef m2 y).
    unfold isQuad in H2.
      rewrite H20 in *.
      apply MF.expo_degree.
      tauto.
    unfold expf in H27.
       tauto.
   rewrite H2 in H28.
     rewrite <- H28 in H14.
      absurd (4 = 2).
     lia.
    tauto.
  rewrite <- H26 in *.
    elim (eq_dart_dec y_1 x_1).
   intros.
     symmetry  in a.
      tauto.
  fold yff in |- *.
     tauto.
  tauto.
  tauto.
  tauto.
  tauto.
  tauto.
split.
 unfold m3 in *.
   rewrite cF_Flip3 in *.
  rewrite <- H13 in *.
    elim (eq_dart_dec y yff).
   intro.
     unfold yff in a.
     unfold x_1 in a.
     assert (expf m2 xff y).
    unfold expf in *.
      split.
      tauto.
    unfold MF.expo in *.
      split.
      tauto.
    split with 2.
      simpl in  *.
      symmetry  in |- *.
       tauto.
   assert (degreef m2 xff = degreef m2 y).
    rewrite H20 in *.
      apply MF.expo_degree.
      tauto.
    unfold expf in H27.
       tauto.
   unfold isQuad in H2.
     rewrite H2 in H28.
     rewrite <- H28 in H14.
      absurd (4 = 2).
     lia.
    tauto.
  rewrite <- H26 in *.
    elim (eq_dart_dec y_1 yff).
   intro.
     symmetry  in a.
      tauto.
  fold y_1 in |- *.
     tauto.
  tauto.
  tauto.
  tauto.
  tauto.
  tauto.
unfold m3 in |- *.
  rewrite cF_Flip3 in |- *.
 rewrite <- H13 in |- *.
   elim (eq_dart_dec y y_1).
  intro.
    unfold y_1 in a.
    unfold yff in a.
    unfold x_1 in a.
    assert (expf m2 xff y).
   unfold expf in |- *.
     split.
     tauto.
   unfold MF.expo in |- *.
     split.
     tauto.
   split with 3.
     simpl in |- *.
     symmetry  in |- *.
      tauto.
  assert (degreef m2 xff = degreef m2 y).
   unfold isQuad in H2.
     rewrite H20 in |- *.
     apply MF.expo_degree.
     tauto.
   unfold expf in H27.
      tauto.
  rewrite H2 in H28.
    rewrite <- H28 in H14.
     absurd (4 = 2).
    lia.
   tauto.
 rewrite <- H26 in |- *.
   elim (eq_dart_dec y_1 y_1).
   tauto.
  tauto.
 tauto.
 tauto.
 tauto.
 tauto.
 tauto.
Qed.

(* cF_detail_2: *)

Lemma cF_Flip3_detail_2:
forall(m2:fmap)(xff x z:dart), exd m2 z ->
inv_hmap m2 -> isMap m2 -> 
 isBar m2 x -> isQuad m2 xff ->
  exd m2 x -> exd m2 xff ->
    let y := cF m2 x in
    let x_1 := cF m2 xff in
    let yff := cF m2 x_1 in
    let y_1 := cF m2 yff in
    let m3 := Merge m2 one xff x in
  x <> z -> y <> z -> xff <> z -> x_1 <> z -> 
    yff <> z -> y_1 <> z ->
       cF m3 z = cF m2 z.
Proof.
intros m2 xff x z Ez.
intros.
assert (exd m2 y).
 unfold y in |- *.
   generalize (exd_cF m2 x).
    tauto.
unfold isBar in H1.
  generalize (degreee_invol_nofixpt m2 x H H3).
  intros.
  assert (cA m2 zero x <> x).
  tauto.
assert (cA m2 zero (cA m2 zero x) = x).
  tauto.
clear H12.
  generalize (invol_inverse m2 zero x H H3).
  intros.
  assert (cA m2 zero x = cA_1 m2 zero x).
  tauto.
clear H12.
  generalize (degreev_fixpt m2 x H H3).
  intro.
  assert (cA m2 one x = x).
  tauto.
clear H12.
  assert (cA_1 m2 one x = x).
 rewrite <- H16 in |- *.
   rewrite cA_1_cA in |- *.
  symmetry  in |- *.
     tauto.
  tauto.
  tauto.
assert (Iter (cF m2) 2 x = x).
 assert (degreef m2 x = 2).
   tauto.
 rewrite <- H17 in |- *.
   assert (cF = MF.f).
   tauto.
 assert (degreef = MF.degree).
   tauto.
 rewrite H18 in |- *.
   rewrite H19 in |- *.
   apply MF.degree_per.
   tauto.
  tauto.
simpl in H17.
  fold y in H17.
  assert (y = cF_1 m2 x).
 rewrite <- H17 in |- *.
   rewrite cF_1_cF in |- *.
   tauto.
  tauto.
  tauto.
assert (y = cA m2 zero x).
 rewrite H18 in |- *.
   unfold cF_1 in |- *.
   rewrite H16 in |- *.
    tauto.
assert (isBar m2 y).
 rewrite H19 in |- *.
   apply isBar_symm.
   tauto.
  tauto.
 unfold isBar in |- *.
    tauto.
generalize (degreee_invol_nofixpt m2 y H H11).
  intros.
  unfold isBar in H20.
  assert (cA m2 zero y <> y).
  tauto.
assert (cA m2 zero (cA m2 zero y) = y).
  tauto.
clear H21.
  generalize (invol_inverse m2 zero y H H11).
  intros.
  assert (cA m2 zero y = cA_1 m2 zero y).
  tauto.
clear H21.
  generalize (degreev_fixpt m2 y H H11).
  intro.
  assert (cA m2 one y = y).
  tauto.
clear H21.
  generalize (Quad_diff_face m2 xff H H4 H2).
(*  simpl in |- *.*)
  fold x_1 in |- *.
  fold yff in |- *.
  fold y_1 in |- *.
  intro.
  assert (degreef = MF.degree).
  tauto.
assert (cF = MF.f).
  tauto.
assert (Iter (cF m2) 4 xff = xff).
 unfold isQuad in H2.
   rewrite <- H2 in |- *.
   rewrite H26 in |- *.
   rewrite H27 in |- *.
   apply MF.degree_per.
   tauto.
  tauto.
assert (exd m2 x_1).
 unfold x_1 in |- *.
   generalize (exd_cF m2 xff).
    tauto.
assert (exd m2 yff).
 unfold yff in |- *.
   generalize (exd_cF m2 x_1).
    tauto.
assert (exd m2 y_1).
 unfold y_1 in |- *.
   generalize (exd_cF m2 yff).
    tauto.
assert (y_1 = cF_1 m2 xff).
 rewrite <- H28 in |- *.
   simpl in |- *.
   fold x_1 in |- *.
   fold yff in |- *.
   fold y_1 in |- *.
   rewrite cF_1_cF in |- *.
   tauto.
  tauto.
  tauto.
unfold m3 in *.
  rewrite cF_Flip3 in |- *.
 rewrite <- H19 in |- *.
   elim (eq_dart_dec y z).
   tauto.
 rewrite <- H32 in |- *.
   elim (eq_dart_dec y_1 z).
   tauto.
  tauto.
 tauto.
 tauto.
 tauto.
 tauto.
 tauto.
Qed.

(*=================================================
 Flip4: SPLITS A HEXAHEDRAL FACE INTO 2 TRIANGLES
==================================================*)

(*=== Dim 0: ===*)

(* cA0, cA0_1: *)

Lemma cA0_Flip4: 
forall(m3:fmap)(yff y:dart)(z:dart),
inv_hmap m3 -> 
 exd m3 y -> exd m3 yff -> exd m3 z ->
 let m4 := Merge m3 one yff y in
  cA m4 zero z = cA m3 zero z.
Proof.
intros.
unfold m4 in |- *.
assert (zero = dim_opp one).
 simpl in |- *.
    tauto.
rewrite H3 in |- *.
  rewrite cA_Merge.
elim (eq_dim_dec one (dim_opp one)). 
simpl. intro. inversion a.
  tauto.
 tauto.
Qed.

(* OK: *)

Lemma cA0_1_Flip4: 
forall(m3:fmap)(yff y:dart)(z:dart),
inv_hmap m3 -> 
 exd m3 y -> exd m3 yff -> exd m3 z ->
 let m4 := Merge m3 one yff y in
  cA_1 m4 zero z = cA_1 m3 zero z.
Proof.
intros.
unfold m4 in |- *.
assert (zero = dim_opp one).
 simpl in |- *.
    tauto.
rewrite H3 in |- *.
rewrite cA_1_Merge.
elim (eq_dim_dec one (dim_opp one)). 
simpl. intro. inversion a.
 tauto.
 tauto.
Qed.

(* degreee: *)

Lemma degreee_Flip4_aux: 
forall(m3:fmap)(yff y:dart)(z:dart),
inv_hmap m3 ->
 exd m3 y -> exd m3 yff -> exd m3 z ->
 let m4 := Merge m3 one yff y in
  degreee m4 z = degreee m4 z.
Proof.
intros.
unfold m4 in |- *.
rewrite degreee_Merge1_summary in |- *.
  tauto.
 tauto.
 tauto.
 tauto.
 tauto.
Qed.

(* degreee, WITH NUMBERS: *)

Lemma degreee_Flip4: 
forall(m3:fmap)(yff y:dart)(z:dart),
inv_hmap m3 -> isMap m3 ->
 exd m3 y -> exd m3 yff -> exd m3 z ->
 let m4 := Merge m3 one yff y in
  degreee m4 z = 2.
Proof.
intros.
unfold m4 in |- *.
rewrite degreee_Merge1_summary in |- *.
 unfold isMap in H0.
   apply (H0 z H3).
 tauto.
 tauto.
 tauto.
 tauto.
Qed.

(* cA1, cA1_1: *)

Lemma cA1_Flip4: 
forall(m3:fmap)(yff y:dart)(z:dart),
inv_hmap m3 -> exd m3 y -> exd m3 yff ->
 cA m3 one y = y -> exd m3 z ->
    let yf0 := cA m3 one yff in   
    let m4 := Merge m3 one yff y in
  cA m4 one z = 
     if eq_dart_dec yff z then y
     else if eq_dart_dec y z then yf0
          else cA m3 one z.
Proof.
intros.
unfold m4 in |- *.
rewrite cA_Merge in |- *.
 assert (cA_1 m3 one y = y).
  rewrite <- H2 in |- *.
    rewrite cA_1_cA in |- *.
   symmetry  in |- *.
      tauto.
   tauto.
   tauto.
 rewrite H4 in |- *.
   fold yf0 in |- *.
    tauto.
 tauto.
Qed.

(* OK: *)

Lemma cA1_1_Flip4: 
forall(m3:fmap)(yff y:dart)(z:dart),
inv_hmap m3 -> exd m3 y -> exd m3 yff ->
 cA m3 one y = y -> exd m3 z ->
    let yf0 := cA m3 one yff in   
    let m4 := Merge m3 one yff y in
  cA_1 m4 one z = 
     if eq_dart_dec y z then yff
     else if eq_dart_dec yf0 z then y
          else cA_1 m3 one z.
Proof.
intros.
unfold m4 in |- *.
rewrite cA_1_Merge in |- *.
 assert (cA_1 m3 one y = y).
  rewrite <- H2 in |- *.
    rewrite cA_1_cA in |- *.
   symmetry  in |- *.
      tauto.
   tauto.
   tauto.
 rewrite H4 in |- *.
   fold yf0 in |- *.
    tauto.
 tauto.
Qed.

(* degreev: *)

Lemma degreev_Flip4_aux: 
forall(m3:fmap)(yff y:dart)(z:dart)(H:inv_hmap m3),
exd m3 y -> exd m3 yff ->  
 degreev m3 y = 1 -> ~ expv m3 yff y -> exd m3 z ->
 let yf0 := cA m3 one yff in   
 let m4 := Merge m3 one yff y in
  degreev m4 z = 
    if expv_dec m3 yff z H then degreev m3 yff + 1 
    else if expv_dec m3 y z H 
          then degreev m3 yff + 1 
          else degreev m3 z.
Proof.
intros.
unfold m4 in |- *.
rewrite (degreev_Merge1_summary m3 yff y z H) in |- *.
 rewrite H2 in |- *.
    tauto.
 tauto.
 tauto.
 tauto.
 tauto.
Qed.

(* degreev, SIMPLIFIED: *)

Lemma degreev_Flip4: 
forall(m3:fmap)(yff y:dart)(z:dart)(H:inv_hmap m3),
exd m3 y -> exd m3 yff ->  
 degreev m3 y = 1 -> ~ expv m3 yff y -> exd m3 z ->
 let yf0 := cA m3 one yff in
 let m4 := Merge m3 one yff y in
 degreev m4 z = 
    if expv_dec m3 yff z H then degreev m3 yff + 1 
    else if eq_dart_dec y z
          then degreev m3 yff + 1 
        else degreev m3 z.
Proof.
intros.
assert (expv m3 y z <-> y = z).
 generalize (degreev_fixpt m3 y H H0).
   intros.
   assert (cA m3 one y = y).
   tauto.
 clear H5.
   split.
  intro.
    unfold expv in H5.
    assert (MA1.MfcA.expo2 m3 y z).
   generalize (MA1.MfcA.expo_expo2 m3 y z).
      tauto.
  unfold MA1.MfcA.expo2 in H7.
    elim H7.
    intros.
    clear H7.
    elim H9.
    intros i Hi.
    elim Hi.
    clear Hi.
    intros.
    unfold degreev in H2.
    assert (MA1.MfcA.degree = MA1Tr.MfM.degree).
    tauto.
  rewrite <- H11 in H2.
    rewrite H2 in H7.
    assert (i = 0).
    lia.
  rewrite H12 in H10.
    simpl in H10.
     tauto.
 intro.
   rewrite <- H5 in |- *.
   apply expv_refl.
    tauto.
unfold m4 in |- *.
  rewrite 
 (degreev_Flip4_aux m3 yff y z H H0 H1 H2 H3 H4)
    in |- *.
  elim (expv_dec m3 yff z H).
  tauto.
elim (expv_dec m3 y z H).
 elim (eq_dart_dec y z).
   tauto.
 unfold expv in H5.
    tauto.
elim (eq_dart_dec y z).
 unfold expv in H5.
    tauto.
 tauto.
Qed.

(* cF, cF_1: *)

Lemma cF_Flip4: 
forall(m3:fmap)(yff y:dart)(z:dart),
inv_hmap m3 -> exd m3 y -> exd m3 yff -> 
  cA m3 one y = y -> exd m3 z ->
   let x := cA m3 zero y in
   let yf := cF_1 m3 yff in
   let m4 := Merge m3 one yff y in
  cF m4 z = 
     if eq_dart_dec x z then yff
     else if eq_dart_dec yf z then y
          else cF m3 z.
Proof.
intros.
unfold m4 in |- *.
rewrite cF_Merge1 in |- *.
 fold x in |- *.
   fold yf in |- *.
   assert (cA_1 m3 one y = y).
  rewrite <- H2 in |- *.
    rewrite cA_1_cA in |- *.
   symmetry  in |- *.
      tauto.
   tauto.
   tauto.
 rewrite H4 in |- *.
    tauto.
 tauto.
 tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma cF_1_Flip4: 
forall(m3:fmap)(yff y:dart)(z:dart),
inv_hmap m3 -> exd m3 y -> exd m3 yff -> 
  cA m3 one y = y -> exd m3 z ->
   let x := cA m3 zero y in
   let yf := cF_1 m3 yff in
   let m4 := Merge m3 one yff y in
  cF_1 m4 z = 
     if eq_dart_dec yff z then x
     else if eq_dart_dec y z then yf
          else cF_1 m3 z.
Proof.
intros.
unfold m4 in |- *.
rewrite cF_1_Merge1 in |- *.
 fold x in |- *.
   fold yf in |- *.
   assert (cA_1 m3 one y = y).
  rewrite <- H2 in |- *.
    rewrite cA_1_cA in |- *.
   symmetry  in |- *.
      tauto.
   tauto.
   tauto.
 rewrite H4 in |- *.
    tauto.
 tauto.
 tauto.
 tauto.
 tauto.
Qed.

(* degreef: *)

Lemma degreef_Flip4: 
forall(m3:fmap)(yff y:dart)(z:dart)(H:inv_hmap m3),
 isHexa m3 yff -> cA m3 one y = y ->
  exd m3 y -> exd m3 yff -> exd m3 z -> 
    let x := cA m3 zero y in
    let m4 := Merge m3 one yff y in
      yff = Iter (cF m3) 4 x ->
   degreef m4 z = 
      if expf_dec m3 x z then 3
      else degreef m3 z.
Proof.
intros.
assert (x = cF_1 m3 y).
 unfold cF_1 in |- *.
   rewrite H1 in |- *.
   fold x in |- *.
    tauto.
assert (y = Iter (cF m3) 1 x).
 simpl in |- *.
   rewrite H6 in |- *.
   rewrite cF_cF_1 in |- *.
   tauto.
  tauto.
  tauto.
assert (exd m3 x).
 unfold x in |- *.
   generalize (exd_cA m3 zero y).
    tauto.
assert (MF0Tr.MfM.degree = degreef).
  tauto.
unfold isHexa in H0.
  assert (degreef m3 x = degreef m3 yff).
 unfold degreef in |- *.
   apply (MF0Tr.MfM.expo_degree m3 x yff).
   tauto.
 unfold MF0Tr.MfM.expo in |- *.
   split.
   tauto.
 split with 4.
   symmetry  in |- *.
    tauto.
assert (y <> yff).
 intro.
   rewrite <- H11 in H5.
   assert (1 = 4).
  apply (MF0Tr.MfM.degree_unicity m3 x).
    tauto.
   tauto.
  rewrite H9 in |- *.
     lia.
  rewrite H9 in |- *.
     lia.
  assert (cF = MF0Tr.MfM.f).
    tauto.
  rewrite <- H12 in |- *.
    rewrite <- H7 in |- *.
     tauto.
 inversion H12.
generalize (degreev_fixpt m3 y H H2).
  intro.
  assert (degreev m3 y = 1).
  tauto.
clear H12.
  assert (~ expv m3 yff y).
 intro.
   assert (expv m3 y yff).
  apply expv_symm.
    tauto.
   tauto.
 unfold expv in H14.
   assert (MA1.MfcA.expo2 m3 y yff).
  generalize (MA1.MfcA.expo_expo2 m3 y yff).
     tauto.
 unfold MA1.MfcA.expo2 in H15.
   elim H15.
   intros.
   clear H15 H16.
   elim H17.
   intros i Hi.
   clear H17.
   elim Hi.
   intros.
   clear Hi.
   unfold degreev in H13.
   assert (i = 0).
  assert (MA1Tr.MfM.degree = MA1.MfcA.degree).
    tauto.
  rewrite H17 in H13.
     lia.
 rewrite H17 in H16.
   simpl in H16.
    tauto.
unfold m4 in |- *.
  assert (2 <= 4 <= degreef m3 yff).
 rewrite H0 in |- *.
    lia.
generalize
 (degreef_Merge1_split_summary_bis m3 yff y z 4
  H H3 H2 H12 H4 H5 H14).
  fold x in |- *.
  fold m4 in |- *.
  rewrite H0 in |- *.
  rewrite <- H1 in |- *.
  rewrite cA_1_cA in |- *.
 rewrite H7 in |- *.
   simpl in |- *.
   intros.
   elim (expf_dec m3 x z).
  intro.
    unfold expf in a.
    assert (MF.expo m3 yff x).
   apply MF.expo_symm.
     tauto.
   unfold MF.expo in |- *.
     split.
     tauto.
   split with 4.
     symmetry  in |- *.
      tauto.
  assert (MF.expo1 m3 yff x).
   generalize (MF.expo_expo1 m3 yff x).
      tauto.
  assert (MF.expo m3 yff z).
   apply MF.expo_trans with x.
     tauto.
    tauto.
  assert (MF.expo1 m3 yff z).
   generalize (MF.expo_expo1 m3 yff z).
      tauto.
  generalize (MF.expo_between_3 m3 yff x z H H17 H19).
    intros.
    assert (betweenf = MF.between).
    tauto.
  rewrite <- H21 in H20.
    assert (MF.f = cF).
    tauto.
  rewrite H22 in H20.
    assert (cF_1 = MF.f_1).
    tauto.
  rewrite <- H23 in H20.
    decompose [and] H15.
    clear H15.
    elim H20.
    tauto.
   tauto.
 unfold expof in H15.
   unfold expf in |- *.
    tauto.
 tauto.
 tauto.
Qed.

(* isTri_1: *)

Lemma isTri_Flip4_1: 
forall(m3:fmap)(yff y:dart)(z:dart)(H:inv_hmap m3),
 isHexa m3 yff -> cA m3 one y = y ->
  exd m3 y -> exd m3 yff -> exd m3 z -> 
    let x := cA m3 zero y in
    let m4 := Merge m3 one yff y in
      yff = Iter (cF m3) 4 x ->
     expf m3 x z -> isTri m4 z.
Proof.
intros.
generalize (degreef_Flip4 m3 yff y z 
  H H0 H1 H2 H3 H4 H5).
fold x in |- *.
elim (expf_dec m3 x z).
 unfold isTri in |- *.
 fold m4 in |- *.
    tauto.
 tauto.
Qed.

(* isTRi_2: *)

Lemma isTri_Flip4_2: 
forall(m3:fmap)(yff y:dart)(z:dart)(H:inv_hmap m3),
 isHexa m3 yff -> cA m3 one y = y ->
  exd m3 y -> exd m3 yff -> exd m3 z -> 
    let x := cA m3 zero y in
    let m4 := Merge m3 one yff y in
      yff = Iter (cF m3) 4 x ->
     ~expf m3 x z -> 
        isTri m3 z -> isTri m4 z.
Proof.
intros.
generalize (degreef_Flip4 m3 yff y z H H0 H1 H2 H3 H4 H5).
fold x in |- *.
elim (expf_dec m3 x z).
  tauto.
unfold isTri in |- *.
  fold m4 in |- *.
  unfold isTri in H7.
  rewrite H7 in |- *.
   tauto.
Qed.

(* cF_detail_1: *)

Lemma cF_Flip4_detail_1: 
forall(m3:fmap)(yff y:dart),
 inv_hmap m3 -> isMap m3 ->  
   exd m3 y -> exd m3 yff -> 
     isHexa m3 yff -> 
       cA m3 one y = y -> 
   let x := cF_1 m3 y in
   let xff := cF m3 y in
   let x_1 := cF m3 xff in
   let y_1 := cF m3 yff in 
   let m4 := Merge m3 one yff y in
  yff = Iter (cF m3) 4 x ->
    (xff = cF m4 y /\
       x_1 = cF m4 xff /\
         y = cF m4 x_1 /\
           yff = cF m4 x /\
             y_1 = cF m4 yff /\
                x = cF m4 y_1).
Proof.
intros.
assert (exd m3 x).
 unfold x in |- *.
   generalize (exd_cF_1 m3 y).
    tauto.
assert (exd m3 xff).
 unfold xff in |- *.
   generalize (exd_cF m3 y).
    tauto.
assert (exd m3 x_1).
 unfold x_1 in |- *.
   generalize (exd_cF m3 xff).
    tauto.
assert (exd m3 y_1).
 unfold y_1 in |- *.
   generalize (exd_cF m3 yff).
    tauto.
assert (y = cF m3 x).
 unfold x in |- *.
   rewrite cF_cF_1 in |- *.
   tauto.
  tauto.
  tauto.
assert (yff = cF m3 x_1).
 unfold x_1 in |- *.
   unfold xff in |- *.
   rewrite H10 in |- *.
   simpl in H5.
    tauto.
assert (degreef = MF.degree).
  tauto.
assert (cF = MF.f).
  tauto.
assert (degreef m3 x = 6).
 unfold isHexa in H3.
   rewrite <- H3 in |- *.
   rewrite H12 in |- *.
   apply MF.expo_degree.
   tauto.
 unfold MF.expo in |- *.
   split.
   tauto.
 split with 4.
   rewrite <- H13 in |- *.
   symmetry  in |- *.
    tauto.
assert (isHexa m3 x).
 unfold isHexa in |- *.
    tauto.
generalize (Hexa_diff_face m3 x H H6 H15).
   cbv zeta.
(* simpl in *.*)
  rewrite <- H10 in *.
  fold xff in |- *.
  fold x_1 in |- *.
  rewrite <- H11 in |- *.
  fold y_1 in |- *.
  intro.
  assert (degreee m3 y = 2).
 unfold isMap in H0.
   apply (H0 y H1).
generalize (degreee_invol_nofixpt m3 y H H1).
  intro.
  assert (cA m3 zero y <> y).
  tauto.
assert (cA m3 zero (cA m3 zero y) = y).
  tauto.
clear H18.
  assert (x = cA m3 zero y).
 unfold x in |- *.
   unfold cF_1 in |- *.
   rewrite H4 in |- *.
    tauto.
assert (x_1 = cF_1 m3 yff).
 rewrite H11 in |- *.
   rewrite cF_1_cF in |- *.
   tauto.
  tauto.
  tauto.
split.
unfold m4.
   rewrite cF_Flip4 in |- *.
  rewrite <- H18 in |- *.
    rewrite <- H21 in |- *.
    elim (eq_dart_dec x y).
    tauto.
  elim (eq_dart_dec x_1 y).
   intro.
     symmetry  in a.
      tauto.
  fold xff in |- *.
     tauto.
  tauto.
  tauto.
  tauto.
  tauto.
  tauto.
split.
 unfold m4 in |- *.
   rewrite cF_Flip4 in |- *.
  rewrite <- H18 in |- *.
    rewrite <- H21 in |- *.
    elim (eq_dart_dec x xff).
    tauto.
  elim (eq_dart_dec x_1 xff).
   intro.
     symmetry  in a.
      tauto.
  fold x_1 in |- *.
     tauto.
  tauto.
  tauto.
  tauto.
  tauto.
  tauto.
split.
 unfold m4 in |- *.
   rewrite cF_Flip4 in |- *.
  rewrite <- H18 in |- *.
    rewrite <- H21 in |- *.
    elim (eq_dart_dec x x_1).
    tauto.
  elim (eq_dart_dec x_1 x_1).
    tauto.
   tauto.
  tauto.
  tauto.
  tauto.
  tauto.
  tauto.
split.
 unfold m4 in |- *.
   rewrite cF_Flip4 in |- *.
  rewrite <- H18 in |- *.
    rewrite <- H21 in |- *.
    elim (eq_dart_dec x x).
    tauto.
   tauto.
  tauto.
  tauto.
  tauto.
  tauto.
  tauto.
split.
 unfold m4 in |- *.
   rewrite cF_Flip4 in |- *.
  rewrite <- H18 in |- *.
    rewrite <- H21 in |- *.
    elim (eq_dart_dec x yff).
    tauto.
  elim (eq_dart_dec x_1 yff).
    tauto.
  fold y_1 in |- *.
     tauto.
  tauto.
  tauto.
  tauto.
  tauto.
  tauto.
unfold m4 in |- *.
  rewrite cF_Flip4 in |- *.
 rewrite <- H18 in |- *.
   rewrite <- H21 in |- *.
   elim (eq_dart_dec x y_1).
   tauto.
 elim (eq_dart_dec x_1 y_1).
   tauto.
 intros.
   unfold y_1 in |- *.
   rewrite H5 in |- *.
   assert (Iter (cF m3) 6 x = x).
  rewrite H13 in |- *.
    rewrite <- H14 in |- *.
    rewrite H12 in |- *.
    apply MF.degree_per.
    tauto.
   tauto.
 simpl in H22.
   simpl in |- *.
   symmetry  in |- *.
    tauto.
 tauto.
 tauto.
 tauto.
 tauto.
 tauto.
Qed.

(* cF_detail_2: *)

Lemma cF_Flip4_detail_2: 
forall(m3:fmap)(yff y z:dart),
 inv_hmap m3 -> isMap m3 ->  
   exd m3 y -> exd m3 yff -> 
     isHexa m3 yff -> 
       cA m3 one y = y -> exd m3 z ->
   let x := cF_1 m3 y in
   let xff := cF m3 y in
   let x_1 := cF m3 xff in
   let y_1 := cF m3 yff in 
   let m4 := Merge m3 one yff y in
  yff = Iter (cF m3) 4 x ->
   x <> z -> xff <> z -> y <> z -> x_1 <> z -> 
     y_1 <> z -> yff <> z ->
        cF m4 z = cF m3 z.
Proof.
intros.
assert (exd m3 x).
 unfold x in |- *.
   generalize (exd_cF_1 m3 y).
    tauto.
assert (exd m3 xff).
 unfold xff in |- *.
   generalize (exd_cF m3 y).
    tauto.
assert (exd m3 x_1).
 unfold x_1 in |- *.
   generalize (exd_cF m3 xff).
    tauto.
assert (exd m3 y_1).
 unfold y_1 in |- *.
   generalize (exd_cF m3 yff).
    tauto.
assert (y = cF m3 x).
 unfold x in |- *.
   rewrite cF_cF_1 in |- *.
   tauto.
  tauto.
  tauto.
assert (y = cF m3 x).
 unfold x in |- *.
   rewrite cF_cF_1 in |- *.
   tauto.
  tauto.
  tauto.
assert (yff = cF m3 x_1).
 unfold x_1 in |- *.
   unfold xff in |- *.
   rewrite H17 in |- *.
   simpl in H6.
    tauto.
assert (degreef = MF.degree).
  tauto.
assert (cF = MF.f).
  tauto.
assert (degreef m3 x = 6).
 unfold isHexa in H3.
   rewrite <- H3 in |- *.
   rewrite H20 in |- *.
   apply MF.expo_degree.
   tauto.
 unfold MF.expo in |- *.
   split.
   tauto.
 split with 4.
   rewrite <- H21 in |- *.
   symmetry  in |- *.
    tauto.
assert (isHexa m3 x).
 unfold isHexa in |- *.
    tauto.
generalize (Hexa_diff_face m3 x H H13 H23).
  cbv zeta.
  rewrite <- H17 in |- *.
  fold xff in |- *.
  fold x_1 in |- *.
  rewrite <- H19 in |- *.
  fold y_1 in |- *.
  intro.
  assert (degreee m3 y = 2).
 unfold isMap in H0.
   apply (H0 y H1).
generalize (degreee_invol_nofixpt m3 y H H1).
  intro.
  assert (cA m3 zero y <> y).
  tauto.
assert (cA m3 zero (cA m3 zero y) = y).
  tauto.
clear H26.
  assert (x = cA m3 zero y).
 unfold x in |- *.
   unfold cF_1 in |- *.
   rewrite H4 in |- *.
    tauto.
assert (x_1 = cF_1 m3 yff).
 rewrite H19 in |- *.
   rewrite cF_1_cF in |- *.
   tauto.
  tauto.
  tauto.
unfold m4 in |- *.
  rewrite cF_Flip4 in |- *.
 rewrite <- H26 in |- *.
   rewrite <- H29 in |- *.
   elim (eq_dart_dec x z).
   tauto.
 elim (eq_dart_dec x_1 z).
   tauto.
  tauto.
 tauto.
 tauto.
 tauto.
 tauto.
 tauto.
Qed.

(*====================================================
       CHANGING THE EMBEDDING OF DARTS: Chp  
         - DOES NOT CHANGE THE TOPOLOGY
====================================================*)

(* Chp CHANGES THE EMBEDDING OF x BY p: *)

Fixpoint Chp (m:fmap)(z:dart)(pz:point){struct m}:=
  match m with
    V => V
  | I m0 x t p =>
     if eq_dart_dec x z then I m0 x t pz
     else I (Chp m0 z pz) x t p
  | L m0 k x y => L (Chp m0 z pz) k x y
  end.

(* OK: *)

Lemma fpoint_Chp: forall(m:fmap)(z t:dart)(pz:point),
 exd m z -> 
  fpoint (Chp m z pz) t = 
    if eq_dart_dec z t then pz else fpoint m t.
Proof.
induction m.
 simpl in |- *.
    tauto.
simpl in |- *.
  intros.
  elim (eq_dart_dec d z).
 simpl in |- *.
   elim (eq_dart_dec d t0).
  intros.
    elim (eq_dart_dec z t0).
    tauto.
  rewrite <- a in |- *.
    rewrite <- a0 in |- *.
     tauto.
 elim (eq_dart_dec z t0).
  intros.
    rewrite <- a in b.
     tauto.
  tauto.
intro.
  assert (exd m z).
  tauto.
simpl in |- *.
  elim (eq_dart_dec d t0).
 elim (eq_dart_dec z t0).
  intros.
    rewrite <- a in a0;  tauto.
  tauto.
elim (eq_dart_dec z t0).
 intros.
   rewrite IHm in |- *.
  elim (eq_dart_dec z t0).
    tauto.
   tauto.
  tauto.
rewrite IHm in |- *.
 elim (eq_dart_dec z t0).
   tauto.
  tauto.
 tauto.
simpl in |- *.
  intros.
  apply IHm.
   tauto.
Qed.

(* OK: *)

Lemma exd_Chp: forall(m:fmap)(u:dart)(pu:point)(z:dart),
   exd (Chp m u pu) z <-> exd m z.
Proof.
intros.
induction m.
 simpl in |- *.
    tauto.
simpl in |- *.
  elim (eq_dart_dec d u).
 simpl in |- *.
    tauto.
simpl in |- *.
   tauto.
simpl in |- *.
   tauto.
Qed.

(* OK: *)

Lemma A_Chp: 
forall(m:fmap)(k:dim)(u:dart)(pu:point)(z:dart),
   A (Chp m u pu) k z = A m k z.
Proof.
intros.
induction m.
 simpl in |- *.
    tauto.
simpl in |- *.
  elim (eq_dart_dec d u).
 simpl in |- *.
    tauto.
simpl in |- *.
   tauto.
simpl in |- *.
  rewrite IHm in |- *.
   tauto.
Qed.

(* OK: *)

Lemma A_1_Chp: 
 forall(m:fmap)(k:dim)(u:dart)(pu:point)(z:dart),
   A_1 (Chp m u pu) k z = A_1 m k z.
Proof.
intros.
induction m.
 simpl in |- *.
    tauto.
simpl in |- *.
  elim (eq_dart_dec d u).
 simpl in |- *.
    tauto.
simpl in |- *.
   tauto.
simpl in |- *.
  rewrite IHm in |- *.
   tauto.
Qed.

(* OK: *)

Lemma succ_Chp: 
  forall(m:fmap)(u:dart)(pu:point)(k:dim)(z:dart),
   succ (Chp m u pu) k z <-> succ m k z.
Proof.
unfold succ in |- *.
intros.
rewrite A_Chp in |- *.
 tauto.
Qed.

(* OK: *)

Lemma pred_Chp: 
  forall(m:fmap)(u:dart)(pu:point)(k:dim)(z:dart),
   pred (Chp m u pu) k z <-> pred m k z.
Proof.
unfold pred in |- *.
intros.
rewrite A_1_Chp in |- *.
 tauto.
Qed.

(* OK: *)

Lemma cA_cA_1_Chp: 
 forall(m:fmap)(k:dim)(u:dart)(pu:point)(z:dart),
   cA (Chp m u pu) k z = cA m k z
  /\ cA_1 (Chp m u pu) k z = cA_1 m k z.
Proof.
intros.
generalize z.
clear z.
induction m.
 simpl in |- *.
    tauto.
simpl in |- *.
  intro.
  elim (eq_dart_dec d u).
 simpl in |- *.
   elim (eq_dart_dec d z).
   tauto.
  tauto.
simpl in |- *.
  assert
   (cA (Chp m u pu) k z = cA m k z /\ 
      cA_1 (Chp m u pu) k z = cA_1 m k z).
 apply IHm.
decompose [and] H.
  rewrite H0 in |- *; rewrite H1 in |- *.
   tauto.
assert (forall z : dart, 
  cA (Chp m u pu) k z = cA m k z).
 intro.
   generalize (IHm z).
    tauto.
assert (forall z : dart,
  cA_1 (Chp m u pu) k z = cA_1 m k z).
 intro.
   generalize (IHm z).
    tauto.
clear IHm.
  intro.
  simpl in |- *.
  elim (eq_dim_dec d k).
 intro.
   rewrite H0 in |- *.
   rewrite H0 in |- *.
   rewrite H in |- *.
   rewrite H in |- *.
    tauto.
rewrite H0 in |- *.
  rewrite H in |- *.
   tauto.
Qed.

(* OK: *)

Lemma cA_Chp: 
 forall(m:fmap)(k:dim)(u:dart)(pu:point)(z:dart),
   cA (Chp m u pu) k z = cA m k z.
Proof.
intros.
generalize (cA_cA_1_Chp m k u pu z).
 tauto.
Qed.

(* OK: *)

Lemma cA_1_Chp: 
 forall(m:fmap)(k:dim)(u:dart)(pu:point)(z:dart),
   cA_1 (Chp m u pu) k z = cA_1 m k z.
Proof.
intros.
generalize (cA_cA_1_Chp m k u pu z).
 tauto.
Qed.

(* OK: *)

Lemma cF_Chp: 
 forall(m:fmap)(u:dart)(pu:point)(z:dart),
   cF (Chp m u pu) z = cF m z.
Proof.
unfold cF in |- *.
intros.
rewrite cA_1_Chp in |- *.
rewrite cA_1_Chp in |- *.
 tauto.
Qed.

(* OK: *)

Lemma cF_1_Chp: 
 forall(m:fmap)(u:dart)(pu:point)(z:dart),
   cF_1 (Chp m u pu) z = cF_1 m z.
Proof.
intros.
unfold cF_1 in |- *.
rewrite cA_Chp in |- *.
rewrite cA_Chp in |- *.
 tauto.
Qed.

(* OK: *)

Lemma nd_Chp: 
 forall(m:fmap)(u:dart)(pu:point),
   nd (Chp m u pu) = nd m.
Proof.
intros.
induction m.
 simpl in |- *.
    tauto.
simpl in |- *.
  elim (eq_dart_dec d u).
 simpl in |- *.
    tauto.
simpl in |- *.
  rewrite IHm in |- *.
   tauto.
simpl in |- *.
   tauto.
Qed.

(* OK: *)

Lemma Iter_cA_Chp: forall(m:fmap)(k:dim)(u:dart)(pu:point)(i:nat)(z:dart),
   Iter (cA (Chp m u pu) k) i z =  Iter (cA m k) i z.
Proof.
intros.
induction i.
 simpl in |- *.
    tauto.
simpl in |- *.
  rewrite IHi in |- *.
  rewrite cA_Chp in |- *.
   tauto.
Qed.

(* OK: *)

Lemma Iter_cA0_Chp: forall(m:fmap)(u:dart)(pu:point)(i:nat)(z:dart),
   Iter (MA0.MfcA.f (Chp m u pu)) i z =  
       Iter (MA0.MfcA.f m) i z.
Proof.
intros.
induction i.
 simpl in |- *.
    tauto.
simpl in |- *.
  rewrite IHi in |- *.
  assert
   (MA0.MfcA.f (Chp m u pu) (Iter (MA0.MfcA.f m) i z) =
    cA (Chp m u pu) zero (Iter (MA0.MfcA.f m) i z)).
  tauto.
rewrite H in |- *.
  rewrite cA_Chp in |- *.
   tauto.
Qed.

(* OK: *)

Lemma Iter_cA1_Chp: forall(m:fmap)(u:dart)(pu:point)(i:nat)(z:dart),
   Iter (MA1.MfcA.f (Chp m u pu)) i z =  
       Iter (MA1.MfcA.f m) i z.
Proof.
intros.
induction i.
 simpl in |- *.
    tauto.
simpl in |- *.
  rewrite IHi in |- *.
  assert
   (MA1.MfcA.f (Chp m u pu) (Iter (MA1.MfcA.f m) i z) =
    cA (Chp m u pu) one (Iter (MA1.MfcA.f m) i z)).
  tauto.
rewrite H in |- *.
  rewrite cA_Chp in |- *.
   tauto.
Qed.

(* OK: *)

Lemma Iter_cA_1_Chp: forall(m:fmap)(k:dim)(u:dart)(pu:point)(i:nat)(z:dart),
 Iter (cA_1 (Chp m u pu) k) i z =  Iter (cA_1 m k) i z.
Proof.
intros.
induction i.
 simpl in |- *.
    tauto.
simpl in |- *.
  rewrite IHi in |- *.
  rewrite cA_1_Chp in |- *.
   tauto.
Qed.

(* OK: *)

Lemma Iter_cF_Chp: forall(m:fmap)(u:dart)(pu:point)(i:nat)(z:dart),
   Iter (cF (Chp m u pu)) i z =  Iter (cF m) i z.
Proof.
intros.
induction i.
 simpl in |- *.
    tauto.
simpl in |- *.
  rewrite IHi in |- *.
  rewrite cF_Chp in |- *.
   tauto.
Qed.

(* OK: *)

Lemma Iter_cF_1_Chp: forall(m:fmap)(u:dart)(pu:point)(i:nat)(z:dart),
   Iter (cF_1 (Chp m u pu)) i z =  Iter (cF_1 m) i z.
Proof.
intros.
induction i.
 simpl in |- *.
    tauto.
simpl in |- *.
  rewrite IHi in |- *.
  rewrite cF_1_Chp in |- *.
   tauto.
Qed.

(* OK: *)

Lemma Iter_McF_Chp: forall(m:fmap)(u:dart)(pu:point)(i:nat)(z:dart),
   Iter (cF (Chp m u pu)) i z =  Iter (cF m) i z.
Proof.
intros.
induction i.
 simpl in |- *.
    tauto.
simpl in |- *.
  rewrite IHi in |- *.
  rewrite cF_Chp in |- *.
   tauto.
Qed.

(* OK: *)

Lemma expe_Chp:
forall(m:fmap)(u:dart)(pu:point)(z t:dart),
  expe (Chp m u pu) z t <-> expe m z t.
Proof.
intros.
unfold expe in |- *.
unfold MA0.MfcA.expo in |- *.
generalize (exd_Chp m u pu z).
cut
 ((exists i : nat, 
 Iter (MA0.MfcA.f (Chp m u pu)) i z = t) <->
  (exists i : nat, Iter (MA0.MfcA.f m) i z = t)).
  tauto.
split.
 intro.
   elim H.
   intros i Hi.
   split with i.
   rewrite Iter_cA0_Chp in Hi.
    tauto.
intro.
  elim H.
  intros i Hi.
  split with i.
  rewrite Iter_cA0_Chp in |- *.
   tauto.
Qed.

(* OK: *)

Lemma expv_Chp:
forall(m:fmap)(u:dart)(pu:point)(z t:dart),
  expv (Chp m u pu) z t <-> expv m z t.
Proof.
intros.
unfold expv in |- *.
unfold MA1.MfcA.expo in |- *.
generalize (exd_Chp m u pu z).
cut
 ((exists i : nat, 
 Iter (MA1.MfcA.f (Chp m u pu)) i z = t) <->
  (exists i : nat, Iter (MA1.MfcA.f m) i z = t)).
  tauto.
split.
 intro.
   elim H.
   intros i Hi.
   split with i.
   rewrite Iter_cA1_Chp in Hi.
    tauto.
intro.
  elim H.
  intros i Hi.
  split with i.
  rewrite Iter_cA1_Chp in |- *.
   tauto.
Qed.

(* OK: *)

Lemma inv_hmap_Chp: forall(m:fmap)(u:dart)(pu:point),
  inv_hmap m <-> inv_hmap (Chp m u pu).
Proof.
induction m.
 simpl in |- *.
    tauto.
simpl in |- *.
  intros.
  elim (eq_dart_dec d u).
 simpl in |- *.
    tauto.
simpl in |- *.
  unfold prec_I in |- *.
  generalize (exd_Chp m u pu d).
  generalize (IHm u pu).
   tauto.
intros.
  simpl in |- *.
  assert (inv_hmap m <-> inv_hmap (Chp m u pu)).
 apply IHm.
cut (prec_L m d d0 d1 <-> prec_L (Chp m u pu) d d0 d1).
  tauto.
unfold prec_L in |- *.
  generalize (exd_Chp m u pu d0).
  generalize (exd_Chp m u pu d1).
  generalize (succ_Chp m u pu d d0).
  generalize (pred_Chp m u pu d d1).
  rewrite cA_Chp in |- *.
   tauto.
Qed.

(* OK: *)

Lemma expf_Chp:
forall(m:fmap)(u:dart)(pu:point)(z t:dart),
  expf (Chp m u pu) z t <-> expf m z t.
Proof.
intros.
unfold expf in |- *.
generalize (inv_hmap_Chp m u pu).
intro.
cut (MF.expo (Chp m u pu) z t <-> MF.expo m z t).
  tauto.
unfold MF.expo in |- *.
  generalize (exd_Chp m u pu z).
  intro.
  cut
   ((exists i : nat, 
   Iter (MF.f (Chp m u pu)) i z = t) <->
    (exists i : nat, Iter (MF.f m) i z = t)).
  tauto.
assert (MF.f = cF).
  tauto.
rewrite H1 in |- *.
  split.
 intro.
   elim H2.
   intros i Hi.
   split with i.
   rewrite Iter_McF_Chp in Hi.
    tauto.
intro.
  elim H2.
  intros i Hi.
  split with i.
  rewrite Iter_McF_Chp in |- *.
   tauto.
Qed.

(* OK: *)

Lemma ne_Chp:forall(m:fmap)(u:dart)(pu:point),
    ne (Chp m u pu) = ne m. 
Proof.
intros.
induction m.
 simpl in |- *.
    tauto.
simpl in |- *.
  elim (eq_dart_dec d u).
 simpl in |- *.
    tauto.
simpl in |- *.
  rewrite IHm in |- *.
   tauto.
induction d.
 simpl in |- *.
   rewrite IHm in |- *.
    tauto.
simpl in |- *.
   tauto.
Qed.

(* OK: *)

Lemma nv_Chp:forall(m:fmap)(u:dart)(pu:point),
    nv (Chp m u pu) = nv m. 
Proof.
intros.
induction m.
 simpl in |- *.
    tauto.
simpl in |- *.
  elim (eq_dart_dec d u).
 simpl in |- *.
    tauto.
simpl in |- *.
  rewrite IHm in |- *.
   tauto.
induction d.
 simpl in |- *.
    tauto.
simpl in |- *.
  rewrite IHm in |- *.
   tauto.
Qed.

(* OK: *)

Lemma nf_Chp:forall(m:fmap)(u:dart)(pu:point),
    nf (Chp m u pu) = nf m. 
Proof.
intros.
induction m.
 simpl in |- *.
    tauto.
simpl in |- *.
  elim (eq_dart_dec d u).
 simpl in |- *.
    tauto.
simpl in |- *.
  rewrite IHm in |- *.
   tauto.
induction d.
 simpl in |- *.
   generalize (expf_Chp m u pu (cA_1 m one d0) d1).
   intro.
   rewrite cA_1_Chp in |- *.
   rewrite IHm in |- *.
   elim (expf_dec (Chp m u pu) (cA_1 m one d0)).
  elim (expf_dec m (cA_1 m one d0) d1).
    tauto.
   tauto.
 elim (expf_dec m (cA_1 m one d0) d1).
   tauto.
  tauto.
simpl in |- *.
  rewrite cA_Chp in |- *.
  rewrite IHm in |- *.
  generalize (expf_Chp m u pu d0 (cA m zero d1)).
  intro.
  elim (expf_dec (Chp m u pu) d0 (cA m zero d1)).
 elim (expf_dec m d0 (cA m zero d1)).
   tauto.
  tauto.
elim (expf_dec m d0 (cA m zero d1)).
  tauto.
 tauto.
Qed.

(* OK: *)

Lemma eqc_Chp:
forall(m:fmap)(u:dart)(pu:point)(z t:dart),
  eqc (Chp m u pu) z t <-> eqc m z t.
Proof.
intros m u pu.
induction m.
 simpl in |- *.
    tauto.
simpl in |- *.
  elim (eq_dart_dec d u).
 simpl in |- *.
    tauto.
simpl in |- *.
  intros.
  generalize (IHm z t0).
   tauto.
intros.
  simpl in |- *.
  generalize (IHm z t).
  generalize (IHm z d0).
  generalize (IHm z d1).
  generalize (IHm d0 t).
  generalize (IHm d1 t).
   tauto.
Qed.

(* OK: *)

Lemma nc_Chp: forall(m:fmap)(u:dart)(pu:point),
   nc (Chp m u pu) = nc m.
Proof.
intros.
induction m.
 simpl in |- *.
    tauto.
simpl in |- *.
  elim (eq_dart_dec d u).
 simpl in |- *.
    tauto.
simpl in |- *.
  rewrite IHm in |- *.
   tauto.
simpl in |- *.
  rewrite IHm in |- *.
  generalize (eqc_Chp m u pu d0 d1).
  intro.
  elim (eqc_dec (Chp m u pu) d0 d1).
 elim (eqc_dec m d0 d1);  tauto.
elim (eqc_dec m d0 d1).
  tauto.
 tauto.
Qed.

Open Scope nat_scope.

(* OK: *)

Lemma ndN_Chp: forall(m:fmap)(u:dart)(pu:point),
   ndN (Chp m u pu) = ndN m.
Proof.
intros.
induction m.
 simpl in |- *.
    tauto.
simpl in |- *.
  elim (eq_dart_dec d u).
 simpl in |- *.
    tauto.
simpl in |- *.
  generalize (exd_Chp m u pu d).
  intros.
  elim (exd_dec (Chp m u pu) d).
 elim (exd_dec m d).
   tauto.
  tauto.
elim (exd_dec m d).
  tauto.
simpl in |- *.
  rewrite IHm in |- *.
   tauto.
simpl in |- *.
   tauto.
Qed.

(* OK: *)

Lemma degreee_Chp_aux: 
  forall(m:fmap)(u:dart)(pu:point)(z:dart)(n:nat),
   inv_hmap m -> exd m z ->
 n <= ndN m ->
  MA0Tr.MfM.degree_aux 
    (Chp m u pu) z (ndN m - n) =
        MA0Tr.MfM.degree_aux m z (ndN m - n).
Proof.
intros.
induction n.
 assert (ndN m - 0 = ndN m).
   lia.
 rewrite H2 in |- *.
   rewrite MA0Tr.MfM.degree_aux_equation in |- *.
   rewrite 
 (MA0Tr.MfM.degree_aux_equation m z (ndN m)) in |- *.
   rewrite Iter_cA0_Chp in |- *.
   rewrite ndN_Chp in |- *.
   elim (Arith.Compare_dec.le_lt_dec (ndN m) (ndN m)).
  elim (Nat.eq_dec (ndN m) (ndN m)).
    tauto.
   tauto.
  tauto.
rewrite MA0Tr.MfM.degree_aux_equation in |- *.
  rewrite 
 (MA0Tr.MfM.degree_aux_equation m z (ndN m - S n))
   in |- *.
  rewrite ndN_Chp in |- *.
  assert (ndN m - S n + 1 = ndN m - n).
  lia.
rewrite H2 in |- *.
  rewrite Iter_cA0_Chp in |- *.
  rewrite IHn in |- *.
  tauto.
 lia.
Qed.

(* OK: *)

Lemma degreee_Chp:
forall(m:fmap)(u:dart)(pu:point)(z:dart),
  inv_hmap m -> exd m z ->
    degreee (Chp m u pu) z = degreee m z.
Proof.
intros.
unfold degreee in |- *.
unfold MA0Tr.MfM.degree in |- *.
assert (0 < ndN m).
 apply MA1.MfcA.ndN_pos with z.
    tauto.
assert (1 = ndN m - (ndN m - 1)).
  lia.
rewrite H2 in |- *.
  apply (degreee_Chp_aux m u pu z (ndN m - 1) H H0).
   lia.
Qed.

(* OK: *)

Lemma degreev_Chp_aux: 
  forall(m:fmap)(u:dart)(pu:point)(z:dart)(n:nat),
   inv_hmap m -> exd m z ->
 n <= ndN m ->
  MA1Tr.MfM.degree_aux 
    (Chp m u pu) z (ndN m - n) =
        MA1Tr.MfM.degree_aux m z (ndN m - n).
Proof.
intros.
induction n.
 assert (ndN m - 0 = ndN m).
   lia.
 rewrite H2 in |- *.
   rewrite MA1Tr.MfM.degree_aux_equation in |- *.
   rewrite 
 (MA1Tr.MfM.degree_aux_equation m z (ndN m)) in |- *.
   rewrite Iter_cA1_Chp in |- *.
   rewrite ndN_Chp in |- *.
   elim (Arith.Compare_dec.le_lt_dec (ndN m) (ndN m)).
  elim (Nat.eq_dec (ndN m) (ndN m)).
    tauto.
   tauto.
  tauto.
rewrite MA1Tr.MfM.degree_aux_equation in |- *.
  rewrite 
 (MA1Tr.MfM.degree_aux_equation m z (ndN m - S n))
   in |- *.
  rewrite ndN_Chp in |- *.
  assert (ndN m - S n + 1 = ndN m - n).
  lia.
rewrite H2 in |- *.
  rewrite Iter_cA1_Chp in |- *.
  rewrite IHn in |- *.
  tauto.
 lia.
Qed.

(* OK: *)

Lemma degreev_Chp:
forall(m:fmap)(u:dart)(pu:point)(z:dart),
  inv_hmap m -> exd m z ->
    degreev (Chp m u pu) z = degreev m z.
Proof.
intros.
unfold degreev in |- *.
unfold MA1Tr.MfM.degree in |- *.
assert (0 < ndN m).
 apply MA1.MfcA.ndN_pos with z.
    tauto.
assert (1 = ndN m - (ndN m - 1)).
  lia.
rewrite H2 in |- *.
  apply (degreev_Chp_aux m u pu z (ndN m - 1) H H0).
   lia.
Qed.

(* OK: *)

Lemma degreef_Chp_aux: 
  forall(m:fmap)(u:dart)(pu:point)(z:dart)(n:nat),
   inv_hmap m -> exd m z ->
 n <= ndN m ->
  MF.degree_aux 
    (Chp m u pu) z (ndN m - n) =
        MF.degree_aux m z (ndN m - n).
Proof.
intros.
induction n.
 assert (ndN m - 0 = ndN m).
   lia.
 rewrite H2 in |- *.
   rewrite MF.degree_aux_equation in |- *.
   rewrite 
 (MF.degree_aux_equation m z (ndN m)) in |- *.
   rewrite Iter_McF_Chp in |- *.
   rewrite ndN_Chp in |- *.
   elim (Arith.Compare_dec.le_lt_dec (ndN m) (ndN m)).
  elim (Nat.eq_dec (ndN m) (ndN m)).
    tauto.
   tauto.
  tauto.
rewrite MF.degree_aux_equation in |- *.
  rewrite
 (MF.degree_aux_equation m z (ndN m - S n)) in |- *.
  rewrite ndN_Chp in |- *.
  assert (ndN m - S n + 1 = ndN m - n).
  lia.
rewrite H2 in |- *.
  rewrite Iter_McF_Chp in |- *.
  rewrite IHn in |- *.
  tauto.
 lia.
Qed.

(* OK: *)

Lemma degreef_Chp:
forall(m:fmap)(u:dart)(pu:point)(z:dart),
 inv_hmap m -> exd m z ->
  degreef (Chp m u pu) z = degreef m z.
Proof.
intros.
unfold degreef in |- *.
assert (MF0Tr.MfM.degree = MF.degree).
  tauto.
rewrite H1 in |- *.
  unfold MF.degree in |- *.
  assert (0 < ndN m).
 apply MA1.MfcA.ndN_pos with z.
    tauto.
assert (1 = ndN m - (ndN m - 1)).
  lia.
rewrite H3 in |- *.
  apply (degreef_Chp_aux m u pu z (ndN m - 1) H H0).
   lia.
Qed.

(*==================================================
             Flip5 AND Flip6
==================================================*)

(* OK: *)

Lemma cA_Flip5:
  forall(m4:fmap)(k:dim)(x:dart)(pxff:point)(z:dart),
    cA (Chp m4 x pxff) k z = cA m4 k z.
Proof.
intros.
rewrite cA_Chp in |- *.
 tauto.
Qed.
 
(* OK: *)

Lemma cA_1_Flip5:
  forall(m4:fmap)(k:dim)(x:dart)(pxff:point)(z:dart),
    cA_1 (Chp m4 x pxff) k z = cA_1 m4 k z.
Proof.
intros.
rewrite cA_1_Chp in |- *.
 tauto.
Qed.
 
(* OK: *)

Lemma degreee_Flip5:
  forall(m4:fmap)(x:dart)(pxff:point)(z:dart),
   inv_hmap m4 -> exd m4 z ->
    degreee (Chp m4 x pxff) z = degreee m4 z.
Proof.
apply degreee_Chp.
Qed.

(* OK: *)

Lemma degreev_Flip5:
  forall(m4:fmap)(x:dart)(pxff:point)(z:dart),
   inv_hmap m4 -> exd m4 z ->
    degreev (Chp m4 x pxff) z = degreev m4 z.
Proof.
apply degreev_Chp.
Qed.

(* OK: *)

Lemma cF_Flip5:
  forall(m4:fmap)(x:dart)(pxff:point)(z:dart),
     cF (Chp m4 x pxff) z = cF m4 z.
Proof.
intros.
rewrite cF_Chp in |- *.
 tauto.
Qed.

(* OK: *)

Lemma cF_1_Flip5:
  forall(m4:fmap)(x:dart)(pxff:point)(z:dart),
     cF_1 (Chp m4 x pxff) z = cF_1 m4 z.
Proof.
intros.
rewrite cF_1_Chp in |- *.
 tauto.
Qed.

(* OK: *)

Lemma degreef_Flip5:
  forall(m4:fmap)(x:dart)(pxff:point)(z:dart),
   inv_hmap m4 -> exd m4 z ->
    degreef (Chp m4 x pxff) z = degreef m4 z.
Proof.
apply degreef_Chp.
Qed.

(* OK: *)

Lemma inv_hmap_Flip5:
 forall(m4:fmap)(x:dart)(pxff:point),
    inv_hmap m4 -> 
       inv_hmap (Chp m4 x pxff).
Proof.
intros.
generalize (inv_hmap_Chp m4 x pxff).
 tauto.
Qed.

(* OK: *)

Lemma isMap_Flip5:
 forall(m4:fmap)(x:dart)(pxff:point),
    inv_hmap m4 -> isMap m4 -> 
       isMap (Chp m4 x pxff).
Proof.
unfold isMap in |- *.
intros.
assert (exd m4 z).
 generalize (exd_Chp m4 x pxff z).
    tauto.
rewrite degreee_Chp in |- *.
 apply H0.
    tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma isTriangulation_Flip5:
 forall(m4:fmap)(x:dart)(pxff:point),
    inv_hmap m4 -> isTriangulation m4 -> 
       isTriangulation (Chp m4 x pxff).
Proof.
unfold isTri in |- *.
unfold isTriangulation in |- *.
unfold isTri in |- *.
intros.
assert (exd m4 z).
 generalize (exd_Chp m4 x pxff z).
    tauto.
rewrite degreef_Chp in |- *.
 apply H0.
    tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma isPoly_Flip5:
 forall(m4:fmap)(x:dart)(pxff:point),
     inv_hmap m4 -> isPoly m4 -> 
       isPoly (Chp m4 x pxff).
Proof.
unfold isPoly in |- *.
intros.
assert (exd m4 z).
 generalize (exd_Chp m4 x pxff z).
    tauto.
rewrite degreev_Chp in |- *.
 apply H0.
    tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma inv_Triangulation_Flip5:
 forall(m4:fmap)(x:dart)(pxff:point),
    inv_Triangulation m4 -> 
       inv_Triangulation (Chp m4 x pxff).
Proof.
unfold inv_Triangulation in |- *.
intros.
split.
 apply inv_hmap_Flip5.
    tauto.
split.
 apply isMap_Flip5.
   tauto.
  tauto.
split.
 apply isPoly_Flip5.
   tauto.
  tauto.
apply isTriangulation_Flip5.
  tauto.
 tauto.
Qed.

(* OK: *)

Lemma cA_Flip6:
  forall(m5:fmap)(k:dim)(y:dart)(pyff:point)(z:dart),
    cA (Chp m5 y pyff) k z = cA m5 k z.
Proof.
intros.
rewrite cA_Chp in |- *.
 tauto.
Qed.

(* OK: *)

Lemma cA_1_Flip6:
  forall(m5:fmap)(k:dim)(y:dart)(pyff:point)(z:dart),
    cA_1 (Chp m5 y pyff) k z = cA_1 m5 k z.
Proof.
intros.
rewrite cA_1_Chp in |- *.
 tauto.
Qed.

(* OK: *)

Lemma degreee_Flip6:
  forall(m5:fmap)(y:dart)(pyff:point)(z:dart),
   inv_hmap m5 -> exd m5 z ->
    degreee (Chp m5 y pyff) z = degreee m5 z.
Proof.
apply degreee_Chp.
Qed.

(* OK: *)

Lemma degreev_Flip6:
  forall(m5:fmap)(y:dart)(pyff:point)(z:dart),
   inv_hmap m5 -> exd m5 z ->
    degreev (Chp m5 y pyff) z = degreev m5 z.
Proof.
apply degreev_Chp.
Qed.

(* OK: *)

Lemma cF_Flip6:
  forall(m5:fmap)(y:dart)(pyff:point)(z:dart),
     cF (Chp m5 y pyff) z = cF m5 z.
Proof.
intros.
rewrite cF_Chp in |- *.
 tauto.
Qed.
 
(* OK: *)

Lemma cF_1_Flip6:
  forall(m5:fmap)(y:dart)(pyff:point)(z:dart),
     cF_1 (Chp m5 y pyff) z = cF_1 m5 z.
Proof.
intros.
rewrite cF_1_Chp in |- *.
 tauto.
Qed.

(* OK: *)

Lemma degreef_Flip6:
  forall(m5:fmap)(y:dart)(pyff:point)(z:dart),
   inv_hmap m5 -> exd m5 z ->
    degreef (Chp m5 y pyff) z = degreef m5 z.
Proof.
apply degreef_Chp.
Qed.

(* OK: *)

Lemma inv_hmap_Flip6:
 forall(m5:fmap)(y:dart)(pyff:point),
    inv_hmap m5 -> 
       inv_hmap (Chp m5 y pyff).
Proof.
intros.
generalize (inv_hmap_Chp m5 y pyff).
 tauto.
Qed.

(* OK: *)

Lemma isMap_Flip6:
 forall(m5:fmap)(y:dart)(pyff:point),
    inv_hmap m5 -> isMap m5 -> 
       isMap (Chp m5 y pyff).
Proof.
unfold isMap in |- *.
intros.
assert (exd m5 z).
 generalize (exd_Chp m5 y pyff z).
    tauto.
rewrite degreee_Chp in |- *.
 apply H0.
    tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma isPoly_Flip6:
 forall(m5:fmap)(y:dart)(pyff:point),
     inv_hmap m5 -> isPoly m5 -> 
       isPoly (Chp m5 y pyff).
Proof.
unfold isPoly in |- *.
intros.
assert (exd m5 z).
 generalize (exd_Chp m5 y pyff z).
    tauto.
rewrite degreev_Chp in |- *.
 apply H0.
    tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma isTriangulation_Flip6:
 forall(m5:fmap)(y:dart)(pyff:point),
    inv_hmap m5 -> isTriangulation m5 -> 
       isTriangulation (Chp m5 y pyff).
Proof.
unfold isTri in |- *.
unfold isTriangulation in |- *.
unfold isTri in |- *.
intros.
assert (exd m5 z).
 generalize (exd_Chp m5 y pyff z).
    tauto.
rewrite degreef_Chp in |- *.
 apply H0.
    tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma inv_Triangulation_Flip6:
 forall(m5:fmap)(y:dart)(pyff:point),
    inv_Triangulation m5 -> 
       inv_Triangulation (Chp m5 y pyff).
Proof.
unfold inv_Triangulation in |- *.
intros.
split.
 apply inv_hmap_Flip6.
    tauto.
split.
 apply isMap_Flip6.
   tauto.
  tauto.
split.
 apply isPoly_Flip6.
   tauto.
  tauto.
apply isTriangulation_Flip6.
  tauto.
 tauto.
Qed.

(*==================================================
    Flip SUMMARY - PART 1: exd, inv_hmap, isMap
====================================================*)

(* Flip CUT IN Flip_topo AND Flip_emb, Precondition: *)

Definition Flip_topo(m:fmap)(x:dart):fmap:=
  let x_1 := cA_1 m one x in
  let y := cA m zero x in
  let y_1 := cA_1 m one y in
  let xff := cF m y_1 in
  let yff := cF m x_1 in
  let m1 := Split m one x x_1 in
  let m2 := Split m1 one y y_1 in 
  let m3 := Merge m2 one xff x in 
  let m4 := Merge m3 one yff y in m4.

Definition Flip_emb(m4:fmap)(x y xff yff:dart):fmap:=
  let pxff := fpoint m4 xff in
  let pyff := fpoint m4 yff in
  let m5 := Chp m4 x pxff in
  let m6 := Chp m5 y pyff in m6.

Definition Flip(m:fmap)(x:dart):fmap:=
  let x_1 := cA_1 m one x in
  let y := cA m zero x in
  let y_1 := cA_1 m one y in
  let xff := cF m y_1 in
  let yff := cF m x_1 in
  let m4 := Flip_topo m x in
  let m6 := Flip_emb m4 x y xff yff in m6.

Definition prec_Flip(m:fmap)(x:dart):Prop:=
  let y:= cA m zero x in exd m x /\ 
      ~ expf m x y /\ ~ expv m x y /\
         3 <= degreev m x /\ 3 <= degreev m y.

Lemma exd_Flip_1_4: forall(m:fmap)(x z:dart),
  let x_1 := cA_1 m one x in
  let y := cA m zero x in
  let y_1 := cA_1 m one y in
  let xff := cF m y_1 in
  let yff := cF m x_1 in
  let m1 := Split m one x x_1 in
  let m2 := Split m1 one y y_1 in 
  let m3 := Merge m2 one xff x in 
  let m4 := Merge m3 one yff y in
     (exd m z <-> exd m1 z) /\
        (exd m1 z <-> exd m2 z) /\
           (exd m2 z <-> exd m3 z) /\
               (exd m3 z <-> exd m4 z).
Proof.
intros.
split.
unfold m1.
generalize (exd_Split m one x x_1 z).
tauto.
split.
unfold m2.
generalize (exd_Split m1 one y y_1 z).
tauto.
split.
unfold m3.
generalize (exd_Merge m2 one xff x z).
tauto.
unfold m4.
generalize (exd_Merge m3 one yff y z).
tauto.
Qed.

Lemma exd_Flip_topo: forall(m:fmap)(x z:dart),
     (exd m z <-> exd (Flip_topo m x) z).
Proof.
 intros.
  unfold Flip_topo. 
  set (x_1 := cA_1 m one x).
  set (y := cA m zero x).
  set (y_1 := cA_1 m one y).
  set (xff := cF m y_1).
  set (yff := cF m x_1).
  set (m1 := Split m one x x_1).
  set (m2 := Split m1 one y y_1). 
  set (m3 := Merge m2 one xff x). 
  set (m4 := Merge m3 one yff y).
Proof.
 assert (exd m z <-> exd m1 z).
    unfold m1.
    apply exd_Split.
assert (exd m1 z <-> exd m2 z).
unfold m2.
apply exd_Split.
assert (exd m2 z <-> exd m3 z).
unfold m3.
apply exd_Merge.
assert (exd m3 z <-> exd m4 z).
unfold m4.
apply exd_Merge.
tauto.
Qed.

Lemma exd_Flip_emb: forall(m4:fmap)(x y xff yff z:dart),
   (exd m4 z <-> exd (Flip_emb m4 x y xff yff) z).
Proof.
 intros. 
   unfold Flip_emb.
  set (pxff:= fpoint m4 xff).
   set (pyff:= fpoint m4 yff).
     set (m5 := Chp m4 x pxff).
 generalize (exd_Chp m5 y pyff z).
      unfold m5.
       generalize (exd_Chp m4 x pxff z).   
   tauto.
Qed. 

Lemma exd_Flip: forall(m:fmap)(x z:dart),
   (exd m z <-> exd (Flip m x) z).
Proof.
 intros. unfold Flip.
  set (x_1 := cA_1 m one x).
  set (y := cA m zero x).
  set (y_1 := cA_1 m one y).
  set (xff := cF m y_1).
  set (yff := cF m x_1).
   generalize 
   (exd_Flip_emb (Flip_topo m x) x y xff yff z).
    generalize (exd_Flip_topo m x z).
 tauto.
Qed.

(* OK: PART 1_4: *)

Lemma inv_hmap_Flip_1_4: forall(m:fmap)(x:dart),
  let x_1 := cA_1 m one x in
  let y := cA m zero x in
  let y_1 := cA_1 m one y in
  let xff := cF m y_1 in
  let yff := cF m x_1 in
  let m1 := Split m one x x_1 in
  let m2 := Split m1 one y y_1 in 
  let m3 := Merge m2 one xff x in 
  let m4 := Merge m3 one yff y in
   inv_Triangulation m -> 
    prec_Flip m x ->
     inv_hmap m1 /\ inv_hmap m2 /\
      inv_hmap m3 /\ inv_hmap m4.
Proof.
intros.
unfold prec_Flip in H0.
unfold inv_Triangulation in H.
fold y in H0.
decompose [and] H.
clear H.
decompose [and] H0.
clear H0.
assert (exd m y).
 unfold y in |- *.
   generalize (exd_cA m zero x).
    tauto.
assert (exd m1 y).
 unfold m1 in |- *.
   generalize (exd_Split m one x x_1 y).
    tauto.
assert (exd m2 y).
 unfold m2 in |- *.
   generalize (exd_Split m1 one y y_1 y).
    tauto.
assert (exd m3 y).
 unfold m3 in |- *.
   generalize (exd_Merge m2 one xff x y).
    tauto.
assert (exd m y_1).
 unfold y_1 in |- *.
   generalize (exd_cA_1 m one y).
    tauto.
assert (exd m xff).
 unfold xff in |- *.
   generalize (exd_cF m y_1).
    tauto.
assert (exd m1 xff).
 unfold m1 in |- *.
   generalize (exd_Split m one x x_1 xff).
    tauto.
assert (exd m2 xff).
 unfold m2 in |- *.
   generalize (exd_Split m1 one y y_1 xff).
    tauto.
assert (exd m1 x).
 unfold m1 in |- *.
   generalize (exd_Split m one x x_1 x).
    tauto.
assert (exd m2 x).
 unfold m2 in |- *.
   generalize (exd_Split m1 one y y_1 x).
    tauto.
assert (exd m x_1).
 unfold x_1 in |- *.
   generalize (exd_cA_1 m one x).
    tauto.
assert (exd m yff).
 unfold yff in |- *.
   generalize (exd_cF m x_1).
    tauto.
assert (exd m1 yff).
 unfold m1 in |- *.
   generalize (exd_Split m one x x_1 yff).
    tauto.
assert (exd m2 yff).
 unfold m2 in |- *.
   generalize (exd_Split m1 one y y_1 yff).
    tauto.
assert (exd m3 yff).
 unfold m3 in |- *.
   generalize (exd_Merge m2 one xff x yff).
    tauto.
assert (isTri m x).
 unfold isTriangulation in H5.
   apply (H5 x H).
assert (isTri m y).
 unfold isTriangulation in H5.
   apply (H5 y H0).
assert (degreee m x = 2).
 unfold isMap in H3.
   apply (H3 x H).
generalize (degreee_invol_nofixpt m x H1 H).
  intro.
  generalize (invol_inverse m zero x H1 H).
  intro.
  assert (cA m zero x <> x).
  tauto.
assert (cA m zero (cA m zero x) = x).
  tauto.
clear H26.
  assert (cA m zero x = cA_1 m zero x).
  tauto.
clear H27.
  fold y in H29.
  assert (y = cA_1 m zero x).
 rewrite <- H29 in |- *.
   rewrite cA_1_cA in |- *.
   tauto.
  tauto.
  tauto.
assert (y_1 = cF m x).
 unfold cF in |- *.
   rewrite <- H27 in |- *.
   fold y_1 in |- *.
    tauto.
assert (x_1 = cF m y).
 unfold cF in |- *.
   rewrite H27 in |- *.
   rewrite <- H26 in |- *.
   rewrite cA_1_cA in |- *.
  fold x_1 in |- *.
     tauto.
  tauto.
  tauto.
generalize (Tri_diff_face m x H1 H H23).
  intro.
  simpl in H32.
  rewrite <- H30 in H32.
  fold xff in H32.
  assert (x <> y).
 intro.
   elim H4.
   rewrite <- H33 in |- *.
   apply expv_refl.
    tauto.
assert (cA_1 m1 one y = cA_1 m one y).
 unfold m1 in |- *.
   unfold x_1 in |- *.
   rewrite cA1_1_Flip1 in |- *.
  elim (eq_dart_dec (cA m one x) y).
   intro.
     elim H4.
     rewrite <- a in |- *.
     unfold expv in |- *.
     unfold MA1.MfcA.expo in |- *.
     split.
     tauto.
   split with 1.
     simpl in |- *.
      tauto.
  elim (eq_dart_dec x y).
    tauto.
   tauto.
  tauto.
  lia.
  tauto.
  tauto.
assert (inv_hmap m1).
 unfold m1 in |- *.
   apply inv_hmap_Split.
    tauto.
assert (inv_hmap m2).
 unfold m2 in |- *.
   apply inv_hmap_Split.
    tauto.
split.
  tauto.
split.
  tauto.
assert (degreev m1 x = 1).
 unfold m1 in |- *.
   unfold x_1 in |- *.
   rewrite (degreev_Flip1 m x x H1) in |- *.
  elim (eq_dart_dec x x).
    tauto.
   tauto.
  tauto.
  tauto.
  lia.
assert (degreev m2 x = 1).
 unfold m2 in |- *.
   unfold y_1 in |- *.
   rewrite <- H34 in |- *.
   rewrite (degreev_Flip2 m1 y x H35) in |- *.
  elim (eq_dart_dec y x).
    tauto.
  rewrite H34 in |- *.
    elim (expv_dec m1 (cA_1 m one y) x H35).
   intros.
     assert (MA1.MfcA.expo m1 x (cA_1 m one y)).
    apply MA1.MfcA.expo_symm.
      tauto.
     tauto.
   assert (MA1.MfcA.expo2 m1 x (cA_1 m one y)).
    generalize 
  (MA1.MfcA.expo_expo2 m1 x (cA_1 m one y)).
       tauto.
   unfold MA1.MfcA.expo2 in H39.
     decompose [and] H39.
     clear H39.
     elim H41.
     clear H41.
     intros i Hi.
     decompose [and] Hi.
     clear Hi.
     assert (MA1.MfcA.degree = degreev).
     tauto.
   rewrite H42 in H39.
     assert (i = 0).
     lia.
   rewrite H43 in H41.
     simpl in H41.
     elim H4.
     rewrite H41 in |- *.
     unfold expv in |- *.
     unfold MA1.MfcA.expo in |- *.
     split.
    generalize (exd_cA_1 m one y).
       tauto.
   split with 1.
     simpl in |- *.
 assert (MA1.MfcA.f m (cA_1 m one y) = 
 cA m one (cA_1 m one y)).
     tauto.
   rewrite cA_cA_1 in H44.
     tauto.
    tauto.
    tauto.
   tauto.
  tauto.
  tauto.
 assert (degreev m1 y = degreev m y).
  unfold m1 in |- *.
    unfold x_1 in |- *.
    rewrite (degreev_Flip1 m x y H1) in |- *.
   elim (eq_dart_dec x y).
     tauto.
   elim (expv_dec m (cA_1 m one x) y H1).
    intros.
      elim H4.
      apply expv_trans with (cA_1 m one x).
     apply MA1.MfcA.expo_symm.
       tauto.
     unfold MA1.MfcA.expo in |- *.
       split.
      generalize (exd_cA_1 m one x).
         tauto.
     split with 1.
       simpl in |- *.
  assert (MA1.MfcA.f m (cA_1 m one x) = 
     cA m one (cA_1 m one x)).
       tauto.
     rewrite cA_cA_1 in H38.
       tauto.
      tauto.
      tauto.
     tauto.
    tauto.
   tauto.
   tauto.
   lia.
 rewrite H38 in |- *.
    lia.
assert (~ expv m2 xff x).
 intro.
   assert (expv m2 x xff).
  apply expv_symm.
    tauto.
   tauto.
 assert (MA1.MfcA.expo2 m2 x xff).
  generalize (MA1.MfcA.expo_expo2 m2 x xff).
     tauto.
 unfold MA1.MfcA.expo2 in H41.
   decompose [and] H41.
   clear H41.
   elim H43.
   clear H43.
   intros i Hi.
   assert (MA1.MfcA.degree = degreev).
   tauto.
 rewrite H41 in Hi.
   assert (i = 0).
   lia.
 rewrite H43 in Hi.
   simpl in Hi.
    tauto.
assert (inv_hmap m3).
 unfold m3 in |- *.
   apply inv_hmap_Merge1.
   tauto.
  tauto.
  tauto.
  tauto.
assert (degreev m1 y = degreev m y).
 unfold m1 in |- *.
   unfold x_1 in |- *.
   rewrite (degreev_Flip1 m x y H1) in |- *.
  elim (eq_dart_dec x y).
    tauto.
  elim (expv_dec m (cA_1 m one x) y H1).
   intros.
     elim H4.
     apply expv_trans with (cA_1 m one x).
    apply MA1.MfcA.expo_symm.
      tauto.
    unfold MA1.MfcA.expo in |- *.
      split.
     generalize (exd_cA_1 m one x).
        tauto.
    split with 1.
      simpl in |- *.
 assert (MA1.MfcA.f m (cA_1 m one x) = 
     cA m one (cA_1 m one x)).
      tauto.
    rewrite cA_cA_1 in H41.
      tauto.
     tauto.
     tauto.
    tauto.
   tauto.
  tauto.
  tauto.
  lia.
assert (degreev m2 y = 1).
 unfold m2 in |- *.
   unfold y_1 in |- *.
   rewrite <- H34 in |- *.
   rewrite (degreev_Flip2 m1 y y H35) in |- *.
  elim (eq_dart_dec y y).
   intro.
      tauto.
   tauto.
  tauto.
  tauto.
  lia.
assert (degreev m3 y = 1).
 unfold m3 in |- *.
   rewrite (degreev_Flip3 m2 xff x y H36) in |- *.
  elim (expv_dec m2 xff y H36).
   intro.
     assert (MA1.MfcA.expo m2 y xff).
    apply MA1.MfcA.expo_symm.
      tauto.
     tauto.
   assert (MA1.MfcA.expo2 m2 y xff).
    generalize (MA1.MfcA.expo_expo2 m2 y xff).
       tauto.
   unfold MA1.MfcA.expo2 in H44.
     elim H44.
     clear H44.
     intros.
     clear H44.
     elim H45.
     intros i Hi.
     assert (MA1.MfcA.degree = degreev).
     tauto.
   rewrite H44 in Hi.
     assert (i = 0).
     lia.
   rewrite H46 in Hi.
     simpl in Hi.
     clear H45.
 generalize
 (Tri_diff_2faces m x y H1 H H0 H23 H24).
     simpl in |- *.
     rewrite <- H30 in |- *.
     rewrite <- H31 in |- *.
     fold xff in |- *.
     fold yff in |- *.
     intros.
   assert (xff = y).
    symmetry  in |- *.
       tauto.
    tauto.
  elim (eq_dart_dec x y).
    tauto.
   tauto.
  tauto.
  tauto.
  tauto.
 intro.
   assert (expv m2 x xff).
  apply expv_symm.
    tauto.
   tauto.
 unfold expv in H44.
   assert (MA1.MfcA.expo2 m2 x xff).
  generalize (MA1.MfcA.expo_expo2 m2 x xff).
     tauto.
 unfold MA1.MfcA.expo2 in H45.
   elim H45.
   clear H45.
   intros.
   clear H45.
   elim H46.
   intros i Hi.
   assert (MA1.MfcA.degree = degreev).
   tauto.
 assert (i = 0).
  rewrite H45 in Hi.
     lia.
 rewrite H47 in Hi.
   simpl in Hi.
    tauto.
  tauto.
assert (~ expv m3 yff y).
 intro.
   assert (expv m3 y yff).
  apply expv_symm.
    tauto.
   tauto.
 assert (MA1.MfcA.expo2 m3 y yff).
  generalize (MA1.MfcA.expo_expo2 m3 y yff).
     tauto.
 unfold MA1.MfcA.expo2 in H46.
   elim H46.
   intros.
   clear H46 H47.
   assert (MA1.MfcA.degree = degreev).
   tauto.
 rewrite H46 in H48.
   elim H48.
   clear H48.
   intros i Hi.
   assert (i = 0).
   lia.
 rewrite H47 in Hi.
   simpl in Hi.
   generalize (Tri_diff_face m y H1 H0 H24).
   simpl in |- *.
   rewrite <- H31 in |- *.
   fold yff in |- *.
    tauto.
split.
  tauto.
assert (inv_hmap m4).
 unfold m4 in |- *.
   apply inv_hmap_Merge1.
   tauto.
  tauto.
  tauto.
  tauto.
tauto.
Qed.

(* PART 5_6: OK *)

Lemma inv_hmap_Flip_5_6: forall(m4:fmap)(x y xff yff:dart),
  let pxff := fpoint m4 xff in
  let pyff := fpoint m4 yff in
  let m5 := Chp m4 x pxff in
  let m6 := Chp m5 y pyff in 
    inv_hmap m4 ->  inv_hmap m6.
Proof.
   intros.
    unfold m6.
   apply inv_hmap_Flip6.
     unfold m5.
  apply inv_hmap_Flip5.
tauto.
Qed.

(* inv_hmap_Flip_topo: *)

Lemma inv_hmap_Flip_topo: 
 forall(m:fmap)(x:dart),
   inv_Triangulation m -> 
       prec_Flip m x ->
           inv_hmap (Flip_topo m x).
Proof.
  intros. unfold Flip_topo.
     generalize  (inv_hmap_Flip_1_4 m x H H0).
  tauto.
Qed.

(* inv_hmap_Flip_emb: *)

Lemma inv_hmap_Flip_emb: forall(m4:fmap)(x y xff yff:dart),
   inv_hmap m4 -> 
        inv_hmap (Flip_emb m4 x y xff yff).
Proof.
  intros. unfold Flip_emb.
       generalize  (inv_hmap_Flip_5_6 m4 x y xff yff).
      simpl.
  tauto.
Qed.

(* inv_hmap_Flip: *)

Theorem  inv_hmap_Flip:
   forall(m:fmap)(x:dart),
   inv_Triangulation m -> 
       prec_Flip m x ->  inv_hmap (Flip m x).
Proof.
   intros. unfold Flip.
     apply  inv_hmap_Flip_emb.
apply  inv_hmap_Flip_topo.
tauto. tauto.
Qed.

(* isMap: PART 1_4: *)

Lemma isMap_Flip_1_4: forall(m:fmap)(x:dart),
  let x_1 := cA_1 m one x in
  let y := cA m zero x in
  let y_1 := cA_1 m one y in
  let xff := cF m y_1 in
  let yff := cF m x_1 in
  let m1 := Split m one x x_1 in
  let m2 := Split m1 one y y_1 in 
  let m3 := Merge m2 one xff x in 
  let m4 := Merge m3 one yff y in
   inv_Triangulation m -> 
     prec_Flip m x ->
       isMap m1 /\ isMap m2 /\
         isMap m3 /\ isMap m4.
Proof.
intros.
generalize (inv_hmap_Flip_1_4 m x H H0).
fold y in |- *.
fold x_1 in |- *.
fold y_1 in |- *.
fold xff in |- *.
fold yff in |- *.
fold m1 in |- *.
fold m2 in |- *.
fold m3 in |- *.
fold m4 in |- *.
intros.
rename H1 into Im.
unfold prec_Flip in H0.
unfold inv_Triangulation in H.
fold y in H0.
decompose [and] H.
clear H.
decompose [and] H0.
clear H0.
assert (exd m y).
 unfold y in |- *.
   generalize (exd_cA m zero x).
    tauto.
assert (exd m1 y).
 unfold m1 in |- *.
   generalize (exd_Split m one x x_1 y).
    tauto.
assert (exd m2 y).
 unfold m2 in |- *.
   generalize (exd_Split m1 one y y_1 y).
    tauto.
assert (exd m3 y).
 unfold m3 in |- *.
   generalize (exd_Merge m2 one xff x y).
    tauto.
assert (exd m y_1).
 unfold y_1 in |- *.
   generalize (exd_cA_1 m one y).
    tauto.
assert (exd m xff).
 unfold xff in |- *.
   generalize (exd_cF m y_1).
    tauto.
assert (exd m1 xff).
 unfold m1 in |- *.
   generalize (exd_Split m one x x_1 xff).
    tauto.
assert (exd m2 xff).
 unfold m2 in |- *.
   generalize (exd_Split m1 one y y_1 xff).
    tauto.
assert (exd m1 x).
 unfold m1 in |- *.
   generalize (exd_Split m one x x_1 x).
    tauto.
assert (exd m2 x).
 unfold m2 in |- *.
   generalize (exd_Split m1 one y y_1 x).
    tauto.
assert (exd m x_1).
 unfold x_1 in |- *.
   generalize (exd_cA_1 m one x).
    tauto.
assert (exd m yff).
 unfold yff in |- *.
   generalize (exd_cF m x_1).
    tauto.
assert (exd m1 yff).
 unfold m1 in |- *.
   generalize (exd_Split m one x x_1 yff).
    tauto.
assert (exd m2 yff).
 unfold m2 in |- *.
   generalize (exd_Split m1 one y y_1 yff).
    tauto.
assert (exd m3 yff).
 unfold m3 in |- *.
   generalize (exd_Merge m2 one xff x yff).
    tauto.
assert (isTri m x).
 unfold isTriangulation in H5.
   apply (H5 x H).
assert (isTri m y).
 unfold isTriangulation in H5.
   apply (H5 y H0).
generalize (Tri_diff_face m x H1 H H23).
  intro.
  simpl in H25.
  fold xff in H25.
  assert (x <> y).
 intro.
   elim H4.
   rewrite <- H26 in |- *.
   apply expv_refl.
    tauto.
assert (cA_1 m1 one y = cA_1 m one y).
 unfold m1 in |- *.
   unfold x_1 in |- *.
   rewrite cA1_1_Flip1 in |- *.
  elim (eq_dart_dec (cA m one x) y).
   intro.
     elim H4.
     rewrite <- a in |- *.
     unfold expv in |- *.
     unfold MA1.MfcA.expo in |- *.
     split.
     tauto.
   split with 1.
     simpl in |- *.
      tauto.
  elim (eq_dart_dec x y).
    tauto.
   tauto.
  tauto.
  lia.
  tauto.
  tauto.
assert (isMap m1).
 unfold m1 in |- *.
   unfold x_1 in |- *.
   apply isMap_Flip1.
   tauto.
  tauto.
  tauto.
split.
  tauto.
assert (isMap m2).
 unfold m2 in |- *.
   unfold y_1 in |- *.
   rewrite <- H27 in |- *.
   apply isMap_Flip2.
   tauto.
  tauto.
  tauto.
 assert (cA m1 zero y = cA m zero y).
  unfold m1 in |- *.
    unfold x_1 in |- *.
    rewrite cA0_Flip1 in |- *.
    tauto.
   tauto.
   tauto.
   tauto.
 rewrite H29 in |- *.
   unfold isMap in H3.
   assert (degreee m x = 2).
  apply H3.
     tauto.
 generalize (degreee_invol_nofixpt m x H1 H).
   intros.
   fold y in H31.
   assert (cA m zero y = x).
   tauto.
 rewrite H32 in |- *.
   unfold m1 in |- *.
   unfold x_1 in |- *.
   rewrite (degreev_Flip1 m x x H1) in |- *.
  elim (eq_dart_dec x x).
    tauto.
   tauto.
  tauto.
  tauto. 
  clear H27 H29 H31 H32.
  lia.
 unfold m1 in |- *.
   unfold x_1 in |- *.
   rewrite (degreev_Flip1 m x y H1) in |- *.
  elim (eq_dart_dec x y).
    tauto.
  elim (expv_dec m (cA_1 m one x) y H1).
   intros.
      lia.
  intros.
     lia.
  tauto.
  tauto.
  lia.
split.
  tauto.
assert (isMap m3).
 unfold m3 in |- *.
   apply isMap_Flip3.
   tauto.
  tauto.
  tauto.
  tauto.
split.
  tauto.
assert (isMap m4).
 unfold m4 in |- *.
   apply isMap_Flip3.
   tauto.
  tauto.
  tauto.
  tauto.
tauto.
Qed.

(* isMap: PART 5_6: *)

Lemma isMap_Flip_5_6: forall(m4:fmap)(x y xff yff:dart),
  let pxff := fpoint m4 xff in
  let pyff := fpoint m4 yff in
  let m5 := Chp m4 x pxff in
  let m6 := Chp m5 y pyff in 
   inv_hmap m4 -> isMap m4 ->  isMap m6.
Proof.
   intros.
    unfold m6.
   apply isMap_Flip6.
     unfold m5.
   apply inv_hmap_Flip5.
      tauto.
     unfold m5.
  apply isMap_Flip5.
tauto.
tauto.
Qed.

(* isMap_Flip_topo: *)

Lemma isMap_Flip_topo: 
 forall(m:fmap)(x:dart),
   inv_Triangulation m -> 
       prec_Flip m x ->
           isMap (Flip_topo m x).
Proof.
  intros. unfold Flip_topo.
     generalize  (isMap_Flip_1_4 m x H H0).
  tauto.
Qed.

(* isMap_Flip_emb: *)

Lemma isMap_Flip_emb: forall(m4:fmap)(x y xff yff:dart),
   inv_hmap m4 -> isMap m4 -> 
        isMap (Flip_emb m4 x y xff yff).
Proof.  
  intros. unfold Flip_emb.
       generalize  (isMap_Flip_5_6 m4 x y xff yff).
      simpl.
  tauto.
Qed.

(* isMap_Flip: *)

Theorem  isMap_Flip:
   forall(m:fmap)(x:dart),
   inv_Triangulation m -> 
       prec_Flip m x ->  isMap (Flip m x).
Proof.
   intros. unfold Flip.
     apply  isMap_Flip_emb.
   apply inv_hmap_Flip_topo.
tauto. tauto.
apply  isMap_Flip_topo.
tauto. tauto.
Qed.

(*==================================================
                 END TRIANG01
====================================================*)


