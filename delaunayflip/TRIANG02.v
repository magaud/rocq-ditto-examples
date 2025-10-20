(*=====================================================
=======================================================
               TOPOLOGICAL FMAPS, HMAPS -
               WITH TAGS AND EMBEDDINGS
                 
            FLIP SUMMARY - PART 2: FACES
               PART 2, COMPILED (7 MIN)

OCTOBER 2008, REVIEWED MAY 2009
=======================================================
=====================================================*)

Require Export TRIANG01.

(*===================================================
             Flip SUMMARY - PART 2: FACES...
====================================================*)

(* isSubd, PART 1_4: *)

Theorem isSubd_Flip_1_4: 
 forall(m:fmap)(x:dart),
  let x_1 := cA_1 m one x in
  let y := cA m zero x in
  let y_1 := cA_1 m one y in
  let xff := cF m y_1 in
  let yff := cF m x_1 in
  let m1 := Split m one x x_1 in
  let m2 := Split m1 one y y_1 in 
  let m3 := Merge m2 one xff x in 
  let m4 := Merge m3 one yff y in
   inv_Triangulation m -> prec_Flip m x -> 
    isHexa m1 x /\
      isBar m2 x /\ isQuad m2 y_1 /\
        isHexa m3 y /\
          isTri m4 x /\ isTri m4 y.
Proof.
intros.
generalize (inv_hmap_Flip_1_4 m x H H0).
generalize (isMap_Flip_1_4 m x H H0).
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
rename H2 into Invm.
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
assert (isTri m x).
 unfold isTriangulation in H5.
   apply (H5 x H).
assert (isTri m y).
 unfold isTriangulation in H5.
   apply (H5 y H0).
assert (2 <= degreev m x).
  lia.
generalize (degreev_crackv m x H1 H H11).
  fold x_1 in |- *.
  intro.
  assert (x <> x_1).
 unfold crackv in H12.
   unfold MA1.crack in H12.
    tauto.
assert (isHexa m1 x).
 unfold m1 in |- *.
   unfold x_1 in |- *.
   apply (isHexa_Flip1 m x H1 H H13 H6).
   tauto.
 fold y in |- *.
    tauto.
split.
  tauto.
assert (exd m1 y).
 unfold m1 in |- *.
   generalize (exd_Split m one x x_1 y).
    tauto.
assert (2 <= degreev m y).
  lia.
generalize (cF_Flip1_detail_1 m x H1 H3 H H11 H16 H4 H6 H8 H10).
  fold x_1 in |- *.
  fold m1 in |- *.
  fold y in |- *.
  fold y_1 in |- *.
  intros.
 fold xff in H17.
  fold yff in H17.
 assert (y = cA m1 zero x).
 unfold m1 in |- *.
   unfold x_1 in |- *.
   rewrite cA0_Flip1 in |- *.
  fold y in |- *.
     tauto.
  tauto.
  tauto.
  tauto.
assert (exd m1 x).
 generalize (exd_cA m1 zero x).
   rewrite <- H18 in |- *.
    tauto.
assert (degreee m1 x = 2).
 assert (isMap m1).
   tauto.
 unfold isMap in H19.
   unfold isMap in H20.
   apply H20.
    tauto.
assert (inv_hmap m1).
  tauto.
generalize (degreee_invol_nofixpt m1 x H21 H19).
  intro.
  assert (cA m1 zero x <> x).
  tauto.
assert (cA m1 zero (cA m1 zero x) = x).
  tauto.
clear H22.
  generalize (invol_inverse m1 zero x H21 H19).
  intros.
  assert (cA m1 zero x = cA_1 m1 zero x).
  tauto.
clear H22.
  rewrite <- H18 in H24.
  rewrite <- H18 in H25.
  assert (y_1 = cA_1 m1 one y).
 rewrite H25 in |- *.
   fold (cF m1 x) in |- *.
   symmetry  in |- *.
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
assert (2 <= degreev m1 y).
unfold m1 in |- *.
   unfold x_1 in |- *.
   rewrite (degreev_Flip1 m x y H1) in |- *.
  elim (eq_dart_dec x y).
   intro.
     elim H4.
     rewrite <- a in |- *.
     apply expv_refl.
      tauto.
  elim (expv_dec m (cA_1 m one x) y H1).
   intros.
      lia.
  intros.
     lia.
  tauto.
  tauto.
  lia.
assert (isBar m2 x).
 unfold m2 in |- *.
   rewrite H22 in |- *.
   rewrite <- H24 in |- *.
   apply (isBar_Flip2 m1 y H21).
   tauto.
  tauto.
 rewrite H24 in |- *.
    tauto.
  tauto.
 rewrite H24 in |- *.
    tauto.
split.
  tauto.
assert (isQuad m2 y_1).
 unfold m2 in |- *.
   rewrite H22 in |- *.
   apply isQuad_Flip2.
   tauto.
  tauto.
  tauto.
 rewrite H24 in |- *.
    tauto.
  tauto.
 rewrite H24 in |- *.
    tauto.
split.
  tauto.
assert (exd m2 x).
 unfold m2 in |- *.
   generalize (exd_Split m1 one y y_1 x).
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
assert (y = cA m2 zero x).
 unfold m2 in |- *.
   rewrite H22 in |- *.
   rewrite cA0_Flip2 in |- *.
   tauto.
  tauto.
  tauto.
  tauto.
assert (inv_Triangulation m).
 unfold inv_Triangulation in |- *.
    tauto.
clear H1 H3 H5 H2.
  clear H0 H8.
  clear H11.
  clear H10.
assert
   (exd m x /\
    exd m1 y /\
    exd m1 x /\
    exd m2 x /\ exd m y_1 /\ exd m xff /\ 
    exd m1 xff /\ exd m2 xff).
  tauto.
clear H H19 H15 H30 H31 H32 H33 H34.
  decompose [and] H17.
  clear H17.
  rewrite <- H in H26.
  rewrite <- H in H14.
  assert (isMap m1).
  tauto.
assert (exd m1 y).
  tauto.
generalize (cF_Flip2_detail_1 m1 y H21 H8 H11 H14 H26 H27).
  rewrite H in |- *.
  rewrite H2 in |- *.
  fold m2 in |- *.
  rewrite H1 in |- *.
  rewrite H3 in |- *.
  rewrite H5 in |- *.
  intros.
  assert (xff = cF m2 y_1).
  tauto.
assert (degreef m2 y_1 = degreef m2 xff).
 assert (degreef = MF.degree).
   tauto.
 assert (cF = MF.f).
   tauto.
 rewrite H17 in |- *.
   rewrite H19 in |- *.
   apply MF.expo_degree.
   tauto.
 unfold MF.expo in |- *.
   split.
  generalize (exd_cF m2 y_1).
    rewrite <- H17 in |- *.
     tauto.
 split with 1.
   simpl in |- *.
    tauto.
assert (isQuad m2 xff).
 unfold isQuad in |- *.
   rewrite <- H19 in |- *.
   unfold isQuad in H29.
    tauto.
unfold isQuad in H29.
  assert (isHexa m3 y).
 unfold m3 in |- *.
   rewrite H35 in |- *.
   apply isHexa_Flip3.
   tauto.
  tauto.
  tauto.
  tauto.
  tauto.
  tauto.
split.
  tauto.
clear H8 H11.
  assert (inv_hmap m2).
  tauto.
assert (isMap m2).
  tauto.
assert (exd m2 x).
  tauto.
assert (exd m2 xff).
  tauto.
generalize (cF_Flip3_detail_1 m2 xff x H8 H11 H28 H30 H32 H33).
  cbv zeta. (*simpl in |- *.*)
  fold m3 in |- *.
  decompose [and] H15.
  rewrite <- H38 in |- *.
  rewrite <- H40 in |- *.
  rewrite <- H42 in |- *.
  rewrite <- H37 in |- *.
  intro.
 clear H34 H38 H37 H39 H40 H42.
  clear H32 H33 H11 H8.
  clear H17.
 assert (exd m2 y).
generalize (exd_cA m2 zero x).
   rewrite <- H35 in |- *.
    tauto.
assert (exd m3 x).
unfold m3.
generalize (exd_Merge m2 one xff x x).
tauto.
assert (exd m3 y).
unfold m3.
generalize (exd_Merge m2 one xff x y).
tauto.
assert (xff = cF m3 y).
tauto.
assert (exd m3 xff).
generalize (exd_cF m3 y).
rewrite H32.
tauto.
assert (x_1 = cF m3 xff).
tauto.
assert (exd m3 x_1).
generalize (exd_cF m3 xff).
rewrite <-H34.
tauto.
assert (yff = cF m3 x_1).
tauto.
assert (exd m3 yff).
generalize (exd_cF m3 x_1).
rewrite <-H38.
tauto.
clear H32 H34 H38.
assert (exd m3 x /\ exd m3 y /\ exd m3 xff /\ exd m3 x_1  /\ exd m3 yff).
tauto.
clear H11 H17 H33 H37 H39.
assert (cA m3 one y = y).
unfold m3.
rewrite cA1_Flip3.
unfold inv_Triangulation in H36.
assert (exd m x).
tauto.
assert (exd m y).
unfold y.
generalize (exd_cA m zero x).
tauto.
assert (isTriangulation m).
tauto.
assert (inv_hmap m).
tauto.
unfold isTriangulation in H33.
assert (isTri m x).
apply H33.
tauto.
assert (isTri m y).
apply H33.
tauto.
assert (cA_1 m zero x = y).
rewrite H25.   
unfold m1.
unfold x_1.
rewrite cA0_1_Flip1.
tauto.
tauto.
tauto.
tauto.
assert (y_1 = cF m x).
unfold cF.
rewrite H39.
fold y_1.
tauto.
generalize (Tri_diff_2faces m x y H34 H11 H17 H37 H38 H6).
simpl.
rewrite <-H40.
fold xff.
intro.
elim (eq_dart_dec xff y).
tauto.
elim (eq_dart_dec x y).
tauto.
intros.
assert (isBar m2 y).
rewrite H35.
apply isBar_symm.
tauto.
tauto.
tauto.
unfold isBar in H43.
assert (inv_hmap m2).
tauto.
generalize (degreev_fixpt m2 y H44 H8).
tauto.
tauto.
tauto.
tauto.
assert (inv_hmap m2).
tauto.
assert (exd m2 x).
tauto.
generalize (degreev_fixpt m2 x H11 H17).
unfold isBar in H28.
tauto.
tauto.
assert (exd m3 x_1).
tauto.
assert (exd m3 yff).
tauto.
assert (cA m2 zero y = x).
unfold m2.
rewrite H22.
rewrite cA0_Flip1.
tauto.
tauto.
tauto.
tauto.
assert (cA m3 zero y = x).
unfold m3.
rewrite cA0_Flip3.
tauto.
tauto.
tauto.
tauto.
tauto.
decompose [and] H41.
clear H41.
assert (yff = Iter (cF m3) 4 x).
unfold Iter; fold Iter.
rewrite <-H38.
rewrite <-H40.
rewrite <-H39.
tauto.
assert (degreef = MF.degree).
tauto.
assert (cF = MF.f).
tauto.
assert (degreef m3 y = degreef m3 yff).
rewrite H44.
apply MF.expo_degree.
tauto.
unfold MF.expo.
split.
tauto.
split with 3.
unfold Iter; fold Iter.
rewrite <-H46.
rewrite <-H40.
rewrite <-H39.
rewrite <-H42.
tauto.
unfold isHexa in H31.
assert (isHexa m3 yff).
unfold isHexa.
rewrite <-H47.
tauto.
assert (isTri m4 x).
unfold m4.
assert (expf m3 x x).
apply expf_refl.
tauto.
tauto.
assert (inv_hmap m3).
tauto.
assert (exd m3 x).
tauto.
assert (exd m3 yff).
tauto.
assert (exd m3 y).
tauto.
assert (expf m3 (cA m3 zero y) x).
rewrite H37.
tauto.
rewrite <-H37 in H41.
apply (isTri_Flip4_1 m3 yff y x H50 H48 H11 H53 H52
 H51 H41 H54).
assert (isTri m4 y).
unfold m4.
assert (inv_hmap m3).
tauto.
assert (exd m3 x).
tauto.
assert (exd m3 yff).
tauto.
assert (exd m3 y).
tauto.
assert (expf m3 x y).
unfold expf.
split.
tauto.
unfold MF.expo.
split.
tauto.
split with 1.
unfold Iter; fold Iter.
rewrite H38.
tauto.
rewrite <-H37 in H41.
rewrite <-H37 in H54.
apply (isTri_Flip4_1 m3 yff y y H50 H48 H11 H53 H52
 H53 H41 H54).
split.
tauto.
tauto.
Qed.

(* degreef_Flip_5_6: *)

Lemma degreef_Flip_5_6: forall(m4:fmap)(x y xff yff z: dart),
  let pxff := fpoint m4 xff in
  let pyff := fpoint m4 yff in
  let m5 := Chp m4 x pxff in
  let m6 := Chp m5 y pyff in 
   inv_hmap m4 -> exd m4 z -> 
       degreef m6 z =  degreef m4 z.
Proof.
   intros.
    unfold m6.
   rewrite degreef_Flip6.
     unfold m5.
   apply degreef_Flip5.
      tauto.
     tauto.
     unfold m5.
  apply inv_hmap_Flip5.
tauto.
unfold m5.
generalize (exd_Chp m4 x pxff z).
tauto.
Qed.

(* isSubd_Flip_5_6: *)

Lemma isSubd_Flip_5_6: forall(m4:fmap)(x y xff yff z: dart),
  let pxff := fpoint m4 xff in
  let pyff := fpoint m4 yff in
  let m5 := Chp m4 x pxff in
  let m6 := Chp m5 y pyff in 
   inv_hmap m4 -> exd m4 z ->  
       isTri m4 z ->  isTri m6 z.
Proof.
   intros.
    unfold m6. unfold m5.
   unfold isTri.
   unfold pxff. unfold pyff.
rewrite degreef_Flip_5_6.
     unfold isTri in H1.
 tauto. tauto. tauto.
Qed.

Lemma isTri_Flip_topo: 
 forall(m:fmap)(x:dart),
   let y := cA m zero x in
   let m4 := Flip_topo m x in
     inv_Triangulation m -> 
        prec_Flip m x ->
           isTri m4 x /\ isTri m4 y.
Proof.
intros.
unfold m4.
unfold Flip_topo.
unfold y.
generalize (isSubd_Flip_1_4 m x H H0).
tauto.
Qed.

(* isTri_Flip *)

Lemma isTri_Flip: 
 forall(m:fmap)(x:dart),
   let y := cA m zero x in
   let m6 := Flip m x in
     inv_Triangulation m -> 
        prec_Flip m x ->
           isTri m6 x /\ isTri m6 y.
Proof.
   intros.
  unfold m6.
unfold Flip.
fold y.
set(y_1:=cA_1 m one y).
set(x_1:=cA_1 m one x).
set(m4:=Flip_topo m x).
set(xff:=cF m y_1).
set(yff:=cF m x_1).
unfold Flip_emb.
assert (inv_hmap m4).
unfold m4.
apply inv_hmap_Flip_topo.
tauto.
tauto.
assert (exd m4 x).
unfold m4.
generalize (exd_Flip_topo m x x).
unfold prec_Flip in H0.
tauto.
assert (exd m y).
generalize (exd_cA m zero x).
fold y.
unfold inv_Triangulation in H.
unfold prec_Flip in H0.
tauto.
assert (exd m4 y).
unfold m4.
generalize (exd_Flip_topo m x y).
unfold prec_Flip in H0.
tauto.
generalize ( isTri_Flip_topo m x H H0).
fold y.
fold m4.
intro.
 split.
apply isSubd_Flip_5_6.
tauto.
tauto.
tauto.
apply isSubd_Flip_5_6.
tauto.
tauto.
tauto.
Qed.

(* OK, BUT NOT USED: 
Lemma diff3_Tri: forall(m:fmap)(z:dart),
  inv_hmap m -> exd m z ->  
  let zf := cF m z in
  let zff:= cF m zf in
    z <> zf -> z <> zff -> zf <> zff -> 
     cF m zff = z ->
       isTri m z.
Proof.
intros.
rename H4 into Eqz.
unfold isTri in |- *.
assert (MF.degree = degreef).
  tauto.
rewrite <- H4 in |- *.
  unfold MF.degree in |- *.
  assert (0 < ndN m).
 apply MF.ndN_pos with z.
    tauto.
assert (cF = MF.f).
  tauto.
generalize (MF.degree_bound m z H H0).
  intro.
  generalize (MF.degree_lub m z H H0).
  simpl in |- *.
  intros.
  decompose [and] H8.
  rewrite MF.degree_aux_equation in |- *.
  clear H8.
  elim (le_lt_dec 1 (ndN m)).
 intro.
   elim (eq_dart_dec z (Iter (MF.f m) 1 z)).
  intro.
    simpl in a0.
    rewrite <- H6 in a0.
    fold zf in a0.
     tauto.
 elim (eq_nat_dec 1 (ndN m)).
  intros.
    assert (MF.degree m z = 1).
    lia.
  rewrite H8 in H11.
    simpl in H11.
    rewrite <- H6 in H11.
    fold zf in H11.
    symmetry  in H11.
     tauto.
 intros.
   assert (1 + 1 = 2).
   lia.
 rewrite H8 in |- *.
   clear H8.
   rewrite MF.degree_aux_equation in |- *.
   elim (le_lt_dec 2 (ndN m)).
  intro.
    elim (eq_dart_dec z (Iter (MF.f m) 2 z)).
   rewrite <- H6 in |- *.
     simpl in |- *.
     fold zf in |- *.
     fold zff in |- *.
      tauto.
  elim (eq_nat_dec 2 (ndN m)).
   intros.
     elim (eq_nat_dec (MF.degree m z) 1).
    intro.
      rewrite a2 in H11.
      simpl in H11.
      rewrite <- H6 in H11.
      fold zf in H11.
      symmetry  in H11.
       tauto.
   intro.
     assert (MF.degree m z = 2).
     lia.
   rewrite H8 in H11.
     simpl in H11.
     rewrite <- H6 in H11.
     fold zf in H11.
     fold zff in H11.
     symmetry  in H11.
      tauto.
  intros.
    rewrite MF.degree_aux_equation in |- *.
    elim (le_lt_dec (2 + 1) (ndN m)).
   intro.
     elim (eq_dart_dec z (Iter (MF.f m) (2 + 1) z)).
    intros.
       lia.
   assert (2 + 1 = 3).
     lia.
   rewrite H8 in |- *.
     rewrite <- H6 in |- *.
     intro.
     simpl in b3.
     fold zf in b3.
     fold zff in b3.
     symmetry  in Eqz.
      tauto.
  intro.
     lia.
 intro.
    lia.
intro.
   lia.
Qed.
*)

(* EXTERIOR, FROM 1 TO 4, OK, 
COMPILATION ABOUT 2 min... : *)

(* SUPPRIMER pxff... m6. *)

Theorem isTriExt_Flip_1_4: 
 forall(m:fmap)(x z:dart),
  let x_1 := cA_1 m one x in
  let y := cA m zero x in
  let y_1 := cA_1 m one y in
  let xff := cF m y_1 in
  let yff := cF m x_1 in
  let pxff := fpoint m xff in
  let pyff := fpoint m yff in
  let m1 := Split m one x x_1 in
  let m2 := Split m1 one y y_1 in 
  let m3 := Merge m2 one xff x in 
  let m4 := Merge m3 one yff y in
  let m5 := Chp m4 x pxff in
  let m6 := Chp m5 y pyff in
   inv_Triangulation m -> 
    prec_Flip m x -> exd m z -> 
     ~expf m x z -> ~expf m y z ->
       isTri m1 z /\
        isTri m2 z /\ 
          isTri m3 z /\
            isTri m4 z.
Proof.
intros.
generalize (inv_hmap_Flip_1_4 m x H H0).
generalize (isMap_Flip_1_4 m x H H0).
generalize (isSubd_Flip_1_4 m x H H0).
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
rename H4 into IS.
rename H5 into IM.
rename H6 into IH.
unfold prec_Flip in H0.
unfold inv_Triangulation in H.
fold y in H0.
decompose [and] H.
clear H.
decompose [and] H0.
clear H0.
fold x_1 in |- *.
assert (2 <= degreev m x).
  lia.
generalize (degreev_crackv m x H4 H H0).
  fold x_1 in |- *.
  intro.
  assert (x <> x_1).
 unfold crackv in H11; unfold MA1.crack in H11.
    tauto.
assert (x = cA_1 m zero y).
 unfold y in |- *.
   rewrite cA_1_cA in |- *.
   tauto.
  tauto.
  tauto.
assert (x_1 = cF m y).
 unfold cF in |- *.
   fold x_1 in |- *.
   rewrite <- H14 in |- *.
   fold x_1 in |- *.
    tauto.
assert (~ expf m x x_1).
 intro.
   assert (~ expf m y x_1).
  intro.
    elim H9.
    apply expf_trans with x_1.
    tauto.
  apply expf_symm.
     tauto.
 elim H17.
   rewrite H15 in |- *.
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
generalize (expof_Split1_CNS m x x_1 x z H4 H11 H).
  simpl in |- *.
  fold m1 in |- *.
  elim (expof_dec m (cF_1 m x) x_1 H4).
 intro.
   elim H16.
   apply expf_trans with (cF_1 m x).
  apply expf_symm.
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
 unfold expf in |- *.
    tauto.
intro.
  intro.
  assert
   (~
    (expof m x z \/
     expof m (cF_1 m x) x /\ expof m x_1 z \/
     expof m (cF_1 m x) z /\ expof m x_1 x)).
 intro.
   elim H18.
  unfold expf in H2.
     tauto.
 clear H18.
   intro.
   elim H18.
  clear H18.
    intro.
     absurd (expof m x_1 z).
   intro.
     elim H3.
     apply expf_trans with x_1.
    rewrite H15 in |- *.
      unfold expf in |- *.
      split.
      tauto.
    unfold MF.expo in |- *.
      split.
     generalize (exd_cA m zero x).
       fold y in |- *.
        tauto.
    split with 1.
      simpl in |- *.
       tauto.
   unfold expf in |- *.
      tauto.
   tauto.
 clear H18.
   intro.
   apply H16.
   apply expf_symm.
   unfold expf in |- *.
    tauto.
assert (~ expof m1 x z).
  tauto.
clear H18.
  clear H17.
  assert (isTri m1 z).
 apply (isTri_Flip1 m x z H4 H8 H H1).
  fold x_1 in |- *.
     tauto.
 fold y in |- *.
    tauto.
 fold x_1 in |- *.
   fold m1 in |- *.
   unfold expf in |- *.
    tauto.
split.
  tauto.
(* END OF isTri m1 z *)
assert (exd m y).
 unfold y in |- *.
   generalize (exd_cA m zero x).
    tauto.
assert (exd m1 y).
 unfold m1 in |- *.
   generalize (exd_Split m one x x_1 y).
    tauto.
assert (exd m1 z).
 unfold m1 in |- *.
   generalize (exd_Split m one x x_1 z).
    tauto.
assert (degreee m x = 2).
 unfold isMap in H6.
   apply H6.
    tauto.
generalize (degreee_invol_nofixpt m x H4 H).
  intros.
  assert (cA m zero (cA m zero x) = x).
  tauto.
assert (cA m zero x <> x).
  tauto.
fold y in H24.
  fold y in H25.
  clear H23.
  generalize (invol_inverse m zero x H4 H).
  fold y in |- *.
  intro.
  assert (y = cA_1 m zero x).
  tauto.
clear H23.
  assert (degreev m1 x = 1).
 unfold m1 in |- *.
   unfold x_1 in |- *.
   rewrite (degreev_Flip1 m x x H4 H) in |- *.
  elim (eq_dart_dec x x).
    tauto.
   tauto.
  tauto.
  lia.
assert (cA_1 m1 one y = cA_1 m one y).
 unfold m1 in |- *.
   unfold x_1 in |- *.
   rewrite cA1_1_Flip1 in |- *.
  elim (eq_dart_dec (cA m one x) y).
   intro.
     elim H7.
     rewrite <- a in |- *.
     unfold expv in |- *.
     unfold MA1.MfcA.expo in |- *.
     split.
     tauto.
   split with 1.
     simpl in |- *.
      tauto.
  elim (eq_dart_dec x y).
   intro.
     symmetry  in a.
      tauto.
   tauto.
  tauto.
  lia.
  tauto.
 assert (2 <= degreev m1 y).
  unfold m1 in |- *.
    unfold x_1 in |- *.
    rewrite (degreev_Flip1 m x y H4 H H18) in |- *.
   elim (eq_dart_dec x y).
    intro.
      symmetry  in a.
       tauto.
   elim (expv_dec m (cA_1 m one x) y H4).
    intros.
       lia.
   intro.
     intro.
      lia.
   lia.
  tauto.
assert (cA m1 zero y = x).
 unfold m1 in |- *.
   unfold x_1 in |- *.
   rewrite cA0_Flip1 in |- *.
   tauto.
  tauto.
  tauto.
  tauto.
assert (2 <= degreev m1 y).
 unfold m1 in |- *.
   unfold x_1 in |- *.
   rewrite (degreev_Flip1 m x y H4 H H18) in |- *.
  elim (eq_dart_dec x y).
   intro.
     symmetry  in a.
      tauto.
  elim (expv_dec m (cA_1 m one x) y H4).
   intros.
      lia.
  intro.
    intro.
     lia.
  lia.
assert (isTri m2 z).
 unfold m2 in |- *.
   unfold y_1 in |- *.
   rewrite <- H27 in |- *.
   apply isTri_Flip2.
   tauto.
  tauto.
  tauto.
  tauto.
 rewrite H28 in |- *.
    tauto.
  tauto.
 rewrite H28 in |- *.
   unfold expf in |- *.
    tauto.
 rewrite H28 in |- *.
    tauto.
  tauto.
split.
  tauto.
(* END OF isTRi m2 z *)
assert (2 <= degreev m y).
 lia.
unfold isTriangulation in H8.
  generalize (H8 x H).
  intro.
  generalize (H8 y H18).
  intro.
  generalize
  (cF_Flip1_detail_1 m x H4 H6 H H0 H31 H7 H9 H32 H33).
  fold y in |- *.
  fold y_1 in |- *.
  fold x_1 in |- *.
  fold m1 in |- *.
  fold xff in |- *.
  fold yff in |- *.
  intro.
 assert (x = cF m1 y).
 symmetry  in |- *.
    tauto.
assert (isHexa m1 x).
  tauto.
assert (inv_hmap m1).
  tauto.
assert (isMap m1).
  tauto.
rewrite H35 in H36.
  rewrite H35 in H23.
  generalize 
 (cF_Flip2_detail_1 m1 y H37 H38 H20 H36 H23 H29).
 rewrite <- H35 in |- *.
  clear H36 H37 H38.
  clear H32 H33.
  clear H22.
  clear H35.
  decompose [and] H34.
  rewrite H33 in |- *.
  rewrite H32 in |- *.
  rewrite H35 in |- *.
  rewrite H36 in |- *.
  fold m2 in |- *.
  clear H22 H33 H32 H35 H36 H38.
intro.
 fold y_1 in H27.
  assert (crackv m1 y y_1).
 generalize (degreev_crackv m1 y).
   rewrite H27 in |- *.
    tauto.
assert (inv_hmap m1).
  tauto.
assert (cF_1 m1 y = yff).
 assert (cF m1 yff = y).
   tauto.
 rewrite <- H35 in |- *.
   rewrite cF_1_cF in |- *.
   tauto.
  tauto.
 generalize (exd_cF m1 yff).
   rewrite H35 in |- *.
    tauto.
assert (expf m1 (cF_1 m1 y) y_1).
 rewrite H35 in |- *.
   assert (cF m1 x_1 = yff).
   tauto.
 rewrite <- H36 in |- *.
   clear H36.
   assert (x_1 = cF m2 xff).
   tauto.
 assert (cF m1 xff = x_1).
   tauto.
 rewrite <- H37 in |- *.
   clear H36 H37.
   assert (cF m1 y_1 = xff).
   tauto.
 rewrite <- H36 in |- *.
   clear H36.
   apply expf_symm.
   unfold expf in |- *.
   split.
   tauto.
 assert (cF = MF.f).
   tauto.
 rewrite H36 in |- *.
   clear H36.
 unfold MF.expo in |- *.
   split.
  rewrite <- H27 in |- *.
    generalize (exd_cA_1 m1 one y).
     tauto.
 split with 3.
   simpl in |- *.
    tauto.
rename H9 into Exy.
clear H31 H26 H25 H24 H18 b H16 H15 H14 H13 H11 H0 H H7 H1.
  generalize 
   (expof_Split1_CNS m1 y y_1 z x H33 H32 H21).
  simpl in |- *.
  fold m2 in |- *.
  rewrite H35 in |- *.
  rewrite H35 in H36.
  elim (expof_dec m1 yff y_1 H33).
 intro.
   intro.
   assert
    (~
     (betweenf m1 y_1 z yff /\ 
       betweenf m1 y_1 x yff \/
      betweenf m1 y z (cF_1 m1 y_1) /\ 
       betweenf m1 y x (cF_1 m1 y_1) \/
      ~ expof m1 yff z /\ expof m1 z x)).
  intro.
 elim H0.
   clear H0.
     intro.
     assert (exd m1 y_1).
    apply MF.expo_exd with yff.
      tauto.
    unfold expf in H36.
       tauto.
   assert (expf m1 y_1 z).
    unfold expf in |- *.
      split.
      tauto.
    generalize (MF.between_expo m1 y_1 z yff).
      unfold betweenf in H0.
       tauto.
 elim H19.
     apply expof_trans with y_1.
    assert (cF m1 x = y_1).
      tauto.
    rewrite <- H9 in |- *.
      unfold expof in |- *.
      unfold MF.expo in |- *.
      split.
     rewrite <- H28 in |- *.
       generalize (exd_cA m1 zero y).
        tauto.
    split with 1.
      simpl in |- *.
       tauto.
   unfold expf in H7.
      tauto.
clear H0.
    intro.
    elim H0.
   clear H0.
     intro.
     assert (expf m1 y z).
    unfold expf in |- *.
      split.
      tauto.
    generalize (MF.between_expo m1 y z (cF_1 m1 y_1)).
      unfold betweenf in H0.
       tauto.
   elim H19.
     apply expof_trans with y.
    assert (cF m1 y = x).
      tauto.
    apply expof_symm.
      tauto.
    rewrite <- H7 in |- *.
      unfold expof in |- *.
      unfold MF.expo in |- *.
      split.
      tauto.
    split with 1.
      simpl in |- *.
       tauto.
   unfold expf in H1.
      tauto.
 clear H0.
    intro.
    elim H19.
    apply expof_symm.
    tauto.
   tauto.
 assert (~ expof m2 z x).
   tauto.
 clear H0.
   clear H.
 assert (~ expof m2 y z).
  intro.
    elim H1.
    clear H1.
    apply expof_trans with y.
   apply expof_symm.
     tauto.
    tauto.
  assert (x = cF m2 y).
    tauto.
  rewrite H0 in |- *.
    unfold expof in |- *.
    unfold MF.expo in |- *.
    split.
   unfold m2 in |- *.
     generalize (exd_Split m1 one y y_1 y).
      tauto.
  split with 1.
    simpl in |- *.
     tauto.
 generalize 
 (expof_Split1_CNS m1 y y_1 z xff H33 H32 H21).
   simpl in |- *.
   fold m2 in |- *.
   rewrite H35 in |- *.
   elim (expof_dec m1 yff y_1 H33).
  intro.
    intro.
assert (cF_1 m1 y_1=x).
 assert (cF m1 x = y_1).
     tauto.
 rewrite <- H7 in |- *.
     rewrite cF_1_cF in |- *.
     tauto.
    tauto.
   rewrite <- H28 in |- *.
     generalize (exd_cA m1 zero y).
      tauto.
 assert (~(betweenf m1 y_1 z yff /\ 
           betweenf m1 y_1 xff yff \/
       betweenf m1 y z x /\ betweenf m1 y xff x \/
       ~ expof m1 yff z /\ expof m1 z xff)).
intro.
 elim H9. 
  clear H9.
  intro.
      assert (exd m1 y_1).
     apply MF.expo_exd with yff.
       tauto.
     unfold expf in H36.
        tauto.
assert (expf m1 y_1 z).
    unfold expf in |- *.
      split.
      tauto.
    generalize (MF.between_expo m1 y_1 z yff).
      unfold betweenf in H9.
       tauto.
elim H19.
     apply expof_trans with y_1.
    assert (cF m1 x = y_1).
      tauto.
    rewrite <- H14 in |- *.
      unfold expof in |- *.
      unfold MF.expo in |- *.
      split.
     rewrite <- H28 in |- *.
       generalize (exd_cA m1 zero y).
        tauto.
    split with 1.
      simpl in |- *.
       tauto.
   unfold expf in H13.
      tauto.
clear H9.
    intro.
    elim H9.
   clear H9.
     intro.
     assert (expf m1 y z).
    unfold expf in |- *.
      split.
      tauto.
    generalize (MF.between_expo m1 y z x).
      unfold betweenf in H9.
       tauto.
   elim H19.
     apply expof_trans with y.
    assert (cF m1 y = x).
      tauto.
    apply expof_symm.
      tauto.
    rewrite <- H13 in |- *.
      unfold expof in |- *.
      unfold MF.expo in |- *.
      split.
      tauto.
    split with 1.
      simpl in |- *.
       tauto.
   unfold expf in H11.
      tauto.
 clear H9.
    intro.
    elim H19.
    apply expof_symm.
    tauto.
apply expof_trans with xff.
tauto.
apply expof_symm.
tauto.
assert (cF m1 y_1 = xff).
tauto.
rewrite <-H11.
assert (cF m1 x = y_1).
tauto.
rewrite <-H13.
clear H11 H13.
unfold expof in |- *.
      unfold MF.expo in |- *.
      split.
rewrite <-H28. 
generalize (exd_cA m1 zero y).
tauto.
 split with 2.
simpl.
tauto.
assert (~expof m2 z xff).
rewrite H7 in H0.
tauto.
clear H0 H9.
assert (exd m2 y).
unfold m2.
generalize (exd_Split m1 one y y_1 y).
tauto.
assert (exd m2 x).
assert (x = cF m2 y).
tauto.
generalize (exd_cF m2 y).
rewrite <-H9.
tauto.
assert (exd m1 y_1).
rewrite <-H27.
generalize (exd_cA_1 m1 one y).
tauto.
assert (exd m2 y_1).
unfold m2.
generalize (exd_Split m1 one y y_1 y_1).
tauto.
assert (xff = cF m2 y_1).
tauto.
assert (exd m2 xff).
generalize (exd_cF m2 y_1).
rewrite <-H15.
tauto.
assert (expf m2 y_1 xff).
unfold expf.
split. tauto.
unfold MF.expo.
split.
tauto.
split with 1.
simpl.
rewrite H15.
tauto.
assert (degreef m2 y_1 = degreef m2 xff).
assert (degreef = MF.degree).
tauto.
rewrite H24.
apply MF.expo_degree.
tauto.
unfold expf in H18.
tauto.
assert (isQuad m2 xff).
unfold isQuad.
rewrite <-H24.
unfold isQuad in IS.
tauto.
assert (exd m2 z).
unfold m2.
generalize (exd_Split m1 one y y_1 z).
tauto.
assert (exd m y).
unfold m1 in H20. 
generalize (exd_Split m one x x_1 y). 
tauto.
assert (exd m x).
generalize (exd_cA m zero x).
fold y.
tauto.
assert (y= cA m1 zero x).
unfold m1.
unfold x_1.
rewrite cA0_Flip1.
fold y.
tauto.
tauto.
tauto.
tauto.
assert (y = cA m2 zero x).
unfold m2.
rewrite <-H27.
rewrite cA0_Flip2.
tauto.
tauto.
tauto.
rewrite <-H28.
generalize (exd_cA m1 zero y).
tauto.
assert (isTri m3 z).
unfold m3.
apply (isTri_Flip3 m2 xff x z).
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
rewrite <-H39.
tauto.
intro.
elim H11.
apply expof_symm.
tauto.
tauto.
split.
tauto.
(* END OF isTri m3 z *)
clear H2 H3 H33.
  assert (inv_hmap m2).
  tauto.
assert (isMap m2).
  tauto.
assert (isBar m2 x).
  tauto.
generalize (cF_Flip3_detail_1 m2 xff x H2 H3 H33 H25 H9 H16).
cbv zeta.
fold m3.
  decompose [and] H22.
  rewrite <- H43 in |- *.
  rewrite <- H45 in |- *.
  rewrite <- H47 in |- *.
  rewrite <- H42 in |- *.
intro.
clear H41 H42 H43 H44 H45 H47.
clear H2 H3 H33.
assert (exd m3 x).
unfold m3.
generalize (exd_Merge m2 one xff x x).
tauto.
assert (exd m3 y).
unfold m3.
generalize (exd_Merge m2 one xff x y).
tauto.
assert (xff = cF m3 y).
tauto.
assert (exd m3 xff).
generalize (exd_cF m3 y).
rewrite H33.
tauto.
assert (x_1 = cF m3 xff).
tauto.
assert (exd m3 x_1).
generalize (exd_cF m3 xff).
rewrite <-H42.
tauto.
assert (yff = cF m3 x_1).
tauto.
assert (exd m3 yff).
generalize (exd_cF m3 x_1).
rewrite <-H44.
tauto.
clear H33 H42 H44.
assert (cA m3 one y = y).
unfold m3.
rewrite cA1_Flip3.
assert (isTriangulation m).
tauto.
assert (inv_hmap m).
tauto.
unfold isTriangulation in H33.
assert (isTri m x).
apply H8.
tauto.
assert (isTri m y).
apply H8.
tauto.
assert (cA m zero y = x).
rewrite <-H28.
unfold m1.
unfold x_1.
rewrite cA0_Flip1.
 tauto.
tauto.
tauto.
tauto.
assert (cA_1 m zero x = y).
rewrite <-H48.
rewrite cA_1_cA.
tauto.
tauto.
tauto.
assert (y_1 = cF m x).
unfold cF.
rewrite H49.
fold y_1.
tauto.
generalize 
   (Tri_diff_2faces m x y H4 H37 H31 H44 H47 Exy).
simpl.
rewrite <-H50.
fold xff.
intro.
elim (eq_dart_dec xff y).
tauto.
elim (eq_dart_dec x y).
tauto.
intros.
assert (isBar m2 y).
rewrite H39.
apply isBar_symm.
tauto.
tauto.
tauto.
unfold isBar in H52.
assert (inv_hmap m2).
tauto.
generalize (degreev_fixpt m2 y H53 H0).
tauto.
tauto.
tauto.
tauto.
assert (inv_hmap m2).
tauto.
generalize (degreev_fixpt m2 x H33 H9).
unfold isBar in IS.
tauto.
tauto.
assert (cA m2 zero y = x).
unfold m2.
rewrite <-H27.
rewrite cA0_Flip1.
tauto.
tauto.
tauto.
tauto.
assert (cA m3 zero y = x).
unfold m3.
rewrite cA0_Flip3.
tauto.
tauto.
tauto.
tauto.
tauto.
decompose [and] H46.
clear H46.
assert (yff = Iter (cF m3) 4 x).
unfold Iter; fold Iter.
rewrite <-H47.
rewrite <-H49.
rewrite <-H48.
tauto.
assert (degreef = MF.degree).
tauto.
assert (cF = MF.f).
tauto.
assert (degreef m3 y = degreef m3 yff).
rewrite H52.
apply MF.expo_degree.
tauto.
unfold MF.expo.
split.
tauto.
split with 3.
unfold Iter; fold Iter.
rewrite <-H54.
rewrite <-H49.
rewrite <-H48.
rewrite <-H50.
tauto.
unfold isHexa in IS.
assert (isHexa m3 yff).
unfold isHexa.
rewrite <-H55.
tauto.
assert (degreef m3 x = degreef m3 yff).
rewrite H52.
rewrite H46.
apply MF.degree_uniform.
tauto.
tauto.
assert (~ expf m3 x z).
intro.
assert (degreef m3 x = degreef m3 z).
rewrite H52.
apply MF.expo_degree.
tauto.
unfold expf in H58.
tauto.
unfold isHexa in H56. 
rewrite H56 in H57.
assert (degreef m3 z=3).
unfold isTri in H40.
tauto.
rewrite H57 in H59.
rewrite H60 in H59.
lia.
assert (inv_hmap m3).
tauto.
assert (exd m3 z).
unfold m3.
generalize (exd_Merge m2 one xff x z).
tauto.
unfold m4.
rewrite <-H44 in H46.  
rewrite <-H44 in H58.
apply (isTri_Flip4_2 m3 yff y z H59 H56 H33 H3 H45
 H60 H46 H58 H40).
unfold expf in H36. 
tauto.
unfold expf in H36. 
tauto.
Qed.

(* COMPILED IN 3 MIN *)

Lemma isTriExt_Flip_topo: 
 forall(m:fmap)(x z:dart),
  let y := cA m zero x in
  let m4:= Flip_topo m x in
   inv_Triangulation m -> 
    prec_Flip m x -> exd m z -> 
     ~expf m x z -> ~expf m y z ->
       isTri m4 z.
Proof.
intros.
unfold m4.
unfold Flip_topo.
unfold y.
generalize (isTriExt_Flip_1_4 m x z H H0).
tauto.
Qed.

(* FOLLOWING eqf IN Flip: *)

(* eqf_Flip1: *)

Lemma eqf_Flip1: forall(m:fmap)(x z:dart),
 inv_hmap m -> 
 exd m x -> exd m z ->
  let y := cA m zero x in
  let x_1 := cA_1 m one x in
  let m1 := Split m one x x_1 in
 x <> x_1 -> ~ expf m x y -> 
    (expf m1 x z <->
      (expf m x z \/ expf m y z)).
Proof.
intros.
assert (exd m y).
 unfold y in |- *.
   generalize (exd_cA m zero x).
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
   assert 
  (MA1.MfcA.f m (cA_1 m one x) = 
        cA m one (cA_1 m one x)).
   tauto.
 rewrite cA_cA_1 in H6.
   tauto.
  tauto.
  tauto.
generalize (expof_Split1_CNS m x x_1 x z H H6 H0).
  cbv zeta.
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
   elim H3.
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
 rewrite H8 in |- *.
   split with 1.
   simpl in |- *.
    tauto.
generalize H7.
  clear H7.
  elim (expof_dec m (cF_1 m x) x_1 H).
 unfold expf in H10.
    tauto.
intros.
  assert (expof m (cF_1 m x) x).
 unfold expof in |- *.
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
assert (~ expof m x_1 x).
 intro.
   elim b.
   apply expof_trans with x.
   tauto.
 apply expof_symm.
   tauto.
  tauto.
assert (expof m x_1 z <-> expof m y z).
 split.
  intro.
    apply expof_trans with x_1.
   rewrite H8 in |- *.
     unfold expof in |- *.
     unfold MF.expo in |- *.
     split.
     tauto.
   split with 1.
      tauto.
   tauto.
 intro.
   apply expof_trans with y.
  apply expof_symm.
    tauto.
  rewrite H8 in |- *.
    unfold expof in |- *.
    unfold MF.expo in |- *.
    split.
    tauto.
  split with 1.
    simpl in |- *.
     tauto.
  tauto.
unfold expf in |- *.
  assert (inv_hmap m1).
 unfold m1 in |- *.
   apply inv_hmap_Split.
    tauto.
 tauto.
Qed.

(* eqf_Flip2: *)

Lemma eqf_Flip2: 
forall(m1:fmap)(y z:dart)(H:inv_hmap m1),
  isMap m1 -> exd m1 y -> exd m1 z ->
  let y_1:= cA_1 m1 one y in
  let x := cA m1 zero y in
  let m2 := Split m1 one y y_1 in
     degreev m1 x = 1 -> 
       2 <= degreev m1 y -> 
        ((expf m2 x z \/ expf m2 y_1 z)
            <-> expf m1 x z).
Proof.
intros.
generalize (degreev_crackv m1 y H H1).
intro.
assert (crackv m1 y y_1).
 unfold y_1 in |- *.
    tauto.
assert (exd m1 y_1).
 unfold y_1 in |- *.
   generalize (exd_cA_1 m1 one y).
    tauto.
set (y_f := cF_1 m1 y) in |- *.
  assert (y = cA m1 one y_1).
 unfold y_1 in |- *.
   rewrite cA_cA_1 in |- *.
   tauto.
  tauto.
  tauto.
assert (x = cF_1 m1 y_1).
 unfold cF_1 in |- *.
   rewrite <- H8 in |- *.
    tauto.
assert (exd m1 x).
 unfold x in |- *.
   generalize (exd_cA m1 zero y).
    tauto.
generalize (degreev_fixpt m1 x H H10).
  intro.
  assert (cA m1 one x = x).
  tauto.
clear H11.
  assert (cA_1 m1 one x = x).
 rewrite <- H12 in |- *.
   rewrite cA_1_cA in |- *.
  symmetry  in |- *.
     tauto.
  tauto.
  tauto.
generalize (degreee_invol_nofixpt m1 y H H1).
  intros.
  generalize (invol_inverse m1 zero y H H1).
  intros.
  assert (degreee m1 y = 2).
 unfold isMap in H0.
   apply H0.
    tauto.
assert (cA m1 zero y <> y).
  tauto.
assert (cA m1 zero (cA m1 zero y) = y).
  tauto.
assert (cA m1 zero y = cA_1 m1 zero y).
  tauto.
clear H15 H13 H14.
  fold x in H17.
  assert (x = cF m1 y).
 unfold cF in |- *.
   fold x in H18.
   rewrite <- H18 in |- *.
   symmetry  in |- *.
    tauto.
assert (y = cF_1 m1 x).
 rewrite H13 in |- *.
   rewrite cF_1_cF in |- *.
   tauto.
  tauto.
  tauto.
assert (expof m1 y_f y_1).
 unfold y_f in |- *.
   rewrite H14 in |- *.
   rewrite H9 in |- *.
   unfold expof in |- *.
   unfold MF.expo in |- *.
   split.
  rewrite <- H9 in |- *.
    rewrite <- H14 in |- *.
    generalize (exd_cF_1 m1 y).
     tauto.
 split with 3.
   simpl in |- *.
   rewrite cF_cF_1 in |- *.
  rewrite cF_cF_1 in |- *.
   rewrite cF_cF_1 in |- *.
     tauto.
    tauto.
    tauto.
   tauto.
  rewrite <- H9 in |- *.
     tauto.
  tauto.
 rewrite <- H9 in |- *.
   rewrite <- H14 in |- *.
    tauto.
generalize (expof_Split1_CNS m1 y y_1 x z H H6 H10).
  simpl in |- *.
  fold m2 in |- *.
  rewrite <- H9 in |- *.
  fold y_f in |- *.
  elim (expof_dec m1 y_f y_1 H).
 intro.
   clear a.
   intro.
   assert (expof m1 y_f x).
  unfold y_f in |- *.
    rewrite H14 in |- *.
    unfold expof in |- *.
    unfold MF.expo in |- *.
    split.
   rewrite <- H14 in |- *.
     generalize (exd_cF_1 m1 y).
      tauto.
  split with 2.
    simpl in |- *.
    rewrite cF_cF_1 in |- *.
   rewrite cF_cF_1 in |- *.
     tauto.
    tauto.
    tauto.
   tauto.
  rewrite <- H14 in |- *.
     tauto.
 assert
  (expof m2 x z <->
   betweenf m1 y_1 x y_f /\ betweenf m1 y_1 z y_f \/
   betweenf m1 y x x /\ betweenf m1 y z x).
   tauto.
 clear H19.
   generalize 
 (expof_Split1_CNS m1 y y_1 y_1 z H H6 H7).
   simpl in |- *.
   fold m2 in |- *.
   fold y_f in |- *.
   rewrite <- H9 in |- *.
   elim (expof_dec m1 y_f y_1 H).
  intro.
    clear a.
    intro.
    assert
     (expof m2 y_1 z <->
      betweenf m1 y_1 y_1 y_f /\ 
         betweenf m1 y_1 z y_f \/
      betweenf m1 y y_1 x /\ betweenf m1 y z x).
    tauto.
  clear H19.
    assert (expof m1 y x).
   rewrite H13 in |- *.
     unfold expof in |- *.
     unfold MF.expo in |- *.
     split.
     tauto.
   split with 1.
     simpl in |- *.
      tauto.
  assert (betweenf m1 y x x).
   unfold betweenf in |- *.
     assert (MF.expo1 m1 y x).
    generalize (MF.expo_expo1 m1 y x).
       tauto.
   generalize (MF.between_expo_refl_2 m1 y x).
      tauto.
  assert (MF.expo m1 y_1 y_f).
   apply MF.expo_symm.
     tauto.
    tauto.
  assert (exd m1 y_f).
   unfold y_f in |- *.
     generalize (exd_cF_1 m1 y).
      tauto.
  assert (betweenf m1 y_1 y_1 y_f).
   unfold betweenf in |- *.
     assert (MF.expo1 m1 y_1 y_f).
    generalize (MF.expo_expo1 m1 y_1 y_f).
       tauto.
   generalize (MF.between_expo_refl_1 m1 y_1 y_f).
      tauto.
  assert
   (expof m2 y_1 z <->
    betweenf m1 y_1 z y_f \/ 
     betweenf m1 y y_1 x /\ betweenf m1 y z x).
    tauto.
  assert
   (expof m2 x z <->
    betweenf m1 y_1 x y_f /\ 
       betweenf m1 y_1 z y_f \/ betweenf m1 y z x).
    tauto.
  clear H21 H22.
    assert
     (expof m2 x z \/ expof m2 y_1 z <->
      betweenf m1 y z x \/ betweenf m1 y_1 z y_f).
    tauto.
  assert (y_1 = cF m1 x).
   rewrite H9 in |- *.
     rewrite cF_cF_1 in |- *.
     tauto.
    tauto.
    tauto.
  rewrite H22 in H21.
    unfold y_f in H21.
    split.
   intro.
     assert (betweenf m1 y z x \/ 
       betweenf m1 (cF m1 x) z (cF_1 m1 y)).
    rewrite <- H22 in H21.
      rewrite <- H22 in |- *.
      unfold expf in H29.
       tauto.
   elim H30.
    clear H30.
      intro.
      unfold betweenf in H30.
      generalize (MF.between_expo m1 y z x).
      intros.
      assert (MF.expo m1 y z /\ MF.expo m1 y x).
      tauto.
    clear H31.
      unfold expf in |- *.
      split.
      tauto.
    apply MF.expo_trans with y.
     apply MF.expo_symm.
       tauto.
      tauto.
     tauto.
   clear H30.
     intro.
     unfold betweenf in H30.
     generalize 
  (MF.between_expo m1 (cF m1 x) z (cF_1 m1 y)).
     rewrite <- H22 in |- *.
     rewrite <- H22 in H30.
     unfold expf in |- *.
     intro.
     assert 
 (MF.expo m1 y_1 z /\ MF.expo m1 y_1 (cF_1 m1 y)).
     tauto.
   clear H31.
     split.
     tauto.
   apply MF.expo_trans with y_1.
    apply MF.expo_trans with y_f.
     apply MF.expo_symm.
       tauto.
      tauto.
     tauto.
    tauto.
  intro.
    assert (expf m1 y z).
   apply expf_trans with x.
    unfold expf in |- *.
       tauto.
    tauto.
  assert (MF.expo1 m1 y z).
   unfold expf in H30.
     generalize (MF.expo_expo1 m1 y z).
      tauto.
  assert (MF.expo1 m1 y x).
   generalize (MF.expo_expo1 m1 y x).
      tauto.
  generalize (MF.expo_between_3 m1 y x z H H32 H31).
    intro.
    unfold betweenf in H21.
    assert (expof m2 x z \/ expof m2 (cF m1 x) z).
    tauto.
  rewrite <- H22 in H34.
    unfold expf in |- *.
    assert (inv_hmap m2).
   unfold m2 in |- *.
     apply (inv_hmap_Split m1 one y y_1).
      tauto.
   tauto.
  tauto.
 tauto.
Qed.

(* eqf_Flip3: *)

Lemma eqf_Flip3: 
forall(m2:fmap)(xff x z:dart),
    let y := cA m2 zero x in
    let y_1:= cF_1 m2 xff in
    let m3 := Merge m2 one xff x in
 inv_hmap m2 -> isMap m2 -> 
   isBar m2 x -> isQuad m2 y_1 -> 
  exd m2 x -> exd m2 xff -> exd m2 z ->
  (expf m3 x z <-> 
      (expf m2 x z \/ expf m2 y_1 z)).
Proof.
intros.
unfold m3 in |- *.
unfold isMap in H0.
assert (degreee m2 x = 2).
 apply (H0 x H3).
generalize (degreee_invol_nofixpt m2 x H H3).
  intro.
  generalize (invol_inverse m2 zero x H H3).
  intro.
  fold y in H8.
  fold y in H7.
  assert (y <> x /\ cA m2 zero y = x).
  tauto.
clear H7.
  assert (y = cA_1 m2 zero x).
  tauto.
clear H8.
  elim H9.
  clear H9.
  intros.
  unfold isBar in H1.
  assert (degreev m2 x = 1).
  tauto.
generalize (degreev_fixpt m2 x H H3).
  intro.
  assert (cA m2 one x = x).
  tauto.
clear H11.
  assert (cA_1 m2 one x = x).
 rewrite <- H12 in |- *.
   rewrite cA_1_cA in |- *.
  symmetry  in |- *.
     tauto.
  tauto.
  tauto.
assert (exd m2 y_1).
 generalize (exd_cF_1 m2 xff).
    tauto.
assert (expf m2 y_1 xff).
 unfold expf in |- *.
   split.
   tauto.
 unfold MF.expo in |- *.
   split.
   tauto.
 split with 1.
   simpl in |- *.
   unfold y_1 in |- *.
   rewrite cF_cF_1 in |- *.
   tauto.
  tauto.
  tauto.
assert (degreef m2 y_1 = degreef m2 xff).
 unfold degreef in |- *.
   apply MF0Tr.MfM.expo_degree.
   tauto.
 unfold expf in H14.
    tauto.
assert (~ expf m2 xff x).
 intro.
   assert (degreef m2 xff = degreef m2 x).
  unfold degreef in |- *.
    apply MF0Tr.MfM.expo_degree.
    tauto.
  unfold expf in H16.
     tauto.
 unfold isQuad in H2.
   rewrite H2 in H15.
   rewrite <- H15 in H17.
   rewrite <- H17 in H1.
    absurd (4 = 2).
   lia.
  tauto.
assert (xff <> x).
 intro.
   rewrite H17 in H16.
   elim H16.
   apply expf_refl.
   tauto.
  tauto.
assert (~ expv m2 xff x).
 intro.
   assert (expv m2 x xff).
  apply expv_symm.
    tauto.
   tauto.
 unfold expv in H19.
   assert (MA1.MfcA.expo2 m2 x xff).
  generalize (MA1.MfcA.expo_expo2 m2 x xff).
     tauto.
 unfold MA1.MfcA.expo2 in H20.
   elim H20.
   intros.
   clear H21.
   clear H20.
   elim H22.
   intros i Hi.
   clear H22.
   assert (MA1.MfcA.degree = degreev).
   tauto.
 rewrite H20 in Hi.
   elim Hi.
   intros.
   clear Hi.
   assert (i = 0).
   lia.
 rewrite H23 in H22.
   simpl in H22.
   symmetry  in H22.
    tauto.
assert (y = cF_1 m2 x).
 unfold cF_1 in |- *.
   rewrite H12 in |- *.
   fold y in |- *.
    tauto.
assert (expf m2 y x).
 unfold expf in |- *.
   split.
   tauto.
 unfold MF.expo in |- *.
   split.
  unfold y in |- *.
    generalize (exd_cA m2 zero x);  tauto.
 split with 1.
   simpl in |- *.
   rewrite H19 in |- *.
   rewrite cF_cF_1 in |- *.
   tauto.
  tauto.
  tauto.
generalize 
 (expof_Merge1_CNS m2 xff x x z H H4 H3 H18 H3).
  simpl in |- *.
  fold m3 in |- *.
  fold y in |- *.
  rewrite H11 in |- *.
  fold y_1 in |- *.
  elim (expof_dec m2 y xff H).
 intro.
   elim H16.
   apply expf_trans with y.
  apply expf_symm.
    unfold expf in |- *.
     tauto.
  tauto.
intro.
  intro.
  assert (expof m3 x z <-> 
     expof m2 x z \/ expof m2 xff z).
 unfold expf in H16.
   unfold expf in H20.
    tauto.
assert (expf m2 xff z <-> expf m2 y_1 z).
 split.
  intro.
    apply expf_trans with xff.
    tauto.
   tauto.
 intro.
   apply expf_trans with y_1.
  apply expf_symm.
     tauto.
  tauto.
unfold expf in H23.
  unfold expf in |- *.
  assert (inv_hmap m3).
 unfold m3 in |- *.
   apply inv_hmap_Merge1.
   tauto.
  tauto.
  tauto.
  tauto.
 tauto.
Qed.

(* eqf_Flip4: *)

Lemma eqf_Flip4: forall(m3:fmap)(yff y:dart)(z:dart),
 inv_hmap m3 -> isHexa m3 yff -> 
  cA m3 one y = y ->
   exd m3 y -> exd m3 yff -> exd m3 z -> 
    let x := cA m3 zero y in
    let m4 := Merge m3 one yff y in
      yff = Iter (cF m3) 4 x ->
 ((expf m4 x z \/ expf m4 y z) <-> expf m3 x z).
Proof.
intros.
assert (x = cF_1 m3 y).
 unfold cF_1 in |- *.
   rewrite H1 in |- *.
   fold x in |- *.
    tauto.
assert (exd m3 x).
 generalize (exd_cA m3 zero y).
   fold x in |- *.
    tauto.
assert (degreev m3 y = 1).
 generalize (degreev_fixpt m3 y H H2).
    tauto.
assert (y = Iter (cF m3) 1 x).
 simpl in |- *.
   rewrite H6 in |- *.
   rewrite cF_cF_1 in |- *.
   tauto.
  tauto.
  tauto.
assert (cF = MF.f).
  tauto.
assert (degreef = MF.degree).
  tauto.
assert (y <> yff).
 intro.
   assert (degreef m3 x = degreef m3 yff).
  rewrite H5 in |- *.
    rewrite H11 in |- *.
    rewrite H10 in |- *.
    apply MF.degree_uniform.
    tauto.
   tauto.
 unfold isHexa in H0.
   rewrite H0 in H13.
   assert (1 = 4).
  apply (MF.degree_unicity m3 x).
    tauto.
   tauto.
  rewrite <- H11 in |- *.
     lia.
  rewrite <- H11 in |- *.
     lia.
  rewrite <- H10 in |- *.
    rewrite <- H9 in |- *.
    rewrite <- H5 in |- *.
     tauto.
  lia.
assert (cA_1 m3 one y = y).
 rewrite <- H1 in |- *.
   rewrite cA_1_cA in |- *.
  symmetry  in |- *.
     tauto.
  tauto.
  tauto.
assert (~ expv m3 yff y).
 intro.
   assert (expv m3 y yff).
  apply expv_symm.
    tauto.
   tauto.
 unfold expv in H15.
   assert (MA1.MfcA.expo2 m3 y yff).
  generalize (MA1.MfcA.expo_expo2 m3 y yff).
     tauto.
 unfold MA1.MfcA.expo2 in H16.
   elim H16.
   clear H16.
   intros.
   clear H16.
   elim H17.
   clear H17.
   intros i Hi.
   elim Hi.
   clear Hi.
   intros.
   assert (MA1.MfcA.degree = degreev).
   tauto.
 rewrite H18 in H16.
   assert (i = 0).
   lia.
 rewrite H19 in H17.
   simpl in H17.
    tauto.
assert (expf m3 x yff).
 unfold expf in |- *.
   split.
   tauto.
 unfold MF.expo in |- *.
   split.
   tauto.
 split with 4.
   rewrite <- H10 in |- *.
   symmetry  in |- *.
    tauto.
generalize 
 (expof_Merge1_CNS m3 yff y x z H H3 H2 H14 H7).
  simpl in |- *.
  fold m4 in |- *.
  fold x in |- *.
  rewrite H13 in |- *.
  set (x_1 := cF_1 m3 yff) in |- *.
  elim (expof_dec m3 x yff H).
 intro.
   intro.
   clear a.
   generalize 
   (expof_Merge1_CNS m3 yff y y z H H3 H2 H14 H2).
   simpl in |- *.
   fold m4 in |- *.
   fold x in |- *.
   rewrite H13 in |- *.
   fold x_1 in |- *.
   elim (expof_dec m3 x yff H).
  intros.
    clear a.
    assert (expof m3 x x).
   apply expof_refl.
      tauto.
  assert (expof m3 x y).
   unfold expof in |- *.
     unfold MF.expo in |- *.
     split.
     tauto.
   split with 1.
     rewrite <- H10 in |- *.
     symmetry  in |- *.
      tauto.
  assert (MF.expo1 m3 yff x).
   assert (MF.expo m3 yff x).
    apply MF.expo_symm.
      tauto.
    unfold expf in H15.
       tauto.
   generalize (MF.expo_expo1 m3 yff x).
      tauto.
  assert (betweenf m3 yff x x).
   unfold betweenf in |- *.
     generalize (MF.between_expo_refl_2 m3 yff x).
      tauto.
  assert (expf m3 x_1 yff).
   unfold expf in |- *.
     split.
     tauto.
   unfold MF.expo in |- *.
     split.
    generalize (exd_cF_1 m3 yff);  tauto.
   split with 1.
     simpl in |- *.
     unfold x_1 in |- *.
     simpl in |- *.
     rewrite cF_cF_1 in |- *.
     tauto.
    tauto.
    tauto.
  assert (expf m3 y x_1).
   apply expf_trans with yff.
    apply expf_trans with x.
     apply expf_symm.
       unfold expf in |- *.
        tauto.
     tauto.
   apply expf_symm.
      tauto.
  assert (MF.expo1 m3 y x_1).
   generalize (MF.expo_expo1 m3 y x_1).
     unfold expf in H23.
      tauto.
  assert (betweenf m3 y y x_1).
   unfold betweenf in |- *.
     generalize (MF.between_expo_refl_1 m3 y x_1).
      tauto.
  clear H20 H24.
    assert (~ betweenf m3 y x x_1).
   unfold betweenf in |- *.
     unfold MF.between in |- *.
     intro.
     elim H20.
    clear H20.
      intros i Hi.
      elim Hi; clear Hi.
      intros j Hj.
      decompose [and] Hj.
      clear Hj.
      assert (expf m3 y yff).
     apply expf_trans with x.
      apply expf_symm.
        unfold expf in |- *.
         tauto.
      tauto.
    assert (MF.Iter_upb m3 y = MF.degree m3 y).
     rewrite MF.upb_eq_degree in |- *.
       tauto.
      tauto.
      tauto.
    assert (MF.degree m3 y = MF.degree m3 yff).
     apply MF.expo_degree.
       tauto.
     unfold expf in H27.
        tauto.
    unfold isHexa in H0.
      rewrite H11 in H0.
      rewrite H0 in H30.
      rewrite H30 in H29.
      unfold x_1 in H26.
      assert (yff = Iter (MF.f m3) 3 y).
     rewrite H9 in |- *.
       rewrite H5 in |- *.
       simpl in |- *; rewrite <- H10 in |- *.
        tauto.
    assert (cF_1 m3 yff = Iter (MF.f m3) 2 y).
     rewrite H31 in |- *.
       assert (cF_1 = MF.f_1).
       tauto.
     rewrite H32 in |- *.
       apply MF.f_1_Iter_f.
       tauto.
      tauto.
    rewrite H32 in H26.
      assert (j = 2).
     apply (MF.degree_unicity m3 y j 2).
       tauto.
      tauto. clear H18 H19 H16 H17 H15 H27 H22 H23.
      lia. clear H18 H19 H16 H17 H15 H27 H22 H23.
      lia.
      tauto.
    assert (degreef m3 x = degreef m3 y).
     unfold degreef in |- *.
       apply MF0Tr.MfM.expo_degree.
       tauto.
     unfold expof in H19.
        tauto.
    assert (Iter (MF.f m3) 5 y = x).
     rewrite H9 in |- *.
       rewrite H10 in |- *.
       rewrite <- MF.Iter_comp in |- *.
       rewrite H11 in H34.
       assert (5 + 1 = 6). clear H18 H19 H16 H17 H15 H27 H22 H23.
       lia.
     rewrite H35 in |- *.
       rewrite <- H30 in |- *.
       rewrite <- H34 in |- *.
       apply MF.degree_per.
       tauto.
      tauto.
    assert (i = 5).
     apply (MF.degree_unicity m3 y i 5).
       tauto.
      tauto. clear H18 H19 H16 H17 H15 H27 H22 H23.
      lia. clear H18 H19 H16 H17 H15 H27 H22 H23.
      lia.
     rewrite H35 in |- *.
        tauto. clear H18 H19 H16 H17 H15 H27 H22 H23.
     lia.
    tauto.
    tauto.
  assert (~ betweenf m3 yff y x).
   unfold betweenf in |- *.
     unfold MF.between in |- *.
     intro.
     elim H24.
    clear H24.
      intros i Hi.
      elim Hi; clear Hi.
      intros j Hj.
      decompose [and] Hj.
      clear Hj.
      assert (MF.Iter_upb m3 yff = degreef m3 yff).
     rewrite H11 in |- *.
       apply MF.upb_eq_degree.
       tauto.
      tauto.
    assert (MF.f_1 m3 (Iter (MF.f m3) i yff) = x).
     rewrite H24 in |- *.
       rewrite H9 in |- *.
       simpl in |- *.
       rewrite cF_1_cF in |- *.
       tauto.
      tauto.
      tauto.
    elim (Nat.eq_dec i 0).
     intro.
       rewrite a in H24.
       simpl in H24.
       symmetry  in H24.
        tauto.
    intro.
      assert (i = S (i - 1)).  clear H18 H19 H16 H17 H15 H27 H22 H23.
      lia.
    rewrite H31 in H30.
      rewrite MF.f_1_Iter_f in H30.
     assert (j = i - 1).
      apply (MF.degree_unicity m3 yff j (i - 1)).
        tauto.
       tauto.
      rewrite <- H11 in |- *. clear H18 H19 H16 H17 H15 H27 H22 H23.
         lia.
      rewrite <- H11 in |- *. clear H18 H19 H16 H17 H15 H27 H22 H23.
         lia.
      rewrite H30 in |- *. 
         tauto.
     clear H31. clear H18 H19 H16 H17 H15 H27 H22 H23.
        lia.
     tauto.
     tauto.
    tauto.
    tauto.
  assert (expof m4 x z <-> betweenf m3 yff z x).
    tauto.
  assert (expof m4 y z <-> betweenf m3 y z x_1).
    tauto.
  assert (expof m4 y z <-> 
    betweenf m3 (cF m3 x) z (cF_1 m3 yff)).
   fold x_1 in |- *.
     simpl in H9.
     rewrite <- H9 in |- *.
      tauto.
  clear H27.
    assert
     (betweenf m3 yff z x \/
     betweenf m3 (cF m3 x) z (cF_1 m3 yff) <->
      expf m3 x z).
   split.
    intro.
      elim H27.
     clear H27.
       intro.
       generalize (MF.between_expo m3 yff z x).
       intro.
       unfold expf in |- *.
       split.
       tauto.
     apply MF.expo_trans with yff.
      unfold expf in H15.
         tauto.
     unfold betweenf in H27.
        tauto.
    clear H27.
      intro.
      simpl in H9.
      rewrite <- H9 in H27.
      generalize 
    (MF.between_expo m3 y z (cF_1 m3 yff)).
      intro.
      unfold expf in |- *.
      split.
      tauto.
    apply MF.expo_trans with y.
      tauto.
     tauto.
   intro.
     assert (MF.expo1 m3 yff x).
    assert (expf m3 yff x).
     apply expf_symm.
        tauto.
    unfold expf in H29.
      generalize (MF.expo_expo1 m3 yff x).
       tauto.
   assert (MF.expo1 m3 yff z).
    assert (expof m3 yff z).
     apply expof_trans with x.
      apply expof_symm.
        tauto.
      unfold expf in H15.
         tauto.
     unfold expf in H27.
        tauto.
    generalize (MF.expo_expo1 m3 yff z).
       tauto.
   unfold betweenf in |- *.
     apply MF.expo_between_3.
     tauto.
    tauto.
    tauto.
  assert (inv_hmap m4).
   unfold m4 in |- *.
     apply inv_hmap_Merge1.
     tauto.
    tauto.
    tauto.
    tauto.
  unfold expf in |- *.
    unfold expf in H27.
     tauto.
 unfold expf in H15.
    tauto.
unfold expf in H15.
   tauto.
Qed.

(* SYNTHESIS: eqf_Flip_1_4: *)
(* COMPILED IN 13 MIN *)

Theorem eqf_Flip_1_4: forall(m:fmap)(x z:dart),
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
    prec_Flip m x -> exd m z -> 
     ((expf m x z \/ expf m y z)
      <->
      (expf m4 x z \/ expf m4 y z)).
Proof.
intros.
generalize (inv_hmap_Flip_1_4 m x H H0).
generalize (isMap_Flip_1_4 m x H H0).
generalize (isSubd_Flip_1_4 m x H H0).
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
rename H2 into IS.
rename H3 into IM.
rename H4 into IH.
unfold prec_Flip in H0.
unfold inv_Triangulation in H.
fold y in H0.
assert (crackv m x x_1).
 unfold x_1 in |- *.
   apply degreev_crackv.
   tauto.
  tauto.
  lia.
assert (x <> x_1).
 unfold crackv in H2.
   unfold MA1.crack in H2.
    tauto.
assert (inv_hmap m).
  tauto.
assert (exd m x).
  tauto.
assert (~ expf m x y).
  tauto.
unfold y in H6.
  unfold x_1 in H3.
  assert (expf m1 x z <-> expf m x z \/ expf m y z).
 apply (eqf_Flip1 m x z H4 H5 H1 H3 H6).
clear H3 H4 H5 H6.
  assert (exd m y).
 unfold y in |- *.
   generalize (exd_cA m zero x).
    tauto.
rename H3 into Ey.
  assert (exd m1 x).
 unfold m1 in |- *.
   generalize (exd_Split m one x x_1 x).
    tauto.
assert (exd m1 z).
 unfold m1 in |- *.
   generalize (exd_Split m one x x_1 z).
    tauto.
assert
 (isHexa m1 x /\
  isBar m2 x /\ isQuad m2 y_1 /\ 
    isHexa m3 y /\ isTri m4 x /\ isTri m4 y).
  tauto.
clear IS.
  rename H5 into IS.
  assert (inv_hmap m1 /\ inv_hmap m2 /\ 
        inv_hmap m3 /\ inv_hmap m4).
  tauto.
clear IH.
  rename H5 into IH.
  assert (isMap m1 /\ isMap m2 /\ 
     isMap m3 /\ isMap m4).
  tauto.
clear IM.
  rename H5 into IM.
  assert (degreee m x = 2).
 assert (isMap m).
   tauto.
 unfold isMap in H5.
   apply H5.
    tauto.
generalize (degreee_invol_nofixpt m x).
  intro.
  fold y in H6.
  assert (y <> x).
  tauto.
assert (cA m zero y = x).
  tauto.
clear H6.
  assert (cA m1 zero y = x).
 unfold m1 in |- *.
   unfold x_1 in |- *.
   rewrite cA0_Flip1 in |- *.
   tauto.
  tauto.
  tauto.
  tauto.
assert (degreev m1 x = 1).
 unfold m1 in |- *.
   unfold x_1 in |- *.
   assert (inv_hmap m).
   tauto.
 rewrite (degreev_Flip1 m x x H10) in |- *.
  elim (eq_dart_dec x x).
    tauto.
   tauto.
  tauto.
  tauto. clear H7.
  lia.
assert (2 <= degreev m1 y).
 unfold m1 in |- *.
   unfold x_1 in |- *.
   assert (inv_hmap m).
   tauto.
 rewrite (degreev_Flip1 m x y H11) in |- *.
  elim (eq_dart_dec x y).
   intro.
     symmetry  in a.
      tauto.
  elim (expv_dec m (cA_1 m one x) y H11).
   intros.  clear H7.
      lia.
  intros.   clear H7.
     lia.
  tauto.
  tauto.  clear H7.
  lia.
assert (cA m one x <> y).
 intro.
    absurd (expv m x y).
   tauto.
 rewrite <- H12 in |- *.
   unfold expv in |- *.
   unfold MA1.MfcA.expo in |- *.
   split.
   tauto.
 split with 1.
   simpl in |- *.
    tauto.
assert (cA_1 m1 one y = y_1).
 unfold m1 in |- *.
   unfold x_1 in |- *.
   rewrite cA1_1_Flip1 in |- *.
  elim (eq_dart_dec (cA m one x) y).
   intro.
     symmetry  in a.
     symmetry  in a.
      tauto.
  elim (eq_dart_dec x y).
   intros.
     symmetry  in a.
      tauto.
  fold y_1 in |- *.
     tauto.
  tauto.  clear H7.
  lia.
  tauto.
  tauto.
assert (exd m1 y).
 unfold m1 in |- *.
   generalize (exd_Split m one x x_1 y).
    tauto.
assert (expf m2 x z \/ expf m2 y_1 z <-> expf m1 x z).
 rewrite <- H13 in |- *.
   unfold m2 in |- *.
   rewrite <- H6 in |- *.
   rewrite <- H13 in |- *.
   apply eqf_Flip2.
   tauto.
  tauto.
  tauto.
  tauto.
 rewrite H6 in |- *.
    tauto.
  tauto.
assert (cA m2 zero y = x).
 unfold m2 in |- *.
   rewrite <- H13 in |- *.
   rewrite cA0_Flip2 in |- *.
   tauto.
  tauto.
  tauto.
  tauto.
assert (exd m2 x).
 unfold m2 in |- *.
   generalize (exd_Split m1 one y y_1 x).
    tauto.
assert (exd m2 z).
 unfold m2 in |- *.
   generalize (exd_Split m1 one y y_1 z).
    tauto.
assert (exd m2 y).
 generalize (exd_cA m2 zero y).
   rewrite H16 in |- *.
    tauto.
assert (degreee m2 y = 2).
 assert (isMap m2).
   tauto.
 unfold isMap in H20.
   apply H20.
    tauto.
generalize (degreee_invol_nofixpt m2 y).
  rewrite H16 in |- *.
  intro.
  assert (cA m2 zero x = y).
  tauto.
clear H21.
  assert (y = cA_1 m zero x).
 rewrite <- H9 in |- *.
   rewrite cA_1_cA in |- *.
   tauto.
  tauto.
  tauto.
assert (y_1 = cF m x).
 unfold cF in |- *.
   rewrite <- H21 in |- *.
   fold y_1 in |- *.
    tauto.
assert (y_1 = cF m1 x).
 unfold m1 in |- *.
   unfold x_1 in |- *.
   rewrite cF_Flip1 in |- *.
  elim (eq_dart_dec (cF_1 m x) x).
   intro.
     assert (x = cF m x).
    rewrite <- a in |- *.
      rewrite cF_cF_1 in |- *.
      tauto.
     tauto.
     tauto.
   assert (isTri m x).
    assert (isTriangulation m).
      tauto.
    unfold isTriangulation in H25.
      apply H25.
       tauto.
   generalize (Tri_diff_face m x).
     simpl in |- *.
      tauto.
  intros.
    fold y in |- *.
    elim (eq_dart_dec y x).
    tauto.
   tauto.
  tauto.  clear H7 H15.
  lia.
  tauto.
  tauto.
assert (cF m1 y_1 = xff).
 unfold m1 in |- *.
   unfold x_1 in |- *.
   rewrite cF_Flip1 in |- *.
  elim (eq_dart_dec (cF_1 m x) y_1).
   intro.
     assert (x = cF m y_1).
    rewrite <- a in |- *.
      rewrite cF_cF_1 in |- *.
      tauto.
     tauto.
     tauto.
   rewrite H25 in H23.
     assert (isTri m y_1).
    assert (isTriangulation m).
      tauto.
    unfold isTriangulation in H26.
      apply H26.
      unfold y_1 in |- *.
      generalize (exd_cA_1 m one y).
       tauto.
   generalize (Tri_diff_face m y_1).
     simpl in |- *.
     assert (exd m y_1).
    unfold y_1 in |- *.
      generalize (exd_cA_1 m one y).
       tauto.
    tauto.
  fold y in |- *.
    elim (eq_dart_dec y y_1).
   intros.
     generalize (degreev_crackv m y).
     fold y_1 in |- *.
     intro.
     assert (crackv m y y_1).
    apply H25.
      tauto.
     tauto.  clear H7 H15.
     lia.
   clear H25.
     unfold crackv in H26.
     unfold MA1.crack in H26.
      tauto.
   tauto.
  tauto.  clear H7 H15.
  lia.
  tauto.
 rewrite H23 in |- *.
   generalize (exd_cF m x).
    tauto.
assert (xff = cF m2 y_1).
 unfold m2 in |- *.
   rewrite <- H13 in |- *.
   rewrite cF_Flip2 in |- *.
  rewrite H13 in |- *.
    elim (eq_dart_dec (cF_1 m1 y) y_1).
   intro.
     assert (y = cF m1 y_1).
    rewrite <- a in |- *.
      rewrite cF_cF_1 in |- *.
      tauto.
     tauto.
     tauto.
   rewrite H25 in H26.
     assert (isTriangulation m).
     tauto.
   unfold isTriangulation in H27.
     assert (isTri m x).
    apply H27.
       tauto.
   assert (isTri m y).
    apply H27.
       tauto.
   generalize (Tri_diff_2faces m x y).
     simpl in |- *.
     rewrite <- H23 in |- *.
     fold xff in |- *.
     symmetry  in H26.
      tauto.
  rewrite H6 in |- *.
    elim (eq_dart_dec x y_1).
   intros.
      absurd (expv m x y).
     tauto.
   rewrite a in |- *.
     unfold expv in |- *.
     unfold MA1.MfcA.expo in |- *.
     split.
    rewrite <- a in |- *.
       tauto.
   split with 1.
     simpl in |- *.
     assert (MA1.MfcA.f m y_1 = cA m one y_1).
     tauto.
   rewrite H26 in |- *.
     unfold y_1 in |- *.
     rewrite cA_cA_1 in |- *.
     tauto.
    tauto.
    tauto.
  symmetry  in H25.
     tauto.
  tauto.
  tauto.
 rewrite H13 in |- *.
   rewrite <- H13 in |- *.
   generalize (exd_cA_1 m1 one y).
    tauto.
  tauto.
assert (exd m1 y_1).
 rewrite H24 in |- *.
   generalize (exd_cF m1 x).
    tauto.
assert (exd m2 y_1).
 unfold m2 in |- *.
   generalize (exd_Split m1 one y y_1 y_1).
    tauto.
assert (exd m2 xff).
 generalize (exd_cF m2 y_1).
   rewrite <- H26 in |- *.
    tauto.
assert (y_1 = cF_1 m2 xff).
 rewrite H26 in |- *.
   rewrite cF_1_cF in |- *.
   tauto.
  tauto.
  tauto.
assert (expf m3 x z <-> expf m2 x z \/ expf m2 y_1 z).
 unfold m3 in |- *.
   rewrite H30 in |- *.
   apply eqf_Flip3.
   tauto.
  tauto.
  tauto.
 rewrite <- H30 in |- *.
    tauto.
  tauto.
  tauto.
  tauto.
(* END OF PART 3 *)
assert (exd m3 y).
 unfold m3 in |- *.
   generalize (exd_Merge m2 one xff x y).
    tauto.
assert (exd m3 xff).
 unfold m3 in |- *.
   generalize (exd_Merge m2 one xff x xff).
    tauto.
assert (exd m3 z).
 unfold m3 in |- *.
   generalize (exd_Merge m2 one xff x z).
    tauto.
assert (x = cA m3 zero y).
 unfold m3 in |- *.
   rewrite cA0_Flip4 in |- *.
  rewrite <- H22 in |- *.
generalize (degreee_invol_nofixpt m2 x).
 intros.
    symmetry  in |- *.
    assert (isMap m2).
   tauto.
  unfold isMap in H36.
assert (degreee m2 x = 2).
   apply H36.
     tauto.
      tauto.
   tauto.
  tauto.
  tauto.
  tauto.
 assert (cA m3 one y = y).
unfold m3.
rewrite cA1_Flip4.
elim (eq_dart_dec xff y).
assert (isTriangulation m).
 tauto.
 unfold isTriangulation in H36.
     assert (isTri m x).
    apply H36.
       tauto.
   assert (isTri m y).
    apply H36.
       tauto.
   generalize (Tri_diff_2faces m x y).
     simpl in |- *.
     rewrite <- H23 in |- *.
     fold xff in |- *.
      tauto.
elim (eq_dart_dec x y).
intro.
symmetry in a.
tauto.
unfold m2.
rewrite <-H13.
rewrite cA1_Flip2.
elim (eq_dart_dec y y).   
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
unfold m2.
rewrite <-H13.
rewrite cA1_Flip2.
elim (eq_dart_dec y x).
tauto.
fold y_1.
rewrite H13.
elim (eq_dart_dec y_1 x).
intro.
  absurd (expv m x y).
     tauto.
   rewrite <-a in |- *.
     unfold expv in |- *.
     unfold MA1.MfcA.expo in |- *.
     split.
    rewrite a in |- *.
       tauto.
   split with 1.
     simpl in |- *.
     assert (MA1.MfcA.f m y_1 = cA m one y_1).
     tauto.
   rewrite H36 in |- *.
     unfold y_1 in |- *.
     rewrite cA_cA_1 in |- *.
     tauto.
    tauto.
    tauto.
unfold m1.
unfold x_1.
rewrite cA1_Flip1.
elim (eq_dart_dec x x).
tauto.
tauto.
tauto.  clear H7 H15 H31.
lia.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
assert (isTriangulation m).
tauto.
unfold isTriangulation in  H37.
assert (isTri m x).
apply H37.
tauto.
assert (isTri m y).
apply H37.
tauto.
assert (cF m1 y = x /\
       cF m1 x = y_1 /\
       cF m1 y_1 = xff /\ cF m1 xff = x_1 /\ 
       cF m1 x_1 = yff /\ cF m1 yff = y).
unfold m1. 
unfold yff.
unfold xff.
unfold y_1.
unfold x_1.
unfold y.
apply cF_Flip1_detail_1.
tauto.
tauto.
tauto. clear H7 H15 H31.
lia.
fold y. clear H7 H15 H31. lia.
fold y. tauto.
fold y. tauto.
tauto.
tauto.
decompose [and] H40.
assert (x = cF m2 y /\
       y = cF m2 x /\
       y_1 = cF m2 yff /\
       xff = cF m2 y_1 /\ 
       x_1 = cF m2 xff /\ yff = cF m2 x_1).
unfold m2.
rewrite <-H45.
rewrite <-H44.
rewrite <-H42.
rewrite <-H43.
rewrite <-H41.
apply cF_Flip2_detail_1.
tauto.
tauto.
tauto.
rewrite H41. tauto.
rewrite H41. tauto.
tauto.
decompose [and] H46.
assert ( isQuad m2 xff).
unfold isQuad.
assert (degreef m2 y_1 = degreef m2 xff).
assert (degreef = MF.degree).
tauto.
rewrite H53.
apply MF.expo_degree.
tauto.
rewrite H51.
unfold MF.expo.
split. tauto.
split with 1.
simpl. tauto.
unfold isQuad in IS.
rewrite <-H53. tauto.
assert ( y = cF m3 x /\
       xff = cF m3 y /\
       x_1 = cF m3 xff /\ yff = cF m3 x_1 /\ 
       y_1 = cF m3 yff /\ x = cF m3 y_1).
unfold m3.
rewrite H49.
rewrite H54.
rewrite H52.
rewrite H50.
apply cF_Flip3_detail_1.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
decompose [and] H55.
assert (yff = Iter (cF m3) 3 y).
unfold Iter; fold Iter.
rewrite <-H58. rewrite <-H57. rewrite <-H59.
tauto.
assert (degreef m3 y = degreef m3 yff).
assert (degreef = MF.degree).
tauto.
rewrite H63.
rewrite H61.
apply (MF.degree_uniform m3 y).
tauto.
tauto.
assert (isHexa m3 yff).
unfold isHexa.
rewrite <-H63.
unfold isHexa in IS.
tauto.
assert (yff = Iter (cF m3) 4 x).
rewrite H56 in H61.
unfold Iter in H61; fold Iter in H61.
tauto.
assert (expf m4 x z \/ expf m4 y z <-> expf m3 x z).
unfold m4.
rewrite H35.
apply (eqf_Flip4 m3 yff y z).
tauto.
tauto.
tauto.
tauto.
assert (cF = MF.f).
tauto.
rewrite H61.
rewrite H66.
generalize (MF.exd_Iter_f m3 3 y).
tauto.
tauto.
rewrite <-H35.
tauto.
clear H2 IS IH IM Ey H3 H4 H5 H9 H6 H17 H18 H19 H32 H34 H40 H46 H55.
tauto.
Qed.

(*====================================================
                 (PROVISIONAL) END
=====================================================*)


