(*=====================================================
=======================================================
               TOPOLOGICAL FMAPS, HMAPS -
               WITH TAGS AND EMBEDDINGS
                 
                  TRIANGULATIONS

                  FLIP SUMMARY - 
             PART 3: PART 2 CONTINUED

                 COMPILED (6 min)

December 2008, REVIEWED May 2009 
=======================================================
=====================================================*)

Require Export TRIANG02.

(*===================================================
        A REPLACER DANS TRIANG02
===================================================*)

Theorem eqf_Flip_topo: forall(m:fmap)(x z:dart),
  inv_Triangulation m -> 
    prec_Flip m x -> exd m z -> 
       let y := cA m zero x in
       let m4:= Flip_topo m x in
     ((expf m x z \/ expf m y z)
      <->
      (expf m4 x z \/ expf m4 y z)).
Proof.
  intros.
    unfold m4.
     unfold Flip_topo.
  generalize (eqf_Flip_1_4 m x z H H0).
  tauto.
Qed.

(* USEFUL LEMMA: *)

Lemma or_dec: forall(A B:Prop),
   {A} + {~A} -> {B} + {~B} ->
      {A \/ B} + {~A /\ ~B}.
Proof.
  intros.
 tauto.
Qed.

(* isTriangulation_Flip_topo: *)

Theorem isTriangulation_Flip_topo: 
 forall(m:fmap)(x:dart),
   inv_Triangulation m -> 
     prec_Flip m x ->
       isTriangulation (Flip_topo m x).
Proof.
  unfold isTriangulation.
 intros.
 set (y:= cA m zero x).
 assert (exd m z).
       generalize (exd_Flip_topo m x z).
     tauto.
 generalize ( eqf_Flip_topo m x z H H0 H2).
   simpl.
      fold y.
   intro.
generalize (isTri_Flip_topo m x H H0).
   fold y.
  intro.
assert (inv_hmap (Flip_topo m x)).
apply inv_hmap_Flip_topo.
tauto.
tauto.
assert (degreef = MF.degree).
tauto.
  elim (or_dec (expf m x z) (expf m y z)).
    intro. 
  assert (expf (Flip_topo m x) x z \/ expf (Flip_topo m x) y z).
tauto.
clear H3.
elim H4.
clear H4.
intros Tx Ty.
 elim H7.
intro.
clear H7.
assert (degreef (Flip_topo m x) x = degreef (Flip_topo m x) z).
rewrite H6.
     apply MF.expo_degree.
tauto.
unfold expf in H3.
tauto.
unfold isTri in Tx.
unfold isTri.
rewrite <-H4.
tauto.
intro.
assert (degreef (Flip_topo m x) y = degreef (Flip_topo m x) z).
rewrite H6.
     apply MF.expo_degree.
tauto.
unfold expf in H3.
tauto.
unfold isTri in Ty.
unfold isTri.
rewrite <-H4.
tauto.
intro.
apply isTriExt_Flip_topo.
tauto.
tauto.
tauto.
tauto.
fold y. tauto.
apply expf_dec.
apply expf_dec.
Qed.

Theorem isTriangulation_Flip: 
forall(m:fmap)(x:dart),
   inv_Triangulation m -> 
       prec_Flip m x ->
          isTriangulation (Flip m x).
Proof.
intros.
assert (inv_hmap (Flip_topo m x)).
apply inv_hmap_Flip_topo.
tauto. tauto.
unfold Flip.
unfold Flip_emb.
apply isTriangulation_Flip6.
generalize (inv_hmap_Chp  (Flip_topo m x) x
    (fpoint (Flip_topo m x) (cF m (cA_1 m one (cA m zero x))))).
tauto.
apply isTriangulation_Flip5.
tauto.
apply isTriangulation_Flip_topo.
tauto. tauto.
Qed.

(*=====================================================
          Flip SUMMARY: degreev, isPoly
=====================================================*)

(* FIRST: exd_Flip_1_4_New: *)

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
     exd m z <-> 
  (exd m1 z /\ exd m2 z /\ exd m3 z /\ exd m4 z).
Proof.
intros.
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

(* OK, COMPILATION DURATION: 3 MIN : *)

Lemma isPoly_Flip_1_4: forall(m:fmap)(x:dart),
   let x_1 := cA_1 m one x in
   let y := cA m zero x in
   let y_1 := cA_1 m one y in
   let xff := cF m y_1 in
   let yff :=  cF m x_1 in
   let m1 := Split m one x x_1 in
   let m2 := Split m1 one y y_1 in 
   let m3 := Merge m2 one xff x in  
   let m4 := Merge m3 one yff y in
 inv_Triangulation m -> prec_Flip m x ->
   ((degreev m1 x = 1 /\ 3 <= degreev m1 y) /\
      (degreev m2 y = 1 /\ degreev m2 x = 1) /\
         (3 <= degreev m3 x /\ degreev m3 y = 1) /\
            (3 <= degreev m4 x /\ 3 <= degreev m4 y)).
Proof.
intros.
 assert (inv_Triangulation m). tauto. 
unfold inv_Triangulation in  H1. 
decompose [and] H1. clear H1.
 assert (prec_Flip m x). tauto.
unfold prec_Flip in H1. decompose [and] H1. clear H1.
fold y in H7. fold y in H8.
  generalize (exd_Flip_1_4 m x x). 
intro. elim H1. fold y. fold y_1.
fold x_1. fold xff. fold yff.
fold m1. fold m2. fold m3. fold m4.
clear H1. intro.
assert (exd m x /\ exd m1 x /\ exd m2 x /\ exd m3 x /\ exd m4 x).  tauto. intro.
clear H1 H12.
assert (exd m y).
generalize (exd_cA m zero x). fold y. tauto.
  generalize (exd_Flip_1_4 m x y). 
intro.
elim H12. fold y. fold y_1.
fold x_1. fold xff. fold yff.
fold m1. fold m2. fold m3. fold m4.
clear H12. intro.
assert (exd m y /\ exd m1 y /\ exd m2 y /\ exd m3 y /\ exd m4 y). 
tauto. intro. clear H12 H14.
  assert (exd m y_1).
generalize (exd_cA_1 m one y). fold y_1. tauto.
generalize (exd_Flip_1_4 m x y_1). 
intro.
elim H14. fold y. fold y_1.
fold x_1. fold xff. fold yff.
fold m1. fold m2. fold m3. fold m4.
clear H14. intro.
assert (exd m y_1 /\ exd m1 y_1 /\ exd m2 y_1 /\ exd m3 y_1 /\ exd m4 y_1). 
tauto. intro. clear H14 H16.
  assert (exd m xff).
generalize (exd_cF m y_1). fold xff. tauto.
generalize (exd_Flip_1_4 m x xff). 
intro.
elim H16. fold y. fold y_1.
fold x_1. fold xff. fold yff.
fold m1. fold m2. fold m3. fold m4.
clear H16. intro.
assert (exd m xff /\ exd m1 xff /\ exd m2 xff /\ exd m3 xff /\ exd m4 xff). 
tauto. intro. clear H18 H16.
clear H5 H1 H12 H14.
  assert (isTri m x). unfold isTriangulation in H6.
apply H6. tauto.
assert (isTri m y). unfold isTriangulation in H6. apply H6. tauto.
assert (exd m x). tauto.
generalize (Tri_diff_face m x H2 H12 H1). 
simpl. intro.
  assert (exd m y). tauto.
generalize (Tri_diff_2faces m x y H2 H12 H16 H1 H5 H8). simpl.
intro.
  assert (degreee m x = 2).
unfold isMap in H4. apply H4. tauto.
generalize (degreee_invol_nofixpt m x H2 H12). intro.
assert 
(cA m zero x <> x /\ cA m zero (cA m zero x) = x).
tauto.
clear H20. fold y in H21. elim H21. clear H21. intros.
generalize (invol_inverse m zero x H2 H12).
fold y. intro. assert (y = cA_1 m zero x). tauto. clear H22.
assert (y_1=cF m x). unfold cF. rewrite <-H23; fold y_1. tauto.
  generalize (isSubd_Flip_1_4 m x H H0).
fold y. fold y_1.
fold x_1. fold xff. fold yff.
fold m1. fold m2. fold m3. fold m4. intro.
  generalize (isMap_Flip_1_4 m x H H0).
fold y. fold y_1.
fold x_1. fold xff. fold yff.
fold m1. fold m2. fold m3. fold m4. intro.
  generalize (inv_hmap_Flip_1_4 m x H H0).
fold y. fold y_1.
fold x_1. fold xff. fold yff.
fold m1. fold m2. fold m3. fold m4. intro.
assert (degreee m y = 2).
unfold isMap in H4. apply H4. tauto.
  generalize (degreee_invol_nofixpt m y H2 H16). intro.
assert 
 (cA m zero y <> y /\ cA m zero (cA m zero y) = y).
tauto.
clear H28. rewrite H21 in H29. elim H29. clear H29. intros.
  generalize (invol_inverse m zero y H2 H16).
rewrite H21. intro. assert (x = cA_1 m zero y). tauto. clear H30.
  assert (x_1=cF m y). 
unfold cF. rewrite <-H31; fold x_1. tauto.
rewrite <-H22 in H18. rewrite <-H22 in H14.
rewrite <-H30 in H18. fold xff in H18. fold yff in H18.
fold xff in H14.
(* PART 1: *)
assert (degreev m1 x = 1 /\ 3 <= degreev m1 y).
unfold m1. unfold x_1. 
split.
  rewrite (degreev_Flip1 m x x H2). 
elim (eq_dart_dec x x). tauto. tauto. 
tauto. tauto. lia.
rewrite (degreev_Flip1 m x y H2). 
elim (eq_dart_dec x y). tauto.
fold x_1. elim (expv_dec m x_1 y). intros.
elim H7. apply expv_trans with x_1.
apply MA1.MfcA.expo_symm. tauto.
unfold  MA1.MfcA.expo. split. 
generalize (exd_cA_1 m one x). fold x_1. tauto.
split with 1. simpl.
assert (MA1.MfcA.f m x_1 = cA m one x_1).
tauto. rewrite H31. rewrite H32. unfold x_1. clear H32. 
rewrite cA_cA_1. tauto. tauto. tauto. tauto.
unfold y. tauto.
tauto. tauto. lia.
split. tauto.
(* PART 2: *)
  assert (y_1 = cA_1 m1 one y).
unfold m1. unfold x_1.
rewrite cA1_1_Flip1. 
rewrite <-H29.  elim (eq_dart_dec y y).
fold y. elim (eq_dart_dec (cA m one x) y). intros.
elim H7. unfold expv. unfold MA1.MfcA.expo. 
split. tauto. split with 1. simpl. rewrite <-a. tauto.
elim (eq_dart_dec x y). tauto. fold y_1. 
tauto. tauto. tauto. lia. tauto. tauto.
assert (y =cA m1 zero x). unfold m1. unfold x_1.
rewrite cA0_Flip1. tauto. tauto. tauto. tauto.
assert (y =cA m2 zero x). unfold m2. 
rewrite H33. rewrite cA0_Flip2. tauto. tauto. tauto. tauto.
  assert (degreev m2 x = 1).
unfold isBar in H24. tauto.
assert (isBar m2 y). rewrite H35.
apply isBar_symm. tauto. tauto. tauto.
assert (degreev m2 y = 1).
unfold isBar in H37. tauto.
split. tauto.
(* PART 3: *)
  assert (~expv m2 x xff). intro.
unfold expv in H39. assert ( MA1.MfcA.expo2 m2 x xff).
generalize (MA1.MfcA.expo_expo2 m2 x xff). tauto.
unfold  MA1.MfcA.expo2 in H40. elim H40. intros. clear H40.
clear H41. elim H42. clear H42. intros i Hi. 
assert (MA1.MfcA.degree = degreev). tauto.
rewrite H40 in Hi. 
assert (i = 0).
 clear -H36 Hi; lia.
 rewrite H41 in Hi.
simpl in Hi. tauto. 
  assert (~ expv m2 xff y).
intro. unfold expv in H40.
assert (MA1.MfcA.expo m2 y xff).
apply MA1.MfcA.expo_symm. tauto. tauto.
assert (MA1.MfcA.expo2 m2 y xff).
generalize (MA1.MfcA.expo_expo2 m2 y xff). tauto.
unfold MA1.MfcA.expo2 in H42.
elim H42. clear H42. intros. clear H42. elim H43. clear H43.
intros i Hi. elim Hi. clear Hi. intros.
assert (MA1.MfcA.degree = degreev). tauto.
rewrite H44 in H42.
assert (i = 0). 
clear -H42 H38.
lia. 
rewrite H45 in H43. simpl in H43. 
symmetry in H43. tauto.
  assert (degreev m3 y = 1).
unfold m3. assert (inv_hmap m2). tauto.
rewrite (degreev_Flip3 m2 xff x y H41).
elim (expv_dec m2 xff y H41). tauto.
elim (eq_dart_dec x y). tauto. tauto.
tauto. tauto. tauto. intro.
elim H39. apply expv_symm. tauto.
tauto. tauto.
  assert (3 <= degreev m3 x). 
unfold m3. assert (inv_hmap m2). tauto.
rewrite (degreev_Flip3 m2 xff x x H42).
elim (expv_dec m2 xff x H42). intro.
elim H39. apply expv_symm. tauto. tauto.
elim (eq_dart_dec x x). intros.
unfold m2. rewrite H33. 
assert (inv_hmap m1). tauto.
rewrite (degreev_Flip2 m1 y xff H43).
elim (eq_dart_dec y xff). intros.
symmetry in a0. tauto.
  assert (cA_1 m1 one y=y_1).
unfold m1. unfold x_1. rewrite cA1_1_Flip1.
elim (eq_dart_dec (cA m one x) y). intro.
elim H7. unfold expv. unfold MA1.MfcA.expo.
split. tauto. split with 1. simpl. tauto.
elim (eq_dart_dec x y). tauto. fold y_1.
tauto. tauto. lia. tauto. tauto. rewrite H44.
elim (expv_dec m1 y_1 xff H43). intros. lia.
intros.
unfold m1. unfold x_1. rewrite (degreev_Flip1 m x xff H2).
elim (eq_dart_dec x xff). tauto.
fold x_1. elim (expv_dec m x_1 xff H2). 
intros. lia. intros.
  assert (2 <= degreev m xff).
unfold isPoly in H3. apply H3. tauto.
lia. tauto. tauto. lia. tauto.
tauto. lia. tauto.  tauto. tauto. tauto.
intro. elim H39. apply expv_symm. 
tauto. tauto. tauto. 
split. tauto.
(* PART 4: *)
  assert (exd m x_1).
generalize (exd_cA_1 m one x). fold x_1. tauto.
assert (exd m yff).
generalize (exd_cF m x_1). fold xff. tauto.
generalize (exd_Flip_1_4 m x yff). 
intro. elim H45. fold y. fold y_1.
fold x_1. fold xff. fold yff.
fold m1. fold m2. fold m3. fold m4.
clear H45. intro.
assert (exd m yff /\ exd m1 yff /\ exd m2 yff /\ exd m3 yff /\ exd m4 yff).  
tauto. intro. clear H45 H47.
generalize (Tri_diff_face m y H2 H16 H5). 
simpl. intro Tdy. rewrite <-H30 in Tdy. fold yff in Tdy.
  assert (~ expv m3 yff y).
intro. unfold expv in H45.
assert (MA1.MfcA.expo m3 y yff).
apply MA1.MfcA.expo_symm. tauto. tauto.
assert (MA1.MfcA.expo2 m3 y yff).
generalize (MA1.MfcA.expo_expo2 m3 y yff). tauto.
unfold MA1.MfcA.expo2 in H48.
elim H48. clear H48. intros. clear H48. elim H49. clear H49.
intros i Hi. elim Hi. clear Hi. intros.
assert (MA1.MfcA.degree = degreev). tauto.
rewrite H50 in H48.
assert (i = 0). 
 clear -H48 H41.
 lia. rewrite H51 in H49. 
simpl in H49. 
tauto.
  assert (2 <= degreev m1 xff).  
unfold m1. unfold x_1.
rewrite (degreev_Flip1 m x xff H2).
elim (eq_dart_dec x xff). tauto.
fold x_1. elim (expv_dec m x_1 xff H2).
intros. 
clear -H9.
lia.
intros.
unfold isPoly in H3. apply H3. tauto. tauto.
tauto.
clear -H9.
 lia. 
  assert (2 <= degreev m2 xff). 
unfold m2. rewrite H33. 
assert (inv_hmap m1). tauto.
rewrite (degreev_Flip2 m1 y xff H48).
elim (eq_dart_dec y xff). intro. 
symmetry in a. tauto.
elim ( expv_dec m1 (cA_1 m1 one y) xff). intros.
clear -H32.
lia. intros. tauto. tauto. tauto. lia.
  assert (2 <= degreev m1 yff).  
unfold m1. unfold x_1.
rewrite (degreev_Flip1 m x yff H2).
elim (eq_dart_dec x yff). tauto.
fold x_1. elim (expv_dec m x_1 yff H2).
intros. clear -H9. lia. intros.
unfold isPoly in H3. apply H3. tauto. tauto.
tauto. clear -H9. lia. 
  assert (2 <= degreev m2 yff). 
unfold m2. rewrite H33. 
assert (inv_hmap m1). tauto.
rewrite (degreev_Flip2 m1 y yff H50).
elim (eq_dart_dec y yff). tauto.
elim ( expv_dec m1 (cA_1 m1 one y) yff). intros.
clear -H32. lia. intros. tauto. tauto. tauto. lia.
  assert (2 <= degreev m3 yff). 
unfold m3. 
assert (inv_hmap m2). tauto.
rewrite (degreev_Flip3 m2 xff x yff H51).
elim (expv_dec m2 xff yff H51). intro.
lia.
elim (eq_dart_dec x yff). tauto. intros.
tauto. tauto. tauto. tauto. intro.
elim H39. apply expv_symm. tauto.
tauto. tauto. 
  split.
unfold m4. assert (inv_hmap m3). tauto. 
rewrite (degreev_Flip4 m3 yff y x H52).
elim (expv_dec m3 yff x H52). intros. lia.
elim (eq_dart_dec y x). intros. lia.
intros. lia. tauto. tauto. tauto. tauto.
tauto.
  unfold m4. assert (inv_hmap m3). tauto. 
rewrite (degreev_Flip4 m3 yff y y H52).
elim (expv_dec m3 yff y H52). intros. lia.
elim (eq_dart_dec y y). intros. lia.
tauto. tauto. tauto. tauto. tauto. tauto. 
Qed.


(* TO AVOID RECOMPILATION DURING THE TESTS: 

Lemma isPoly_Flip_1_4: forall(m:fmap)(x:dart),
   let x_1 := cA_1 m one x in
   let y := cA m zero x in
   let y_1 := cA_1 m one y in
   let xff := cF m y_1 in
   let yff :=  cF m x_1 in
   let m1 := Split m one x x_1 in
   let m2 := Split m1 one y y_1 in 
   let m3 := Merge m2 one xff x in  
   let m4 := Merge m3 one yff y in
 inv_Triangulation m -> prec_Flip m x ->
   ((degreev m1 x = 1 /\ 3 <= degreev m1 y) /\
      (degreev m2 y = 1 /\ degreev m2 x = 1) /\
         (3 <= degreev m3 x /\ degreev m3 y = 1) /\
            (3 <= degreev m4 x /\ 3 <= degreev m4 y)).
Admitted.
*)

(* OK, COMPILED IN 3 MIN: *)

Lemma isPolyExt_Flip_1_4: forall(m:fmap)(x:dart),
   let x_1 := cA_1 m one x in
   let y := cA m zero x in
   let y_1 := cA_1 m one y in
   let xff := cF m y_1 in
   let yff :=  cF m x_1 in
   let m1 := Split m one x x_1 in
   let m2 := Split m1 one y y_1 in 
   let m3 := Merge m2 one xff x in  
   let m4 := Merge m3 one yff y in
  inv_Triangulation m -> prec_Flip m x -> 
  ((forall z, exd m z -> 
       x <> z -> 2 <= degreev m1 z) /\
   (forall z, exd m z -> 
       x <> z -> y <> z -> 2 <= degreev m2 z) /\
   (forall z, exd m z -> 
       y <> z -> 2 <= degreev m3 z) /\
   (forall z, exd m z -> 2 <= degreev m4 z)).
Proof.
intros.
assert (inv_Triangulation m). tauto. 
unfold inv_Triangulation in  H1. 
decompose [and] H1. clear H1.
 assert (prec_Flip m x). tauto.
unfold prec_Flip in H1. decompose [and] H1. clear H1.
fold y in H7. fold y in H8.
  generalize (exd_Flip_1_4 m x x). 
intro. elim H1. fold y. fold y_1.
fold x_1. fold xff. fold yff.
fold m1. fold m2. fold m3. fold m4.
clear H1. intro.
assert (exd m x /\ exd m1 x /\ exd m2 x /\ exd m3 x /\ exd m4 x). tauto. intro.
clear H1 H12.
assert (exd m y).
generalize (exd_cA m zero x). fold y. tauto.
  generalize (exd_Flip_1_4 m x y). 
intro.
elim H12. fold y. fold y_1.
fold x_1. fold xff. fold yff.
fold m1. fold m2. fold m3. fold m4.
clear H12. intro.
assert (exd m y /\ exd m1 y /\ exd m2 y /\ exd m3 y /\ exd m4 y). 
tauto. intro. clear H12 H14.
  assert (exd m y_1).
generalize (exd_cA_1 m one y). fold y_1. tauto.
generalize (exd_Flip_1_4 m x y_1). 
intro.
elim H14. fold y. fold y_1.
fold x_1. fold xff. fold yff.
fold m1. fold m2. fold m3. fold m4.
clear H14. intro.
assert (exd m y_1 /\ exd m1 y_1 /\ exd m2 y_1 /\ exd m3 y_1 /\ exd m4 y_1). 
tauto. intro. clear H14 H16.
  assert (exd m xff).
generalize (exd_cF m y_1). fold xff. tauto.
generalize (exd_Flip_1_4 m x xff). 
intro.
elim H16. fold y. fold y_1.
fold x_1. fold xff. fold yff.
fold m1. fold m2. fold m3. fold m4.
clear H16. intro.
assert (exd m xff /\ exd m1 xff /\ exd m2 xff /\ exd m3 xff /\ exd m4 xff). 
tauto. intro. clear H18 H16.
clear H5 H1 H12 H14.
  assert (isTri m x). unfold isTriangulation in H6.
apply H6. tauto.
assert (isTri m y). unfold isTriangulation in H6. apply H6. tauto.
assert (exd m x). tauto.
generalize (Tri_diff_face m x H2 H12 H1). 
simpl. intro.
  assert (exd m y). tauto.
generalize (Tri_diff_2faces m x y H2 H12 H16 H1 H5 H8). simpl.
intro.
  assert (degreee m x = 2).
unfold isMap in H4. apply H4. tauto.
generalize (degreee_invol_nofixpt m x H2 H12). intro.
assert 
(cA m zero x <> x /\ cA m zero (cA m zero x) = x).
tauto.
clear H20. fold y in H21. elim H21. clear H21. intros.
generalize (invol_inverse m zero x H2 H12).
fold y. intro. assert (y = cA_1 m zero x). tauto. clear H22.
assert (y_1=cF m x). unfold cF. rewrite <-H23; fold y_1. tauto.
  generalize (isSubd_Flip_1_4 m x H H0).
fold y. fold y_1.
fold x_1. fold xff. fold yff.
fold m1. fold m2. fold m3. fold m4. intro.
  generalize (isMap_Flip_1_4 m x H H0).
fold y. fold y_1.
fold x_1. fold xff. fold yff.
fold m1. fold m2. fold m3. fold m4. intro.
  generalize (inv_hmap_Flip_1_4 m x H H0).
fold y. fold y_1.
fold x_1. fold xff. fold yff.
fold m1. fold m2. fold m3. fold m4. intro.
assert (degreee m y = 2).
unfold isMap in H4. apply H4. tauto.
  generalize (degreee_invol_nofixpt m y H2 H16). intro.
assert 
 (cA m zero y <> y /\ cA m zero (cA m zero y) = y).
tauto.
clear H28. rewrite H21 in H29. elim H29. clear H29. intros.
  generalize (invol_inverse m zero y H2 H16).
rewrite H21. intro. assert (x = cA_1 m zero y). tauto. clear H30.
  assert (x_1=cF m y). 
unfold cF. rewrite <-H31; fold x_1. tauto.
rewrite <-H22 in H18. rewrite <-H22 in H14.
rewrite <-H30 in H18. fold xff in H18. fold yff in H18.
fold xff in H14.
(* PART 1: *)
 assert ((forall z : dart, exd m z -> x <> z -> 2 <= degreev m1 z)).
intros.
unfold m1. unfold x_1.
rewrite (degreev_Flip1 m x z H2).
elim (eq_dart_dec x z). tauto. fold x_1.
elim (expv_dec m x_1 z H2). intros. lia.
intros. unfold isPoly in H3. apply H3. tauto.
tauto. tauto. lia.
split. tauto.
(* PART 2: *)
  assert (y_1 = cA_1 m1 one y).
unfold m1. unfold x_1.
rewrite cA1_1_Flip1. 
rewrite <-H29.  elim (eq_dart_dec y y).
fold y. elim (eq_dart_dec (cA m one x) y). intros.
elim H7. unfold expv. unfold MA1.MfcA.expo. 
split. tauto. split with 1. simpl. rewrite <-a. tauto.
elim (eq_dart_dec x y). tauto. fold y_1. 
tauto. tauto. tauto. lia. tauto. tauto.
   generalize (isPoly_Flip_1_4 m x H H0).
fold y. fold y_1.
fold x_1. fold xff. fold yff.
fold m1. fold m2. fold m3. fold m4. intro.
   assert 
(forall z : dart, exd m z -> x <> z -> y <> z -> 2 <= degreev m2 z).
intros. unfold m2. rewrite H33. 
assert (inv_hmap m1). tauto.
rewrite (degreev_Flip2 m1 y z H38). rewrite <-H33.
elim (eq_dart_dec y z). tauto.
elim ( expv_dec m1 y_1 z H38). intros. 
clear -H34; lia.
intros. apply H32. tauto. tauto. tauto. unfold m1.
generalize (exd_Split m one x x_1 z). tauto.
lia. split. tauto.
(* PART 3: *)
 assert (~expv m2 x xff). intro.
unfold expv in H36. assert ( MA1.MfcA.expo2 m2 x xff).
generalize (MA1.MfcA.expo_expo2 m2 x xff). tauto.
unfold  MA1.MfcA.expo2 in H37. elim H37. intros. clear H37.
clear H38. elim H39. clear H39. intros i Hi. 
assert (MA1.MfcA.degree = degreev). tauto.
rewrite H37 in Hi. 
assert (i = 0). 
clear - Hi H34; lia. rewrite H38 in Hi.
simpl in Hi. tauto. 
  assert (2<= degreev m2 xff).
apply H35. tauto. tauto. intro. symmetry in H37. tauto.
assert (inv_hmap m2). tauto.
assert (forall z : dart, exd m z -> y <> z -> 2 <= degreev m3 z).
intros. assert (exd m1 z). unfold m1.
generalize (exd_Split m one x x_1 z). tauto.
assert (exd m2 z). unfold m2. 
generalize (exd_Split m1 one y y_1 z). tauto.
unfold m3. 
rewrite (degreev_Flip3 m2 xff x z H38).
elim (expv_dec m2 xff z H38). intros. lia.
intros. elim (eq_dart_dec x z). intros. lia.
intro. apply H35. tauto. tauto. tauto. tauto.
tauto. tauto. intro. elim H36. 
apply expv_symm. tauto. tauto. tauto.
split. tauto.
(* PART 4: *)
 assert (exd m x_1).
generalize (exd_cA_1 m one x). fold x_1. tauto.
assert (exd m yff).
generalize (exd_cF m x_1). fold xff. tauto.
generalize (exd_Flip_1_4 m x yff). 
intro. elim H42. fold y. fold y_1.
fold x_1. fold xff. fold yff.
fold m1. fold m2. fold m3. fold m4.
clear H42. intro.
assert (exd m yff /\ exd m1 yff /\ exd m2 yff /\ exd m3 yff /\ exd m4 yff).  
tauto. intro. clear H42 H44.
generalize (Tri_diff_face m y H2 H16 H5). 
simpl. intro Tdy. rewrite <-H30 in Tdy. fold yff in Tdy.
  assert (~ expv m3 yff y).
intro. unfold expv in H42.
assert (MA1.MfcA.expo m3 y yff).
apply MA1.MfcA.expo_symm. tauto. tauto.
assert (MA1.MfcA.expo2 m3 y yff).
generalize (MA1.MfcA.expo_expo2 m3 y yff). tauto.
unfold MA1.MfcA.expo2 in H45.
elim H45. clear H45. intros. clear H45. elim H46. clear H46.
intros i Hi. elim Hi. clear Hi. intros.
assert (MA1.MfcA.degree = degreev). tauto.
rewrite H47 in H45.
assert (i = 0).
clear - H45 H34; lia. rewrite H48 in H46. 
simpl in H46. 
tauto.
    assert (2 <= degreev m3 yff). 
apply H39. tauto. tauto.
intros. assert (exd m1 z). unfold m1.
generalize (exd_Split m one x x_1 z). tauto.
assert (exd m2 z). unfold m2. 
generalize (exd_Split m1 one y y_1 z). tauto.
assert (exd m3 z). unfold m3.
generalize (exd_Merge m2 one xff x z). tauto.
unfold m4. assert (inv_hmap m3). tauto.
rewrite (degreev_Flip4 m3 yff y z H49).
elim (expv_dec m3 yff z H49). intros. lia.
elim (eq_dart_dec y z). intros. lia.
intros. apply H39. tauto. tauto. tauto. tauto.
tauto. tauto. tauto.
Qed. 

(* ADMITTED FOR THE FOLLOWING DEVELOPMENTS: 

Lemma isPolyExt_Flip_1_4: forall(m:fmap)(x:dart),
   let x_1 := cA_1 m one x in
   let y := cA m zero x in
   let y_1 := cA_1 m one y in
   let xff := cF m y_1 in
   let yff :=  cF m x_1 in
   let m1 := Split m one x x_1 in
   let m2 := Split m1 one y y_1 in 
   let m3 := Merge m2 one xff x in  
   let m4 := Merge m3 one yff y in
  inv_Triangulation m -> prec_Flip m x -> 
  ((forall z, exd m z -> 
       x <> z -> 2 <= degreev m1 z) /\
   (forall z, exd m z -> 
       x <> z -> y <> z -> 2 <= degreev m2 z) /\
   (forall z, exd m z -> 
       y <> z -> 2 <= degreev m3 z) /\
   (forall z, exd m z -> 2 <= degreev m4 z)) .
Admitted.
*)

(* THEN: *)

Lemma isPoly_Flip_topo: forall(m:fmap)(x:dart),
   inv_Triangulation m -> prec_Flip m x ->
           isPoly (Flip_topo m x).
Proof.
intros.
generalize (isPolyExt_Flip_1_4 m x H H0).
intro.
decompose [and] H1.
unfold Flip_topo.
unfold isPoly.
intro.
intro.
apply H6.
generalize (exd_Flip_topo m x z).
unfold Flip_topo. tauto.
Qed.

(* FINALLY: *)

Lemma isPoly_Flip: forall(m:fmap)(x:dart),
   inv_Triangulation m -> prec_Flip m x ->
           isPoly (Flip m x).
Proof.
 intros.
  unfold Flip.
    unfold Flip_emb.
       generalize (inv_hmap_Flip_topo m x H H0). intro.
       apply isPoly_Flip6.
         set(pu:=  (fpoint (Flip_topo m x) (cF m (cA_1 m one (cA m zero x))))).
          generalize (inv_hmap_Chp (Flip_topo m x) x pu). tauto.
        apply isPoly_Flip5. tauto.
     apply isPoly_Flip_topo. tauto. tauto.
Qed.

Theorem inv_Triangulation_Flip_topo: forall(m:fmap)(x:dart),
   inv_Triangulation m -> prec_Flip m x ->
           inv_Triangulation (Flip_topo m x).
Proof.
intros.
   unfold  inv_Triangulation.
  split. apply inv_hmap_Flip_topo. tauto. tauto.
 split. apply isMap_Flip_topo. tauto. tauto.
split. apply isPoly_Flip_topo. tauto. tauto.
apply isTriangulation_Flip_topo. tauto. tauto.
Qed.

(* VERY IMPORTANT: *)

Theorem inv_Triangulation_Flip: forall(m:fmap)(x:dart),
   inv_Triangulation m -> prec_Flip m x ->
           inv_Triangulation (Flip m x).
Proof.
intros.
   unfold  inv_Triangulation.
  split. apply inv_hmap_Flip. tauto. tauto.
 split. apply isMap_Flip. tauto. tauto.
split. apply isPoly_Flip. tauto. tauto.
apply isTriangulation_Flip. tauto. tauto.
Qed.  

(*===========================================================
                              NUMBERINGS
============================================================*)

(* Edge numbering: *)

Lemma ne_Flip1: forall(m:fmap)(x:dart),
   inv_hmap m -> exd m x ->
    2 <= degreev m x ->
    let x_1 := cA_1 m one x in
        ne (Split m one x x_1) = ne m.
Proof.
 intros.
    generalize (degreev_crackv m x  H H0 H1).  intro.
    rewrite ne_Split1. tauto. tauto. unfold x_1. tauto.
Qed.

Lemma ne_Flip2: forall(m1:fmap)(y:dart),
   inv_hmap m1 -> exd m1 y ->
    2 <= degreev m1 y ->
    let y_1 := cA_1 m1 one y in
        ne (Split m1 one y y_1) = ne m1.
Proof.
 intros.
    generalize (degreev_crackv m1 y H H0 H1).  intro.
    rewrite ne_Split1. tauto. tauto. unfold y_1. tauto.
Qed.

Lemma ne_G1_bis : forall(m:fmap)(x y:dart), 
  inv_hmap m -> exd m x -> 
   ne (G m one x y) = ne m. 
Proof.
intros.
unfold G in |- *.
simpl in |- *.
elim (succ_dec m one x).
 intro.
 rewrite ne_Shift1 in |- *.
   tauto.
  tauto.
tauto.
tauto.
Qed.

Lemma ne_Merge1_bis : forall(m: fmap)(x y: dart), 
  inv_hmap m -> exd m x -> exd m y ->
   ne (Merge m one x y) = ne m. 
Proof.
unfold Merge in |- *.
intros.
  set (y_1:=cA_1 m one y).
assert (exd m y_1).
generalize (exd_cA_1 m one y). fold y_1. tauto.
  elim (pred_dec m one y). intros. 
  assert (cA_1 m one y=A_1 m one y).
rewrite cA_1_eq. elim (pred_dec m one y). 
tauto. tauto. tauto. 
  assert (succ m one y_1).  unfold succ. unfold y_1.
rewrite H3. rewrite A_A_1. apply exd_not_nil with m.
tauto. tauto. tauto. tauto.
  rewrite ne_G1_bis. rewrite ne_Shift1. tauto.
tauto. tauto. apply inv_hmap_Shift. tauto.
tauto. generalize (exd_Shift m one y_1 x). tauto.
  rewrite ne_G1_bis. tauto. tauto. tauto.
Qed.

Lemma ne_Flip3: forall(m2:fmap)(xff x:dart),
   inv_hmap m2 -> exd m2 x -> exd m2 xff ->
        ne (Merge m2 one xff x) = ne m2.
Proof.
 intros.
 apply ne_Merge1_bis. tauto. tauto. tauto.
Qed.

Lemma ne_Flip4: forall(m3:fmap)(yff y:dart),
   inv_hmap m3 -> exd m3 y -> exd m3 yff ->
        ne (Merge m3 one yff y) = ne m3.
Proof.
 intros.
 apply ne_Merge1_bis. tauto. tauto. tauto.
Qed.

Lemma ne_Flip_1_4:forall(m:fmap)(x:dart),
   let x_1 := cA_1 m one x in
   let y := cA m zero x in
   let y_1 := cA_1 m one y in
   let xff := cF m y_1 in
   let yff :=  cF m x_1 in
   let m1 := Split m one x x_1 in
   let m2 := Split m1 one y y_1 in 
   let m3 := Merge m2 one xff x in  
   let m4 := Merge m3 one yff y in
  inv_Triangulation m -> prec_Flip m x -> 
      ne m1 = ne m /\
        ne m2 = ne m1 /\
             ne m3 = ne m2 /\
                 ne m4 = ne m3.
Proof.
  intros.  
 generalize (inv_hmap_Flip_1_4 m x H H0).
fold y. fold y_1.
fold x_1. fold xff. fold yff.
fold m1. fold m2. fold m3. fold m4. intro.
  generalize (exd_Flip_1_4 m x x). intro.
elim H2.
fold y. fold y_1.
fold x_1. fold xff. fold yff.
fold m1. fold m2. fold m3. fold m4. intros. 
clear H2. clear H4.
assert
 (exd m x /\ exd m1 x /\ exd m2 x /\ exd m3 x /\ exd m4 x).
unfold prec_Flip in H0. tauto. clear H3. 
(* PART 1: *)
  split. unfold m1. unfold x_1. apply ne_Flip1.
unfold inv_Triangulation in H. tauto. tauto.
unfold prec_Flip in H0. lia.
(* PART 2: *)
assert (inv_hmap m). unfold  inv_Triangulation in H. tauto.
assert (inv_hmap m1). unfold m1.
  apply inv_hmap_Split. tauto.
assert (exd m y). generalize (exd_cA m zero x). fold y.  tauto.
  assert (cA m one x <> y). intro.
unfold prec_Flip in H0. fold y in H0.
absurd (expv m x y). tauto.
unfold expv. unfold MA1.MfcA.expo.
split. tauto. split with 1. simpl. 
rewrite <-H6. tauto.
  assert (x <> y). intro. 
unfold prec_Flip in H0. fold y in H0.
absurd (expv m x y). tauto.
rewrite <-H7. apply expv_refl. tauto.
  assert (cA_1 m1 one y = y_1). unfold m1. unfold x_1. 
  rewrite (cA1_1_Flip1 m x y H3).
elim (eq_dart_dec (cA m one x) y). tauto.
elim (eq_dart_dec x y). tauto. fold y_1. tauto.
  unfold prec_Flip in H0. lia. tauto. tauto.
generalize (isPoly_Flip_1_4 m x H H0).
  fold y. fold y_1.
fold x_1. fold xff. fold yff.
fold m1. fold m2. fold m3. fold m4. intros. 
split. unfold m2. rewrite <-H8. rewrite ne_Flip2. 
tauto. tauto. unfold m1. 
generalize (exd_Split m one x x_1 y). tauto.
lia.
(* PART 3: *)
assert (exd m y_1).
generalize (exd_cA_1 m one y). fold y_1. tauto.
assert (exd m xff).
generalize (exd_cF m y_1). fold xff. tauto.
generalize (exd_Flip_1_4 m x xff). intro.
elim H12.
fold y. fold y_1.
fold x_1. fold xff. fold yff.
fold m1. fold m2. fold m3. fold m4. intros. 
clear H12. clear H14.
assert
 (exd m xff /\ exd m1 xff /\ exd m2 xff /\ exd m3 xff /\ exd m4 xff).
tauto. clear H13.
split. unfold m3. rewrite ne_Flip3.
tauto. tauto. tauto. tauto.
(* PART 4 *)
unfold m4. rewrite ne_Flip4. tauto.
tauto.
assert (exd m1 y). unfold m1.
generalize (exd_Split m one x x_1 y). tauto.
assert (exd m2 y). unfold m2.
generalize (exd_Split m1 one y y_1 y). tauto.
unfold m3. generalize (exd_Merge m2 one xff x y). 
tauto. 
assert (exd m x_1).
generalize (exd_cA_1 m one x). fold x_1. tauto.
assert (exd m yff).
generalize (exd_cF m x_1). fold yff. tauto.
generalize (exd_Flip_1_4 m x yff). intro.
elim H15.
fold y. fold y_1.
fold x_1. fold xff. fold yff.
fold m1. fold m2. fold m3. fold m4. intros. 
tauto.
Qed.

Theorem ne_Flip_topo: forall(m:fmap)(x:dart),
   inv_Triangulation m ->
     prec_Flip m x ->
        ne (Flip_topo m x) = ne m.
Proof.
intros. unfold Flip_topo. 
 generalize (ne_Flip_1_4 m x H H0). intros. 
  decompose [and] H1. clear H1. 
      rewrite H6. rewrite H3. rewrite H4. tauto.
Qed.

(* Vertice numbering: *)

Lemma nv_Flip1: forall(m:fmap)(x:dart),
   inv_hmap m -> exd m x ->
    2 <= degreev m x ->
    let x_1 := cA_1 m one x in
        nv (Split m one x x_1) = (nv m + 1)%Z.
Proof.
 intros.
    generalize (degreev_crackv m x  H H0 H1).  intro.
    rewrite nv_Split1. tauto. tauto. unfold x_1. tauto.
Qed.

Lemma nv_Flip2: forall(m1:fmap)(y:dart),
   inv_hmap m1 -> exd m1 y ->
    2 <= degreev m1 y ->
    let y_1 := cA_1 m1 one y in
        nv (Split m1 one y y_1) = (nv m1 + 1)%Z.
Proof.
 intros.
    generalize (degreev_crackv m1 y H H0 H1).  intro.
    rewrite nv_Split1. tauto. tauto. unfold y_1. tauto.
Qed.

Lemma nv_Flip3: forall(m2:fmap)(xff x:dart),
   inv_hmap m2 -> exd m2 x -> exd m2 xff ->
    ~ expv m2 xff x ->
        nv (Merge m2 one xff x) = (nv m2 - 1)%Z.
Proof.
 intros.
 rewrite nv_Merge1. tauto. tauto. tauto. tauto.
Qed.

Lemma nv_Flip4: forall(m3:fmap)(yff y:dart),
   inv_hmap m3 -> exd m3 y -> exd m3 yff ->  
     ~ expv m3 yff y ->
        nv (Merge m3 one yff y) = (nv m3 - 1)%Z.
Proof.
 intros.
 apply nv_Merge1. tauto. tauto. tauto. 
Qed.

(* SUMMARY: OK: *)

Open Scope Z_scope.

Lemma nv_Flip_1_4:forall(m:fmap)(x:dart),
   let x_1 := cA_1 m one x in
   let y := cA m zero x in
   let y_1 := cA_1 m one y in
   let xff := cF m y_1 in
   let yff :=  cF m x_1 in
   let m1 := Split m one x x_1 in
   let m2 := Split m1 one y y_1 in 
   let m3 := Merge m2 one xff x in  
   let m4 := Merge m3 one yff y in
  inv_Triangulation m -> prec_Flip m x -> 
      nv m1 = nv m + 1 /\
        nv m2 = nv m1 + 1 /\
             nv m3 = nv m2 - 1 /\
                 nv m4 = nv m3 - 1.
Proof.
intros.  generalize H H0. intros IT PF. 
 generalize (inv_hmap_Flip_1_4 m x H H0).
fold y. fold y_1.
fold x_1. fold xff. fold yff.
fold m1. fold m2. fold m3. fold m4. intro.
  generalize (exd_Flip_1_4 m x x). intro.
elim H2.
fold y. fold y_1.
fold x_1. fold xff. fold yff.
fold m1. fold m2. fold m3. fold m4. intros. 
clear H2. clear H4.
assert
 (exd m x /\ exd m1 x /\ exd m2 x /\ exd m3 x /\ exd m4 x).
unfold prec_Flip in H0. tauto. clear H3. 
 generalize (exd_Flip_1_4 m x y). intro.
elim H3.
fold y. fold y_1.
fold x_1. fold xff. fold yff.
fold m1. fold m2. fold m3. fold m4. intros. 
clear H3. clear H5.
assert
 (exd m y /\ exd m1 y /\ exd m2 y /\ exd m3 y /\ exd m4 y).
unfold prec_Flip in H0. generalize (exd_cA m zero x). fold y. 
unfold inv_Triangulation in H. tauto. clear H4. 
(* PART 1: *)
  split. unfold m1. unfold x_1. apply nv_Flip1.
unfold inv_Triangulation in H. tauto. tauto.
unfold prec_Flip in H0. lia.
(* PART 2: *)
unfold  inv_Triangulation in H. unfold isMap in H. 
unfold isPoly in H. unfold isTriangulation in H.
decompose [and] H. clear H. 
assert (degreee m x = 2%nat). apply H6. tauto. 
assert (2<= degreev m x)%nat.  apply H5. tauto. 
assert (exd m x). tauto. 
generalize (degreee_invol_nofixpt m x H4 H9). intro.
fold y in H10. assert (y <> x /\ cA m zero y = x). tauto. 
decompose [and] H11. clear H11 H10. 
assert (isTri m x). apply H8. tauto. 
unfold prec_Flip in H0. 
fold y in H0. decompose [and] H0. clear H0. 
assert (cA m one x <> y). 
intro. assert (x=cA_1 m one y). 
rewrite <-H0. rewrite cA_1_cA. tauto. tauto. tauto. 
assert (y=cA_1 m zero x). rewrite <-H13. rewrite cA_1_cA. tauto. 
tauto. tauto. rewrite H19 in H17. fold (cF m x) in H17. 
generalize (Tri_diff_face m x H4 H11 H10). simpl. tauto. 
assert (cA_1 m1 one y = cA_1 m one y).
unfold m1. rewrite cA1_1_Flip1. 
elim ( eq_dart_dec (cA m one x) y). tauto. 
elim (eq_dart_dec x y). intro. symmetry in a. tauto. tauto. 
tauto. tauto. tauto. tauto. 
assert (2<= degreev m1 y)%nat. 
unfold m1. unfold x_1. rewrite (degreev_Flip1 m x y H4). 
elim (eq_dart_dec x y). intro. symmetry in a. tauto. 
elim (expv_dec m (cA_1 m one x) y H4). intros. 
elim H14. apply expv_trans with (cA_1 m one x). 
apply MA1.MfcA.expo_f_1. tauto. tauto. tauto. intros.
apply H5. tauto. tauto. tauto. tauto. 
split. unfold m2.  unfold y_1. 
rewrite <-H17. rewrite nv_Flip2. tauto. tauto. tauto. tauto. 
(* PART 3: *)
assert (exd m xff). unfold xff. generalize (exd_cF m y_1). 
generalize (exd_cA_1 m one y). tauto.
assert (exd m1 xff). unfold m1. 
generalize (exd_Split m one x x_1 xff). tauto. 
assert (exd m2 xff). unfold m2. 
generalize (exd_Split m1 one y y_1 xff). tauto. 
generalize (Tri_diff_face m x H4 H11 H10).
intro. simpl in H23. 
assert (y = cA_1 m zero x). 
rewrite <-H13. rewrite cA_1_cA. tauto. tauto. tauto. 
assert (y_1 = cF m x). unfold cF. rewrite <-H24. fold y_1. tauto. 
assert (xff = cF m (cF m x)). rewrite <-H25. fold xff. tauto. 
rewrite <-H26 in H23. 
assert (degreev m2 x = 1%nat). 
generalize (isPoly_Flip_1_4 m x IT PF).  tauto. 
assert (cA m2 one x = x). 
generalize (degreev_fixpt m2 x). tauto.
assert (~ expv m2 x xff). intro. 
unfold expv in H29. assert (MA1.MfcA.expo2 m2 x xff). 
generalize (MA1.MfcA.expo_expo2 m2 x xff). tauto. 
unfold MA1.MfcA.expo2 in H30. decompose [and] H30. clear H30. 
elim H32. intros j Hj. unfold degreev in H27. 
assert (MA1Tr.MfM.degree m2 x =  MA1.MfcA.degree m2 x). 
tauto. rewrite <-H30 in Hj. 
rewrite H27 in Hj. assert (j = 0)%nat.  lia. 
rewrite H33 in Hj. simpl in Hj. 
absurd (xff=x). tauto. symmetry. tauto. 
split. unfold m3. rewrite nv_Flip3. tauto. 
tauto. tauto. tauto. intro. elim H29. 
apply expv_symm. tauto. tauto. 
(* PART 4: *)
assert (exd m yff). unfold yff. generalize (exd_cF m x_1). 
generalize (exd_cA_1 m one x). tauto.
assert (exd m1 yff). unfold m1. 
generalize (exd_Split m one x x_1 yff). tauto. 
assert (exd m2 yff). unfold m2. 
generalize (exd_Split m1 one y y_1 yff). tauto. 
assert (exd m3 yff). unfold m3. 
generalize (exd_Merge m2 one xff x yff).  tauto. 
assert (exd m y). tauto. 
assert (isTri m y). apply H8. tauto. 
generalize (Tri_diff_face m y H4 H34 H35).
intro. simpl in H36. 
assert (degreee m y = 2%nat). apply H6. tauto. 
assert (x = cA_1 m zero y). 
generalize (degreee_invol_nofixpt m y). 
generalize (invol_inverse m zero y). 
rewrite <-H13. tauto. 
assert (yff = cF m (cF m y)).
unfold cF at 2. rewrite <-H38. fold x_1. fold yff. tauto. 
rewrite <-H39 in H36.
assert (degreev m3 y = 1%nat). 
generalize (isPoly_Flip_1_4 m x IT PF).  tauto. 
assert (cA m3 one y = y). 
generalize (degreev_fixpt m3 y). tauto.
assert (~ expv m3 y yff). intro. 
unfold expv in H42. assert (MA1.MfcA.expo2 m3 y yff). 
generalize (MA1.MfcA.expo_expo2 m3 y yff). tauto. 
unfold MA1.MfcA.expo2 in H43. decompose [and] H43. clear H43. 
elim H45. intros j Hj. unfold degreev in H40. 
assert (MA1Tr.MfM.degree m3 y =  MA1.MfcA.degree m3 y). 
tauto. rewrite <-H43 in Hj. 
rewrite H40 in Hj. assert (j = 0)%nat.  lia. 
rewrite H46 in Hj. simpl in Hj. 
absurd (yff=y). tauto. symmetry. tauto. 
unfold m4. rewrite nv_Flip4. tauto. 
tauto. tauto. tauto. intro. elim H42. 
apply expv_symm. tauto. tauto. 
Qed.

Theorem nv_Flip_topo: forall(m:fmap)(x:dart),
   inv_Triangulation m ->
     prec_Flip m x ->
        nv (Flip_topo m x) = nv m.
Proof.
    Proof.
intros. unfold Flip_topo. 
 generalize (nv_Flip_1_4 m x H H0). intros. 
  decompose [and] H1. clear H1. 
     rewrite H6. rewrite H3. rewrite H4. rewrite H2. 
 lia.
Qed.

(* Face numbering: *)

Lemma nf_Flip1: forall(m:fmap)(x:dart),
      let y:= cA m zero x in 
      let x_1 := cA_1 m one x in
   inv_hmap m -> exd m x -> x <> x_1 -> ~expf m x y -> 
        nf (Split m one x x_1) = (nf m - 1)%Z.
Proof.
 intros.
 assert (exd m x_1). generalize (exd_cA_1 m one x). fold x_1. tauto. 
 assert (expv m x x_1). apply expv_symm. tauto. 
  unfold expv. unfold MA1.MfcA.expo. 
   split. tauto. split with 1%nat. simpl. unfold x_1.
  assert (MA1.MfcA.f m (cA_1 m one x) = cA m one (cA_1 m one x)). tauto. 
    rewrite H4. rewrite cA_cA_1. tauto. tauto. tauto. 
 assert (crackv m x x_1). unfold crackv. unfold MA1.crack.
  tauto. 
   assert (x = cA_1 m zero y). unfold y. rewrite cA_1_cA. tauto. tauto. tauto.
     assert (x_1 = cF m y). unfold cF. rewrite <-H6. fold x_1. tauto. 
      assert (~expf m x x_1). intro. 
      elim H2. apply expf_trans with x_1. tauto. rewrite H7. 
         apply expf_symm. unfold expf. split. tauto. 
         apply MF.expo_f. generalize (exd_cA m zero x). fold y. tauto. 
      rewrite nf_Split1. elim (expf_dec m x x_1). tauto. 
        intros. lia. tauto. tauto.
Qed.

Lemma nf_Flip2: forall(m1:fmap)(y:dart),
   let y_1 := cA_1 m1 one y in
     inv_hmap m1 -> exd m1 y -> y <> y_1 -> expf m1 y y_1 -> 
        nf (Split m1 one y y_1) = (nf m1 + 1)%Z.
Proof.
  intros. 
   assert (exd m1 y_1). generalize (exd_cA_1 m1 one y). fold y_1. tauto. 
 assert (expv m1 y y_1). apply expv_symm. tauto. 
  unfold expv. unfold MA1.MfcA.expo. 
   split. tauto. split with 1%nat. simpl. unfold y_1.
  assert (MA1.MfcA.f m1 (cA_1 m1 one y) = cA m1 one (cA_1 m1 one y)). tauto. 
    rewrite H4. rewrite cA_cA_1. tauto. tauto. tauto. 
 assert (crackv m1 y y_1). unfold crackv. unfold MA1.crack.
  split. tauto. tauto. 
     rewrite nf_Split1. elim (expf_dec m1 y y_1). tauto. tauto.
     tauto. tauto.
Qed.

Lemma nf_Flip3: forall(m2:fmap)(xff x:dart), 
  let y:= cA m2 zero x in 
   inv_hmap m2 -> exd m2 x -> exd m2 xff ->
     ~expf m2 xff y ->
        nf (Merge m2 one xff x) = (nf m2 - 1)%Z.
Proof.
  intros. 
     rewrite nf_Merge1. fold y. 
    elim (expf_dec m2 xff y). tauto. intro. lia. 
         tauto. tauto. tauto. 
Qed.

Lemma nf_Flip4: forall(m3:fmap)(yff y:dart), 
  let x:= cA m3 zero y in 
   inv_hmap m3 -> exd m3 y -> exd m3 yff ->
     expf m3 yff x ->
        nf (Merge m3 one yff y) = (nf m3 + 1)%Z.
Proof.
  intros. 
   rewrite nf_Merge1. fold x. 
    elim (expf_dec m3 yff x). tauto. tauto.
         tauto. tauto. tauto. 
Qed.

(* SUMMARY: OK: *)

Open Scope Z_scope.

Lemma nf_Flip_1_4:forall(m:fmap)(x:dart),
   let x_1 := cA_1 m one x in
   let y := cA m zero x in
   let y_1 := cA_1 m one y in
   let xff := cF m y_1 in
   let yff :=  cF m x_1 in
   let m1 := Split m one x x_1 in
   let m2 := Split m1 one y y_1 in 
   let m3 := Merge m2 one xff x in  
   let m4 := Merge m3 one yff y in
  inv_Triangulation m -> prec_Flip m x -> 
      nf m1 = nf m - 1 /\
        nf m2 = nf m1 + 1 /\
             nf m3 = nf m2 - 1 /\
                 nf m4 = nf m3 + 1.
Proof.
intros.  generalize H H0. intros IT PF. 
 generalize (inv_hmap_Flip_1_4 m x H H0).
fold y. fold y_1.
fold x_1. fold xff. fold yff.
fold m1. fold m2. fold m3. fold m4. intro.
  generalize (exd_Flip_1_4 m x x). intro.
elim H2.
fold y. fold y_1.
fold x_1. fold xff. fold yff.
fold m1. fold m2. fold m3. fold m4. intros. 
clear H2. clear H4.
assert
 (exd m x /\ exd m1 x /\ exd m2 x /\ exd m3 x /\ exd m4 x).
unfold prec_Flip in H0. tauto. clear H3. 
 generalize (exd_Flip_1_4 m x y). intro.
elim H3.
fold y. fold y_1.
fold x_1. fold xff. fold yff.
fold m1. fold m2. fold m3. fold m4. intros. 
clear H3. clear H5.
assert
 (exd m y /\ exd m1 y /\ exd m2 y /\ exd m3 y /\ exd m4 y).
unfold prec_Flip in H0. generalize (exd_cA m zero x). fold y. 
unfold inv_Triangulation in H. tauto. clear H4. 
unfold inv_Triangulation in H. 
unfold isMap in H. unfold isPoly in H. unfold isTriangulation in H. 
decompose [and] H. clear H.
unfold prec_Flip in H0. fold y in H0. 
decompose [and] H0. clear H0. 
(* PART 1: *)
assert (2 <= degreev m x)%nat. 
apply H5. tauto.  
assert (x <> x_1). 
generalize (Poly_diff_vertex m x). simpl. fold x_1. tauto. 
split. unfold m1. 
rewrite nf_Flip1. tauto. tauto. tauto. fold x_1. tauto.
  fold y. tauto. 
(* PART 2: *)
assert (degreee m x = 2%nat). apply H6. tauto. 
assert (exd m x). tauto. 
generalize (degreee_invol_nofixpt m x H4 H14). intro.
fold y in H15. assert (y <> x /\ cA m zero y = x). tauto. 
decompose [and] H16. clear H16 H15. 
assert (cA m one x <> y). 
intro. assert (x=cA_1 m one y). 
rewrite <-H15. rewrite cA_1_cA. tauto. tauto. tauto. 
assert (y=cA_1 m zero x). rewrite <-H18. rewrite cA_1_cA. tauto. 
tauto. tauto. rewrite H19 in H16. fold (cF m x) in H16. 
assert (isTri m x). apply H8. tauto. 
generalize (Tri_diff_face m x H4 H14 H20). simpl. tauto. 
assert (cA_1 m1 one y = y_1).
unfold m1. rewrite cA1_1_Flip1. 
elim (eq_dart_dec (cA m one x) y). tauto. 
elim (eq_dart_dec x y). intro. symmetry in a. tauto. 
fold y_1. tauto. tauto. tauto. tauto. tauto.
assert (expv m1 y y_1). apply expv_symm. tauto.
assert (y = cA m1 one y_1). rewrite <-H16. 
rewrite cA_cA_1. tauto. tauto. tauto. rewrite H19.
   apply MA1.MfcA.expo_f. rewrite <-H16. 
   generalize (exd_cA_1 m1 one y). tauto. 
assert (2<= degreev m y)%nat. apply H5. tauto. 
assert (y <> y_1). 
generalize (Poly_diff_vertex m y). simpl. fold y_1. tauto. 
assert (isTri m x). apply H8. tauto.
assert (isTri m y). apply H8. tauto.
assert (y_1 = cF m1 (cF m1 y)).
assert (isMap m). unfold isMap. tauto. 
generalize (cF_Flip1_detail_1 m x H4 H24 H H0 H20 H7 H9 H22 H23).
fold x_1. fold y. fold m1. fold y_1. intro. decompose [and] H25. clear H25. 
     rewrite H26. symmetry. tauto. 
assert (expf m1 y y_1). 
unfold expf. split. tauto. 
  unfold MF.expo. split. tauto. split with 2%nat. simpl. symmetry. tauto. 
split. unfold m2. 
rewrite nf_Split1. 
elim (expf_dec m1 y y_1). tauto. tauto. 
tauto. unfold crackv. unfold MA1.crack. tauto. 
(* PART3: *)
assert (exd m xff). 
unfold xff. generalize (exd_cF m y_1). 
generalize (exd_cA_1 m one y). fold y_1. tauto. 
generalize (isSubd_Flip_1_4 m x IT PF). 
fold x_1. fold y. fold y_1. fold xff. fold yff. 
fold m1. fold m2; fold m3; fold m4.
intros. 
assert (cA m2 zero x = y). unfold m2.
rewrite cA_Split. 
elim (eq_dim_dec one zero). intro. inversion a. 
unfold m1. 
rewrite cA_Split. 
elim (eq_dim_dec one zero). intro. inversion a. 
fold y. tauto. tauto. 
unfold crack. elim (eq_dim_dec one zero). intro. inversion a. 
unfold crackv. unfold MA1.crack. split. tauto. 
apply MA1.MfcA.expo_f_1. tauto. tauto. tauto. 
unfold crack. elim (eq_dim_dec one zero). intro. inversion a. 
unfold crackv. unfold MA1.crack. split. tauto. 
rewrite <-H16. apply MA1.MfcA.expo_f_1. tauto. tauto. 
assert (exd m1 xff). unfold m1. generalize (exd_Split m one x x_1 xff). tauto.
assert (exd m2 xff). unfold m2. generalize (exd_Split m1 one y y_1 xff). tauto.
assert (cA m1 one x = x). unfold m1. 
rewrite cA_Split. elim (eq_dim_dec one one). elim (eq_dart_dec x x). 
unfold x_1. rewrite cA_cA_1. tauto. tauto. tauto. tauto. tauto. tauto. 
unfold crack. elim (eq_dim_dec one zero). intro. inversion a. 
unfold crackv. unfold MA1.crack. split. tauto. 
apply MA1.MfcA.expo_f_1. tauto. tauto. 
assert (degreev m1 x = 1)%nat. 
generalize (degreev_fixpt m1 x). tauto. 
assert (2 <= degreev m1 y)%nat. 
unfold m1. unfold x_1. rewrite (degreev_Flip1 m x y H4). 
elim (eq_dart_dec x y). intro. symmetry in a. tauto.
elim (expv_dec m (cA_1 m one x) y). intros. 
elim H7. apply expv_trans with x_1. 
unfold x_1. apply MA1.MfcA.expo_f_1. tauto. tauto. 
unfold x_1. tauto. tauto. tauto. tauto. tauto. 
assert (inv_hmap m1). tauto. 
assert (isHexa m1 x). tauto. 
assert (isMap m1). unfold isMap. intros. 
assert (isMap m). unfold isMap. tauto. 
unfold m1. assert (exd m z). 
generalize (exd_Split m one x x_1 z). fold m1. tauto. 
unfold x_1. rewrite (degreee_Flip1 m x z H4 H37 H14 H38). 
tauto. 
assert (exd m1 y). tauto. 
assert (x = cF m1 y). 
unfold m1. rewrite cF_Flip1. fold y. 
elim (eq_dart_dec (cF_1 m x) y). intro.
elim H9. rewrite <-a. unfold expf. 
  split. tauto. apply MF.expo_f_1. tauto. tauto. 
  elim ( eq_dart_dec y y). tauto. tauto. tauto. tauto. tauto. tauto.
   rewrite H38 in H35. rewrite H38 in H32. 
generalize (cF_Flip2_detail_1 m1 y H34 H36 H37 H35 H32 H33). 
  rewrite <-H38. 
rewrite <-H38 in H24. rewrite <-H24. fold m2. 
intro. 
assert (isMap m). unfold isMap. tauto. 
generalize (cF_Flip1_detail_1 m x H4 H40 H14 H0 H20 H7 H9 H22 H23).  
fold y. fold x_1. fold y_1. fold xff. fold yff. fold m1. intro.  
decompose [and] H39. clear H39. 
decompose [and] H41. clear H41. 
rewrite H47 in H43. rewrite H47 in H46. rewrite H47 in H48. 
rewrite H50 in H43. rewrite H50 in H48. rewrite H51 in H43. 
rewrite H45 in H47. 
assert (~expf m2 xff y). intro. 
assert (expf m2 xff y_1). rewrite <-H47. apply expf_symm. 
unfold expf. split. tauto. apply  MF.expo_f.
generalize (exd_cF m2 y_1). rewrite H47. tauto. 
assert (expf m2 x y). rewrite H44. 
   unfold expf. split. tauto. apply MF.expo_f. tauto. 
assert (expf m2 x y_1). 
apply expf_trans with y. tauto. apply expf_trans with xff. 
 apply expf_symm. tauto. tauto. 
unfold isBar in H27. 
assert (degreef m2 x = 2%nat). tauto. 
 assert (degreef m2 y_1 = 2%nat). 
unfold degreef. 
assert (MF0Tr.MfM.degree m2 y_1 = MF.degree m2 y_1). tauto. 
rewrite H57. 
rewrite <- (MF.expo_degree m2 x y_1). tauto. tauto. 
unfold expf in H55. tauto. 
unfold isQuad in H27. 
rewrite H57 in H27. 
absurd  (2%nat = 4%nat). lia.
tauto.
split. unfold m3. rewrite nf_Flip3.
 tauto. tauto. tauto. tauto. rewrite H28. tauto. 
(* PART 4: *)
rewrite H50 in H46.
rewrite H51 in H48.
rewrite <-H45 in H47. rewrite H47 in H45. 
assert (cA m3 zero y = x). 
unfold m3. rewrite cA0_Flip3.
unfold m2. rewrite <-H16. rewrite cA0_Flip2. 
unfold m1. unfold x_1.  rewrite cA0_Flip1. tauto. 
tauto. tauto. tauto. tauto. tauto. tauto. tauto. tauto. tauto. tauto. 
assert (exd m yff). unfold yff. 
generalize (exd_cF m x_1). generalize (exd_cA_1 m one x). fold x_1. tauto. 
generalize (exd_Flip_1_4 m x yff). intro.
elim H55. 
fold y. fold y_1.
fold x_1. fold xff. fold yff.
fold m1. fold m2. fold m3. fold m4. intros. 
assert (exd m1 yff /\ exd m2 yff /\ exd m3 yff /\ exd m4 yff). 
tauto. clear H55 H56 H57. 
assert (isQuad m2 xff). unfold isQuad. 
assert (degreef = MF.degree). tauto. rewrite H55.
rewrite (MF.expo_degree m2 xff y_1). 
unfold isQuad in H27. tauto. tauto. rewrite H45. 
apply MF.expo_symm. tauto. apply MF.expo_f. 
generalize (exd_cF m2 y_1). rewrite <-H45. tauto. 
assert (inv_hmap m2). tauto. 
assert (isMap m2). 
unfold isMap. intros. 
unfold m2. rewrite <-H16. 
rewrite degreee_Flip2. tauto. tauto. tauto. tauto. 
unfold m2 in H57. generalize (exd_Split m1 one y y_1 z). tauto. 
assert (exd m2 x). tauto. 
assert (isBar m2 x). tauto. 
generalize (cF_Flip3_detail_1 m2 xff x H56 H57 H60 H55 H59 H30). 
intro. cbv zeta in H61. 
rewrite <-H44 in H61. rewrite <-H46 in H61. 
rewrite <-H48 in H61. rewrite <-H43 in H61. 
fold m3 in H61. 
assert (expf m3 yff x).
apply expf_symm. unfold expf. 
split. tauto. unfold MF.expo. split. tauto. 
split with 4%nat. unfold Iter; fold Iter.
decompose [and] H61. clear H61. 
assert (MF.f=cF). tauto. rewrite H61.
rewrite <-H62. rewrite <-H64. rewrite <-H63. rewrite <-H65. 
tauto. 
unfold m4. rewrite nf_Flip4.
tauto. tauto. tauto. tauto. rewrite H52. tauto.
Qed.

Theorem nf_Flip_topo: forall(m:fmap)(x:dart),
   inv_Triangulation m ->
     prec_Flip m x ->
        nf (Flip_topo m x) = nf m.
Proof.
    Proof.
intros. unfold Flip_topo. 
 generalize (nf_Flip_1_4 m x H H0). intros. 
  decompose [and] H1. clear H1. 
     rewrite H6. rewrite H3. rewrite H4. rewrite H2. 
 lia.
Qed.

(* Component counting in the planar case: *)

Lemma planar_nc_Flip1: forall(m:fmap)(x:dart),
  let y := cA m zero x in
  let x_1 := cA_1 m one x in
   inv_hmap m -> planar m -> exd m x ->
    degreee m x = 2%nat ->
      (2 <= degreev m x)%nat -> ~expf m x y ->
        nc (Split m one x x_1) = nc m.
Proof.
 intros.
  generalize (Poly_diff_vertex m x). simpl. fold x_1. intro. 
   assert (x <> cA m one x /\ x <> x_1). tauto. clear H5. 
  generalize (degreee_invol_nofixpt m x H H1). 
     intro. assert (cA m zero x <> x /\ cA m zero (cA m zero x) = x). 
       tauto. fold y in H7. clear H5. 
  assert (x_1 = cF m y). unfold cF. unfold y. rewrite cA_1_cA. fold x_1. tauto. 
       tauto. tauto. 
  assert (expv m x x_1). unfold x_1. unfold expv. 
      apply MA1.MfcA.expo_f_1. tauto. tauto. 
  assert (crackv m x x_1). unfold crackv. 
      unfold MA1.crack. tauto. 
  assert (~ expf m x x_1). intro.
       elim H4. apply expf_trans with x_1. tauto. 
         apply expf_symm. rewrite H5. unfold expf. 
      split. tauto. apply MF.expo_f. 
      generalize (exd_cA m zero x). fold y. tauto. 
  rewrite planar_nc_Split1. 
 elim (expf_dec m x x_1). tauto. intro. lia. 
   tauto. tauto. tauto. 
Qed.
     
Lemma nd_Split:forall(m:fmap)(k:dim)(x x':dart),
  nd (Split m k x x') = nd m.
Proof.
   intros. unfold Split. 
     elim (succ_dec m k x). 
         elim (succ_dec m k x'). 
     intros. rewrite nd_B. simpl. rewrite nd_B. tauto.
  intros. rewrite nd_B. tauto. rewrite nd_B. tauto.
Qed.

Lemma nd_Flip_1_4:forall(m:fmap)(x:dart),
   let x_1 := cA_1 m one x in
   let y := cA m zero x in
   let y_1 := cA_1 m one y in
   let xff := cF m y_1 in
   let yff :=  cF m x_1 in
   let m1 := Split m one x x_1 in
   let m2 := Split m1 one y y_1 in 
   let m3 := Merge m2 one xff x in  
   let m4 := Merge m3 one yff y in
    inv_Triangulation m ->
      nd m1 = nd m /\
        nd m2 = nd m1 /\
             nd m3 = nd m2 /\
                 nd m4 = nd m3.
Proof.
  intros. 
  split. unfold m1. rewrite nd_Split. tauto. 
  split. unfold m2. rewrite nd_Split. tauto. 
  split. unfold m3. rewrite nd_Merge. tauto. 
  unfold m4. rewrite nd_Merge. tauto. 
Qed.

(* Deconnection!  Jordan configuration: *)

Lemma planar_nc_Flip2: forall(m1:fmap)(y:dart),
  let y_1 := cA_1 m1 one y in
   inv_hmap m1 -> planar m1 -> exd m1 y ->
      y <> y_1 -> expf m1 y y_1 ->
        nc (Split m1 one y y_1) = nc m1 + 1.
Proof.
  intros. 
  assert (crackv m1 y y_1). 
  unfold crackv. unfold MA1.crack. split. tauto. 
     unfold y_1. apply MA1.MfcA.expo_f_1. tauto. tauto.
   rewrite planar_nc_Split1. 
  elim (expf_dec m1 y y_1). tauto. tauto.
  tauto. tauto. tauto. 
Qed.
  
Lemma nc_Flip3: forall(m2:fmap)(xff x:dart),
   inv_hmap m2 -> exd m2 x -> exd m2 xff ->
       ~eqc m2 xff x -> 
         nc (Merge m2 one xff x) = nc m2 - 1.
Proof.
  intros. 
   rewrite nc_Merge. 
   elim (eqc_dec m2 xff x). tauto.
intro. lia. tauto. tauto. tauto.
Qed.

Lemma nc_Flip4: forall(m3:fmap)(yff y:dart),
   inv_hmap m3 -> exd m3 y -> exd m3 yff ->
      eqc m3 yff y -> 
         nc (Merge m3 one yff y) = nc m3.
Proof.
  intros. 
   rewrite nc_Merge. 
   elim (eqc_dec m3 yff y). intro. lia.
    tauto. tauto. tauto. tauto.
Qed.

(* REPRENDRE ICI: 

UTILISER LE CRITERE DE DECONNEXION *)

Lemma planar_nc_Flip_1_4:forall(m:fmap)(x:dart),
   let x_1 := cA_1 m one x in
   let y := cA m zero x in
   let y_1 := cA_1 m one y in
   let xff := cF m y_1 in
   let yff :=  cF m x_1 in
   let m1 := Split m one x x_1 in
   let m2 := Split m1 one y y_1 in 
   let m3 := Merge m2 one xff x in  
   let m4 := Merge m3 one yff y in
  inv_Triangulation m -> prec_Flip m x -> planar m ->
      nc m1 = nc m /\ planar m1 /\
        nc m2 = nc m1 + 1 /\ planar m2 /\
             nc m3 = nc m2 - 1 /\ planar m3 /\
                 nc m4 = nc m3 /\ planar m4.
Proof.
intros.  generalize H H0 H1. intros IT PF PL. clear H1. 
generalize (nd_Flip_1_4 m x IT). 
fold y. fold y_1.
fold x_1. fold xff. fold yff.
fold m1. fold m2. fold m3. fold m4. intro ND.
generalize (ne_Flip_1_4 m x IT PF). 
fold y. fold y_1.
fold x_1. fold xff. fold yff.
fold m1. fold m2. fold m3. fold m4. intro NE.
generalize (nv_Flip_1_4 m x IT PF). 
fold y. fold y_1.
fold x_1. fold xff. fold yff.
fold m1. fold m2. fold m3. fold m4. intro NV.
generalize (nf_Flip_1_4 m x IT PF). 
fold y. fold y_1.
fold x_1. fold xff. fold yff.
fold m1. fold m2. fold m3. fold m4. intro NF.
 generalize (inv_hmap_Flip_1_4 m x H H0).
fold y. fold y_1.
fold x_1. fold xff. fold yff.
fold m1. fold m2. fold m3. fold m4. intro.
  generalize (exd_Flip_1_4 m x x). intro.
elim H2.
fold y. fold y_1.
fold x_1. fold xff. fold yff.
fold m1. fold m2. fold m3. fold m4. intros. 
clear H2. clear H4.
assert
 (exd m x /\ exd m1 x /\ exd m2 x /\ exd m3 x /\ exd m4 x).
unfold prec_Flip in H0. tauto. clear H3. 
 generalize (exd_Flip_1_4 m x y). intro.
elim H3.
fold y. fold y_1.
fold x_1. fold xff. fold yff.
fold m1. fold m2. fold m3. fold m4. intros. 
clear H3. clear H5.
assert
 (exd m y /\ exd m1 y /\ exd m2 y /\ exd m3 y /\ exd m4 y).
unfold prec_Flip in H0. generalize (exd_cA m zero x). fold y. 
unfold inv_Triangulation in H. tauto. clear H4. 
unfold inv_Triangulation in H. 
unfold isMap in H. unfold isPoly in H. unfold isTriangulation in H. 
decompose [and] H. clear H.
unfold prec_Flip in H0. fold y in H0. 
decompose [and] H0. clear H0. 
(* PART 1: *)
assert (2 <= degreev m x)%nat. 
apply H5. tauto.  
assert (x <> x_1). 
generalize (Poly_diff_vertex m x). simpl. fold x_1. tauto. 
assert (nc m1 = nc m).
unfold m1. 
rewrite planar_nc_Flip1. tauto. tauto. tauto. tauto. 
apply H6. tauto. tauto. fold y. tauto. 
split. tauto. 
assert (planar m1).
unfold planar. unfold genus. unfold ec. 
assert (nv m1 = nv m + 1). tauto. rewrite H14. clear H14.
assert (ne m1 = ne m). tauto. rewrite H14. clear H14.
assert (nf m1 = nf m - 1). tauto. rewrite H14. clear H14.
assert (nd m1 = nd m). tauto. rewrite H14. clear H14.
rewrite H13. 
assert (nv m + 1 + ne m + (nf m - 1) - nd m = nv m + ne m + nf m - nd m). 
lia. rewrite H14. 
unfold planar in PL. unfold genus. unfold ec. tauto. 
rename H14 into PL1.
split. tauto. 
(* PART 2: *)
assert (degreee m x = 2%nat). apply H6. tauto. 
generalize (degreee_invol_nofixpt m x H4 H). intro.
fold y in H15. assert (y <> x /\ cA m zero y = x). tauto. 
decompose [and] H16. clear H16 H15. 
assert (cA m one x <> y). 
intro. assert (x=cA_1 m one y). 
rewrite <-H15. rewrite cA_1_cA. tauto. tauto. tauto. 
assert (y=cA_1 m zero x). rewrite <-H18. rewrite cA_1_cA. tauto. 
tauto. tauto. rewrite H19 in H16. fold (cF m x) in H16. 
assert (isTri m x). apply H8. tauto. 
generalize (Tri_diff_face m x H4 H H20). simpl. tauto. 
assert (cA_1 m1 one y = y_1).
unfold m1. rewrite cA1_1_Flip1. 
elim (eq_dart_dec (cA m one x) y). tauto. 
elim (eq_dart_dec x y). intro. symmetry in a. tauto. 
fold y_1. tauto. tauto. tauto. tauto. tauto.
assert (expv m1 y y_1). apply expv_symm. tauto.
assert (y = cA m1 one y_1). rewrite <-H16. 
rewrite cA_cA_1. tauto. tauto. tauto. rewrite H19.
   apply MA1.MfcA.expo_f. rewrite <-H16. 
   generalize (exd_cA_1 m1 one y). tauto. 
assert (2<= degreev m y)%nat. apply H5. tauto. 
assert (y <> y_1). 
generalize (Poly_diff_vertex m y). simpl. fold y_1. tauto. 
assert (isTri m x). apply H8. tauto.
assert (isTri m y). apply H8. tauto.
assert (y_1 = cF m1 (cF m1 y)).
assert (isMap m). unfold isMap. tauto. 
generalize (cF_Flip1_detail_1 m x H4 H24 H H0 H20 H7 H9 H22 H23).
fold x_1. fold y. fold m1. fold y_1. intro. decompose [and] H25. clear H25. 
     rewrite H26. symmetry. tauto. 
assert (expf m1 y y_1). 
unfold expf. split. tauto. 
  unfold MF.expo. split. tauto. split with 2%nat. simpl. symmetry. tauto. 
assert (nc m2 = nc m1 + 1).
unfold m2. rewrite <-H16. 
rewrite planar_nc_Flip2. 
tauto. tauto. tauto. tauto. rewrite H16. tauto. rewrite H16. tauto. 
split. tauto. 
assert (planar m2). 
unfold planar. unfold genus. unfold ec. 
assert (nv m2 = nv m1 + 1). tauto. rewrite H27. clear H27.
assert (ne m2 = ne m1). tauto. rewrite H27. clear H27.
assert (nf m2 = nf m1 + 1). tauto. rewrite H27. clear H27.
assert (nd m2 = nd m1). tauto. rewrite H27. clear H27.
rewrite H26. 
assert (nv m1 + 1 + ne m1 + (nf m1 + 1) - nd m1 = 
       (nv m1 + ne m1 + nf m1 - nd m1) + (1)*2). lia. 
rewrite H27. clear H27.
rewrite Zdiv.Z_div_plus.
unfold planar in PL1. unfold genus in PL1. unfold ec in PL1. 
lia. lia. 
split. tauto. 
(* PART3: *)
assert (exd m xff). 
unfold xff. generalize (exd_cF m y_1). 
generalize (exd_cA_1 m one y). fold y_1. tauto. 
generalize (isSubd_Flip_1_4 m x IT PF). 
fold x_1. fold y. fold y_1. fold xff. fold yff. 
fold m1. fold m2; fold m3; fold m4.
intros. 
assert (cA m2 zero x = y). unfold m2.
rewrite cA_Split. 
elim (eq_dim_dec one zero). intro. inversion a. 
unfold m1. 
rewrite cA_Split. 
elim (eq_dim_dec one zero). intro. inversion a. 
fold y. tauto. tauto. 
unfold crack. elim (eq_dim_dec one zero). intro. inversion a. 
unfold crackv. unfold MA1.crack. split. tauto. 
apply MA1.MfcA.expo_f_1. tauto. tauto. tauto. 
unfold crack. elim (eq_dim_dec one zero). intro. inversion a. 
unfold crackv. unfold MA1.crack. split. tauto. 
rewrite <-H16. apply MA1.MfcA.expo_f_1. tauto. tauto. 
assert (exd m1 xff). unfold m1. generalize (exd_Split m one x x_1 xff). tauto.
assert (exd m2 xff). unfold m2. generalize (exd_Split m1 one y y_1 xff). tauto.
assert (inv_hmap m1). tauto. 
generalize (disconnect_planar_criterion_Split1 m1 y y_1
       H33 PL1 H19 H21). 
assert (cA m1 one y_1 = y). 
rewrite <-H16. rewrite cA_cA_1. tauto. tauto. tauto. 
rewrite H34. fold m2. intros. 
assert (~ eqc m2 y_1 y). simpl in H35. tauto. clear H35. 
generalize (isMap_Flip_1_4 m x IT PF). 
fold y. fold y_1.
fold x_1. fold xff. fold yff.
fold m1. fold m2. fold m3. fold m4. intro IM.
assert (isMap m1). tauto. 
assert (exd m1 y). tauto. 
assert (isHexa m1 x). tauto. 
assert (degreev m1 x = 1%nat). 
unfold m1. unfold x_1. rewrite (degreev_Flip1 m x x H4). 
elim (eq_dart_dec x x). tauto. tauto. tauto. tauto. tauto. 
assert (2 <= degreev m1 y)%nat. 
unfold m1. unfold x_1. rewrite (degreev_Flip1 m x y H4). 
elim (eq_dart_dec x y). intro. symmetry in a. tauto. 
elim (expv_dec m (cA_1 m one x) y H4). intros. 
lia. intros. lia. tauto. tauto. tauto.  
assert (isMap m). unfold isMap. tauto.
assert (2 <= degreev m x)%nat. lia. 
assert (2 <= degreev m y)%nat. lia. 
unfold y in H43. unfold y in H9. unfold y in H7.
generalize (cF_Flip1_detail_1 m x H4 H41 H H42 H43 H7 H9 H22 H23). 
fold y. fold y_1.
fold x_1. fold xff. fold yff.
fold m1. fold m2. fold m3. fold m4. intro CF1.
decompose [and] CF1. clear CF1. 
rewrite <-H44 in H38. rewrite <-H44 in H39.
generalize (cF_Flip2_detail_1 m1 y H33 H35 H37 H38 H39 H40). 
rewrite H44. rewrite H46. rewrite H45.  rewrite H47. rewrite H48. 
fold m2. intro CF2. 
assert (~eqc m2 xff x). intro. 
elim H36. 
apply eqc_trans with x. 
apply eqc_trans with xff. 
assert (xff =  cF m2 y_1). tauto. rewrite H51. 
apply expf_eqc. tauto. apply MF.expo_f. 
generalize (exd_cF m2 y_1). rewrite <-H51. tauto. tauto. 
assert (y = cF m2 x). tauto. rewrite H51. 
apply expf_eqc. tauto. apply MF.expo_f. tauto. 
assert (nc m3 = nc m2 - 1).
unfold m3. rewrite nc_Merge. 
elim (eqc_dec m2 xff x). tauto. intro. lia. 
tauto. tauto. tauto. 
split. tauto. 
assert (planar m3). 
unfold planar. unfold genus. unfold ec. 
assert (nv m3 = nv m2 - 1). tauto. rewrite H52. clear H52.
assert (ne m3 = ne m2). tauto. rewrite H52. clear H52.
assert (nf m3 = nf m2 - 1). tauto. rewrite H52. clear H52.
assert (nd m3 = nd m2). tauto. rewrite H52. clear H52.
rewrite H51. 
assert (nv m2 - 1  + ne m2 + (nf m2 - 1) - nd m2 = 
       (nv m2 + ne m2 + nf m2 - nd m2) + (-1)*2). lia. 
rewrite H52. clear H52.
rewrite Zdiv.Z_div_plus.
unfold planar in H27. unfold genus in H27. unfold ec in H27. 
lia. lia. 
split. tauto. 
(* PART 4: *)
assert (exd m yff). unfold yff. 
generalize (exd_cA_1 m one x). fold x_1. 
generalize (exd_cF m x_1). tauto. 
generalize (exd_Flip_1_4 m x yff). 
intro. elim H54. 
fold x_1. fold y. 
fold y_1. fold xff. fold yff.
fold m1. fold m2. fold m3. fold m4. intros. clear H54.
assert ( exd m1 yff /\ exd m2 yff /\ exd m3 yff /\ exd m4 yff). tauto. 
clear H55 H56. 
assert (exd m3 yff). tauto. 
assert (inv_hmap m2). tauto.
assert (isMap m2). tauto. 
assert (isBar m2 x). tauto. 
assert (isQuad m2 xff). unfold isQuad. 
assert (degreef = MF.degree). tauto. rewrite H59. 
rewrite (MF.expo_degree m2 xff y_1).  
unfold isQuad in H29. tauto. tauto. 
apply MF.expo_symm. tauto.
assert (xff = cF m2 y_1). tauto. rewrite H60. 
apply MF.expo_f. 
generalize (exd_cF m2 y_1). rewrite <-H60. tauto. 
assert (exd m2 x). tauto. 
assert (exd m2 xff). tauto. 
decompose [and] CF2. clear CF2. 
generalize (cF_Flip3_detail_1 m2 xff x H56 H57 H58 H59 H60 H61). 
intro. elim H67. clear H67. 
rewrite <-H64. rewrite <-H66. rewrite <-H68. rewrite <-H63. 
fold m3. intros. decompose [and] H69. 
assert (y = Iter (cF m3) 3%nat yff). 
unfold Iter; fold Iter. rewrite <-H73. rewrite <-H75. tauto. 
assert (expf m3 yff y). 
unfold expf. split. tauto. 
unfold MF.expo. split. tauto. 
split with 3%nat. symmetry. tauto. 
assert (nc m4 = nc m3). 
unfold m4. 
rewrite nc_Merge. 
elim (eqc_dec m3 yff y). intro. lia. intro.
elim b. apply expf_eqc. tauto. unfold expf in H76. tauto. 
tauto. tauto. tauto. 
split. tauto. 
unfold planar. unfold genus. unfold ec. 
assert (nv m4 = nv m3 - 1). tauto. rewrite H78. clear H78.
assert (ne m4 = ne m3). tauto. rewrite H78. clear H78.
assert (nf m4 = nf m3 + 1). tauto. rewrite H78. clear H78.
assert (nd m4 = nd m3). tauto. rewrite H78. clear H78.
rewrite H77. 
assert (nv m3 - 1 + ne m3 + (nf m3 + 1) - nd m3 =
      nv m3  + ne m3 + nf m3  - nd m3).  lia. 
rewrite H78. 
unfold planar in H52. unfold genus in H52. unfold ec in H52.
tauto.
Qed.

Theorem planar_nc_Flip_topo: forall(m:fmap)(x:dart),
   inv_Triangulation m -> 
     prec_Flip m x -> planar m ->
        nc (Flip_topo m x) = nc m.
Proof.
    Proof.
intros. unfold Flip_topo. 
 generalize (planar_nc_Flip_1_4 m x H H0 H1). intros. 
  decompose [and] H2. clear H2. 
     rewrite H9. rewrite H7. rewrite H4. rewrite H3. 
 lia.
Qed.

Theorem planar_Flip_topo: forall(m:fmap)(x:dart),
   inv_Triangulation m -> 
     prec_Flip m x -> planar m ->
        planar (Flip_topo m x).
Proof.
intros. unfold Flip_topo. 
 generalize (planar_nc_Flip_1_4 m x H H0 H1). intros. 
  tauto. 
Qed.

Lemma nd_Chp: forall(m:fmap)(x:dart)(p:point),
      nd (Chp m x p) = nd m.
Proof.
 induction m. simpl. tauto.
 simpl. intros. 
    elim (eq_dart_dec d x). simpl. tauto.
    simpl. intro. rewrite IHm. tauto.
 simpl. tauto.
Qed.

Lemma nd_Flip_emb: forall(m4:fmap)(x y xff yff:dart),
      nd (Flip_emb m4 x y xff yff) = nd m4.
Proof.
   intros.
    unfold Flip_emb. rewrite nd_Chp. rewrite nd_Chp.
 tauto.
Qed.

Lemma nd_Flip_topo: forall(m:fmap)(x:dart),
  inv_Triangulation m -> 
      nd (Flip_topo m x) = nd m. 
Proof.
  intros. 
  unfold Flip_topo. 
   set(y:=cA m zero x).
   set(y_1:=cA_1 m one y).
   set(x_1:=cA_1 m one x).
   set(xff:=cF m y_1).
   set(yff:=cF m x_1).
   set(m1:=Split m one x x_1).
   set(m2:=Split m1 one y y_1).
   set(m3:=Merge m2 one xff x). 
   set(m4:=Merge m3 one yff y).
    generalize (nd_Flip_1_4 m x). intros.
       elim H0. fold y. fold y_1. fold x_1. fold xff. fold yff.
   fold m1. fold m2; fold m3. fold m4. intros. clear H0. 
    decompose [and] H2. clear H2. 
    rewrite H5. rewrite H4. rewrite H0. rewrite H1. 
tauto. tauto.
Qed.

Lemma nd_Flip: forall(m:fmap)(x:dart),
  inv_Triangulation m -> 
      nd (Flip m x) = nd m. 
Proof.
   unfold Flip. intros. 
    rewrite nd_Flip_emb. 
     rewrite nd_Flip_topo.
  tauto. tauto.
Qed.
    

Lemma ne_Chp: forall(m:fmap)(x:dart)(p:point),
      ne (Chp m x p) = ne m.
Proof.
 induction m. simpl. tauto.
 simpl. intros. 
    elim (eq_dart_dec d x). simpl. tauto.
    simpl. intro. rewrite IHm. tauto.
 intros. 
    induction d. simpl. rewrite IHm. tauto.
    simpl. apply IHm.
Qed.

Lemma ne_Flip_emb: forall(m4:fmap)(x y xff yff:dart),
      ne (Flip_emb m4 x y xff yff) = ne m4.
Proof.
   intros.
    unfold Flip_emb. rewrite ne_Chp. rewrite ne_Chp.
 tauto.
Qed.

Lemma ne_Flip: forall(m:fmap)(x:dart),
  inv_Triangulation m -> prec_Flip m x ->
      ne (Flip m x) = ne m. 
Proof.
   unfold Flip. intros. 
    rewrite ne_Flip_emb. 
     rewrite ne_Flip_topo.
  tauto. tauto. tauto.
Qed.
    
Lemma nv_Chp: forall(m:fmap)(x:dart)(p:point),
      nv (Chp m x p) = nv m.
Proof.
 induction m. simpl. tauto.
 simpl. intros. 
    elim (eq_dart_dec d x). simpl. tauto.
    simpl. intro. rewrite IHm. tauto.
 intros. 
    induction d. simpl. rewrite IHm. tauto.
    simpl. rewrite IHm. tauto.
Qed.

Lemma nv_Flip_emb: forall(m4:fmap)(x y xff yff:dart),
      nv (Flip_emb m4 x y xff yff) = nv m4.
Proof.
   intros.
    unfold Flip_emb. rewrite nv_Chp. rewrite nv_Chp.
 tauto.
Qed.

Lemma nv_Flip: forall(m:fmap)(x:dart),
  inv_Triangulation m -> prec_Flip m x ->
      nv (Flip m x) = nv m. 
Proof.
   unfold Flip. intros. 
    rewrite nv_Flip_emb. 
     rewrite nv_Flip_topo.
  tauto. tauto. tauto.
Qed.

Lemma Iter_cF_Chp: forall(m:fmap)(x:dart)(p:point)(z:dart)(i:nat),
     Iter (cF (Chp m x p)) i z = Iter (cF m) i z.
Proof.
  induction i. simpl. tauto. 
   simpl. rewrite IHi. rewrite cF_Chp. tauto.
Qed.

Lemma expf_Chp: forall(m:fmap)(x:dart)(p:point)(z t:dart),
      expf (Chp m x p) z t <-> expf m z t.
Proof.
  intros. 
    unfold expf. 
    generalize (exd_Chp m x p z). 
 generalize (inv_hmap_Chp m x p). intros.
   split. intro. split. tauto. 
 unfold MF.expo in H1. 
     decompose [and] H1. 
       elim H5. intros i Hi. unfold MF.expo. 
       split. tauto. split with i. 
   rewrite <- (Iter_cF_Chp m x p). tauto.
split. tauto.   decompose [and] H1. 
       unfold MF.expo in H3.   decompose [and] H3. clear H3. 
     unfold MF.expo. split. tauto. elim H5. intros i Hi. 
         split with i. rewrite Iter_cF_Chp. tauto.
Qed.
    
Lemma nf_Chp: forall(m:fmap)(x:dart)(p:point),
      nf (Chp m x p) = nf m.
Proof.
 induction m. simpl. tauto.
 simpl. intros. 
    elim (eq_dart_dec d x). simpl. tauto.
    simpl. intro. rewrite IHm. tauto.
 intros. 
    induction d. simpl. unfold Chp. fold Chp. 
      rewrite cA_1_Chp. rewrite IHm. 
    generalize (expf_Chp m x p (cA_1 m one d0) d1). 
     elim (expf_dec (Chp m x p) (cA_1 m one d0) d1). 
       elim (expf_dec m (cA_1 m one d0) d1). tauto. tauto. 
  elim (expf_dec m (cA_1 m one d0) d1). tauto. tauto.
    simpl. unfold Chp. fold Chp. 
      rewrite cA_Chp. rewrite IHm. 
    generalize (expf_Chp m x p d0 (cA m zero d1)). intro. 
   elim (expf_dec (Chp m x p) d0 (cA m zero d1)). 
     elim (expf_dec m d0 (cA m zero d1)). tauto. tauto.
     elim (expf_dec m d0 (cA m zero d1)). tauto. tauto.
Qed.
  
Lemma nf_Flip_emb: forall(m4:fmap)(x y xff yff:dart),
      nf (Flip_emb m4 x y xff yff) = nf m4.
Proof.
   intros.
    unfold Flip_emb. rewrite nf_Chp. rewrite nf_Chp.
 tauto.
Qed.

Lemma nf_Flip: forall(m:fmap)(x:dart),
  inv_Triangulation m -> prec_Flip m x ->
      nf (Flip m x) = nf m. 
Proof.
   unfold Flip. intros. 
    rewrite nf_Flip_emb. 
     rewrite nf_Flip_topo.
  tauto. tauto. tauto.
Qed.

Lemma eqc_Chp: forall(m:fmap)(x:dart)(p:point)(z t:dart),
   eqc (Chp m x p) z t <-> eqc m z t.
Proof.
  induction m. simpl. tauto.
  simpl. intros. 
   elim (eq_dart_dec d x). simpl. tauto.
      simpl. generalize (IHm x p0 z t0). tauto. 
       simpl. intros. 
   generalize (IHm x p z t). 
   generalize (IHm x p z d0). 
   generalize (IHm x p z d1). 
   generalize (IHm x p d0 t). 
   generalize (IHm x p d1 t). 
tauto.
Qed.

Lemma nc_Chp: forall(m:fmap)(x:dart)(p:point),
      nc (Chp m x p) = nc m.
Proof.
 induction m. simpl. tauto.
 simpl. intros. 
    elim (eq_dart_dec d x). simpl. tauto.
    simpl. intro. rewrite IHm. tauto.
 intros. 
    simpl. rewrite IHm. 
   generalize (eqc_Chp m x p d0 d1). intro. 
  elim (eqc_dec (Chp m x p) d0 d1). 
     elim (eqc_dec m d0 d1). tauto. tauto.
     elim (eqc_dec m d0 d1). tauto. tauto.
Qed.

Lemma nc_Flip_emb: forall(m4:fmap)(x y xff yff:dart),
      nc (Flip_emb m4 x y xff yff) = nc m4.
Proof.
   intros.
    unfold Flip_emb. rewrite nc_Chp. rewrite nc_Chp.
 tauto.
Qed.

Lemma planar_nc_Flip: forall(m:fmap)(x:dart),
  inv_Triangulation m -> prec_Flip m x -> planar m ->
       nc (Flip m x) = nc m. 
Proof.
   unfold Flip. intros. 
    rewrite nc_Flip_emb. 
     rewrite planar_nc_Flip_topo.
  tauto. tauto. tauto. tauto.
Qed.


Lemma planar_Chp: forall(m:fmap)(x:dart)(p:point),
  planar m -> planar (Chp m x p).
Proof.
   intros. unfold planar. unfold genus. 
     unfold ec. 
    rewrite nd_Chp. rewrite ne_Chp. 
    rewrite nv_Chp. rewrite nf_Chp. 
    rewrite nc_Chp. 
    unfold planar in H. unfold genus in H. 
     unfold ec in H. 
tauto.
Qed.

Lemma planar_Flip_emb: forall(m:fmap)(x y xff yff:dart),
  planar m -> planar (Flip_emb m x y xff yff).
Proof.
   unfold Flip_emb. intros. 
     apply  planar_Chp.  apply  planar_Chp. tauto.
Qed.

Lemma planar_Flip: forall(m:fmap)(x:dart),
  inv_Triangulation m -> prec_Flip m x -> planar m ->
       planar (Flip m x).
Proof.
   unfold Flip. intros. 
    apply planar_Flip_emb. 
     apply planar_Flip_topo.
  tauto. tauto. tauto. 
Qed.

(* POUR LA SUITE DE DELAUNAY, 

IL FAUDRA MONTRER QUE 2 TRIANGLES ADJACENTS (DISTINCTS)
SONT TELS QUE 3 <= degreev POUR LES EXTREMITES DE 
LEUR COTE COMMUN :

Theorem : DANS LE CONTEXTE HABITUEL : 
   (x_1 <> cA m zero xff (= x1) <-> 
          (3 <= degreev m x /\ 3 <= degreev m y)).
ET IDEM POUR y...

*)

(* ENFIN MONTRER QUE LE PLONGEMENT EST
CORRECTEMENT PRESERVE *)


(* 2 PAPIERS : 
- "A BASIS FOR COMPUTER-AIDED PROOFS OF TOPOLOGICAL PROPERTIES
 IN SURFACE SUBDIVISIONS" : Del01 TO Del13

- "PROVING WITH A COMPUTER TOPOLOGICAL PROPERTIES
 OF SPHERE TRIANGULATIONS" : TRIANG01 TO TRIANG03.
 *)

(*====================================================
                  (PROVISIONAL) END
=====================================================*)


