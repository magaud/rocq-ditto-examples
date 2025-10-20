(*=====================================================
=======================================================
                 TOPOLOGICAL FMAPS, HMAPS -
                 WITH TAGS AND EMBEDDINGS
            
                       PART 11: 

             expf, genus, planarity, nc, nf /
  L_B0, B0, L_B1, B1, Shift0, Shift1, Split0, Split1

=======================================================
=====================================================*)

Require Export Del10.

(*=====================================================
    genus, planarity, planarity criterion / 
             L_B0, B0, L_B1, B1
=====================================================*)

(* OK: *)

From Stdlib Require Import ZArith.
Open Scope Z_scope.

Lemma genus_L_B0:forall(m:fmap)(x:dart),
  inv_hmap m -> succ m zero x ->
     genus (L (B m zero x) zero x (A m zero x)) 
       = genus m.
Proof.
unfold genus in |- *.
unfold ec in |- *.
intros m x Inv Suc.
rewrite nc_L_B.
 rewrite nv_L_B.
  rewrite nf_L_B0.
   rewrite ne_L_B.
    rewrite ndZ_L_B.
     repeat tauto.
     try tauto.
     tauto.
    tauto.
    tauto.
   tauto.
   tauto.
  tauto.
  tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma genus_L_B1:forall(m:fmap)(x:dart),
  inv_hmap m -> succ m one x ->
     genus (L (B m one x) one x (A m one x)) 
       = genus m.
Proof.
unfold genus in |- *.
unfold ec in |- *.
intros m x Inv Suc.
rewrite nc_L_B in |- *.
 rewrite nv_L_B in |- *.
  rewrite nf_L_B1 in |- *.
   rewrite ne_L_B in |- *.
    rewrite ndZ_L_B in |- *.
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
 tauto.
Qed.

(* OK: *)

Lemma planar_L_B0:forall(m:fmap)(x:dart),
  inv_hmap m -> succ m zero x -> 
  (planar m <->  
    planar (L (B m zero x) zero x (A m zero x))).
Proof.
unfold planar in |- *.
intros.
generalize (genus_L_B0 m x H H0).
intro.
rewrite H1.
tauto.
Qed.

(* OK: *)

Lemma planar_L_B1:forall(m:fmap)(x:dart),
  inv_hmap m -> succ m one x -> 
  (planar m <->  
    planar (L (B m one x) one x (A m one x))).
Proof.
unfold planar in |- *.
intros.
generalize (genus_L_B1 m x H H0).
intro.
rewrite H1.
tauto.
Qed.

(* OK!: *)

Lemma planar_B0:forall(m:fmap)(x:dart),
  inv_hmap m -> succ m zero x ->
    planar m -> planar (B m zero x).
Proof.
intros.
assert (planar (L (B m zero x) zero x (A m zero x))).
 generalize (planar_L_B0 m x H H0).
   tauto.
 generalize
 (planarity_crit_0 (B m zero x) x (A m zero x)).
   intros.
   assert (exd m x).
  apply succ_exd with zero.
   tauto.
   tauto.
  assert (inv_hmap (B m zero x)).
   apply inv_hmap_B.
     tauto.
   unfold prec_L in H3.
     assert (exd (B m zero x) x).
    generalize (exd_B m zero x x).
      tauto.
    assert (exd m (A m zero x)).
     apply succ_exd_A.
      tauto.
      tauto.
     assert (exd (B m zero x) (A m zero x)).
      generalize (exd_B m zero x (A m zero x)).
        tauto.
      assert (~ succ (B m zero x) zero x).
       unfold succ in |- *.
         rewrite A_B.
        tauto.
        tauto.
       assert (~ pred (B m zero x) zero (A m zero x)).
        unfold pred in |- *.
          rewrite A_1_B.
         tauto.
         tauto.
        assert (cA (B m zero x) zero x <> A m zero x).
         rewrite cA_B.
          elim (eq_dart_dec x x).
           intro.
             apply succ_bottom.
            tauto.
            tauto.
           tauto.
          tauto.
          tauto.
         tauto.
Qed.

(* OK: *)

Lemma planar_B1:forall(m:fmap)(x:dart),
  inv_hmap m -> succ m one x ->
    planar m -> planar (B m one x).
Proof.
intros.
assert (planar (L (B m one x) one x (A m one x))).
 generalize (planar_L_B1 m x H H0).
   tauto.
 generalize
 (planarity_crit_1 (B m one x) x (A m one x)).
   intros.
   assert (exd m x).
  apply succ_exd with one.
   tauto.
   tauto.
  assert (inv_hmap (B m one x)).
   apply inv_hmap_B.
     tauto.
   unfold prec_L in H3.
     assert (exd (B m one x) x).
    generalize (exd_B m one x x).
      tauto.
    assert (exd m (A m one x)).
     apply succ_exd_A.
      tauto.
      tauto.
     assert (exd (B m one x) (A m one x)).
      generalize (exd_B m one x (A m one x)).
        tauto.
      assert (~ succ (B m one x) one x).
       unfold succ in |- *.
         rewrite A_B.
        tauto.
        tauto.
       assert (~ pred (B m one x) one (A m one x)).
        unfold pred in |- *.
          rewrite A_1_B.
         tauto.
         tauto.
        assert (cA (B m one x) one x <> A m one x).
         rewrite cA_B.
          elim (eq_dart_dec x x).
           intro.
             apply succ_bottom.
            tauto.
            tauto.
           tauto.
          tauto.
          tauto.
         tauto.
Qed.

(* PLANARITY CRITERION / B0: OK! *)

Theorem planarity_crit_B0: forall (m:fmap)(x:dart),
 inv_hmap m -> succ m zero x ->
  let m0 := B m zero x in
  let y := A m zero x  in
   (planar m <->
 (planar m0 /\ 
     (~eqc m0 x y \/ expf m0 (cA_1 m0 one x) y))).
Proof.
intros.
assert (inv_hmap (B m zero x)).
 apply inv_hmap_B.
   tauto.
 assert (genus (B m zero x) >= 0).
  apply genus_corollary.
    tauto.
  generalize H2.
    unfold planar in |- *.
    unfold genus in |- *.
    unfold ec in |- *.
    unfold m0 in |- *.
    rewrite nc_B.
   rewrite nv_B.
    rewrite ne_B.
     rewrite ndZ_B.
      rewrite nf_B0.
       assert (cA m zero x = A m zero x).
        rewrite cA_eq.
         elim (succ_dec m zero x).
          tauto.
          tauto.
         tauto.
        generalize (expf_not_expf_B0 m x H H0).
          simpl in |- *.
          rewrite H3.
          rewrite cA_1_B_ter.
         fold y in |- *.
           fold m0 in |- *.
           set (x_1 := cA_1 m one x) in |- *.
           set (x0 := bottom m zero x) in |- *.
           intro.
           elim (expf_dec m y x0).
          elim (eqc_dec m0 x y).
           intros.
             assert
       (nv m + 0 + (ne m + 1) + (nf m + 1) - nd m =
               nv m + ne m + nf m - nd m + 1 * 2).
           clear H4.
            lia.
            rewrite H6.
              rewrite H6 in H5.
              clear H6.
              rewrite Z_div_plus.
             rewrite Z_div_plus in H5.
        set (z := nv m + ne m + nf m - nd m) in |- *.
                fold z in H5.
                split.
               intro.
                 absurd (nc m + 0 - (z / 2 + 1) >= 0). clear H4 a0. 
                lia.
                tauto.
               tauto. clear H4 a0. 
              lia. clear H4 a0. 
             lia.
           intros.
             assert
         (nv m + 0 + (ne m + 1) + (nf m + 1) - nd m =
               nv m + ne m + nf m - nd m + 1 * 2). clear H4 a. 
            lia.
            rewrite H6 in H5.
              rewrite H6.
              clear H6.
              rewrite Z_div_plus in H5.
             rewrite Z_div_plus.
         set (z := nv m + ne m + nf m - nd m) in |- *.
                fold z in H5.
      assert (nc m - z / 2 = nc m + 1 - (z / 2 + 1)). clear H4 a. 
               lia.
               rewrite H6.
                 tauto. clear H4 a. 
              lia. clear H4 a. 
             lia.
          elim (eqc_dec m0 x y).
           intros.
             assert
      (nv m + 0 + (ne m + 1) + (nf m + -1) - nd m =
               nv m + ne m + nf m - nd m). clear H4.
            lia.
            rewrite H6.
              clear H6.
              assert
          (nc m - (nv m + ne m + nf m - nd m) / 2 =
        nc m + 0 - (nv m + ne m + nf m - nd m) / 2). clear H4.
             lia.
             rewrite H6.
               clear H6.
               tauto.
           intros.
             assert (cA_1 m0 one x = cA_1 m one x).
            unfold m0 in |- *.
              rewrite cA_1_B_ter.
             tauto.
             tauto.
             intro.
               inversion H6.
            assert (eqc m0 x_1 y).
             apply expf_eqc.
              unfold m0 in |- *.
                tauto.
              unfold expf in H4.
                unfold expf in b0.
                tauto.
             elim b.
               apply eqc_cA_1_eqc with one.
              unfold m0 in |- *; tauto.
              rewrite H6.
                fold x_1 in |- *.
                tauto.
         tauto.
         intro.
           inversion H4.
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
Qed.

(* OK: *)

Theorem planarity_crit_B1: forall (m:fmap)(x:dart),
 inv_hmap m -> succ m one x ->
  let m1 := B m one x in
  let y:= cA m one x in
  let tx1 := top m one x in
   (planar m <->
 (planar m1 /\ (~eqc m1 x y \/ expf m1 x tx1))).
Proof.
intros.
assert (inv_hmap (B m one x)).
 apply inv_hmap_B.
    tauto.
assert (genus (B m one x) >= 0).
 apply genus_corollary.
    tauto.
generalize H2.
  unfold planar in |- *.
  unfold genus in |- *.
  unfold ec in |- *.
  unfold m1 in |- *.
  rewrite nc_B in |- *.
 rewrite nv_B in |- *.
  rewrite ne_B in |- *.
   rewrite ndZ_B in |- *.
    rewrite nf_B1 in |- *.
     assert (cA m one x = A m one x).
      rewrite cA_eq in |- *.
       elim (succ_dec m one x).
         tauto.
        tauto.
       tauto.
     generalize (not_expf_expf_B1 m x H H0).
       simpl in |- *.
       fold tx1 in |- *.
       rewrite <- H3 in |- *.
       fold y in |- *.
       fold m1 in |- *.
       intro.
       assert (exd m x).
      apply succ_exd with one.
        tauto.
       tauto.
     rename H5 into Ex.
       elim (expf_dec m x tx1).
      elim (eqc_dec m1 x y).
       intros.
         assert
          (nv m + 1 + (ne m + 0) + (nf m + 1) - nd m =
           nv m + ne m + nf m - nd m + 1 * 2). clear H4 a0. 
         lia.
       rewrite H6 in |- *.
         rewrite H6 in H5.
         clear H6.
         rewrite Z_div_plus in |- *.
        rewrite Z_div_plus in H5.
         set (z := nv m + ne m + nf m - nd m) in |- *.
           fold z in H5.
           split.
          intro.
            split.
            absurd (nc m + 0 - (z / 2 + 1) >= 0). clear H4 a0. 
             lia.
            tauto.
           absurd (nc m + 0 - (z / 2 + 1) >= 0). clear H4 a0. 
            lia.
           tauto.
         intro.
           elim H6.
           clear H6.
           intro.
           intro.
            tauto. clear H4 a0. 
         lia. clear H4 a0. 
        lia.
      intros.
        generalize H5.
        clear H5.
        assert
         (nv m + 1 + (ne m + 0) + (nf m + 1) - nd m =
          nv m + ne m + nf m - nd m + 1 * 2). clear H4 a. 
        lia.
      rewrite H5 in |- *.
        clear H5.
        set (z := nv m + ne m + nf m - nd m) in |- *.
        rewrite Z_div_plus in |- *.
       intro.
         split.
        intro.
          split. clear H4 a. 
          lia.
         tauto.
       intros. clear H4 a. 
          lia. clear H4 a. 
       lia.
     intro.
       assert (expf m1 x tx1).
       tauto.
     set (x_1 := cF_1 m x) in |- *.
       assert (tx1 = cF m1 x_1).
      unfold m1 in |- *.
        rewrite cF_B in |- *.
       fold m1 in |- *.
         elim (eq_dim_dec one zero).
        intro.
          inversion a.
       intro.
  elim (eq_dart_dec (A m one x) (cA_1 m1 zero x_1)).
        fold tx1 in |- *.
           tauto.
       unfold m1 in |- *.
         rewrite cA_1_B_ter in |- *.
        unfold x_1 in |- *.
          unfold cF_1 in |- *.
          rewrite cA_1_cA in |- *.
         symmetry  in H3.
            tauto.
         tauto.
        generalize (exd_cA m one x).
           tauto.
        tauto.
       intro.
         inversion H6.
       tauto.
       tauto.
     assert (expf m1 x_1 tx1).
      unfold expf in |- *.
        split.
        tauto.
      unfold expf in |- *.
        split.
       unfold m1 in |- *.
         generalize (exd_B m one x x_1).
         generalize (exd_cF_1 m x).
         fold x_1 in |- *.
          tauto.
      split with 1%nat.
        simpl in |- *.
        rewrite H6 in |- *.
         tauto.
     assert (expf m1 x x_1).
      apply expf_trans with tx1.
        tauto.
      apply expf_symm.
         tauto.
     assert (eqc m1 x x_1).
      apply expf_eqc.
        tauto.
      unfold expf in H8.
         tauto.
     assert (cA m1 zero y = x_1).
      unfold m1 in |- *.
        rewrite cA_B_ter in |- *.
       unfold y in |- *.
         fold (cF_1 m x) in |- *.
         fold x_1 in |- *.
          tauto.
       tauto.
      intro.
        inversion H10.
     rewrite <- H10 in H8.
       assert (eqc m1 y (cA m1 zero y)).
      apply eqc_cA_r.
        tauto.
      assert (exd m y).
       unfold y in |- *.
         assert (exd m x).
        apply succ_exd with one.
          tauto.
         tauto.
       generalize (exd_cA m one x).
          tauto.
      unfold m1 in |- *.
        generalize (exd_B m one x y).
         tauto.
     rewrite H10 in H11.
       assert (eqc m1 x y).
      apply eqc_trans with (cA m1 zero y).
       apply expf_eqc.
         tauto.
       unfold expf in H8.
          tauto.
      apply eqc_symm.
        rewrite H10 in |- *.
         tauto.
     elim (eqc_dec m1 x y).
      intro.
        assert
         (nv m + 1 + (ne m + 0) + (nf m + -1) - nd m =
          nv m + ne m + nf m - nd m). clear H4 H8.
        lia.
      rewrite H13 in |- *.
        clear H13.
        set (z := nv m + ne m + nf m - nd m) in |- *.
        intros.
        split.
       intro.
         split. clear H4 H8.
         lia.
        tauto.
      intros. clear H4 H8.
         lia.
     intro.
       assert
        (nv m + 1 + (ne m + 0) + (nf m + -1) - nd m =
         nv m + ne m + nf m - nd m). clear H4 H8.
       lia.
     rewrite H13 in |- *.
       clear H13.
       set (z := nv m + ne m + nf m - nd m) in |- *.
       intros.
       split.
      intro.
        split.
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
  tauto.
 tauto.
 tauto.
Qed.

(* OK, VERY USEFUL: *)

Theorem disconnect_planar_criterion_B0:
 forall (m:fmap)(x:dart),
  inv_hmap m -> planar m -> succ m zero x ->
    let y := A m zero x in
    let x0 := bottom m zero x in
      (expf m y x0 <-> ~eqc (B m zero x) x y).
Proof.
intros.
generalize (face_cut_join_criterion_B0 m x H H1).
simpl in |- *.
fold x0 in |- *.
fold y in |- *.
intros.
generalize (planarity_crit_B0 m x H H1).
simpl in |- *.
fold x0 in |- *.
fold y in |- *.
intros.
set (x_1 := cA_1 (B m zero x) one x) in |- *.
fold x_1 in H3.
assert (expf (B m zero x) x0 x_1).
 assert (x0 = cA (B m zero x) zero x).
  rewrite cA_B in |- *.
   elim (eq_dart_dec x x).
    fold x0 in |- *.
       tauto.
    tauto.
   tauto.
   tauto.
 unfold x_1 in |- *.
   assert (x = cA_1 (B m zero x) zero x0).
  rewrite H4 in |- *.
    rewrite cA_1_cA in |- *.
    tauto.
  apply inv_hmap_B.
     tauto.
  generalize (exd_B m zero x x).
    assert (exd m x).
   apply succ_exd with zero.
     tauto.
    tauto.
   tauto.
 set (m0 := B m zero x) in |- *.
   rewrite H5 in |- *.
   fold m0 in |- *.
   fold (cF m0 x0) in |- *.
   assert (MF.f = cF).
   tauto.
 rewrite <- H6 in |- *.
   unfold expf in |- *.
   split.
  unfold m0 in |- *.
    apply inv_hmap_B.
     tauto.
 unfold MF.expo in |- *.
   split.
  unfold m0 in |- *.
    generalize (exd_B m zero x x0).
    unfold x0 in |- *.
    assert (exd m (bottom m zero x)).
   apply exd_bottom.
     tauto.
   apply succ_exd with zero.
     tauto.
    tauto.
   tauto.
 split with 1%nat.
   simpl in |- *.
    tauto.
split.
 intro.
   intro.
   assert (~ expf (B m zero x) x_1 y).
  intro.
     absurd (expf (B m zero x) y x0).
    tauto.
  apply expf_trans with x_1.
   apply expf_symm.
      tauto.
  apply expf_symm.
     tauto.
  tauto.
intro.
  assert (cA (B m zero x) zero x = x0).
 unfold x0 in |- *.
   rewrite cA_B in |- *.
  elim (eq_dart_dec x x).
    tauto.
   tauto.
  tauto.
  tauto.
assert (exd m x).
 apply succ_exd with zero.
   tauto.
  tauto.
assert (exd (B m zero x) x).
 generalize (exd_B m zero x x).
    tauto.
assert (inv_hmap (B m zero x)).
 apply inv_hmap_B.
    tauto.
generalize (eqc_cA_r (B m zero x) zero x H9 H8).
  intro.
  assert (~ eqc (B m zero x) y x0).
 intro.
    absurd (eqc (B m zero x) x y).
   tauto.
 apply eqc_trans with x0.
  rewrite <- H6 in |- *.
     tauto.
 apply eqc_symm.
    tauto.
assert (~ expf (B m zero x) y x0).
 intro.
   elim H11.
   apply expf_eqc.
   tauto.
 unfold expf in H12.
    tauto.
 tauto.
Qed.

(* DISCONNECTION CRITERION: OK, VERY USEFUL *)

Theorem disconnect_planar_criterion_B1:forall (m:fmap)(x:dart),
  inv_hmap m -> planar m -> succ m one x ->
    let y := A m one x in
    let tx1 := top m one x in
      (expf m x tx1 <-> ~eqc (B m one x) x y).
Proof.
intros.
generalize (face_cut_join_criterion_B1 m x H H1).
simpl in |- *.
fold y in |- *.
fold tx1 in |- *.
intros.
generalize (planarity_crit_B1 m x H H1).
simpl in |- *.
fold y in |- *; fold tx1 in |- *.
assert (cA m one x = A m one x).
 rewrite cA_eq in |- *.
  elim (succ_dec m one x).
    tauto.
   tauto.
  tauto.
fold y in H3.
  rewrite H3 in |- *.
  set (m1 := B m one x) in |- *.
  intros.
  fold m1 in H2.
  split.
  tauto.
intro.
  generalize (expf_eqc m1 x tx1).
  intros.
  assert (inv_hmap m1).
 unfold m1 in |- *.
   apply inv_hmap_B.
    tauto.
clear H4.
  assert (MF.expo m1 x tx1 -> eqc m1 x tx1).
  tauto.
clear H6.
  assert (expf m1 x tx1 -> eqc m1 x tx1).
 unfold expf in |- *.
    tauto.
clear H4.
  assert (y = cA m1 one tx1).
 unfold m1 in |- *.
   rewrite cA_B in |- *.
  elim (eq_dart_dec x tx1).
   intro.
     rewrite a in H1.
     unfold tx1 in H1.
      absurd (succ m one (top m one x)).
    apply not_succ_top.
       tauto.
    tauto.
  fold tx1 in |- *.
    elim (eq_dart_dec tx1 tx1).
   fold y in |- *.
      tauto.
   tauto.
  tauto.
  tauto.
elim (expf_dec m1 x tx1).
 intro.
   elim H5.
   rewrite H4 in |- *.
   apply eqc_trans with tx1.
   tauto.
 apply eqc_cA_r.
   tauto.
 generalize (MF.expo_exd m1 x tx1).
   unfold expf in a.
    tauto.
 tauto.
Qed.

(* ====================================================
           EQUIVALENCE AND top/bottom
=====================================================*)

(* OK: *)

Lemma eqc_bottom_top: forall(m:fmap)(k:dim)(x:dart),
  inv_hmap m -> exd m x -> 
    (eqc m x (bottom m k x) /\ eqc m x (top m k x)).
Proof.
induction m.
 simpl in |- *.
    tauto.
simpl in |- *.
  unfold prec_I in |- *.
  intros.
  elim H0.
 clear H0.
   elim (eq_dart_dec d x).
  intros.
    symmetry  in a.
     tauto.
  tauto.
clear H0.
  intro.
  elim (eq_dart_dec d x).
 intro.
   symmetry  in a.
    tauto.
intro.
  generalize (IHm k x).
   tauto.
simpl in |- *.
  unfold prec_L in |- *.
  intros.
  elim (eq_dim_dec d k).
 intro.
   elim (eq_dart_dec d1 (bottom m d x)).
  elim (eq_dart_dec d0 (top m d x)).
   intros.
     rewrite a0 in |- *.
     rewrite a1 in |- *.
     rewrite bottom_top_bis in |- *.
    rewrite top_bottom_bis in |- *.
     generalize (IHm d x).
        tauto.
     tauto.
     tauto.
    tauto.
    tauto.
  intros.
    rewrite a0 in |- *.
    generalize (IHm d x).
    generalize (IHm d d0).
     tauto.
 elim (eq_dart_dec d0 (top m d x)).
  intros.
    rewrite a0 in |- *.
    generalize (IHm d x).
    generalize (IHm d d1).
     tauto.
 generalize (IHm d x).
    tauto.
generalize (IHm k x).
   tauto.
Qed.

(* SPECIALIZATIONS: *)

Lemma eqc_bottom: forall(m:fmap)(k:dim)(x:dart),
  inv_hmap m -> exd m x -> eqc m x (bottom m k x).
Proof.
intros.
generalize (eqc_bottom_top m k x H H0).
 tauto.
Qed.

Lemma eqc_top: forall(m:fmap)(k:dim)(x:dart),
  inv_hmap m -> exd m x -> eqc m x (top m k x).
Proof.
intros.
generalize (eqc_bottom_top m k x H H0).
 tauto.
Qed.

(* OK: *)

Lemma eqc_B_bottom: forall(m:fmap)(k:dim)(x:dart),
  inv_hmap m -> exd m x -> 
    eqc (B m k x) x (bottom m k x).
Proof.
intros.
elim (succ_dec m k x).
 intro.
   assert (cA (B m k x) k x = bottom m k x).
  generalize (cA_B m k x x H a).
    elim (eq_dart_dec x x).
    tauto.
   tauto.
 rewrite <- H1 in |- *.
   apply eqc_eqc_cA.
  apply inv_hmap_B.
     tauto.
 apply eqc_refl.
   generalize (exd_B m k x x).
    tauto.
intro.
  rewrite not_succ_B in |- *.
 generalize (eqc_bottom_top m k x H H0).
    tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma eqc_B_top: forall(m:fmap)(k:dim)(x:dart),
  inv_hmap m -> succ m k x -> 
    eqc (B m k x) (A m k x) (top m k x).
Proof.
intros.
assert (cA_1 (B m k x) k (A m k x) = top m k x).
 generalize (cA_1_B m k x (A m k x) H H0).
   elim (eq_dart_dec (A m k x) (A m k x)).
   tauto.
  tauto.
rewrite <- H1 in |- *.
  apply eqc_eqc_cA_1.
 apply inv_hmap_B.
    tauto.
apply eqc_refl.
  generalize (exd_B m k x (A m k x)).
  generalize (succ_exd_A m k x).
   tauto.
Qed.

(*=====================================================
              PROPERTIES ON B
=====================================================*)

Lemma B_idem:forall(m:fmap)(k:dim)(x:dart),
  inv_hmap m -> B (B m k x) k x = B m k x.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   rewrite IHm.
  tauto.
  tauto.
 simpl in |- *.
   unfold prec_L in |- *.
   intros.
   decompose [and] H.
   clear H.
   elim (succ_dec m k x).
  intro.
    elim (eq_dim_dec d k).
   elim (eq_dart_dec d0 x).
    intros.
      rewrite a1 in H3.
      rewrite <- a0 in a.
      tauto.
    simpl in |- *.
      elim (eq_dim_dec d k).
     elim (eq_dart_dec d0 x).
      tauto.
      rewrite IHm.
       tauto.
       tauto.
     tauto.
   simpl in |- *.
     elim (eq_dim_dec d k).
    tauto.
    rewrite IHm.
     tauto.
     tauto.
  intro.
    elim (eq_dim_dec d k).
   elim (eq_dart_dec d0 x).
    intro.
      intro.
      apply not_succ_B.
     tauto.
     tauto.
    simpl in |- *.
      elim (eq_dim_dec d k).
     elim (eq_dart_dec d0 x).
      tauto.
      rewrite IHm.
       tauto.
       tauto.
     tauto.
   simpl in |- *.
     elim (eq_dim_dec d k).
    tauto.
    rewrite IHm.
     tauto.
     tauto.
Qed.

Lemma nc_B_sup:forall(m:fmap)(k:dim)(x:dart),
  inv_hmap m -> nc (B m k x) >= nc m.
Proof.
intros.
elim (succ_dec m k x).
 intro.
   rewrite nc_B.
  elim (eqc_dec (B m k x) x (A m k x)).
   intro.
     lia.
   intro.
     lia.
  tauto.
  tauto.
 intro.
   rewrite not_succ_B.
  lia.
  tauto.
  tauto.
Qed.

(*====================================================
                expe AND bottom
=====================================================*)

(* CALLED f_cA IN J2A, Functor MA: *)

Lemma cA0_MA0:forall(m:fmap)(z:dart),
  cA m zero z = MA0.MfcA.f m z. 
Proof. tauto. Qed.

(* CALLED Iter_f_cA IN J2A, Functor MA: *)

Lemma cA0_MA0_Iter:forall(m:fmap)(i:nat)(z:dart),
  Iter (cA m zero) i z = Iter (MA0.MfcA.f m) i z. 
Proof. 
intros.
symmetry  in |- *.
apply MA0.Iter_f_cA.
Qed.

Lemma cA1_MA1:forall(m:fmap)(z:dart),
  cA m one z = MA1.MfcA.f m z. 
Proof. tauto. Qed.

(* CALLED Iter_f_cA IN J2A, Functor MA: *)

Lemma cA1_MA1_Iter:forall(m:fmap)(i:nat)(z:dart),
  Iter (cA m one) i z = Iter (MA1.MfcA.f m) i z. 
Proof. 
intros.
symmetry  in |- *.
apply MA1.Iter_f_cA.
Qed.

(* CALLED bottom_cA IN J2A, Functor MA: *)

Lemma bottom_cA: forall(m:fmap)(k:dim)(z:dart),
   inv_hmap m -> exd m z -> 
     bottom m k (cA m k z) = bottom m k z. 
Proof.
intros.
induction k.
 apply MA0.bottom_cA.
   tauto.
  tauto.
apply MA1.bottom_cA.
  tauto.
 tauto.
Qed.

(* CALLED expo_bottom_ind in J2A, functor MA: *)

Lemma expe_bottom_ind:   
 forall(m:fmap)(z:dart)(i:nat),
  inv_hmap m -> exd m z -> 
  let t:= Iter (cA m zero) i z in
    bottom m zero z = bottom m zero t. 
Proof.
intros.
unfold t.
apply MA0.expo_bottom_ind.
tauto.
tauto.
Qed.

Lemma expv_bottom_ind:
 forall(m:fmap)(z:dart)(i:nat),
  inv_hmap m -> exd m z -> 
  let t:= Iter (cA m one) i z in
    bottom m one z = bottom m one t. 
Proof.
intros.
unfold t.
apply MA1.expo_bottom_ind.
tauto.
tauto.
Qed.

(* expo_bottom IN J2A... *)

Lemma expe_bottom: forall(m:fmap)(z t:dart),
  inv_hmap m -> expe m z t ->
    bottom m zero z = bottom m zero t. 
Proof.
intros.
apply MA0.expo_bottom.
  tauto.
 tauto.
Qed.

(* expo_bottom IN J2A... *)

Lemma expv_bottom: forall(m:fmap)(z t:dart),
  inv_hmap m -> expv m z t ->
    bottom m one z = bottom m one t. 
Proof.
intros.
apply MA1.expo_bottom.
  tauto.
 tauto.
Qed.

(* THEN, SIMILARLY (OK): *)

Lemma top_cA_1: forall(m:fmap)(k:dim)(z:dart),
   inv_hmap m -> exd m z -> 
     top m k (cA_1 m k z) = top m k z. 
Proof.
induction k.
 intros.
   apply MA0.top_cA_1.
   tauto.
  tauto.
intros.
  apply MA1.top_cA_1.
  tauto.
 tauto.
Qed.

(* CONVERSELY: *)

Lemma cA0_1_MA0_1:forall(m:fmap)(z:dart),
  cA_1 m zero z = MA0.MfcA.f_1 m z. 
Proof. tauto. Qed.

Lemma cA0_1_MA0_1_Iter:forall(m:fmap)(i:nat)(z:dart),
  Iter (cA_1 m zero) i z = Iter (MA0.MfcA.f_1 m) i z. 
Proof. 
intros.
symmetry  in |- *.
apply MA0.Iter_f_1_cA_1.
Qed.

Lemma cA1_1_MA1_1:forall(m:fmap)(z:dart),
  cA_1 m one z = MA1.MfcA.f_1 m z. 
Proof. tauto. Qed.

Lemma cA1_1_MA1_1_Iter:forall(m:fmap)(i:nat)(z:dart),
  Iter (cA_1 m one) i z = Iter (MA1.MfcA.f_1 m) i z. 
Proof. 
intros.
symmetry  in |- *.
apply MA1.Iter_f_1_cA_1.
Qed.

(* OK: *)

Lemma expe_top_ind: forall(m:fmap)(z:dart)(i:nat),
  inv_hmap m -> exd m z -> 
  let t:= Iter (cA m zero) i z in
    top m zero z = top m zero t. 
Proof.
intros.
unfold t in |- *.
apply MA0.expo_top_ind.
  tauto.
 tauto.
Qed.

(* OK: *)

Lemma expv_top_ind: forall(m:fmap)(z:dart)(i:nat),
  inv_hmap m -> exd m z -> 
  let t:= Iter (cA m one) i z in
    top m one z = top m one t. 
Proof.
intros.
unfold t in |- *.
apply MA1.expo_top_ind.
  tauto.
 tauto.
Qed.

(* FINALLY: *)

Lemma expe_top: forall(m:fmap)(z t:dart),
  inv_hmap m -> expe m z t ->
    top m zero z = top m zero t. 
Proof.
intros.
apply MA0.expo_top.
  tauto.
 tauto.
Qed.

Lemma expv_top: forall(m:fmap)(z t:dart),
  inv_hmap m ->expv m z t ->
    top m one z = top m one t. 
Proof.
intros.
apply MA1.expo_top.
  tauto.
 tauto.
Qed.

(*=====================================================
  expe, betweene_dec, 
  between_bottom_B0 AND MA0.MfcA.between_dec
=====================================================*)

(* Decidability of betweene, in Prop: *)

Lemma betweene_dec1: forall(m:fmap)(z v t:dart),
  inv_hmap m -> exd m z -> exd m v ->
    (betweene m z v t \/ ~betweene m z v t).
Proof.
unfold betweene in |- *.
intros.
apply betweene_dec.
  tauto.
 tauto.
Qed.

Lemma bottom_B0: 
  forall (m : fmap)(z : dart),
   inv_hmap m -> exd m z -> 
        bottom (B m zero z) zero z = bottom m zero z.
Proof.
intros.
apply bottom_B.
tauto.
tauto.
Qed.

Lemma bottom_B1: 
  forall (m : fmap)(z : dart),
   inv_hmap m -> exd m z -> 
        bottom (B m one z) one z = bottom m one z.
Proof.
intros.
apply bottom_B.
tauto.
tauto.
Qed.

(* OK: *)

Lemma succ0_zi: forall(m:fmap)(z:dart)(i:nat),
  inv_hmap m -> exd m z -> ~pred m zero z -> 
   (i + 1 < MA0.MfcA.Iter_upb m z)%nat ->
     let zi:= Iter (MA0.MfcA.f m) i z in
       succ m zero zi.
Proof.
intros.
unfold zi in |- *.
apply MA0.succ_zi.
  tauto.
 tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma succ1_zi: forall(m:fmap)(z:dart)(i:nat),
  inv_hmap m -> exd m z -> ~pred m one z -> 
   (i + 1 < MA1.MfcA.Iter_upb m z)%nat ->
     let zi:= Iter (MA1.MfcA.f m) i z in
       succ m one zi.
Proof.
intros.
unfold zi in |- *.
apply MA1.succ_zi.
  tauto.
 tauto.
 tauto.
 tauto.
Qed.

(* OK! BY INSTANTIATION: *)

Lemma bottom_B0_bis: forall(m:fmap)(z:dart)(i j:nat),
  inv_hmap m -> exd m z -> ~pred m zero z ->
    let zi := Iter (MA0.MfcA.f m) i z in
    let zj := Iter (MA0.MfcA.f m) j z in
    let m0 := B m zero zi in
      (i < j < MA0.MfcA.Iter_upb m z)%nat ->
         bottom m0 zero zj = A m zero zi.
Proof.
intros.
unfold zi in |- *.
unfold zj in |- *.
unfold m0 in |- *.
unfold zi in |- *.
apply MA0.bottom_B_bis.
  tauto.
 tauto.
 tauto.
 tauto.
Qed.

Lemma bottom_B1_bis: forall(m:fmap)(z:dart)(i j:nat),
  inv_hmap m -> exd m z -> ~pred m one z ->
    let zi := Iter (MA1.MfcA.f m) i z in
    let zj := Iter (MA1.MfcA.f m) j z in
    let m0 := B m one zi in
      (i < j < MA1.MfcA.Iter_upb m z)%nat ->
         bottom m0 one zj = A m one zi.
Proof.
intros.
unfold zj in |- *.
unfold m0 in |- *.
unfold zi in |- *.
apply MA1.bottom_B_bis.
  tauto.
 tauto.
 tauto.
 tauto.
Qed.

(* THEN, BY INSTANTIATION *)

Lemma bottom_B0_ter: forall(m:fmap)(z:dart)(i j:nat),
  inv_hmap m -> exd m z -> ~pred m zero z ->
    let zi := Iter (MA0.MfcA.f m) i z in
    let zj := Iter (MA0.MfcA.f m) j z in
    let m0 := B m zero zi in
      (j <= i < MA0.MfcA.Iter_upb m z)%nat ->
         bottom m0 zero zj = bottom m zero zj.
Proof.
intros.
unfold zj in |- *.
unfold m0 in |- *.
unfold zi in |- *.
apply MA0.bottom_B_ter.
  tauto.
 tauto.
 tauto.
 tauto.
Qed.


Lemma bottom_B1_ter: forall(m:fmap)(z:dart)(i j:nat),
  inv_hmap m -> exd m z -> ~pred m one z ->
    let zi := Iter (MA1.MfcA.f m) i z in
    let zj := Iter (MA1.MfcA.f m) j z in
    let m0 := B m one zi in
      (j <= i < MA1.MfcA.Iter_upb m z)%nat ->
         bottom m0 one zj = bottom m one zj.
Proof.
intros.
unfold zj in |- *.
unfold m0 in |- *.
unfold zi in |- *.
apply MA1.bottom_B_ter.
  tauto.
 tauto.
 tauto.
 tauto.
Qed.

(* THEN, WE HAVE (OK!): *)

Lemma bottom_B0_quad: forall(m:fmap)(z v:dart)(j:nat),
  inv_hmap m -> exd m z -> ~pred m zero z ->
  let m0 := B m zero v in
  let t := Iter (MA0.MfcA.f m) j z in
   (j < MA0.MfcA.Iter_upb m z)%nat ->
     ~MA0.MfcA.expo m z v ->
        bottom m0 zero t = bottom m zero t.
Proof.
intros.
unfold m0 in |- *.
unfold t in |- *.
apply MA0.bottom_B_quad.
  tauto.
 tauto.
 tauto.
 tauto.
 tauto.
Qed.

Lemma bottom_B1_quad: forall(m:fmap)(z v:dart)(j:nat),
  inv_hmap m -> exd m z -> ~pred m one z ->
  let m0 := B m one v in
  let t := Iter (MA1.MfcA.f m) j z in
   (j < MA1.MfcA.Iter_upb m z)%nat ->
     ~MA1.MfcA.expo m z v ->
        bottom m0 one t = bottom m one t.
Proof.
intros.
unfold m0 in |- *.
unfold t in |- *.
apply MA1.bottom_B_quad.
  tauto.
 tauto.
 tauto.
 tauto.
 tauto.
Qed.

(* THEN (OK): *)

Lemma not_between_B0:forall(m:fmap)(x z:dart),
  inv_hmap m -> exd m x -> exd m z -> x <> z -> 
  let z0:= bottom m zero z in 
   ~betweene m z0 x z ->
       (~MA0.MfcA.expo m z0 x
    \/  forall(i j:nat),
         x = Iter (MA0.MfcA.f m) i z0 ->
         z = Iter (MA0.MfcA.f m) j z0 ->
         (i < MA0.MfcA.Iter_upb m z0)%nat ->
         (j < MA0.MfcA.Iter_upb m z0)%nat ->
              (j <= i)%nat).
Proof.
intros.
unfold z0 in |- *.
apply MA0.not_between_B.
  tauto.
 tauto.
 tauto.
 tauto.
 tauto.
Qed.

Lemma not_between_B1:forall(m:fmap)(x z:dart),
  inv_hmap m -> exd m x -> exd m z -> x <> z -> 
  let z0:= bottom m one z in 
   ~betweenv m z0 x z ->
       (~MA1.MfcA.expo m z0 x
    \/  forall(i j:nat),
         x = Iter (MA1.MfcA.f m) i z0 ->
         z = Iter (MA1.MfcA.f m) j z0 ->
         (i < MA1.MfcA.Iter_upb m z0)%nat ->
         (j < MA1.MfcA.Iter_upb m z0)%nat ->
              (j <= i)%nat).
Proof.
intros.
unfold z0 in |- *.
apply MA1.not_between_B.
  tauto.
 tauto.
 tauto.
 tauto.
 tauto.
Qed.

Lemma Iter_cA0_I:
 forall(m:fmap)(d z:dart)(t:tag)(p:point)(i:nat),
  inv_hmap (I m d t p) -> exd m z ->
    Iter (cA (I m d t p) zero) i z = 
        Iter (cA m zero) i z.
Proof.
intros.
apply MA0.Iter_cA_I.
  tauto.
 tauto.
Qed.

Lemma Iter_cA1_I:
 forall(m:fmap)(d z:dart)(t:tag)(p:point)(i:nat),
  inv_hmap (I m d t p) -> exd m z ->
    Iter (cA (I m d t p) one) i z = 
        Iter (cA m one) i z.
Proof.
intros.
apply MA1.Iter_cA_I.
  tauto.
 tauto.
Qed.

(* USEFUL LEMMAS: *)

(* OK!!: *)

Lemma nopred_expe_L_i:
 forall(m:fmap)(i:nat)(k:dim)(x y z:dart),
   inv_hmap (L m k x y) -> 
    exd m z -> ~pred m zero z ->
     let t:= Iter (cA m zero) i z in  
       (i < MA0.MfcA.Iter_upb m z)%nat ->
         expe (L m k x y) z t.
Proof.
intros.
unfold t in |- *.
apply MA0.nopred_expo_L_i.
  tauto.
 tauto.
 tauto.
 tauto.
Qed.

Lemma nopred_expv_L_i:
 forall(m:fmap)(i:nat)(k:dim)(x y z:dart),
   inv_hmap (L m k x y) -> 
    exd m z -> ~pred m one z ->
     let t:= Iter (cA m one) i z in  
       (i < MA1.MfcA.Iter_upb m z)%nat ->
         expv (L m k x y) z t.
Proof.
intros.
unfold t in |- *.
apply MA1.nopred_expo_L_i.
  tauto.
 tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma expe_bottom_z: forall(m:fmap)(z:dart),
  inv_hmap m -> exd m z -> 
     expe m (bottom m zero z) z.
Proof.
intros.
unfold expe in |- *.
apply MA0.expo_bottom_z.
  tauto.
 tauto.
Qed.

(* OK: *)

Lemma expv_bottom_z: forall(m:fmap)(z:dart),
  inv_hmap m -> exd m z -> 
     expv m (bottom m one z) z.
Proof.
intros.
unfold expe in |- *.
apply MA1.expo_bottom_z.
  tauto.
 tauto.
Qed.

(* IDEM: *)

Lemma bottom_bottom_expe: forall(m:fmap)(z t:dart),
  inv_hmap m -> exd m z -> exd m t -> 
    bottom m zero z = bottom m zero t ->
        expe m z t.
Proof.
intros.
apply MA0.bottom_bottom_expo.
  tauto.
 tauto.
 tauto.
 tauto.
Qed.

(* IDEM: *)

Lemma top_top_expe: forall(m:fmap)(z t:dart),
  inv_hmap m -> exd m z -> exd m t -> 
    top m zero z = top m zero t ->
        expe m z t.
Proof.
intros.
apply MA0.top_top_expo.
  tauto.
 tauto.
 tauto.
 tauto.
Qed.

Lemma bottom_bottom_expv: forall(m:fmap)(z t:dart),
  inv_hmap m -> exd m z -> exd m t -> 
    bottom m one z = bottom m one t ->
        expv m z t.
Proof.
intros.
apply MA1.bottom_bottom_expo.
  tauto.
 tauto.
 tauto.
 tauto.
Qed.

(* IDEM: *)

Lemma top_top_expv: forall(m:fmap)(z t:dart),
  inv_hmap m -> exd m z -> exd m t -> 
    top m one z = top m one t ->
        expv m z t.
Proof.
intros.
apply MA1.top_top_expo.
  tauto.
 tauto.
 tauto.
 tauto.
Qed.

(* FINALLY, THE EXPECTED RESULT (OK): *)

Lemma between_bottom_B0_bis: forall(m:fmap)(x' x:dart),
  inv_hmap m -> exd m x -> exd m x' -> x' <> x -> 
  let x0 := bottom m zero x in
  let m0 := B m zero x' in
      ((betweene m x0 x' x ->
          bottom m0 zero x = A m zero x')
    /\ (~betweene m x0 x' x ->
          bottom m0 zero x = bottom m zero x)).
Proof.
intros.
unfold x0 in |- *; unfold m0 in |- *.
apply MA0.between_bottom_B_bis.
  tauto.
 tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma between_bottom_B1_bis: forall(m:fmap)(x' x:dart),
  inv_hmap m -> exd m x -> exd m x' -> x' <> x -> 
  let x0 := bottom m one x in
  let m0 := B m one x' in
      ((betweenv m x0 x' x ->
          bottom m0 one x = A m one x')
    /\ (~betweenv m x0 x' x ->
          bottom m0 one x = bottom m one x)).
Proof.
intros.
unfold x0 in |- *; unfold m0 in |- *.
apply MA1.between_bottom_B_bis.
  tauto.
 tauto.
 tauto.
 tauto.
Qed.

(* COROLLARY: OK *)

Lemma not_expe_bottom_B0: forall(m:fmap)(x' x:dart),
  inv_hmap m -> exd m x -> exd m x' ->
  let m0 := B m zero x' in
    ~ expe m x' x ->
        bottom m0 zero x = bottom m zero x.
Proof.
intros.
unfold m0 in |- *.
apply MA0.not_expo_bottom_B.
  tauto.
 tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma not_expv_bottom_B0: forall(m:fmap)(x' x:dart),
  inv_hmap m -> exd m x -> exd m x' ->
  let m0 := B m one x' in
    ~ expv m x' x ->
        bottom m0 one x = bottom m one x.
Proof.
intros.
unfold m0 in |- *.
apply MA1.not_expo_bottom_B.
  tauto.
 tauto.
 tauto.
 tauto.
Qed.

(* OK, WHERE ? USELESS ? ... *)

Lemma existi_dec:forall(m:fmap)(z v:dart)(k:nat),
(exists i:nat, (i < k)%nat /\ 
    Iter (MA0.MfcA.f m) i z = v) \/
  (~exists i:nat, (i < k)%nat /\ 
      Iter (MA0.MfcA.f m) i z = v).
Proof.
induction k.
 right.
   intro.
   elim H.
   intros.
    lia.
elim IHk.
 clear IHk.
   intro.
   elim H.
   clear H.
   intros i Hi.
   left.
   split with i.
   split.
   lia.
  tauto.
clear IHk.
  intro.
  elim (eq_dart_dec (Iter (MA0.MfcA.f m) k z) v).
 intro.
   left.
   split with k.
   split.
   lia.
  tauto.
intro.
  right.
  intro.
  elim H0.
  intros i Hi.
  apply H.
  split with i.
  elim (eq_nat_dec i k).
 intro.
   rewrite a in Hi.
    tauto.
intro.
  split.
  lia.
 tauto.
Qed.

(* DECIDABILITY OF MA0.MfcA.between: COULD BE GENERALIZED *)

(* USELESS: 

Lemma MA0_between_dec:
  forall(m:fmap)(z v t:dart), inv_hmap m -> exd m z ->
 (MA0.MfcA.between m z v t \/ 
     ~MA0.MfcA.between m z v t).
*)

(* OK: *)

Lemma betweene_bottom_x_top: forall(m:fmap)(x:dart),
 inv_hmap m -> succ m zero x -> 
    betweene m (bottom m zero x) x (top m zero x).
Proof.
intros.
apply MA0.between_bottom_x_top.
  tauto.
 tauto.
Qed.

Lemma betweenv_bottom_x_top: forall(m:fmap)(x:dart),
 inv_hmap m -> succ m one x -> 
    betweenv m (bottom m one x) x (top m one x).
Proof.
intros.
apply MA1.between_bottom_x_top.
  tauto.
 tauto.
Qed.

(*=====================================================
      CHANGING THE OPENING IN AN ORBIT BY Shift:
  exd, inv_hmap, planar, cA, cA_1, bottom, cF, cF_1,
  top, expf, expe, eqc...
=====================================================*)

(* TAKE THE RESULTS ON Shift IN J2A *)

(* IN FACT: 
cA_Shift
     : forall (m : fmap) (k : dim) (x z : dart),
       inv_hmap m -> succ m k x -> 
           cA (Shift m k x) k z = cA m k z

cA_Shift_ter
     : forall (m : fmap) (k : dim) (x z : dart),
       inv_hmap m ->
       succ m k x -> let k1 := dim_opp k in 
          cA (Shift m k x) k1 z = cA m k1 z

A_Shift
     : forall (m : fmap) (k : dim) (x z : dart),
       inv_hmap m ->
       succ m k x ->
       A (Shift m k x) k z =
       (if eq_dart_dec x z
        then nil
        else if eq_dart_dec (top m k x) z 
             then bottom m k x else A m k z)

A_Shift_ter
     : forall (m : fmap) (k : dim) (x z : dart),
       inv_hmap m ->
       succ m k x -> let k1 := dim_opp k in
          A (Shift m k x) k1 z = A m k1 z

cA_1_Shift
     : forall (m : fmap) (k : dim) (x z : dart),
       inv_hmap m -> succ m k x -> cA_1 (Shift m k x) k z = cA_1 m k z

cA_1_Shift_ter
     : forall (m : fmap) (k : dim) (x z : dart),
       inv_hmap m ->
       succ m k x ->
       let k1 := dim_opp k in 
         cA_1 (Shift m k x) k1 z = cA_1 m k1 z

A_1_Shift
     : forall (m : fmap) (k : dim) (x z : dart),
       inv_hmap m ->
       succ m k x ->
       A_1 (Shift m k x) k z =
       (if eq_dart_dec (A m k x) z
        then nil
        else if eq_dart_dec (bottom m k x) z 
             then top m k x else A_1 m k z)

A_1_Shift_ter
     : forall (m : fmap) (k : dim) (x z : dart),
       inv_hmap m ->
       succ m k x ->
       let k1 := dim_opp k in A_1 (Shift m k x) k1 z = A_1 m k1 z

inv_hmap_Shift
     : forall (m : fmap) (k : dim) (x : dart),
       inv_hmap m -> succ m k x ->
          inv_hmap (Shift m k x)

exd_Shift
     : forall (m : fmap) (k : dim) (x z : dart),
       exd m z <-> exd (Shift m k x) z
*)

(* OK!: "MAIS INUTILE, PUISQU'ON A LE Th QUI SUIT":*) 

Theorem planar_Shift0:forall(m:fmap)(x:dart),
   inv_hmap m -> succ m zero x -> planar m -> 
      planar (Shift m zero x).
Proof.
intros.
generalize (inv_hmap_Shift m zero x H H0).
intro.
generalize
 (planarity_criterion_0 (B m zero x)
      (top m zero x) (bottom m zero x)).
fold (Shift m zero x) in |- *.
set (tx0 := top m zero x) in |- *.
set (bx0 := bottom m zero x) in |- *.
set (m0 := B m zero x) in |- *.
intros.
assert (inv_hmap m0).
 unfold m0 in |- *.
   apply inv_hmap_B.
    tauto.
assert (exd m x).
 apply succ_exd with zero.
   tauto.
  tauto.
assert (exd m tx0).
 unfold tx0 in |- *.
   generalize (exd_top m zero x).
    tauto.
assert (exd m bx0).
 unfold bx0 in |- *.
   generalize (exd_bottom m zero x).
    tauto.
assert (exd m0 tx0).
 unfold m0 in |- *.
   generalize (exd_B m zero x tx0).
    tauto.
assert (exd m0 bx0).
 unfold m0 in |- *.
   generalize (exd_B m zero x bx0).
    tauto.
assert (~ succ m zero tx0).
 unfold tx0 in |- *.
   apply not_succ_top.
    tauto.
assert (~ succ m0 zero tx0).
 unfold m0 in |- *.
   unfold succ in |- *.
   rewrite A_B_bis in |- *.
  unfold succ in H10.
     tauto.
 intro.
   rewrite H11 in H10.
    tauto.
assert (~ pred m zero bx0).
 unfold bx0 in |- *.
   apply not_pred_bottom.
    tauto.
assert (~ pred m0 zero bx0).
 unfold m0 in |- *.
   unfold pred in |- *.
   rewrite A_1_B_bis in |- *.
  unfold pred in H12.
     tauto.
  tauto.
 intro.
   rewrite H13 in H12.
   unfold pred in H12.
   rewrite A_1_A in H12.
  apply H12.
    intro.
    rewrite H14 in H5.
     absurd (exd m nil).
   apply not_exd_nil.
      tauto.
   tauto.
  tauto.
  tauto.
assert (bx0 <> cA m0 zero tx0).
 unfold m0 in |- *.
   rewrite cA_B in |- *.
  elim (eq_dart_dec x tx0).
   intro.
     rewrite <- a in H10.
      tauto.
  fold tx0 in |- *.
    elim (eq_dart_dec tx0 tx0).
   intros.
     intro.
     rewrite H14 in H12.
     unfold pred in H12.
     rewrite A_1_A in H12.
    apply H12.
      intro.
      rewrite H15 in H5.
      generalize H5.
      apply not_exd_nil.
       tauto.
    tauto.
    tauto.
   tauto.
  tauto.
  tauto.
assert (prec_L m0 zero tx0 bx0).
 unfold prec_L in |- *.
   assert (cA m0 zero tx0 <> bx0).
  intro.
    symmetry  in H15.
     tauto.
  tauto.
generalize (planarity_crit_B0 m x H H0).
  simpl in |- *.
  fold m0 in |- *.
  intro.
  assert (planar m0).
  tauto.
generalize (H3 H4 H15 H17).
  intro.
  clear H3.
  assert (~ eqc m0 x (A m zero x) \/ 
       expf m0 (cA_1 m0 one x) (A m zero x)).
  tauto.
clear H16.
  assert (cA m zero x = A m zero x).
 rewrite cA_eq in |- *.
  elim (succ_dec m zero x).
    tauto.
   tauto.
  tauto.
elim H3.
 clear H3.
   intro.
   assert (eqc m0 x bx0).
  unfold bx0 in |- *.
    unfold m0 in |- *.
    apply eqc_B_bottom.
    tauto.
   tauto.
 assert (eqc m0 (A m zero x) tx0).
  unfold tx0 in |- *.
    unfold m0 in |- *.
    apply eqc_B_top.
    tauto.
   tauto.
 assert (~ eqc m0 tx0 bx0).
  intro.
    elim H3.
    apply eqc_trans with bx0.
    tauto.
  apply eqc_trans with tx0.
   apply eqc_symm.
      tauto.
  apply eqc_symm.
     tauto.
  tauto.
intro.
  clear H3.
  assert (cA_1 m0 one x = cA_1 m one x).
 unfold m0 in |- *.
   rewrite cA_1_B_ter in |- *.
   tauto.
  tauto.
 intro.
   inversion H3.
rewrite H3 in H19.
  assert (cA_1 m0 one tx0 = cA_1 m one tx0).
 unfold m0 in |- *.
   rewrite cA_1_B_ter in |- *.
   tauto.
  tauto.
 intro.
   inversion H20.
rewrite H20 in H18.
  assert (expf m0 (A m zero x) (cA_1 m one tx0)).
 unfold expf in |- *.
   split.
   tauto.
 unfold MF.expo in |- *.
   split.
  assert (exd m (A m zero x)).
   apply succ_exd_A.
     tauto.
    tauto.
  unfold m0 in |- *.
    generalize (exd_B m zero x (A m zero x)).
     tauto.
 split with 1%nat.
   simpl in |- *.
   assert (MF.f = cF).
   tauto.
 rewrite H21 in |- *.
   unfold m0 in |- *.
   rewrite cF_B in |- *.
  elim (eq_dim_dec zero zero).
   elim (eq_dart_dec (A m zero x) (A m zero x)).
    rewrite cA_1_B_ter in |- *.
     fold tx0 in |- *.
        tauto.
     tauto.
    intro.
      inversion H22.
    tauto.
   tauto.
  tauto.
  tauto.
assert (expf m0 bx0 (cA_1 m one x)).
 unfold expf in |- *.
   split.
   tauto.
 unfold MF.expo in |- *.
   split.
   tauto.
 split with 1%nat.
   simpl in |- *.
   unfold m0 in |- *.
   rewrite cF_B in |- *.
  elim (eq_dim_dec zero zero).
   elim (eq_dart_dec (A m zero x) bx0).
    rewrite cA_1_B_ter in |- *.
     intro.
       rewrite <- a in H12.
       unfold pred in H12.
       rewrite A_1_A in H12.
       absurd (x <> nil).
        tauto.
      intro.
        rewrite H22 in H5.
         absurd (exd m nil).
       apply not_exd_nil.
          tauto.
       tauto.
      tauto.
      tauto.
     tauto.
    intro.
      inversion H22.
   fold bx0 in |- *.
     elim (eq_dart_dec bx0 bx0).
    rewrite cA_1_B_ter in |- *.
      tauto.
     tauto.
    intro.
      inversion H22.
    tauto.
   tauto.
  tauto.
  tauto.
assert (expf m0 (cA_1 m one tx0) bx0).
 apply expf_trans with (A m zero x).
  apply expf_symm.
     tauto.
 apply expf_trans with (cA_1 m one x).
  apply expf_symm.
     tauto.
 apply expf_symm.
    tauto.
 tauto.
Qed.

(* OK: *)

Theorem planarity_crit_Shift0:
 forall(m:fmap)(x:dart),
   inv_hmap m -> succ m zero x -> 
 (planar m <-> planar (Shift m zero x)).
Proof.
intros.
unfold Shift in |- *.
set (tx0 := top m zero x) in |- *.
set (bx0 := bottom m zero x) in |- *.
set (m0 := B m zero x) in |- *.
assert (inv_hmap m0).
 unfold m0 in |- *.
   apply inv_hmap_B.
    tauto.
assert (exd m x).
 apply succ_exd with zero.
   tauto.
  tauto.
assert (exd m tx0).
 unfold tx0 in |- *.
   generalize (exd_top m zero x).
    tauto.
assert (exd m bx0).
 unfold bx0 in |- *.
   generalize (exd_bottom m zero x).
    tauto.
assert (exd m0 tx0).
 unfold m0 in |- *.
   generalize (exd_B m zero x tx0).
    tauto.
assert (exd m0 bx0).
 unfold m0 in |- *.
   generalize (exd_B m zero x bx0).
    tauto.
assert (~ succ m zero tx0).
 unfold tx0 in |- *.
   apply not_succ_top.
    tauto.
assert (~ succ m0 zero tx0).
 unfold m0 in |- *.
   unfold succ in |- *.
   rewrite A_B_bis in |- *.
   tauto.
 intro.
   assert (~ pred m zero bx0).
  unfold bx0 in |- *.
    apply not_pred_bottom.
     tauto.
 rewrite H8 in H7.
    tauto.
assert (bx0 <> cA m0 zero tx0).
 unfold m0 in |- *.
   rewrite cA_B in |- *.
  elim (eq_dart_dec x tx0).
   intro.
     rewrite <- a in H7.
      tauto.
  fold tx0 in |- *.
    elim (eq_dart_dec tx0 tx0).
   intros.
     unfold bx0 in |- *.
     apply succ_bottom.
     tauto.
    tauto.
   tauto.
  tauto.
  tauto.
assert (~ pred m0 zero bx0).
 unfold m0 in |- *.
   unfold pred in |- *.
   rewrite A_1_B_bis in |- *.
  fold (pred m zero bx0) in |- *.
    unfold bx0 in |- *.
    apply not_pred_bottom.
     tauto.
  tauto.
 unfold bx0 in |- *.
   apply succ_bottom.
   tauto.
  tauto.
generalize (planarity_crit_B0 m x H H0).
  simpl in |- *.
  fold m0 in |- *.
  intro.
  assert (prec_L m0 zero tx0 bx0).
 unfold prec_L in |- *.
   split.
   tauto.
 split.
   tauto.
 split.
   tauto.
 split.
   tauto.
 intro.
   symmetry  in H12.
    tauto.
generalize (planarity_crit_0 m0 tx0 bx0 H1 H12).
  intro.
  assert (eqc m0 x (A m zero x) <-> eqc m0 tx0 bx0).
 assert (cA m zero x = A m zero x).
  rewrite cA_eq in |- *.
   elim (succ_dec m zero x).
     tauto.
    tauto.
   tauto.
 assert (eqc m0 x bx0).
  unfold bx0 in |- *.
    unfold m0 in |- *.
    apply eqc_B_bottom.
    tauto.
   tauto.
 assert (eqc m0 (A m zero x) tx0).
  unfold tx0 in |- *.
    unfold m0 in |- *.
    apply eqc_B_top.
    tauto.
   tauto.
 split.
  intro.
    apply eqc_trans with (A m zero x).
   apply eqc_symm.
      tauto.
  apply eqc_trans with x.
   apply eqc_symm.
      tauto.
   tauto.
 intro.
   apply eqc_trans with bx0.
   tauto.
 apply eqc_symm.
   apply eqc_trans with tx0.
   tauto.
  tauto.
assert (cA_1 m0 one x = cA_1 m one x).
 unfold m0 in |- *.
   rewrite cA_1_B_ter in |- *.
   tauto.
  tauto.
 intro.
   inversion H15.
assert (cA_1 m0 one tx0 = cA_1 m one tx0).
 unfold m0 in |- *.
   rewrite cA_1_B_ter in |- *.
   tauto.
  tauto.
 intro.
   inversion H16.
assert (expf m0 (A m zero x) (cA_1 m one tx0)).
 unfold expf in |- *.
   split.
   tauto.
 unfold MF.expo in |- *.
   split.
  assert (exd m (A m zero x)).
   apply succ_exd_A.
     tauto.
    tauto.
  unfold m0 in |- *.
    generalize (exd_B m zero x (A m zero x)).
     tauto.
 split with 1%nat.
   simpl in |- *.
   assert (MF.f = cF).
   tauto.
 rewrite H17 in |- *.
   unfold m0 in |- *.
   rewrite cF_B in |- *.
  elim (eq_dim_dec zero zero).
   elim (eq_dart_dec (A m zero x) (A m zero x)).
    rewrite cA_1_B_ter in |- *.
     fold tx0 in |- *.
        tauto.
     tauto.
    intro.
      inversion H18.
    tauto.
   tauto.
  tauto.
  tauto.
assert (expf m0 bx0 (cA_1 m one x)).
 unfold expf in |- *.
   split.
   tauto.
 unfold MF.expo in |- *.
   split.
   tauto.
 split with 1%nat.
   simpl in |- *.
   unfold m0 in |- *.
   rewrite cF_B in |- *.
  elim (eq_dim_dec zero zero).
   elim (eq_dart_dec (A m zero x) bx0).
    rewrite cA_1_B_ter in |- *.
     intro.
       rewrite <- a in H12.
       unfold pred in H12.
        absurd (x <> nil).
      intro.
        symmetry  in a.
        generalize a.
        unfold bx0 in |- *; apply succ_bottom.
        tauto.
       tauto.
     symmetry  in a.
        absurd (bx0 = A m zero x).
      unfold bx0 in |- *; apply succ_bottom.
        tauto.
       tauto.
      tauto.
     tauto.
    intro.
      inversion H18.
   fold bx0 in |- *.
     elim (eq_dart_dec bx0 bx0).
    rewrite cA_1_B_ter in |- *.
      tauto.
     tauto.
    intro.
      inversion H18.
    tauto.
   tauto.
  tauto.
  tauto.
rewrite H16 in H13.
  assert
   (expf m0 (cA_1 m0 one x) (A m zero x) 
 <-> expf m0 (cA_1 m one tx0) bx0).
 rewrite H15 in |- *.
   split.
  intro.
    apply expf_trans with (A m zero x).
   apply expf_symm.
      tauto.
  apply expf_symm.
    apply expf_trans with (cA_1 m one x).
    tauto.
   tauto.
 intro.
   apply expf_trans with bx0.
  apply expf_symm.
     tauto.
 apply expf_symm.
   apply expf_trans with (cA_1 m one tx0).
   tauto.
  tauto.
 tauto.
Qed.

(* OK, MAIS "INUTILE A CAUSE DU Th SUIVANT": *)

Theorem planar_Shift1:forall(m:fmap)(x:dart),
   inv_hmap m -> succ m one x -> 
  planar m -> planar (Shift m one x).
Proof.
intros.
generalize (inv_hmap_Shift m one x H H0).
intro.
generalize (planarity_criterion_1 (B m one x) 
    (top m one x) (bottom m one x)).
set (tx1 := top m one x) in |- *.
set (bx1 := bottom m one x) in |- *.
set (m1 := B m one x) in |- *.
intros.
assert (inv_hmap m1).
 unfold m1 in |- *.
   apply inv_hmap_B.
    tauto.
assert (exd m x).
 apply succ_exd with one.
   tauto.
  tauto.
assert (exd m tx1).
 unfold tx1 in |- *.
   generalize (exd_top m one x).
    tauto.
assert (exd m bx1).
 unfold bx1 in |- *.
   generalize (exd_bottom m one x).
    tauto.
assert (exd m1 tx1).
 unfold m1 in |- *.
   generalize (exd_B m one x tx1).
    tauto.
assert (exd m1 bx1).
 unfold m1 in |- *.
   generalize (exd_B m one x bx1).
    tauto.
assert (~ succ m one tx1).
 unfold tx1 in |- *.
   apply not_succ_top.
    tauto.
assert (~ succ m1 one tx1).
 unfold m1 in |- *.
   unfold succ in |- *.
   rewrite A_B_bis in |- *.
  unfold succ in H10.
     tauto.
 intro.
   rewrite H11 in H10.
    tauto.
assert (~ pred m one bx1).
 unfold bx1 in |- *.
   apply not_pred_bottom.
    tauto.
assert (~ pred m1 one bx1).
 unfold m1 in |- *.
   unfold pred in |- *.
   rewrite A_1_B_bis in |- *.
  unfold pred in H12.
     tauto.
  tauto.
 intro.
   rewrite H13 in H12.
   unfold pred in H12.
   rewrite A_1_A in H12.
  apply H12.
    intro.
    rewrite H14 in H5.
     absurd (exd m nil).
   apply not_exd_nil.
      tauto.
   tauto.
  tauto.
  tauto.
assert (x <> tx1).
 intro.
   rewrite H14 in H0.
    tauto.
rename H14 into Dx.
  assert (bx1 <> cA m1 one tx1).
 unfold m1 in |- *.
   rewrite cA_B in |- *.
  elim (eq_dart_dec x tx1).
   intro.
     rewrite <- a in H10.
      tauto.
  fold tx1 in |- *.
    elim (eq_dart_dec tx1 tx1).
   intros.
     intro.
     rewrite H14 in H12.
     unfold pred in H12.
     rewrite A_1_A in H12.
    apply H12.
      intro.
      rewrite H15 in H5.
      generalize H5.
      apply not_exd_nil.
       tauto.
    tauto.
    tauto.
   tauto.
  tauto.
  tauto.
assert (prec_L m1 one tx1 bx1).
 unfold prec_L in |- *.
   assert (cA m1 one tx1 <> bx1).
  intro.
    symmetry  in H15.
     tauto.
  tauto.
generalize (planarity_crit_B1 m x H H0).
  simpl in |- *.
  intro.
  assert (planar m1).
  tauto.
generalize (H3 H4 H15 H17).
  intro.
  clear H3.
  fold m1 in H16.
  assert (~ eqc m1 x (cA m one x) \/ 
     expf m1 x (top m one x)).
  tauto.
clear H16.
  assert (cA m one x = A m one x).
 rewrite cA_eq in |- *.
  elim (succ_dec m one x).
    tauto.
   tauto.
  tauto.
fold tx1 in H3.
  set (y := cA m one x) in |- *.
  fold y in H3.
  elim H3.
 clear H3.
   intro.
   assert (eqc m1 x bx1).
  unfold bx1 in |- *.
    unfold m1 in |- *.
    apply eqc_B_bottom.
    tauto.
   tauto.
 assert (eqc m1 (A m one x) tx1).
  unfold tx1 in |- *.
    unfold m1 in |- *.
    apply eqc_B_top.
    tauto.
   tauto.
 assert (~ eqc m1 tx1 bx1).
  intro.
    elim H3.
    apply eqc_trans with bx1.
    tauto.
  apply eqc_trans with tx1.
   apply eqc_symm.
      tauto.
  apply eqc_symm.
    unfold y in |- *.
    rewrite H16 in |- *.
     tauto.
  tauto.
intro.
  clear H3.
  assert (cA m1 zero bx1 = cA m zero bx1).
 unfold m1 in |- *.
   rewrite cA_B_ter in |- *.
   tauto.
  tauto.
 intro.
   inversion H3.
rewrite H3 in H18.
  assert (cF m1 (cA m zero bx1) = x).
 unfold m1 in |- *.
   rewrite cF_B in |- *.
  elim (eq_dim_dec one zero).
   intro.
     inversion a.
  fold m1 in |- *.
    fold bx1 in |- *.
    rewrite <- H16 in |- *.
    fold y in |- *.
    elim (eq_dart_dec y 
        (cA_1 m1 zero (cA m zero bx1))).
   unfold m1 in |- *.
     rewrite cA_1_B_ter in |- *.
    rewrite cA_1_cA in |- *.
     intro.
       rewrite <- a in H12.
       unfold pred in H12.
       unfold y in H12.
       rewrite H16 in H12.
       rewrite A_1_A in H12.
       absurd (x <> nil).
        tauto.
      intro.
        rewrite H20 in H5.
        generalize H5.
        apply not_exd_nil.
         tauto.
      tauto.
      tauto.
     tauto.
     tauto.
    tauto.
   intro.
     inversion H20.
  unfold m1 in |- *.
    rewrite cA_1_B_ter in |- *.
   rewrite cA_1_cA in |- *.
    elim (eq_dart_dec bx1 bx1).
      tauto.
     tauto.
    tauto.
    tauto.
   tauto.
  intro.
    inversion H20.
  tauto.
  tauto.
assert (expf m1 (cA m zero bx1) x).
 unfold expf in |- *.
   split.
   tauto.
 unfold MF.expo in |- *.
   split.
  rewrite <- H3 in |- *.
    generalize (exd_cA m1 zero bx1).
     tauto.
 split with 1%nat.
   simpl in |- *.
    tauto.
assert (expf m1 tx1 (cA m zero bx1)).
 apply expf_trans with x.
  apply expf_symm.
     tauto.
 apply expf_symm.
    tauto.
 tauto.
Qed.

(* OK: *)

Theorem planarity_crit_Shift1:forall(m:fmap)(x:dart),
   inv_hmap m -> succ m one x -> 
 (planar m <-> planar (Shift m one x)).
Proof.
intros.
generalize (inv_hmap_Shift m one x H H0).
intro.
unfold Shift in |- *.
set (tx1 := top m one x) in |- *.
set (bx1 := bottom m one x) in |- *.
set (m1 := B m one x) in |- *.
intros.
assert (inv_hmap m1).
 unfold m1 in |- *.
   apply inv_hmap_B.
    tauto.
assert (exd m x).
 apply succ_exd with one.
   tauto.
  tauto.
assert (exd m tx1).
 unfold tx1 in |- *.
   generalize (exd_top m one x).
    tauto.
assert (exd m bx1).
 unfold bx1 in |- *.
   generalize (exd_bottom m one x).
    tauto.
assert (exd m1 tx1).
 unfold m1 in |- *.
   generalize (exd_B m one x tx1).
    tauto.
assert (exd m1 bx1).
 unfold m1 in |- *.
   generalize (exd_B m one x bx1).
    tauto.
assert (~ succ m one tx1).
 unfold tx1 in |- *.
   apply not_succ_top.
    tauto.
assert (~ succ m1 one tx1).
 unfold m1 in |- *.
   unfold succ in |- *.
   rewrite A_B_bis in |- *.
   tauto.
 intro.
   rewrite H9 in H8.
    tauto.
assert (~ pred m one bx1).
 unfold bx1 in |- *.
   apply not_pred_bottom.
    tauto.
assert (~ pred m1 one bx1).
 unfold m1 in |- *.
   unfold pred in |- *.
   rewrite A_1_B_bis in |- *.
   tauto.
  tauto.
 unfold bx1 in |- *.
   apply succ_bottom.
   tauto.
  tauto.
assert (bx1 <> cA m1 one tx1).
 unfold m1 in |- *.
   rewrite cA_B in |- *.
  elim (eq_dart_dec x tx1).
   intro.
     rewrite <- a in H8.
      tauto.
  fold tx1 in |- *.
    elim (eq_dart_dec tx1 tx1).
   intros.
     unfold bx1 in |- *.
     apply succ_bottom.
     tauto.
    tauto.
   tauto.
  tauto.
  tauto.
assert (prec_L m1 one tx1 bx1).
 unfold prec_L in |- *.
   assert (cA m1 one tx1 <> bx1).
  intro.
    symmetry  in H13.
     tauto.
  tauto.
generalize (planarity_crit_B1 m x H H0).
  simpl in |- *.
  fold m1 in |- *.
  fold tx1 in |- *.
  intro.
  generalize (planarity_crit_1 m1 tx1 bx1 H2 H13).
  intros.
  assert (cA m one x = A m one x).
 rewrite cA_eq in |- *.
  elim (succ_dec m one x).
    tauto.
   tauto.
  tauto.
set (y := cA m one x) in |- *.
  fold y in H14.
  fold y in H16.
  assert (eqc m1 x bx1).
 unfold bx1 in |- *.
   unfold m1 in |- *.
   apply eqc_B_bottom.
   tauto.
  tauto.
assert (eqc m1 (A m one x) tx1).
 unfold tx1 in |- *.
   unfold m1 in |- *.
   apply eqc_B_top.
   tauto.
  tauto.
rewrite <- H16 in H18.
  assert (~ eqc m1 x y <-> ~ eqc m1 tx1 bx1).
 split.
  intro.
    intro.
    apply H19.
    apply eqc_trans with bx1.
    tauto.
  apply eqc_symm.
    apply eqc_trans with tx1.
    tauto.
   tauto.
 intro.
   intro.
   elim H19.
   apply eqc_symm.
   apply eqc_trans with y.
  apply eqc_trans with x.
   apply eqc_symm;  tauto.
   tauto.
  tauto.
assert (cA m1 zero bx1 = cA m zero bx1).
 unfold m1 in |- *.
   rewrite cA_B_ter in |- *.
   tauto.
  tauto.
 intro.
   inversion H20.
rewrite H20 in H15.
  assert (cF m1 (cA m zero bx1) = x).
 unfold m1 in |- *.
   rewrite cF_B in |- *.
  elim (eq_dim_dec one zero).
   intro.
     inversion a.
  fold m1 in |- *.
    fold bx1 in |- *.
    rewrite <- H16 in |- *.
    fold y in |- *.
    elim (eq_dart_dec y 
  (cA_1 m1 zero (cA m zero bx1))).
   unfold m1 in |- *.
     rewrite cA_1_B_ter in |- *.
    rewrite cA_1_cA in |- *.
     intros.
       symmetry  in a.
        absurd (bx1 = y).
      unfold bx1 in |- *.
        rewrite H16 in |- *.
        apply succ_bottom.
        tauto.
       tauto.
      tauto.
     tauto.
     tauto.
    tauto.
   intro.
     inversion H21.
  rewrite <- H20 in |- *.
    rewrite cA_1_cA in |- *.
   elim (eq_dart_dec bx1 bx1).
     tauto.
    tauto.
   tauto.
   tauto.
  tauto.
  tauto.
assert (expf m1 (cA m zero bx1) x).
 unfold expf in |- *.
   split.
   tauto.
 unfold MF.expo in |- *.
   split.
  rewrite <- H20 in |- *.
    generalize (exd_cA m1 zero bx1).
     tauto.
 split with 1%nat.
   simpl in |- *.
    tauto.
assert (expf m1 x tx1 <-> expf m1 tx1 (cA m zero bx1)).
 split.
  intro.
    apply expf_symm.
    apply expf_trans with x.
    tauto.
   tauto.
 intro.
   apply expf_symm.
   apply expf_trans with (cA m zero bx1).
   tauto.
  tauto.
 tauto.
Qed.

(* OK: "INUTILE PUISQU'ON A LE Th SUIVANT": *)

Theorem planar_Shift:forall(m:fmap)(k:dim)(x:dart),
   inv_hmap m -> succ m k x -> 
  (planar m -> planar (Shift m k x)).
Proof.
induction k.
 apply planar_Shift0.
apply planar_Shift1.
Qed.

(* OK: *)

Theorem planarity_crit_Shift:
 forall(m:fmap)(k:dim)(x:dart),
   inv_hmap m -> succ m k x -> 
  (planar m <-> planar (Shift m k x)).
Proof.
intros.
induction k.
 apply (planarity_crit_Shift0 m x H H0).
apply (planarity_crit_Shift1 m x H H0).
Qed.

(* OK: *)

Lemma bottom_Shift0: 
 forall(m:fmap)(x z:dart)(H:inv_hmap m), 
  succ m zero x -> exd m z -> x <> z ->
  bottom (Shift m zero x) zero z = 
    if expe_dec m x z H then (A m zero x) 
    else bottom m zero z.
Proof.
intros.
generalize (MA0.bottom_Shift m x z H H0 H1 H2).
elim (expe_dec m x z H).
 elim (MA0.MfcA.expo_dec m x z H).
   tauto.
  tauto.
elim (MA0.MfcA.expo_dec m x z H).
  tauto.
 tauto.
Qed.

(* OK: *)

Lemma bottom_Shift1: 
 forall(m:fmap)(x z:dart)(H:inv_hmap m), 
  succ m one x -> exd m z -> x <> z ->
  bottom (Shift m one x) one z = 
    if expv_dec m x z H then (A m one x) 
    else bottom m one z.
Proof.
intros.
generalize (MA1.bottom_Shift m x z H H0 H1 H2).
elim (expv_dec m x z H).
 elim (MA1.MfcA.expo_dec m x z H).
   tauto.
  tauto.
elim (MA1.MfcA.expo_dec m x z H).
  tauto.
 tauto.
Qed.

(* OK: *)

Lemma top_Shift0:
 forall(m:fmap)(x z:dart)(H:inv_hmap m),
 succ m zero x -> exd m z -> x <> z ->
   top (Shift m zero x) zero z =
     if expe_dec m x z H then x 
     else top m zero z.
Proof.
intros.
generalize (MA0.top_Shift m x z H H0 H1 H2).
 tauto.
Qed.

(* OK: *)

Lemma top_Shift1:
 forall(m:fmap)(x z:dart)(H:inv_hmap m),
 succ m one x -> exd m z -> x <> z ->
   top (Shift m one x) one z =
     if expv_dec m x z H then x 
     else top m one z.
Proof.
intros.
generalize (MA1.top_Shift m x z H H0 H1 H2).
 tauto.
Qed.

(* RECALL: 
cF_Shift
     : forall (m : fmap) (k : dim) (x z : dart),
       inv_hmap m -> succ m k x ->
          cF (Shift m k x) z = cF m z

cF_1_Shift
     : forall (m : fmap) (k : dim) (x z : dart),
       inv_hmap m -> succ m k x -> 
          cF_1 (Shift m k x) z = cF_1 m z

Iter_cF_Shift
  : forall (m : fmap) (k : dim) (x z : dart) (i : nat),
       inv_hmap m ->
       succ m k x ->
       let m0 := Shift m k x in 
          Iter (cF m0) i z = Iter (cF m) i z

expof_Shift
     : forall (m : fmap) (k : dim) (x z t : dart),
       inv_hmap m -> succ m k x -> 
          (expof (Shift m k x) z t <-> expof m z t)
*)

(* OK: *)

Theorem nc_Shift :forall(m:fmap)(k:dim)(x:dart),
  inv_hmap m -> succ m k x -> 
     nc (Shift m k x) = nc m.
Proof.
simpl in |- *.
intros.
rewrite nc_B in |- *.
 assert (exd m x).
  apply succ_exd with k.
    tauto.
   tauto.
 generalize (eqc_B_top m k x H H0).
   generalize (eqc_B_bottom m k x H H1).
   intros.
   elim (eqc_dec (B m k x) x (A m k x)).
  elim (eqc_dec (B m k x) (top m k x) (bottom m k x)).
   intros.
      lia.
  intros.
    elim b.
    apply eqc_trans with (A m k x).
   apply eqc_symm.
      tauto.
  apply eqc_trans with x.
   apply eqc_symm.
      tauto.
   tauto.
 elim (eqc_dec (B m k x) (top m k x) (bottom m k x)).
  intros.
    elim b.
    apply eqc_trans with (bottom m k x).
    tauto.
  apply eqc_trans with (top m k x).
   apply eqc_symm.
      tauto.
  apply eqc_symm.
     tauto.
 intros.
    lia.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma eqc_Shift:forall (m:fmap)(k:dim)(x z t:dart),
  inv_hmap m -> succ m k x ->
    (eqc (Shift m k x) z t <-> eqc m z t).
Proof.
simpl in |- *.
intros.
generalize (eqc_B m k x z t H H0).
simpl in |- *.
intro.
generalize (eqc_B_top m k x H H0).
intro.
assert (exd m x).
 apply succ_exd with k.
   tauto.
  tauto.
generalize (eqc_B_bottom m k x H H3).
  intro.
  elim H1.
  clear H1.
  intros.
  split.
 clear H1.
   intro.
   elim H1.
   tauto.
 clear H1.
   intro.
   elim H1.
  clear H1.
    intro.
    assert (eqc (B m k x) z (A m k x)).
   apply eqc_trans with (top m k x).
     tauto.
   apply eqc_symm.
      tauto.
  assert (eqc (B m k x) x t).
   apply eqc_trans with (bottom m k x).
     tauto.
    tauto.
   tauto.
 clear H1.
   intro.
   assert (eqc (B m k x) z x).
  apply eqc_trans with (bottom m k x).
    tauto.
  apply eqc_symm.
     tauto;  tauto.
 assert (eqc (B m k x) (A m k x) t).
  apply eqc_trans with (top m k x).
    tauto.
   tauto.
  tauto.
clear H5.
  intro.
  elim H1.
 clear H1.
   intro.
    tauto.
clear H1.
  intro.
  elim H1.
 clear H1.
   intro.
   right.
   right.
   split.
  apply eqc_trans with x.
    tauto.
   tauto.
 apply eqc_trans with (A m k x).
  apply eqc_symm.
     tauto.
  tauto.
clear H1.
  intro.
  right.
  left.
  split.
 apply eqc_trans with (A m k x).
   tauto.
  tauto.
apply eqc_trans with x.
 apply eqc_symm.
    tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma diff_dim_opp:forall(k j:dim), 
   k <> j -> j = dim_opp k.
Proof.
intros k j; case k; case j; intros.
  tauto.
simpl in |- *.
   tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma Iter_cA_Shift: 
 forall(m:fmap)(k j:dim)(x z:dart)(i:nat),
  inv_hmap m -> succ m k x -> 
   let m0:= Shift m k x in
    Iter (cA m0 j) i z = Iter (cA m j) i z.
Proof.
  intros.
  unfold m0.
induction i.
 simpl in |- *.
 tauto.
 unfold Iter; fold Iter.
 rewrite IHi.
 elim (eq_dim_dec k j).
 intro.
   rewrite <- a in |- *.
   rewrite cA_Shift in |- *.
   tauto.
  tauto.
  tauto.
intro.
  assert (j = dim_opp k).
 apply diff_dim_opp.
    tauto.
rewrite H1 in |- *.
  rewrite cA_Shift_ter in |- *.
  tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma expe_Shift:forall (m:fmap)(x z t:dart),
  inv_hmap m -> succ m zero x ->
     (expe (Shift m zero x) z t <-> expe m z t).
Proof.
intros.
unfold expe in |- *.
apply MA0.expo_Shift.
  tauto.
 tauto.
Qed.

(* OK: *)

Lemma expv_Shift:forall (m:fmap)(x z t:dart),
  inv_hmap m -> succ m one x ->
     (expv (Shift m one x) z t <-> expv m z t).
Proof.
intros.
unfold expe in |- *.
apply MA1.expo_Shift.
  tauto.
 tauto.
Qed.

(* OK: *)

Theorem nf_Shift: forall (m:fmap)(k:dim)(x:dart),
  inv_hmap m -> succ m k x ->
    nf (Shift m k x) = nf m. 
Proof.
intros.
assert (exd m x).
 apply succ_exd with k.
   tauto.
  tauto.
assert (cA m k x = A m k x).
 rewrite cA_eq in |- *.
  elim (succ_dec m k x).
    tauto.
   tauto.
  tauto.
unfold Shift in |- *.
  set (txk := top m k x) in |- *.
  set (bxk := bottom m k x) in |- *.
  induction k.
 simpl in |- *.
   rewrite nf_B0 in |- *.
  fold bxk in |- *.
    rewrite cA_1_B_ter in |- *.
   generalize (expf_not_expf_B0 m x H H0).
     simpl in |- *.
     fold txk in |- *.
     fold bxk in |- *.
     intros.
     rewrite <- H2 in |- *.
     set (y := cA m zero x) in |- *.
     fold y in H3.
     set (m0 := B m zero x) in |- *.
     fold m0 in H3.
     assert (cF m0 bxk = cA_1 m one x).
    unfold m0 in |- *.
      rewrite cF_B in |- *.
     elim (eq_dim_dec zero zero).
      elim (eq_dart_dec (A m zero x) bxk).
       intro.
         symmetry  in a.
          absurd (bxk = A m zero x).
        unfold bxk in |- *.
          apply (succ_bottom m zero x H H0).
        tauto.
      fold bxk in |- *.
        elim (eq_dart_dec bxk bxk).
       rewrite cA_1_B_ter in |- *.
         tauto.
        tauto.
       intro.
         inversion H4.
       tauto.
      tauto.
     tauto.
     tauto.
   assert (cF m0 y = cA_1 m one txk).
    unfold m0 in |- *.
      rewrite cF_B in |- *.
     elim (eq_dim_dec zero zero).
      rewrite <- H2 in |- *.
        fold y in |- *.
        elim (eq_dart_dec y y).
       fold txk in |- *.
         rewrite cA_1_B_ter in |- *.
         tauto.
        tauto.
       intro.
         inversion H5.
       tauto.
      tauto.
     tauto.
     tauto.
   assert (exd m bxk).
    unfold bxk in |- *.
      generalize (exd_bottom m zero x).
       tauto.
   assert (exd m0 bxk).
    unfold m0 in |- *.
      generalize (exd_B m zero x bxk).
       tauto.
   assert (exd m y).
    unfold y in |- *.
      generalize (exd_cA m zero x).
       tauto.
   assert (exd m0 y).
    unfold m0 in |- *.
      generalize (exd_B m zero x y).
       tauto.
   assert (expf m0 bxk (cA_1 m one x)).
    unfold expf in |- *.
      split.
     unfold m0 in |- *.
       apply inv_hmap_B.
        tauto.
    unfold MF.expo in |- *.
      split.
      tauto.
    split with 1%nat.
      simpl in |- *.
       tauto.
   assert (expf m0 y (cA_1 m one txk)).
    unfold expf in |- *.
      split.
     unfold m0 in |- *.
       apply inv_hmap_B.
        tauto.
    unfold MF.expo in |- *.
      split.
      tauto.
    split with 1%nat.
      simpl in |- *.
       tauto.
   elim (expf_dec m y bxk).
    elim (expf_dec m0 (cA_1 m one txk) bxk).
     intros.
       assert (expf m0 (cA_1 m one x) y).
      apply expf_trans with bxk.
       apply expf_symm.
          tauto.
      apply expf_trans with (cA_1 m one txk).
       apply expf_symm.
          tauto.
      apply expf_symm.
         tauto.
      tauto.
    intros. clear H3 H10 H11 a.
       lia.
   elim (expf_dec m0 (cA_1 m one txk) bxk).
    intros. clear H3 H10 H11 a.
       lia.
   intros.
     elim b.
     clear b.
     apply expf_trans with y.
    apply expf_symm.
       tauto.
   apply expf_trans with (cA_1 m one x).
    apply expf_symm.
       tauto.
   apply expf_symm.
      tauto.
   tauto.
  intro.
    inversion H3.
  tauto.
  tauto.
simpl in |- *.
  rewrite nf_B1 in |- *.
 fold txk in |- *.
   rewrite cA_B_ter in |- *.
  set (m1 := B m one x) in |- *.
    generalize (not_expf_expf_B1 m x H H0).
    simpl in |- *.
    fold m1 in |- *.
    fold txk in |- *.
    intro.
    assert (cF m1 (cA m zero bxk) = x).
   unfold m1 in |- *.
     rewrite cF_B in |- *.
    elim (eq_dim_dec one zero).
     intro.
       inversion a.
    rewrite cA_1_B_ter in |- *.
     rewrite cA_1_cA in |- *.
      elim (eq_dart_dec (A m one x) bxk).
       intros.
         symmetry  in a.
          absurd (bxk = A m one x).
        unfold bxk in |- *.
          apply succ_bottom.
          tauto.
         tauto.
        tauto.
      fold bxk in |- *.
        elim (eq_dart_dec bxk bxk).
        tauto.
       tauto.
      tauto.
     unfold bxk in |- *.
       generalize (exd_bottom m one x).
        tauto.
     tauto.
    intro.
      inversion H4.
    tauto.
    tauto.
  assert (expf m1 (cA m zero bxk) x).
   unfold expf in |- *.
     split.
    unfold m1 in |- *.
      apply inv_hmap_B;  tauto.
   unfold MF.expo in |- *.
     split.
    generalize (exd_cF m1 (cA m zero bxk)).
      rewrite H4 in |- *.
      assert (exd m1 x).
     unfold m1 in |- *.
       generalize (exd_B m one x x).
        tauto.
    assert (inv_hmap m1).
     unfold m1 in |- *.
       apply inv_hmap_B.
        tauto.
     tauto.
   split with 1%nat.
     simpl in |- *.
      tauto.
  elim (expf_dec m x txk).
   elim (expf_dec m1 txk (cA m zero bxk)).
    intros.
      assert (expf m1 x txk).
     apply expf_symm.
       apply expf_trans with (cA m zero bxk).
       tauto.
      tauto.
     tauto.
   intros. clear H3 H5 a.
      lia.
  elim (expf_dec m1 txk (cA m zero bxk)).
   intros. clear H3 H5 a.
      lia.
  intros.
    elim b.
    clear b.
    apply expf_symm.
    apply expf_trans with x.
    tauto.
   tauto.
  tauto.
 intro.
   inversion H3.
 tauto.
 tauto.
Qed.

(* RECALL:
expof_Shift
     : forall (m : fmap) (k : dim) (x z t : dart),
       inv_hmap m -> succ m k x -> 
    (expof (Shift m k x) z t <-> expof m z t)
*)

Lemma expf_Shift: 
  forall (m : fmap) (k : dim) (x z t : dart),
     inv_hmap m -> succ m k x ->
      (expf (Shift m k x) z t <-> expf m z t).
Proof.
unfold expf in |- *.
intros.
assert (inv_hmap (Shift m k x)).
 apply inv_hmap_Shift.
   tauto.
  tauto.
generalize (expof_Shift m k x z t H H0).
  unfold expof in |- *.
   tauto.
Qed.
 
(*====================================================
            Split: Splitting an edge, a vertex... 

=====================================================*)

(* OK: *)

Lemma planar_Split:forall(m:fmap)(k:dim)(x x':dart),
  inv_hmap m -> planar m -> x <> x' -> 
    (succ m k x \/ succ m k x') ->
       planar (Split m k x x').
Proof.
intros.
unfold Split in |- *.
fold (Shift m k x) in |- *.
elim (succ_dec m k x).
 elim (succ_dec m k x').
  intros.
    induction k.
   apply planar_B0.
    apply inv_hmap_Shift.
      tauto.
     tauto.
   unfold succ in |- *.
     rewrite A_Shift in |- *.
    elim (eq_dart_dec x x').
      tauto.
    elim (eq_dart_dec (top m zero x) x').
     intros.
       rewrite <- a1 in a.
        absurd (succ m zero (top m zero x)).
      apply not_succ_top.
         tauto.
      tauto.
    unfold succ in a.
       tauto.
    tauto.
    tauto.
   apply planar_Shift.
     tauto.
    tauto.
    tauto.
  apply planar_B1.
   apply inv_hmap_Shift.
     tauto.
    tauto.
  unfold succ in |- *.
    rewrite A_Shift in |- *.
   elim (eq_dart_dec x x').
     tauto.
   elim (eq_dart_dec (top m one x) x').
    intros.
      rewrite <- a1 in a.
       absurd (succ m one (top m one x)).
     apply not_succ_top.
        tauto.
     tauto.
   unfold succ in a.
      tauto.
   tauto.
   tauto.
  apply planar_Shift.
    tauto.
   tauto.
   tauto.
 intros.
   induction k.
  apply planar_B0.
    tauto.
   tauto.
   tauto.
 apply planar_B1.
   tauto.
  tauto.
  tauto.
intros.
  induction k.
 apply planar_B0.
   tauto.
  tauto.
  tauto.
apply planar_B1.
  tauto.
 tauto.
 tauto.
Qed.

(* OK!!: MAIS VOIR APRES:

Theorem planarity_crit_Split0_bis:
 forall(m:fmap)(x x':dart),
  inv_hmap m -> 
  cracke m x x' ->
   let y := cA m zero x in
   let y':= cA m zero x' in
   let m0 := Split m zero x x' in
  (planar m <->
 (planar m0 /\ (~eqc m0 x' y' \/ expf m0 y y'))).
Proof.
intros.
assert (cracke m x x').
  tauto.
rename H1 into Splitx.
  unfold cracke in Splitx.
  unfold MA0.crack in Splitx.
  elim Splitx.
  intros Dx Exx'.
  assert (exd m x).
 unfold MA0.MfcA.expo in Exx'.
    tauto.
assert (exd m x').
 generalize (MA0.MfcA.expo_exd m x x').
    tauto.
rename H1 into Ex.
  rename H2 into Ex'.
  clear Splitx.
  unfold m0 in |- *.
  unfold Split in |- *.
  elim (succ_dec m zero x).
 intro.
   elim (succ_dec m zero x').
  fold (Shift m zero x) in |- *.
    set (m1 := Shift m zero x) in |- *.
    intro.
    assert (inv_hmap m1).
   unfold m1 in |- *.
     apply inv_hmap_Shift.
     tauto.
    tauto.
  assert (succ m1 zero x').
   unfold m1 in |- *.
     unfold succ in |- *.
     rewrite A_Shift in |- *.
    elim (eq_dart_dec x x').
     unfold cracke in H0.
       unfold MA0.crack in H0.
        tauto.
    elim (eq_dart_dec (top m zero x) x').
     intros.
       rewrite <- a1 in a0.
        absurd (succ m zero (top m zero x)).
      apply not_succ_top.
         tauto.
      tauto.
    unfold succ in a0.
       tauto.
    tauto.
    tauto.
  generalize (planarity_crit_B0 m1 x' H1 H2).
    intro.
    assert (A m1 zero x' = y').
   unfold m1 in |- *.
     rewrite A_Shift in |- *.
    elim (eq_dart_dec x x').
     unfold cracke in H0.
       unfold MA0.crack in H0.
        tauto.
    elim (eq_dart_dec (top m zero x) x').
     intros.
       rewrite <- a1 in a0.
        absurd (succ m zero (top m zero x)).
      apply not_succ_top.
         tauto.
      tauto.
    unfold y' in |- *.
      rewrite cA_eq in |- *.
     elim (succ_dec m zero x');  tauto.
     tauto.
    tauto.
    tauto.
  assert (cA_1 m0 one x' = cA_1 m one x').
   unfold m0 in |- *.
     assert (one = dim_opp zero).
    simpl in |- *.
       tauto.
   rewrite H5 in |- *.
     rewrite MA0.cA_1_Split_opp in |- *.
     tauto.
    tauto.
  rewrite H4 in H3.
    assert (cF (B m1 zero x') y =
       cA_1 (B m1 zero x') one x').
   rewrite cF_B in |- *.
    elim (eq_dim_dec zero zero).
     elim (eq_dart_dec (A m1 zero x') y).
      intros.
        rewrite a1 in H4.
        assert (x = cA_1 m zero y).
       unfold y in |- *.
         rewrite cA_1_cA in |- *.
         tauto.
        tauto.
        tauto.
      rewrite H4 in H6.
        unfold y' in H6.
        rewrite cA_1_cA in H6.
        tauto.
       tauto.
       tauto.
     elim (eq_dart_dec (bottom m1 zero x') y).
       tauto.
     intros.
       elim b.
       unfold m1 in |- *.
       rewrite (bottom_Shift0 m x x' H) in |- *.
      elim (expe_dec m x x' H).
       unfold y in |- *.
         rewrite cA_eq in |- *.
        elim (succ_dec m zero x).
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
  unfold m0 in H3.
    rewrite <- H6 in H3.
    assert 
 (expf (B m1 zero x') y (cF (B m1 zero x') y)).
   unfold expf in |- *.
     split.
    apply inv_hmap_B.
       tauto.
   unfold MF.expo in |- *.
     split.
    generalize (exd_B m1 zero x' y).
      unfold m1 in |- *.
      generalize (exd_Shift m zero x y).
      assert (exd m y).
     unfold y in |- *.
       generalize (exd_cA m zero x).
        tauto.
     tauto.
   split with 1%nat.
     simpl in |- *.
      tauto.
  assert
   (expf (B m1 zero x') y y' <-> 
     expf (B m1 zero x') (cF (B m1 zero x') y) y').
   split.
    intro.
      apply expf_trans with y.
     apply expf_symm.
        tauto.
     tauto.
   intro.
     apply expf_trans with (cF (B m1 zero x') y).
     tauto.
    tauto.
  generalize (planarity_crit_Shift0 m x H a).
    fold m1 in |- *.
     tauto.
 intro.
   generalize (eqc_B m zero x x' y' H a).
   simpl in |- *.
   set (m1 := B m zero x) in |- *.
   assert (y = A m zero x).
  unfold y in |- *.
    rewrite cA_eq in |- *.
   elim (succ_dec m zero x).
     tauto.
    tauto.
   tauto.
 rewrite <- H1 in |- *.
   intro.
   generalize (planarity_crit_B0 m x H a).
   simpl in |- *.
   fold m1 in |- *.
   rewrite <- H1 in |- *.
   intros.
   assert (cA m1 zero x' = y).
  unfold m1 in |- *.
    rewrite cA_B in |- *.
   elim (eq_dart_dec x x').
     tauto.
   elim (eq_dart_dec (top m zero x) x').
    symmetry  in |- *.
       tauto.
   intros.
     elim b0.
     assert (top m zero x' = x').
    apply nosucc_top.
      tauto.
     tauto.
     tauto.
   rewrite <- H4 in |- *.
     apply expe_top.
     tauto.
    tauto.
   tauto.
   tauto.
 assert (eqc m1 x' y).
  rewrite <- H4 in |- *.
    apply eqc_cA_r.
   unfold m1 in |- *.
     apply inv_hmap_B.
      tauto.
  unfold m1 in |- *.
    generalize (exd_B m zero x x').
     tauto.
 assert (cA m1 zero x = y').
  unfold m1 in |- *.
    rewrite cA_B in |- *.
   elim (eq_dart_dec x x).
    intro.
      clear a0.
      assert (bottom m zero x' = y').
     generalize (cA_eq m zero x').
       elim (succ_dec m zero x').
       tauto.
     fold y' in |- *.
       symmetry  in |- *.
        tauto.
    rewrite <- H6 in |- *.
      apply expe_bottom.
      tauto.
     tauto.
    tauto.
   tauto.
   tauto.
 assert (eqc m1 x y').
  rewrite <- H6 in |- *.
    apply eqc_cA_r.
   unfold m1 in |- *.
     apply inv_hmap_B.
      tauto.
  unfold m1 in |- *.
    generalize (exd_B m zero x x).
     tauto.
 assert (eqc m1 x y <-> eqc m1 x' y').
  split.
   intro.
     apply eqc_trans with y.
     tauto.
   apply eqc_trans with x.
    apply eqc_symm.
       tauto.
    tauto.
  intro.
    apply eqc_trans with x'.
   apply eqc_trans with y'.
     tauto.
   apply eqc_symm.
      tauto.
   tauto.
 assert (cF m1 y' = cA_1 m1 one x).
  unfold m1 in |- *.
    rewrite cA_1_B_ter in |- *.
   rewrite cF_B in |- *.
    elim (eq_dim_dec zero zero).
     elim (eq_dart_dec (A m zero x) y').
      intros.
        assert (y = A m zero x).
       unfold y in |- *.
         rewrite cA_eq in |- *.
        elim (succ_dec m zero x).
          tauto.
         tauto.
        tauto.
      assert (x = cA_1 m zero y).
       unfold y in |- *.
         rewrite cA_1_cA in |- *.
         tauto.
        tauto.
        tauto.
      rewrite H9 in H10.
        rewrite a0 in H10.
        unfold y' in H10.
        rewrite cA_1_cA in H10.
        tauto.
       tauto.
       tauto.
     elim (eq_dart_dec (bottom m zero x) y').
      rewrite cA_1_B_ter in |- *.
        tauto.
       tauto.
      intro.
        inversion H9.
     intros.
       elim b0.
       assert (bottom m zero x' = y').
      generalize (cA_eq m zero x').
        elim (succ_dec m zero x').
        tauto.
      fold y' in |- *.
        symmetry  in |- *.
         tauto.
     rewrite <- H9 in |- *.
       apply expe_bottom.
       tauto.
      tauto.
     tauto.
    tauto.
    tauto.
   tauto.
  intro.
    inversion H9.
 rewrite <- H9 in H3.
   assert (expf m1 y' (cF m1 y')).
  unfold expf in |- *.
    split.
   unfold m1 in |- *.
     apply inv_hmap_B.
      tauto.
  unfold MF.expo in |- *.
    split.
   unfold m1 in |- *.
     generalize (exd_B m zero x y').
     assert (exd m y').
    unfold y' in |- *.
      generalize (exd_cA m zero x').
       tauto.
    tauto.
  split with 1%nat.
    simpl in |- *;  tauto.
 assert (expf m1 y y' <-> expf m1 (cF m1 y') y).
  split.
   intro.
     apply expf_trans with y'.
    apply expf_symm.
       tauto.
   apply expf_symm;  tauto; intro.
  intro.
    apply expf_trans with (cF m1 y').
   apply expf_symm.
      tauto.
  apply expf_symm;  tauto.
  tauto.
intro.
  assert (succ m zero x').
 generalize (MA0.crack_succ m x x').
    tauto.
generalize (planarity_crit_B0 m x' H H1).
  simpl in |- *.
  set (m1 := B m zero x') in |- *.
  assert (y' = A m zero x').
 unfold y' in |- *.
   rewrite cA_eq in |- *.
  elim (succ_dec m zero x').
    tauto.
   tauto.
  tauto.
rewrite <- H2 in |- *.
  intros.
  assert (cF m1 y = cA_1 m1 one x').
 unfold m1 in |- *.
   rewrite cA_1_B_ter in |- *.
  rewrite cF_B in |- *.
   elim (eq_dim_dec zero zero).
    elim (eq_dart_dec (A m zero x') y).
     intros.
       assert (x' = cA_1 m zero y').
      unfold y' in |- *.
        rewrite cA_1_cA in |- *.
        tauto.
       tauto.
       tauto.
     rewrite H2 in H4.
       rewrite a in H4.
       unfold y in H4.
       rewrite cA_1_cA in H4.
      symmetry  in H4.
         tauto.
      tauto.
      tauto.
    elim (eq_dart_dec (bottom m zero x') y).
     rewrite cA_1_B_ter in |- *.
       tauto.
      tauto.
     intro.
       inversion H4.
    intros.
      elim b0.
      assert (bottom m zero x = y).
     generalize (cA_eq m zero x).
       elim (succ_dec m zero x).
       tauto.
     fold y in |- *.
       symmetry  in |- *.
        tauto.
    rewrite <- H4 in |- *.
      apply expe_bottom.
      tauto.
    apply expe_symm.
      tauto.
     tauto.
    tauto.
   tauto.
   tauto.
  tauto.
 intro.
   inversion H4.
rewrite <- H4 in H3.
  assert (expf m1 y (cF m1 y)).
 unfold expf in |- *.
   split.
  unfold m1 in |- *.
    apply inv_hmap_B.
     tauto.
 unfold MF.expo in |- *.
   split.
  unfold m1 in |- *.
    generalize (exd_B m zero x' y).
    assert (exd m y).
   unfold y in |- *.
     generalize (exd_cA m zero x).
      tauto.
   tauto.
 split with 1%nat.
   simpl in |- *;  tauto.
assert (expf m1 y y' <-> expf m1 (cF m1 y) y').
 split.
  intro.
    apply expf_symm.
    apply expf_trans with y.
   apply expf_symm.
      tauto.
   tauto.
 intro.
   apply expf_trans with (cF m1 y).
   tauto.
  tauto.
 tauto.
Qed.
*)

(* OK : MIEUX... *)

Theorem planarity_crit_Split0:
 forall(m:fmap)(x x':dart),
  inv_hmap m -> 
  cracke m x x' ->
   let y := cA m zero x in
   let y':= cA m zero x' in
   let m0 := Split m zero x x' in
  (planar m <->
 (planar m0 /\ (~eqc m0 x x' \/ expf m0 y y'))).
Proof.
intros.
assert (cracke m x x').
  tauto.
rename H1 into Splitx.
  unfold cracke in Splitx.
  unfold MA0.crack in Splitx.
  elim Splitx.
  intros Dx Exx'.
  assert (exd m x).
 unfold MA0.MfcA.expo in Exx'.
    tauto.
assert (exd m x').
 generalize (MA0.MfcA.expo_exd m x x').
    tauto.
rename H1 into Ex.
  rename H2 into Ex'.
  clear Splitx.
  unfold m0 in |- *.
  unfold Split in |- *.
  elim (succ_dec m zero x).
 intro.
   elim (succ_dec m zero x').
  fold (Shift m zero x) in |- *.
    set (m1 := Shift m zero x) in |- *.
    intro.
    assert (inv_hmap m1).
   unfold m1 in |- *.
     apply inv_hmap_Shift.
     tauto.
    tauto.
  assert (succ m1 zero x').
   unfold m1 in |- *.
     unfold succ in |- *.
     rewrite A_Shift in |- *.
    elim (eq_dart_dec x x').
     unfold cracke in H0.
       unfold MA0.crack in H0.
        tauto.
    elim (eq_dart_dec (top m zero x) x').
     intros.
       rewrite <- a1 in a0.
        absurd (succ m zero (top m zero x)).
      apply not_succ_top.
         tauto.
      tauto.
    unfold succ in a0.
       tauto.
    tauto.
    tauto.
  generalize (planarity_crit_B0 m1 x' H1 H2).
    intro.
    unfold m0 in H3.
    assert (A m1 zero x' = y').
   unfold m1 in |- *.
     rewrite A_Shift in |- *.
    elim (eq_dart_dec x x').
     unfold cracke in H0.
       unfold MA0.crack in H0.
        tauto.
    elim (eq_dart_dec (top m zero x) x').
     intros.
       rewrite <- a1 in a0.
        absurd (succ m zero (top m zero x)).
      apply not_succ_top.
         tauto.
      tauto.
    unfold y' in |- *.
      rewrite cA_eq in |- *.
     elim (succ_dec m zero x');  tauto.
     tauto.
    tauto.
    tauto.
  rewrite H4 in H3.
    assert (cA_1 m0 one x' = cA_1 m one x').
   unfold m0 in |- *.
     assert (one = dim_opp zero).
    simpl in |- *.
       tauto.
   rewrite H5 in |- *.
     rewrite MA0.cA_1_Split_opp in |- *.
     tauto.
    tauto.
  assert (cF (B m1 zero x') y = 
   cA_1 (B m1 zero x') one x').
   rewrite cF_B in |- *.
    elim (eq_dim_dec zero zero).
     elim (eq_dart_dec (A m1 zero x') y).
      intros.
        rewrite a1 in H4.
        assert (x = cA_1 m zero y).
       unfold y in |- *.
         rewrite cA_1_cA in |- *.
         tauto.
        tauto.
        tauto.
      rewrite H4 in H6.
        unfold y' in H6.
        rewrite cA_1_cA in H6.
        tauto.
       tauto.
       tauto.
     elim (eq_dart_dec (bottom m1 zero x') y).
       tauto.
     intros.
       elim b.
       unfold m1 in |- *.
       rewrite (bottom_Shift0 m x x' H) in |- *.
      elim (expe_dec m x x' H).
       unfold y in |- *.
         rewrite cA_eq in |- *.
        elim (succ_dec m zero x).
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
  rewrite <- H6 in H3.
    assert (expf (B m1 zero x') 
    y (cF (B m1 zero x') y)).
   unfold expf in |- *.
     split.
    apply inv_hmap_B.
       tauto.
   unfold MF.expo in |- *.
     split.
    generalize (exd_B m1 zero x' y).
      unfold m1 in |- *.
      generalize (exd_Shift m zero x y).
      assert (exd m y).
     unfold y in |- *.
       generalize (exd_cA m zero x).
        tauto.
     tauto.
   split with 1%nat.
     simpl in |- *.
      tauto.
  assert
   (expf (B m1 zero x') y y' <-> 
  expf (B m1 zero x') (cF (B m1 zero x') y) y').
   split.
    intro.
      apply expf_trans with y.
     apply expf_symm.
        tauto.
     tauto.
   intro.
     apply expf_trans with (cF (B m1 zero x') y).
     tauto.
    tauto.
  generalize (planarity_crit_Shift0 m x H a).
    fold m1 in |- *.
    intro.
    assert (cA (B m1 zero x') zero x = y').
   unfold m1 in |- *.
     rewrite cA_B in |- *.
    elim (eq_dart_dec x' x).
     intro.
       symmetry  in a1.
        tauto.
    elim
  (eq_dart_dec (top (Shift m zero x) zero x') x).
     intros.
       rewrite A_Shift in |- *.
      elim (eq_dart_dec x x').
        tauto.
      elim (eq_dart_dec (top m zero x) x').
       intros.
         rewrite <- a2 in a0.
          absurd (succ m zero (top m zero x)).
        apply not_succ_top.
           tauto.
        tauto.
      unfold y' in |- *.
        rewrite cA_eq in |- *.
       elim (succ_dec m zero x').
         tauto.
        tauto.
       tauto.
      tauto.
      tauto.
    intros.
      rewrite (top_Shift0 m x x' H) in b.
     generalize b.
       elim (expe_dec m x x' H).
       tauto.
      tauto.
     tauto.
     tauto.
    intro.
      symmetry  in H10.
       tauto.
   apply inv_hmap_Shift.
     tauto.
    tauto.
   unfold succ in |- *.
     rewrite A_Shift in |- *.
    elim (eq_dart_dec x x').
      tauto.
    elim (eq_dart_dec (top m zero x) x').
     intros.
       rewrite <- a1 in a0.
        absurd (succ m zero (top m zero x)).
      apply not_succ_top.
         tauto.
      tauto.
    unfold succ in a0.
       tauto.
    tauto.
    tauto.
  assert (eqc (B m1 zero x') x y').
   rewrite <- H10 in |- *.
     apply eqc_cA_r.
    generalize (inv_hmap_B m1 zero x').
      unfold m1 in |- *.
      generalize (inv_hmap_Shift m zero x).
       tauto.
   generalize (exd_B m1 zero x' x).
     unfold m1 in |- *.
     generalize (exd_Shift m zero x x).
      tauto.
  assert (eqc (B m1 zero x') x x' <->
     eqc (B m1 zero x') x' y').
   split.
    intro.
      apply eqc_trans with x.
     apply eqc_symm.
        tauto.
     tauto.
   intro.
     apply eqc_trans with y'.
     tauto.
   apply eqc_symm.
      tauto.
   tauto.
 intro.
   assert (y = A m zero x).
  unfold y in |- *.
    rewrite cA_eq in |- *.
   elim (succ_dec m zero x).
     tauto.
    tauto.
   tauto.
 generalize (planarity_crit_B0 m x H a).
   simpl in |- *.
   set (m1 := B m zero x) in |- *.
   rewrite <- H1 in |- *.
   intros.
   assert (cA m1 zero x' = y).
  unfold m1 in |- *.
    rewrite cA_B in |- *.
   elim (eq_dart_dec x x').
     tauto.
   elim (eq_dart_dec (top m zero x) x').
    symmetry  in |- *.
       tauto.
   intros.
     elim b0.
     assert (top m zero x' = x').
    apply nosucc_top.
      tauto.
     tauto.
     tauto.
   rewrite <- H3 in |- *.
     apply expe_top.
     tauto.
    tauto.
   tauto.
   tauto.
 assert (eqc m1 x' y).
  rewrite <- H3 in |- *.
    apply eqc_cA_r.
   unfold m1 in |- *.
     apply inv_hmap_B.
      tauto.
  unfold m1 in |- *.
    generalize (exd_B m zero x x').
     tauto.
 assert (eqc m1 x y <-> eqc m1 x x').
  split.
   intro.
     apply eqc_trans with y.
     tauto.
   apply eqc_symm.
      tauto.
  intro.
    apply eqc_trans with x'.
    tauto.
   tauto.
 assert (cF m1 y' = cA_1 m1 one x).
  unfold m1 in |- *.
    rewrite cA_1_B_ter in |- *.
   rewrite cF_B in |- *.
    elim (eq_dim_dec zero zero).
     elim (eq_dart_dec (A m zero x) y').
      intros.
        assert (x = cA_1 m zero y).
       unfold y in |- *.
         rewrite cA_1_cA in |- *.
         tauto.
        tauto.
        tauto.
      rewrite H1 in H6.
        rewrite a0 in H6.
        unfold y' in |- *.
        unfold y' in H6.
        rewrite cA_1_cA in H6.
        tauto.
       tauto.
       tauto.
     elim (eq_dart_dec (bottom m zero x) y').
      rewrite cA_1_B_ter in |- *.
        tauto.
       tauto.
      intro.
        inversion H6.
     intros.
       elim b0.
       assert (bottom m zero x' = y').
      generalize (cA_eq m zero x').
        elim (succ_dec m zero x').
        tauto.
      fold y' in |- *.
        symmetry  in |- *.
         tauto.
     rewrite <- H6 in |- *.
       apply expe_bottom.
       tauto.
      tauto.
     tauto.
    tauto.
    tauto.
   tauto.
  intro.
    inversion H6.
 rewrite <- H6 in H2.
   assert (expf m1 y' (cF m1 y')).
  unfold expf in |- *.
    split.
   unfold m1 in |- *.
     apply inv_hmap_B.
      tauto.
  unfold MF.expo in |- *.
    split.
   unfold m1 in |- *.
     generalize (exd_B m zero x y').
     assert (exd m y').
    unfold y' in |- *.
      generalize (exd_cA m zero x').
       tauto.
    tauto.
  split with 1%nat.
    simpl in |- *;  tauto.
 assert (expf m1 y y' <-> expf m1 (cF m1 y') y).
  split.
   intro.
     apply expf_trans with y'.
    apply expf_symm.
       tauto.
   apply expf_symm;  tauto; intro.
  intro.
    apply expf_trans with (cF m1 y').
   apply expf_symm.
      tauto.
  apply expf_symm;  tauto.
  tauto.
intro.
  assert (succ m zero x').
 generalize (MA0.crack_succ m x x').
    tauto.
generalize (planarity_crit_B0 m x' H H1).
  simpl in |- *.
  set (m1 := B m zero x') in |- *.
  assert (y' = A m zero x').
 unfold y' in |- *.
   rewrite cA_eq in |- *.
  elim (succ_dec m zero x').
    tauto.
   tauto.
  tauto.
rewrite <- H2 in |- *.
  intros.
  assert (cF m1 y = cA_1 m1 one x').
 unfold m1 in |- *.
   rewrite cA_1_B_ter in |- *.
  rewrite cF_B in |- *.
   elim (eq_dim_dec zero zero).
    elim (eq_dart_dec (A m zero x') y).
     intros.
       assert (x' = cA_1 m zero y').
      unfold y' in |- *.
        rewrite cA_1_cA in |- *.
        tauto.
       tauto.
       tauto.
     rewrite H2 in H4.
       rewrite a in H4.
       unfold y in H4.
       rewrite cA_1_cA in H4.
      symmetry  in H4.
         tauto.
      tauto.
      tauto.
    elim (eq_dart_dec (bottom m zero x') y).
     rewrite cA_1_B_ter in |- *.
       tauto.
      tauto.
     intro.
       inversion H4.
    intros.
      elim b0.
      assert (bottom m zero x = y).
     generalize (cA_eq m zero x).
       elim (succ_dec m zero x).
       tauto.
     fold y in |- *.
       symmetry  in |- *.
        tauto.
    rewrite <- H4 in |- *.
      apply expe_bottom.
      tauto.
    apply expe_symm.
      tauto.
     tauto.
    tauto.
   tauto.
   tauto.
  tauto.
 intro.
   inversion H4.
rewrite <- H4 in H3.
  assert (expf m1 y (cF m1 y)).
 unfold expf in |- *.
   split.
  unfold m1 in |- *.
    apply inv_hmap_B.
     tauto.
 unfold MF.expo in |- *.
   split.
  unfold m1 in |- *.
    generalize (exd_B m zero x' y).
    assert (exd m y).
   unfold y in |- *.
     generalize (exd_cA m zero x).
      tauto.
   tauto.
 split with 1%nat.
   simpl in |- *;  tauto.
assert (expf m1 y y' <-> expf m1 (cF m1 y) y').
 split.
  intro.
    apply expf_symm.
    apply expf_trans with y.
   apply expf_symm.
      tauto.
   tauto.
 intro.
   apply expf_trans with (cF m1 y).
   tauto.
  tauto.
assert (cA m1 zero x = y').
 unfold m1 in |- *.
   rewrite cA_B in |- *.
  elim (eq_dart_dec x' x).
   intro.
     symmetry  in a.
      tauto.
  elim (eq_dart_dec (top m zero x') x).
   intro.
     symmetry  in |- *.
      tauto.
  intros.
    elim b0.
    assert (top m zero x = x).
   apply nosucc_top.
     tauto.
    tauto.
    tauto.
  rewrite <- H7 in |- *.
    symmetry  in |- *.
    apply expe_top.
    tauto.
   tauto.
  tauto.
  tauto.
assert (eqc m1 x y').
 rewrite <- H7 in |- *.
   apply eqc_cA_r.
  unfold m1 in |- *.
    apply inv_hmap_B.
     tauto.
 unfold m1 in |- *.
   generalize (exd_B m zero x' x).
    tauto.
assert (eqc m1 x' y' <-> eqc m1 x x').
 split.
  intro.
    apply eqc_trans with y'.
    tauto.
  apply eqc_symm.
     tauto.
 intro.
   apply eqc_trans with x.
  apply eqc_symm.
     tauto.
  tauto.
 tauto.
Qed.

(* OK!!: *)

Theorem planarity_crit_Split1:
 forall(m:fmap)(x x':dart),
  inv_hmap m -> 
  crackv m x x' ->
   let m0 := Split m one x x' in
  (planar m <->
 (planar m0 /\ (~eqc m0 x x' \/ expf m0 x x'))).
Proof.
intros.
assert (crackv m x x').
  tauto.
rename H1 into Splitx.
  unfold crackv in Splitx.
  unfold MA1.crack in Splitx.
  elim Splitx.
  intros Dx Exx'.
  assert (exd m x).
 unfold MA1.MfcA.expo in Exx'.
    tauto.
assert (exd m x').
 generalize (MA1.MfcA.expo_exd m x x').
    tauto.
rename H1 into Ex.
  rename H2 into Ex'.
  clear Splitx.
  unfold m0 in |- *.
  unfold Split in |- *.
  fold (Shift m one x) in |- *.
  set (m1 := Shift m one x) in |- *.
  elim (succ_dec m one x).
 intro.
   set (y := cA m one x) in |- *.
   assert (y = A m one x).
  unfold y in |- *.
    rewrite cA_eq in |- *.
   elim (succ_dec m one x).
     tauto.
    tauto.
   tauto.
 elim (succ_dec m one x').
  intro.
    set (y' := cA m one x') in |- *.
    assert (y' = A m one x').
   unfold y' in |- *.
     rewrite cA_eq in |- *.
    elim (succ_dec m one x').
      tauto.
     tauto.
    tauto.
  assert (inv_hmap m1).
   unfold m1 in |- *.
     apply inv_hmap_Shift.
     tauto.
    tauto.
  assert (succ m1 one x').
   unfold m1 in |- *.
     unfold succ in |- *.
     rewrite A_Shift in |- *.
    elim (eq_dart_dec x x').
     unfold cracke in H0.
        tauto.
    elim (eq_dart_dec (top m one x) x').
     intros.
       rewrite <- a1 in a0.
        absurd (succ m one (top m one x)).
      apply not_succ_top.
         tauto.
      tauto.
    unfold succ in a0.
       tauto.
    tauto.
    tauto.
  generalize (planarity_crit_B1 m1 x' H3 H4).
    intro.
    unfold y in H5.
    assert (top m1 one x' = x).
   unfold m1 in |- *.
     rewrite (top_Shift1 m x x' H a Ex' Dx) in |- *.
     elim (expv_dec m x x' H).
     tauto.
    tauto.
  rewrite H6 in H5.
    assert (expf (B m1 one x') x' x <-> 
     expf (B m1 one x') x x').
   split.
    apply expf_symm.
   apply expf_symm.
  assert (cA m1 one x' = y').
   unfold m1 in |- *.
     rewrite cA_Shift in |- *.
    fold y' in |- *.
       tauto.
    tauto.
    tauto.
  rewrite H8 in H5.
    assert (cA (B m1 one x') one x = y').
   rewrite cA_B in |- *.
    elim (eq_dart_dec x' x).
     intros.
       symmetry  in a1.
        tauto.
    elim (eq_dart_dec (top m1 one x') x).
     intros.
       generalize H8.
       rewrite cA_eq in |- *.
      elim (succ_dec m1 one x').
        tauto.
       tauto.
      tauto.
    intros.
       tauto.
    tauto.
    tauto.
  assert (eqc (B m1 one x') x y').
   rewrite <- H9 in |- *.
     apply eqc_cA_r.
    apply inv_hmap_B.
       tauto.
   generalize (exd_B m1 one x' x).
     generalize (exd_Shift m one x x).
     unfold m1 in |- *.
      tauto.
  assert (eqc (B m1 one x') x' y' <-> 
     eqc (B m1 one x') x x').
   split.
    intro.
      apply eqc_trans with y'.
      tauto.
    apply eqc_symm.
       tauto.
   intro.
     apply eqc_trans with x.
    apply eqc_symm.
       tauto.
    tauto.
  generalize (planarity_crit_Shift1 m x).
    fold m1 in |- *.
     tauto.
 intro.
   generalize (planarity_crit_B1 m x H a).
   simpl in |- *.
   set (m2 := B m one x) in |- *.
   fold y in |- *.
   intros.
   assert (top m one x = x').
  assert (top m one x' = x').
   apply nosucc_top.
     tauto.
    tauto.
    tauto.
  rewrite <- H3 in |- *.
    apply MA1.expo_top.
    tauto.
   tauto.
 rewrite H3 in H2.
   assert (cA m2 one x' = y).
  unfold m2 in |- *.
    rewrite cA_B in |- *.
   elim (eq_dart_dec x x').
     tauto.
   elim (eq_dart_dec (top m one x) x').
    rewrite <- H1 in |- *.
       tauto.
    tauto.
   tauto.
   tauto.
 assert (eqc m2 x' y).
  rewrite <- H4 in |- *.
    apply eqc_cA_r.
   unfold m2 in |- *.
     apply inv_hmap_B.
      tauto.
  unfold m2 in |- *.
    generalize (exd_B m one x x').
     tauto.
 assert (eqc m2 x y <-> eqc m2 x x').
  split.
   intro.
     apply eqc_trans with y.
     tauto.
   apply eqc_symm.
      tauto.
  intro.
    apply eqc_trans with x'.
    tauto.
   tauto.
  tauto.
intro.
  assert (succ m one x').
 generalize (MA1.crack_succ m x x').
    tauto.
generalize (planarity_crit_B1 m x' H H1).
  simpl in |- *.
  set (m2 := B m one x') in |- *.
  set (y' := cA m one x') in |- *.
  assert (y' = A m one x').
 unfold y' in |- *.
   rewrite cA_eq in |- *.
  elim (succ_dec m one x').
    tauto.
   tauto.
  tauto.
assert (top m one x' = x).
 assert (top m one x = x).
  apply nosucc_top.
    tauto.
   tauto.
   tauto.
 rewrite <- H3 in |- *.
   apply MA1.expo_top.
   tauto.
 apply expv_symm.
   tauto.
  tauto.
rewrite H3 in |- *.
  intro.
  assert (expf m2 x' x <-> expf m2 x x').
 split.
  apply expf_symm.
 apply expf_symm.
assert (cA m2 one x = y').
 unfold m2 in |- *.
   rewrite cA_B in |- *.
  elim (eq_dart_dec x' x).
   intro.
     symmetry  in a.
      tauto.
  elim (eq_dart_dec (top m one x') x).
   symmetry  in |- *.
      tauto.
   tauto.
  tauto.
  tauto.
assert (eqc m2 x y').
 rewrite <- H6 in |- *.
   apply eqc_cA_r.
  unfold m2 in |- *.
    apply inv_hmap_B.
     tauto.
 unfold m2 in |- *.
   generalize (exd_B m one x' x).
    tauto.
assert (eqc m2 x' y' <-> eqc m2 x x').
 split.
  intro.
    apply eqc_trans with y'.
    tauto.
  apply eqc_symm.
     tauto.
 intro.
   apply eqc_trans with x.
  apply eqc_symm.
     tauto.
  tauto.
 tauto.
Qed.

(* RECALLS ABOUT crack:

cracke = MA0.crack
crackv = MA1.crack

MA0.crack_comm

MA0.crack_succ
     : forall (m : fmap) (x x' : dart),
       inv_hmap m -> MA0.crack m x x' -> succ m Md0.kd x \/ succ m Md0.kd x'

MA0.crack_exd
     : forall (m : fmap) (x x' : dart),
       inv_hmap m -> MA0.crack m x x' -> exd m x /\ exd m x'

MA0.cA_Split
     : forall (m : fmap) (x x' z : dart),
       inv_hmap m ->
       MA0.crack m x x' ->
       cA (Split m Md0.kd x x') Md0.kd z =
       (if eq_dart_dec x z
        then cA m Md0.kd x'
        else if eq_dart_dec x' z then cA m Md0.kd x else cA m Md0.kd z)

MA0.cA_1_Split
     : forall (m : fmap) (x x' z : dart),
       inv_hmap m ->
       MA0.crack m x x' ->
       cA_1 (Split m Md0.kd x x') Md0.kd z =
       (if eq_dart_dec (cA m Md0.kd x) z
        then x'
        else if eq_dart_dec (cA m Md0.kd x') z then x else cA_1 m Md0.kd z)

MA0.cA_Split_opp
     : forall (m : fmap) (x x' z : dart),
       inv_hmap m ->
       cA (Split m Md0.kd x x') (dim_opp Md0.kd) z = cA m (dim_opp Md0.kd) z

MA0.cA_1_Split_opp
     : forall (m : fmap) (x x' z : dart),
       inv_hmap m ->
       cA_1 (Split m Md0.kd x x') (dim_opp Md0.kd) z = cA_1 m (dim_opp Md0.kd) z

IDEM DIM 1 AND crackv...
*)


(* IDEM, WITH cF, cF_1 / Split0, Split1:

cF_Split0
     : forall (m : fmap) (x x' z : dart),
       inv_hmap m ->
       cracke m x x' ->
       exd m z ->
       cF (Split m zero x x') z =
       (if eq_dart_dec (cA m zero x) z
        then cA_1 m one x'
        else if eq_dart_dec (cA m zero x') z then cA_1 m one x else cF m z)

cF_Split1
     : forall (m : fmap) (x x' z : dart),
       inv_hmap m ->
       crackv m x x' ->
       exd m z ->
       cF (Split m one x x') z =
       (if eq_dart_dec (cF_1 m x) z
        then x'
        else if eq_dart_dec (cF_1 m x') z then x else cF m z)

cF_1_Split0
     : forall (m : fmap) (x x' z : dart),
       inv_hmap m ->
       cracke m x x' ->
       exd m z ->
       cF_1 (Split m zero x x') z =
       (if eq_dart_dec (cA_1 m one x') z
        then cA m zero x
        else if eq_dart_dec (cA_1 m one x) z then cA m zero x' else cF_1 m z)

cF_1_Split1
     : forall (m : fmap) (x x' z : dart),
       inv_hmap m ->
       crackv m x x' ->
       exd m z ->
       cF_1 (Split m one x x') z =
       (if eq_dart_dec x' z
        then cF_1 m x
        else if eq_dart_dec x z then cF_1 m x' else cF_1 m z)
*)

(* PAS TRADUIT:
Lemma cF_1_Br1_bis:forall(m:fmap)(x x' z:dart),
 inv_hmap m -> double_link m x x' -> 
 cF_1 (Br1 m x x') z = 
  if eq_dart_dec (cA_1 m one x) z then cA m zero x'
  else if eq_dart_dec (cA_1 m one x') z 
       then cA m zero x 
       else cF_1 m z.
Proof.
intros.
unfold cF_1 in |- *.
rewrite cA1_Br1 in |- *.
 rewrite cA0_Br1 in |- *.
  generalize (double_link_exd m x x' H H0).
    intro Exx'.
    elim (exd_dec m z).
   intro.
     elim (eq_dart_dec x (cA m one z)).
    elim (eq_dart_dec (cA_1 m one x) z).
      tauto.
    intros.
      rewrite a0 in b.
      rewrite cA_1_cA in b.
      tauto.
     tauto.
     tauto.
   elim (eq_dart_dec x' (cA m one z)).
    elim (eq_dart_dec (cA_1 m one x) z).
     intros.
       rewrite <- a0 in b.
       rewrite cA_cA_1 in b.
       tauto.
      tauto.
      tauto.
    elim (eq_dart_dec (cA_1 m one x') z).
      tauto.
    intros.
      rewrite a0 in b.
      rewrite cA_1_cA in b.
      tauto.
     tauto.
     tauto.
   elim (eq_dart_dec (cA_1 m one x) z).
    intros.
      rewrite <- a0 in b0.
      rewrite cA_cA_1 in b0.
      tauto.
     tauto.
     tauto.
   elim (eq_dart_dec (cA_1 m one x') z).
    intros.
      rewrite <- a0 in b0.
      rewrite cA_cA_1 in b0.
      tauto.
     tauto.
     tauto.
    tauto.
  intro.
    assert (cA m one z = nil).
   apply not_exd_cA.
     tauto.
    tauto.
  rewrite H1 in |- *.
    elim (eq_dart_dec x nil).
   intro.
     rewrite a in Exx'.
      absurd (exd m nil).
    apply not_exd_nil.
       tauto.
    tauto.
  elim (eq_dart_dec x' nil).
   intro.
     rewrite a in Exx'.
      absurd (exd m nil).
    apply not_exd_nil.
       tauto.
    tauto.
  elim (eq_dart_dec (cA_1 m one x) z).
   intros.
     rewrite <- a in b.
      absurd (exd m (cA_1 m one x)).
     tauto.
   generalize (exd_cA_1 m one x).
      tauto.
  elim (eq_dart_dec (cA_1 m one x') z).
   intros.
     rewrite <- a in b.
      absurd (exd m (cA_1 m one x')).
     tauto.
   generalize (exd_cA_1 m one x').
      tauto.
   tauto.
  tauto.
  tauto.
 tauto.
Qed.
*)

(* OK: *)

Theorem disconnect_planar_criterion_Split0:
 forall (m:fmap)(x x':dart),
  inv_hmap m -> planar m -> expe m x x' -> x <> x' ->
    let y  := cA m zero x in
    let y' := cA m zero x' in
  (expf m y y' <-> ~eqc (Split m zero x x') x' y').
Proof.
intros.
rename H1 into DL.
rename H2 into Dx.
unfold Split in |- *.
elim (succ_dec m zero x).
 elim (succ_dec m zero x').
  intros.
    fold (Shift m zero x) in |- *.
    set (m0 := Shift m zero x) in |- *.
    assert (eqc m0 x' y' <-> eqc m x' y').
   unfold m0 in |- *.
     apply (eqc_Shift m zero x x' y' H a0).
  assert (inv_hmap m0).
   unfold m0 in |- *.
     apply inv_hmap_Shift.
     tauto.
    tauto.
  assert (succ m0 zero x').
   unfold succ in |- *.
     unfold m0 in |- *.
     rewrite A_Shift in |- *.
    elim (eq_dart_dec x x').
      tauto.
    elim (eq_dart_dec (top m zero x) x').
     intro.
       rewrite <- a1 in a.
        absurd (succ m zero (top m zero x)).
      apply not_succ_top.
         tauto.
      tauto.
    unfold succ in a.
       tauto.
    tauto.
    tauto.
  generalize (eqc_B m0 zero x' x' y' H2 H3).
    intros.
    assert (planar m0).
   unfold m0 in |- *.
     apply planar_Shift0.
     tauto.
    tauto.
    tauto.
  generalize 
 (disconnect_planar_criterion_B0 m0 x' H2 H5 H3).
    intros.
    generalize (expof_Shift m zero x y y' H a0).
    fold m0 in |- *.
    intro.
    assert (expf m0 y y' <-> expof m y y').
   generalize (expf_expof m0 y y').
     generalize (expf_expof m y y').
      tauto.
  rename H7 into Exp.
    rename H8 into H7.
    set (x0 := bottom m0 zero x') in |- *.
    assert (exd m x').
   apply succ_exd with zero.
     tauto.
    tauto.
  generalize (bottom_Shift0 m x x' H a0 H8 Dx).
    fold m0 in |- *.
    elim (expe_dec m x x' H).
   intros.
     assert (cA m zero x = A m zero x).
    rewrite cA_eq in |- *.
     elim (succ_dec m zero x).
       tauto.
      tauto.
     tauto.
   assert (A m0 zero x' = y').
    unfold m0 in |- *.
      rewrite A_Shift in |- *.
     elim (eq_dart_dec x x').
       tauto.
     elim (eq_dart_dec (top m zero x) x').
      intro.
        rewrite <- a2 in a.
         absurd (succ m zero (top m zero x)).
       apply not_succ_top.
          tauto.
       tauto.
     intros.
       unfold y' in |- *.
       rewrite cA_eq in |- *.
      elim (succ_dec m zero x').
        tauto.
       tauto.
      tauto.
     tauto.
     tauto.
   unfold y in H6.
     rewrite H11 in H6.
     assert (expf m y y' <-> expf m y' y).
    split.
     apply expf_symm.
    apply expf_symm.
   assert (expf m0 y y' <-> expf m0 y' y).
    split.
     apply expf_symm.
    apply expf_symm.
   rewrite H9 in H6.
     rewrite <- H10 in H6.
     fold y in H6.
     generalize (expf_expof m y y').
      tauto.
  unfold expe in DL.
     tauto.
 intros.
   assert (y' = bottom m zero x').
  unfold y' in |- *.
    rewrite cA_eq in |- *.
   elim (succ_dec m zero x').
     tauto.
    tauto.
   tauto.
 generalize (expe_bottom m x x' H DL).
   intro.
   rewrite <- H2 in H1.
   rewrite H1 in |- *.
   assert (top m zero x' = x').
  rewrite nosucc_top in |- *.
    tauto.
   tauto.
  unfold expe in DL.
    apply MA0.MfcA.expo_exd with x.
    tauto.
   tauto.
   tauto.
 generalize (expe_top m x x' H DL).
   intro.
   rewrite <- H3 in |- *.
   rewrite <- H4 in |- *.
   set (x0 := bottom m zero x) in |- *.
   set (h0 := top m zero x) in |- *.
   generalize (eqc_B_top m zero x H a).
   intro.
   assert (exd m x).
  apply succ_exd with zero.
    tauto.
   tauto.
 generalize (eqc_B_bottom m zero x H H6).
   intro.
   generalize
 (disconnect_planar_criterion_B0 m x H H0 a).
   simpl in |- *.
   intros.
   assert (y = A m zero x).
  unfold y in |- *.
    rewrite cA_eq in |- *.
   elim (succ_dec m zero x).
     tauto.
    tauto.
   tauto.
 rewrite <- H9 in H8.
   fold x0 in H7.
   fold x0 in H8.
   fold h0 in H5.
   rewrite <- H9 in H5.
   assert (~ eqc (B m zero x) h0 x0 <-> 
       ~ eqc (B m zero x) x y).
  split.
   intro.
     intro.
     apply H10.
     clear H10.
     apply eqc_trans with x.
    apply eqc_symm.
      apply eqc_trans with y.
      tauto.
     tauto.
    tauto.
  intro.
    intro.
    apply H10.
    clear H10.
    apply eqc_trans with x0.
    tauto.
  apply eqc_trans with h0.
   apply eqc_symm.
      tauto.
  apply eqc_symm.
     tauto.
  tauto.
intros.
  assert (y = bottom m zero x).
 unfold y in |- *.
   rewrite cA_eq in |- *.
  elim (succ_dec m zero x).
    tauto.
   tauto.
  tauto.
assert (y = bottom m zero x').
 rewrite H1 in |- *.
   apply expe_bottom.
   tauto.
 unfold expe in DL.
    tauto.
rewrite H2 in |- *.
  elim (succ_dec m zero x').
 intro.
   generalize
 (disconnect_planar_criterion_B0 m x' H H0 a).
   simpl in |- *.
   intro.
   assert
    (expf m (bottom m zero x') y' <->
     expf m (A m zero x') (bottom m zero x')).
  assert (y' = A m zero x').
   unfold y' in |- *.
     rewrite cA_eq in |- *.
    elim (succ_dec m zero x').
      tauto.
     tauto.
    tauto.
  rewrite <- H4 in |- *.
    split.
   apply expf_symm.
  apply expf_symm.
 assert (y' = A m zero x').
  unfold y' in |- *.
    rewrite cA_eq in |- *.
   elim (succ_dec m zero x').
     tauto.
    tauto.
   tauto.
 rewrite <- H5 in H4.
   rewrite <- H5 in H3.
    tauto.
intro.
  unfold expe in DL.
  assert (exd m x').
 apply MA0.MfcA.expo_exd with x.
   tauto.
  tauto.
assert (exd m x).
 unfold MA0.MfcA.expo in DL.
    tauto.
assert (top m zero x = x).
 apply nosucc_top.
   tauto.
  tauto.
  tauto.
assert (top m zero x' = x').
 apply nosucc_top.
   tauto.
  tauto.
  tauto.
elim Dx.
  rewrite <- H5 in |- *.
  rewrite <- H6 in |- *.
  apply expe_top.
  tauto.
unfold expe in |- *.
   tauto.
Qed.

(* DIM 1: OK! *)

Theorem disconnect_planar_criterion_Split1:
 forall (m:fmap)(x x':dart),
  inv_hmap m -> planar m -> expv m x x' -> x <> x' ->
    let y':= cA m one x' in 
  (expf m x x' <-> ~eqc (Split m one x x') x' y').
Proof.
intros.
rename H1 into DL.
rename H2 into Dx.
assert (exd m x).
 unfold expv in DL.
   unfold MA1.MfcA.expo in DL.
    tauto.
set (tx1 := top m one x) in |- *.
  set (tx'1 := top m one x') in |- *.
  assert (tx1 = tx'1).
 unfold tx1 in |- *; unfold tx'1 in |- *.
   apply expv_top.
   tauto.
  tauto.
set (y := cA m one x) in |- *.
  unfold Split in |- *.
  elim (succ_dec m one x).
 intro.
   fold (Shift m one x) in |- *.
   set (m1 := Shift m one x) in |- *.
   assert (inv_hmap m1).
  unfold m1 in |- *.
    apply inv_hmap_Shift.
    tauto.
   tauto.
 assert (cA m one x = A m one x).
  rewrite cA_eq in |- *.
   elim (succ_dec m one x).
     tauto.
    tauto.
   tauto.
 assert (tx1 <> x).
  intro.
    rewrite <- H5 in a.
     absurd (succ m one tx1).
   unfold tx1 in |- *.
     apply not_succ_top.
      tauto.
   tauto.
 elim (succ_dec m one x').
  intros.
    assert (eqc m1 x' y' <-> eqc m x' y').
   unfold m1 in |- *.
     apply (eqc_Shift m one x x' y' H a).
  assert (inv_hmap m1).
   unfold m1 in |- *.
     apply inv_hmap_Shift.
     tauto.
    tauto.
  assert (succ m1 one x').
   unfold succ in |- *.
     unfold m1 in |- *.
     rewrite A_Shift in |- *.
    fold tx1 in |- *.
      elim (eq_dart_dec x x').
      tauto.
    elim (eq_dart_dec tx1 x').
     intros.
       rewrite <- a1 in a0.
        absurd (succ m one tx1).
      unfold tx1 in |- *.
        apply not_succ_top.
         tauto.
      tauto.
    unfold succ in a0.
       tauto.
    tauto.
    tauto.
  generalize (eqc_B m1 one x' x' y' H3 H8).
    intros.
    assert (planar m1).
   unfold m1 in |- *.
     apply planar_Shift1.
     tauto.
    tauto.
    tauto.
  generalize 
 (disconnect_planar_criterion_B1 m1 x' H3 H10 H8).
    intros.
    assert (top m1 one x' = x).
   unfold m1 in |- *.
     rewrite (top_Shift1 m x x' H) in |- *.
    elim (expv_dec m x x' H).
      tauto.
    unfold expv in DL.
       tauto.
    tauto.
   apply succ_exd with one.
     tauto.
    tauto.
    tauto.
  rewrite H12 in H11.
    assert (A m1 one x' = y').
   unfold m1 in |- *.
     rewrite A_Shift in |- *.
    elim (eq_dart_dec x x').
      tauto.
    elim (eq_dart_dec (top m one x) x').
     intro.
       rewrite <- a1 in a0.
        absurd (succ m one (top m one x)).
      apply not_succ_top.
         tauto.
      tauto.
    unfold y' in |- *.
      rewrite cA_eq in |- *.
     elim (succ_dec m one x').
       tauto.
      tauto.
     tauto.
    tauto.
    tauto.
  rewrite H13 in H11.
    assert (expf m x x' <-> expf m x' x).
   split.
    apply expf_symm.
   apply expf_symm.
  cut (expf m x' x <-> ~ eqc (B m1 one x') x' y').
    tauto.
  generalize (expf_Shift m one x x' x H a).
    fold m1 in |- *.
    intro.
    cut (expf m1 x' x <-> ~ eqc (B m1 one x') x' y').
    tauto.
  apply H11.
 intros.
   assert (tx'1 = x').
  unfold tx'1 in |- *.
    apply nosucc_top.
    tauto.
  unfold expv in DL.
     eapply MA1.MfcA.expo_exd.
      tauto.
    apply DL.
     tauto.
   rewrite <- H2 in H6.
   generalize 
   (disconnect_planar_criterion_B1 m x H H0 a).
   simpl in |- *.
   fold tx1 in |- *.
   rewrite H6 in |- *.
   rewrite <- H4 in |- *.
   fold y in |- *.
   intros.
   generalize (eqc_B m one x x' y' H a).
   simpl in |- *.
   rewrite <- H4 in |- *.
   fold y in |- *.
   intro.
   assert (y' = bottom m one x').
  unfold y' in |- *.
    rewrite cA_eq in |- *.
   elim (succ_dec m one x').
     tauto.
    tauto.
   tauto.
 assert (eqc m x' y').
  rewrite H9 in |- *.
    apply eqc_bottom.
    tauto.
  unfold expv in DL.
     eapply MA1.MfcA.expo_exd.
      tauto.
    apply DL.
   assert
    (eqc (B m one x) x' y' \/
     eqc (B m one x) x' x /\ eqc (B m one x) y y' \/
     eqc (B m one x) x' y /\ eqc (B m one x) x y').
   tauto.
 clear H8.
   assert (eqc (B m one x) y tx1).
  unfold y in |- *.
    rewrite H4 in |- *.
    unfold tx1 in |- *.
    apply eqc_B_top.
    tauto.
   tauto.
 rewrite H6 in H8.
   set (bx1 := bottom m one x) in |- *.
   assert (bx1 = y').
  unfold bx1 in |- *.
    unfold y' in |- *.
    assert (bottom m one x = bottom m one x').
   apply expv_bottom.
     tauto.
    tauto.
  rewrite H12 in |- *.
    rewrite cA_eq in |- *.
   elim (succ_dec m one x').
     tauto.
    tauto.
   tauto.
 assert (eqc (B m one x) x y').
  rewrite <- H12 in |- *.
    unfold bx1 in |- *.
    apply eqc_B_bottom.
    tauto.
   tauto.
 split.
  intro.
    assert (~ eqc (B m one x) x y).
    tauto.
  intro.
    elim H15.
    apply eqc_trans with y'.
    tauto.
  apply eqc_trans with x'.
   apply eqc_symm.
      tauto.
  apply eqc_symm.
     tauto.
 intro.
   assert (~ eqc (B m one x) x y).
  intro.
    elim H14.
    apply eqc_trans with y.
   apply eqc_symm.
      tauto.
  apply eqc_trans with x.
   apply eqc_symm.
      tauto.
   tauto.
  tauto.
  intro.
  assert (succ m one x').
 generalize (MA1.crack_succ m x x').
   unfold expv in DL.
   unfold MA1.crack in |- *.
    tauto.
generalize 
  (disconnect_planar_criterion_B1 m x' H H0 H3).
  simpl in |- *.
  intro.
  assert (y' = A m one x').
 unfold y' in |- *.
   rewrite cA_eq in |- *.
  elim (succ_dec m one x');  tauto.
  tauto.
rewrite <- H5 in H4.
  assert (tx1 = x).
 unfold tx1 in |- *.
   apply nosucc_top.
   tauto.
  tauto.
  tauto.
rewrite H2 in H6.
  fold tx'1 in H4.
  rewrite H6 in H4.
  assert (expf m x x' <-> expf m x' x).
 split.
  apply expf_symm.
 apply expf_symm.
 tauto.
Qed.

(* OK: *)

Lemma Split0_comm: forall (m:fmap)(x x':dart),
  inv_hmap m -> cracke m x x' ->
     Split m zero x x' = Split m zero x' x.
Proof.
unfold cracke in |- *.
unfold MA0.crack.
intros.
unfold Split in |- *.
elim (succ_dec m zero x).
 elim (succ_dec m zero x').
  simpl in |- *.
    intros.
    elim (eq_dart_dec (top m zero x) x').
   intro.
     rewrite <- a1 in a.
      absurd (succ m zero (top m zero x)).
    apply not_succ_top.
       tauto.
    tauto.
  elim (eq_dart_dec (top m zero x') x).
   intro.
     rewrite <- a1 in a0;  
      absurd (succ m zero (top m zero x')).
    apply not_succ_top.
       tauto.
    tauto.
  intros.
    rewrite B_B in |- *.
    assert (top m zero x = top m zero x').
   apply expe_top.
     tauto.
   unfold expe in H0.
      tauto.
  assert (bottom m zero x = bottom m zero x').
   apply expe_bottom.
     tauto.
   unfold expe in H0.
      tauto.
  rewrite <- H1 in |- *.
    rewrite <- H2 in |- *.
     tauto.
  tauto.
intro.
  elim (succ_dec m zero x').
  tauto.
intro.
  assert (top m zero x = x).
 apply nosucc_top.
   tauto.
 unfold expe in |- *.
   unfold expe in H0.
   unfold MA0.MfcA.expo in H0.
    tauto.
  tauto.
assert (top m zero x' = x').
 apply nosucc_top.
   tauto.
 apply MA0.MfcA.expo_exd with x.
   tauto.
 unfold expe in H0.
    tauto.
  tauto.
assert (top m zero x = top m zero x').
 apply expe_top.
   tauto.
 unfold expe in H0.
    tauto.
rewrite H1 in H3.
  rewrite H2 in H3.
   tauto.
Qed.

(* THEN: *)

Lemma Split1_comm: forall (m:fmap)(x x':dart),
  inv_hmap m -> crackv m x x' ->
     Split m one x x' = Split m one x' x.
Proof.
unfold crackv in |- *.
unfold MA1.crack.
intros.
unfold Split in |- *.
elim (succ_dec m one x).
 elim (succ_dec m one x').
  simpl in |- *.
    intros.
    elim (eq_dart_dec (top m one x) x').
   intro.
     rewrite <- a1 in a.
      absurd (succ m one (top m one x)).
    apply not_succ_top.
       tauto.
    tauto.
  elim (eq_dart_dec (top m one x') x).
   intro.
     rewrite <- a1 in a0;  
      absurd (succ m one (top m one x')).
    apply not_succ_top.
       tauto.
    tauto.
  intros.
    rewrite B_B in |- *.
    assert (top m one x = top m one x').
   apply expv_top.
     tauto.
   unfold expv in H0.
      tauto.
  assert (bottom m one x = bottom m one x').
   apply expv_bottom.
     tauto.
   unfold expv in H0.
      tauto.
  rewrite <- H1 in |- *.
    rewrite <- H2 in |- *.
     tauto.
  tauto.
intro.
  elim (succ_dec m one x').
  tauto.
intro.
  assert (top m one x = x).
 apply nosucc_top.
   tauto.
 unfold expv in |- *.
   unfold expv in H0.
   unfold MA1.MfcA.expo in H0.
    tauto.
  tauto.
assert (top m one x' = x').
 apply nosucc_top.
   tauto.
 apply MA1.MfcA.expo_exd with x.
   tauto.
 unfold expv in H0.
    tauto.
  tauto.
assert (top m one x = top m one x').
 apply expv_top.
   tauto.
 unfold expv in H0.
    tauto.
rewrite H1 in H3.
  rewrite H2 in H3.
   tauto.
Qed.

(* THE "SYMMETRIC": *)

Theorem disconnect_planar_criterion_Split0_bis:
 forall (m:fmap)(x x':dart),
  inv_hmap m -> planar m -> cracke m x x' ->
    let y  := cA m zero x in
    let y' := cA m zero x' in
  (expf m y y' <-> ~eqc (Split m zero x x') x y).
Proof.
intros.
rewrite Split0_comm in |- *.
 generalize
 (disconnect_planar_criterion_Split0 m x' x H H0).
   generalize (MA0.crack_comm m x x' H).
   simpl in |- *.
   simpl in |- *.
   fold y in |- *.
   fold y' in |- *.
   intros.
   unfold cracke in H1.
   assert (expf m y' y <-> expf m y y').
  split.
   apply expf_symm.
  apply expf_symm.
 unfold expe in H3.
   unfold MA0.crack in H1.
   unfold MA0.crack in H2.
    tauto.
 tauto.
 tauto.
Qed.

(* THE "SYMMETRIC": *)

Theorem disconnect_planar_criterion_Split1_bis:
 forall (m:fmap)(x x':dart),
  inv_hmap m -> planar m -> crackv m x x' ->
   let y := cA m one x in
  (expf m x x' <-> ~eqc (Split m one x x') x y).
Proof.
intros.
rewrite Split1_comm in |- *.
 generalize
 (disconnect_planar_criterion_Split1 m x' x H H0).
   generalize (MA1.crack_comm m x x' H).
   simpl in |- *.
   simpl in |- *.
   fold y in |- *.
   intros.
   unfold crackv in H1.
   assert (expf m x' x <-> expf m x x').
  split.
   apply expf_symm.
  apply expf_symm.
 unfold expv in H3.
   unfold MA1.crack in H1.
   unfold MA1.crack in H2.
    tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Theorem planar_nc_Split0: forall (m:fmap)(x x':dart),
  inv_hmap m -> planar m -> cracke m x x' ->
    let y  := cA m zero x in
    let y' := cA m zero x' in
  nc (Split m zero x x') = nc m + 
     if expf_dec m y y' then 1 else 0.
Proof.
intros.
unfold Split in |- *.
elim (succ_dec m zero x).
 elim (succ_dec m zero x').
  intros.
    fold (Shift m zero x) in |- *.
    set (m0 := Shift m zero x) in |- *.
    assert (inv_hmap m0).
   unfold m0 in |- *.
     apply inv_hmap_Shift.
     tauto.
    tauto.
  assert (succ m0 zero x').
   unfold succ in |- *.
     unfold m0 in |- *.
     rewrite A_Shift in |- *.
    elim (eq_dart_dec x x').
     elim (eq_dart_dec (top m zero x) x').
      intros.
        rewrite <- a1 in a.
         absurd (succ m zero (top m zero x)).
       apply not_succ_top.
          tauto.
       tauto.
     unfold cracke in H1.
       unfold MA0.crack in H1.
        tauto.
    elim (eq_dart_dec (top m zero x) x').
     intros.
       rewrite <- a1 in a.
        absurd (succ m zero (top m zero x)).
      apply not_succ_top.
         tauto.
      tauto.
    unfold succ in a.
       tauto.
    tauto.
    tauto.
  assert (y = bottom m0 zero x').
   unfold m0 in |- *.
     unfold cracke in H1.
     unfold MA0.crack in H1.
     assert (x <> x').
     tauto.
   assert (exd m x').
    apply MA0.MfcA.expo_exd with x.
      tauto.
    unfold expe in H1.
       tauto.
   rewrite (bottom_Shift0 m x x' H a0 H5 H4) in |- *.
     elim (expe_dec m x x' H).
    unfold y in |- *.
      rewrite cA_eq in |- *.
     elim (succ_dec m zero x).
       tauto.
      tauto.
     tauto.
    tauto.
  assert (y' = A m0 zero x').
   unfold m0 in |- *.
     rewrite A_Shift in |- *.
    elim (eq_dart_dec x x').
     unfold cracke in H1; unfold MA0.crack in H1.
        tauto.
    elim (eq_dart_dec (top m zero x) x').
     intro.
       rewrite <- a1 in a.
        absurd (succ m zero (top m zero x)).
      apply not_succ_top.
         tauto.
      tauto.
    intros.
      unfold y' in |- *.
      rewrite cA_eq in |- *.
     elim (succ_dec m zero x').
       tauto.
      tauto.
     tauto.
    tauto.
    tauto.
  generalize (expf_Shift m zero x y y' H a0).
    fold m0 in |- *.
    intro.
    assert (nc m0 = nc m).
   unfold m0 in |- *.
     rewrite nc_Shift in |- *.
     tauto.
    tauto.
    tauto.
  rewrite nc_B in |- *.
   assert (planar m0).
    unfold m0 in |- *.
      apply planar_Shift0.
      tauto.
     tauto.
     tauto.
   generalize
 (disconnect_planar_criterion_B0 m0 x' H2 H8 H3).
     intro.
     rewrite <- H5 in H9.
     rewrite <- H4 in H9.
     assert (expf m0 y' y <-> 
      ~ eqc (B m0 zero x') x' y').
    apply H9.
   rewrite <- H5 in |- *.
     clear H9.
     rewrite <- H7 in |- *.
     elim (eqc_dec (B m0 zero x') x' y').
    elim (expf_dec m y y').
     intro.
       assert (expf m0 y' y).
      apply expf_symm.
         tauto.
      tauto.
     tauto.
   elim (expf_dec m y y').
    intro.
      assert (expf m0 y' y).
     apply expf_symm.
        tauto.
     tauto.
   intros.
     assert (expf m0 y y').
    apply expf_symm.
       tauto.
    tauto.
   tauto.
   tauto.
 intros.
   rewrite nc_B in |- *.
  unfold y' in |- *.
    assert (y = A m zero x).
   unfold y in |- *.
     rewrite cA_eq in |- *.
    elim (succ_dec m zero x).
      tauto.
     tauto.
    tauto.
  rewrite <- H2 in |- *.
    rewrite cA_eq in |- *.
   elim (succ_dec m zero x').
     tauto.
   intro.
     generalize
 (disconnect_planar_criterion_B0 m x H H0 a).
     simpl in |- *.
     rewrite <- H2 in |- *.
     intros.
     elim (eqc_dec (B m zero x) x y).
    elim (expf_dec m y (bottom m zero x')).
     intros.
       assert (bottom m zero x = bottom m zero x').
      apply expe_bottom.
        tauto.
      unfold cracke in H1.
        unfold MA0.crack in H1.
        unfold expe in |- *.
         tauto.
     rewrite <- H4 in a0.
        tauto.
     tauto.
   elim (expf_dec m y (bottom m zero x')).
     tauto.
   intros.
     assert (bottom m zero x = bottom m zero x').
    apply expe_bottom.
      tauto.
    unfold cracke in H1.
      unfold MA0.crack in H1.
      unfold expe in |- *.
       tauto.
   rewrite <- H4 in b1.
      tauto.
   tauto.
  tauto.
  tauto.
intro.
  assert (succ m zero x').
 generalize (MA0.crack_succ m x x').
   unfold cracke in H1.
    tauto.
rewrite nc_B in |- *.
 assert (y' = A m zero x').
  unfold y' in |- *.
    rewrite cA_eq in |- *.
   elim (succ_dec m zero x').
     tauto.
    tauto.
   tauto.
 rewrite <- H3 in |- *.
   assert (y = bottom m zero x').
  unfold y in |- *.
    rewrite cA_eq in |- *.
   elim (succ_dec m zero x).
     tauto.
   intro.
     apply expe_bottom.
     tauto.
   unfold cracke in H1.
     unfold MA0.crack in H1.
     unfold expe in |- *.
      tauto.
   tauto.
 rewrite H4 in |- *.
   generalize
 (disconnect_planar_criterion_B0 m x' H H0 H2).
   simpl in |- *.
   rewrite <- H3 in |- *.
   intros.
   elim (eqc_dec (B m zero x') x' y').
  elim (expf_dec m (bottom m zero x') y').
   intros.
     assert (expf m y' (bottom m zero x')).
    apply expf_symm.
       tauto.
    tauto.
   tauto.
 elim (expf_dec m (bottom m zero x') y').
   tauto.
 intros.
   elim b0.
   apply expf_symm.
    tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Theorem planar_nc_Split1: forall (m:fmap)(x x':dart),
  inv_hmap m -> planar m -> crackv m x x' ->
  nc (Split m one x x') = nc m + 
     if expf_dec m x x' then 1 else 0.
Proof.
intros.
unfold Split in |- *.
fold (Shift m one x) in |- *.
elim (succ_dec m one x).
 elim (succ_dec m one x').
  intros.
    set (m0 := Shift m one x) in |- *.
    assert (inv_hmap m0).
   unfold m0 in |- *.
     apply inv_hmap_Shift.
     tauto.
    tauto.
  assert (succ m0 one x').
   unfold succ in |- *.
     unfold m0 in |- *.
     rewrite A_Shift in |- *.
    elim (eq_dart_dec x x').
     elim (eq_dart_dec (top m one x) x').
      intros.
        rewrite <- a1 in a.
         absurd (succ m one (top m one x)).
       apply not_succ_top.
          tauto.
       tauto.
     unfold crackv in H1.
       unfold MA1.crack in H1.
        tauto.
    elim (eq_dart_dec (top m one x) x').
     intros.
       rewrite <- a1 in a.
        absurd (succ m one (top m one x)).
      apply not_succ_top.
         tauto.
      tauto.
    unfold succ in a.
       tauto.
    tauto.
    tauto.
  assert (exd m x').
   apply MA1.MfcA.expo_exd with x.
     tauto.
   unfold expv in H1.
     unfold crackv in H1.
     unfold MA1.crack in H1.
      tauto.
  assert (x <> x').
   unfold crackv in H1.
     unfold MA1.crack in H1.
      tauto.
  rewrite nc_B in |- *.
   set (y' := cA m one x') in |- *.
     assert (y' = A m0 one x').
    unfold m0 in |- *.
      rewrite A_Shift in |- *.
     elim (eq_dart_dec x x').
       tauto.
     elim (eq_dart_dec (top m one x) x').
      intro.
        rewrite <- a1 in a.
         absurd (succ m one (top m one x)).
       apply not_succ_top.
          tauto.
       tauto.
     intros.
       unfold y' in |- *.
       rewrite cA_eq in |- *.
      elim (succ_dec m one x').
        tauto.
       tauto.
      tauto.
     tauto.
     tauto.
   rewrite <- H6 in |- *.
     assert (nc m0 = nc m).
    unfold m0 in |- *.
      rewrite nc_Shift in |- *.
      tauto.
     tauto.
     tauto.
   assert (planar m0).
    unfold m0 in |- *.
      apply planar_Shift1.
      tauto.
     tauto.
     tauto.
   generalize 
   (disconnect_planar_criterion_B1 m0 x' H2 H8 H3).
     intro.
     rewrite <- H6 in H9.
     assert (x = top m0 one x').
    unfold m0 in |- *.
      rewrite (top_Shift1 m x x' H a0 H4 H5) in |- *.
      elim (expv_dec m x x' H).
      tauto.
    unfold crackv in H1.
      unfold MA1.crack in H1.
       tauto.
   rewrite <- H10 in H9.
     assert (expf m0 x' x <->
         ~ eqc (B m0 one x') x' y').
    apply H9.
   assert (expf m0 x' x <-> expf m0 x x').
    split.
     apply expf_symm.
    apply expf_symm.
   assert (expf m0 x x' <-> expf m x x').
    generalize (expf_Shift m one x x x').
      fold m0 in |- *.
       tauto.
   elim (eqc_dec (B m0 one x') x' y').
    elim (expf_dec m x x').
      tauto.
    intros.
      rewrite H7 in |- *.
       tauto.
   elim (expf_dec m x x').
    rewrite H7 in |- *.
      intros.
       tauto.
    tauto.
   tauto.
   tauto.
 intros.
   rewrite nc_B in |- *.
  set (y := cA m one x) in |- *.
    assert (y = A m one x).
   unfold y in |- *.
     rewrite cA_eq in |- *.
    elim (succ_dec m one x).
      tauto.
     tauto.
    tauto.
  rewrite <- H2 in |- *.
    generalize 
 (disconnect_planar_criterion_B1 m x H H0 a).
    simpl in |- *.
    rewrite <- H2 in |- *.
    intro.
    assert (x' = top m one x).
   assert (top m one x = top m one x').
    apply expv_top.
      tauto.
    unfold expv in |- *.
      unfold crackv in H1; unfold MA1.crack in H1.
       tauto.
   rewrite H4 in |- *.
     rewrite nosucc_top in |- *.
     tauto.
    tauto.
   unfold crackv in H1.
     generalize (MA1.crack_exd m x x').
      tauto.
    tauto.
  rewrite <- H4 in H3.
    elim (eqc_dec (B m one x) x y).
   elim (expf_dec m x x').
     tauto.
    tauto.
  elim (expf_dec m x x').
    tauto.
   tauto.
  tauto.
  tauto.
intro.
  assert (succ m one x').
 generalize (MA1.crack_succ m x x').
   unfold crackv in H1.
    tauto.
rewrite nc_B in |- *.
 set (y' := cA m one x') in |- *.
   assert (y' = A m one x').
  unfold y' in |- *.
    rewrite cA_eq in |- *.
   elim (succ_dec m one x').
     tauto.
    tauto.
   tauto.
 rewrite <- H3 in |- *.
   generalize 
(disconnect_planar_criterion_B1 m x' H H0 H2).
   simpl in |- *.
   rewrite <- H3 in |- *.
   assert (x = top m one x').
  assert (top m one x = top m one x').
   apply expv_top.
     tauto.
   unfold expv in |- *.
     unfold crackv in H1; unfold MA1.crack in H1.
      tauto.
  rewrite <- H4 in |- *.
    rewrite nosucc_top in |- *.
    tauto.
   tauto.
  unfold crackv in H1.
    unfold MA1.crack in H1.
    unfold MA1.MfcA.expo in H1.
     tauto.
   tauto.
 rewrite <- H4 in |- *.
   intro.
   assert (expf m x' x <-> expf m x x').
  split.
   apply expf_symm.
  apply expf_symm.
 elim (eqc_dec (B m one x') x' y').
  elim (expf_dec m x x').
    tauto.
   tauto.
 elim (expf_dec m x x').
   tauto.
  tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Theorem nf_Split0: forall (m:fmap)(x x':dart),
  inv_hmap m -> cracke m x x' ->
    let y  := cA m zero x in
    let y' := cA m zero x' in
  nf (Split m zero x x') = nf m + 
     if expf_dec m y y' then 1 else -1.
Proof.
intros.
unfold Split in |- *.
elim (succ_dec m zero x).
 elim (succ_dec m zero x').
  intros.
    fold (Shift m zero x) in |- *.
    rewrite nf_B0 in |- *.
   set (m0 := Shift m zero x) in |- *.
     assert (inv_hmap m0).
    unfold m0 in |- *.
      apply inv_hmap_Shift.
      tauto.
     tauto.
   assert (succ m0 zero x').
    unfold succ in |- *.
      unfold m0 in |- *.
      rewrite A_Shift in |- *.
     elim (eq_dart_dec x x').
      elim (eq_dart_dec (top m zero x) x').
       intros.
         rewrite <- a1 in a.
          absurd (succ m zero (top m zero x)).
        apply not_succ_top.
           tauto.
        tauto.
      unfold cracke in H0.
        unfold MA0.crack in H0.
         tauto.
     elim (eq_dart_dec (top m zero x) x').
      intros.
        rewrite <- a1 in a.
         absurd (succ m zero (top m zero x)).
       apply not_succ_top.
          tauto.
       tauto.
     unfold succ in a.
        tauto.
     tauto.
     tauto.
   assert (y = bottom m0 zero x').
    unfold m0 in |- *.
      unfold cracke in H0.
      unfold MA0.crack in H0.
      assert (x <> x').
      tauto.
    assert (exd m x').
     apply MA0.MfcA.expo_exd with x.
       tauto.
     unfold expe in H0.
        tauto.
    rewrite (bottom_Shift0 m x x' H a0 H4 H3) in |- *.
      elim (expe_dec m x x' H).
     unfold y in |- *.
       rewrite cA_eq in |- *.
      elim (succ_dec m zero x).
        tauto.
       tauto.
      tauto.
     tauto.
   assert (y' = A m0 zero x').
    unfold m0 in |- *.
      rewrite A_Shift in |- *.
     elim (eq_dart_dec x x').
      unfold cracke in H0; unfold MA0.crack in H0.
         tauto.
     elim (eq_dart_dec (top m zero x) x').
      intro.
        rewrite <- a1 in a.
         absurd (succ m zero (top m zero x)).
       apply not_succ_top.
          tauto.
       tauto.
     intros.
       unfold y' in |- *.
       rewrite cA_eq in |- *.
      elim (succ_dec m zero x').
        tauto.
       tauto.
      tauto.
     tauto.
     tauto.
   rewrite <- H3 in |- *.
     rewrite <- H4 in |- *.
     assert (expf m0 y' y <-> expf m y' y).
    unfold m0 in |- *.
      apply expf_Shift.
      tauto.
     tauto.
   assert (expf m y' y <-> expf m y y').
    split.
     apply expf_symm.
    apply expf_symm.
   unfold m0 in |- *.
     rewrite nf_Shift in |- *.
    fold m0 in |- *.
      elim (expf_dec m0 y' y).
     elim (expf_dec m y y').
       tauto.
      tauto.
    elim (expf_dec m y y').
      tauto.
     tauto.
    tauto.
    tauto.
  apply inv_hmap_Shift.
    tauto.
   tauto.
  unfold succ in |- *.
    rewrite A_Shift in |- *.
   elim (eq_dart_dec x x').
    elim (eq_dart_dec (top m zero x) x').
     intros.
       rewrite <- a1 in a.
        absurd (succ m zero (top m zero x)).
      apply not_succ_top.
         tauto.
      tauto.
    unfold cracke in H0.
      unfold MA0.crack in H0.
       tauto.
   elim (eq_dart_dec (top m zero x) x').
    intros.
      rewrite <- a1 in a.
       absurd (succ m zero (top m zero x)).
     apply not_succ_top.
        tauto.
     tauto.
   unfold succ in a.
      tauto.
   tauto.
   tauto.
 intros.
   rewrite nf_B0 in |- *.
  assert (y = A m zero x).
   unfold y in |- *.
     rewrite cA_eq in |- *.
    elim (succ_dec m zero x).
      tauto.
     tauto.
    tauto.
  rewrite <- H1 in |- *.
    assert (bottom m zero x = bottom m zero x').
   apply expe_bottom.
     tauto.
   unfold cracke in H0.
     unfold MA0.crack in H0.
     unfold expe in |- *.
      tauto.
  rewrite H2 in |- *.
    assert (y' = bottom m zero x').
   unfold y' in |- *.
     rewrite cA_eq in |- *.
    elim (succ_dec m zero x').
      tauto.
     tauto.
    tauto.
  rewrite <- H3 in |- *.
     tauto.
  tauto.
  tauto.
intro.
  assert (succ m zero x').
 generalize (MA0.crack_succ m x x').
   unfold cracke in H0.
    tauto.
rewrite nf_B0 in |- *.
 assert (y' = A m zero x').
  unfold y' in |- *.
    rewrite cA_eq in |- *.
   elim (succ_dec m zero x').
     tauto.
    tauto.
   tauto.
 rewrite <- H2 in |- *.
   assert (y = bottom m zero x').
  unfold y in |- *.
    rewrite cA_eq in |- *.
   elim (succ_dec m zero x).
     tauto.
   intro.
     apply expe_bottom.
     tauto.
   unfold cracke in H0.
     unfold MA0.crack in H0.
     unfold expe in |- *.
      tauto.
   tauto.
 rewrite <- H3 in |- *.
   assert (expf m y y' <-> expf m y' y).
  split.
   apply expf_symm.
  apply expf_symm.
 elim (expf_dec m y' y).
  elim (expf_dec m y y').
    tauto.
   tauto.
 elim (expf_dec m y y').
   tauto.
  tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Theorem nf_Split1: forall (m:fmap)(x x':dart),
  inv_hmap m -> crackv m x x' ->
  nf (Split m one x x') = nf m + 
     if expf_dec m x x' then 1 else -1.
Proof.
intros.
unfold Split in |- *.
fold (Shift m one x) in |- *.
elim (succ_dec m one x).
 elim (succ_dec m one x').
  intros.
    set (m0 := Shift m one x) in |- *.
    assert (inv_hmap m0).
   unfold m0 in |- *.
     apply inv_hmap_Shift.
     tauto.
    tauto.
  assert (succ m0 one x').
   unfold succ in |- *.
     unfold m0 in |- *.
     rewrite A_Shift in |- *.
    elim (eq_dart_dec x x').
     elim (eq_dart_dec (top m one x) x').
      intros.
        rewrite <- a1 in a.
         absurd (succ m one (top m one x)).
       apply not_succ_top.
          tauto.
       tauto.
     unfold crackv in H0.
       unfold MA1.crack in H0.
        tauto.
    elim (eq_dart_dec (top m one x) x').
     intros.
       rewrite <- a1 in a.
        absurd (succ m one (top m one x)).
      apply not_succ_top.
         tauto.
      tauto.
    unfold succ in a.
       tauto.
    tauto.
    tauto.
  assert (exd m x').
   apply MA1.MfcA.expo_exd with x.
     tauto.
   unfold expv in H0.
     unfold crackv in H0.
     unfold MA1.crack in H0.
      tauto.
  assert (x <> x').
   unfold crackv in H0.
     unfold MA1.crack in H0.
      tauto.
  rewrite nf_B1 in |- *.
   assert (top m0 one x' = x).
    unfold m0 in |- *.
      rewrite (top_Shift1 m x x' H) in |- *.
     elim (expv_dec m x x' H).
       tauto.
     unfold crackv in H0.
       unfold MA1.crack in H0.
        tauto.
     tauto.
     tauto.
     tauto.
   rewrite H5 in |- *.
     assert (expf m x x' <-> expf m x' x).
    split.
     apply expf_symm.
    apply expf_symm.
   unfold m0 in |- *.
     rewrite nf_Shift in |- *.
    fold m0 in |- *;
   assert (expf m0 x' x <-> expf m x' x).
     unfold m0 in |- *.
       apply expf_Shift.
       tauto.
      tauto.
    elim (expf_dec m0 x' x).
     elim (expf_dec m x x').
       tauto.
      tauto.
    elim (expf_dec m x x').
      tauto.
     tauto.
    tauto.
    tauto.
  unfold m0 in |- *.
    apply inv_hmap_Shift.
    tauto.
   tauto.
  unfold succ in |- *.
    unfold m0 in |- *.
    rewrite A_Shift in |- *.
   elim (eq_dart_dec x x').
    elim (eq_dart_dec (top m one x) x').
     intros.
       rewrite <- a1 in a.
        absurd (succ m one (top m one x)).
      apply not_succ_top.
         tauto.
      tauto.
    unfold crackv in H0.
      unfold MA1.crack in H0.
       tauto.
   elim (eq_dart_dec (top m one x) x').
    intros.
      rewrite <- a1 in a.
       absurd (succ m one (top m one x)).
     apply not_succ_top.
        tauto.
     tauto.
   unfold succ in a.
      tauto.
   tauto.
   tauto.
 intros.
   rewrite nf_B1 in |- *.
  assert (x' = top m one x).
   assert (top m one x = top m one x').
    apply expv_top.
      tauto.
    unfold expv in |- *.
      unfold crackv in H0; unfold MA1.crack in H0.
       tauto.
   rewrite H1 in |- *.
     rewrite nosucc_top in |- *.
     tauto.
    tauto.
   unfold crackv in H0.
     generalize (MA1.crack_exd m x x').
      tauto.
    tauto.
  rewrite <- H1 in |- *.
     tauto.
  tauto.
  tauto.
intro.
  assert (succ m one x').
 generalize (MA1.crack_succ m x x').
   unfold crackv in H0.
    tauto.
rewrite nf_B1 in |- *.
 assert (x = top m one x').
  assert (top m one x = top m one x').
   apply expv_top.
     tauto.
   unfold expv in |- *.
     unfold crackv in H0; unfold MA1.crack in H0.
      tauto.
  rewrite <- H2 in |- *.
    rewrite nosucc_top in |- *.
    tauto.
   tauto.
  unfold crackv in H0.
    unfold MA1.crack in H0.
    unfold MA1.MfcA.expo in H0.
     tauto.
   tauto.
 rewrite <- H2 in |- *.
   assert (expf m x' x <-> expf m x x').
  split.
   apply expf_symm.
  apply expf_symm.
 elim (expf_dec m x' x).
  elim (expf_dec m x x').
    tauto.
   tauto.
 elim (expf_dec m x x').
   tauto.
  tauto.
 tauto.
 tauto.
Qed.

(*====================================================
        ne, nv, expe, expv, expf ... / Shift, Split
=====================================================*)

(* OK: *)

Theorem ne_Shift0:
  forall (m : fmap)(x : dart),
  inv_hmap m -> succ m zero x ->
   ne (Shift m zero x) = ne m.
Proof.
intros.
assert (exd m x).
 apply succ_exd with zero.
   tauto.
  tauto.
unfold Shift in |- *.
  simpl in |- *.
  rewrite ne_B in |- *.
 elim (eq_dim_dec zero zero).
intro.
     lia.
  tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Theorem ne_Shift1:
  forall (m : fmap)(x : dart),
  inv_hmap m -> succ m one x ->
   ne (Shift m one x) = ne m.
Proof.
intros.
unfold Shift in |- *.
simpl in |- *.
rewrite ne_B in |- *.
 elim (eq_dim_dec one zero).
  intro.
    inversion a.
 intro.
    lia.
 tauto.
 tauto.
Qed.

(* OK *)

Theorem nv_Shift1:
  forall (m : fmap)(x : dart),
  inv_hmap m -> succ m one x ->
   nv (Shift m one x) = nv m.
Proof.
intros.
assert (exd m x).
 apply succ_exd with one.
   tauto.
  tauto.
unfold Shift in |- *.
  simpl in |- *.
  rewrite nv_B in |- *.
 elim (eq_dim_dec one one).
intro.
     lia.
  tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Theorem nv_Shift0:
  forall (m : fmap)(x : dart),
  inv_hmap m -> succ m zero x ->
   nv (Shift m zero x) = nv m.
Proof.
intros.
unfold Shift in |- *.
simpl in |- *.
rewrite nv_B in |- *.
 elim (eq_dim_dec zero one).
  intro.
    inversion a.
 intro.
    lia.
 tauto.
 tauto.
Qed.

(* OK : *)

Theorem ne_Split0:
  forall (m : fmap)(x x' : dart),
  inv_hmap m -> cracke m x x' ->
   ne (Split m zero x x') = ne m + 1.
Proof.
unfold Split in |- *.
intros.
fold (Shift m zero x) in |- *.
elim (succ_dec m zero x).
 elim (succ_dec m zero x').
  intros.
    rewrite ne_B in |- *.
   rewrite ne_Shift0 in |- *.
    elim (eq_dim_dec zero zero).
      tauto.
     tauto.
    tauto.
    tauto.
  apply inv_hmap_Shift.
    tauto.
   tauto.
  unfold succ in |- *.
    rewrite A_Shift in |- *.
   elim (eq_dart_dec x x').
    unfold cracke in H0.
      unfold MA0.crack in H0.
       tauto.
   elim (eq_dart_dec (top m zero x) x').
    intro.
      rewrite <- a1 in a.
       absurd (succ m zero (top m zero x)).
     apply not_succ_top.
        tauto.
     tauto.
   unfold succ in a.
      tauto.
   tauto.
   tauto.
 intros.
   rewrite ne_B in |- *.
  elim (eq_dim_dec zero zero).
    tauto.
   tauto.
  tauto.
  tauto.
intro.
  assert (succ m zero x').
 generalize (MA0.crack_succ m x x').
   unfold cracke in H0.
    tauto.
rewrite ne_B in |- *.
 elim (eq_dim_dec zero zero).
   tauto.
  tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Theorem ne_Split1:
  forall (m : fmap)(x x' : dart),
  inv_hmap m -> crackv m x x' ->
   ne (Split m one x x') = ne m.
Proof.
intros.
unfold Split in |- *.
elim (succ_dec m one x).
 elim (succ_dec m one x').
  intros.
    rewrite ne_B in |- *.
   elim (eq_dim_dec one zero).
    intro.
      inversion a1.
   intro.
     clear b.
     simpl in |- *.
     rewrite ne_B in |- *.
    elim (eq_dim_dec one zero).
     intro.
       inversion a1.
    intro.
       lia.
    tauto.
    tauto.
  fold (Shift m one x) in |- *.
    apply inv_hmap_Shift.
    tauto.
   tauto.
  fold (Shift m one x) in |- *.
    unfold succ in |- *.
    rewrite A_Shift in |- *.
   elim (eq_dart_dec x x').
    unfold crackv in H0.
      unfold MA1.crack in H0.
       tauto.
   elim (eq_dart_dec (top m one x) x').
    intro.
      rewrite <- a1 in a.
       absurd (succ m one (top m one x)).
     apply not_succ_top.
        tauto.
     tauto.
   unfold succ in a.
      tauto.
   tauto.
   tauto.
 intros.
   rewrite ne_B in |- *.
  elim (eq_dim_dec one zero).
   intro.
     intros.
     inversion a0.
  intro.
     lia.
  tauto.
  tauto.
intro.
  assert (succ m one x').
 generalize (MA1.crack_succ m x x').
   unfold crackv in H0.
    tauto.
rewrite ne_B in |- *.
 elim (eq_dim_dec one zero).
  intro.
    inversion a.
 intro.
    lia.
 tauto.
 tauto.
Qed.

(* OK: *)

Theorem nv_Split1:
  forall (m : fmap)(x x' : dart),
  inv_hmap m -> crackv m x x' ->
   nv (Split m one x x') = nv m + 1.
Proof.
unfold Split in |- *.
intros.
fold (Shift m one x) in |- *.
elim (succ_dec m one x).
 elim (succ_dec m one x').
  intros.
    rewrite nv_B in |- *.
   rewrite nv_Shift1 in |- *.
    elim (eq_dim_dec one one).
      tauto.
     tauto.
    tauto.
    tauto.
  apply inv_hmap_Shift.
    tauto.
   tauto.
  unfold succ in |- *.
    rewrite A_Shift in |- *.
   elim (eq_dart_dec x x').
    unfold crackv in H0.
      unfold MA1.crack in H0.
       tauto.
   elim (eq_dart_dec (top m one x) x').
    intro.
      rewrite <- a1 in a.
       absurd (succ m one (top m one x)).
     apply not_succ_top.
        tauto.
     tauto.
   unfold succ in a.
      tauto.
   tauto.
   tauto.
 intros.
   rewrite nv_B in |- *.
  elim (eq_dim_dec one one).
    tauto.
   tauto.
  tauto.
  tauto.
intro.
  assert (succ m one x').
 generalize (MA1.crack_succ m x x').
   unfold crackv in H0.
    tauto.
rewrite nv_B in |- *.
 elim (eq_dim_dec one one).
   tauto.
  tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Theorem nv_Split0:
  forall (m : fmap)(x x' : dart),
  inv_hmap m -> cracke m x x' ->
   nv (Split m zero x x') = nv m.
Proof.
intros.
unfold Split in |- *.
elim (succ_dec m zero x).
 elim (succ_dec m zero x').
  intros.
    rewrite nv_B in |- *.
   elim (eq_dim_dec zero one).
    intro.
      inversion a1.
   intro.
     clear b.
     simpl in |- *.

     rewrite nv_B in |- *.
    elim (eq_dim_dec zero one).
     intro.
       inversion a1.
    intro.
       lia.
    tauto.
    tauto.
  fold (Shift m zero x) in |- *.
    apply inv_hmap_Shift.
    tauto.
   tauto.
  fold (Shift m zero x) in |- *.
    unfold succ in |- *.
    rewrite A_Shift in |- *.
   elim (eq_dart_dec x x').
    unfold cracke in H0.
      unfold MA0.crack in H0.
       tauto.
   elim (eq_dart_dec (top m zero x) x').
    intro.
      rewrite <- a1 in a.
       absurd (succ m zero (top m zero x)).
     apply not_succ_top.
        tauto.
     tauto.
   unfold succ in a.
      tauto.
   tauto.
   tauto.
 intros.
   rewrite nv_B in |- *.
  elim (eq_dim_dec zero one).
   intro.
     intros.
     inversion a0.
  intro.
     lia.
  tauto.
  tauto.
intro.
  assert (succ m zero x').
 generalize (MA0.crack_succ m x x').
   unfold cracke in H0.
    tauto.
rewrite nv_B in |- *.
 elim (eq_dim_dec zero one).
  intro.
    inversion a.
 intro.
    lia.
 tauto.
 tauto.
Qed.

(* OK: "GENERALISATION DE D13 POUR D11": *)

Lemma not_succ_Split_fst:forall(m:fmap)(k:dim)(x x':dart),
  inv_hmap m -> ~succ (Split m k x x') k x.
Proof.
unfold Split in |- *.
intros.
elim (succ_dec m k x).
 elim (succ_dec m k x').
  intros.
    unfold succ in |- *.
    simpl in |- *.
    elim (eq_dim_dec k k).
   intro.
     clear a1.
     elim (eq_dart_dec (top m k x) x').
    intro.
      rewrite <- a1 in a.
       absurd (succ m k (top m k x)).
     apply not_succ_top.
        tauto.
     tauto.
   simpl in |- *.
     elim (eq_dim_dec k k).
    intro.
      clear a1.
      elim (eq_dart_dec (top m k x) x).
     intros.
       rewrite <- a1 in a0.
        absurd (succ m k (top m k x)).
      apply not_succ_top.
         tauto.
      tauto.
    intros.
      elim (eq_dart_dec x x').
     intro.
       rewrite <- a1 in |- *.
       rewrite A_B in |- *.
       tauto.
     apply inv_hmap_B.
        tauto.
    intro.
      rewrite A_B_bis in |- *.
     rewrite A_B in |- *.
       tauto.
      tauto.
     tauto.
   unfold succ in |- *.
      tauto.
   tauto.
 unfold succ in |- *.
   intros.
   elim (eq_dart_dec x x').
  intro.
    rewrite A_B in |- *.
    tauto.
   tauto.
 intro.
   rewrite A_B in |- *.
   tauto.
  tauto.
intro.
  elim (eq_dart_dec x x').
 intros.
   rewrite <- a in |- *.
   unfold succ in |- *.
   rewrite A_B in |- *.
   tauto.
  tauto.
intro.
  unfold succ in |- *.
  rewrite A_B_bis in |- *.
 unfold succ in b.
    tauto.
 tauto.
Qed.

(* OK: *)

Lemma not_succ_Split_snd:forall(m:fmap)(k:dim)(x x':dart),
  inv_hmap m -> ~succ (Split m k x x') k x'.
Proof.
intros.
unfold Split.
elim (succ_dec m k x).
 elim (succ_dec m k x').
  intros.
    unfold succ in |- *.
    simpl in |- *.
    elim (eq_dim_dec k k).
   intro.
     clear a1.
     elim (eq_dart_dec (top m k x) x').
    intro.
      rewrite <- a1 in a.
       absurd (succ m k (top m k x)).
     apply not_succ_top.
        tauto.
     tauto.
   intro.
     simpl in |- *.
     elim (eq_dim_dec k k).
    intro.
      clear a1.
      elim (eq_dart_dec (top m k x) x').
      tauto.
    intro.
      rewrite A_B in |- *.
      tauto.
    apply inv_hmap_B.
       tauto.
    tauto.
   tauto.
 unfold succ in |- *.
   elim (eq_dart_dec x x').
  intros.
    rewrite <- a in |- *.
    rewrite A_B in |- *.
    tauto.
   tauto.
 intros.
   rewrite A_B_bis in |- *.
   tauto.
 intro.
   symmetry  in H0.
    tauto.
unfold succ in |- *.
  rewrite A_B in |- *.
  tauto.
 tauto.
Qed.

(* OK: "GENERALISATION DE D13 POUR D11":*)

Lemma expf_expf_B0:forall (m:fmap)(x z t:dart),
 inv_hmap m -> succ m zero x -> 
   let y := A m zero x in
   let x0 := bottom m zero x in
   ~expf m y x0 ->
      expf m z t -> expf (B m zero x) z t.
Proof.
intros.
generalize (expf_B0_CS m x z t H H0).
simpl in |- *.
fold x0 in |- *.
fold y in |- *.
assert (y = cA m zero x).
 rewrite cA_eq in |- *.
  elim (succ_dec m zero x).
   unfold y in |- *.
      tauto.
   tauto.
  tauto.
rewrite <- H3 in |- *.
  elim (expf_dec m y x0).
  tauto.
assert (exd m z).
 unfold expf in H2.
   unfold MF.expo in H2.
    tauto.
 tauto.
Qed.

(* OK: "GENERALISATION DE D13 POUR D11":*)

Lemma expf_expf_B1:forall (m:fmap)(x z t:dart),
 inv_hmap m -> succ m one x -> 
   let tx1 := top m one x in
   let x10 := cF_1 m x in
   ~expf m x10 tx1 ->
      expf m z t -> expf (B m one x) z t.
Proof.
intros.
generalize (expf_B1_CS m x z t H H0).
simpl in |- *.
fold x10 in |- *.
fold tx1 in |- *.
pose (tx1_1 := cF_1 m tx1).
fold tx1_1 in |- *.
elim (expf_dec m x10 tx1).
  tauto.
intros.
  assert (exd m z).
 unfold expf in H2.
   unfold MF.expo in H2.
    tauto.
 tauto.
Qed.

(*===================================================
           RESULTS ABOUT expe, expv / Split0, Split1
====================================================*)

(* OK: "GENERALISATION DE D13 POUR D11":*)

Lemma expe_top_z:forall(m:fmap)(z:dart),
  inv_hmap m -> exd m z -> 
    expe m (top m zero z) z.
Proof.
intros.
apply MA0.expo_top_z.
  tauto.
 tauto.
Qed.

(* OK: "GENERALISATION DE D13 POUR D11":*)

Lemma expv_top_z:forall(m:fmap)(z:dart),
  inv_hmap m -> exd m z -> 
    expv m (top m one z) z.
Proof.
intros.
apply MA1.expo_top_z.
  tauto.
 tauto.
Qed.

(* bottom DONE *)

(* OK: "GENERALISATION DE D13 POUR D11":*)

Lemma expe_top_A:forall(m:fmap)(z:dart),
  inv_hmap m -> succ m zero z -> 
    expe m (top m zero z) (A m zero z).
Proof.
intros.
assert (cA m zero z = A m zero z).
 rewrite cA_eq in |- *.
  elim (succ_dec m zero z).
    tauto.
   tauto.
  tauto.
rewrite <- H1 in |- *.
  assert (exd m z).
 apply succ_exd with zero.
   tauto.
  tauto.
generalize (expe_top_z m z H H2).
  unfold expe in |- *.
  intro.
  apply MA0.MfcA.expo_trans with z.
  tauto.
unfold MA0.MfcA.expo in |- *.
  split.
  tauto.
split with 1%nat.
  simpl in |- *.
   tauto.
Qed.

(* OK: "GENERALISATION DE D13 POUR D11":*)

Lemma expv_top_A:forall(m:fmap)(z:dart),
  inv_hmap m -> succ m one z -> 
    expv m (top m one z) (A m one z).
Proof.
intros.
assert (cA m one z = A m one z).
 rewrite cA_eq in |- *.
  elim (succ_dec m one z).
    tauto.
   tauto.
  tauto.
rewrite <- H1 in |- *.
  assert (exd m z).
 apply succ_exd with one.
   tauto.
  tauto.
generalize (expv_top_z m z H H2).
  unfold expv in |- *.
  intro.
  apply MA1.MfcA.expo_trans with z.
  tauto.
unfold MA1.MfcA.expo in |- *.
  split.
  tauto.
split with 1%nat.
  simpl in |- *.
   tauto.
Qed.

(* OK: "GENERALISATION DE D13 POUR D11":*)

Lemma expe_B_i:  forall(m:fmap)(x z:dart)(i:nat),
  inv_hmap m -> succ m zero x -> exd m z -> 
    let t := Iter (MA0.MfcA.f (B m zero x)) i z 
      in expe m z t.
Proof.
induction i.
 simpl in |- *.
   unfold expe in |- *.
   intros.
   apply MA0.MfcA.expo_refl.
    tauto.
simpl in |- *.
  intros.
  simpl in IHi.
  set (t := Iter (MA0.MfcA.f (B m zero x)) i z)
     in |- *.
  fold t in IHi.
  assert (MA0.MfcA.f (B m zero x) t =
      cA (B m zero x) zero t).
  tauto.
rewrite H2 in |- *.
  rewrite cA_B in |- *.
 elim (eq_dart_dec x t).
  intro.
    rewrite a in |- *.
    unfold expe in |- *.
    apply MA0.MfcA.expo_trans with t.
    tauto.
  apply MA0.MfcA.expo_symm.
    tauto.
  apply expe_bottom_z.
    tauto.
  assert (expe m z t).
    tauto.
  unfold expe in H3.
    generalize (MA0.MfcA.expo_exd m z t H H3).
     tauto.
 intro.
   elim (eq_dart_dec (top m zero x) t).
  intro.
    assert (expe m z t).
    tauto.
  unfold expe in |- *.
    apply MA0.MfcA.expo_trans with t.
   unfold expe in H3.
      tauto.
  rewrite <- a in |- *.
    apply expe_top_A.
     tauto.
   tauto.
 intro.
   unfold expe in |- *.
   apply MA0.MfcA.expo_trans with t.
  fold (expe m z t) in |- *.
     tauto.
 assert (cA m zero t = MA0.MfcA.f m t).
   tauto.
 rewrite H3 in |- *.
   unfold MA0.MfcA.expo in |- *.
   split.
  generalize (exd_cA (B m zero x) zero t).
    generalize (exd_B m zero x t).
    generalize (inv_hmap_B m zero x).
    generalize (MA0.MfcA.exd_Iter_f (B m zero x) i z).
    generalize (exd_B m zero x z).
     tauto.
 split with 1%nat.
   simpl in |- *.
    tauto.
 tauto.
 tauto.
Qed.

(* OK: "GENERALISATION DE D13 POUR D11":*)

Lemma expv_B_i:  forall(m:fmap)(x z:dart)(i:nat),
  inv_hmap m -> succ m one x -> exd m z -> 
    let t := Iter (MA1.MfcA.f (B m one x)) i z 
      in expv m z t.
Proof.
induction i.
 simpl in |- *.
   unfold expv in |- *.
   intros.
   apply MA1.MfcA.expo_refl.
    tauto.
simpl in |- *.
  intros.
  simpl in IHi.
  set (t := Iter (MA1.MfcA.f (B m one x)) i z)
     in |- *.
  fold t in IHi.
  assert (MA1.MfcA.f (B m one x) t =
      cA (B m one x) one t).
  tauto.
rewrite H2 in |- *.
  rewrite cA_B in |- *.
 elim (eq_dart_dec x t).
  intro.
    rewrite a in |- *.
    unfold expv in |- *.
    apply MA1.MfcA.expo_trans with t.
    tauto.
  apply MA1.MfcA.expo_symm.
    tauto.
  apply expv_bottom_z.
    tauto.
  assert (expv m z t).
    tauto.
  unfold expv in H3.
    generalize (MA1.MfcA.expo_exd m z t H H3).
     tauto.
 intro.
   elim (eq_dart_dec (top m one x) t).
  intro.
    assert (expv m z t).
    tauto.
  unfold expv in |- *.
    apply MA1.MfcA.expo_trans with t.
   unfold expv in H3.
      tauto.
  rewrite <- a in |- *.
    apply expv_top_A.
     tauto.
   tauto.
 intro.
   unfold expv in |- *.
   apply MA1.MfcA.expo_trans with t.
  fold (expv m z t) in |- *.
     tauto.
 assert (cA m one t = MA1.MfcA.f m t).
   tauto.
 rewrite H3 in |- *.
   unfold MA1.MfcA.expo in |- *.
   split.
  generalize (exd_cA (B m one x) one t).
    generalize (exd_B m one x t).
    generalize (inv_hmap_B m one x).
    generalize (MA1.MfcA.exd_Iter_f (B m one x) i z).
    generalize (exd_B m one x z).
     tauto.
 split with 1%nat.
   simpl in |- *.
    tauto.
 tauto.
 tauto.
Qed.

(* OK: "GENERALISATION DE D13 POUR D11":*)

Lemma expe_B_expe:  forall(m:fmap)(x z t:dart),
  inv_hmap m -> expe (B m zero x) z t -> expe m z t.
Proof.
intros.
assert (inv_hmap (B m zero x)).
 apply inv_hmap_B.
    tauto.
assert (MA0.MfcA.expo (B m zero x) z t).
 unfold expe in H0.
    tauto.
assert (exd (B m zero x) t).
 generalize (MA0.MfcA.expo_exd (B m zero x) z t).
    tauto.
assert (exd m t).
 generalize (exd_B m zero x t).
    tauto.
elim (succ_dec m zero x).
 intro.
   unfold MA0.MfcA.expo in H2.
   elim H2.
   clear H2.
   intros.
   elim H5.
   clear H5.
   intros i Hi.
   rewrite <- Hi in |- *.
   apply expe_B_i.
   tauto.
  tauto.
 generalize (exd_B m zero x z).
    tauto.
intro.
  generalize (not_succ_B m zero x).
  intros.
  rewrite H5 in H0.
  tauto.
 tauto.
 tauto.
Qed.

(* OK: "GENERALISATION DE D13 POUR D11":*)

Lemma expv_B_expv:  forall(m:fmap)(x z t:dart),
  inv_hmap m -> expv (B m one x) z t -> expv m z t.
Proof.
intros.
assert (inv_hmap (B m one x)).
 apply inv_hmap_B.
    tauto.
assert (MA1.MfcA.expo (B m one x) z t).
 unfold expv in H0.
    tauto.
assert (exd (B m one x) t).
 generalize (MA1.MfcA.expo_exd (B m one x) z t).
    tauto.
assert (exd m t).
 generalize (exd_B m one x t).
    tauto.
elim (succ_dec m one x).
 intro.
   unfold MA1.MfcA.expo in H2.
   elim H2.
   clear H2.
   intros.
   elim H5.
   clear H5.
   intros i Hi.
   rewrite <- Hi in |- *.
   apply expv_B_i.
   tauto.
  tauto.
 generalize (exd_B m one x z).
    tauto.
intro.
  generalize (not_succ_B m one x).
  intros.
  rewrite H5 in H0.
  tauto.
 tauto.
 tauto.
Qed.

(* OK: "GENERALISATION DE D13 POUR D11":*)

Lemma expe_Split_expe :forall(m:fmap)(x x' z t:dart),
   inv_hmap m -> 
     expe (Split m zero x x') z t -> expe m z t.
Proof.
intros m x x' z t H.
unfold Split in |- *.
fold (Shift m zero x) in |- *.
elim (succ_dec m zero x).
 elim (succ_dec m zero x').
  intros.
    set (m0 := Shift m zero x) in |- *.
    fold m0 in H0.
    assert (inv_hmap m0).
   unfold m0 in |- *.
     apply inv_hmap_Shift.
     tauto.
    tauto.
  generalize (expe_B_expe m0 x' z t H1 H0).
    intro.
    generalize (expe_Shift m x z t H a0).
    simpl in |- *.
    fold m0 in |- *.
     tauto.
 intros.
   apply expe_B_expe with x.
   tauto.
  tauto.
intro.
  intro.
  elim (succ_dec m zero x').
 intro.
   apply expe_B_expe with x'.
   tauto.
  tauto.
intro.
  rewrite not_succ_B in H0.
  tauto.
 tauto.
 tauto.
Qed.

(* OK: "GENERALISATION DE D13 POUR D11":*)

Lemma expv_Split_expv :forall(m:fmap)(x x' z t:dart),
   inv_hmap m -> 
     expv (Split m one x x') z t -> expv m z t.
Proof.
intros m x x' z t H.
unfold Split in |- *.
fold (Shift m one x) in |- *.
elim (succ_dec m one x).
 elim (succ_dec m one x').
  intros.
    set (m0 := Shift m one x) in |- *.
    fold m0 in H0.
    assert (inv_hmap m0).
   unfold m0 in |- *.
     apply inv_hmap_Shift.
     tauto.
    tauto.
  generalize (expv_B_expv m0 x' z t H1 H0).
    intro.
    generalize (expv_Shift m x z t H a0).
    simpl in |- *.
    fold m0 in |- *.
     tauto.
 intros.
   apply expv_B_expv with x.
   tauto.
  tauto.
intro.
  intro.
  elim (succ_dec m one x').
 intro.
   apply expv_B_expv with x'.
   tauto.
  tauto.
intro.
  rewrite not_succ_B in H0.
  tauto.
 tauto.
 tauto.
Qed.

(*===================================================
           RESULTS ABOUT expf / Split0, Split1
====================================================*)

(* OK: "GENERALISATION DE D13 POUR D11": *)

Lemma expf_Split0:forall(m:fmap)(x x' z t:dart),
   inv_hmap m -> planar m -> 
    cracke m x x' ->
    let y:= cA m zero x in
    let y':= cA m zero x' in
    ~expf m y y' -> 
        (expf m z t -> expf (Split m zero x x') z t).
Proof.
intros.
unfold Split in |- *.
elim (succ_dec m zero x).
 elim (succ_dec m zero x').
  intros.
    fold (Shift m zero x) in |- *.
    set (m0 := Shift m zero x) in |- *.
    assert (inv_hmap m0).
   unfold m0 in |- *.
     apply inv_hmap_Shift.
     tauto.
    tauto.
  assert (planar m0).
   unfold m0 in |- *.
     apply planar_Shift0.
     tauto.
    tauto.
    tauto.
  assert (y = A m zero x).
   unfold y in |- *.
     rewrite cA_eq in |- *.
    elim (succ_dec m zero x).
      tauto.
     tauto.
    tauto.
  assert (y' = A m zero x').
   unfold y' in |- *.
     rewrite cA_eq in |- *.
    elim (succ_dec m zero x').
      tauto.
     tauto.
    tauto.
  assert (exd m x').
   apply succ_exd with zero.
     tauto.
    tauto.
  assert (~ expf m0 y y').
   intro.
     elim H1.
     generalize (expf_Shift m zero x y y' H a0).
     fold m0 in |- *.
      tauto.
  assert (~ expf m0 (A m0 zero x') 
       (bottom m0 zero x')).
   unfold cracke in H1.
     unfold MA0.crack in H1.
     elim H1.
     clear H1.
     intros.
     unfold m0 in |- *.
     rewrite (bottom_Shift0 m x x' H a0 H8 H1) in |- *.
     elim (expe_dec m x x' H).
    intro.
      rewrite (A_Shift m zero x x' H a0) in |- *.
      elim (eq_dart_dec x x').
      tauto.
    elim (eq_dart_dec (top m zero x) x').
     intros.
       rewrite <- a2 in a.
        absurd (succ m zero (top m zero x)).
      apply not_succ_top.
         tauto.
      tauto.
    intros.
      fold m0 in |- *.
      rewrite <- H6 in |- *.
      rewrite <- H7 in |- *.
      intro.
      elim H9.
      apply expf_symm.
       tauto.
    tauto.
  apply expf_expf_B0.
    tauto.
  unfold succ in |- *.
    unfold m0 in |- *.
    rewrite A_Shift in |- *.
   elim (eq_dart_dec x x').
    unfold cracke in H1.
      unfold MA0.crack in H1.
       tauto.
   elim (eq_dart_dec (top m zero x) x').
    intro.
      rewrite <- a1 in a.
       absurd (succ m zero (top m zero x)).
     apply not_succ_top.
        tauto.
     tauto.
   unfold succ in a.
      tauto.
   tauto.
   tauto.
   tauto.
  unfold m0 in |- *.
    generalize (expf_Shift m zero x z t H a0).
     tauto.
 intros.
   assert (bottom m zero x = bottom m zero x').
  apply expe_bottom.
    tauto.
  unfold cracke in H1.
    unfold MA0.crack in H1.
     tauto.
 assert (bottom m zero x' = y').
  unfold y' in |- *.
    rewrite cA_eq in |- *.
   elim (succ_dec m zero x').
     tauto.
    tauto.
   tauto.
 rewrite <- H4 in H5.
   rewrite <- H5 in H2.
   apply expf_expf_B0.
   tauto.
  tauto.
 unfold y in H2.
   rewrite cA_eq in H2.
  generalize H2.
    clear H2.
    elim (succ_dec m zero x).
    tauto.
   tauto.
  tauto.
  tauto.
intro.
  elim (succ_dec m zero x').
 intro.
   assert (bottom m zero x = bottom m zero x').
  apply expe_bottom.
    tauto.
  unfold cracke in H1.
    unfold MA0.crack in H1.
     tauto.
 assert (bottom m zero x = y).
  unfold y in |- *.
    rewrite cA_eq in |- *.
   elim (succ_dec m zero x).
     tauto.
    tauto.
   tauto.
 rewrite H4 in H5.
   rewrite <- H5 in H2.
   assert (y' = A m zero x').
  unfold y' in |- *.
    rewrite cA_eq in |- *.
   elim (succ_dec m zero x').
     tauto.
    tauto.
   tauto.
 rewrite H6 in H2.
   assert (~ expf m (A m zero x') (bottom m zero x')).
  intro.
    apply H2.
    apply expf_symm.
     tauto.
 apply expf_expf_B0.
   tauto.
  tauto.
  tauto.
  tauto.
intro.
  rewrite not_succ_B in |- *.
  tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma expf_Split1:forall(m:fmap)(x x' z t:dart),
   inv_hmap m -> planar m -> 
    crackv m x x' ->
    ~expf m x x' -> 
        (expf m z t -> expf (Split m one x x') z t).
Proof. 
intros.
unfold Split in |- *.
elim (succ_dec m one x).
 elim (succ_dec m one x').
  intros.
    fold (Shift m one x) in |- *.
    set (m0 := Shift m one x) in |- *.
    assert (inv_hmap m0).
   unfold m0 in |- *.
     apply inv_hmap_Shift.
     tauto.
    tauto.
  assert (planar m0).
   unfold m0 in |- *.
     apply planar_Shift1.
     tauto.
    tauto.
    tauto.
  assert (~ expf m0 x x').
   generalize (expf_Shift m one x x x' H a0).
     fold m0 in |- *.
      tauto.
  assert (exd m x).
   apply succ_exd with one.
     tauto.
    tauto.
  assert (exd m x').
   apply succ_exd with one.
     tauto.
    tauto.
  unfold crackv in H1.
    unfold MA1.crack in H1.
    elim H1.
    clear H1.
    intros.
    set (tx'1 := top m one x') in |- *.
    set (x'10 := cF_1 m x') in |- *.
    assert (top m0 one x' = x).
   unfold m0 in |- *.
     rewrite (top_Shift1 m x x' H a0 H8 H1) in |- *.
     elim (expv_dec m x x' H).
     tauto.
    tauto.
  assert (cF_1 m0 x' = cF_1 m x').
   unfold m0 in |- *; rewrite cF_1_Shift in |- *.
     tauto.
    tauto.
    tauto.
  apply expf_expf_B1.
    tauto.
  unfold m0 in |- *.
    unfold succ in |- *.
    rewrite A_Shift in |- *.
   elim (eq_dart_dec x x').
     tauto.
   elim (eq_dart_dec (top m one x) x').
    intros.
      rewrite <- a1 in a.
       absurd (succ m one (top m one x)).
     apply not_succ_top.
        tauto.
     tauto.
   intros.
     unfold succ in a.
      tauto.
   tauto.
   tauto.
  rewrite H10 in |- *.
    rewrite H11 in |- *.
    intro.
    assert (expf m (cF_1 m x') x).
   generalize (expf_Shift m one x (cF_1 m x') x).
     fold m0 in |- *.
      tauto.
  assert (expf m x x').
   apply expf_trans with (cF_1 m x').
    apply expf_symm.
       tauto.
   unfold expf in |- *.
     split.
     tauto.
   unfold MF.expo in |- *.
     split.
    generalize (exd_cF_1 m x').
       tauto.
   split with 1%nat.
     simpl in |- *.
     rewrite cF_cF_1 in |- *.
     tauto.
    tauto.
    tauto.
  apply H6.
    generalize (expf_Shift m one x x x').
    fold m0 in |- *.
     tauto.
  generalize (expf_Shift m one x z t).
    fold m0 in |- *.
     tauto.
 intros.
   assert (top m one x = x').
  rewrite (expv_top m x x') in |- *.
   apply nosucc_top.
     tauto.
   unfold crackv in H1.
     unfold MA1.crack in H1.
     generalize (MA1.MfcA.expo_exd m x x').
      tauto.
    tauto.
   tauto.
  unfold crackv in H1.
    unfold MA1.crack in H1.
     tauto.
 apply expf_expf_B1.
   tauto.
  tauto.
 rewrite H4 in |- *.
   intro.
   elim H2.
   apply expf_trans with (cF_1 m x).
  apply expf_symm.
    unfold expf in |- *.
    split.
    tauto.
  unfold MF.expo in |- *.
    split.
   generalize (exd_cF_1 m x).
     assert (exd m x).
    apply succ_exd with one.
      tauto.
     tauto.
    tauto.
  split with 1%nat.
    simpl in |- *.
    rewrite cF_cF_1 in |- *.
    tauto.
   tauto.
  apply succ_exd with one.
    tauto.
   tauto.
  tauto.
  tauto.
intro.
  assert (succ m one x').
 generalize (MA1.crack_succ m x x').
    tauto.
assert (exd m x').
 apply succ_exd with one.
   tauto.
  tauto.
assert (exd m x).
 unfold crackv in H1.
   unfold MA1.crack in H1.
   unfold MA1.MfcA.expo in H1.
    tauto.
assert (top m one x' = x).
 rewrite <- (expv_top m x x') in |- *.
  apply nosucc_top.
    tauto.
   tauto.
   tauto.
  tauto.
 unfold crackv in H1.
   unfold MA1.crack in H1.
    tauto.
apply expf_expf_B1.
  tauto.
 tauto.
rewrite H7 in |- *.
  intro.
  apply H2.
  apply expf_trans with (cF_1 m x').
 apply expf_symm.
    tauto.
unfold MF.expo in |- *.
  split.
  tauto.
unfold MF.expo in |- *.
  split.
 generalize (exd_cF_1 m x').
    tauto.
split with 1%nat.
  simpl in |- *.
  rewrite cF_cF_1 in |- *.
  tauto.
 tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma betweenf_expf1:forall(m:fmap)(z v t:dart),
 inv_hmap m -> exd m z ->
  betweenf m z v t -> (expf m v z /\ expf m v t).
Proof.
intros.
assert (expf m z v /\ expf m z t).
 apply (betweenf_expf m z v t H H0 H1).
split.
 apply expf_symm.
    tauto.
apply expf_trans with z.
 apply expf_symm.
    tauto.
 tauto.
Qed.

(* OK: "REPRIS DE Del13" : *)

Lemma not_expf_B0:forall (m:fmap)(x z t:dart),
 inv_hmap m -> planar m -> succ m zero x -> 
   let y := A m zero x in
   let x0 := bottom m zero x in 
         (~expf m y z /\ ~expf m x0 z
       \/ ~expf m y t /\ ~expf m x0 t) ->
   ~expf m z t -> ~expf (B m zero x) z t.
Proof.
simpl in |- *.
intros.
set (x0 := cA m zero x) in |- *.
set (xb0 := bottom m zero x) in |- *.
fold x0 in H2.
fold xb0 in H2.
assert (x0 = A m zero x).
 unfold x0 in |- *.
   rewrite cA_eq in |- *.
  elim (succ_dec m zero x).
    tauto.
   tauto.
  tauto.
intro NC.
  assert (inv_hmap (B m zero x)).
 apply inv_hmap_B.
    tauto.
assert (exd (B m zero x) z).
 unfold expf in NC.
   unfold MF.expo in NC.
    tauto.
assert (exd m z).
 generalize (exd_B m zero x z).
    tauto.
assert (exd m x).
 apply succ_exd with zero.
   tauto.
  tauto.
assert (exd m (top m zero x)).
 apply exd_top.
   tauto.
  tauto.
assert (exd m (cA_1 m one (top m zero x))).
 generalize (exd_cA_1 m one (top m zero x)).
    tauto.
assert (exd m (cA_1 m one x)).
 generalize (exd_cA_1 m one x).
    tauto.
rename H11 into Fa.
  generalize (expf_B0_CNS m x z t H H1).
  simpl in |- *.
  fold x0 in |- *.
  fold xb0 in |- *.
  elim (expf_dec m x0 xb0).
 intros.
   assert
    (betweenf m (cA_1 m one x) z xb0 /\
      betweenf m (cA_1 m one x) t xb0 \/
     betweenf m (cA_1 m one (top m zero x)) z x0 /\
     betweenf m (cA_1 m one (top m zero x)) t x0 \/
     ~ expf m (cA_1 m one x) z /\ expf m z t).
   tauto.
 clear H11.
   elim H12.
  clear H12.
    intro.
    decompose [and] H11.
    clear H11.
    generalize (betweenf_expf1 
       m (cA_1 m one x) z xb0 H Fa H12).
    intro.
    generalize (betweenf_expf1 
       m (cA_1 m one x) t xb0 H Fa H13).
    intro.
    assert (expf m xb0 z).
   apply expf_symm.
      tauto.
  assert (expf m xb0 t).
   apply expf_symm.
      tauto.
   tauto.
 clear H12.
   intro.
   elim H11.
  clear H11.
    intro.
    decompose [and] H11.
    clear H11.
    generalize (betweenf_expf1 
       m (cA_1 m one (top m zero x)) z x0 H H10 H12).
    intro.
    generalize (betweenf_expf1
       m (cA_1 m one (top m zero x)) t x0 H H10 H13).
    intro.
    rewrite <- H4 in H2.
    assert (expf m x0 z).
   apply expf_symm.
      tauto.
  assert (expf m x0 t).
   apply expf_symm.
      tauto.
   tauto.
  tauto.
intros.
  rewrite <- H4 in H2.
   tauto.
Qed.

(* OK, "REPRIS DE Del13": DEJA REPRIS...

Lemma not_expf_B0:forall (m:fmap)(x z t:dart),
 inv_hmap m -> planar m -> succ m zero x -> 
   let y := A m zero x in
   let x0 := bottom m zero x in 
         (~expf m y z /\ ~expf m x0 z
       \/ ~expf m y t /\ ~expf m x0 t) ->
   ~expf m z t -> ~expf (B m zero x) z t.
Proof.
simpl in |- *.
intros.
set (x0 := cA m zero x) in |- *.
set (xb0 := bottom m zero x) in |- *.
fold x0 in H2.
fold xb0 in H2.
assert (x0 = A m zero x).
 unfold x0 in |- *.
   rewrite cA_eq in |- *.
  elim (succ_dec m zero x).
    tauto.
   tauto.
  tauto.
intro NC.
  assert (inv_hmap (B m zero x)).
 apply inv_hmap_B.
    tauto.
assert (exd (B m zero x) z).
 unfold expf in NC.
   unfold MF.expo in NC.
    tauto.
assert (exd m z).
 generalize (exd_B m zero x z).
    tauto.
assert (exd m x).
 apply succ_exd with zero.
   tauto.
  tauto.
assert (exd m (top m zero x)).
 apply exd_top.
   tauto.
  tauto.
assert (exd m (cA_1 m one (top m zero x))).
 generalize (exd_cA_1 m one (top m zero x)).
    tauto.
assert (exd m (cA_1 m one x)).
 generalize (exd_cA_1 m one x).
    tauto.
rename H11 into Fa.
  generalize (expf_B0_CNS m x z t H H1).
  simpl in |- *.
  fold x0 in |- *.
  fold xb0 in |- *.
  elim (expf_dec m x0 xb0).
 intros.
   assert
    (betweenf m (cA_1 m one x) z xb0 /\
      betweenf m (cA_1 m one x) t xb0 \/
     betweenf m (cA_1 m one (top m zero x)) z x0 /\
     betweenf m (cA_1 m one (top m zero x)) t x0 \/
     ~ expf m (cA_1 m one x) z /\ expf m z t).
   tauto.
 clear H11.
   elim H12.
  clear H12.
    intro.
    decompose [and] H11.
    clear H11.
    generalize (betweenf_expf1 
       m (cA_1 m one x) z xb0 H Fa H12).
    intro.
    generalize (betweenf_expf1 
       m (cA_1 m one x) t xb0 H Fa H13).
    intro.
    assert (expf m xb0 z).
   apply expf_symm.
      tauto.
  assert (expf m xb0 t).
   apply expf_symm.
      tauto.
   tauto.
 clear H12.
   intro.
   elim H11.
  clear H11.
    intro.
    decompose [and] H11.
    clear H11.
    generalize (betweenf_expf1 
       m (cA_1 m one (top m zero x)) z x0 H H10 H12).
    intro.
    generalize (betweenf_expf1
       m (cA_1 m one (top m zero x)) t x0 H H10 H13).
    intro.
    rewrite <- H4 in H2.
    assert (expf m x0 z).
   apply expf_symm.
      tauto.
  assert (expf m x0 t).
   apply expf_symm.
      tauto.
   tauto.
  tauto.
intros.
  rewrite <- H4 in H2.
   tauto.
Qed.

*)

(* OK: "GENERALISE DE Del13": *)

Lemma not_expf_B1:forall (m:fmap)(x z t:dart),
 inv_hmap m -> planar m -> succ m one x -> 
   let tx1 := top m one x in
   let x10 := cF_1 m x in
         (~expf m x10 z /\ ~expf m tx1 z
       \/ ~expf m x10 t /\ ~expf m tx1 t) ->
   ~expf m z t -> ~expf (B m one x) z t.
Proof.
simpl in |- *.
intros.
set (tx1 := top m one x) in |- *.
set (x10 := cF_1 m x) in |- *.
fold tx1 in H2; fold x10 in H2.
intro NC.
assert (inv_hmap (B m one x)).
 apply inv_hmap_B.
    tauto.
assert (exd (B m one x) z).
 unfold expf in NC.
   unfold MF.expo in NC.
    tauto.
assert (exd m z).
 generalize (exd_B m one x z).
    tauto.
assert (exd m x).
 apply succ_exd with one.
   tauto.
  tauto.
set (tx1_1 := cF_1 m tx1) in |- *.
  assert (exd m tx1).
 unfold tx1 in |- *.
   apply exd_top.
   tauto.
  tauto.
assert (exd m tx1_1).
 unfold tx1_1 in |- *.
   generalize (exd_cF_1 m tx1).
    tauto.
generalize (expf_B1_CNS m x z t H H1).
  simpl in |- *.
  fold tx1 in |- *.
  fold x10 in |- *.
  fold tx1_1 in |- *.
  elim (expf_dec m x10 tx1).
 intros.
   assert
    (betweenf m tx1 z x10 /\ betweenf m tx1 t x10 \/
     betweenf m x z tx1_1 /\ betweenf m x t tx1_1 \/
     ~ expf m x10 z /\ expf m z t).
   tauto.
 clear H10.
   elim H11.
  clear H11.
    intro.
    decompose [and] H10.
    clear H10.
    generalize (betweenf_expf1 m tx1 z x10 H H8 H11).
    intro.
    generalize (betweenf_expf1 m tx1 t x10 H H8 H12).
    intro.
    assert (expf m tx1 z).
   apply expf_symm.
      tauto.
  assert (expf m x10 z).
   apply expf_symm.
      tauto.
  assert (expf m x10 t).
   apply expf_symm.
      tauto.
  assert (expf m tx1 t).
   apply expf_symm.
      tauto.
   tauto.
 clear H11.
   intro.
   elim H10.
  clear H10.
    intro.
    decompose [and] H10.
    clear H10.
    generalize (betweenf_expf m x z tx1_1 H H7 H11).
    intro.
    generalize (betweenf_expf m x t tx1_1 H H7 H12).
    intro.
    assert (expf m x10 z).
   apply expf_trans with x.
    unfold x10 in |- *.
      unfold expf in |- *.
      split.
      tauto.
    unfold MF.expo in |- *.
      split.
     generalize (exd_cF_1 m x).
        tauto.
    split with 1%nat.
      simpl in |- *.
      rewrite cF_cF_1 in |- *.
      tauto.
     tauto.
     tauto.
    tauto.
  assert (expf m tx1 z).
   apply expf_trans with x10.
    apply expf_symm.
       tauto.
    tauto.
  assert (expf m x10 t).
   apply expf_trans with z.
     tauto.
   apply expf_trans with x.
    apply expf_symm.
       tauto.
    tauto.
  assert (expf m tx1 t).
   apply expf_trans with x10.
    apply expf_symm.
       tauto.
    tauto.
   tauto.
 intro.
   clear H10.
    tauto.
 tauto.
Qed.

(* OK: "REPRIS DE Del13": *)

Lemma not_expf_Split0:forall (m:fmap)(x x' z t:dart),
 inv_hmap m -> planar m -> cracke m x x' ->
   let y  := cA m zero x in
   let y' := cA m zero x' in 
         (~expf m y z /\ ~expf m y' z
       \/ ~expf m y t /\ ~expf m y' t) ->
   ~expf m z t -> ~expf (Split m zero x x') z t.
Proof.
intros.
unfold Split in |- *.
elim (succ_dec m zero x).
 elim (succ_dec m zero x').
  intros.
    fold (Shift m zero x) in |- *.
    set (m0 := Shift m zero x) in |- *.
    assert (inv_hmap m0).
   unfold m0 in |- *.
     apply inv_hmap_Shift.
     tauto.
    tauto.
  assert (planar m0).
   unfold m0 in |- *.
     apply planar_Shift.
     tauto.
    tauto.
    tauto.
  assert (~ expf m0 z t).
   intro.
     apply H3.
     generalize (expf_Shift m zero x z t H a0).
     fold m0 in |- *.
      tauto.
  assert (y' = A m0 zero x').
   unfold m0 in |- *.
     rewrite A_Shift in |- *.
    elim (eq_dart_dec x x').
     unfold cracke in H1.
       unfold MA0.crack in H1.
        tauto.
    elim (eq_dart_dec (top m zero x) x').
     intro.
       rewrite <- a1 in a.
        absurd (succ m zero (top m zero x)).
      apply not_succ_top.
         tauto.
      tauto.
    intros.
      unfold y' in |- *.
      rewrite cA_eq in |- *.
     elim (succ_dec m zero x').
       tauto.
      tauto.
     tauto.
    tauto.
    tauto.
  assert (y = bottom m0 zero x').
   unfold m0 in |- *.
     unfold cracke in H1.
     unfold MA0.crack in H1.
     assert (x <> x').
     tauto.
   assert (exd m x').
    apply MA0.MfcA.expo_exd with x.
      tauto.
    unfold cracke in H1.
      unfold MA0.crack in H1.
       tauto.
   rewrite (bottom_Shift0 m x x' H a0 H9 H8) in |- *.
     elim (MA0.MfcA.expo_dec m x x').
    unfold y in |- *.
      rewrite cA_eq in |- *.
     elim (succ_dec m zero x).
       tauto.
      tauto.
     tauto.
    tauto.
  assert (succ m0 zero x').
   unfold succ in |- *.
     rewrite <- H7 in |- *.
     unfold y' in |- *.
     rewrite cA_eq in |- *.
    elim (succ_dec m zero x').
     fold (succ m zero x') in |- *.
        tauto.
     tauto.
    tauto.
  elim H2.
   clear H2.
     intro.
     decompose [and] H2.
     clear H2.
     assert (~ expf m0 y z).
    intro.
      apply H10.
      generalize (expf_Shift m zero x y z H a0).
      fold m0 in |- *.
       tauto.
   assert (~ expf m0 y' z).
    intro.
      apply H11.
      generalize (expf_Shift m zero x y' z H a0).
      fold m0 in |- *.
       tauto.
   apply not_expf_B0.
     tauto.
    tauto.
    tauto.
   rewrite <- H7 in |- *.
     rewrite <- H8 in |- *.
      tauto.
    tauto.
  intro.
    decompose [and] H10.
    clear H2 H10.
    assert (~ expf m0 y t).
   intro.
     apply H11.
     generalize (expf_Shift m zero x y t H a0).
     fold m0 in |- *.
      tauto.
  assert (~ expf m0 y' t).
   intro.
     apply H12.
     generalize (expf_Shift m zero x y' t H a0).
     fold m0 in |- *.
      tauto.
  apply not_expf_B0.
    tauto.
   tauto.
   tauto.
  rewrite <- H7 in |- *.
    rewrite <- H8 in |- *.
     tauto.
   tauto.
 intros.
   assert (y' = bottom m zero x).
  unfold y' in |- *.
    rewrite cA_eq in |- *.
   elim (succ_dec m zero x').
     tauto.
   intro.
     symmetry  in |- *.
     apply expe_bottom.
     tauto.
   unfold expe in H1.
     assert (y = A m zero x).
    unfold y in |- *.
      rewrite cA_eq in |- *.
     elim (succ_dec m zero x).
       tauto.
      tauto.
     tauto.
   unfold cracke in H1.
     unfold MA0.crack in H1.
      tauto.
   tauto.
 apply not_expf_B0.
   tauto.
  tauto.
  tauto.
 rewrite <- H4 in |- *.
   assert (y = A m zero x).
  unfold y in |- *.
    rewrite cA_eq in |- *.
   elim (succ_dec m zero x).
     tauto.
    tauto.
   tauto.
 rewrite <- H5 in |- *.
    tauto.
  tauto.
intro.
  elim (succ_dec m zero x').
 intro.
   assert (y = bottom m zero x').
  unfold y in |- *.
    rewrite cA_eq in |- *.
   elim (succ_dec m zero x).
    elim (succ_dec m zero x').
      tauto.
    intro.
       tauto.
   intro.
     apply expe_bottom.
     tauto.
   unfold cracke in H1.
     unfold MA0.crack in H1.
      tauto.
   tauto.
 assert (y' = A m zero x').
  unfold y' in |- *.
    rewrite cA_eq in |- *.
   elim (succ_dec m zero x').
     tauto.
    tauto.
   tauto.
 apply not_expf_B0.
   tauto.
  tauto.
  tauto.
 rewrite <- H5 in |- *.
   rewrite <- H4 in |- *.
    tauto.
  tauto.
intro.
  rewrite not_succ_B in |- *.
  tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma not_expf_Split1:forall (m:fmap)(x x' z t:dart),
 inv_hmap m -> planar m -> crackv m x x' ->
         (~expf m x z /\ ~expf m x' z
       \/ ~expf m x t /\ ~expf m x' t) ->
   ~expf m z t -> ~expf (Split m one x x') z t.
Proof.
intros.
unfold Split in |- *.
elim (succ_dec m one x).
 elim (succ_dec m one x').
  intros.
    fold (Shift m one x) in |- *.
    set (m0 := Shift m one x) in |- *.
    assert (inv_hmap m0).
   unfold m0 in |- *.
     apply inv_hmap_Shift.
     tauto.
    tauto.
  assert (planar m0).
   unfold m0 in |- *.
     apply planar_Shift.
     tauto.
    tauto.
    tauto.
  assert (~ expf m0 z t).
   intro.
     apply H3.
     generalize (expf_Shift m one x z t H a0).
     fold m0 in |- *.
      tauto.
  assert (cF_1 m0 x' = cF_1 m x').
   unfold m0 in |- *.
     rewrite cF_1_Shift in |- *.
     tauto.
    tauto.
    tauto.
  assert (top m0 one x' = x).
   unfold m0 in |- *.
     assert (exd m x').
    apply succ_exd with one.
      tauto.
     tauto.
   assert (x <> x').
    unfold crackv in H1.
      unfold MA1.crack in H1.
       tauto.
   rewrite (top_Shift1 m x x' H a0 H8 H9) in |- *.
     elim (expv_dec m x x').
     tauto.
   unfold crackv in H1.
     unfold MA1.crack in H1.
      tauto.
  unfold m0 in |- *.
    apply not_expf_B1.
   apply inv_hmap_Shift.
     tauto.
    tauto.
  apply planar_Shift1.
    tauto.
   tauto.
   tauto.
  unfold succ in |- *.
    rewrite A_Shift in |- *.
   elim (eq_dart_dec x x').
    unfold crackv in H1.
      unfold MA1.crack in H1.
       tauto.
   elim (eq_dart_dec (top m one x) x').
    intros.
      rewrite <- a1 in a.
       absurd (succ m one (top m one x)).
     apply not_succ_top.
        tauto.
     tauto.
   unfold succ in a.
      tauto.
   tauto.
   tauto.
  fold m0 in |- *.
    rewrite H7 in |- *.
    rewrite H8 in |- *.
    assert (expf m0 x z <-> expf m x z).
   unfold m0 in |- *.
     generalize (expf_Shift m one x x z).
      tauto.
  assert (expf m0 (cF_1 m x') z <-> 
  expf m (cF_1 m x') z).
   unfold m0 in |- *.
     generalize (expf_Shift m one x (cF_1 m x') z).
      tauto.
  assert (exd m x').
   apply succ_exd with one.
     tauto.
    tauto.
  assert (exd m (cF_1 m x')).
   generalize (exd_cF_1 m x').
      tauto.
  assert (expf m (cF_1 m x') z <-> expf m x' z).
   split.
    intro.
      apply expf_trans with (cF_1 m x').
     apply expf_symm.
       unfold expf in |- *.
       split.
       tauto.
     unfold MF.expo in |- *.
       split.
       tauto.
     split with 1%nat.
       simpl in |- *.
       rewrite cF_cF_1 in |- *.
       tauto.
      tauto.
      tauto.
     tauto.
   intro.
     apply expf_trans with x'.
    unfold expf in |- *.
      split.
      tauto.
    unfold MF.expo in |- *.
      split.
      tauto.
    split with 1%nat.
      simpl in |- *.
      rewrite cF_cF_1 in |- *.
      tauto.
     tauto.
     tauto.
    tauto.
  assert (expf m0 x t <-> expf m x t).
   unfold m0 in |- *.
     generalize (expf_Shift m one x x t).
      tauto.
  assert (expf m0 (cF_1 m x') t <->
      expf m (cF_1 m x') t).
   unfold m0 in |- *.
     generalize (expf_Shift m one x (cF_1 m x') t).
      tauto.
  assert (expf m (cF_1 m x') t <-> expf m x' t).
   split.
    intro.
      apply expf_trans with (cF_1 m x').
     apply expf_symm.
       unfold expf in |- *.
       split.
       tauto.
     unfold MF.expo in |- *.
       split.
       tauto.
     split with 1%nat.
       simpl in |- *.
       rewrite cF_cF_1 in |- *.
       tauto.
      tauto.
      tauto.
     tauto.
   intro.
     apply expf_trans with x'.
    unfold expf in |- *.
      split.
      tauto.
    unfold MF.expo in |- *.
      split.
      tauto.
    split with 1%nat.
      simpl in |- *.
      rewrite cF_cF_1 in |- *.
      tauto.
     tauto.
     tauto.
    tauto.
   tauto.
  fold m0 in |- *.
     tauto.
 intros.
   assert (exd m x).
  apply (succ_exd m one x H a).
 set (x10 := cF_1 m x) in |- *.
   set (tx1 := top m one x) in |- *.
   assert (exd m x10).
  unfold x10 in |- *.
    generalize (exd_cF_1 m x).
     tauto.
 assert (exd m tx1).
  unfold tx1 in |- *.
    apply exd_top.
    tauto.
   tauto.
 apply (not_expf_B1 m x z t H H0).
   tauto.
 fold tx1 in |- *; fold x10 in |- *.
   assert (~ expf m x z -> ~ expf m x10 z).
  intro.
    intro.
    elim H7.
    apply expf_trans with x10.
   apply expf_symm.
     unfold expf in |- *.
     split.
     tauto.
   unfold MF.expo in |- *.
     split.
    unfold x10 in |- *.
       tauto.
   split with 1%nat.
     simpl in |- *.
     unfold x10 in |- *.
     rewrite cF_cF_1 in |- *.
     tauto.
    tauto.
    tauto.
   tauto.
 assert (~ expf m x t -> ~ expf m x10 t).
  intro.
    intro.
    elim H8.
    apply expf_trans with x10.
   apply expf_symm.
     unfold expf in |- *.
     split.
     tauto.
   unfold MF.expo in |- *.
     split.
    unfold x10 in |- *.
       tauto.
   split with 1%nat.
     simpl in |- *.
     unfold x10 in |- *.
     rewrite cF_cF_1 in |- *.
     tauto.
    tauto.
    tauto.
   tauto.
 assert (tx1 = x').
  unfold tx1 in |- *.
    rewrite (expv_top m x x') in |- *.
   apply nosucc_top.
     tauto.
   unfold crackv in H1.
     unfold MA1.crack in H1.
     generalize (MA1.MfcA.expo_exd m x x').
      tauto.
    tauto.
   tauto.
  unfold crackv in H1.
    unfold MA1.crack in H1.
     tauto.
 rewrite H9 in |- *.
    tauto.
  tauto.
intro.
  assert (succ m one x').
 generalize (MA1.crack_succ m x x').
    tauto.
assert (exd m x').
 apply (succ_exd m one x' H H4).
set (x10 := cF_1 m x') in |- *.
  set (tx1 := top m one x') in |- *.
  assert (exd m x10).
 unfold x10 in |- *.
   generalize (exd_cF_1 m x').
    tauto.
assert (exd m tx1).
 unfold tx1 in |- *.
   apply exd_top.
   tauto.
  tauto.
apply (not_expf_B1 m x' z t H H0).
  tauto.
fold tx1 in |- *; fold x10 in |- *.
  assert (~ expf m x' z -> ~ expf m x10 z).
 intro.
   intro.
   elim H8.
   apply expf_trans with x10.
  apply expf_symm.
    unfold expf in |- *.
    split.
    tauto.
  unfold MF.expo in |- *.
    split.
   unfold x10 in |- *.
      tauto.
  split with 1%nat.
    simpl in |- *.
    unfold x10 in |- *.
    rewrite cF_cF_1 in |- *.
    tauto.
   tauto.
   tauto.
  tauto.
assert (~ expf m x' t -> ~ expf m x10 t).
 intro.
   intro.
   elim H9.
   apply expf_trans with x10.
  apply expf_symm.
    unfold expf in |- *.
    split.
    tauto.
  unfold MF.expo in |- *.
    split.
   unfold x10 in |- *.
      tauto.
  split with 1%nat.
    simpl in |- *.
    unfold x10 in |- *.
    rewrite cF_cF_1 in |- *.
    tauto.
   tauto.
   tauto.
  tauto.
assert (tx1 = x).
 unfold tx1 in |- *.
   rewrite (expv_top m x' x) in |- *.
  apply nosucc_top.
    tauto.
  unfold crackv in H1.
    unfold MA1.crack in H1.
    unfold MA1.MfcA.expo in H1.
     tauto.
   tauto.
  tauto.
 apply expv_symm.
   tauto.
 unfold crackv in H1.
   unfold MA1.crack in H1.
    tauto.
rewrite H10 in |- *.
   tauto.
 tauto.
Qed.

(* OK: *)

Lemma expf_Split0_cracke: forall (m : fmap) (x x': dart),
  inv_hmap m -> planar m -> cracke m x x' ->
    let y :=cA m zero x in
    let y':=cA m zero x' in
  ~expf m y y' -> expf (Split m zero x x') y y'.
Proof.
intros.
set (m1 := Split m zero x x') in |- *.
generalize H1.
unfold cracke in |- *.
unfold MA0.crack in |- *.
intro.
elim H3.
intros Dx Mex.
unfold MA0.MfcA.expo in H3.
assert (exd m x).
  tauto.
clear H3.
  assert (exd m x').
 generalize (MA0.MfcA.expo_exd m x x').
    tauto.
rename H4 into Ex.
  rename H3 into Ex'.
  assert (cF m1 y = cA_1 m one x').
 unfold m1 in |- *.
   rewrite cF_Split0 in |- *.
  elim (eq_dart_dec (cA m zero x) y).
    tauto.
  unfold y in |- *.
     tauto.
  tauto.
  tauto.
 assert (cA_1 m1 one x' = cA_1 m one x').
  unfold m1 in |- *.
    unfold Split in |- *.
    fold (Shift m zero x) in |- *.
    elim (succ_dec m zero x).
   elim (succ_dec m zero x').
    intros.
      rewrite cA_1_B_ter in |- *.
     assert (one = dim_opp zero).
      simpl in |- *.
         tauto.
     rewrite H3 in |- *.
       apply cA_1_Shift_ter.
       tauto.
      tauto.
    fold (Shift m zero x) in |- *.
      apply inv_hmap_Shift.
      tauto.
     tauto.
    intro.
      inversion H3.
   intros.
     rewrite cA_1_B_ter in |- *.
     tauto.
    tauto.
   intro.
     inversion H3.
  intros.
    assert (succ m zero x').
   generalize (MA0.crack_succ m x x').
      tauto.
  rewrite cA_1_B_ter in |- *.
    tauto.
   tauto.
  intro.
    inversion H4.
 generalize (exd_cA m zero x).
   fold y in |- *.
    tauto.
unfold m1 in |- *.
  assert (cF m y' = cA_1 m one x').
 unfold cF in |- *.
   unfold y' in |- *.
   rewrite cA_1_cA in |- *.
   tauto.
  tauto.
  tauto.
assert (inv_hmap m1).
 unfold m1 in |- *.
   apply inv_hmap_Split.
    tauto.
assert (expf m1 y (cA_1 m one x')).
 rewrite <- H3 in |- *.
   unfold expf in |- *.
   split.
   tauto.
 unfold MF.expo in |- *.
   split.
  unfold m1 in |- *.
    generalize (exd_Split m zero x x' y).
    assert (exd m y).
   unfold y in |- *.
     generalize (exd_cA m zero x).
      tauto.
   tauto.
 split with 1%nat.
   simpl in |- *.
    tauto.
assert (expf m1 y' (cA_1 m one x')).
 unfold m1 in |- *.
   apply expf_Split0.
   tauto.
  tauto.
  tauto.
 fold y in |- *.
   fold y' in |- *.
    tauto.
 rewrite <- H4 in |- *.
   unfold expf in |- *.
   split.
   tauto.
 unfold MF.expo in |- *.
   split.
  generalize (exd_cA m zero x').
    fold y' in |- *.
     tauto.
 split with 1%nat.
   simpl in |- *.
    tauto.
fold m1 in |- *.
  apply expf_trans with (cA_1 m one x').
  tauto.
apply expf_symm.
   tauto.
Qed.

(* OK: *)

Lemma expf_Split1_crackv: forall (m : fmap) (x x': dart),
  inv_hmap m -> planar m -> crackv m x x' ->
  ~expf m x x' -> expf (Split m one x x') x x'.
Proof.
intros.
set (m1 := Split m one x x') in |- *.
generalize H1.
unfold crackv in |- *.
unfold MA1.crack in |- *.
intro.
elim H3.
intros Dx Mex.
unfold MA1.MfcA.expo in H3.
assert (exd m x).
  tauto.
clear H3.
  assert (exd m x').
 generalize (MA1.MfcA.expo_exd m x x').
    tauto.
rename H4 into Ex.
  rename H3 into Ex'.
  set (x10 := cF_1 m x) in |- *.
  assert (exd m x10).
 unfold x10 in |- *.
   generalize (exd_cF_1 m x).
    tauto.
assert (cF m1 x10 = x').
 unfold m1 in |- *.
   rewrite cF_Split1 in |- *.
  fold x10 in |- *.
    elim (eq_dart_dec x10 x10).
    tauto.
   tauto.
  tauto.
  tauto.
  tauto.
assert (expf m1 x10 x').
 assert (inv_hmap m1).
  unfold m1 in |- *.
    apply inv_hmap_Split.
     tauto.
 assert (expf m1 x10 x').
  unfold expf in |- *.
    split.
    tauto.
  unfold MF.expo in |- *.
    split.
   unfold m1 in |- *.
     generalize (exd_Split m one x x' x10).
      tauto.
  split with 1%nat.
    simpl in |- *.
     tauto.
  tauto.
assert (expf m x10 x).
 unfold expf in |- *.
   split.
   tauto.
 unfold MF.expo in |- *.
   split.
   tauto.
 split with 1%nat.
   simpl in |- *.
   unfold x10 in |- *.
   rewrite cF_cF_1 in |- *.
   tauto.
  tauto.
  tauto.
assert (expf m1 x10 x).
 unfold m1 in |- *.
   apply expf_Split1.
   tauto.
  tauto.
  tauto.
  tauto.
  tauto.
apply expf_trans with x10.
 apply expf_symm.
    tauto.
 tauto.
Qed.

(*====================================================
              UNIFIED cA, cA_1 / Split
====================================================*)

Definition crack(m:fmap)(k:dim)(x x':dart):=
   if eq_dim_dec k zero then cracke m x x' else crackv m x x'.   

Lemma cA_Split:
  forall(m:fmap)(k:dim)(x x':dart)(j:dim)(z:dart),
    inv_hmap m -> 
       crack m k x x' ->
          cA (Split m k x x') j z =
             if eq_dim_dec k j 
             then if eq_dart_dec x z then cA m k x'
                    else if eq_dart_dec x' z then cA m k x
                           else cA m k z
             else cA m j z.
Proof.
   intros. generalize H0. clear H0. 
     unfold crack. 
    induction k. 
       induction j. 
           elim ( eq_dim_dec zero zero). intros.
       rewrite MA0.cA_Split. tauto. 
              tauto. tauto. tauto.
             elim (eq_dim_dec zero one). 
             intro. inversion a. 
          elim ( eq_dim_dec zero zero). intros.
            rewrite MA0.cA_Split_opp. tauto. tauto. tauto.
         elim (eq_dim_dec one zero). intro. inversion a. 
         induction j. 
             elim (eq_dim_dec one zero). tauto. intros. 
            rewrite MA1.cA_Split_opp. tauto. tauto. 
          elim (eq_dim_dec one one). intros.
            rewrite MA1.cA_Split. tauto. tauto. tauto. tauto.
Qed.
    
Lemma cA_1_Split:
  forall(m:fmap)(k:dim)(x x':dart)(j:dim)(z:dart),
    inv_hmap m -> 
       crack m k x x' ->
          cA_1 (Split m k x x') j z =
             if eq_dim_dec k j 
             then if eq_dart_dec (cA m k x) z then x'
                    else if eq_dart_dec (cA m k x') z then x
                           else cA_1 m k z
             else cA_1 m j z.
Proof.
   intros. generalize H0. clear H0. 
     unfold crack. 
    induction k. 
       induction j. 
           elim ( eq_dim_dec zero zero). intros.
       rewrite MA0.cA_1_Split. tauto. 
              tauto. tauto. tauto.
             elim (eq_dim_dec zero one). 
             intro. inversion a. 
          elim ( eq_dim_dec zero zero). intros.
            rewrite MA0.cA_1_Split_opp. tauto. tauto. tauto.
         elim (eq_dim_dec one zero). intro. inversion a. 
         induction j. 
             elim (eq_dim_dec one zero). tauto. intros. 
            rewrite MA1.cA_1_Split_opp. tauto. tauto. 
          elim (eq_dim_dec one one). intros.
            rewrite MA1.cA_1_Split. tauto. tauto. tauto. tauto.
Qed.

(*====================================================
======================================================
                     END
====================================================== 
=====================================================*)



