(*====================================================
======================================================
                 TOPOLOGICAL FMAPS, HMAPS -

                 WITH TAGS AND EMBEDDINGS

                          PART 6:

         MAPS, OPERATIONS, PROPERTIES / B, L_B :

 inv_hmap_B,  inv_hmap_B_L, exd_B, exd_L_B,           
   A_B, cA_B, cA_L_B, F_B, cF_B..., 
   eqc_B, eqc_L_B,
   ndZ_B, ndZ_L_B, ne_B, ne_L_B, nc_B, nc_L_B...
 expf_B0 (FROM expof_B0), expf_B1 (FROM expof_B1...)
======================================================
=====================================================*)

Require Export Del05.

(*=====================================================
       inv_hmap_B_L, exd_B_L, cA_B_L,
          inv_hmap_B, exd_B, cA_B...  
=====================================================*)

(* OK: *)

Lemma inv_hmap_L_B:forall (m:fmap)(k:dim)(x:dart), 
 inv_hmap m -> succ m k x -> 
   inv_hmap (L (B m k x) k x (A m k x)).
Proof.
intros.
simpl in |- *.
unfold prec_L in |- *.
split.
 generalize (inv_hmap_B m k x).
   tauto.
 split.
  generalize (exd_B m k x x).
    generalize (succ_exd m k x).
    tauto.
  split.
   generalize (exd_B m k x (A m k x)).
     generalize (succ_exd_A m k x).
     tauto.
   split.
    unfold succ in |- *.
      rewrite A_B.
     tauto.
     tauto.
    split.
     unfold pred in |- *.
       rewrite A_1_B.
      tauto.
      tauto.
     unfold succ in H0.
       rewrite cA_B.
      elim (eq_dart_dec x x).
       intro.
   apply succ_bottom.
        tauto.
        unfold succ in |- *.
          tauto.
       tauto.
      tauto.
      unfold succ in |- *.
       tauto.
Qed.

(* OK: *)

Lemma exd_L_B:forall (m:fmap)(k:dim)(x z:dart),
 inv_hmap m -> succ m k x -> 
   let y:= A m k x in 
     exd (L (B m k x) k x y) z <-> exd m z. 
Proof.
simpl in |- *.
intros.
generalize (exd_B m k x z).
tauto.
Qed.

(* OK: *)

Lemma A_L_B:forall (m:fmap)(k j:dim)(x z:dart),
 inv_hmap m -> succ m k x -> 
   let y:= A m k x in 
     A (L (B m k x) k x y) j z = A m j z. 
Proof.
induction m.
 simpl in |- *.
   intros.
   unfold succ in H0.
   simpl in H0.
   tauto.
 simpl in |- *.
   unfold prec_I in |- *.
   unfold succ in |- *.
   intros.
   elim (eq_dim_dec k j).
  elim (eq_dart_dec x z).
   intro.
     rewrite a.
     intro.
     rewrite a0.
     tauto.
   intros.
     rewrite a.
     rewrite A_B_bis.
    tauto.
    intro.
      symmetry  in H1.
      tauto.
  intro.
    rewrite A_B_ter.
   tauto.
   tauto.
 simpl in |- *.
   unfold prec_L in |- *.
   unfold succ in |- *.
   unfold pred in |- *.
   intros.
   elim (eq_dim_dec k j).
  elim (eq_dim_dec d k).
   intros.
     rewrite a.
     rewrite a0.
     elim (eq_dim_dec j j).
    intro.
      elim (eq_dart_dec x z).
     intro.
       rewrite a2.
       tauto.
     elim (eq_dart_dec d0 x).
      elim (eq_dart_dec d0 z).
       intros.
         rewrite a3 in a2.
         tauto.
       tauto.
      simpl in |- *.
        elim (eq_dim_dec j j).
       intros.
         rewrite A_B_bis.
        tauto.
        intro.
          symmetry  in H1.
          tauto.
       tauto.
    tauto.
   simpl in |- *.
     elim (eq_dart_dec x z).
    intros.
      rewrite <- a0.
      elim (eq_dim_dec d k).
     tauto.
     rewrite a.
       tauto.
    intros.
      rewrite <- a.
      rewrite A_B_bis.
     tauto.
     intro.
       symmetry  in H1.
       tauto.
  elim (eq_dim_dec d k).
   elim (eq_dim_dec d j).
    intros.
      rewrite a0 in a.
      tauto.
    elim (eq_dart_dec d0 x).
     tauto.
     simpl in |- *.
       elim (eq_dim_dec d j).
      tauto.
      intros.
        rewrite A_B_ter.
       tauto.
       tauto.
   simpl in |- *.
     intros.
     rewrite A_B_ter.
    tauto.
    tauto.
Qed.

(* IDEM: *)

Lemma A_1_L_B:forall (m:fmap)(k j:dim)(x z:dart),
 inv_hmap m -> succ m k x -> 
   let y:= A m k x in 
     A_1 (L (B m k x) k x y) j z = A_1 m j z. 
Proof.
induction m.
 simpl in |- *.
   intros.
   unfold succ in H0.
   simpl in H0.
    tauto.
simpl in |- *.
  unfold prec_I in |- *.
  unfold succ in |- *.
  intros.
  elim (eq_dim_dec k j).
 elim (eq_dart_dec (A m k x) z).
  intro.
    rewrite <- a in |- *.
    intro.
    rewrite <- a0 in |- *.
    rewrite A_1_A in |- *.
   auto.
   tauto.
  simpl in H0; unfold succ in |- *.
     tauto.
 intros.
   simpl in H0.
   rewrite <- a in |- *.
   rewrite A_1_B_bis in |- *.
  auto.
 auto.
    tauto.
 intro.
   symmetry  in H1.
    tauto.
simpl in H0.
  intro.
  rewrite A_1_B_ter in |- *.
  tauto.
 tauto.
simpl in |- *.
  unfold prec_L in |- *.
  unfold succ in |- *.
  unfold pred in |- *.
  intros.
  simpl in H0.
  generalize H0.
  clear H0.
  elim (eq_dim_dec k j).
 elim (eq_dim_dec d k).
  intros a b.
    rewrite a in |- *.
    rewrite <- b in |- *.
    rewrite a in H.
    elim (eq_dart_dec d0 x).
   elim (eq_dart_dec d1 z).
    elim (eq_dim_dec k k).
     symmetry  in |- *.
        tauto.
     tauto.
   elim (eq_dim_dec k k).
     tauto.
    tauto.
  elim (eq_dart_dec (A m k x) z).
   elim (eq_dim_dec k k).
    elim (eq_dart_dec d1 z).
     intros.
       rewrite <- a0 in a2.
       rewrite <- a2 in H.
       rewrite A_1_A in H.
       absurd (x <> nil).
        tauto.
      apply exd_not_nil with m.
        tauto.
      apply succ_exd with k.
        tauto.
      unfold succ in |- *.
         tauto.
      tauto.
     unfold succ in |- *.
        tauto.
    intros.
      rewrite <- a1 in |- *.
      rewrite A_1_A in |- *.
      tauto.
     tauto.
    unfold succ in |- *.
       tauto.
    tauto.
  simpl in |- *.
    elim (eq_dim_dec k k).
   elim (eq_dart_dec d1 z).
     tauto.
   intros.
     rewrite A_1_B_bis in |- *.
     tauto.
    tauto.
   intro.
     symmetry  in H1.
      tauto.
   tauto.
 elim (eq_dart_dec (A m k x) z).
  elim (eq_dim_dec d j).
   elim (eq_dart_dec d1 z).
    intros.
      rewrite <- a2 in a0.
       tauto.
   intros.
     rewrite <- a1 in |- *.
     rewrite <- a0 in |- *.
     rewrite A_1_A in |- *.
     tauto.
    tauto.
   unfold succ in |- *.
      tauto.
  intros.
    rewrite <- a0 in |- *.
    rewrite <- a in |- *.
    rewrite A_1_A in |- *.
    tauto.
   tauto.
  unfold succ in |- *.
     tauto.
 simpl in |- *.
   intros.
   elim (eq_dim_dec d j).
  intro.
    rewrite <- a in a0.
     tauto.
 intro.
   rewrite <- a in |- *.
   rewrite A_1_B_bis in |- *.
   tauto.
  tauto.
 intro.
   symmetry  in H1.
    tauto.
elim (eq_dim_dec d k).
 elim (eq_dart_dec d0 x).
  elim (eq_dim_dec d j).
   intros.
     rewrite a1 in a.
      tauto.
   tauto.
 simpl in |- *.
   elim (eq_dim_dec d j).
  intros.
    rewrite a0 in a.
     tauto.
 intros.
   rewrite A_1_B_ter in |- *.
   tauto.
  tauto.
simpl in |- *.
  elim (eq_dim_dec d j).
 elim (eq_dart_dec d1 z).
   tauto.
 intros.
   rewrite A_1_B_ter in |- *.
   tauto.
  tauto.
intros.
  rewrite A_1_B_ter in |- *.
  tauto.
 tauto.
Qed.

(* OK: *)

Lemma F_L_B:forall (m:fmap)(k:dim)(x z:dart),
 inv_hmap m -> succ m k x -> 
   let y:= A m k x in 
     F (L (B m k x) k x y) z = F m z. 
Proof.
intros.
unfold F in |- *.
unfold y in |- *.
rewrite A_1_L_B.
 rewrite A_1_L_B.
  tauto.
  tauto.
  tauto.
 tauto.
 tauto.
Qed.

(* OK!! *)

Lemma cA_L_B:forall (m:fmap)(k j:dim)(x z:dart),
 inv_hmap m -> succ m k x -> 
   let y:= A m k x in 
     cA (L (B m k x) k x y) j z = cA m j z. 
Proof.
simpl in |- *.
intros.
elim (eq_dim_dec k j).
 intro.
   elim (eq_dart_dec x z).
  rewrite a.
    intro.
    rewrite a0.
    rewrite a0 in H0.
    generalize (A_cA m j z (A m j z)).
    intros.
    symmetry  in |- *.
    apply H1.
   tauto.
   apply succ_exd with k.
    tauto.
    tauto.
   apply succ_exd_A.
    tauto.
    rewrite <- a.
      tauto.
   tauto.
  intro.
    elim (eq_dart_dec (cA_1 (B m k x) j (A m k x)) z).
   intro.
     rewrite <- a.
     rewrite <- a in a0.
     rewrite cA_1_B in a0.
    generalize a0.
      clear a0.
      elim (eq_dart_dec (A m k x) (A m k x)).
     intros.
       rewrite <- a1.
       rewrite cA_top.
      rewrite cA_B.
       elim (eq_dart_dec x x).
        tauto.
        tauto.
       tauto.
       tauto.
      tauto.
      apply succ_exd with k.
       tauto.
       tauto.
     tauto.
    tauto.
    tauto.
   intro.
     rewrite <- a.
     rewrite cA_B.
    elim (eq_dart_dec x z).
     tauto.
     intro.
       elim (eq_dart_dec (top m k x) z).
      intro.
        rewrite <- a in b0.
        rewrite cA_1_B in b0.
       generalize b0.
         elim (eq_dart_dec (A m k x) (A m k x)).
        tauto.
        tauto.
       tauto.
       tauto.
      tauto.
    tauto.
    tauto.
 intro.
   rewrite cA_B_ter.
  tauto.
  tauto.
  tauto.
Qed.

(* IDEM: *)

Lemma cA_1_L_B:forall(m : fmap)(k j : dim)(x z : dart),
 inv_hmap m -> succ m k x -> 
   let y:= A m k x in 
     cA_1 (L (B m k x) k x y) j z = cA_1 m j z. 
Proof.
simpl in |- *.
intros.
elim (eq_dim_dec k j).
 intro.
   elim (eq_dart_dec (A m k x) z).
  rewrite a in |- *.
    intro.
    rewrite <- a0 in |- *.
    assert (cA m j x = A m j x).
   apply A_cA.
     tauto.
   apply succ_exd with k.
     tauto.
    tauto.
   rewrite <- a in |- *.
     apply succ_exd_A.
     tauto.
    tauto.
    tauto.
  rewrite <- H1 in |- *.
    rewrite cA_1_cA in |- *.
    tauto.
   tauto.
  apply succ_exd with k.
    tauto.
   tauto.
 elim (eq_dart_dec (cA (B m k x) j x) z).
  intros.
    rewrite <- a in |- *.
    rewrite cA_1_B in |- *.
   elim (eq_dart_dec (A m k x) (A m k x)).
    intros.
      generalize a0.
      clear a0.
      rewrite <- a in |- *.
      rewrite cA_B in |- *.
     elim (eq_dart_dec x x).
      intros.
        rewrite <- a2 in |- *.
        rewrite cA_1_bottom in |- *.
        tauto.
       tauto.
      apply succ_exd with k.
        tauto.
       tauto.
      tauto.
     tauto.
     tauto.
    tauto.
   tauto.
   tauto.
 intros.
   rewrite <- a in |- *.
   rewrite cA_1_B in |- *.
  elim (eq_dart_dec (A m k x) z).
    tauto.
  elim (eq_dart_dec (bottom m k x) z).
   intros.
     rewrite <- a in b.
     rewrite cA_B in b.
    generalize b.
      elim (eq_dart_dec x x).
      tauto.
     tauto.
    tauto.
   unfold succ in |- *.
     unfold succ in H0.
      tauto.
   tauto.
  tauto.
  tauto.
intro.
  rewrite cA_1_B_ter in |- *.
  tauto.
 tauto.
 tauto.
Qed.

Lemma cF_L_B:forall (m:fmap)(k:dim)(x z:dart),
 inv_hmap m -> succ m k x -> 
   let y:= A m k x in 
     cF (L (B m k x) k x y) z = cF m z. 
Proof.
  intros.
  unfold cF.
rewrite cA_1_L_B.
 rewrite cA_1_L_B.
  tauto.
  tauto.
  tauto.
 tauto.
 tauto.
Qed.

(* WITH Iter: *)

Lemma Iter_cF_L_B:
 forall (m:fmap)(k:dim)(x:dart)(i:nat)( z:dart),
  inv_hmap m -> succ m k x -> 
   let y:= A m k x in 
    Iter (cF (L (B m k x) k x (A m k x))) i z
      =   Iter (cF m) i z.
Proof.
 intros.
induction i.
 simpl in |- *.
   tauto.
   unfold Iter; fold Iter.
   rewrite IHi.
   rewrite cF_L_B.
  tauto.
  tauto.
tauto.
Qed. 

Definition expofo(m:fmap)(x:dart)(z t:dart):=
  expf (L (B m zero x) zero x (A m zero x)) z t.
 
Lemma expofo_expf:forall(m:fmap)(x:dart)(z t:dart),
  inv_hmap m -> succ m zero x ->
    (expofo m x z t <-> expf m z t).
Proof.
unfold expofo in |- *.
unfold expf in |- *.
unfold MF.expo in |- *.
simpl in |- *.
unfold prec_L in |- *.
unfold succ in |- *.
unfold pred in |- *.
intros.
unfold MF.f in |- *.
unfold McF.f in |- *.
assert (exd m x).
 apply succ_exd with zero.
  tauto.
  unfold succ in |- *.
    tauto.
 split.
  intros.
    decompose [and] H2.
    clear H2.
    split.
   tauto.
   generalize (exd_B m zero x z).
     split.
    tauto.
    elim H11.
      intros i Hi.
      split with i.
      rewrite Iter_cF_L_B in Hi.
     tauto.
     tauto.
     tauto.
  unfold succ in |- *.
    intro.
    decompose [and] H2.
    clear H2.
    split.
   split.
    apply inv_hmap_B.
      tauto.
    split.
     generalize (exd_B m zero x x).
       tauto.
     split.
      generalize (exd_B m zero x (A m zero x)).
        assert (exd m (A m zero x)).
       apply succ_exd_A.
        tauto.
        tauto.
       tauto.
      split.
       rewrite A_B.
        tauto.
        tauto.
       split.
        rewrite A_1_B.
         tauto.
         tauto.
        rewrite cA_B.
         elim (eq_dart_dec x x).
          intro.
            apply succ_bottom.
           tauto.
           unfold succ in |- *.
             tauto.
          tauto.
         tauto.
         unfold succ in |- *.
           tauto.
   split.
    generalize (exd_B m zero x z).
      tauto.
    elim H6.
      intros i Hi.
      split with i.
      rewrite Iter_cF_L_B.
     tauto.
     tauto.
     tauto.
Qed.

(*=====================================================
                eqc_B : eqc on B, L_B 
=====================================================*)

(* OK: LONG... *)

Lemma eqc_B_CN: forall(m:fmap)(k:dim)(x z t:dart),
 inv_hmap m -> succ m k x ->
  let xk:= A m k x in
  let m0:= B m k x in
    eqc m z t -> 
      (eqc m0 z t \/ 
       eqc m0 z x /\ eqc m0 xk t \/ 
       eqc m0 z xk /\ eqc m0 x t).
Proof.
induction m.
 simpl in |- *.
   unfold succ in |- *.
   simpl in |- *.
   tauto.
 rename t into u.
 unfold succ in |- *.
   simpl in |- *.
   intros.
   unfold succ in IHm.
   intros.
   unfold prec_I in H.
   decompose [and] H.
   clear H.
   generalize (IHm k x z t H2 H0).
   intros.
   intuition.
 unfold succ in |- *.
   simpl in |- *.
   unfold prec_L in |- *.
   intros.
   generalize H0.
   clear H0.
   decompose [and] H.
   clear H.
   rename d into j.
   elim (eq_dim_dec j k).
  elim (eq_dart_dec d0 x).
   intros.
     rewrite <- a.
     tauto.
   simpl in |- *.
     intros.
     unfold succ in IHm.
     elim H1.
    intro.
      generalize (IHm k x z t H0 H6 H).
      tauto.
    intro.
      elim H.
     intros.
       decompose [and] H8.
       clear H8.
       clear H1.
       generalize (IHm k x z d0 H0 H6 H9).
       generalize (IHm k x d1 t H0 H6 H10).
       intros.
       elim H1.
      elim H8.
       intros.
         tauto.
       intros.
         elim H11.
        intros.
          clear H11.
          tauto.
        intro.
          clear H11.
          tauto.
      intros.
        elim H11.
       clear H11.
         intro.
         elim H8.
        intro.
          tauto.
        intro.
          elim H12.
         clear H12.
           intro.
           tauto.
         intro.
           clear H12.
           assert (eqc (B m k x) z t).
          apply eqc_trans with (A m k x).
           tauto.
           tauto.
          tauto.
       intro.
         clear H11.
         elim H8.
        intro.
          tauto.
        intro.
          elim H11.
         clear H11.
           intro.
           assert (eqc (B m k x) z t).
          apply eqc_trans with x.
           tauto.
           tauto.
          tauto.
         intro.
           clear H11.
           tauto.
     intro.
       clear H.
       clear H1.
       decompose [and] H8.
       clear H8.
       generalize (IHm k x z d1 H0 H6 H).
       generalize (IHm k x d0 t H0 H6 H1).
       intros.
       elim H8.
      intro.
        elim H9.
       intro.
         tauto.
       intro.
         elim H11.
        clear H11.
          intro.
          tauto.
        clear H11.
          intro.
          tauto.
      intro.
        elim H10.
       clear H10.
         intro.
         elim H9.
        intro.
          tauto.
        intro.
          elim H11.
         clear H11.
           intro.
           tauto.
         clear H11.
           intro.
           assert (eqc (B m k x) z t).
          apply eqc_trans with (A m k x).
           tauto.
           tauto.
          tauto.
       intro.
         clear H10.
         elim H9.
        intro.
          tauto.
        intro.
          elim H10.
         clear H10.
           intro.
           assert (eqc (B m k x) z t).
          apply eqc_trans with x.
           tauto.
           tauto.
          tauto.
         elim H10.
          clear H10.
            intro.
            tauto.
          tauto.
  simpl in |- *.
    intros.
    unfold succ in IHm.
    elim H1.
   intro.
     generalize (IHm k x z t H0 H6 H).
     tauto.
   intro.
     elim H.
    intros.
      decompose [and] H8.
      clear H8.
      clear H1.
      generalize (IHm k x z d0 H0 H6 H9).
      generalize (IHm k x d1 t H0 H6 H10).
      intros.
      elim H1.
     elim H8.
      intros.
        tauto.
      intros.
        elim H11.
       intros.
         clear H11.
         tauto.
       intro.
         clear H11.
         tauto.
     intros.
       elim H11.
      clear H11.
        intro.
        elim H8.
       intro.
         tauto.
       intro.
         elim H12.
        clear H12.
          intro.
          tauto.
        intro.
          clear H12.
          assert (eqc (B m k x) z t).
         apply eqc_trans with (A m k x).
          tauto.
          tauto.
         tauto.
      intro.
        clear H11.
        elim H8.
       intro.
         tauto.
       intro.
         elim H11.
        clear H11.
          intro.
          assert (eqc (B m k x) z t).
         apply eqc_trans with x.
          tauto.
          tauto.
         tauto.
        intro.
          clear H11.
          tauto.
    intro.
      clear H.
      clear H1.
      decompose [and] H8.
      clear H8.
      generalize (IHm k x z d1 H0 H6 H).
      generalize (IHm k x d0 t H0 H6 H1).
      intros.
      elim H8.
     intro.
       elim H9.
      intro.
        tauto.
      intro.
        elim H11.
       clear H11.
         intro.
         tauto.
       clear H11.
         intro.
         tauto.
     intro.
       elim H10.
      clear H10.
        intro.
        elim H9.
       intro.
         tauto.
       intro.
         elim H11.
        clear H11.
          intro.
          tauto.
        clear H11.
          intro.
          assert (eqc (B m k x) z t).
         apply eqc_trans with (A m k x).
          tauto.
          tauto.
         tauto.
      intro.
        clear H10.
        elim H9.
       intro.
         tauto.
       intro.
         elim H10.
        clear H10.
          intro.
          assert (eqc (B m k x) z t).
         apply eqc_trans with x.
          tauto.
          tauto.
         tauto.
        elim H10.
         clear H10.
           intro.
           tauto.
         tauto.
Qed.

(* OK! IDEM *)

Lemma eqc_B_CS: forall(m:fmap)(k:dim)(x z t:dart),
 inv_hmap m -> succ m k x ->
  let xk:= A m k x in
  let m0:= B m k x in 
      (eqc m0 z t \/ 
       eqc m0 z x /\ eqc m0 xk t \/ 
       eqc m0 z xk /\ eqc m0 x t) ->
    eqc m z t.
Proof.
induction m.
 simpl in |- *.
   unfold succ in |- *.
   simpl in |- *.
   tauto.
  rename t into u.
 unfold succ in |- *.
   simpl in |- *.
   intros.
   unfold prec_I in H.
   decompose [and] H.
   clear H.
   generalize (IHm k x z t H2 H0).
   simpl in |- *.
   intros.
   assert (x <> d).
  intro.
    rewrite <- H3 in H5.
    apply H5.
    apply succ_exd with k.
   tauto.
   tauto.
  assert (A m k x <> d).
   intro.
     rewrite <- H6 in H5.
     elim H5.
     apply succ_exd_A.
    tauto.
    unfold succ in |- *.
      tauto.
   intuition.
 unfold succ in |- *.
   simpl in |- *.
   unfold prec_L in |- *.
   intros k x z t H.
   unfold succ in IHm.
   decompose [and] H.
   clear H.
   rename d into j.
   elim (eq_dim_dec j k).
  elim (eq_dart_dec d0 x).
   intros.
     rewrite a.
     tauto.
   simpl in |- *.
     intros.
     rewrite a in H6.
     elim H5.
    intro.
      elim H7.
     generalize (IHm k x z t H0 H).
       tauto.
     intro.
       elim H8.
      intro.
        generalize (IHm k x z d0 H0 H).
        generalize (IHm k x d1 t H0 H).
        tauto.
      intro.
        clear H8.
        generalize (IHm k x z d1 H0 H).
        generalize (IHm k x d0 t H0 H).
        tauto.
    clear H5.
      intro.
      elim H5.
     clear H5.
       intro.
       decompose [and or] H5.
      clear H5.
        generalize (IHm k x z t H0 H).
        tauto.
      generalize (IHm k x z d0 H0 H).
        generalize (IHm k x d1 t H0 H).
        tauto.
      generalize (IHm k x z d1 H0 H).
        generalize (IHm k x d0 t H0 H).
        tauto.
      generalize (IHm k x z d0 H0 H).
        generalize (IHm k x d1 t H0 H).
        tauto.
      generalize (IHm k x d1 t H0 H).
        generalize (IHm k x z d0 H0 H).
        tauto.
      assert (eqc (B m k x) z t).
       apply eqc_trans with d0.
        tauto.
        tauto.
       generalize (IHm k x z t H0 H).
         tauto.
      generalize (IHm k x z d1 H0 H).
        generalize (IHm k x d0 t H0 H).
        tauto.
      assert (eqc (B m k x) z t).
       apply eqc_trans with d1.
        tauto.
        tauto.
       generalize (IHm k x z t H0 H).
         tauto.
      generalize (IHm k x z d1 H0 H).
        generalize (IHm k x d0 t H0 H).
        tauto.
     intro.
       clear H5.
       intuition.
      generalize (IHm k x z t H0 H).
        tauto.
      generalize (IHm k x z d0 H0 H).
        generalize (IHm k x d1 t H0 H).
        tauto.
      generalize (IHm k x z d1 H0 H).
        generalize (IHm k x d0 t H0 H).
        tauto.
      generalize (IHm k x z d0 H0 H).
        generalize (IHm k x d1 t H0 H).
        tauto.
      generalize (IHm k x z d1 H0 H).
        generalize (IHm k x d0 t H0 H).
        tauto.
      generalize (IHm k x d1 t H0 H).
        generalize (IHm k x z d0 H0 H).
        tauto.
      assert (eqc (B m k x) z t).
       apply eqc_trans with d0.
        tauto.
        tauto.
       generalize (IHm k x z t H0 H).
         tauto.
      assert (eqc (B m k x) z t).
       apply eqc_trans with d1.
        tauto.
        tauto.
       generalize (IHm k x z t H0 H).
         tauto.
      generalize (IHm k x z d1 H0 H).
        generalize (IHm k x d0 t H0 H).
        tauto.
  simpl in |- *.
    intros.
    elim H5.
   intro.
     elim H7.
    generalize (IHm k x z t H0 H).
      tauto.
    intro.
      elim H8.
     intro.
       generalize (IHm k x z d0 H0 H).
       generalize (IHm k x d1 t H0 H).
       tauto.
     intro.
       clear H8.
       generalize (IHm k x z d1 H0 H).
       generalize (IHm k x d0 t H0 H).
       tauto.
   clear H5.
     intro.
     elim H5.
    clear H5.
      intro.
      decompose [and or] H5.
     clear H5.
       generalize (IHm k x z t H0 H).
       tauto.
     generalize (IHm k x z d0 H0 H).
       generalize (IHm k x d1 t H0 H).
       tauto.
     generalize (IHm k x z d1 H0 H).
       generalize (IHm k x d0 t H0 H).
       tauto.
     generalize (IHm k x z d0 H0 H).
       generalize (IHm k x d1 t H0 H).
       tauto.
     generalize (IHm k x d1 t H0 H).
       generalize (IHm k x z d0 H0 H).
       tauto.
     assert (eqc (B m k x) z t).
      apply eqc_trans with d0.
       tauto.
       tauto.
      generalize (IHm k x z t H0 H).
        tauto.
     generalize (IHm k x z d1 H0 H).
       generalize (IHm k x d0 t H0 H).
       tauto.
     assert (eqc (B m k x) z t).
      apply eqc_trans with d1.
       tauto.
       tauto.
      generalize (IHm k x z t H0 H).
        tauto.
     generalize (IHm k x z d1 H0 H).
       generalize (IHm k x d0 t H0 H).
       tauto.
    intro.
      clear H5.
      intuition.
     generalize (IHm k x z t H0 H).
       tauto.
     generalize (IHm k x z d0 H0 H).
       generalize (IHm k x d1 t H0 H).
       tauto.
     generalize (IHm k x z d1 H0 H).
       generalize (IHm k x d0 t H0 H).
       tauto.
     generalize (IHm k x z d0 H0 H).
       generalize (IHm k x d1 t H0 H).
       tauto.
     generalize (IHm k x z d1 H0 H).
       generalize (IHm k x d0 t H0 H).
       tauto.
     generalize (IHm k x d1 t H0 H).
       generalize (IHm k x z d0 H0 H).
       tauto.
     assert (eqc (B m k x) z t).
      apply eqc_trans with d0.
       tauto.
       tauto.
      generalize (IHm k x z t H0 H).
        tauto.
     assert (eqc (B m k x) z t).
      apply eqc_trans with d1.
       tauto.
       tauto.
      generalize (IHm k x z t H0 H).
        tauto.
     generalize (IHm k x z d1 H0 H).
       generalize (IHm k x d0 t H0 H).
       tauto.
Qed.

(* OK: *)

Theorem eqc_B: forall(m:fmap)(k:dim)(x z t:dart),
 inv_hmap m -> succ m k x ->
  let xk:= A m k x in
  let m0:= B m k x in
    (eqc m z t <-> 
      (eqc m0 z t \/ 
       eqc m0 z x /\ eqc m0 xk t \/ 
       eqc m0 z xk /\ eqc m0 x t)).
Proof.
simpl in |- *.
intros.
split.
 apply eqc_B_CN.
  tauto.
  tauto.
 apply eqc_B_CS.
  tauto.
  tauto.
Qed.

(* DEFINITION OF eqco WHICH ALLOWS TO PUT AHEAD 
ANY 0-LINK: *)

Definition eqco(m:fmap)(k:dim)(x z t:dart):=
  eqc (L (B m k x) k x (A m k x)) z t.

Lemma eqco_eqc:forall(m:fmap)(k:dim)(x z t:dart),
  inv_hmap m -> succ m k x ->
    (eqco m k x z t <-> eqc m z t).
Proof.
unfold eqco in |- *.
simpl in |- *.
intros.
generalize (eqc_B m k x z t H H0).
simpl in |- *.
tauto.
Qed.

(* OK: *)

Lemma eqc_B_eqc :forall(m:fmap)(k:dim)(x z t:dart),
  inv_hmap m -> succ m k x ->
    eqc (B m k x) z t -> eqc m z t.
Proof.
unfold succ in |- *.
induction m.
 simpl in |- *.
   tauto.
rename t into u.
 simpl in |- *.
   unfold prec_I in |- *.
   intros.
   decompose [and] H.
   clear H.
   elim H1.
  intro.
    tauto.
  intro.
    right.
    apply (IHm k x z t H2 H0 H).
 simpl in |- *.
   unfold prec_L in |- *.
   intros k x z t H.
   decompose [and] H.
   clear H.
   rename d into j.
   elim (eq_dim_dec j k).
  elim (eq_dart_dec d0 x).
   intros.
     tauto.
   simpl in |- *.
     intros.
     intuition.
    left.
      apply (IHm k x z t).
     tauto.
     tauto.
     tauto.
    right.
      left.
      generalize (IHm k x z d0 H0 H).
      generalize (IHm k x d1 t H0 H).
      tauto.
    generalize (IHm k x z d1 H0 H).
      generalize (IHm k x d0 t H0 H).
      tauto.
  simpl in |- *.
    intros.
    generalize (IHm k x z d0 H0 H).
    generalize (IHm k x d1 t H0 H).
    generalize (IHm k x z d1 H0 H).
    generalize (IHm k x d0 t H0 H).
    generalize (IHm k x z t H0 H).
    tauto.
Qed.

(* OK, USEFUL IN nc/B,L: *)

Lemma eqc_eqc_B : forall(m:fmap)(k:dim)(x z t:dart),
  inv_hmap m -> succ m k x ->
     eqc (B m k x) x (A m k x) -> 
        eqc m z t -> eqc (B m k x) z t.
Proof.
intros.
generalize (eqc_B_CN m k x z t H H0 H2).
intro.
elim H3.
  tauto.
clear H3.
  intro.
  elim H3.
 clear H3.
   intro.
   apply eqc_trans with x.
   tauto.
 apply eqc_trans with (A m k x).
   tauto.
  tauto.
clear H3.
  intro.
   eapply eqc_trans with (A m k x).
  tauto.
apply eqc_trans with x.
 apply eqc_symm.
    tauto.
 tauto.
Qed.

Lemma ndZ_B:forall (m:fmap)(k:dim)(x:dart),
  inv_hmap m -> succ m k x ->
    nd (B m k x) = nd m.
Proof.
intros.
simpl in |- *.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   unfold succ in |- *.
   simpl in |- *.
   intros.
   unfold succ in IHm.
   unfold succ in H0.
   simpl in H0.
   assert (nd (B m k x) = nd m).
  apply IHm.
   simpl in H.
     tauto.
   tauto.
  lia.
 simpl in |- *.
   unfold succ in H0.
   simpl in H0.
   generalize H0.
   clear H0.
   simpl in H.
   elim (eq_dim_dec d k).
  elim (eq_dart_dec d0 x).
   tauto.
   simpl in |- *.
     intros.
     apply IHm.
    tauto.
    tauto.
  simpl in |- *.
    intro.
    apply IHm.
    tauto.
Qed.

Lemma ndZ_L_B:forall (m:fmap)(k:dim)(x:dart),
  inv_hmap m -> succ m k x ->
   let m1:= L (B m k x) k x (A m k x) in
      nd m1 = nd m.
Proof.
simpl in |- *.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   unfold succ in |- *.
   simpl in |- *.
   intros.
   unfold succ in IHm.
   assert (nd (B m k x) = nd m).
  apply IHm.
   tauto.
   tauto.
  lia.
 simpl in |- *.
   unfold succ in |- *.
   unfold succ in IHm.
   unfold prec_L in |- *.
   simpl in |- *.
   intros k x H.
   elim (eq_dim_dec d k).
  elim (eq_dart_dec d0 x).
   tauto.
   simpl in |- *.
     intros.
     apply IHm.
    tauto.
    tauto.
  simpl in |- *.
    intro.
    apply IHm.
    tauto.
Qed.

Lemma ne_B:forall (m:fmap)(k:dim)(x:dart),
  inv_hmap m -> succ m k x ->
    ne (B m k x) = ne m + 
      if (eq_dim_dec k zero) then 1 else 0.
Proof.
intros.
induction m.
 unfold succ in H0.
   simpl in H0.
   tauto.
 unfold succ in H0.
   simpl in H0.
   simpl in |- *.
   simpl in H.
   assert (ne (B m k x) =
 ne m + (if eq_dim_dec k zero then 1 else 0)).
  apply IHm.
   tauto.
   unfold succ in |- *.
     tauto.
  lia.
 simpl in H.
   unfold succ in H0.
   simpl in H0.
   generalize H0.
   clear H0.
   induction k.
  simpl in |- *.
    elim (eq_dim_dec d zero).
   elim (eq_dart_dec d0 x).
    intros.
      induction d.
     lia.
     inversion a0.
    simpl in |- *.
      intros.
      induction d.
     unfold succ in IHm.
       assert
        (ne (B m zero x) = 
  ne m + (if eq_dim_dec zero zero then 1 else 0)).
      apply IHm.
       tauto.
       tauto.
      generalize H1.
        clear H1.
        elim (eq_dim_dec zero zero).
       intros.
         lia.
       tauto.
     inversion a.
   simpl in |- *.
     induction d.
    tauto.
    intros.
      assert
       (ne (B m zero x) = 
  ne m + (if eq_dim_dec zero zero then 1 else 0)).
     apply IHm.
      tauto.
      unfold succ in |- *.
        tauto.
     generalize H1.
       clear H1.
       elim (eq_dim_dec zero zero).
      tauto.
      tauto.
  simpl in |- *.
    elim (eq_dim_dec d one).
   elim (eq_dart_dec d0 x).
    elim d.
     intros.
       inversion a0.
     intros.
       lia.
    simpl in |- *.
      intros.
      elim d.
     assert (ne (B m one x) = 
  ne m + (if eq_dim_dec one zero then 1 else 0)).
      apply IHm.
       tauto.
       unfold succ in |- *.
         tauto.
      generalize H1.
        elim (eq_dim_dec one zero).
       intro.
         inversion a0.
       intros.
         lia.
     assert (ne (B m one x) = 
  ne m + (if eq_dim_dec one zero then 1 else 0)).
      apply IHm.
       tauto.
       unfold succ in |- *.
         tauto.
      generalize H1.
        elim (eq_dim_dec one zero).
       intro.
         inversion a0.
       tauto.
   simpl in |- *.
     intros.
     elim d.
    assert (ne (B m one x) = 
  ne m + (if eq_dim_dec one zero then 1 else 0)).
     apply IHm.
      tauto.
      unfold succ in |- *.
        tauto.
     generalize H1.
       elim (eq_dim_dec one zero).
      intro.
        inversion a.
      intros.
        lia.
    assert (ne (B m one x) = 
  ne m + (if eq_dim_dec one zero then 1 else 0)).
     apply IHm.
      tauto.
      unfold succ in |- *.
        tauto.
     generalize H1.
       elim (eq_dim_dec one zero).
      intro.
        inversion a.
      intros.
        lia.
Qed.

Lemma ne_L_B:forall (m:fmap)(k:dim)(x:dart),
  inv_hmap m -> succ m k x ->
   let m1 := L (B m k x) k x (A m k x) in
      ne m1 = ne m.
Proof.
simpl in |- *.
intros.
generalize (ne_B m k x H H0).
induction k.
 elim (eq_dim_dec zero zero).
  intros.
    lia.
  tauto.
 elim (eq_dim_dec one zero).
  intro.
    inversion a.
  intros.
    lia.
Qed.

Lemma nv_B:forall (m:fmap)(k:dim)(x:dart),
  inv_hmap m -> succ m k x ->
    nv (B m k x) = nv m + 
      if (eq_dim_dec k one) then 1 else 0.
Proof.
intros.
induction m.
 unfold succ in H0.
   simpl in H0.
   tauto.
 unfold succ in H0.
   simpl in H0.
   simpl in |- *.
   simpl in H.
   assert (nv (B m k x) =
 nv m + (if eq_dim_dec k one then 1 else 0)).
  apply IHm.
   tauto.
   unfold succ in |- *.
     tauto.
  lia.
 simpl in H.
   unfold succ in H0.
   simpl in H0.
   generalize H0.
   clear H0.
   simpl in |- *.
   elim (eq_dim_dec d k).
  intro.
    elim (eq_dart_dec d0 x).
   intros.
     rewrite a.
     elim k.
    elim (eq_dim_dec zero one).
     intro.
       inversion a1.
     intro.
       lia.
    elim (eq_dim_dec one one).
     intro.
       lia.
     tauto.
   simpl in |- *.
     intros H1 H2.
     assert (nv (B m k x) = 
 nv m + (if eq_dim_dec k one then 1 else 0)).
    apply IHm.
     tauto.
     unfold succ in |- *.
       tauto.
    generalize H0.
      clear H0.
      rewrite a.
      rewrite a in H.
      induction k.
     tauto.
     intros.
       lia.
  simpl in |- *.
    intros H1 H2.
    elim d.
   apply IHm.
    tauto.
    unfold succ in |- *.
      tauto.
   assert (nv (B m k x) = 
  nv m + (if eq_dim_dec k one then 1 else 0)).
    apply IHm.
     tauto.
     unfold succ in |- *.
       tauto.
    lia.
Qed.

Lemma nv_L_B:forall (m:fmap)(k:dim)(x:dart),
  inv_hmap m -> succ m k x ->
   let m1 := L (B m k x) k x (A m k x) in
      nv m1 = nv m.
Proof.
intros.
generalize (nv_B m k x H H0).
induction k.
 elim (eq_dim_dec zero one).
  unfold m1 in |- *.
    intro.
    inversion a.
  unfold m1 in |- *.
    simpl in |- *.
    intros.
    lia.
 unfold m1 in |- *.
   simpl in |- *.
   intros.
   lia.
Qed.

(* OK: *)

Lemma nc_B:forall(m:fmap)(k:dim)(x:dart),
  inv_hmap m -> succ m k x ->
    let m0 := B m k x in
  nc m0 = 
   nc m + if eqc_dec m0 x (A m k x) then 0 else 1.
Proof.
induction m.
 unfold succ in |- *.
   simpl in |- *.
   tauto.
rename t into u.
 unfold succ in |- *.
   simpl in |- *.
   intros.
   decompose [and] H.
   clear H.
   unfold succ in IHm.
   generalize (IHm k x H1 H0).
   elim (eqc_dec (I (B m k x) d u p) x (A m k x)).
  simpl in |- *.
    unfold prec_I in H2.
    intro.
    elim a.
   clear a.
     intro.
     absurd (x = d).
    intro.
      rewrite <- H3 in H2.
      absurd (exd m x).
     tauto.
     apply succ_exd with k.
      tauto.
      unfold succ in |- *.
        tauto.
    tauto.
   clear a.
     intro.
     elim (eqc_dec (B m k x) x (A m k x)).
    intros.
      lia.
    tauto.
  simpl in |- *.
    intro.
    elim (eqc_dec (B m k x) x (A m k x)).
   tauto.
   intros.
     lia.
 simpl in |- *.
   unfold succ in |- *.
   unfold prec_L in |- *.
   simpl in |- *.
   intros k x H.
   decompose [and] H.
   clear H.
   rename d into j.
   elim (eq_dim_dec j k).
  intro.
    elim (eq_dart_dec d0 x).
   intros.
     rewrite <- a0.
     lia.
   simpl in |- *.
     intros.
     unfold succ in IHm.
     generalize (IHm k x H0 H).
     intro.
     elim (eqc_dec (L (B m k x) j d0 d1) x (A m k x)).
    rewrite a.
      simpl in |- *.
      intro.
      generalize H5.
      clear H5.
      elim (eqc_dec (B m k x) x (A m k x)).
     intros.
       assert (nc (B m k x) = nc m).
      lia.
      clear H5.
        rewrite H7.
        assert (eqc (B m k x) d0 d1 <-> eqc m d0 d1).
       split.
        apply eqc_B_eqc.
         tauto.
         unfold succ in |- *.
           tauto.
        apply eqc_eqc_B.
         tauto.
         unfold succ in |- *.
           tauto.
         tauto.
       elim (eqc_dec (B m k x) d0 d1).
        elim (eqc_dec m d0 d1).
         intros. clear a0 a1 H5 a2 a3.
           lia.
         intros.
           generalize (eqc_dec (B m k x) d0 d1).
           generalize (eqc_dec m d0 d1).
           tauto.
        intro.
          elim (eqc_dec m d0 d1).
         intro.
           generalize (eqc_dec (B m k x) d0 d1).
           generalize (eqc_dec m d0 d1).
           tauto.
         intro. clear a0 a1 H5.
           lia.
     intros.
       elim a0.
      tauto.
      clear a0.
        intro.
        elim H7.
       clear H7.
         intro.
         elim (eqc_dec (B m k x) d0 d1).
        intro.
          elim b0.
          apply eqc_trans with d0.
         tauto.
         apply eqc_trans with d1.
          tauto.
          tauto.
        intro.
          elim (eqc_dec m d0 d1).
         intro.
           lia.
         intro.
           generalize (eqc_B_CS m k x d0 d1).
           unfold succ in |- *.
           generalize (eqc_symm (B m k x) x d0).
         generalize (eqc_symm (B m k x) d1 (A m k x)).
           tauto.
       clear H7.
         intro.
         elim (eqc_dec (B m k x) d0 d1).
        intro.
          elim b0.
          apply eqc_trans with d1.
         tauto.
         apply eqc_trans with d0.
          apply eqc_symm.
            tauto.
          tauto.
        elim (eqc_dec m d0 d1).
         intros.
           lia.
         intros.
           generalize (eqc_B_CS m k x d0 d1).
           unfold succ in |- *.
           tauto.
    simpl in |- *.
      intros.
      generalize H5.
      clear H5.
      elim (eqc_dec (B m k x) x (A m k x)).
     tauto.
     intros.
       elim (eqc_dec (B m k x) d0 d1).
      intro.
        elim (eqc_dec m d0 d1).
       intro.
         lia.
       intro.
         generalize (eqc_B_eqc m k x d0 d1).
         unfold succ in |- *.
         tauto.
      intro.
        elim (eqc_dec m d0 d1).
       intro.
         generalize (eqc_B_CN m k x d0 d1).
         unfold succ in |- *.
         intro.
         generalize (eqc_symm (B m k x) d0 x).
         generalize (eqc_symm (B m k x) (A m k x) d1).
         tauto.
       intro.
         lia.
  simpl in |- *.
    intros.
    unfold succ in IHm.
    generalize (IHm k x H0 H).
    intro.
    elim (eqc_dec (L (B m k x) j d0 d1) x (A m k x)).
   simpl in |- *.
     intro.
     generalize H5.
     clear H5.
     elim (eqc_dec (B m k x) x (A m k x)).
    intros.
      assert (nc (B m k x) = nc m).
     lia.
     clear H5.
       rewrite H7.
       assert (eqc (B m k x) d0 d1 <-> eqc m d0 d1).
      split.
       apply eqc_B_eqc.
        tauto.
        unfold succ in |- *.
          tauto.
       apply eqc_eqc_B.
        tauto.
        unfold succ in |- *.
          tauto.
        tauto.
      elim (eqc_dec (B m k x) d0 d1).
       elim (eqc_dec m d0 d1).
        intros. clear a a0 H5 a1 a2.
          lia.
        intros.
          generalize (eqc_dec (B m k x) d0 d1).
          generalize (eqc_dec m d0 d1).
          tauto.
       intro.
         elim (eqc_dec m d0 d1).
        intro.
          generalize (eqc_dec (B m k x) d0 d1).
          generalize (eqc_dec m d0 d1).
          tauto.
        intro. clear a a0 H5.
          lia.
    intros.
      elim a.
     tauto.
     clear a.
       intro.
       elim H7.
      clear H7.
        intro.
        elim (eqc_dec (B m k x) d0 d1).
       intro.
         elim b0.
         apply eqc_trans with d0.
        tauto.
        apply eqc_trans with d1.
         tauto.
         tauto.
       intro.
         elim (eqc_dec m d0 d1).
        intro. clear a H7.
          lia. 
        intro.
          generalize (eqc_B_CS m k x d0 d1).
          unfold succ in |- *.
          generalize (eqc_symm (B m k x) x d0).
          generalize (eqc_symm (B m k x) d1 (A m k x)).
          tauto.
      clear H7.
        intro.
        elim (eqc_dec (B m k x) d0 d1).
       intro.
         elim b0.
         apply eqc_trans with d1.
        tauto.
        apply eqc_trans with d0.
         apply eqc_symm.
           tauto.
         tauto.
       elim (eqc_dec m d0 d1).
        intros. clear a.
          lia.
        intros.
          generalize (eqc_B_CS m k x d0 d1).
          unfold succ in |- *.
          tauto.
   simpl in |- *.
     intros.
     generalize H5.
     clear H5.
     elim (eqc_dec (B m k x) x (A m k x)).
    tauto.
    intros.
      elim (eqc_dec (B m k x) d0 d1).
     intro.
       elim (eqc_dec m d0 d1).
      intro. clear a a0. 
        lia.
      intro.
        generalize (eqc_B_eqc m k x d0 d1).
        unfold succ in |- *.
        tauto.
     intro.
       elim (eqc_dec m d0 d1).
      intro.
        generalize (eqc_B_CN m k x d0 d1).
        unfold succ in |- *.
        intro.
        generalize (eqc_symm (B m k x) d0 x).
        generalize (eqc_symm (B m k x) (A m k x) d1).
        tauto.
      intro.
        lia.
Qed.

(* OK: *)

Lemma nc_L_B:forall(m:fmap)(k:dim)(x:dart),
  inv_hmap m -> succ m k x ->
    let m0:= B m k x in
    let m1:= L m0 k x (A m k x) in
  nc m1 = nc m.
Proof.
simpl in |- *.
intros.
generalize (nc_B m k x).
simpl in |- *.
intros.
assert
 (nc (B m k x) = nc m + 
    (if eqc_dec (B m k x) x (A m k x) then 0 else 1)).
 tauto.
 lia.
Qed.

(* LEMMA, USEFUL: *)

Lemma A_not_cA: forall(m:fmap)(k:dim)(x:dart),
 inv_hmap m -> succ m k x ->  
   A m k x <> cA (B m k x) k x.
Proof.
intros.
generalize (succ_bottom m k x H H0).
intro.
assert (exd m x).
 apply succ_exd with k.
  tauto.
  tauto.
 generalize (cA_B m k x x H H0).
   elim (eq_dart_dec x x).
  intros.
    rewrite H3.
    intro.
    symmetry  in H4.
    tauto.
  tauto.
Qed.

(*====================================================
                 cF_B, B_B...
  expf_B0_CNS : ANCIENT FORMULATION PROVEN FROM
                FUNCTOR MTr
   + CONSEQUENCES
            (USED IN Jordan CT) 
====================================================*)

Lemma cF_B:forall(m:fmap)(k:dim)(x z:dart),
  inv_hmap m -> succ m k x ->
  cF (B m k x) z =
   if eq_dim_dec k zero
   then 
    cA_1 (B m zero x) one
     (if eq_dart_dec (A m zero x) z
      then top m zero x
      else if eq_dart_dec (bottom m zero x) z 
           then x else cA_1 m zero z) 
   else 
    (if eq_dart_dec (A m one x) 
         (cA_1 (B m one x) zero z)
     then top m one x
     else
      if eq_dart_dec (bottom m one x) 
         (cA_1 (B m one x) zero z)
      then x
      else cA_1 m one (cA_1 (B m one x) zero z)).
Proof.
intros.
unfold cF in |- *.
elim (eq_dim_dec k zero).
 intro.
   rewrite a.
   rewrite cA_1_B.
  tauto.
  tauto.
  rewrite a in H0.
    tauto.
 intro.
   induction k.
  tauto.
  rewrite cA_1_B.
   tauto.
   tauto.
   tauto.
Qed.

Lemma B_B : forall (m:fmap)(k j:dim)(u v:dart),
   B (B m k u) j v =  B (B m j v) k u. 
Proof.
intros.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   rewrite IHm.
  tauto.
 simpl in |- *.
   elim (eq_dim_dec d k).
  elim (eq_dim_dec d j).
   elim (eq_dart_dec d0 u).
    elim (eq_dart_dec d0 v).
     intros.
       rewrite <- a.
       rewrite <- a0.
       rewrite <- a1; rewrite a2.
       tauto.
     intro.
       simpl in |- *.
       elim (eq_dim_dec d k).
      elim (eq_dart_dec d0 u).
       tauto.
       tauto.
      tauto.
    simpl in |- *.
      elim (eq_dim_dec d j).
     elim (eq_dart_dec d0 v).
      tauto.
      simpl in |- *.
        elim (eq_dart_dec d0 u).
       tauto.
       elim (eq_dim_dec d k).
          rewrite IHm.
         tauto.
         tauto.
     tauto.
   simpl in |- *.
     elim (eq_dim_dec d k).
    elim (eq_dart_dec d0 u).
     tauto.
     simpl in |- *.
       elim (eq_dim_dec d j).
      tauto.
        rewrite IHm.
       tauto.
       tauto.
  simpl in |- *.
    elim (eq_dim_dec d j).
   elim (eq_dart_dec d0 v).
    tauto.
    simpl in |- *.
      elim (eq_dim_dec d k).
     tauto.
       rewrite IHm.
      tauto.
   simpl in |- *.
     elim (eq_dim_dec d k).
    tauto.
    rewrite IHm.
     tauto.
Qed.

(*==============================================
         expof_B0: ANCIENT FORMULATION
================================================*)

(* IN Jordan2C: WE HAVE FROM GENERICITY:

Theorem expof_B0_CNS: 
  forall(m:fmap)(x z t:dart)(H:inv_hmap m),
      let x0 := cA m zero x in
      let tx0:= top m zero x in
      let bx0 := cA m zero tx0 in
      let tx0_1:= cA_1 m one tx0 in
      let x_1:= cA_1 m one x in 
      let m1 := B m zero x in
  succ m zero x -> exd m z ->
 (expof m1 z t <->  
    (if expof_dec m x0 tx0_1 H
     then
      betweenf m tx0_1 z x0 /\ betweenf m tx0_1 t x0 \/
      betweenf m x_1 z bx0 /\ betweenf m x_1 t bx0 \/
      ~ expof m x0 z /\ expof m z t
     else 
      expof m z t \/
      expof m x0 z /\ expof m tx0_1 t \/
      expof m x0 t /\ expof m tx0_1 z)).

WHICH IS EQUIVALENT TO THE PREVIOUS FORMULATION 
EXCEPT exd m z. PROOF: 
*)

(* NEW PROOF (TO KEEP): *)

Theorem expf_B0_CNS:forall (m:fmap)(x z t:dart),
 inv_hmap m -> succ m zero x -> exd m z ->
  (expf (B m zero x) z t <->
   let x0 := cA m zero x in
   let xb0 := bottom m zero x in
   let x_1 := cA_1 m one x in
   let xh0 := top m zero x in
   let xh0_1 := cA_1 m one xh0 in 
     (if expf_dec m x0 xb0 
      then 
         betweenf m x_1 z xb0 /\ betweenf m x_1 t xb0
      \/ betweenf m xh0_1 z x0 /\ betweenf m xh0_1 t x0
      \/ ~ expf m x_1 z /\ expf m z t
      else
         expf m xb0 z /\ expf m x0 t
      \/ expf m xb0 t /\ expf m x0 z
      \/ expf m z t)).
Proof.
intros.
generalize (expof_B0_CNS m x z t H H0).
simpl in |- *.
set (tx0 := top m zero x) in |- *.
set (bx0 := bottom m zero x) in |- *.
set (x0 := cA m zero x) in |- *.
set (x_1 := cA_1 m one x) in |- *.
set (tx0_1 := cA_1 m one tx0) in |- *.
assert (exd m x).
 apply succ_exd with zero.
   tauto.
  tauto.
rename H2 into Ex.
assert (bx0 = cA m zero tx0).
 unfold tx0 in |- *.
   rewrite cA_top in |- *.
  fold bx0 in |- *.
     tauto.
  tauto.
  tauto.
assert (expf m bx0 tx0_1).
 assert (tx0 = cA_1 m zero bx0).
  rewrite H2 in |- *.
    rewrite cA_1_cA in |- *.
    tauto.
   tauto.
  unfold tx0 in |- *.
    apply exd_top.
    tauto.
   tauto.
 unfold tx0_1 in |- *.
   rewrite H3 in |- *.
   fold (cF m bx0) in |- *.
   unfold expf in |- *.
   split.
   tauto.
 unfold MF.expo in |- *.
   split.
  unfold bx0 in |- *.
    apply exd_bottom.
    tauto.
   tauto.
 split with 1%nat.
   simpl in |- *.
    tauto.
assert (forall u : dart, 
   expf m bx0 u <-> expof m tx0_1 u).
 intro.
   split.
  intro.
    apply expof_trans with bx0.
   apply expof_symm.
     tauto.
   unfold expof in |- *; unfold expf in H3.
      tauto.
  unfold expof in |- *.
    unfold expf in H4.
     tauto.
 intro.
   apply expf_trans with tx0_1.
   tauto.
 unfold expf in |- *.
   unfold expof in H4.
    tauto.
assert (expf m x0 bx0 <-> expof m x0 tx0_1).
 split.
  intro.
    apply expof_trans with bx0.
   unfold expof in |- *.
     unfold expf in H5.
      tauto.
  unfold expof in |- *.
    unfold expf in H3.
     tauto.
 intro.
   apply expf_trans with tx0_1.
  unfold expf in |- *.
    unfold expof in H5.
     tauto.
 apply expf_symm.
    tauto.
assert (bx0 = cA m zero tx0).
 unfold tx0 in |- *.
   rewrite cA_top in |- *.
  fold bx0 in |- *.
     tauto.
  tauto.
  tauto.
rewrite <- H6 in |- *.
  set
   (A1 :=
    betweenf m tx0_1 z x0 /\ betweenf m tx0_1 t x0 \/
    betweenf m x_1 z bx0 /\ betweenf m x_1 t bx0 \/
    ~ expof m x0 z /\ expof m z t) in |- *.
  set
   (A2 :=
    betweenf m x_1 z bx0 /\ betweenf m x_1 t bx0 \/
    betweenf m tx0_1 z x0 /\ betweenf m tx0_1 t x0 \/
    ~ expf m x_1 z /\ expf m z t) in |- *.
  set
   (B1 :=
    expof m z t \/
    expof m x0 z /\ expof m tx0_1 t \/ 
       expof m x0 t /\ expof m tx0_1 z)
   in |- *.
  set
   (B2 :=
    expf m bx0 z /\ expf m x0 t \/ 
      expf m bx0 t /\ expf m x0 z \/ expf m z t)
   in |- *.
  assert (A1 <-> A2).
 unfold A1 in |- *; unfold A2 in |- *.
   assert (expf m x0 x_1).
  unfold x_1 in |- *.
    assert (x = cA_1 m zero x0).
   unfold x0 in |- *.
     rewrite cA_1_cA in |- *.
     tauto.
    tauto.
   apply succ_exd with zero.
     tauto.
    tauto.
  rewrite H7 in |- *.
    unfold expf in |- *.
    split.
    tauto.
  unfold MF.expo in |- *.
    split.
   unfold x0 in |- *.
     generalize (exd_cA m zero x).
      tauto.
  split with 1%nat.
    simpl in |- *.
    fold (cF m x0) in |- *.
     tauto.
 assert (expof m x0 z <-> expf m x_1 z).
  split.
   intro.
     apply expf_trans with x0.
    apply expf_symm.
       tauto.
   unfold expof in H8.
     unfold expf in |- *.
      tauto.
  intro.
    apply expof_trans with x_1.
   unfold expf in H7.
     unfold expof in |- *.
      tauto.
  unfold expof in |- *.
    unfold expf in H8.
     tauto;  tauto.
 assert (expf m z t <-> expof m z t).
  unfold expf in |- *.
    unfold expof in |- *.
     tauto.
  tauto.
assert (B1 <-> B2).
 unfold B1 in |- *; unfold B2 in |- *.
   assert (expof m z t <-> expf m z t).
  unfold expf in |- *; unfold expof in |- *.
     tauto.
 assert (expof m x0 z /\ expof m tx0_1 t <-> 
 expf m bx0 t /\ expf m x0 z).
  generalize (H4 t).
    unfold expf in |- *; unfold expof in |- *.
     tauto.
 assert (expof m x0 t /\ expof m tx0_1 z <-> 
  expf m bx0 z /\ expf m x0 t).
  generalize (H4 z).
    unfold expf in |- *; unfold expof in |- *.
     tauto.
  tauto.
assert (inv_hmap (B m zero x)).
 apply inv_hmap_B.
    tauto.
intro.
  split.
 intro.
   assert (exd m z).
  unfold expf in H11.
    unfold MF.expo in H11.
    generalize (exd_B m zero x z).
     tauto.
 assert 
 (if expof_dec m x0 tx0_1 H then A1 else B1).
  assert (expof (B m zero x) z t).
   unfold expof in |- *.
     unfold expf in H11.
      tauto.
  assert 
 (if expof_dec m x0 tx0_1 H then A1 else B1).
    tauto.
   tauto.
 generalize H13.
   elim (expof_dec m x0 tx0_1 H).
  elim (expf_dec m x0 bx0).
    tauto.
  unfold expof in |- *.
    unfold expf in |- *.
    unfold expf in H5; unfold expof in H5.
     tauto.
 elim (expf_dec m x0 bx0).
  unfold expf in |- *.
    unfold expof in |- *.
    unfold expof in H5.
    unfold expf in H5.
     tauto.
  tauto.
intro.
  assert 
 (if expof_dec m x0 tx0_1 H then A1 else B1).
 generalize H11.
   elim (expf_dec m x0 bx0).
  elim (expof_dec m x0 tx0_1 H).
    tauto.
  unfold expof in |- *; unfold expf in |- *.
    unfold expf in H5; unfold expof in H5.
     tauto.
 elim (expof_dec m x0 tx0_1 H).
   tauto.
  tauto.
assert (exd m z -> expof (B m zero x) z t).
  tauto.
unfold expf in |- *.
  split.
  tauto.
unfold expof in H13.
  apply H13.
tauto.
Qed.

(* NECESSARY CONDITION: *)

Theorem expf_B0_CN:forall (m:fmap)(x z t:dart),
 inv_hmap m -> succ m zero x -> exd m z ->
  expf (B m zero x) z t ->
   let x0 := cA m zero x in
   let xb0 := bottom m zero x in
   let x_1 := cA_1 m one x in
   let xh0 := top m zero x in
   let xh0_1 := cA_1 m one xh0 in 
     (if expf_dec m x0 xb0 
      then 
        betweenf m x_1 z xb0 /\ betweenf m x_1 t xb0
      \/ betweenf m xh0_1 z x0 /\ betweenf m xh0_1 t x0
      \/ ~ expf m x_1 z /\ expf m z t
      else
         expf m xb0 z /\ expf m x0 t
      \/ expf m xb0 t /\ expf m x0 z
      \/ expf m z t).
Proof.
intros.
generalize (expf_B0_CNS m x z t H H0 H1).
simpl in |- *.
 tauto.
Qed.

(* SUFFICIENT CONDITION: *)

Theorem expf_B0_CS:forall (m:fmap)(x z t:dart),
 inv_hmap m -> succ m zero x -> exd m z ->
   let x0 := cA m zero x in
   let xb0 := bottom m zero x in
   let x_1 := cA_1 m one x in
   let xh0 := top m zero x in
   let xh0_1 := cA_1 m one xh0 in 
     (if expf_dec m x0 xb0 
      then 
        betweenf m x_1 z xb0 /\ betweenf m x_1 t xb0
     \/ betweenf m xh0_1 z x0 /\ betweenf m xh0_1 t x0
     \/ ~ expf m x_1 z /\ expf m z t
      else
        expf m xb0 z /\ expf m x0 t
     \/ expf m xb0 t /\ expf m x0 z
     \/ expf m z t)
      -> expf (B m zero x) z t.
Proof.
intros.
generalize (expf_B0_CNS m x z t H H0 H1).
simpl in |- *.
 tauto.
Qed.

(*=====================================================
               CONSEQUENCES / B0
=====================================================*)

(* VERY USEFUL IN JORDAN CURVE THEOREM: OK: *)

Open Scope nat_scope.

(* expf (B m zero x) x0 xb0 <-> ~expf m x0 xb0
COULD BE BETTER... *)

Theorem expf_not_expf_B0: forall (m:fmap)(x:dart),
  inv_hmap m -> succ m zero x -> 
  let x_1:= cA_1 m one x in
  let x0 := cA m zero x in
  let xb0 := bottom m zero x in
   (expf (B m zero x) x_1 x0 <-> ~expf m x0 xb0).
Proof.
intros.
assert (exd m x).
 apply (succ_exd m zero x H H0).
rename H1 into Ex.
  assert (exd m x_1).
 unfold x_1 in |- *.
   generalize (exd_cA_1 m one x).
    tauto.
rename H1 into Ex_1.
  split.
 intro.
   generalize (expf_B0_CN m x x_1 x0 H H0 Ex_1 H1).
   simpl in |- *.
   fold x_1 in |- *.
   fold xb0 in |- *.
   fold x0 in |- *.
   set (xh0 := top m zero x) in |- *.
   set (xh0_1 := cA_1 m one xh0) in |- *.
   elim (expf_dec m x0 xb0).
  intros.
    elim H2; clear H2.
   intro.
     elim H2.
     clear H2.
     intros.
     elim (eq_dart_dec x0 xb0).
    intro.
      unfold x0 in a0.
      unfold xb0 in a0.
      generalize a0.
      rewrite cA_eq in |- *.
     elim (succ_dec m zero x).
      intros.
        symmetry  in a2.
         absurd (bottom m zero x = A m zero x).
       apply succ_bottom.
         tauto.
        tauto.
       tauto.
      tauto.
     tauto.
   intro.
     unfold betweenf in H3.
     unfold MF.between in H3.
     elim H3.
    intros i Hi.
      clear H3.
      elim Hi.
      intros j Hj.
      clear Hi.
      decompose [and] Hj.
      set (p := MF.Iter_upb m x_1) in |- *.
      fold p in H7.
      assert (x0 = Iter (cF m) (p - 1) x_1).
     unfold x_1 in |- *.
       rewrite <- MF.Iter_f_f_1 in |- *.
      simpl in |- *.
        fold x_1 in |- *.
        unfold p in |- *.
        rewrite MF.Iter_upb_period in |- *.
       unfold x_1 in |- *.
         assert (cF_1 = MF.f_1).
         tauto.
       rewrite <- H6 in |- *.
         unfold cF_1 in |- *.
         rewrite cA_cA_1 in |- *.
        fold x0 in |- *.
           tauto.
        tauto.
        tauto.
       tauto.
       tauto.
      tauto.
     fold x_1 in |- *.
        tauto.
      lia.
    rewrite H6 in H3.
      assert (i = p - 1).
     apply (MF.unicity_mod_p m x_1).
       tauto.
      tauto.
     fold p in |- *.
        lia.
     fold p in |- *.
        lia.
      tauto.
    fold p in Hj.
      decompose [and] Hj.
      assert (i = j).
      lia.
    rewrite H12 in H9.
      rewrite H9 in H11.
       tauto.
    tauto.
    tauto.
  intros.
    elim H2.
   clear H2.
     intros.
     elim H2.
     clear H2.
     intros.
     unfold betweenf in H2.
     unfold MF.between in H2.
     elim H2.
    intros i Hi.
      clear H2.
      elim Hi.
      intros j Hj.
      clear Hi.
      decompose [and] Hj.
      set (p := MF.Iter_upb m xh0_1) in |- *.
      fold p in H7.
      clear Hj.
      assert (x_1 = cF m x0).
     unfold cF in |- *.
       unfold x0 in |- *.
       rewrite cA_1_cA in |- *.
      fold x_1 in |- *.
         tauto.
      tauto.
      tauto.
    rewrite H6 in H2.
      rewrite <- H6 in H2.
      assert (MF.f = cF).
      tauto.
    assert (MF.f m (Iter (MF.f m) j xh0_1) = 
     Iter (MF.f m) (S j) xh0_1).
     simpl in |- *.
        tauto.
    elim (Nat.eq_dec (S j) p).
     intro.
       rewrite a0 in H9.
       unfold p in H9.
       rewrite MF.Iter_upb_period in H9.
      assert (x_1 = xh0_1).
       rewrite H5 in H9.
         rewrite H6 in |- *.
         rewrite <- H8 in |- *.
          tauto.
      assert (x = cA m one x_1).
       unfold x_1 in |- *.
         rewrite cA_cA_1 in |- *.
         tauto.
        tauto.
        tauto.
      assert (xh0 = cA m one xh0_1).
       unfold xh0_1 in |- *.
         rewrite cA_cA_1 in |- *.
         tauto.
        tauto.
       unfold xh0 in |- *.
         apply exd_top.
         tauto.
        tauto.
      assert (x = xh0).
       rewrite H11 in |- *.
         rewrite H10 in |- *.
         symmetry  in |- *.
          tauto.
      rewrite H13 in H0.
         absurd (succ m zero xh0).
       unfold xh0 in |- *.
         apply not_succ_top.
          tauto.
       tauto.
      tauto.
     unfold xh0_1 in |- *.
       generalize (exd_cA_1 m one xh0).
       unfold xh0 in |- *.
       generalize (exd_top m zero x).
        tauto.
    intro.
      assert (i = S j).
     apply (MF.unicity_mod_p m xh0_1 i (S j) H).
      unfold xh0_1 in |- *.
        generalize (exd_cA_1 m one xh0).
        unfold xh0 in |- *.
        generalize (exd_top m zero x).
         tauto.
     fold p in |- *.
        lia.
     fold p in |- *.
        lia.
     rewrite H2 in |- *.
       rewrite <- H9 in |- *.
       rewrite H5 in |- *.
        tauto.
     absurd (i = S j).
      lia.
     tauto.
    tauto.
   unfold xh0_1 in |- *.
     generalize (exd_cA_1 m one xh0).
     unfold xh0 in |- *.
     generalize (exd_top m zero x).
      tauto.
  clear H2.
    intro.
     absurd (expf m x_1 x_1).
    tauto.
  apply expf_refl.
    tauto.
   tauto.
 intro.
    tauto.
intro.
  generalize (expf_B0_CS m x x_1 x0 H H0 Ex_1).
  simpl in |- *.
  fold x_1 in |- *.
  fold xb0 in |- *.
  fold x0 in |- *.
  elim (expf_dec m x0 xb0).
  tauto.
intros.
  apply H2.
  clear H2.
  clear b.
  right.
  right.
  apply expf_symm.
  unfold x0 in |- *.
  unfold x_1 in |- *.
  fold x0 in |- *.
  fold x_1 in |- *.
  unfold expf in |- *.
  split.
  tauto.
unfold MF.expo in |- *.
  split.
 unfold x0 in |- *.
   generalize (exd_cA m zero x).
    tauto.
split with 1.
  simpl in |- *.
  unfold x0 in |- *.
  assert (cF = MF.f).
  tauto.
rewrite <- H2 in |- *.
  unfold cF in |- *.
  rewrite cA_1_cA in |- *.
 fold x_1 in |- *.
    tauto.
 tauto.
 tauto.
Qed.

(*==============================================
            expf_B1: ANCIENT FORMULATION
================================================*)

(* IN Jordan2C: WE HAVE FROM GENERICITY (MTr):

expof_B1_CNS
     : forall (m : fmap) (x : dart),
       dart ->
       forall (z t : dart) (H : inv_hmap m),
       let tx1 := top m one x in
       let x_1 := cF_1 m x in
       let tx1_1 := cF_1 m tx1 in
       let m1 := B m one x in
       succ m one x ->
       exd m z ->
       (expof m1 z t <->
        (if expof_dec m x_1 tx1 H
         then
        betweenf m tx1 z x_1 /\ betweenf m tx1 t x_1 \/
        betweenf m x z tx1_1 /\ betweenf m x t tx1_1 \/
        ~ expof m x_1 z /\ expof m z t
         else
        expof m z t \/
        expof m x_1 z /\ expof m tx1 t \/ 
        expof m x_1 t /\ expof m tx1 z))

*)

(* NECESSARY AND SUFFICIENT CONDITION: *)

Theorem expf_B1_CNS: 
   forall (m : fmap) (x z t : dart),
   inv_hmap m -> succ m one x -> exd m z ->
       let tx1 := top m one x in
       let x_1 := cF_1 m x in
       let tx1_1 := cF_1 m tx1 in
       let m1 := B m one x in
   (expf m1 z t <->
     (if expf_dec m x_1 tx1
      then
        betweenf m tx1 z x_1 /\ betweenf m tx1 t x_1 \/
        betweenf m x z tx1_1 /\ betweenf m x t tx1_1 \/
        ~ expf m x_1 z /\ expf m z t
      else
        expf m z t \/
        expf m x_1 z /\ expf m tx1 t \/ 
        expf m x_1 t /\ expf m tx1 z)).
Proof.
intros.
generalize (expof_B1_CNS m x x z t H H0 H1).
fold tx1 in |- *.
fold x_1 in |- *.
fold tx1_1 in |- *.
fold m1 in |- *.
assert (inv_hmap m1).
 unfold m1 in |- *.
   apply inv_hmap_B.
    tauto.
assert (expof m1 z t <-> expf m1 z t).
 unfold expof in |- *.
   unfold expf in |- *.
    tauto.
set
 (A1 :=
  betweenf m tx1 z x_1 /\ betweenf m tx1 t x_1 \/
  betweenf m x z tx1_1 /\ betweenf m x t tx1_1 \/
  ~ expof m x_1 z /\ expof m z t) in |- *.
  set
   (A2 :=
    betweenf m tx1 z x_1 /\ betweenf m tx1 t x_1 \/
    betweenf m x z tx1_1 /\ betweenf m x t tx1_1 \/
    ~ expf m x_1 z /\ expf m z t) in |- *.
  set
   (B1 :=
    expf m z t \/
    expf m x_1 z /\ expf m tx1 t \/ 
       expf m x_1 t /\ expf m tx1 z)
   in |- *.
  set
   (B2 :=
    expof m z t \/
    expof m x_1 z /\ expof m tx1 t \/ 
     expof m x_1 t /\ expof m tx1 z)
   in |- *.
  assert (A1 <-> A2).
 unfold A1 in |- *; unfold A2 in |- *.
   assert (~ expof m x_1 z <-> ~ expf m x_1 z).
  unfold expof in |- *; unfold expf in |- *.
     tauto.
 assert (expof m z t <-> expf m z t).
  unfold expof in |- *; unfold expf in |- *.
     tauto.
  tauto.
assert (B1 <-> B2).
 unfold B1 in |- *; unfold B2 in |- *.
   unfold expf in |- *; unfold expof in |- *.
    tauto.
elim (expof_dec m x_1 tx1 H).
 elim (expf_dec m x_1 tx1).
   tauto.
 unfold expf in |- *; unfold expof in |- *.
    tauto.
elim (expf_dec m x_1 tx1).
 unfold expf in |- *; unfold expof in |- *.
    tauto.
 tauto.
Qed.

(* NECESSARY CONDITION: *)

Theorem expf_B1_CN: 
   forall (m : fmap) (x z t : dart),
   inv_hmap m -> succ m one x -> exd m z ->
       let tx1 := top m one x in
       let x_1 := cF_1 m x in
       let tx1_1 := cF_1 m tx1 in
       let m1 := B m one x in
   expf m1 z t ->
     (if expf_dec m x_1 tx1
      then
        betweenf m tx1 z x_1 /\ betweenf m tx1 t x_1 \/
        betweenf m x z tx1_1 /\ betweenf m x t tx1_1 \/
        ~ expf m x_1 z /\ expf m z t
      else
        expf m z t \/
        expf m x_1 z /\ expf m tx1 t \/ 
        expf m x_1 t /\ expf m tx1 z).
Proof.
intros.
generalize (expf_B1_CNS m x z t H H0 H1).
simpl in |- *.
fold tx1 in |- *; fold x_1 in |- *; fold tx1_1 in |- *.
 tauto.
Qed.

(* SUFFICIENT CONDITION: *)

Theorem expf_B1_CS:
   forall (m : fmap) (x z t : dart),
   inv_hmap m -> succ m one x -> exd m z ->
       let tx1 := top m one x in
       let x_1 := cF_1 m x in
       let tx1_1 := cF_1 m tx1 in
       let m1 := B m one x in
     (if expf_dec m x_1 tx1
      then
        betweenf m tx1 z x_1 /\ betweenf m tx1 t x_1 \/
        betweenf m x z tx1_1 /\ betweenf m x t tx1_1 \/
        ~ expf m x_1 z /\ expf m z t
      else
        expf m z t \/
        expf m x_1 z /\ expf m tx1 t \/
        expf m x_1 t /\ expf m tx1 z)
    -> expf m1 z t.
Proof.
intros.
generalize (expf_B1_CNS m x z t H H0 H1).
simpl in |- *.
fold tx1 in |- *; fold x_1 in |- *; fold tx1_1 in |- *.
 tauto.
Qed.

(*=====================================================
               CONSEQUENCES / B1
=====================================================*)

Open Scope nat_scope.

(* OK: *)

Theorem not_expf_expf_B1: forall (m:fmap)(x:dart),
  inv_hmap m -> succ m one x -> 
       let tx1 := top m one x in
   (expf (B m one x) x tx1 <-> ~expf m x tx1).
Proof.
intros.
set (x_1 := cF_1 m x) in |- *.
set (tx1_1 := cF_1 m tx1) in |- *.
assert (exd m x).
 apply succ_exd with one.
   tauto.
  tauto.
assert (exd m x_1).
 unfold x_1 in |- *.
   generalize (exd_cF_1 m x).
    tauto.
assert (exd m tx1).
 unfold tx1 in |- *.
   apply exd_top.
   tauto.
  tauto.
generalize (expf_B1_CNS m x x tx1 H H0 H1).
  simpl in |- *.
  fold tx1 in |- *; fold x_1 in |- *.
  fold tx1_1 in |- *.
  elim (expf_dec m x tx1).
 intro.
   assert (expf m x_1 tx1).
  apply expf_trans with x.
   unfold expf in |- *.
     split.
     tauto.
   unfold MF.expo in |- *.
     split.
     tauto.
   split with 1.
     simpl in |- *.
     unfold x_1 in |- *.
     rewrite cF_cF_1 in |- *.
     tauto.
    tauto.
    tauto.
   tauto.
 elim (expf_dec m x_1 tx1).
  intro.
    intro.
    split.
   intro.
     assert
    (betweenf m tx1 x x_1 /\ betweenf m tx1 tx1 x_1 \/
      betweenf m x x tx1_1 /\ betweenf m x tx1 tx1_1 \/
       ~ expf m x_1 x /\ expf m x tx1).
     tauto.
   clear H5.
     clear a0.
     elim H7.
    clear H7.
      intros.
       absurd (betweenf m tx1 x x_1).
     intro.
       clear H5.
       unfold betweenf in H7.
       unfold MF.between in H7.
       elim H7.
      clear H7.
        intros i Hi.
        elim Hi.
        clear Hi.
        intros j Hj.
        decompose [and] Hj.
        clear Hj.
        set (p := MF.Iter_upb m tx1) in |- *.
        fold p in H10.
        assert (j <> p - 1).
       intro.
         rewrite H9 in H8.
         rewrite <- MF.Iter_f_f_1 in H8.
        unfold p in |- *.
          unfold p in |- *.
          unfold p in H8.
          rewrite MF.Iter_upb_period in H8.
         simpl in H8.
           unfold tx1 in H8.
           unfold x_1 in H8.
           assert (x = cF m (cF_1 m tx1)).
          unfold tx1 in |- *.
            assert (cF_1 = MF.f_1).
            tauto.
          rewrite H11 in |- *.
            rewrite H8 in |- *.
            rewrite cF_cF_1 in |- *.
            tauto.
           tauto.
           tauto.
         rewrite cF_cF_1 in H11.
          unfold tx1 in H11.
            rewrite H11 in H0.
             absurd (succ m one (top m one x)).
           apply not_succ_top.
              tauto.
           tauto.
          tauto.
          tauto.
         tauto.
         tauto.
        tauto.
        tauto.
        lia.
      assert (i = S j).
       apply (MF.unicity_mod_p m tx1 i (S j)).
         tauto.
        tauto.
       fold p in |- *.
          lia.
       fold p in |- *.
          lia.
       simpl in |- *.
         rewrite H5 in |- *; rewrite H8 in |- *.
         unfold x_1 in |- *.
         rewrite cF_cF_1 in |- *.
         tauto.
        tauto.
        tauto.
      elim H9.
         lia.
      tauto.
      tauto.
     tauto.
   clear H7.
     intros.
     elim H5.
    clear H5.
      intros.
      elim H5.
      clear H5.
      intros.
      clear H5.
      unfold betweenf in H7.
      unfold MF.between in H7.
      elim H7.
     clear H7.
       intros i Hi.
       elim Hi.
       clear Hi.
       intros j Hj.
       decompose [and] Hj.
       clear Hj.
       set (p := MF.Iter_upb m x) in |- *.
       fold p in H10.
       assert (j <> p - 1).
      intro.
        rewrite H9 in H8.
        rewrite <- MF.Iter_f_f_1 in H8.
       unfold p in H8.
         rewrite MF.Iter_upb_period in H8.
        simpl in H8.
          unfold tx1_1 in H8.
          assert (x = cF m (cF_1 m tx1)).
         unfold tx1 in |- *.
           assert (cF_1 = MF.f_1).
           tauto.
         fold tx1 in |- *.
           rewrite <- H8 in |- *.
           rewrite cF_cF_1 in |- *.
           tauto.
          tauto.
          tauto.
        rewrite cF_cF_1 in H11.
         unfold tx1 in H11.
           rewrite H11 in H0.
            absurd (succ m one (top m one x)).
          apply not_succ_top.
             tauto.
          tauto.
         tauto.
         tauto.
        tauto.
        tauto.
       tauto.
       tauto.
       lia.
     assert (i = S j).
      apply (MF.unicity_mod_p m x i (S j)).
        tauto.
       tauto.
      fold p in |- *.
         lia.
      fold p in |- *.
         lia.
      simpl in |- *.
        rewrite H5 in |- *; rewrite H8 in |- *.
        unfold tx1_1 in |- *.
        rewrite cF_cF_1 in |- *.
        tauto.
       tauto.
       tauto.
     elim H9.
        lia.
     tauto.
     tauto.
   clear H5.
     intros.
      absurd (expf m x_1 x).
     tauto.
   unfold expf in |- *.
     split.
     tauto.
   unfold MF.expo in |- *.
     split.
     tauto.
   split with 1.
     simpl in |- *.
     unfold x_1 in |- *.
     rewrite cF_cF_1 in |- *.
     tauto.
    tauto.
    tauto.
   tauto.
  tauto.
intro.
  intros.
  split.
  tauto.
intro.
  clear H5.
  generalize H4.
  clear H4.
  assert (expf m x_1 x).
 unfold expf in |- *.
   split.
   tauto.
 unfold MF.expo in |- *.
   split.
   tauto.
 split with 1.
   simpl in |- *.
   unfold x_1 in |- *.
   rewrite cF_cF_1 in |- *.
   tauto.
  tauto.
  tauto.
elim (expf_dec m x_1 tx1).
 intro.
   elim b.
   apply expf_trans with x_1.
  apply expf_symm.
     tauto.
  tauto.
intro.
  intro.
  assert
   (expf m x tx1 \/
    expf m x_1 x /\ expf m tx1 tx1 \/ 
     expf m x_1 tx1 /\ expf m tx1 x).
 right.
   left.
   split.
   tauto.
 apply expf_refl.
   tauto.
  tauto.
 tauto.
Qed.

(*==================================================
            B0_L0_L0, B1_L1_L1,...
===================================================*)

Lemma B0_L0_L0:forall (m:fmap)(x y x' y':dart),
  let m1 := L (L m zero x y) zero x' y' in
    inv_hmap m1 -> B m1 zero x = L m zero x' y'.
Proof.
simpl in |- *.
intros.
decompose [and] H.
clear H.
unfold prec_L in H1.
unfold succ in H1.
unfold pred in H1.
simpl in H1.
decompose [and] H1.
clear H1.
generalize H0 H5.
clear H0 H5.
unfold prec_L in H3.
generalize H7.
clear H7.
unfold succ in H3.
unfold pred in H3.
decompose [and] H3.
clear H3.
elim (eq_dart_dec x x').
 intros.
    absurd (y <> nil).
   tauto.
 apply exd_not_nil with m.
   tauto.
  tauto.
elim (eq_dart_dec y y').
 intros.
    absurd (x <> nil).
   tauto.
 apply exd_not_nil with m.
   tauto.
  tauto.
elim (eq_dart_dec x' x).
 intro.
   rewrite a in |- *.
    tauto.
elim (eq_dart_dec x x).
  tauto.
 tauto.
Qed.

(* OK: *)

Lemma B1_L1_L1:forall (m:fmap)(x y x' y':dart),
  let m1 := L (L m one x y) one x' y' in
    inv_hmap m1 -> B m1 one x = L m one x' y'.
Proof.
simpl in |- *.
intros.
decompose [and] H.
clear H.
unfold prec_L in H1.
unfold succ in H1.
unfold pred in H1.
simpl in H1.
decompose [and] H1.
clear H1.
generalize H0 H5.
clear H0 H5.
unfold prec_L in H3.
generalize H7.
clear H7.
unfold succ in H3.
unfold pred in H3.
decompose [and] H3.
clear H3.
elim (eq_dart_dec x x').
 intros.
    absurd (y <> nil).
   tauto.
 apply exd_not_nil with m.
   tauto.
  tauto.
elim (eq_dart_dec y y').
 intros.
    absurd (x <> nil).
   tauto.
 apply exd_not_nil with m.
   tauto.
  tauto.
elim (eq_dart_dec x' x).
 intro.
   rewrite a in |- *.
    tauto.
elim (eq_dart_dec x x).
  tauto.
 tauto.
Qed.

(* OK: *)

Lemma B0_L1_L0:forall (m:fmap)(x y x' y':dart),
  let m1 := L (L m zero x y) one x' y' in
    inv_hmap m1 -> B m1 zero x = L m one x' y'.
Proof.
simpl in |- *.
unfold prec_L in |- *.
unfold succ in |- *.
unfold pred in |- *.
simpl in |- *.
intros m x y x' y'.
elim (eq_dart_dec x x).
  tauto.
 tauto.
Qed.

Lemma B1_L0_L1:forall (m:fmap)(x y x' y':dart),
  let m1 := L (L m one x y) zero x' y' in
    inv_hmap m1 -> B m1 one x = L m zero x' y'.
Proof.
simpl in |- *.
unfold prec_L in |- *.
unfold succ in |- *.
unfold pred in |- *.
simpl in |- *.
intros m x y x' y'.
elim (eq_dart_dec x x).
  tauto.
 tauto.
Qed.

(*=====================================================
=======================================================
                     END OF PART 6
=======================================================
=====================================================*)





