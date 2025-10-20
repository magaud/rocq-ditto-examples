(*=====================================================
=======================================================
                 TOPOLOGICAL FMAPS, HMAPS -

                 WITH TAGS AND EMBEDDINGS

                          PART 8:

                    nf_L0L0, nf_L1L1:

          (nf_L0L1 IN FILES Del09 and Del10)

=======================================================
=====================================================*)

Require Export Del07.

(*===================================================
   inv_hmap_L0L0, inv_hmap_L1L1, inv_hmap_L0L1,...
=====================================================*)

(* OK: *)

Lemma inv_hmap_L0L0:forall (m:fmap)(x y x' y':dart),
  let m1:= L (L m zero x y) zero x' y' in
  let m2:= L (L m zero x' y') zero x y in
  inv_hmap m1 -> inv_hmap m2.
Proof.
simpl in |- *.
unfold prec_L in |- *.
unfold succ in |- *.
unfold pred in |- *.
simpl in |- *.
intros m x y x' y'.
intros.
decompose [and] H.
clear H.
generalize H8 H9 H11.
clear H8 H9 H11.
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
elim (eq_dart_dec (cA_1 m zero y) x').
 intros.
   intros.
   split.
  assert (cA m zero x' <> y').
   intro.
     rewrite <- a in H.
     rewrite cA_cA_1 in H.
     tauto.
    tauto.
    tauto.
   tauto.
 split.
   tauto.
 split.
   tauto.
 elim (eq_dart_dec x' x).
  intro.
    symmetry  in a0.
     tauto.
 elim (eq_dart_dec y' y).
  intro.
    symmetry  in a0.
     tauto.
 elim (eq_dart_dec (cA_1 m zero y') x).
  intro.
    rewrite <- a0 in H11.
    rewrite cA_cA_1 in H11.
    tauto.
   tauto.
   tauto.
  tauto.
intros.
  elim (eq_dart_dec x' x).
 intro.
   symmetry  in a.
    tauto.
elim (eq_dart_dec y' y).
 intro.
   symmetry  in a.
    tauto.
elim (eq_dart_dec (cA_1 m zero y') x).
 intro.
   assert (cA m zero x' <> y).
  intro.
    rewrite <- H in b.
    rewrite cA_1_cA in b.
    tauto.
   tauto.
   tauto.
  tauto.
 tauto.
Qed.

(* OK: *)

Lemma inv_hmap_L1L1:forall (m:fmap)(x y x' y':dart),
  let m1:= L (L m one x y) one x' y' in
  let m2:= L (L m one x' y') one x y in
  inv_hmap m1 -> inv_hmap m2.
Proof.
 simpl in |- *.
unfold prec_L in |- *.
unfold succ in |- *.
unfold pred in |- *.
simpl in |- *.
intros m x y x' y'.
intros.
decompose [and] H.
clear H.
generalize H8 H9 H11.
clear H8 H9 H11.
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
elim (eq_dart_dec (cA_1 m one y) x').
 intros.
   intros.
   split.
  assert (cA m one x' <> y').
   intro.
     rewrite <- a in H.
     rewrite cA_cA_1 in H.
     tauto.
    tauto.
    tauto.
   tauto.
 split.
   tauto.
 split.
   tauto.
 elim (eq_dart_dec x' x).
  intro.
    symmetry  in a0.
     tauto.
 elim (eq_dart_dec y' y).
  intro.
    symmetry  in a0.
     tauto.
 elim (eq_dart_dec (cA_1 m one y') x).
  intro.
    rewrite <- a0 in H11.
    rewrite cA_cA_1 in H11.
    tauto.
   tauto.
   tauto.
  tauto.
intros.
  elim (eq_dart_dec x' x).
 intro.
   symmetry  in a.
    tauto.
elim (eq_dart_dec y' y).
 intro.
   symmetry  in a.
    tauto.
elim (eq_dart_dec (cA_1 m one y') x).
 intro.
   assert (cA m one x' <> y).
  intro.
    rewrite <- H in b.
    rewrite cA_1_cA in b.
    tauto.
   tauto.
   tauto.
  tauto.
 tauto.
Qed.

(* IDEM, FOR nf_L0L1 : *)

Lemma inv_hmap_L0L1:forall (m:fmap)(x y x' y':dart),
  let m1:= L (L m zero x y) one x' y' in
  let m2:= L (L m one x' y') zero x y in
  inv_hmap m1 -> inv_hmap m2.
Proof.
simpl in |- *.
unfold prec_L in |- *.
unfold succ in |- *.
unfold pred in |- *.
simpl in |- *.
intros m x y x' y'.
intros.
decompose [and] H.
clear H.
 tauto.
Qed.

(*==================================================
           USEFUL LEMMAS ON betweenf:
====================================================*)

(* OK: *)

Lemma betweenf_expf:forall(m:fmap)(z v t:dart),
 inv_hmap m -> exd m z -> 
  betweenf m z v t -> (expf m z v /\ expf m z t).
Proof.
unfold betweenf in |- *.
unfold expf in |- *.
intros.
generalize (MF.between_expo1 m z v t H H0 H1).
intros.
generalize (MF.expo_expo1 m z v).
generalize (MF.expo_expo1 m z t).
 tauto.
Qed.

(* OK!: *)

Lemma betweenf1 : forall(m:fmap)(u v u' v':dart),
  inv_hmap m -> exd m u' -> u <> u' -> v <> v' -> 
  (betweenf m u' u v' /\ betweenf m u' v v') ->
    (betweenf m u u' v /\ betweenf m u v' v
     \/ betweenf m (cF m v) u' (cF_1 m u) /\
          betweenf m (cF m v) v' (cF_1 m u)).
Proof.
intros.
assert (betweenf m u' u v' /\ betweenf m u' v v').
  tauto.
rename H4 into H3'.
  unfold betweenf in H3.
  unfold MF.between in H3.
  decompose [and] H3.
  clear H3.
  generalize (H4 H H0).
  clear H4.
  intro.
  generalize (H5 H H0).
  clear H5.
  intros.
  elim H3.
  clear H3.
  intros iu Hiu.
  elim Hiu.
  clear Hiu.
  intros jv' Hiv'.
  decompose [and] Hiv'.
  clear Hiv'.
  elim H4.
  clear H4.
  intros iv Hiv.
  elim Hiv.
  clear Hiv.
  intros jv'1 Hjv.
  decompose [and] Hjv.
  clear Hjv.
  set (p := MF.Iter_upb m u') in |- *.
  fold p in H11.
  fold p in H8.
  decompose [and] H3'.
  clear H3'.
  unfold betweenf in H10.
  generalize (MF.between_expo m u' u v' H H0 H10).
  intro.
  unfold betweenf in H12.
  generalize (MF.between_expo m u' v v' H H0 H12).
  intro.
  decompose [and] H13.
  decompose [and] H14.
  clear H13 H14.
  assert (MF.f = cF).
  tauto.
assert (MF.expo m u' (cF m v)).
 apply MF.expo_trans with v.
   tauto.
 assert (exd m v).
  generalize (MF.expo_exd m u' v).
     tauto.
 unfold MF.expo in |- *.
   split.
   tauto.
 split with 1%nat.
   simpl in |- *.
    tauto.
generalize (MF.period_expo m u' u H H15).
  intro.
  generalize (MF.period_expo m u' (cF m v) H H14).
  intro.
  fold p in H19.
  fold p in H20.
  assert (jv' = jv'1).
 apply (MF.unicity_mod_p m u').
   tauto.
  tauto.
 fold p in |- *.
    lia.
 fold p in |- *.
    tauto.
 rewrite H6 in |- *.
   rewrite H9 in |- *.
    tauto.
assert (iu <> 0%nat).
 intro.
   rewrite H22 in H3.
   simpl in H3.
   symmetry  in H3.
    tauto.
assert (iv <> jv').
 intro.
   rewrite <- H21 in H9.
   rewrite <- H23 in H9.
   rewrite H4 in H9.
    tauto.
assert (exd m (cF m v)).
 generalize (MF.expo_exd m u' v).
   generalize (exd_cF m v).
    tauto.
elim (Arith.Compare_dec.le_gt_dec iu iv).
 intro.
   right.
   split.
  unfold betweenf in |- *.
    unfold MF.between in |- *.
    intros.
    split with (p - S iv)%nat.
    split with (p - S iv + (iu - 1))%nat.
    rewrite <- H20 in |- *.
    split.
   rewrite <- MF.Iter_f_f_1 in |- *.
    rewrite H20 in |- *.
      rewrite MF.Iter_upb_period in |- *.
     rewrite MF.Iter_f_1_Si in |- *.
      assert (cF_1 = MF.f_1).
        tauto.
      rewrite <- H27 in |- *.
        rewrite cF_1_cF in |- *.
       rewrite <- H4 in |- *.
         apply MF.Iter_f_f_1_i.
         tauto.
        tauto.
       tauto.
      generalize (exd_cF m v).
         tauto.
      tauto.
      tauto.
     tauto.
     tauto.
    tauto.
    tauto.
    lia.
  split.
   assert (cF_1 = MF.f_1).
     tauto.
   assert ((p - S iv + (iu - 1))%nat = 
           (p + iu - 1 - S iv)%nat).
     lia.
   rewrite H28 in |- *.
     rewrite <- MF.Iter_f_f_1 in |- *.
    rewrite MF.Iter_f_1_Si in |- *.
     rewrite <- H13 in |- *.
       assert (MF.f m v = Iter (MF.f m) 1 v).
      simpl in |- *.
         tauto.
     rewrite H29 in |- *.
       rewrite <- MF.Iter_comp in |- *.
       assert ((p + iu - 1 + 1)%nat = S (p + iu - 1)).
       lia.
     rewrite H30 in |- *.
       rewrite MF.f_1_Iter_f in |- *.
      rewrite MF.Iter_f_f_1 in |- *.
       rewrite <- H4 in |- *.
         rewrite <- MF.Iter_comp in |- *.
         assert ((p + iu - 1 - iv + iv)%nat = 
               (p + iu - 1)%nat).
        clear H28 H30.
           lia.
       rewrite H31 in |- *.
         rewrite <- H3 in |- *.
         assert ((p + iu - 1)%nat = 
   (p + (iu - 1))%nat).
        clear H30 H31 H28.
           lia.
       rewrite H32 in |- *.
         rewrite MF.Iter_plus_inv in |- *.
        assert (iu = S (iu - 1)).
         clear H30 H31 H32.
            lia.
        rewrite H33 in |- *.
          rewrite MF.f_1_Iter_f in |- *.
         rewrite <- H33 in |- *.
            tauto.
         tauto.
         tauto.
        tauto.
        tauto.
       unfold p in |- *.
         apply MF.Iter_upb_period.
         tauto.
        tauto.
       tauto.
      generalize (exd_cF m v).
         tauto.
      clear H28 H30.
         lia.
      tauto.
     generalize (exd_cF m v).
        tauto.
     tauto.
    generalize (MF.exd_Iter_f m (p + iu - 1) (cF m v)).
       tauto.
    tauto.
    tauto.
   clear H28.
      lia.
   lia.
 assert (cF_1 = MF.f_1).
   tauto.
 unfold betweenf in |- *.
   unfold MF.between in |- *.
   intros.
   split with (jv' - S iv)%nat.
   split with (p - S iv + (iu - 1))%nat.
   rewrite <- H20 in |- *.
   split.
  rewrite <- H13 in |- *.
    assert (MF.f m v = Iter (MF.f m) 1 v).
   simpl in |- *.
      tauto.
  rewrite H28 in |- *.
    rewrite <- MF.Iter_comp in |- *.
    rewrite <- H4 in |- *.
    rewrite <- MF.Iter_comp in |- *.
    rewrite <- H9 in |- *.
    rewrite <- H21 in |- *.
    assert ((jv' - S iv + 1 + iv)%nat = jv').
    lia.
  rewrite H29 in |- *.
     tauto.
 split.
  rewrite <- H13 in |- *.
    assert (MF.f m v = Iter (MF.f m) 1 v).
   simpl in |- *.
      tauto.
  rewrite H28 in |- *.
    rewrite <- MF.Iter_comp in |- *.
    rewrite <- H4 in |- *.
    rewrite <- MF.Iter_comp in |- *.
    rewrite <- H3 in |- *.
    rewrite H25 in |- *.
    assert (iu = S (iu - 1)).
    lia.
  rewrite H29 in |- *.
    rewrite MF.f_1_Iter_f in |- *.
   assert ((p - S iv + (S (iu - 1) - 1) + 1 + iv)%nat = 
       (p + (iu - 1))%nat).
    clear H29.
       lia.
   rewrite H30 in |- *.
     apply MF.Iter_plus_inv.
     tauto.
    tauto.
   unfold p in |- *.
     apply MF.Iter_upb_period.
     tauto.
    tauto.
   tauto.
   tauto.
  lia.
intro.
  left.
  split.
 unfold betweenf in |- *.
   unfold MF.between in |- *.
   intros.
   split with (p - iu)%nat.
   split with (p + iv - iu)%nat.
   split.
  rewrite <- H3 in |- *.
    rewrite <- MF.Iter_comp in |- *.
    assert ((p - iu + iu)%nat = p).
    lia.
  rewrite H27 in |- *.
    unfold p in |- *.
    apply MF.Iter_upb_period.
    tauto.
   tauto.
 split.
  rewrite <- H3 in |- *.
    rewrite <- H4 in |- *.
    rewrite <- MF.Iter_comp in |- *.
    assert ((p + iv - iu + iu)%nat = (p + iv)%nat).
    lia.
  rewrite H27 in |- *.
    apply MF.Iter_plus_inv.
    tauto.
   tauto.
  unfold p in |- *.
    apply MF.Iter_upb_period.
    tauto.
   tauto.
 fold p in |- *.
   rewrite <- H19 in |- *.
    lia.
unfold betweenf in |- *.
  unfold MF.between in |- *.
  intros.
  split with (jv' - iu)%nat.
  split with (p - iu + iv)%nat.
  split.
 rewrite <- H3 in |- *.
   rewrite <- MF.Iter_comp in |- *.
   rewrite <- H6 in |- *.
   assert ((jv' - iu + iu)%nat = jv').
   lia.
 rewrite H27 in |- *.
    tauto.
split.
 rewrite <- H3 in |- *.
   rewrite <- H4 in |- *.
   rewrite <- MF.Iter_comp in |- *.
   assert ((p - iu + iv + iu)%nat = (p + iv)%nat).
   lia.
 rewrite H27 in |- *.
   apply MF.Iter_plus_inv.
   tauto.
  tauto.
 unfold p in |- *.
   apply MF.Iter_upb_period.
   tauto.
  tauto.
 lia.
Qed.

(* IDEM : *)

(* THEN, SYMMETRICALLY: OK, TERRIBLE !! *)

Lemma betweenf2:forall(m:fmap)(u v u' v':dart),
  inv_hmap m -> exd m v' -> u <> u' -> v <> v' -> 
   (betweenf m (cF m v') u (cF_1 m u') 
   /\ betweenf m (cF m v') v (cF_1 m u')) ->
     (betweenf m u u' v /\ betweenf m u v' v
     \/ betweenf m (cF m v) u' (cF_1 m u) /\
          betweenf m (cF m v) v' (cF_1 m u)).
Proof.
intros.
assert
 (betweenf m (cF m v') u (cF_1 m u') 
       /\ betweenf m (cF m v') v (cF_1 m u')).
  tauto.
rename H4 into H3'.
  unfold betweenf in H3.
  unfold MF.between in H3.
  decompose [and] H3.
  clear H3.
  assert (exd m (cF m v')).
 generalize (exd_cF m v').
    tauto.
rename H3 into Ev'1.
  generalize (H4 H Ev'1).
  clear H4.
  intro.
  generalize (H5 H Ev'1).
  clear H5.
  intros.
  elim H3.
  clear H3.
  intros iu Hiu.
  elim Hiu.
  clear Hiu.
  intros iu'_1 Hiu'_1.
  decompose [and] Hiu'_1.
  clear Hiu'_1.
  elim H4.
  clear H4.
  intros iv Hiv.
  elim Hiv.
  clear Hiv.
  intros iu'_2 Hiu'_2.
  decompose [and] Hiu'_2.
  clear Hiu'_2.
  set (p := MF.Iter_upb m (cF m v')) in |- *.
  fold p in H11.
  fold p in H8.
  decompose [and] H3'.
  clear H3'.
  unfold betweenf in H10.
  generalize
  (MF.between_expo m (cF m v') u (cF_1 m u') 
      H Ev'1 H10).
  intro.
  unfold betweenf in H12.
  generalize
  (MF.between_expo m (cF m v') v (cF_1 m u')
       H Ev'1 H12).
  intro.
  decompose [and] H13.
  decompose [and] H14.
  clear H13 H14.
  assert (MF.f = cF).
  tauto.
assert (iu'_1 = iu'_2).
 apply (MF.unicity_mod_p m (cF m v')).
   tauto.
  tauto.
 fold p in |- *.
    tauto.
 fold p in |- *.
    tauto.
 rewrite H9 in |- *.
    tauto.
rewrite <- H14 in H7.
  clear H11 H9 H14.
  clear iu'_2.
  assert (MF.f_1 = cF_1).
  tauto.
elim (Nat.eq_dec (p - 1) iv).
 intro.
   assert (v' = Iter (MF.f m) (p - 1) (cF m v')).
  rewrite <- MF.Iter_f_f_1 in |- *.
   unfold p in |- *.
     rewrite MF.Iter_upb_period in |- *.
    simpl in |- *.
      rewrite H9 in |- *.
      rewrite cF_1_cF in |- *.
      tauto.
     tauto.
    generalize (exd_cF_1 m v').
       tauto.
    tauto.
    tauto.
   tauto.
   tauto.
   lia.
 symmetry  in H9.
   rewrite a in H11.
   rewrite H4 in H11.
   symmetry  in H11.
    tauto.
intro.
  assert (exd m (cF_1 m u')).
 rewrite <- H6 in |- *.
   generalize (MF.exd_Iter_f m iu'_1 (cF m v')).
    tauto.
assert (exd m u').
 generalize (exd_cF_1 m u').
    tauto.
elim (Nat.eq_dec (S iu'_1) iu).
 intro.
   assert (Iter (MF.f m) (S iu'_1) (cF m v') = u').
  simpl in |- *.
    rewrite H6 in |- *.
    rewrite H13 in |- *.
    rewrite cF_cF_1 in |- *.
    tauto.
   tauto.
   tauto.
 rewrite a in H19.
   rewrite H3 in H19.
    tauto.
intro.
  set (v'1 := cF m v') in |- *.
  fold v'1 in Ev'1.
  fold v'1 in H3.
  fold v'1 in H6.
  fold v'1 in H4.
  fold v'1 in p.
  fold v'1 in H10.
  fold v'1 in H12.
  fold v'1 in H15.
  fold v'1 in H16.
  fold v'1 in H17.
  fold v'1 in H18.
  set (u'_1 := cF_1 m u') in |- *.
  fold u'_1 in H6.
  fold u'_1 in H10.
  fold u'_1 in H12.
  fold u'_1 in H16.
  fold u'_1 in H18.
  fold u'_1 in H11.
  assert (exd m v).
 apply MF.expo_exd with v'1.
   tauto.
  tauto.
assert (exd m (cF m v)).
 generalize (exd_cF m v).
    tauto.
set (v1 := cF m v) in |- *.
  set (u_1 := cF_1 m u) in |- *.
  assert (MF.expo m v'1 v1).
 apply MF.expo_trans with v.
   tauto.
 unfold MF.expo in |- *.
   split.
   tauto.
 split with 1%nat.
   simpl in |- *.
   unfold v1 in |- *.
    tauto.
assert (p = MF.Iter_upb m v1).
 unfold MF.expo in H21.
   elim H21.
   clear H21.
   intros.
   elim H22.
   intros i Hi.
   rewrite <- Hi in |- *.
   unfold p in |- *.
   apply MF.period_uniform.
   tauto.
  tauto.
elim (Arith.Compare_dec.le_gt_dec iu iv).
 intro.
   right.
   split.
  unfold betweenf in |- *.
    unfold MF.between in |- *.
    intros.
    elim (Nat.eq_dec iu'_1 (p - 1)).
   intro.
     assert (u' = v'1).
    assert (u' = cF m u'_1).
     unfold u'_1 in |- *.
       rewrite cF_cF_1 in |- *.
       tauto.
      tauto.
      tauto.
    rewrite H25 in |- *.
      rewrite <- H6 in |- *.
      rewrite a0 in |- *.
      assert
       (cF m (Iter (MF.f m) (p - 1) v'1) =
        Iter (MF.f m) 1 (Iter (MF.f m) (p - 1) v'1)).
     simpl in |- *.
       rewrite H13 in |- *.
        tauto.
    rewrite H26 in |- *.
      clear H26.
      rewrite <- MF.Iter_comp in |- *.
      assert ((1 + (p - 1))%nat = p).
      lia.
    rewrite H26 in |- *.
      clear H26.
      unfold p in |- *.
      rewrite MF.Iter_upb_period in |- *.
      tauto.
     tauto.
     tauto.
   assert (u <> v'1).
    intro.
      rewrite <- H25 in H26.
       tauto.
   assert (iu <> 0%nat).
    intro.
      rewrite H27 in H3.
      simpl in H3.
      symmetry  in H3.
       tauto.
   clear H23.
     clear H26.
     split with (p - S iv)%nat.
     split with (p - S iv + iu - 1)%nat.
     rewrite <- H22 in |- *.
     split.
    rewrite <- MF.Iter_f_f_1 in |- *.
     rewrite H22 in |- *.
       rewrite MF.Iter_upb_period in |- *.
      unfold v1 in |- *.
        rewrite <- H4 in |- *.
        simpl in |- *.
        rewrite H9 in |- *.
        assert (cF m (Iter (MF.f m) iv v'1) =
         Iter (MF.f m) (S iv) v'1).
       simpl in |- *.
         rewrite H13 in |- *.
          tauto.
      rewrite H23 in |- *.
        assert
         (cF_1 m (Iter (cF_1 m) iv 
           (Iter (MF.f m) (S iv) v'1)) =
          Iter (cF_1 m) (S iv) 
            (Iter (MF.f m) (S iv) v'1)).
       simpl in |- *.
          tauto.
      rewrite H26 in |- *.
        rewrite <- H9 in |- *.
        rewrite MF.Iter_f_f_1_i in |- *.
       assert (u' = cF m u'_1).
        unfold u'_1 in |- *.
          rewrite cF_cF_1 in |- *.
          tauto.
         tauto.
         tauto.
       rewrite H28 in |- *.
         rewrite <- H6 in |- *.
         rewrite a0 in |- *.
         rewrite <- MF.Iter_f_f_1 in |- *.
        simpl in |- *.
          rewrite <- H13 in |- *.
          rewrite MF.f_f_1 in |- *.
         unfold p in |- *.
           rewrite MF.Iter_upb_period in |- *.
           tauto.
          tauto.
          tauto.
         tauto.
        unfold p in |- *.
          rewrite MF.Iter_upb_period in |- *.
          tauto.
         tauto.
         tauto.
        tauto.
        tauto.
        lia.
       tauto.
       tauto.
      tauto.
      tauto.
     tauto.
     tauto.
     lia.
   split.
    unfold v1 in |- *.
      rewrite <- H4 in |- *.
      assert (cF m (Iter (MF.f m) iv v'1) =
       Iter (MF.f m) (S iv) v'1).
     simpl in |- *.
       rewrite H13 in |- *.
        tauto.
    rewrite H23 in |- *.
      rewrite <- MF.Iter_comp in |- *.
      assert ((p - S iv + iu - 1 + S iv)%nat = 
         (iu - 1 + p)%nat).
      lia.
    rewrite H26 in |- *.
      clear H26.
      rewrite MF.Iter_comp in |- *.
      unfold p in |- *.
      rewrite MF.Iter_upb_period in |- *.
     rewrite <- MF.Iter_f_f_1 in |- *.
      rewrite H3 in |- *.
        simpl in |- *.
        unfold u_1 in |- *.
         tauto.
      tauto.
      tauto.
      lia.
     tauto.
     tauto.
    lia.
  intro.
    elim (Nat.eq_dec iu 0).
   intro.
     assert (u = v'1).
    rewrite a0 in H3.
      simpl in H3.
      symmetry  in |- *.
       tauto.
   split with (S iu'_1 - S iv)%nat.
     split with (p - S iv - 1)%nat.
     rewrite <- H22 in |- *.
     split.
    unfold v1 in |- *.
      rewrite <- H4 in |- *.
      assert (cF m (Iter (MF.f m) iv v'1) = 
       Iter (MF.f m) (S iv) v'1).
     simpl in |- *.
       rewrite H13 in |- *.
        tauto.
    rewrite H26 in |- *.
      rewrite <- MF.Iter_comp in |- *.
      assert ((S iu'_1 - S iv + S iv)%nat = S iu'_1).
      lia.
    rewrite H27 in |- *.
      clear H27 H26.
      simpl in |- *.
      rewrite H6 in |- *.
      unfold u'_1 in |- *.
      rewrite H13 in |- *.
      rewrite cF_cF_1 in |- *.
      tauto.
     tauto.
     tauto.
   split.
    unfold v1 in |- *.
      rewrite <- H4 in |- *.
      assert (cF m (Iter (MF.f m) iv v'1) =
        Iter (MF.f m) (S iv) v'1).
     simpl in |- *.
       rewrite H13 in |- *.
        tauto.
    rewrite H26 in |- *.
      rewrite <- MF.Iter_comp in |- *.
      assert ((p - S iv - 1 + S iv)%nat = (p - 1)%nat).
      lia.
    rewrite H27 in |- *.
      clear H27.
      rewrite <- MF.Iter_f_f_1 in |- *.
     unfold p in |- *.
       rewrite MF.Iter_upb_period in |- *.
      simpl in |- *.
        rewrite <- H25 in |- *.
        unfold u_1 in |- *.
         tauto.
      tauto.
      tauto.
     tauto.
     tauto.
     lia.
    lia.
  intro.
    split with (S iu'_1 - S iv)%nat.
    split with (p - S iv + iu - 1)%nat.
    rewrite <- H22 in |- *.
    split.
   unfold v1 in |- *.
     rewrite <- H4 in |- *.
     assert (cF m (Iter (MF.f m) iv v'1) = 
        Iter (MF.f m) (S iv) v'1).
    simpl in |- *.
      rewrite H13 in |- *.
       tauto.
   rewrite H25 in |- *.
     rewrite <- MF.Iter_comp in |- *.
     assert ((S iu'_1 - S iv + S iv)%nat = S iu'_1).
     lia.
   rewrite H26 in |- *.
     clear H25 H26.
     simpl in |- *.
     rewrite H6 in |- *.
     unfold u'_1 in |- *.
     rewrite H13 in |- *.
     rewrite cF_cF_1 in |- *.
     tauto.
    tauto.
    tauto.
  split.
   unfold v1 in |- *.
     rewrite <- H4 in |- *.
     assert (cF m (Iter (MF.f m) iv v'1) =
      Iter (MF.f m) (S iv) v'1).
    simpl in |- *.
      rewrite H13 in |- *.
       tauto.
   rewrite H25 in |- *.
     rewrite <- MF.Iter_comp in |- *.
     assert ((p - S iv + iu - 1 + S iv)%nat = 
        (iu - 1 + p)%nat).
     lia.
   rewrite H26 in |- *.
     clear H26.
     clear H25.
     rewrite MF.Iter_comp in |- *.
     unfold p in |- *.
     rewrite MF.Iter_upb_period in |- *.
    rewrite <- MF.Iter_f_f_1 in |- *.
     rewrite H3 in |- *.
       simpl in |- *.
       unfold u_1 in |- *.
        tauto.
     tauto.
     tauto.
     lia.
    tauto.
    tauto.
   lia.
 assert (cF m (Iter (MF.f m) iv v'1) = 
 Iter (MF.f m) (S iv) v'1).
  simpl in |- *.
    rewrite H13 in |- *.
     tauto.
 rewrite H4 in H23.
   unfold betweenf in |- *.
   unfold MF.between in |- *.
   intros.
   clear H24.
   rewrite <- H22 in |- *.
   elim (Nat.eq_dec iu 0).
  split with (p - 1 - S iv)%nat.
    split with (p - S iv - 1)%nat.
    split.
   unfold v1 in |- *.
     rewrite H23 in |- *.
     rewrite <- MF.Iter_comp in |- *.
     assert ((p - 1 - S iv + S iv)%nat = (p - 1)%nat).
     lia.
   rewrite H24 in |- *.
     clear H24.
     rewrite <- MF.Iter_f_f_1 in |- *.
    unfold p in |- *.
      rewrite MF.Iter_upb_period in |- *.
     simpl in |- *.
       unfold v'1 in |- *.
       rewrite H9 in |- *.
       rewrite cF_1_cF in |- *.
       tauto.
      tauto.
     generalize (exd_cF m v').
       fold v'1 in |- *.
        tauto.
     tauto.
     tauto.
    tauto.
    tauto.
    lia.
  split.
   unfold v1 in |- *.
     rewrite H23 in |- *.
     rewrite <- MF.Iter_comp in |- *.
     assert ((p - S iv - 1 + S iv)%nat = (p - 1)%nat).
     lia.
   rewrite H24 in |- *.
     rewrite <- MF.Iter_f_f_1 in |- *.
    unfold p in |- *.
      rewrite MF.Iter_upb_period in |- *.
     simpl in |- *.
       unfold v'1 in |- *.
       rewrite H9 in |- *.
       rewrite cF_1_cF in |- *.
      rewrite a0 in H3.
        simpl in H3.
        unfold u_1 in |- *.
        rewrite <- H3 in |- *.
        unfold v'1 in |- *.
        rewrite cF_1_cF in |- *.
        tauto.
       tauto.
       tauto.
      tauto.
      tauto.
     tauto.
     tauto.
    tauto.
    tauto.
    lia.
   lia.
 intro.
   split with (p - 1 - S iv)%nat.
   split with (p - S iv + iu - 1)%nat.
   split.
  unfold v1 in |- *.
    rewrite H23 in |- *.
    rewrite <- MF.Iter_comp in |- *.
    assert ((p - 1 - S iv + S iv)%nat = (p - 1)%nat).
    lia.
  rewrite H24 in |- *.
    clear H24.
    rewrite <- MF.Iter_f_f_1 in |- *.
   unfold p in |- *.
     rewrite MF.Iter_upb_period in |- *.
    simpl in |- *.
      unfold v'1 in |- *.
      rewrite H9 in |- *.
      rewrite cF_1_cF in |- *.
      tauto.
     tauto.
    generalize (exd_cF m v').
      fold v'1 in |- *.
       tauto.
    tauto.
    tauto.
   tauto.
   tauto.
   lia.
 split.
  unfold v1 in |- *.
    rewrite H23 in |- *.
    rewrite <- MF.Iter_comp in |- *.
    assert ((p - S iv + iu - 1 + S iv)%nat = 
       (p + (iu - 1))%nat).
    lia.
  rewrite H24 in |- *.
    clear H24.
    rewrite Nat.add_comm in |- *.
    rewrite MF.Iter_comp in |- *.
    unfold p in |- *.
    rewrite MF.Iter_upb_period in |- *.
   simpl in |- *.
     rewrite <- MF.Iter_f_f_1 in |- *.
    rewrite H3 in |- *.
      simpl in |- *.
      unfold u_1 in |- *.
       tauto.
    tauto.
    tauto.
    lia.
   tauto.
   tauto.
  lia.
intro.
  left.
  unfold betweenf in |- *.
  assert (p = MF.Iter_upb m u).
 rewrite <- H3 in |- *.
   unfold p in |- *.
   apply MF.period_uniform.
   tauto.
  tauto.
split.
 unfold MF.between in |- *.
   intros.
   clear H24.
   split with (iu'_1 + 1 - iu)%nat.
   split with (p + iv - iu)%nat.
   rewrite <- H23 in |- *.
   split.
  rewrite <- H3 in |- *.
    rewrite <- MF.Iter_comp in |- *.
    assert ((iu'_1 + 1 - iu + iu)%nat = S iu'_1).
    lia.
  rewrite H24 in |- *.
    clear H24.
    simpl in |- *.
    rewrite H6 in |- *.
    unfold u'_1 in |- *.
    rewrite H13 in |- *.
    rewrite cF_cF_1 in |- *.
    tauto.
   tauto.
   tauto.
 split.
  rewrite <- H3 in |- *.
    rewrite <- MF.Iter_comp in |- *.
    assert ((p + iv - iu + iu)%nat = (iv + p)%nat).
    lia.
  rewrite H24 in |- *.
    clear H24.
    rewrite MF.Iter_comp in |- *.
    unfold p in |- *.
    rewrite MF.Iter_upb_period in |- *.
    tauto.
   tauto.
   tauto.
  lia.
unfold betweenf in |- *.
  unfold MF.between in |- *.
  intros.
  clear H24.
  split with (p - 1 - iu)%nat.
  split with (p - iu + iv)%nat.
  rewrite <- H23 in |- *.
  split.
 rewrite <- H3 in |- *.
   rewrite <- MF.Iter_comp in |- *.
   assert ((p - 1 - iu + iu)%nat = (p - 1)%nat).
   lia.
 rewrite H24 in |- *.
   clear H24.
   rewrite <- MF.Iter_f_f_1 in |- *.
  unfold p in |- *.
    rewrite MF.Iter_upb_period in |- *.
   simpl in |- *.
     unfold v'1 in |- *.
     rewrite H9 in |- *.
     rewrite cF_1_cF in |- *.
     tauto.
    tauto.
   generalize (exd_cF m v').
     fold v'1 in |- *.
      tauto.
   tauto.
   tauto.
  tauto.
  tauto.
  lia.
split.
 rewrite <- H3 in |- *.
   rewrite <- MF.Iter_comp in |- *.
   assert ((p - iu + iv + iu)%nat = (p + iv)%nat).
   lia.
 rewrite H24 in |- *.
   clear H24.
   rewrite Nat.add_comm in |- *.
   rewrite MF.Iter_comp in |- *.
   unfold p in |- *.
   rewrite MF.Iter_upb_period in |- *.
  simpl in |- *.
     tauto.
  tauto.
  tauto.
lia.
Qed.

(* OK, TRIVIAL: USEFUL? 

Lemma nf_L_B_aux :forall(m:fmap)(k:dim)(x:dart),
 inv_hmap m -> succ m k x ->
  let y := A m k x in
  let m0 := B m k x in
  let m1 := L m0 k x (A m k x) in
   nf m1 = 
     match k with
      | zero =>
          let x_1 := cA_1 m0 one x in
          nf m0 +
          (if expof_dec m0 x_1 y then 1 else -1)
      | one =>
          let y0 := cA m0 zero y in
          nf m0 +
          (if expof_dec m0 x y0 then 1 else -1)
      end.
Proof.
simpl in |- *.
tauto.
Qed.

*)

(*=================================================
           6 LEMMAS FOR nf_L0L0
==================================================*)

(* DO THE SAME FOR nf_L1L1 *)

(* OK: *)

Lemma nf_L0L0_I:forall (m:fmap)(x y x' y':dart),
  let m1:= L (L m zero x y) zero x' y' in
  let m2:= L (L m zero x' y') zero x y in
    inv_hmap m1 -> 
    let x_1  := cA_1 m one x in
    let x'_1 := cA_1 m one x' in
     expf m x_1 y -> 
     expf m x'_1 y' ->
       expf (L m zero x' y') x_1 y ->
       ~ expf (L m zero x y) x'_1 y' ->
          nf m1 = nf m2.
Proof.
intros.
rename H0 into E0.
rename H1 into E1.
rename H2 into E2.
rename H3 into E3.
assert (inv_hmap m2).
 unfold m2 in |- *.
   apply inv_hmap_L0L0.
   fold m1 in |- *.
    tauto.
unfold m1 in |- *.
  unfold m2 in |- *.
  simpl in |- *.
  assert (inv_hmap m1).
  tauto.
assert (inv_hmap m2).
  tauto.
unfold m1 in H1.
  unfold m2 in H2.
  simpl in H1.
  simpl in H2.
  unfold prec_L in H1.
  unfold prec_L in H2.
  unfold pred in H1.
  unfold pred in H2.
  unfold succ in H1.
  unfold succ in H2.
  simpl in H1.
  simpl in H2.
  decompose [and] H1.
  clear H1.
  decompose [and] H2.
  clear H2.
  generalize H11 H14 H21 H24.
  elim (eq_dart_dec x x').
 intros.
   elim H2.
   apply exd_not_nil with m.
   tauto.
  tauto.
elim (eq_dart_dec x' x).
 intros.
   elim H25.
   apply exd_not_nil with m.
   tauto.
 auto.
clear H11 H14 H21 H24.
  intros.
  generalize H12 H22.
  clear H12 H22.
  elim (eq_dart_dec y y').
 intros.
   elim H12.
   apply exd_not_nil with m.
   tauto.
  tauto.
elim (eq_dart_dec y' y).
 intros.
   elim H22.
   apply exd_not_nil with m.
   tauto.
  tauto.
intros.
  clear H13 H19 H1 H16.
  clear H11 H21 H12 H22.
  clear H15.
  clear b0 b2.
  set (xb0 := cA m zero x) in |- *.
  fold xb0 in H14.
  set (x'b0 := cA m zero x') in |- *.
  fold x'b0 in H24.
  set (yt0 := cA_1 m zero y) in |- *.
  fold yt0 in H14.
  set (y't0 := cA_1 m zero y') in |- *.
  fold y't0 in H24.
  assert (inv_hmap (L m zero x y)).
 simpl in |- *.
   unfold m1 in H.
   simpl in H.
    tauto.
assert (exd m x'_1).
 unfold x'_1 in |- *.
   generalize (exd_cA_1 m one x').
    tauto.
assert (inv_hmap (L m zero x' y')).
 simpl in |- *.
   unfold m2 in H0.
   simpl in H0.
    tauto.
assert (exd m x_1).
 unfold x_1 in |- *.
   generalize (exd_cA_1 m one x).
    tauto.
generalize (expf_L0_CNS m x y x'_1 y' H1 H2).
  simpl in |- *.
  fold x_1 in |- *.
  fold xb0 in |- *.
  fold yt0 in |- *.
  set (yt0_1 := cA_1 m one yt0) in |- *.
  intro.
  generalize (expf_L0_CNS m x' y' x_1 y H11 H12).
  simpl in |- *.
  fold x'_1 in |- *.
  fold x'b0 in |- *.
  fold y't0 in |- *.
  set (y't0_1 := cA_1 m one y't0) in |- *.
  intro.
  generalize H13.
  clear H13.
(* DEBUT DU RAISONNEMENT: *)
  elim (expf_dec m x_1 y).
 generalize H15.
   clear H15.
   elim (expf_dec m x'_1 y').
  intros.
    elim (expf_dec (L m zero x' y') x_1 y).
   elim (expf_dec (L m zero x y) x'_1 y').
     tauto.
   intros.
     clear a a0 b0 a1.
     assert
     (betweenf m x'_1 x_1 y' /\ betweenf m x'_1 y y' \/
      betweenf m y't0_1 x_1 x'b0 /\ 
           betweenf m y't0_1 y x'b0 \/
       ~ expf m x'_1 x_1 /\ expf m x_1 y).
    clear H13 H14 H24 b b1 H7 H8 H17 H18.
      clear H10 E0 E1 E3.
       tauto.
   clear H15.
     clear E2.
     generalize (expf_dec (L m zero x y) x'_1 y').
     intro.
     assert
      (~
       (betweenf m x_1 x'_1 y /\ betweenf m x_1 y' y \/
        betweenf m yt0_1 x'_1 xb0 /\ 
             betweenf m yt0_1 y' xb0 \/
        ~ expf m x_1 x'_1 /\ expf m x'_1 y')).
    clear H16 H7 H8 H17 H18 b b1 E0 E1.
       tauto.
   clear H13 E3 H15.
     elim H19.
     clear H19.
     elim H16.
    clear H16.
      intro.
      assert (yt0_1 = cF m y).
     unfold yt0_1 in |- *.
       unfold yt0 in |- *.
       fold (cF m y) in |- *.
        tauto.
    assert (xb0 = cF_1 m x_1).
     unfold xb0 in |- *.
       unfold x_1 in |- *.
       unfold cF_1 in |- *.
       rewrite cA_cA_1 in |- *.
       tauto.
      tauto.
      tauto.
    rewrite H15 in |- *.
      rewrite H16 in |- *.
      assert (y <> y').
     intro.
       symmetry  in H19.
        tauto.
    assert (x_1 <> x'_1).
     intro.
       assert (cA m one x_1 = cA m one x'_1).
      rewrite H21 in |- *.
         tauto.
     unfold x_1 in H22.
       unfold x'_1 in H22.
       rewrite cA_cA_1 in H22.
      rewrite cA_cA_1 in H22.
       symmetry  in H22.
          tauto.
       tauto.
       tauto.
      tauto.
      tauto.
    generalize 
  (betweenf1 m x_1 y x'_1 y' H5 H2 H21 H19).
      clear H19 H21 H7 H8 H17 H18 E0 E1 H20.
       tauto.
   clear H16.
     intros.
     elim H13; clear H13; intro.
    assert (yt0_1 = cF m y).
     unfold yt0_1 in |- *.
       unfold yt0 in |- *.
       fold (cF m y) in |- *.
        tauto.
    assert (xb0 = cF_1 m x_1).
     unfold xb0 in |- *.
       unfold x_1 in |- *.
       unfold cF_1 in |- *.
       rewrite cA_cA_1 in |- *.
       tauto.
      tauto.
      tauto.
    assert (y't0_1 = cF m y').
     unfold y't0_1 in |- *.
       unfold y't0 in |- *.
       fold (cF m y') in |- *.
        tauto.
    assert (x'b0 = cF_1 m x'_1).
     unfold x'b0 in |- *.
       unfold x'_1 in |- *.
       unfold cF_1 in |- *.
       rewrite cA_cA_1 in |- *.
       tauto.
      tauto.
      tauto.
    rewrite H15 in |- *.
      rewrite H16 in |- *.
      rewrite H19 in H13.
      rewrite H21 in H13.
      assert (y <> y').
     intro.
       symmetry  in H22.
        tauto.
    assert (x_1 <> x'_1).
     intro.
       assert (cA m one x_1 = cA m one x'_1).
      rewrite H23 in |- *.
         tauto.
     unfold x_1 in H25.
       unfold x'_1 in H25.
       rewrite cA_cA_1 in H25.
      rewrite cA_cA_1 in H25.
       symmetry  in H25.
          tauto.
       tauto.
       tauto.
      tauto.
      tauto.
    generalize 
        (betweenf2 m x_1 y x'_1 y' H5 H4 H23 H22).
      clear H22 H23 H7 H8 H17 H18 H12 H2 E0 E1 H10.
       tauto.
   right.
     right.
     split.
    intro.
      assert (expf m x'_1 x_1).
     apply expf_symm.
        tauto.
     tauto.
    tauto.
   tauto.
  tauto.
 tauto.
Qed.

(*OK: *)

Lemma nf_L0L0_II:forall (m:fmap)(x y x' y':dart),
  let m1:= L (L m zero x y) zero x' y' in
  let m2:= L (L m zero x' y') zero x y in
    inv_hmap m1 -> 
    let x_1  := cA_1 m one x in
    let x'_1 := cA_1 m one x' in
     expf m x_1 y -> 
     ~ expf m x'_1 y' ->
        expf (L m zero x' y') x_1 y ->
        expf (L m zero x y) x'_1 y' ->
            nf m1 = nf m2.
Proof.
intros.
rename H0 into E0.
rename H1 into E1.
rename H2 into E2.
rename H3 into E3.
assert (inv_hmap m2).
 unfold m2 in |- *.
   apply inv_hmap_L0L0.
   fold m1 in |- *.
    tauto.
unfold m1 in |- *.
  unfold m2 in |- *.
  simpl in |- *.
  assert (inv_hmap m1).
  tauto.
assert (inv_hmap m2).
  tauto.
unfold m1 in H1.
  unfold m2 in H2.
  simpl in H1.
  simpl in H2.
  unfold prec_L in H1.
  unfold prec_L in H2.
  unfold pred in H1.
  unfold pred in H2.
  unfold succ in H1.
  unfold succ in H2.
  simpl in H1.
  simpl in H2.
  decompose [and] H1.
  clear H1.
  decompose [and] H2.
  clear H2.
  generalize H11 H14 H21 H24.
  elim (eq_dart_dec x x').
 intros.
   elim H2.
   apply exd_not_nil with m.
   tauto.
  tauto.
elim (eq_dart_dec x' x).
 intros.
   elim H25.
   apply exd_not_nil with m.
   tauto.
 auto.
clear H11 H14 H21 H24.
  intros.
  generalize H12 H22.
  clear H12 H22.
  elim (eq_dart_dec y y').
 intros.
   elim H12.
   apply exd_not_nil with m.
   tauto.
  tauto.
elim (eq_dart_dec y' y).
 intros.
   elim H22.
   apply exd_not_nil with m.
   tauto.
  tauto.
intros.
  clear H13 H19 H1 H16.
  clear H11 H21 H12 H22.
  clear H15.
  clear b0 b2.
  set (xb0 := cA m zero x) in |- *.
  fold xb0 in H14.
  set (x'b0 := cA m zero x') in |- *.
  fold x'b0 in H24.
  set (yt0 := cA_1 m zero y) in |- *.
  fold yt0 in H14.
  set (y't0 := cA_1 m zero y') in |- *.
  fold y't0 in H24.
  assert (inv_hmap (L m zero x y)).
 simpl in |- *.
   unfold m1 in H.
   simpl in H.
    tauto.
assert (exd m x'_1).
 unfold x'_1 in |- *.
   generalize (exd_cA_1 m one x').
    tauto.
assert (inv_hmap (L m zero x' y')).
 simpl in |- *.
   unfold m2 in H0.
   simpl in H0.
    tauto.
assert (exd m x_1).
 unfold x_1 in |- *.
   generalize (exd_cA_1 m one x).
    tauto.
generalize (expf_L0_CNS m x y x'_1 y' H1 H2).
  simpl in |- *.
  fold x_1 in |- *.
  fold xb0 in |- *.
  fold yt0 in |- *.
  set (yt0_1 := cA_1 m one yt0) in |- *.
  intro.
  generalize (expf_L0_CNS m x' y' x_1 y H11 H12).
  simpl in |- *.
  fold x'_1 in |- *.
  fold x'b0 in |- *.
  fold y't0 in |- *.
  set (y't0_1 := cA_1 m one y't0) in |- *.
  intro.
  generalize H13.
  clear H13.
  elim (expf_dec m x_1 y).
 generalize H15.
   clear H15.
   elim (expf_dec m x'_1 y').
  intros.
     tauto.
 elim (expf_dec (L m zero x' y') x_1 y).
  elim (expf_dec (L m zero x y) x'_1 y').
   intros.
     clear a a0 b0 a1.
     assert
   (betweenf m x_1 x'_1 y /\ betweenf m x_1 y' y \/
   betweenf m yt0_1 x'_1 xb0 /\
         betweenf m yt0_1 y' xb0 \/
  ~ expf m x_1 x'_1 /\ expf m x'_1 y').
    clear H15 H7 H8 H17 H18.
       tauto.
   clear H13.
     clear H15.
     elim E1.
     clear E1.
     elim H16; clear H16; intro.
    decompose [and] H13.
      clear H13.
      generalize 
        (betweenf_expf m x_1 x'_1 y H5 H12 H15).
      intro.
      generalize (betweenf_expf m x_1 y' y H5 H12 H16).
      intro.
      apply expf_trans with x_1.
     apply expf_symm.
        tauto.
     tauto.
   elim H13.
    clear H13.
      intros.
      decompose [and] H13.
      clear H13.
      assert (exd m yt0_1).
     unfold yt0_1 in |- *.
       generalize (exd_cA_1 m one yt0).
       assert (exd m yt0).
      unfold yt0 in |- *.
        generalize (exd_cA_1 m zero y).
         tauto.
      tauto.
    generalize 
    (betweenf_expf m yt0_1 x'_1 xb0 H5 H13 H15).
      generalize
    (betweenf_expf m yt0_1 y' xb0 H5 H13 H16).
      intros.
      apply expf_trans with yt0_1.
     apply expf_symm.
        tauto.
     tauto.
   clear H13.
      tauto.
   tauto.
  tauto.
 tauto.
Qed.

(* OK: *)

Lemma nf_L0L0_III:forall (m:fmap)(x y x' y':dart),
  let m1:= L (L m zero x y) zero x' y' in
  let m2:= L (L m zero x' y') zero x y in
    inv_hmap m1 -> 
    let x_1  := cA_1 m one x in
    let x'_1 := cA_1 m one x' in
     expf m x_1 y -> 
     ~ expf m x'_1 y' ->
         expf (L m zero x' y') x_1 y ->
         ~ expf (L m zero x y) x'_1 y' ->
            nf m1 = nf m2.
Proof.
intros.
unfold m1 in |- *.
unfold m2 in |- *.
simpl in |- *.
fold x_1 in |- *.
fold x'_1 in |- *.
elim (expf_dec m x_1 y).
 elim (expf_dec m x'_1 y').
   tauto.
 elim (expf_dec (L m zero x' y') x_1 y).
  elim (expf_dec (L m zero x y) x'_1 y').
    tauto.
  intros.
     lia.
  tauto.
 tauto.
Qed.

(* OK: *)

Lemma nf_L0L0_IV:forall (m:fmap)(x y x' y':dart),
  let m1:= L (L m zero x y) zero x' y' in
  let m2:= L (L m zero x' y') zero x y in
    inv_hmap m1 -> 
    let x_1  := cA_1 m one x in
    let x'_1 := cA_1 m one x' in
     expf m x_1 y -> 
     ~ expf m x'_1 y' ->
        ~ expf (L m zero x' y') x_1 y ->
        expf (L m zero x y) x'_1 y' ->
            nf m1 = nf m2.
Proof.
intros.
rename H0 into E0.
rename H1 into E1.
rename H2 into E2.
rename H3 into E3.
assert (inv_hmap m2).
 unfold m2 in |- *.
   apply inv_hmap_L0L0.
   fold m1 in |- *.
    tauto.
unfold m1 in |- *.
  unfold m2 in |- *.
  simpl in |- *.
  assert (inv_hmap m1).
  tauto.
assert (inv_hmap m2).
  tauto.
unfold m1 in H1.
  unfold m2 in H2.
  simpl in H1.
  simpl in H2.
  unfold prec_L in H1.
  unfold prec_L in H2.
  unfold pred in H1.
  unfold pred in H2.
  unfold succ in H1.
  unfold succ in H2.
  simpl in H1.
  simpl in H2.
  decompose [and] H1.
  clear H1.
  decompose [and] H2.
  clear H2.
  generalize H11 H14 H21 H24.
  elim (eq_dart_dec x x').
 intros.
   elim H2.
   apply exd_not_nil with m.
   tauto.
  tauto.
elim (eq_dart_dec x' x).
 intros.
   elim H25.
   apply exd_not_nil with m.
   tauto.
 auto.
clear H11 H14 H21 H24.
  intros.
  generalize H12 H22.
  clear H12 H22.
  elim (eq_dart_dec y y').
 intros.
   elim H12.
   apply exd_not_nil with m.
   tauto.
  tauto.
elim (eq_dart_dec y' y).
 intros.
   elim H22.
   apply exd_not_nil with m.
   tauto.
  tauto.
intros.
  clear H13 H19 H1 H16.
  clear H11 H21 H12 H22.
  clear H15.
  clear b0 b2.
  set (xb0 := cA m zero x) in |- *.
  fold xb0 in H14.
  set (x'b0 := cA m zero x') in |- *.
  fold x'b0 in H24.
  set (yt0 := cA_1 m zero y) in |- *.
  fold yt0 in H14.
  set (y't0 := cA_1 m zero y') in |- *.
  fold y't0 in H24.
  assert (inv_hmap (L m zero x y)).
 simpl in |- *.
   unfold m1 in H.
   simpl in H.
    tauto.
assert (exd m x'_1).
 unfold x'_1 in |- *.
   generalize (exd_cA_1 m one x').
    tauto.
assert (inv_hmap (L m zero x' y')).
 simpl in |- *.
   unfold m2 in H0.
   simpl in H0.
    tauto.
assert (exd m x_1).
 unfold x_1 in |- *.
   generalize (exd_cA_1 m one x).
    tauto.
generalize (expf_L0_CNS m x y x'_1 y' H1 H2).
  simpl in |- *.
  fold x_1 in |- *.
  fold xb0 in |- *.
  fold yt0 in |- *.
  set (yt0_1 := cA_1 m one yt0) in |- *.
  intro.
  generalize (expf_L0_CNS m x' y' x_1 y H11 H12).
  simpl in |- *.
  fold x'_1 in |- *.
  fold x'b0 in |- *.
  fold y't0 in |- *.
  set (y't0_1 := cA_1 m one y't0) in |- *.
  intro.
  generalize H13.
  clear H13.
  elim (expf_dec m x_1 y).
 generalize H15.
   clear H15.
   elim (expf_dec m x'_1 y').
  intros.
     tauto.
 elim (expf_dec (L m zero x' y') x_1 y).
   tauto.
 elim (expf_dec (L m zero x y) x'_1 y').
  intros.
    clear a a0 b0 b2.
    assert
     (~
      (expf m x_1 y \/
       expf m x_1 y' /\ expf m y x'b0 \/ expf m y y' 
         /\ expf m x_1 x'b0)).
   clear H13 H7 H8 H17 H18 b b1.
     generalize (expf_dec (L m zero x' y') x_1 y).
      tauto.
  clear H15 E2.
    clear H13 H7 H17 H18 b b1.
     tauto.
  tauto.
 tauto.
Qed.

(* OK: *)

Lemma nf_L0L0_V:forall (m:fmap)(x y x' y':dart),
  let m1:= L (L m zero x y) zero x' y' in
  let m2:= L (L m zero x' y') zero x y in
    inv_hmap m1 -> 
    let x_1  := cA_1 m one x in
    let x'_1 := cA_1 m one x' in
     ~ expf m x_1 y -> 
     ~ expf m x'_1 y' ->
        expf (L m zero x' y') x_1 y ->
        ~ expf (L m zero x y) x'_1 y' ->
            nf m1 = nf m2.
Proof.
intros.
rename H0 into E0.
rename H1 into E1.
rename H2 into E2.
rename H3 into E3.
assert (inv_hmap m2).
 unfold m2 in |- *.
   apply inv_hmap_L0L0.
   fold m1 in |- *.
    tauto.
unfold m1 in |- *.
  unfold m2 in |- *.
  simpl in |- *.
  assert (inv_hmap m1).
  tauto.
assert (inv_hmap m2).
  tauto.
unfold m1 in H1.
  unfold m2 in H2.
  simpl in H1.
  simpl in H2.
  unfold prec_L in H1.
  unfold prec_L in H2.
  unfold pred in H1.
  unfold pred in H2.
  unfold succ in H1.
  unfold succ in H2.
  simpl in H1.
  simpl in H2.
  decompose [and] H1.
  clear H1.
  decompose [and] H2.
  clear H2.
  generalize H11 H14 H21 H24.
  elim (eq_dart_dec x x').
 intros.
   elim H2.
   apply exd_not_nil with m.
   tauto.
  tauto.
elim (eq_dart_dec x' x).
 intros.
   elim H25.
   apply exd_not_nil with m.
   tauto.
 auto.
clear H11 H14 H21 H24.
  intros.
  generalize H12 H22.
  clear H12 H22.
  elim (eq_dart_dec y y').
 intros.
   elim H12.
   apply exd_not_nil with m.
   tauto.
  tauto.
elim (eq_dart_dec y' y).
 intros.
   elim H22.
   apply exd_not_nil with m.
   tauto.
  tauto.
intros.
  clear H13 H19 H1 H16.
  clear H11 H21 H12 H22.
  clear H15.
  clear b0 b2.
  set (xb0 := cA m zero x) in |- *.
  fold xb0 in H14.
  set (x'b0 := cA m zero x') in |- *.
  fold x'b0 in H24.
  set (yt0 := cA_1 m zero y) in |- *.
  fold yt0 in H14.
  set (y't0 := cA_1 m zero y') in |- *.
  fold y't0 in H24.
  assert (inv_hmap (L m zero x y)).
 simpl in |- *.
   unfold m1 in H.
   simpl in H.
    tauto.
assert (exd m x'_1).
 unfold x'_1 in |- *.
   generalize (exd_cA_1 m one x').
    tauto.
assert (inv_hmap (L m zero x' y')).
 simpl in |- *.
   unfold m2 in H0.
   simpl in H0.
    tauto.
assert (exd m x_1).
 unfold x_1 in |- *.
   generalize (exd_cA_1 m one x).
    tauto.
generalize (expf_L0_CNS m x y x'_1 y' H1 H2).
  simpl in |- *.
  fold x_1 in |- *.
  fold xb0 in |- *.
  fold yt0 in |- *.
  set (yt0_1 := cA_1 m one yt0) in |- *.
  intro.
  generalize (expf_L0_CNS m x' y' x_1 y H11 H12).
  simpl in |- *.
  fold x'_1 in |- *.
  fold x'b0 in |- *.
  fold y't0 in |- *.
  set (y't0_1 := cA_1 m one y't0) in |- *.
  intro.
  generalize H13.
  clear H13.
  elim (expf_dec m x_1 y).
  tauto.
elim (expf_dec (L m zero x y) x'_1 y').
  tauto.
generalize H15; clear H15.
  elim (expf_dec m x'_1 y').
  tauto.
elim (expf_dec (L m zero x' y') x_1 y).
 intros.
   clear a b0 b2 b3.
   assert
    (expf m x_1 y \/
     expf m x_1 y' /\ expf m y x'b0 \/ expf m y y' 
     /\ expf m x_1 x'b0).
  clear H13 H7 H8 H17 H18 b b1.
     tauto.
 clear H15.
   assert
    (~
     (expf m x'_1 y' \/
      expf m x'_1 y /\ expf m y' xb0 \/ expf m y' y 
        /\ expf m x'_1 xb0)).
  generalize (expf_dec (L m zero x y) x'_1 y').
    clear H16 H17 H18 H7 H8 b b1.
     tauto.
 clear H13 E2 E3.
   elim H15.
   clear H15.
   elim H16.
   tauto.
 clear H16.
   intro.
   elim H13; clear H13; intro.
  right.
    left.
    split.
   apply expf_trans with x'b0.
    apply expf_symm.
      unfold x'_1 in |- *.
      assert (x' = cA_1 m zero x'b0).
     unfold x'b0 in |- *.
       rewrite cA_1_cA in |- *.
       tauto.
      tauto.
      tauto.
    rewrite H15 in |- *.
      fold (cF m x'b0) in |- *.
      assert (cF = MF.f).
      tauto.
    rewrite H16 in |- *.
      unfold expf in |- *.
      split.
      tauto.
    unfold MF.expo in |- *.
      split.
     unfold x'b0 in |- *.
       generalize (exd_cA m zero x').
        tauto.
    simpl in |- *.
      split with 1%nat.
      simpl in |- *.
       tauto.
   apply expf_symm.
      tauto.
  apply expf_trans with x_1.
   apply expf_symm.
      tauto.
  unfold x_1 in |- *.
    assert (x = cA_1 m zero xb0).
   unfold xb0 in |- *.
     rewrite cA_1_cA in |- *.
     tauto.
    tauto.
    tauto.
  rewrite H15 in |- *.
    fold (cF m xb0) in |- *.
    apply expf_symm.
    assert (cF = MF.f).
    tauto.
  rewrite H16 in |- *.
    unfold expf in |- *.
    split.
    tauto.
  unfold MF.expo in |- *.
    split.
   unfold xb0 in |- *.
     generalize (exd_cA m zero x).
      tauto.
  simpl in |- *.
    split with 1%nat.
    simpl in |- *.
     tauto.
 right.
   right.
   split.
  apply expf_symm.
     tauto.
 apply expf_trans with x'b0.
  apply expf_symm.
    unfold x'_1 in |- *.
    assert (x' = cA_1 m zero x'b0).
   unfold x'b0 in |- *.
     rewrite cA_1_cA in |- *.
     tauto.
    tauto.
    tauto.
  rewrite H15 in |- *.
    fold (cF m x'b0) in |- *.
    assert (cF = MF.f).
    tauto.
  rewrite H16 in |- *.
    unfold expf in |- *.
    split.
    tauto.
  unfold MF.expo in |- *.
    split.
   unfold x'b0 in |- *.
     generalize (exd_cA m zero x').
      tauto.
  simpl in |- *.
    split with 1%nat.
    simpl in |- *.
     tauto.
 apply expf_trans with x_1.
  apply expf_symm.
     tauto.
 unfold x_1 in |- *.
   assert (x = cA_1 m zero xb0).
  unfold xb0 in |- *.
    rewrite cA_1_cA in |- *.
    tauto.
   tauto.
   tauto.
 rewrite H15 in |- *.
   fold (cF m xb0) in |- *.
   apply expf_symm.
   assert (cF = MF.f).
   tauto.
 rewrite H16 in |- *.
   unfold expf in |- *.
   split.
   tauto.
 unfold MF.expo in |- *.
   split.
  unfold xb0 in |- *.
    generalize (exd_cA m zero x).
     tauto.
 simpl in |- *.
   split with 1%nat.
   simpl in |- *.
    tauto.
 tauto.
Qed.

(* OK: *)

Lemma nf_L0L0_VI:forall (m:fmap)(x y x' y':dart),
  let m1:= L (L m zero x y) zero x' y' in
  let m2:= L (L m zero x' y') zero x y in
    inv_hmap m1 -> 
    let x_1  := cA_1 m one x in
    let x'_1 := cA_1 m one x' in
     expf m x_1 y -> 
     ~ expf m x'_1 y' ->
        ~ expf (L m zero x' y') x_1 y ->
        ~ expf (L m zero x y) x'_1 y' ->
            nf m1 = nf m2.
Proof.
intros.
rename H0 into E0.
rename H1 into E1.
rename H2 into E2.
rename H3 into E3.
assert (inv_hmap m2).
 unfold m2 in |- *.
   apply inv_hmap_L0L0.
   fold m1 in |- *.
    tauto.
unfold m1 in |- *.
  unfold m2 in |- *.
  simpl in |- *.
  assert (inv_hmap m1).
  tauto.
assert (inv_hmap m2).
  tauto.
unfold m1 in H1.
  unfold m2 in H2.
  simpl in H1.
  simpl in H2.
  unfold prec_L in H1.
  unfold prec_L in H2.
  unfold pred in H1.
  unfold pred in H2.
  unfold succ in H1.
  unfold succ in H2.
  simpl in H1.
  simpl in H2.
  decompose [and] H1.
  clear H1.
  decompose [and] H2.
  clear H2.
  generalize H11 H14 H21 H24.
  elim (eq_dart_dec x x').
 intros.
   elim H2.
   apply exd_not_nil with m.
   tauto.
  tauto.
elim (eq_dart_dec x' x).
 intros.
   elim H25.
   apply exd_not_nil with m.
   tauto.
 auto.
clear H11 H14 H21 H24.
  intros.
  generalize H12 H22.
  clear H12 H22.
  elim (eq_dart_dec y y').
 intros.
   elim H12.
   apply exd_not_nil with m.
   tauto.
  tauto.
elim (eq_dart_dec y' y).
 intros.
   elim H22.
   apply exd_not_nil with m.
   tauto.
  tauto.
intros.
  clear H13 H19 H1 H16.
  clear H11 H21 H12 H22.
  clear H15.
  clear b0 b2.
  set (xb0 := cA m zero x) in |- *.
  fold xb0 in H14.
  set (x'b0 := cA m zero x') in |- *.
  fold x'b0 in H24.
  set (yt0 := cA_1 m zero y) in |- *.
  fold yt0 in H14.
  set (y't0 := cA_1 m zero y') in |- *.
  fold y't0 in H24.
  assert (inv_hmap (L m zero x y)).
 simpl in |- *.
   unfold m1 in H.
   simpl in H.
    tauto.
assert (exd m x'_1).
 unfold x'_1 in |- *.
   generalize (exd_cA_1 m one x').
    tauto.
assert (inv_hmap (L m zero x' y')).
 simpl in |- *.
   unfold m2 in H0.
   simpl in H0.
    tauto.
assert (exd m x_1).
 unfold x_1 in |- *.
   generalize (exd_cA_1 m one x).
    tauto.
generalize (expf_L0_CNS m x y x'_1 y' H1 H2).
  simpl in |- *.
  fold x_1 in |- *.
  fold xb0 in |- *.
  fold yt0 in |- *.
  set (yt0_1 := cA_1 m one yt0) in |- *.
  intro.
  generalize (expf_L0_CNS m x' y' x_1 y H11 H12).
  simpl in |- *.
  fold x'_1 in |- *.
  fold x'b0 in |- *.
  fold y't0 in |- *.
  set (y't0_1 := cA_1 m one y't0) in |- *.
  intro.
  generalize H13.
  clear H13.
  elim (expf_dec m x_1 y).
 generalize H15.
   clear H15.
   elim (expf_dec m x'_1 y').
   tauto.
 elim (expf_dec (L m zero x' y') x_1 y).
   tauto.
 elim (expf_dec (L m zero x y) x'_1 y').
   tauto.
 intros.
   clear a b0 b2 b3.
   assert
    (~
     (expf m x_1 y \/
      expf m x_1 y' /\ expf m y x'b0 \/ expf m y y' 
        /\ expf m x_1 x'b0)).
  clear H13 H7 H8 H17 H18 b b1.
    generalize (expf_dec (L m zero x' y') x_1 y).
     tauto.
 clear H15 E2.
    tauto.
 tauto.
Qed.

(* FINALLY, THE RESULT: OK!! *)

Theorem nf_L0L0:forall (m:fmap)(x y x' y':dart),
  let m1:= L (L m zero x y) zero x' y' in
  let m2:= L (L m zero x' y') zero x y in
    inv_hmap m1 -> nf m1 = nf m2.
Proof.
intros.
unfold m1 in H.
unfold m1 in |- *.
unfold m2 in |- *.
simpl in |- *.
elim (expf_dec m (cA_1 m one x) y).
 elim (expf_dec m (cA_1 m one x') y').
  elim (expf_dec (L m zero x' y') (cA_1 m one x) y).
   elim (expf_dec (L m zero x y) (cA_1 m one x') y').
    intros.
       lia.
   intros.
     generalize (nf_L0L0_I m x y x' y' H a1 a0 a b).
     simpl in |- *.
     elim (expf_dec m (cA_1 m one x) y).
    elim (expf_dec (L m zero x y) (cA_1 m one x') y').
     elim (expf_dec (L m zero x' y') (cA_1 m one x) y).
      elim (expf_dec m (cA_1 m one x') y').
        tauto.
       tauto.
      tauto.
    elim (expf_dec m (cA_1 m one x') y').
     elim (expf_dec (L m zero x' y') (cA_1 m one x) y).
       tauto.
      tauto.
    elim (expf_dec (L m zero x' y') (cA_1 m one x) y).
      tauto.
     tauto.
   elim (expf_dec m (cA_1 m one x') y').
     tauto.
    tauto.
  elim (expf_dec (L m zero x y) (cA_1 m one x') y').
   intros.
     assert (inv_hmap m2).
    unfold m2 in |- *.
      apply inv_hmap_L0L0.
       tauto.
   unfold m2 in H0.
     generalize (nf_L0L0_I m x' y' x y H0 a0 a1 a b).
     simpl in |- *.
     elim (expf_dec m (cA_1 m one x) y).
    elim (expf_dec m (cA_1 m one x') y').
     elim (expf_dec (L m zero x' y') (cA_1 m one x) y).
       tauto.
     elim (expf_dec (L m zero x y) (cA_1 m one x') y').
      intros.
        rewrite H1 in |- *.
         tauto.
      tauto.
     tauto.
    tauto.
  intros.
     tauto.
 elim (expf_dec (L m zero x y) (cA_1 m one x') y').
  elim (expf_dec (L m zero x' y') (cA_1 m one x) y).
   intros.
     generalize (nf_L0L0_II m x y x' y' H a1 b a a0).
     simpl in |- *.
     elim (expf_dec m (cA_1 m one x) y).
    elim (expf_dec m (cA_1 m one x') y').
      tauto.
    elim (expf_dec (L m zero x' y') (cA_1 m one x) y).
     elim (expf_dec (L m zero x y) (cA_1 m one x') y').
      intros.
         tauto.
      tauto.
     tauto.
    tauto.
  intros.
    generalize (nf_L0L0_IV m x y x' y' H a0 b0 b a).
    simpl in |- *.
    elim (expf_dec m (cA_1 m one x') y').
    tauto.
  elim (expf_dec (L m zero x' y') (cA_1 m one x) y).
    tauto.
  elim (expf_dec m (cA_1 m one x) y).
   elim (expf_dec (L m zero x y) (cA_1 m one x') y').
     tauto.
    tauto.
   tauto.
 elim (expf_dec (L m zero x' y') (cA_1 m one x) y).
  intros.
     lia.
 intros.
   generalize (nf_L0L0_VI m x y x' y' H a b1 b b0).
   simpl in |- *.
   elim (expf_dec m (cA_1 m one x) y).
  elim (expf_dec m (cA_1 m one x') y').
    tauto.
  elim (expf_dec (L m zero x' y') (cA_1 m one x) y).
    tauto.
  elim (expf_dec (L m zero x y) (cA_1 m one x') y').
    tauto.
   tauto.
  tauto.
elim (expf_dec m (cA_1 m one x') y').
 elim (expf_dec (L m zero x' y') (cA_1 m one x) y).
  elim (expf_dec (L m zero x y) (cA_1 m one x') y').
   intros.
     assert (inv_hmap m2).
    unfold m2 in |- *.
      apply inv_hmap_L0L0.
       tauto.
   unfold m2 in H0.
     generalize (nf_L0L0_II m x' y' x y H0 a1 b a a0).
     simpl in |- *.
     elim (expf_dec m (cA_1 m one x) y).
     tauto.
   elim (expf_dec m (cA_1 m one x') y').
    elim (expf_dec (L m zero x' y') (cA_1 m one x) y).
     elim (expf_dec (L m zero x y) (cA_1 m one x') y').
      intros.
        symmetry  in |- *.
         tauto.
      tauto.
     tauto.
    tauto.
  intros.
    assert (inv_hmap m2).
   unfold m2 in |- *.
     apply inv_hmap_L0L0.
      tauto.
  generalize (nf_L0L0_IV m x' y' x y H0 a0 b0 b a).
    simpl in |- *.
    elim (expf_dec m (cA_1 m one x) y).
    tauto.
  elim (expf_dec (L m zero x y) (cA_1 m one x') y').
   elim (expf_dec m (cA_1 m one x') y').
    elim (expf_dec (L m zero x' y') (cA_1 m one x) y).
      tauto.
     tauto.
    tauto.
  elim (expf_dec m (cA_1 m one x') y').
   elim (expf_dec (L m zero x' y') (cA_1 m one x) y).
    intros.
      symmetry  in |- *.
       tauto.
    tauto.
   tauto.
 elim (expf_dec (L m zero x y) (cA_1 m one x') y').
  intros.
     lia.
 intros.
   assert (inv_hmap m2).
  unfold m2 in |- *; apply inv_hmap_L0L0.
     tauto.
 generalize (nf_L0L0_VI m x' y' x y H0 a b1 b b0).
   simpl in |- *.
   elim (expf_dec m (cA_1 m one x') y').
  elim (expf_dec m (cA_1 m one x) y).
    tauto.
  elim (expf_dec (L m zero x' y') (cA_1 m one x) y).
    tauto.
  elim (expf_dec (L m zero x y) (cA_1 m one x') y').
    tauto.
  intros.
    symmetry  in |- *.
     tauto.
  tauto.
elim (expf_dec (L m zero x' y') (cA_1 m one x) y).
 elim (expf_dec (L m zero x y) (cA_1 m one x') y').
  intros.
     lia.
 intros.
   generalize (nf_L0L0_V m x y x' y' H b1 b0 a b).
   simpl in |- *.
   elim (expf_dec m (cA_1 m one x) y).
   tauto.
 elim (expf_dec m (cA_1 m one x') y').
   tauto.
 elim (expf_dec (L m zero x y) (cA_1 m one x') y').
   tauto.
 elim (expf_dec (L m zero x' y') (cA_1 m one x) y).
   tauto.
  tauto.
elim (expf_dec (L m zero x y) (cA_1 m one x') y').
 intros.
   assert (inv_hmap m2).
  unfold m2 in |- *.
    apply inv_hmap_L0L0.
     tauto.
 generalize (nf_L0L0_V m x' y' x y H0 b0 b1 a b).
   simpl in |- *.
   elim (expf_dec m (cA_1 m one x) y).
   tauto.
 elim (expf_dec m (cA_1 m one x') y').
   tauto.
 elim (expf_dec (L m zero x' y') (cA_1 m one x) y).
   tauto.
 elim (expf_dec (L m zero x y) (cA_1 m one x') y').
  intros.
    symmetry  in |- *.
     tauto.
  tauto.
intros.
   lia.
Qed.


(*===================================================
                       nf_L1L1
=====================================================*)

(* IN  JORDAN5, WE HAVE:

Theorem expf_L1_CNS:forall (m:fmap)(x y z t:dart),
  inv_hmap (L m one x y) -> exd m z ->
  (expf (L m one x y) z t <-> 
    let x1 := cA m one x in
    let x10 := cA m zero x1 in 
    let y0 := cA m zero y in   
    let y_1 := cA_1 m one y in
      if expf_dec m x y0 
      then betweenf m x z y0 /\ betweenf m x t y0
        \/ betweenf m y_1 z x10 /\ betweenf m y_1 t x10
        \/ ~ expf m x z /\ expf m z t 
      else   expf m z t
          \/ expf m z x /\ expf m t y0
          \/ expf m t x /\ expf m z y0).

*)

Lemma nf_L1L1_I:forall (m:fmap)(x y x' y':dart),
  let m1:= L (L m one x y) one x' y' in
  let m2:= L (L m one x' y') one x y in
    inv_hmap m1 -> 
    let y0  := cA m zero y in
    let y'0 := cA m zero y' in
     expf m x y0 -> 
     expf m x' y'0 ->
       expf (L m one x' y') x y0 ->
       ~ expf (L m one x y) x' y'0 ->
          nf m1 = nf m2.
Proof.
intros.
rename H0 into E0.
rename H1 into E1.
rename H2 into E2.
rename H3 into E3.
assert (inv_hmap m2).
 unfold m2 in |- *.
   apply inv_hmap_L1L1.
   fold m1 in |- *.
    tauto.
unfold m1 in |- *.
  unfold m2 in |- *.
  simpl in |- *.
  assert (inv_hmap m1).
  tauto.
assert (inv_hmap m2).
  tauto.
unfold m1 in H1.
  unfold m2 in H2.
  simpl in H1.
  simpl in H2.
  unfold prec_L in H1.
  unfold prec_L in H2.
  unfold pred in H1.
  unfold pred in H2.
  unfold succ in H1.
  unfold succ in H2.
  simpl in H1.
  simpl in H2.
  decompose [and] H1.
  clear H1.
  decompose [and] H2.
  clear H2.
  generalize H11 H14 H21 H24.
  elim (eq_dart_dec x x').
 intros.
   elim H2.
   apply exd_not_nil with m.
   tauto.
  tauto.
elim (eq_dart_dec x' x).
 intros.
   elim H25.
   apply exd_not_nil with m.
   tauto.
 auto.
clear H11 H14 H21 H24.
  intros.
  generalize H12 H22.
  clear H12 H22.
  elim (eq_dart_dec y y').
 intros.
   elim H12.
   apply exd_not_nil with m.
   tauto.
  tauto.
elim (eq_dart_dec y' y).
 intros.
   elim H22.
   apply exd_not_nil with m.
   tauto.
  tauto.
intros.
  clear H13 H19 H1 H16.
  clear H11 H21 H12 H22.
  clear H15.
  clear b0 b2.
  set (xb1 := cA m one x) in |- *.
  fold xb1 in H14.
  set (x'b1 := cA m one x') in |- *.
  fold x'b1 in H24.
  set (yt1 := cA_1 m one y) in |- *.
  fold yt1 in H14.
  set (y't1 := cA_1 m one y') in |- *.
  fold y't1 in H24.
  assert (inv_hmap (L m one x y)).
 simpl in |- *.
   unfold m1 in H.
   simpl in H.
    tauto.
assert (exd m y'0).
 unfold y'0 in |- *.
   generalize (exd_cA m zero y').
    tauto.
assert (inv_hmap (L m one x' y')).
 simpl in |- *.
   unfold m2 in H0.
   simpl in H0.
    tauto.
assert (exd m y0).
 unfold y0 in |- *.
   generalize (exd_cA m zero y).
    tauto.
generalize (expf_L1_CNS m x y x' y'0 H1 H9).
  simpl in |- *.
  fold y0 in |- *.
  fold xb1 in |- *.
  fold yt1 in |- *.
  set (xb10 := cA m zero xb1) in |- *.
  intro.
  generalize (expf_L1_CNS m x' y' x y0 H11 H3).
  simpl in |- *.
  fold y'0 in |- *.
  fold x'b1 in |- *.
  fold y't1 in |- *.
  set (x'b10 := cA m zero x'b1) in |- *.
  intro.
  generalize H13.
  clear H13.
  elim (expf_dec m x y0).
 generalize H15.
   clear H15.
(* DEBUT DU RAISONNEMENT: *)
   elim (expf_dec m x' y'0).
  intros.
    elim (expf_dec (L m one x' y') x y0).
   elim (expf_dec (L m one x y) x' y'0).
     tauto.
   intros.
     clear a a0 b0 a1.
     assert
      (betweenf m x' x y'0 /\ betweenf m x' y0 y'0 \/
       betweenf m y't1 x x'b10 /\ 
      betweenf m y't1 y0 x'b10 \/
       ~ expf m x' x /\ expf m x y0).
    clear H13 H14 H24 b b1 H7 H8 H17 H18.
      clear H10 E0 E1 E3.
       tauto.
   clear H15.
     clear E2.
     generalize (expf_dec (L m one x y) x' y'0).
     intro.
     assert
      (~
       (betweenf m x x' y0 /\ betweenf m x y'0 y0 \/
        betweenf m yt1 x' xb10 /\ 
          betweenf m yt1 y'0 xb10 \/
        ~ expf m x x' /\ expf m x' y'0)).
    clear H16 H7 H8 H17 H18 b b1 E0 E1.
       tauto.
   clear H13 E3 H15.
     elim H19.
     clear H19.
     elim H16.
    clear H16.
      intro.
      assert (xb10 = cF_1 m x).
     unfold xb10 in |- *.
       unfold xb1 in |- *.
       fold (cF_1 m x) in |- *.
        tauto.
    assert (yt1 = cF m y0).
     unfold yt1 in |- *.
       unfold y0 in |- *.
       unfold cF in |- *.
       rewrite cA_1_cA in |- *.
       tauto.
      tauto.
      tauto.
    rewrite H15 in |- *.
      rewrite H16 in |- *.
      assert (y0 <> y'0).
     intro.
       assert (cA_1 m zero y0 = cA_1 m zero y'0).
      rewrite H19 in |- *.
         tauto.
     generalize H21.
       unfold y0 in |- *.
       unfold y'0 in |- *.
       rewrite cA_1_cA in |- *.
      rewrite cA_1_cA in |- *.
       intro.
         symmetry  in H22.
          tauto.
       tauto.
       tauto.
      tauto.
      tauto.
    assert (x <> x').
     intro.
       symmetry  in H21.
        tauto.
    generalize (betweenf1 m x y0 x' y'0 H5 H9 H21 H19).
      clear H19 H21 H7 H8 H17 H18 E0 E1 H20.
       tauto.
   clear H16.
     intros.
     elim H13; clear H13; intro.
    assert (xb10 = cF_1 m x).
     unfold xb10 in |- *.
       unfold xb1 in |- *.
       fold (cF_1 m x) in |- *.
        tauto.
    assert (yt1 = cF m y0).
     unfold yt1 in |- *.
       unfold y0 in |- *.
       unfold cF in |- *.
       rewrite cA_1_cA in |- *.
       tauto.
      tauto.
      tauto.
    assert (x'b10 = cF_1 m x').
     unfold x'b10 in |- *.
       unfold x'b1 in |- *.
       fold (cF_1 m x') in |- *.
        tauto.
    assert (y't1 = cF m y'0).
     unfold y't1 in |- *.
       unfold y'0 in |- *.
       unfold cF in |- *.
       rewrite cA_1_cA in |- *.
       tauto.
      tauto.
      tauto.
    assert (y0 <> y'0).
     intro.
       assert (cA_1 m zero y0 = cA_1 m zero y'0).
      rewrite H22 in |- *.
         tauto.
     generalize H23.
       unfold y0 in |- *.
       unfold y'0 in |- *.
       rewrite cA_1_cA in |- *.
      rewrite cA_1_cA in |- *.
       intro.
         symmetry  in H25.
          tauto.
       tauto.
       tauto.
      tauto.
      tauto.
    assert (x <> x').
     intro.
       symmetry  in H23.
        tauto.
    assert (exd m y'0).
     unfold y'0 in |- *.
       generalize (exd_cA m zero y').
        tauto.
    generalize
    (betweenf2 m x y0 x' y'0 H5 H25 H23 H22).
      rewrite H15 in |- *.
      rewrite H16 in |- *.
      rewrite H21 in H13.
      rewrite H19 in H13.
      clear H22 H23 H7 H8 H17 H18 H12 H2 E0 E1 H10.
       tauto.
   right.
     right.
     split.
    intro.
      assert (expf m x' x).
     apply expf_symm.
        tauto.
     tauto.
    tauto.
   tauto.
  tauto.
 tauto.
Qed.

(* OK: *)

Lemma nf_L1L1_II:forall (m:fmap)(x y x' y':dart),
  let m1:= L (L m one x y) one x' y' in
  let m2:= L (L m one x' y') one x y in
    inv_hmap m1 -> 
    let y0  := cA m zero y in
    let y'0 := cA m zero y' in
     expf m x y0 -> 
     ~ expf m x' y'0 ->
       expf (L m one x' y') x y0 ->
        expf (L m one x y) x' y'0 ->
          nf m1 = nf m2.
Proof.
intros.
rename H0 into E0.
rename H1 into E1.
rename H2 into E2.
rename H3 into E3.
assert (inv_hmap m2).
 unfold m2 in |- *.
   apply inv_hmap_L1L1.
   fold m1 in |- *.
    tauto.
unfold m1 in |- *.
  unfold m2 in |- *.
  simpl in |- *.
  assert (inv_hmap m1).
  tauto.
assert (inv_hmap m2).
  tauto.
unfold m1 in H1.
  unfold m2 in H2.
  simpl in H1.
  simpl in H2.
  unfold prec_L in H1.
  unfold prec_L in H2.
  unfold pred in H1.
  unfold pred in H2.
  unfold succ in H1.
  unfold succ in H2.
  simpl in H1.
  simpl in H2.
  decompose [and] H1.
  clear H1.
  decompose [and] H2.
  clear H2.
  generalize H11 H14 H21 H24.
  elim (eq_dart_dec x x').
 intros.
   elim H2.
   apply exd_not_nil with m.
   tauto.
  tauto.
elim (eq_dart_dec x' x).
 intros.
   elim H25.
   apply exd_not_nil with m.
   tauto.
 auto.
clear H11 H14 H21 H24.
  intros.
  generalize H12 H22.
  clear H12 H22.
  elim (eq_dart_dec y y').
 intros.
   elim H12.
   apply exd_not_nil with m.
   tauto.
  tauto.
elim (eq_dart_dec y' y).
 intros.
   elim H22.
   apply exd_not_nil with m.
   tauto.
  tauto.
intros.
  clear H13 H19 H1 H16.
  clear H11 H21 H12 H22.
  clear H15.
  clear b0 b2.
  set (xb1 := cA m one x) in |- *.
  fold xb1 in H14.
  set (x'b1 := cA m one x') in |- *.
  fold x'b1 in H24.
  set (yt1 := cA_1 m one y) in |- *.
  fold yt1 in H14.
  set (y't1 := cA_1 m one y') in |- *.
  fold y't1 in H24.
  assert (inv_hmap (L m one x y)).
 simpl in |- *.
   unfold m1 in H.
   simpl in H.
    tauto.
assert (exd m y'0).
 unfold y'0 in |- *.
   generalize (exd_cA m zero y').
    tauto.
assert (inv_hmap (L m one x' y')).
 simpl in |- *.
   unfold m2 in H0.
   simpl in H0.
    tauto.
assert (exd m y0).
 unfold y0 in |- *.
   generalize (exd_cA m zero y).
    tauto.
generalize (expf_L1_CNS m x y x' y'0 H1 H9).
  simpl in |- *.
  fold y0 in |- *.
  fold xb1 in |- *.
  fold yt1 in |- *.
  set (xb10 := cA m zero xb1) in |- *.
  intro.
  generalize (expf_L1_CNS m x' y' x y0 H11 H3).
  simpl in |- *.
  fold y'0 in |- *.
  fold x'b1 in |- *.
  fold y't1 in |- *.
  set (x'b10 := cA m zero x'b1) in |- *.
  intro.
  generalize H13.
  clear H13.
  elim (expf_dec m x y0).
 generalize H15.
   clear H15.
   elim (expf_dec m x' y'0).
   tauto.
 elim (expf_dec (L m one x' y') x y0).
  elim (expf_dec (L m one x y) x' y'0).
   intros.
     assert
      (betweenf m x x' y0 /\ betweenf m x y'0 y0 \/
       betweenf m yt1 x' xb10 /\ 
        betweenf m yt1 y'0 xb10 \/
       ~ expf m x x' /\ expf m x' y'0).
    clear H15 H7 H8 H17 H18.
       tauto.
   clear H13.
     clear H15.
     elim E1.
     clear E1.
     elim H16; clear H16; intro.
    decompose [and] H13.
      clear H13.
      generalize (betweenf_expf m x x' y0 H5 H3 H15).
      intro.
      generalize (betweenf_expf m x y'0 y0 H5 H3 H16).
      intro.
      apply expf_trans with x.
     apply expf_symm.
        tauto.
     tauto.
   elim H13.
    clear H13.
      intros.
      decompose [and] H13.
      clear H13.
      assert (exd m yt1).
     unfold yt1 in |- *.
       generalize (exd_cA_1 m one y).
        tauto.
    generalize 
   (betweenf_expf m yt1 x' xb10 H5 H13 H15).
      generalize 
   (betweenf_expf m yt1 y'0 xb10 H5 H13 H16).
      intros.
      apply expf_trans with yt1.
     apply expf_symm.
        tauto.
     tauto.
   clear H13.
      tauto.
   tauto.
  tauto.
 tauto.
Qed.

(* OK: *)

Lemma nf_L1L1_III:forall (m:fmap)(x y x' y':dart),
  let m1:= L (L m one x y) one x' y' in
  let m2:= L (L m one x' y') one x y in
    inv_hmap m1 -> 
    let y0  := cA m zero y in
    let y'0 := cA m zero y' in
     expf m x y0 -> 
     ~ expf m x' y'0 ->
       expf (L m one x' y') x y0 ->
        ~ expf (L m one x y) x' y'0 ->
           nf m1 = nf m2.
Proof.
intros.
unfold m1 in |- *.
unfold m2 in |- *.
simpl in |- *.
fold y0 in |- *.
fold y'0 in |- *.
elim (expf_dec m x y0).
 elim (expf_dec m x' y'0).
   tauto.
 elim (expf_dec (L m one x' y') x y0).
  elim (expf_dec (L m one x y) x' y'0).
    tauto.
  intros.
     lia.
  tauto.
 tauto.
Qed.

(* OK: *)

Lemma nf_L1L1_IV:forall (m:fmap)(x y x' y':dart),
  let m1:= L (L m one x y) one x' y' in
  let m2:= L (L m one x' y') one x y in
    inv_hmap m1 -> 
    let y0  := cA m zero y in
    let y'0 := cA m zero y' in
     expf m x y0 -> 
     ~ expf m x' y'0 ->
       ~ expf (L m one x' y') x y0 ->
          expf (L m one x y) x' y'0 ->
            nf m1 = nf m2.
Proof.
intros.
rename H0 into E0.
rename H1 into E1.
rename H2 into E2.
rename H3 into E3.
assert (inv_hmap m2).
 unfold m2 in |- *.
   apply inv_hmap_L1L1.
   fold m1 in |- *.
    tauto.
unfold m1 in |- *.
  unfold m2 in |- *.
  simpl in |- *.
  assert (inv_hmap m1).
  tauto.
assert (inv_hmap m2).
  tauto.
unfold m1 in H1.
  unfold m2 in H2.
  simpl in H1.
  simpl in H2.
  unfold prec_L in H1.
  unfold prec_L in H2.
  unfold pred in H1.
  unfold pred in H2.
  unfold succ in H1.
  unfold succ in H2.
  simpl in H1.
  simpl in H2.
  decompose [and] H1.
  clear H1.
  decompose [and] H2.
  clear H2.
  generalize H11 H14 H21 H24.
  elim (eq_dart_dec x x').
 intros.
   elim H2.
   apply exd_not_nil with m.
   tauto.
  tauto.
elim (eq_dart_dec x' x).
 intros.
   elim H25.
   apply exd_not_nil with m.
   tauto.
 auto.
clear H11 H14 H21 H24.
  intros.
  generalize H12 H22.
  clear H12 H22.
  elim (eq_dart_dec y y').
 intros.
   elim H12.
   apply exd_not_nil with m.
   tauto.
  tauto.
elim (eq_dart_dec y' y).
 intros.
   elim H22.
   apply exd_not_nil with m.
   tauto.
  tauto.
intros.
  clear H13 H19 H1 H16.
  clear H11 H21 H12 H22.
  clear H15.
  clear b0 b2.
  set (xb1 := cA m one x) in |- *.
  fold xb1 in H14.
  set (x'b1 := cA m one x') in |- *.
  fold x'b1 in H24.
  set (yt1 := cA_1 m one y) in |- *.
  fold yt1 in H14.
  set (y't1 := cA_1 m one y') in |- *.
  fold y't1 in H24.
  assert (inv_hmap (L m one x y)).
 simpl in |- *.
   unfold m1 in H.
   simpl in H.
    tauto.
assert (exd m y'0).
 unfold y'0 in |- *.
   generalize (exd_cA m zero y').
    tauto.
assert (inv_hmap (L m one x' y')).
 simpl in |- *.
   unfold m2 in H0.
   simpl in H0.
    tauto.
assert (exd m y0).
 unfold y0 in |- *.
   generalize (exd_cA m zero y).
    tauto.
generalize (expf_L1_CNS m x y x' y'0 H1 H9).
  simpl in |- *.
  fold y0 in |- *.
  fold xb1 in |- *.
  fold yt1 in |- *.
  set (xb10 := cA m zero xb1) in |- *.
  intro.
  generalize (expf_L1_CNS m x' y' x y0 H11 H3).
  simpl in |- *.
  fold y'0 in |- *.
  fold x'b1 in |- *.
  fold y't1 in |- *.
  set (x'b10 := cA m zero x'b1) in |- *.
  intro.
  generalize H13.
  clear H13.
  elim (expf_dec m x y0).
 generalize H15.
   clear H15.
   elim (expf_dec m x' y'0).
  intros.
     tauto.
 elim (expf_dec (L m one x' y') x y0).
   tauto.
 elim (expf_dec (L m one x y) x' y'0).
  intros.
    assert
     (~
      (expf m x y0 \/
       expf m x x' /\ expf m y0 y'0 \/ 
    expf m y0 x' /\ expf m x y'0)).
   clear H13 H7 H8 H17 H18 b b1.
     generalize (expf_dec (L m zero x' y') x y0).
      tauto.
  clear H15 E2.
    clear H13 H7 H17 H18 b b1.
     tauto.
  tauto.
 tauto.
Qed.

(* OK: *)

Lemma nf_L1L1_V:forall (m:fmap)(x y x' y':dart),
  let m1:= L (L m one x y) one x' y' in
  let m2:= L (L m one x' y') one x y in
    inv_hmap m1 -> 
    let y0  := cA m zero y in
    let y'0 := cA m zero y' in
     ~ expf m x y0 -> 
      ~ expf m x' y'0 ->
         expf (L m one x' y') x y0 ->
          ~ expf (L m one x y) x' y'0 ->
               nf m1 = nf m2.
Proof.
intros.
rename H0 into E0.
rename H1 into E1.
rename H2 into E2.
rename H3 into E3.
assert (inv_hmap m2).
 unfold m2 in |- *.
   apply inv_hmap_L1L1.
   fold m1 in |- *.
    tauto.
unfold m1 in |- *.
  unfold m2 in |- *.
  simpl in |- *.
  assert (inv_hmap m1).
  tauto.
assert (inv_hmap m2).
  tauto.
unfold m1 in H1.
  unfold m2 in H2.
  simpl in H1.
  simpl in H2.
  unfold prec_L in H1.
  unfold prec_L in H2.
  unfold pred in H1.
  unfold pred in H2.
  unfold succ in H1.
  unfold succ in H2.
  simpl in H1.
  simpl in H2.
  decompose [and] H1.
  clear H1.
  decompose [and] H2.
  clear H2.
  generalize H11 H14 H21 H24.
  elim (eq_dart_dec x x').
 intros.
   elim H2.
   apply exd_not_nil with m.
   tauto.
  tauto.
elim (eq_dart_dec x' x).
 intros.
   elim H25.
   apply exd_not_nil with m.
   tauto.
 auto.
clear H11 H14 H21 H24.
  intros.
  generalize H12 H22.
  clear H12 H22.
  elim (eq_dart_dec y y').
 intros.
   elim H12.
   apply exd_not_nil with m.
   tauto.
  tauto.
elim (eq_dart_dec y' y).
 intros.
   elim H22.
   apply exd_not_nil with m.
   tauto.
  tauto.
intros.
  clear H13 H19 H1 H16.
  clear H11 H21 H12 H22.
  clear H15.
  clear b0 b2.
  set (xb1 := cA m one x) in |- *.
  fold xb1 in H14.
  set (x'b1 := cA m one x') in |- *.
  fold x'b1 in H24.
  set (yt1 := cA_1 m one y) in |- *.
  fold yt1 in H14.
  set (y't1 := cA_1 m one y') in |- *.
  fold y't1 in H24.
  assert (inv_hmap (L m one x y)).
 simpl in |- *.
   unfold m1 in H.
   simpl in H.
    tauto.
assert (exd m y'0).
 unfold y'0 in |- *.
   generalize (exd_cA m zero y').
    tauto.
assert (inv_hmap (L m one x' y')).
 simpl in |- *.
   unfold m2 in H0.
   simpl in H0.
    tauto.
assert (exd m y0).
 unfold y0 in |- *.
   generalize (exd_cA m zero y).
    tauto.
generalize (expf_L1_CNS m x y x' y'0 H1 H9).
  simpl in |- *.
  fold y0 in |- *.
  fold xb1 in |- *.
  fold yt1 in |- *.
  set (xb10 := cA m zero xb1) in |- *.
  intro.
  generalize (expf_L1_CNS m x' y' x y0 H11 H3).
  simpl in |- *.
  fold y'0 in |- *.
  fold x'b1 in |- *.
  fold y't1 in |- *.
  set (x'b10 := cA m zero x'b1) in |- *.
  intro.
  generalize H13.
  clear H13.
  elim (expf_dec m x y0).
  tauto.
elim (expf_dec (L m one x y) x' y'0).
  tauto.
generalize H15; clear H15.
  elim (expf_dec m x' y'0).
  tauto.
elim (expf_dec (L m one x' y') x y0).
 intros.
   clear a b0 b2 b3.
   assert
    (expf m x y0 \/
     expf m x x' /\ expf m y0 y'0 \/ 
      expf m y0 x' /\ expf m x y'0).
  clear H13 H7 H8 H17 H18 b b1.
     tauto.
 clear H15.
   assert
    (~
     (expf m x' y'0 \/
      expf m x' x /\ expf m y'0 y0 \/
      expf m y'0 x /\ expf m x' y0)).
  generalize (expf_dec (L m zero x y) x' y'0).
    clear H16 H17 H18 H7 H8 b b1.
     tauto.
 clear H13 E2 E3.
   elim H15.
   clear H15.
   elim H16.
   tauto.
 clear H16.
   intro.
   elim H13; clear H13; intro.
  right.
    left.
    split.
   apply expf_symm.
      tauto.
  apply expf_symm.
     tauto.
 right.
   right.
   split.
  apply expf_symm.
     tauto.
 apply expf_symm.
    tauto.
intros.
tauto.
Qed.

(* OK: *)

Lemma nf_L1L1_VI:forall (m:fmap)(x y x' y':dart),
  let m1:= L (L m one x y) one x' y' in
  let m2:= L (L m one x' y') one x y in
    inv_hmap m1 -> 
    let y0  := cA m zero y in
    let y'0 := cA m zero y' in
     expf m x y0 -> 
      ~ expf m x' y'0 ->
         ~ expf (L m one x' y') x y0 ->
           ~ expf (L m one x y) x' y'0 ->
               nf m1 = nf m2.
Proof.
intros.
rename H0 into E0.
rename H1 into E1.
rename H2 into E2.
rename H3 into E3.
assert (inv_hmap m2).
 unfold m2 in |- *.
   apply inv_hmap_L1L1.
   fold m1 in |- *.
    tauto.
unfold m1 in |- *.
  unfold m2 in |- *.
  simpl in |- *.
  assert (inv_hmap m1).
  tauto.
assert (inv_hmap m2).
  tauto.
unfold m1 in H1.
  unfold m2 in H2.
  simpl in H1.
  simpl in H2.
  unfold prec_L in H1.
  unfold prec_L in H2.
  unfold pred in H1.
  unfold pred in H2.
  unfold succ in H1.
  unfold succ in H2.
  simpl in H1.
  simpl in H2.
  decompose [and] H1.
  clear H1.
  decompose [and] H2.
  clear H2.
  generalize H11 H14 H21 H24.
  elim (eq_dart_dec x x').
 intros.
   elim H2.
   apply exd_not_nil with m.
   tauto.
  tauto.
elim (eq_dart_dec x' x).
 intros.
   elim H25.
   apply exd_not_nil with m.
   tauto.
 auto.
clear H11 H14 H21 H24.
  intros.
  generalize H12 H22.
  clear H12 H22.
  elim (eq_dart_dec y y').
 intros.
   elim H12.
   apply exd_not_nil with m.
   tauto.
  tauto.
elim (eq_dart_dec y' y).
 intros.
   elim H22.
   apply exd_not_nil with m.
   tauto.
  tauto.
intros.
  clear H13 H19 H1 H16.
  clear H11 H21 H12 H22.
  clear H15.
  clear b0 b2.
  set (xb1 := cA m one x) in |- *.
  fold xb1 in H14.
  set (x'b1 := cA m one x') in |- *.
  fold x'b1 in H24.
  set (yt1 := cA_1 m one y) in |- *.
  fold yt1 in H14.
  set (y't1 := cA_1 m one y') in |- *.
  fold y't1 in H24.
  assert (inv_hmap (L m one x y)).
 simpl in |- *.
   unfold m1 in H.
   simpl in H.
    tauto.
assert (exd m y'0).
 unfold y'0 in |- *.
   generalize (exd_cA m zero y').
    tauto.
assert (inv_hmap (L m one x' y')).
 simpl in |- *.
   unfold m2 in H0.
   simpl in H0.
    tauto.
assert (exd m y0).
 unfold y0 in |- *.
   generalize (exd_cA m zero y).
    tauto.
generalize (expf_L1_CNS m x y x' y'0 H1 H9).
  simpl in |- *.
  fold y0 in |- *.
  fold xb1 in |- *.
  fold yt1 in |- *.
  set (xb10 := cA m zero xb1) in |- *.
  intro.
  generalize (expf_L1_CNS m x' y' x y0 H11 H3).
  simpl in |- *.
  fold y'0 in |- *.
  fold x'b1 in |- *.
  fold y't1 in |- *.
  set (x'b10 := cA m zero x'b1) in |- *.
  intro.
  generalize H13.
  clear H13.
  elim (expf_dec m x y0).
 generalize H15.
   clear H15.
   elim (expf_dec m x' y'0).
   tauto.
 elim (expf_dec (L m one x' y') x y0).
   tauto.
 elim (expf_dec (L m one x y) x' y'0).
   tauto.
 intros.
   clear a b0 b2 b3.
   assert
    (~
     (expf m x y0 \/
      expf m x x' /\ expf m y0 y'0 \/
        expf m y0 x' /\ expf m x y'0)).
  clear H13 H7 H8 H17 H18 b b1.
    generalize (expf_dec (L m zero x' y') x y0).
     tauto.
 clear H15 E2.
    tauto.
 tauto.
Qed.

(* FINALLY, THE RESULT: *)

Theorem nf_L1L1:forall (m:fmap)(x y x' y':dart),
    let m1:= L (L m one x y) one x' y' in
    let m2:= L (L m one x' y') one x y in
     inv_hmap m1 -> nf m1 = nf m2.
Proof.
intros.
unfold m1 in H.
unfold m1 in |- *.
unfold m2 in |- *.
simpl in |- *.
elim (expf_dec m x (cA m zero y)).
 elim (expf_dec m x' (cA m zero y')).
  elim (expf_dec (L m one x' y') x (cA m zero y)).
   elim (expf_dec (L m one x y) x' (cA m zero y')).
    intros.
       tauto.
   intros.
     generalize (nf_L1L1_I m x y x' y' H a1 a0 a b).
     simpl in |- *.
     elim (expf_dec m x (cA m zero y)).
    elim (expf_dec (L m one x y) x' (cA m zero y')).
     elim (expf_dec (L m one x' y') x (cA m zero y)).
      elim (expf_dec m x' (cA m zero y')).
        tauto.
       tauto.
      tauto.
    elim (expf_dec m x' (cA m zero y')).
     elim (expf_dec (L m one x' y') x (cA m zero y)).
       tauto.
      tauto.
    elim (expf_dec (L m one x' y') x (cA m zero y)).
      tauto.
     tauto.
   elim (expf_dec m x' (cA m zero y')).
     tauto.
    tauto.
  elim (expf_dec (L m one x y) x' (cA m zero y')).
   intros.
     assert (inv_hmap m2).
    unfold m2 in |- *.
      apply inv_hmap_L1L1.
       tauto.
   unfold m2 in H0.
     generalize (nf_L1L1_I m x' y' x y H0 a0 a1 a b).
     simpl in |- *.
     elim (expf_dec m x (cA m zero y)).
    elim (expf_dec m x' (cA m zero y')).
     elim (expf_dec (L m one x' y') x (cA m zero y)).
       tauto.
     elim (expf_dec (L m one x y) x' (cA m zero y')).
      intros.
        rewrite H1 in |- *.
         tauto.
      tauto.
     tauto.
    tauto.
  intros.
     tauto.
 elim (expf_dec (L m one x y) x' (cA m zero y')).
  elim (expf_dec (L m one x' y') x (cA m zero y)).
   intros.
     generalize (nf_L1L1_II m x y x' y' H a1 b a a0).
     simpl in |- *.
     elim (expf_dec m x (cA m zero y)).
    elim (expf_dec m x' (cA m zero y')).
      tauto.
    elim (expf_dec (L m one x' y') x (cA m zero y)).
     elim (expf_dec (L m one x y) x' (cA m zero y')).
      intros.
         tauto.
      tauto.
     tauto.
    tauto.
  intros.
    generalize (nf_L1L1_IV m x y x' y' H a0 b0 b a).
    simpl in |- *.
    elim (expf_dec m x' (cA m zero y')).
    tauto.
  elim (expf_dec (L m one x' y') x (cA m zero y)).
    tauto.
  elim (expf_dec m x (cA m zero y)).
   elim (expf_dec (L m one x y) x' (cA m zero y')).
     tauto.
    tauto.
   tauto.
 elim (expf_dec (L m one x' y') x (cA m zero y)).
  intros.
     lia.
 intros.
   generalize (nf_L1L1_VI m x y x' y' H a b1 b b0).
   simpl in |- *.
   elim (expf_dec m x (cA m zero y)).
  elim (expf_dec m x' (cA m zero y')).
    tauto.
  elim (expf_dec (L m one x' y') x (cA m zero y)).
    tauto.
  elim (expf_dec (L m one x y) x' (cA m zero y')).
    tauto.
   tauto.
  tauto.
elim (expf_dec m x' (cA m zero y')).
 elim (expf_dec (L m one x' y') x (cA m zero y)).
  elim (expf_dec (L m one x y) x' (cA m zero y')).
   intros.
     assert (inv_hmap m2).
    unfold m2 in |- *.
      apply inv_hmap_L1L1.
       tauto.
   unfold m2 in H0.
     generalize (nf_L1L1_II m x' y' x y H0 a1 b a a0).
     simpl in |- *.
     elim (expf_dec m x (cA m zero y)).
     tauto.
   elim (expf_dec m x' (cA m zero y')).
    elim (expf_dec (L m one x' y') x (cA m zero y)).
     elim (expf_dec (L m one x y) x' (cA m zero y')).
      intros.
        symmetry  in |- *.
         tauto.
      tauto.
     tauto.
    tauto.
  intros.
    assert (inv_hmap m2).
   unfold m2 in |- *.
     apply inv_hmap_L1L1.
      tauto.
  generalize (nf_L1L1_IV m x' y' x y H0 a0 b0 b a).
    simpl in |- *.
    elim (expf_dec m x (cA m zero y)).
    tauto.
  elim (expf_dec (L m one x y) x' (cA m zero y')).
   elim (expf_dec m x' (cA m zero y')).
    elim (expf_dec (L m one x' y') x (cA m zero y)).
      tauto.
     tauto.
    tauto.
  elim (expf_dec m x' (cA m zero y')).
   elim (expf_dec (L m one x' y') x (cA m zero y)).
    intros.
      symmetry  in |- *.
       tauto.
    tauto.
   tauto.
 elim (expf_dec (L m one x y) x' (cA m zero y')).
  intros.
     lia.
 intros.
   assert (inv_hmap m2).
  unfold m2 in |- *; apply inv_hmap_L1L1.
     tauto.
 generalize (nf_L1L1_VI m x' y' x y H0 a b1 b b0).
   simpl in |- *.
   elim (expf_dec m x' (cA m zero y')).
  elim (expf_dec m x (cA m zero y)).
    tauto.
  elim (expf_dec (L m one x' y') x (cA m zero y)).
    tauto.
  elim (expf_dec (L m one x y) x' (cA m zero y')).
    tauto.
  intros.
    symmetry  in |- *.
     tauto.
  tauto.
elim (expf_dec (L m one x' y') x (cA m zero y)).
 elim (expf_dec (L m one x y) x' (cA m zero y')).
  intros.
     lia.
 intros.
   simpl in |- *.
   generalize (nf_L1L1_V m x y x' y' H b1 b0 a b).
   simpl in |- *.
   elim (expf_dec m x (cA m zero y)).
   tauto.
 elim (expf_dec m x' (cA m zero y')).
   tauto.
 elim (expf_dec (L m one x y) x' (cA m zero y')).
   tauto.
 elim (expf_dec (L m one x' y') x (cA m zero y)).
   tauto.
  tauto.
elim (expf_dec (L m one x y) x' (cA m zero y')).
 intros.
   assert (inv_hmap m2).
  unfold m2 in |- *.
    apply inv_hmap_L1L1.
     tauto.
 generalize (nf_L1L1_V m x' y' x y H0 b0 b1 a b).
   simpl in |- *.
   elim (expf_dec m x (cA m zero y)).
   tauto.
 elim (expf_dec m x' (cA m zero y')).
   tauto.
 elim (expf_dec (L m one x' y') x (cA m zero y)).
   tauto.
 elim (expf_dec (L m one x y) x' (cA m zero y')).
  intros.
    symmetry  in |- *.
     tauto.
  tauto.
intros.
   lia.
Qed.

(*=====================================================
=======================================================
		    END OF PART 7
=======================================================
=====================================================*)

