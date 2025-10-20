(*=====================================================
=======================================================
               TOPOLOGICAL FMAPS, HMAPS -

              WITH TAGS AND EMBEDDINGS

                      PART 7:

              expf, degreef /L0, /L1

                  (DIM 0 and DIM 1) 

(* RATHER REDONDANT WITH J2C... *)
=======================================================
=====================================================*)

Require Export Del06.

(*=====================================================
              cA_I, cF_I, expf_I
=====================================================*)

Lemma cA_I:forall(m:fmap)(k:dim)(x z:dart)(u:tag)(p:point),
  inv_hmap m -> prec_I m x -> x <> z ->
    (cA (I m x u p) k z = cA m k z). 
Proof.
simpl in |- *.
intros.
elim (eq_dart_dec x z).
 tauto.
 tauto.
Qed.

Lemma cA_1_I:
 forall(m:fmap)(k:dim)(x z:dart)(u:tag)(p:point),
  inv_hmap m -> prec_I m x -> x <> z ->
    (cA_1 (I m x u p) k z = cA_1 m k z). 
Proof.
simpl in |- *.
intros.
elim (eq_dart_dec x z).
 tauto.
 tauto.
Qed.

Lemma cF_I:forall(m:fmap)(x z:dart)(u:tag)(p:point),
  inv_hmap m -> prec_I m x -> exd m z -> x <> z ->
    (cF (I m x u p) z = cF m z). 
Proof.
unfold cF in |- *.
intros.
rewrite cA_1_I.
 rewrite cA_1_I.
  tauto.
  tauto.
  tauto.
  tauto.
 tauto.
 tauto.
 simpl in |- *.
   elim (eq_dart_dec x z).
  tauto.
  intro.
    intro.
    unfold prec_I in H0.
    generalize (exd_cA_1 m zero z).
    rewrite <- H3.
    tauto.
Qed.

Lemma Iter_cF_I:
 forall(m:fmap)(x z:dart)(u:tag)(p:point)(i:nat),
  inv_hmap m -> prec_I m x -> 
   exd m z -> x <> z ->
    Iter (cF (I m x u p)) i z = Iter (cF m) i z. 
Proof.
induction i.
 simpl in |- *.
   tauto.
    intros.
    unfold Iter; fold Iter.
    rewrite IHi.
  rewrite cF_I.
   tauto.
   tauto.
   tauto.
   assert (MF.f = cF).
    tauto.
    rewrite <- H3.
      generalize (MF.exd_Iter_f m i z).
      tauto.
   intro.
     unfold prec_I in H0.
     rewrite H3 in H0.
  generalize (MF.exd_Iter_f m i z).
     tauto.
  tauto.
  tauto.
  tauto.
  tauto.
Qed.

(* OK!: *)

Lemma expf_I:
 forall(m:fmap)(x z t:dart)(u:tag)(p:point),
  inv_hmap m -> prec_I m x -> 
   exd m z -> x <> z ->
    (expf (I m x u p) z t <-> expf m z t). 
Proof.
intros.
unfold expf in |- *.
unfold MF.expo in |- *.
simpl in |- *.
assert (MF.f = cF).
 tauto.
 rewrite H3.
   split.
  intros.
    decompose [and] H4.
    clear H4.
    elim H9.
    intros i Eq.
    split.
   tauto.
   split.
    tauto.
    split with i.
      generalize (Iter_cF_I m x z u p i H7 H8 H1 H2).
      intro.
      rewrite <- H4.
      tauto.
  intros.
    decompose [and] H4.
    clear H4.
    split.
   tauto.
   split.
    tauto.
    elim H8.
      intros i Hi.
      split with i.
      rewrite Iter_cF_I.
     tauto.
     tauto.
     tauto.
     tauto.
     tauto.
Qed.

(*=====================================================
=======================================================
              expf_L0, degree_L0
======================================================
=====================================================*)

(* RECALL: NEW VERSION (IN J2B): 
EQUIVALENT TO THE ANCIENT ONE: 

Theorem expof_L0_CNS: 
  forall(m:fmap)(X Y z t:dart)(H:inv_hmap m),
    prec_L m zero X Y -> exd m z ->
       let m1 := L m zero X Y in
       let Y_0_1 := cF m Y in
       let X0 := cA m zero X in
       let X_1 := cA_1 m one X in
 (expof m1 z t <->
   (if expof_dec m Y X_1 H
    then
      betweenf m X_1 z Y /\ betweenf m X_1 t Y \/
      betweenf m Y_0_1 z X0 /\ betweenf m Y_0_1 t X0 \/
      ~ expof m Y z /\ expof m z t
    else
      expof m z t \/
      expof m Y z /\ expof m X_1 t \/
      expof m Y t /\ expof m X_1 z)).
*)

(* ANCIENT VERSION: OK, WITH THE PREVIOUS RESULT: *)

Theorem expf_L0_CNS:forall (m:fmap)(x y z t:dart),
  inv_hmap (L m zero x y) -> exd m z ->
  (expf (L m zero x y) z t <->
   let x0 := cA m zero x in
   let x_1 := cA_1 m one x in
   let y_0:= cA_1 m zero y in
   let y_0_1 := cA_1 m one y_0 in
   (if expf_dec m x_1 y 
    then betweenf m x_1 z y /\ betweenf m x_1 t y
      \/ betweenf m y_0_1 z x0 /\ betweenf m y_0_1 t x0
      \/ ~ expf m x_1 z /\ expf m z t 
    else   expf m z t
      \/ expf m z y /\ expf m t x0
      \/ expf m t y /\ expf m z x0)).
Proof.
intros.
assert (prec_L m zero x y).
 simpl in H.
    tauto.
assert (inv_hmap m).
 simpl in H;  tauto.
generalize (expof_L0_CNS m x y z t H2 H1 H0).
  simpl in |- *.
  fold (cF m y) in |- *.
  set (x0 := cA m zero x) in |- *.
  set (x_1 := cA_1 m one x) in |- *.
  assert (x_1 = cF m x0).
 unfold x0 in |- *.
   unfold cF in |- *.
   rewrite cA_1_cA in |- *.
  fold x_1 in |- *.
     tauto.
  tauto.
 unfold prec_L in H1;  tauto.
assert (expof m x0 x_1).
 unfold expof in |- *.
   unfold MF.expo in |- *.
   split.
  unfold x0 in |- *.
    generalize (exd_cA m zero x).
    unfold prec_L in H1;  tauto.
 split with 1%nat.
   simpl in |- *.
   rewrite H3 in |- *.
    tauto.
elim (expof_dec m y x_1 H2).
 elim (expf_dec m x_1 y).
  intros.
    assert (~ expof m y z <-> ~ expf m x_1 z).
   split.
    intro.
      intro.
      apply H6.
      apply expof_trans with x_1.
      tauto.
    generalize (expf_expof m x_1 z).
       tauto.
   intro.
     intro.
     apply H6.
     apply expf_trans with y.
    apply expf_symm.
      generalize (expf_expof m y x_1).
       tauto.
   generalize (expf_expof m y z);  tauto.
  generalize (expf_expof m z t H2).
    intro.
    generalize (expf_expof (L m zero x y) z t H).
    intro.
     tauto.
 intros.
   elim b.
   apply expf_symm.
   generalize (expf_expof m y x_1 H2).
    tauto.
elim (expf_dec m x_1 y).
 intros.
   elim b.
   apply expof_symm.
   tauto.
 generalize (expf_expof m x_1 y H2).
    tauto.
intros.
  set
   (E1 :=
    expof m z t \/ expof m y z /\ expof m x_1 t \/ 
       expof m y t /\ expof m x_1 z)
   in |- *.
  set
   (E2 :=
    expf m z t \/ expf m z y /\ expf m t x0 \/
       expf m t y /\ expf m z x0)
   in |- *.
  fold E1 in H5.
  cut (E1 <-> E2).
 generalize (expf_expof (L m zero x y) z t H).
    tauto.
assert (expof m y z <-> expf m z y).
 split.
  intro.
    apply expf_symm.
    generalize (expf_expof m y z).
     tauto.
 intro.
   apply expof_symm.
   tauto.
 generalize (expf_expof m z y).
    tauto.
assert (expof m x_1 t <-> expof m t x0).
 split.
  intro.
    apply expof_trans with x_1.
   apply expof_symm.
     tauto.
    tauto.
  apply expof_symm.
    tauto.
   tauto.
 intro.
   apply expof_symm.
   tauto.
 apply expof_trans with x0.
   tauto.
  tauto.
assert (expof m x_1 t <-> expf m t x0).
 generalize (expf_expof m t x0).
    tauto.
clear H7.
  assert (expof m y t <-> expf m t y).
 generalize (expf_expof m t y).
   generalize (expof_symm m y t).
   generalize (expof_symm m t y).
    tauto.
assert (expof m x_1 z <-> expof m z x0).
 split.
  intro.
    apply expof_trans with x_1; apply expof_symm;  tauto.
 intro.
   apply expof_trans with x0.
  apply expof_symm.
    tauto.
   tauto.
 apply expof_symm.
   tauto.
  tauto.
assert (expof m x_1 z <-> expf m z x0).
 generalize (expf_expof m z x0).
    tauto.
clear H9.
  unfold E1 in |- *; unfold E2 in |- *.
  generalize (expf_expof m z t H2).
   tauto.
Qed.

(* COROLLARIES: *)

Theorem expf_L0_CS:forall (m:fmap)(x y z t:dart),
  inv_hmap (L m zero x y) -> exd m z ->
   let x0 := cA m zero x in
   let x_1 := cA_1 m one x in
   let y_0:= cA_1 m zero y in
   let y_0_1 := cA_1 m one y_0 in
   (if expf_dec m x_1 y 
    then betweenf m x_1 z y /\ betweenf m x_1 t y
      \/ betweenf m y_0_1 z x0 /\ betweenf m y_0_1 t x0
      \/ ~ expf m x_1 z /\ expf m z t 
    else   expf m z t
      \/ expf m z y /\ expf m t x0
      \/ expf m t y /\ expf m z x0)
   -> expf (L m zero x y) z t.
Proof.
intros.
generalize (expf_L0_CNS m x y z t H H0).
 tauto.
Qed.

Theorem expf_L0_CN:forall (m:fmap)(x y z t:dart),
  inv_hmap (L m zero x y) -> exd m z ->
   let x0 := cA m zero x in
   let x_1 := cA_1 m one x in
   let y_0:= cA_1 m zero y in
   let y_0_1 := cA_1 m one y_0 in
 expf (L m zero x y) z t ->
   (if expf_dec m x_1 y 
    then betweenf m x_1 z y /\ betweenf m x_1 t y
      \/ betweenf m y_0_1 z x0 /\ betweenf m y_0_1 t x0
      \/ ~ expf m x_1 z /\ expf m z t 
    else   expf m z t
      \/ expf m z y /\ expf m t x0
      \/ expf m t y /\ expf m z x0).
Proof.
intros.
generalize (expf_L0_CNS m x y z t H H0).
 tauto.
Qed.

(*==================================================== 
         CONSEQUENCES FOR PARTICULAR CASES: 
=====================================================*)

(* WHAT ARE y, x0... AFTER L0: *)

Lemma y_L0:forall (m:fmap)(x y:dart),
  let m1 := L m zero x y in 
  inv_hmap m1 -> y = cA m1 zero x.
Proof.
 simpl in |- *.
intros.
elim (eq_dart_dec x x).
 tauto.
 tauto.
Qed.
  
Lemma x0_L0:forall (m:fmap)(x y:dart),
  let m1 := L m zero x y in 
  inv_hmap m1 -> 
     cA m zero x = bottom m1 zero x.
Proof.
simpl in |- *.
intros.
elim (eq_dart_dec y (bottom m zero x)).
 intros.
   unfold prec_L in H.
   rewrite cA_eq.
  elim (succ_dec m zero x).
   tauto.
   tauto.
  tauto.
 unfold prec_L in H.
   intro.
   rewrite cA_eq.
  elim (succ_dec m zero x).
   tauto.
   tauto.
  tauto.
Qed.

Lemma x_1_L0:forall (m:fmap)(x y:dart),
  let m1 := L m zero x y in 
  inv_hmap m1 -> 
     cA_1 m one x = cA_1 m1 one x.
Proof.
simpl in |- *.
tauto.
Qed.

Lemma y_0_L0:forall (m:fmap)(x y:dart),
  let m1 := L m zero x y in 
  inv_hmap m1 -> 
     cA_1 m zero y = top m1 zero x.
Proof.
simpl in |- *.
unfold prec_L in |- *.
intros.
rewrite cA_1_top.
 elim (eq_dart_dec x (top m zero x)).
  tauto.
  intro.
    rewrite nosucc_top in b.
   tauto.
   tauto.
   tauto.
   tauto.
 tauto.
 tauto.
 tauto.
Qed.

Lemma y_0_1_L0:forall (m:fmap)(x y:dart),
  let m1 := L m zero x y in 
  inv_hmap m1 -> 
     cF m y = cA_1 m1 one (top m1 zero x).
Proof.
intros.
unfold cF in |- *.
unfold m1 in |- *.
rewrite <- y_0_L0.
 simpl in |- *.
   tauto.
 fold m1 in |- *.
   tauto.
Qed.

(* OK :*)

Lemma not_expf_expf_L0_CN: forall (m:fmap)(x y:dart),
  inv_hmap (L m zero x y) -> 
   let x_1:= cA_1 m one x in
   let x0 := cA m zero x in
    ~expf m x_1 y -> 
      expf (L m zero x y) y x0.
Proof.
intros.
assert (inv_hmap (L m zero x y)).
  tauto.
rename H1 into Inv.
  simpl in Inv.
  unfold prec_L in Inv.
  apply expf_L0_CS.
  tauto.
 tauto.
elim (expf_dec m (cA_1 m one x) y).
 fold x_1 in |- *.
    tauto.
fold x_1 in |- *.
  intros.
  right.
  left.
  split.
 apply expf_refl.
   tauto.
  tauto.
fold x0 in |- *.
  apply expf_refl.
  tauto.
unfold x0 in |- *.
  generalize (exd_cA m zero x).
   tauto.
Qed.

(* CONTRAVARIANT FORM AND NC: *)

Lemma expf_not_expf_L0_CV:forall (m:fmap)(x y:dart),
  inv_hmap (L m zero x y) -> 
  let x_1:= cA_1 m one x in
  let x0 := cA m zero x in
     expf (L m zero x y) y x0 ->
        ~expf m x_1 y.
Proof.
intros.
assert (inv_hmap (L m zero x y)).
 tauto.
 rename H1 into Inv.
   simpl in Inv.
   unfold prec_L in Inv.
   decompose [and] Inv.
   clear Inv.
   generalize (expf_L0_CN m x y y x0 H H2 H0).
   simpl in |- *.
   fold x_1 in |- *.
   elim (expf_dec m x_1 y).
  intros.
    elim H6.
   clear H6.
     intros.
     decompose [and] H6.
     clear H6.
     generalize H9.
     clear H9.
     unfold betweenf in |- *.
     unfold MF.between in |- *.
     intros.
     elim H9.
    intros i Hi.
      clear H9.
      elim Hi.
      clear Hi.
      intros j Hj.
      decompose [and] Hj.
      clear Hj.
      set (p := MF.Iter_upb m x_1) in |- *.
      fold p in H12.
      assert (Iter (MF.f m) (p - 1) x_1 = x0).
     rewrite <- MF.Iter_f_f_1.
      unfold p in |- *.
        rewrite MF.Iter_upb_period.
       simpl in |- *.
         assert (MF.f_1 = cF_1).
        tauto.
        rewrite H11.
          unfold cF_1 in |- *.
          unfold x_1 in |- *.
          rewrite cA_cA_1.
         fold x0 in |- *.
           tauto.
         tauto.
         tauto.
       tauto.
       unfold x_1 in |- *.
         generalize (exd_cA_1 m one x).
         tauto.
      tauto.
      unfold x_1 in |- *.
        generalize (exd_cA_1 m one x).
        tauto.
      lia.
     assert (i = (p - 1)%nat).
      apply MF.unicity_mod_p with m x_1.
       tauto.
       unfold x_1 in |- *.
         generalize (exd_cA_1 m one x).
         tauto.
       fold p in |- *.
         lia.
       fold p in |- *.
         lia.
       rewrite H6.
         symmetry  in |- *.
         tauto.
      absurd (i = (p - 1)%nat).
       elim (Nat.eq_dec i j).
        intro.
          rewrite a0 in H6.
          assert (x0 = y).
         rewrite <- H6.
           tauto.
         unfold x0 in H14.
           tauto.
        intro.
          lia.
       tauto.
    tauto.
    unfold x_1 in |- *.
      generalize (exd_cA_1 m one x).
      tauto.
   clear H6.
     intro.
     elim H6.
    clear H6.
      fold x0 in |- *.
      fold (cF m y) in |- *.
      intro.
      decompose [and] H6.
      clear H6.
      assert (exd m x0).
     unfold x0 in |- *.
       generalize (exd_cA m zero x).
       tauto.
     assert (exd m x_1).
      unfold x_1 in |- *.
        generalize (exd_cA_1 m one x).
        tauto.
      generalize H8.
        clear H8.
        unfold betweenf in |- *.
        unfold MF.between in |- *.
        intros.
        elim H8.
       intros i Hi.
         clear H8.
         elim Hi.
         clear Hi.
         intros j Hj.
         decompose [and] Hj.
         clear Hj.
         set (y_0_1 := cF m y) in |- *.
         fold y_0_1 in H8.
         fold y_0_1 in H12.
         set (p := MF.Iter_upb m (cF m y)) in |- *.
         fold p in H14.
         fold y_0_1 in p.
         assert (Iter (MF.f m) (p - 1) y_0_1 = y).
        rewrite <- MF.Iter_f_f_1.
         unfold p in |- *.
           rewrite MF.Iter_upb_period.
          simpl in |- *.
            assert (MF.f_1 = cF_1).
           tauto.
           rewrite H13.
             unfold cF_1 in |- *.
             unfold y_0_1 in |- *.
             unfold cF in |- *.
             rewrite cA_cA_1.
            rewrite cA_cA_1.
             tauto.
             tauto.
             tauto.
            tauto.
            generalize (exd_cA_1 m zero y).
              tauto.
          tauto.
          unfold y_0_1 in |- *.
            generalize (exd_cF m y).
            tauto.
         tauto.
         unfold y_0_1 in |- *.
           generalize (exd_cF m y).
           tauto.
         lia.
        assert (i = (p - 1)%nat).
         apply MF.unicity_mod_p with m y_0_1.
          tauto.
          unfold y_0_1 in |- *.
            generalize (exd_cF m y).
            tauto.
          fold p in |- *.
            lia.
          fold p in |- *.
            lia.
          rewrite H13.
            tauto.
         elim (Nat.eq_dec i j).
          intro.
            rewrite a0 in H8.
            rewrite H12 in H8.
            unfold x0 in H8.
            tauto.
          intro.
            elim b.
            lia.
       tauto.
       generalize (exd_cF m y).
         tauto.
    clear H6.
      tauto.
  tauto.
Qed.

(* THEN, BY expf_dec: IMPORTANT RESULT *)

Theorem expf_not_expf_L0: forall (m:fmap)(x y:dart),
  inv_hmap (L m zero x y) -> 
  let x_1:= cA_1 m one x in
  let x0 := cA m zero x in
   (expf m x_1 y <-> 
       ~expf (L m zero x y) y x0).
Proof.
intros.
generalize (expf_not_expf_L0_CV m x y H).
simpl in |- *.
fold x0 in |- *.
fold x_1 in |- *.
intros.
generalize (not_expf_expf_L0_CN m x y H).
simpl in |- *.
fold x0 in |- *.
fold x_1 in |- *.
intro.
generalize (expf_dec m x_1 y).
tauto.
Qed.

(*====================================================
                  degreef_L0 
=====================================================*)

Open Scope nat_scope.

(* RECALL:
Definition degreef:=MF0Tr.MfM.degree.

Lemma degreef_0_1:
  MF0Tr.MfM.degree = MF1Tr.MfM.degree.
Proof. tauto. Qed.
*)

(* OK: *)

Theorem degreef_L0_merge:
  forall (m : fmap) (x y : dart),
    inv_hmap m -> exd m x -> exd m y ->
       let m1 := L m zero x y in
       let x_1:= cA_1 m one x in
   ~ expof m y x_1 ->
 degreef m1 x_1 = degreef m x_1 + degreef m y.
Proof.
intros.
set (X := y) in |- *.
set (Y := x_1) in |- *.
assert (x = cA m one Y).
 unfold Y in |- *.
   unfold x_1 in |- *.
   rewrite cA_cA_1 in |- *.
   tauto.
  tauto.
  tauto.
assert (m1 = L m zero (cA m one Y) X).
 rewrite <- H3 in |- *.
   unfold X in |- *.
    tauto.
unfold degreef in |- *.
  assert (m1 = ModcF0.Tr m X Y).
 unfold m1 in |- *.
    tauto.
rewrite H4 in |- *.
  rewrite <- H4 in |- *.
  rewrite H5 in |- *.
  apply MF0Tr.degree_Tr_merge_y.
 unfold ModcF0.Prec_Tr in |- *.
    tauto.
 tauto.
unfold X in |- *.
   tauto.
unfold Y in |- *.
  unfold x_1 in |- *.
  generalize (exd_cA_1 m one x).
   tauto.
unfold expof in H2.
   tauto.
Qed.

(* OK: *)

Lemma MF0Tr_cF_Iter: forall(m:fmap)(i:nat)(z:dart),
  Iter (MF0Tr.MfM.f m) i z = Iter (cF m) i z.
Proof.
induction i.
 simpl in |- *.
    tauto.
intros.
  simpl in |- *.
  rewrite IHi in |- *.
   tauto.
Qed.

(* SPLIT: OK: *)

Theorem degreef_L0_split
     : forall (m : fmap) (x y : dart) (j : nat),
       inv_hmap m ->
       exd m x ->
       exd m y ->
       let m1 := L m zero x y in
       let y1 := cF m y in
       let x_1:= cA_1 m one x in
       let dx_1 := degreef m x_1 in
       x_1 = Iter (cF m) j y ->
        2 <= j <= dx_1 ->
 degreef m1 x_1 + degreef m1 y1 = degreef m x_1.
Proof.
simpl in |- *.
intros.
unfold degreef in |- *.
set (X := y) in |- *.
set (Y := cA_1 m one x) in |- *.
assert (x = cA m one Y).
 unfold Y in |- *.
   rewrite cA_cA_1 in |- *.
   tauto.
  tauto.
  tauto.
rewrite H4 in |- *.
  assert (ModcF0.Tr m X Y = L m zero (cA m one Y) X).
  tauto.
rewrite <- H5 in |- *.
  apply (MF0Tr.degree_Tr_split m X Y j).
  tauto.
unfold X in |- *.
   tauto.
unfold Y in |- *.
  generalize (exd_cA_1 m one x).
   tauto.
unfold Y in |- *.
   tauto.
unfold ModcF0.Prec_Tr in |- *.
   tauto.
unfold Y in |- *.
   tauto.
Qed.

(*==================================================
====================================================
              degreef_L1, expf_L1
====================================================
===================================================*)

(* OK, USEFUL ? 

Lemma cF_L1:forall(m:fmap)(x y z:dart),
  inv_hmap m -> prec_L m one x y ->
   let x10 := cF_1 m x in 
   let y0 := cA m zero y in   
   let y_1 := cA_1 m one y in
   let m1:= L m one x y in
  cF m1 z =
   if eq_dart_dec y0 z then x
   else if eq_dart_dec x10 z then y_1
          else cF m z. 
Proof.
intros.
unfold m1 in |- *.
elim (exd_dec m z).
 intro.
   rename a into Ez.
   unfold m1 in |- *.
   rewrite cF_L in |- *.
   elim (eq_dim_dec one zero).
  intro.
    inversion a.
 intros.
   elim (eq_dart_dec y (cA_1 m zero z)).
  intro.
    elim (eq_dart_dec y0 z).
   fold m1 in |- *.
      tauto.
  intros.
    elim b0.
    unfold y0 in |- *.
    rewrite a in |- *.
    rewrite cA_cA_1 in |- *.
    tauto.
   tauto.
   tauto.
 elim (eq_dart_dec (cA m one x) (cA_1 m zero z)).
  fold m1 in |- *.
    intros.
    elim (eq_dart_dec y0 z).
   unfold y0 in |- *.
     intro.
     elim b0.
     rewrite <- a0 in |- *.
     rewrite cA_1_cA in |- *.
     tauto.
    tauto.
   unfold prec_L in H0.
      tauto.
  elim (eq_dart_dec x10 z).
   intros.
     unfold y_1 in |- *.
      tauto.
  intros.
    unfold x10 in b1.
    elim b1.
    unfold cF_1 in |- *.
    rewrite a in |- *.
    rewrite cA_cA_1 in |- *.
    tauto.
   tauto.
   tauto.
 intros.
   elim (eq_dart_dec y0 z).
  intro.
    unfold y0 in a.
    elim b1.
    rewrite <- a in |- *.
    rewrite cA_1_cA in |- *.
    tauto.
   tauto.
  unfold prec_L in H0.
     tauto.
 elim (eq_dart_dec x10 z).
  unfold x10 in |- *.
    intros.
    unfold cF_1 in a.
    elim b0.
    rewrite <- a in |- *.
    rewrite cA_1_cA in |- *.
    tauto.
   tauto.
  generalize (exd_cA m one x).
    unfold prec_L in H0.
     tauto.
  tauto.
intros.
  elim (eq_dart_dec y0 z).
 intro.
   unfold y0 in a.
   elim b.
   rewrite <- a in |- *.
   generalize (exd_cA m zero y).
   unfold prec_L in H0.
    tauto.
elim (eq_dart_dec x10 z).
 unfold x10 in |- *.
   intros.
   elim b.
   rewrite <- a in |- *.
   generalize (exd_cF_1 m x).
   unfold prec_L in H0.
    tauto.
intros.
  assert (~ exd m1 z).
 unfold m1 in |- *.
   simpl in |- *.
    tauto.
assert (inv_hmap m1).
 unfold m1 in |- *.
   simpl in |- *.
    tauto.
generalize (exd_cF_not_nil m1 z H2).
  intro.
  intros.
  generalize (exd_dec m z).
  intro.
  generalize (exd_dec m1 z).
  intro.
  generalize (eq_dart_dec (cF m z) nil).
  generalize (eq_dart_dec (cF m1 z) nil).
  intros.
  assert (cF m z = nil).
 generalize (exd_cF_not_nil m z H).
   intro.
    tauto.
assert (cF m1 z = nil).
  tauto.
fold m1 in |- *.
  rewrite H8 in |- *.
   tauto.
Qed.

*)

(*===================================================
           NEW INSTANTIATIONS  OF 
           degreef_L1, expof_L1: 
====================================================*)

(* MERGE: ANCIENT FORM NEWLY PROVEN: OK!! *)

Theorem degreef_L1_merge: 
  forall (m:fmap)(x y z:dart),
   let y0 := cA m zero y in   
   let m1 := L m one x y in 
   inv_hmap m1 -> exd m z ->
   ~expf m x y0 ->
   let dx:= degreef m x in
   let dy0:= degreef m y0 in
   MF.degree m1 z =
      if expf_dec m x z then dx + dy0 
      else if expf_dec m y0 z then dx + dy0
           else degreef m z.
Proof.
intros.
generalize H.
intro.
unfold m1 in H2.
simpl in H2.
unfold prec_L in H2.
decompose [and] H2.
clear H2.
set (X := y0) in |- *.
set (Y := x) in |- *.
set (dX := dy0) in |- *.
set (dY := dx) in |- *.
unfold m1 in |- *.
fold Y in |- *.
assert (y = cA_1 m zero X).
 unfold X in |- *.
   unfold y0 in |- *.
   rewrite cA_1_cA in |- *.
   tauto.
  tauto.
  tauto.
rewrite H2 in |- *.
  unfold expf in H1.
  assert (~ MF.expo m x y0).
  tauto.
assert (ModcF1.Prec_Tr m y0 x).
 unfold ModcF1.Prec_Tr in |- *.
    tauto.
assert (ModcF1.Tr m y0 x = L m one x y).
 unfold ModcF1.Tr in |- *.
   unfold y0 in |- *.
   rewrite cA_1_cA in |- *.
   tauto.
  tauto.
  tauto.
assert (inv_hmap (ModcF1.Tr m y0 x)).
 rewrite H11 in |- *.
   fold m1 in |- *.
    tauto.
assert (~ MF1Tr.MfM.expo m y0 x).
 intro.
   elim H8.
   apply MF.expo_symm.
   tauto.
  tauto.
assert (exd m y0).
 unfold y0 in |- *.
   generalize (exd_cA m zero y).
    tauto.
generalize (MF1Tr.degree_Tr_merge_summary m y0 x z H3 H10 H14 H5 H0 H12 H13).
  assert (MF.degree = MF1Tr.MfM.degree).
  tauto.
unfold dY in |- *.
  unfold dX in |- *.
  fold (degreef m x) in |- *.
  unfold dx in |- *; unfold dy0 in |- *.
  unfold degreef in |- *.
  assert (MF0Tr.MfM.degree = MF1Tr.MfM.degree).
  tauto.
rewrite <- H16 in |- *.
  fold (degreef m x) in |- *.
  fold (degreef m y0) in |- *.
  unfold X in |- *.
  unfold Y in |- *.
  unfold y0 in |- *.
  rewrite cA_1_cA in |- *.
 fold y0 in |- *.
   fold (degreef m z) in |- *.
   rewrite H11 in |- *.
   rewrite H15 in |- *.
   rewrite <- H16 in |- *.
   fold (degreef (L m one x y) z) in |- *.
   fold m1 in |- *.
   elim (MF1Tr.MfM.expo_dec m y0 z H3).
  elim (expf_dec m y0 z).
   elim (expf_dec m x z).
    intros.
      rewrite Nat.add_comm in |- *.
       tauto.
   intros.
     rewrite Nat.add_comm in |- *.
      tauto.
  unfold expf in |- *.
     tauto.
 elim (expf_dec m y0 z).
  unfold expf in |- *.
     tauto.
 elim (MF1Tr.MfM.expo_dec m x z H3).
  elim (expf_dec m x z).
   intros.
     rewrite Nat.add_comm in |- *.
      tauto.
  unfold expf in |- *.
     tauto.
 elim (expf_dec m x z).
  unfold expf in |- *.
     tauto.
  tauto.
 tauto.
 tauto.
Qed.

(* SPLIT: ANCIENT FORM NEWLY PROVEN: OK!! *)

Theorem degreef_L1_split: 
  forall (m:fmap)(x y z:dart)(j : nat),
   let y0 := cA m zero y in
   let y_1:= cA_1 m one y in   
   let m1 := L m one x y in   
   let dx:= degreef m x in
   inv_hmap m1 -> exd m z ->
   x = Iter (cF m) j y0 ->
   2 <= j <= dx ->
   degreef m z =
      if expf_dec m x z 
      then degreef m1 x + degreef m1 y_1 
      else degreef m1 z.
Proof.
intros.
generalize H.
intro.
unfold m1 in H3.
simpl in H3.
unfold prec_L in H3.
decompose [and] H3.
clear H3.
assert (ModcF1.Tr m y0 x = L m one x y).
 unfold ModcF1.Tr in |- *.
   unfold y0 in |- *.
   rewrite cA_1_cA in |- *.
   tauto.
  tauto.
  tauto.
assert (ModcF1.Prec_Tr m y0 x).
 unfold ModcF1.Prec_Tr in |- *.
    tauto.
assert (inv_hmap (ModcF1.Tr m y0 x)).
 rewrite H3 in |- *.
   fold m1 in |- *.
    tauto.
assert (exd m y0).
 unfold y0 in |- *.
   generalize (exd_cA m zero y).
    tauto.
generalize
 (MF1Tr.degree_Tr_split_summary m y0 x z j 
      H4 H9 H12 H6 H0 H1 H2 H11).
  assert (MF0Tr.MfM.degree = MF1Tr.MfM.degree).
  tauto.
assert (MF.degree = MF1Tr.MfM.degree).
  tauto.
rewrite <- H13 in |- *.
  rewrite H3 in |- *.
  fold m1 in |- *.
  fold (degreef m1 x) in |- *.
  fold (degreef m1 z) in |- *.
  assert (MF1Tr.MfM.f m y0 = y_1).
 unfold y0 in |- *.
   unfold MF1Tr.MfM.f in |- *.
   assert (cF = ModcF1.M.f).
   tauto.
 rewrite <- H15 in |- *.
   unfold cF in |- *.
   rewrite cA_1_cA in |- *.
  fold y_1 in |- *.
     tauto.
  tauto.
  tauto.
rewrite H15 in |- *.
  fold (degreef m1 y_1) in |- *.
  fold (degreef m z) in |- *.
  elim (MF1Tr.MfM.expo_dec m x z H4).
 elim (expf_dec m x z).
   tauto.
 unfold expf in |- *.
    tauto.
elim (expf_dec m x z).
 unfold expf in |- *.
    tauto.
 tauto.
Qed.

(* ANCIENT FORM, NEWLY PROVEN, OK: *)

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
Proof.
intros.
assert (prec_L m one x y).
 simpl in H.
    tauto.
assert (inv_hmap m).
 simpl in H;  tauto.
generalize (expof_L1_CNS m x y z t H2 H1 H0).
  simpl in |- *.
  fold (cF_1 m x) in |- *.
  set (y0 := cA m zero y) in |- *.
  set (y_1 := cA_1 m one y) in |- *.
  elim (expof_dec m y0 x H2).
 elim (expf_dec m x y0).
  intros.
    assert (~ expof m y0 z <-> ~ expf m x z).
   split.
    intro.
      intro.
      apply H4.
      apply expof_trans with x.
      tauto.
    generalize (expf_expof m x z).
       tauto.
   intro.
     intro.
     apply H4.
     apply expf_trans with y0.
    apply expf_symm.
      generalize (expf_expof m y0 x).
       tauto.
   generalize (expf_expof m y0 z).
      tauto.
  generalize (expf_expof (L m one x y) z t).
    intros.
    generalize (expf_expof m z t H2).
     tauto.
 intros.
   elim b.
   apply expf_symm.
   generalize (expf_expof m y0 x).
    tauto.
elim (expf_dec m x y0).
 intros.
   elim b.
   apply expof_symm.
   tauto.
 generalize (expf_expof m x y0 H2).
    tauto.
set
 (E1 := expof m z t \/ expof m y0 z /\ expof m x t \/
    expof m y0 t /\ expof m x z)
 in |- *.
  set
   (E2 :=
    expf m z t \/ expf m z x /\ expf m t y0 \/
       expf m t x /\ expf m z y0)
   in |- *.
  intros.
  cut (E1 <-> E2).
 generalize (expf_expof (L m one x y) z t).
    tauto.
assert (expof m y0 z <-> expf m z y0).
 split.
  intro.
    apply expf_symm.
    generalize (expf_expof m y0 z).
     tauto.
 intro.
   apply expof_symm.
   tauto.
 generalize (expf_expof m z y0).
    tauto.
assert (expof m x t <-> expf m t x).
 split.
  intro.
    apply expf_symm.
    generalize (expf_expof m x t).
     tauto.
 intro.
   apply expof_symm.
   tauto.
 generalize (expf_expof m t x).
    tauto.
assert (expof m x z <-> expf m z x).
 split.
  intro.
    apply expf_symm.
    generalize (expf_expof m x z).
     tauto.
 intro.
   apply expof_symm.
   tauto.
 generalize (expf_expof m z x).
    tauto.
assert (expof m y0 t <-> expf m t y0).
 split.
  intro.
    apply expf_symm.
    generalize (expf_expof m y0 t).
     tauto.
 intro.
   apply expof_symm.
   tauto.
 generalize (expf_expof m t y0).
    tauto.
generalize (expf_expof m z t).
  intro.
  unfold E1 in |- *.
  unfold E2 in |- *.
   tauto.
Qed.

(* OK: *)

Theorem expf_L1_CN:forall (m:fmap)(x y z t:dart),
  inv_hmap (L m one x y) -> exd m z ->
  expf (L m one x y) z t -> 
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
          \/ expf m t x /\ expf m z y0.
Proof.
intros.
generalize (expf_L1_CNS m x y z t H H0).
 tauto.
Qed.

(* OK: *)

Theorem expf_L1_CS:forall (m:fmap)(x y z t:dart),
  inv_hmap (L m one x y) -> exd m z ->
    let x1 := cA m one x in
    let x10 := cA m zero x1 in 
    let y0 := cA m zero y in   
    let y_1 := cA_1 m one y in
      (if expf_dec m x y0 
      then betweenf m x z y0 /\ betweenf m x t y0
        \/ betweenf m y_1 z x10 /\ betweenf m y_1 t x10
        \/ ~ expf m x z /\ expf m z t 
      else   expf m z t
          \/ expf m z x /\ expf m t y0
          \/ expf m t x /\ expf m z y0)
     -> expf (L m one x y) z t.
Proof.
intros.
generalize (expf_L1_CNS m x y z t H H0).
 tauto.
Qed.

(*=====================================================
=======================================================
                    END OF PART 7
=======================================================
=====================================================*)

