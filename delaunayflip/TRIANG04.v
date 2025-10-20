(*=====================================================
=======================================================
               TOPOLOGICAL HMAPS, MAPS -
               WITH TAGS AND EMBEDDINGS

                  DELAUNAY TRIANGULATIONS
 
                  Embeddings, Flip (END)  :
         Preservation of the embedding properties
                      

                               PART 4, 
                           COMPILED (8 min)

JULY 2009
=======================================================
=====================================================*)

Require Export TRIANG03.

(*=====================================================
      KNUTH axiomatics [CB08] for ccw and collinear 
=====================================================*)

Module Type SigKnuth.

Parameter point : Set.

Parameter ccw : point -> point -> point -> Prop.

Parameter collinear : point -> point -> point -> Prop.

Axiom ccw_dec : forall (p q r : point),
  {ccw p q r} + {~ ccw p q r}.

Axiom ccw_axiom_1 : forall (p q r : point),
  ccw p q r -> ccw q r p.

Axiom ccw_axiom_2 : forall (p q r : point),
  ccw p q r -> ~ ccw p r q.

Axiom ccw_axiom_2_refl : forall (p q r : point),
  ~ collinear p q r -> ~ ccw p q r -> ccw p r q.

Axiom ccw_axiom_3 : forall (p q r : point),
  ~ collinear p q r -> (ccw p q r) \/ (ccw p r q).

Axiom ccw_axiom_4 : forall (p q r t : point),
  (ccw t q r) -> (ccw p t r) -> (ccw p q t) -> (ccw p q r).

Axiom ccw_axiom_5 : forall (p q r s t : point),
  (ccw t s p) -> (ccw t s q) -> (ccw t s r) -> (ccw t p q) -> (ccw t q r) -> 
  (ccw t p r).

Axiom ccw_axiom_5_bis : forall (p q r s t : point),
  (ccw s t p) -> (ccw s t q) -> (ccw s t r) -> (ccw t p q) -> (ccw t q r) -> 
  (ccw t p r).

Axiom collinear_dec : forall (p q r : point),
  {collinear p q r} + {~ collinear p q r}.

Axiom collinear_com : forall (p q r : point),
  collinear p q r -> collinear p r q.

End SigKnuth.

(* FONCTOR TO PROVE PROPERTIES
AT AN ABSTRACT LEVEL: *)

Module FK(M:SigKnuth)<:SigKnuth
   with Definition point:= M.point
   with Definition ccw:= M.ccw
   with Definition collinear:= M.collinear.
Definition point:= M.point.
Definition ccw:= M.ccw.
Definition collinear:= M.collinear.
Definition ccw_dec:= M.ccw_dec. 
Definition ccw_axiom_1:= M.ccw_axiom_1.
Definition ccw_axiom_2:= M.ccw_axiom_2.
Definition ccw_axiom_2_refl:= M.ccw_axiom_2_refl.
Definition ccw_axiom_3:= M.ccw_axiom_3.
Definition ccw_axiom_4:= M.ccw_axiom_4.
Definition ccw_axiom_5:= M.ccw_axiom_5.
Definition ccw_axiom_5_bis:= M.ccw_axiom_5_bis.
Definition collinear_dec:= M.collinear_dec. 
Definition collinear_com:= M.collinear_com.

Lemma not_collinear_com : forall (p q r : point),
  ~collinear p q r -> ~collinear p r q.
Proof.
intros p q r. unfold collinear. 
generalize (collinear_dec p r q). 
generalize (collinear_com p r q). 
tauto.
Qed.

Lemma ccw_axiom_6:  forall p q r, 
    ccw p q r -> p <> q.
Proof.
   unfold ccw. intros. intro. 
   rewrite <-H0 in H. 
   generalize (ccw_axiom_1 p p r H). 
   generalize (ccw_axiom_2 p p r H). 
 tauto. 
Qed.

Lemma ccw_axiom_6_bis:  forall p q r, 
    ccw p q r -> (p <> q /\ q <> r /\ r <> p).
Proof.
   intros. generalize (ccw_axiom_1 p q r H). intro. 
split. apply ccw_axiom_6 with r. tauto. 
split. apply ccw_axiom_6 with p. tauto. 
generalize (ccw_axiom_1 q r p H0). intro. 
   apply (ccw_axiom_6 r p q H1). 
Qed.

End FK.

(* ================================ *)
(* ========== ########## ========== *)
(* ================================ *)

Module ModelOfKnuth <: SigKnuth.

Open Scope R_scope.

Definition point := point.

(* ================================ *)
(* ========== ########## ========== *)
(* ================================ *)

Definition det (p q r : point) : R :=
  (fst p * snd q) - (fst q * snd p) - 
     (fst p * snd r) + (fst r * snd p) +
  (fst q * snd r) - (fst r * snd q).

Lemma eq_det : forall (p q r : point),
  det p q r = det q r p.
Proof.
intros p q r.
unfold det; ring.
Qed.

Lemma neq_det : forall (p q r : point),
  det p q r = - det p r q.
Proof.
intros p q r.
unfold det; ring.
Qed.

(* ================================ *)
(* ========== ########## ========== *)
(* ================================ *)

Definition ccw (p q r : point) : Prop :=
  (det p q r > 0).

Lemma ccw_dec : forall (p q r : point),
  {ccw p q r} + {~ccw p q r}.
Proof.
intros p q r.
unfold ccw.
apply Rgt_dec.
Qed.

(* ======= ####### ======= *)

Definition collinear (p q r : point) : Prop :=
  (det p q r = 0).

Lemma collinear_com : forall (p q r : point),
  collinear p q r -> collinear p r q.
Proof.
intros p q r.
unfold collinear.
rewrite (neq_det p r q). intro. 
rewrite H. rewrite Ropp_0. tauto.
Qed.

Lemma collinear_dec : forall (p q r : point),
  {collinear p q r} + {~collinear p q r}.
Proof.
intros p q r.
unfold collinear.
generalize (total_order_T (det p q r) 0).
generalize (Rlt_dichotomy_converse (det p q r) 0).
tauto.
Qed.

(*
Lemma not_collinear_com : forall (p q r : point),
  ~collinear p q r -> ~collinear p r q.
Proof.
intros p q r. intro. 
generalize (collinear_dec p r q). intro.
elim H0. intro. generalize (collinear_com p r q). tauto. 
tauto. 
Qed.
*)

(* =================================== *)
(* ============ ######### ============ *)
(* =================================== *)

Lemma Rle_neq_lt : forall (r1 r2 : R),
  r1 <= r2 -> r1 <> r2 -> r1 < r2.
Proof.
intros r1 r2 H1 H2.
elim (Rdichotomy r1 r2).
trivial.
generalize (Rle_not_lt r2 r1).
tauto.
assumption.
Qed.

Lemma R_gt_0_plus : forall (r1 r2 : R),
  r1 > 0 -> r2 > 0 -> r1 + r2 > 0.
Proof.
intros r1 r2 H1 H2.
apply Rgt_trans with r1.
 pattern r1 at 2; rewrite <- (Rplus_0_r r1).
 apply Rplus_gt_compat_l; assumption.
assumption.
Qed.

Lemma R_gt_0_mult : forall (r1 r2 : R),
  r1 > 0 -> r2 > 0 -> r1 * r2 > 0.
Proof.
apply Rmult_gt_0_compat.
Qed.

Lemma R_gt_0_div : forall (r1 r2 : R),
  r1 > 0 -> r2 > 0 -> r1 * / r2 > 0.
Proof.
intros r1 r2 H1 H2.
apply R_gt_0_mult.
 assumption.
 unfold Rgt in *; auto with real.
Qed.

Lemma R_mult_div : forall (r1 r2 r3 : R),
  r1 = r2 * r3 -> r2 > 0 -> r1 * / r2 = r3.
Proof.
intros r1 r2 r3 H1 H2.
subst r1; auto with real.
Qed.

(* ================================ *)
(* ========== ########## ========== *)
(* ================================ *)

Lemma ccw_axiom_1 : forall (p q r : point),
  ccw p q r -> ccw q r p.
Proof.
intros p q r.
unfold ccw.
generalize (eq_det p q r).
intros H1.
rewrite H1.
trivial.
Qed.

(* ===== ##### ===== *)

Lemma ccw_axiom_2 : forall (p q r : point),
  ccw p q r -> ~ ccw p r q.
Proof.
intros p q r.
unfold ccw.
rewrite (neq_det p q r).
generalize (Ropp_gt_lt_contravar (- det p r q) 0).
rewrite Ropp_involutive.
rewrite Ropp_0.
intro H1.
generalize (Rlt_le (det p r q) 0).
intros H2.
generalize (Rle_not_lt 0 (det p r q)).
intros H3.
tauto.
Qed.

Lemma ccw_axiom_2_refl : forall (p q r : point),
  ~ collinear p q r -> ~ ccw p q r -> ccw p r q.
Proof.
intros p q r.
unfold collinear.
unfold ccw.
intros H1 H2.
generalize (Rnot_gt_le (det p q r) 0).
intro H3.
generalize (Rle_neq_lt (det p q r) 0).
intros H4.
generalize (Ropp_gt_lt_0_contravar (det p q r)).
intro H5.
rewrite (neq_det p r q).
tauto.
Qed.

(* ===== ##### ===== *)

Lemma ccw_axiom_3 : forall (p q r : point),
  ~ collinear p q r -> (ccw p q r) \/ (ccw p r q).
Proof.
intros p q r.
elim (ccw_dec p q r).
tauto.
generalize (ccw_axiom_2_refl p q r).
tauto.
Qed.

(* ===== ##### ===== *)

Lemma ccw_axiom_4 : forall (p q r t : point),
  (ccw t q r) -> (ccw p t r) -> (ccw p q t) -> (ccw p q r).
Proof.
intros p q r t H1 H2 H3.
unfold ccw in *.
assert (det t q r + det p t r + det p q t = det p q r).
unfold det; ring.
rewrite <- H.
apply R_gt_0_plus; [apply R_gt_0_plus; assumption | assumption].
Qed.

(* ===== ##### ===== *)

Lemma ccw_axiom_5 : forall (p q r s t : point),
  (ccw t s p) -> (ccw t s q) -> (ccw t s r) -> (ccw t p q) -> (ccw t q r) -> 
  (ccw t p r).
Proof.
intros p q r s t H1 H2 H3 H4 H5.
unfold ccw in *.
replace (det t p r) with ((det t p q * det t s r + det t q r * det t s p) * / (det t s q)).
apply R_gt_0_div.
 apply R_gt_0_plus.
  apply R_gt_0_mult; assumption.
  apply R_gt_0_mult; assumption.
 assumption.
apply R_mult_div.
 unfold det; ring.
 assumption.
Qed.

(* ===== ##### ===== *)

Lemma ccw_axiom_5_bis : forall (p q r s t : point),
  (ccw s t p) -> (ccw s t q) -> (ccw s t r) -> (ccw t p q) -> (ccw t q r) -> 
  (ccw t p r).
Proof.
intros p q r s t H1 H2 H3 H4 H5.
unfold ccw in *.
replace (det t p r) with ((det t p q * det s t r + det t q r * det s t p) * / (det s t q)).
apply R_gt_0_div.
 apply R_gt_0_plus.
  apply R_gt_0_mult; assumption.
  apply R_gt_0_mult; assumption.
 assumption.
apply R_mult_div.
 unfold det; ring.
 assumption.
Qed.

End ModelOfKnuth.

(*====================================================
             Well-embedded triangulation
            (with only one external triangle)
====================================================*)

Open Scope R_scope.

Module FKMK:= FK (ModelOfKnuth). 

Definition ccw:= ModelOfKnuth.ccw.
Definition ccw_dec:= ModelOfKnuth.ccw_dec.

Definition collinear:= ModelOfKnuth.collinear.
Definition collinear_dec:= ModelOfKnuth.collinear_dec.
Definition collinear_com:= ModelOfKnuth.collinear_com.
Definition not_collinear_com:= FKMK.not_collinear_com.

Definition ccw_axiom_1:= ModelOfKnuth.ccw_axiom_1.
Definition ccw_axiom_2:= ModelOfKnuth.ccw_axiom_2.
Definition ccw_axiom_2_refl:= ModelOfKnuth.ccw_axiom_2_refl.
Definition ccw_axiom_3:= ModelOfKnuth.ccw_axiom_3.
Definition ccw_axiom_4:= ModelOfKnuth.ccw_axiom_4.
Definition ccw_axiom_5:= ModelOfKnuth.ccw_axiom_5.
Definition ccw_axiom_5_bis:= ModelOfKnuth.ccw_axiom_5_bis.
Definition ccw_axiom_6 := FKMK.ccw_axiom_6.
Definition ccw_axiom_6_bis:= FKMK.ccw_axiom_6_bis.

(* Darts of the same face are embedded into
a direct triangle (ccw): *)

Definition ccw_triangle(m:fmap)(z:dart):Prop:=
  let pz:= fpoint m z in
  let pzf:= fpoint m (cF m z) in
  let pzff:= fpoint m (cF m (cF m z)) in
      ccw pz pzf pzff.

(* Darts of the same face are embedded into
an indirect triangle (cw): *)

Definition collinear_triangle(m:fmap)(z:dart):Prop:=
  let pz:= fpoint m z in
  let pzf:= fpoint m (cF m z) in
  let pzff:= fpoint m (cF m (cF m z)) in
      collinear pz pzff pzf.

Definition cw_triangle(m:fmap)(z:dart):Prop:=
  let pz:= fpoint m z in
  let pzf:= fpoint m (cF m z) in
  let pzff:= fpoint m (cF m (cF m z)) in
      ccw pz pzff pzf.

(* TO PROVE FIRST IN KNUTH'S AXIOM.: *)

Lemma cw_ccw_triangle: forall (m:fmap)(z:dart),
   cw_triangle m z <-> 
        (~ccw_triangle m z /\ ~collinear_triangle m z).
Proof.
  intros. unfold cw_triangle. 
  unfold ccw_triangle. 
 split. intro. 
    split. apply ccw_axiom_2. tauto. 
    unfold collinear_triangle. 
    unfold ccw in H. unfold collinear. 
    unfold ModelOfKnuth.ccw in H. 
    unfold ModelOfKnuth.collinear. 
    unfold ModelOfKnuth.det. 
    unfold ModelOfKnuth.det in H.
    apply Rgt_not_eq. tauto. 
 unfold collinear_triangle. intros.  
    apply ccw_axiom_2_refl. 
    apply not_collinear_com. tauto. tauto. 
Qed.
   
Lemma ccw_cw_triangle: forall (m:fmap)(z:dart),
   ccw_triangle m z <-> 
        (~cw_triangle m z /\ ~collinear_triangle m z).
Proof.
 unfold cw_triangle. unfold ccw_triangle. 
 unfold collinear_triangle. 
 intros. 
 split. intro. 
    split. apply ccw_axiom_2. tauto.
    apply not_collinear_com. 
    unfold ccw in H. 
    unfold ModelOfKnuth.ccw in H. 
    unfold ModelOfKnuth.collinear. 
    apply Rgt_not_eq. tauto. intros. 
    apply ccw_axiom_2_refl. tauto. 
    tauto. 
Qed.

(*
Lemma ccw_collinear_cw_triangle_dec: forall (m:fmap)(z:dart),
   {ccw_triangle m z} + {collinear_triangle m z} + {cw_triangle m z}.
Admitted.
*)

(* Well embedding: *)

(* No null edge: *)

Definition isWellembede(m:fmap):Prop:=
   forall z:dart, exd m z ->
         fpoint m z <> fpoint m (cA m zero z).

(* Darts of the same vertex are embedded
 into the same point: *)

Definition isWellembedv(m:fmap):Prop:=
   forall z t:dart, exd m z -> expv m z t ->
         fpoint m z = fpoint m t.

(* Well-embedded faces: *)

Definition isWellembedf(m:fmap):Prop:=
  cw_triangle m 1%nat /\ 
     forall z, exd m z -> ~expf m z 1%nat -> ccw_triangle m z.

(* Well-embedded triangulation: *)

Definition isWellembed(m:fmap):Prop:=
  exd m 1%nat /\ isWellembede m /\ isWellembedv m /\ isWellembedf m.

(* What is about the COLLINEARITY of 3 sites ?? *)

(*====================================================
            New embeddings after L, B, etc., Flip
====================================================*)

Open Scope nat_scope.

(* OK: *)

Lemma fpoint_L: forall (m:fmap)(k:dim)(x y z:dart), 
  fpoint (L m k x y) z = fpoint m z.
Proof.
   simpl. tauto. 
Qed.

Lemma fpoint_B: forall (m:fmap)(k:dim)(x z:dart), 
  fpoint (B m k x) z = fpoint m z.
Proof.
   induction m. simpl. tauto. 
   simpl. intros. elim (eq_dart_dec d z). tauto. 
    intro. apply IHm. 
   simpl. intros. elim (eq_dim_dec d k). 
       elim (eq_dart_dec d0 x). tauto. 
         simpl. intros. apply IHm. simpl. intros.
          apply IHm. 
Qed.

Lemma fpoint_Split: forall (m:fmap)(x x' z:dart), 
  fpoint (Split m one x x') z = fpoint m z.
Proof. 
   unfold Split. intros.
     elim (succ_dec m one x). 
       elim (succ_dec m one x'). intros.
       rewrite fpoint_B. simpl. rewrite fpoint_B. tauto. 
          rewrite fpoint_B. tauto. rewrite fpoint_B. tauto. 
Qed.

Lemma fpoint_Shift: forall (m:fmap)(x z:dart), 
  fpoint (Shift m one x) z = fpoint m z.
Proof. 
   unfold Shift. intros. simpl. 
    rewrite fpoint_B. tauto. 
Qed.

Lemma fpoint_G: forall (m:fmap)(x y z:dart), 
  fpoint (G m one x y) z = fpoint m z.
Proof. 
    unfold G. intros.
     elim (succ_dec m one x). simpl. rewrite fpoint_B. tauto. 
     simpl. tauto. 
Qed.

Lemma fpoint_Merge: forall (m:fmap)(x y z:dart), 
  fpoint (Merge m one x y) z = fpoint m z.
Proof. 
    unfold Merge. intros.
     elim (pred_dec m one y). 
     rewrite fpoint_G.  rewrite fpoint_Shift. tauto. 
     rewrite fpoint_G. tauto. 
Qed.

Lemma fpoint_Flip_topo: forall (m:fmap)(x z:dart), 
  fpoint (Flip_topo m x) z = fpoint m z.
Proof. 
    unfold Flip_topo. intros.
    rewrite fpoint_Merge. rewrite fpoint_Merge. 
      rewrite fpoint_Split. rewrite fpoint_Split. 
     tauto. 
Qed.

Lemma fpoint_Flip_emb: forall (m:fmap)(x y xff yff z:dart),
    let pxff:= fpoint m xff in
    let pyff:= fpoint m yff in
 exd m x -> exd m y -> x <> y -> 
  fpoint (Flip_emb m x y xff yff) z =  
    if eq_dart_dec x z then pxff
     else if eq_dart_dec y z then pyff
          else fpoint m z. 
Proof.
  intros. unfold Flip_emb. 
    fold pxff. fold pyff. 
   rewrite fpoint_Chp.   rewrite fpoint_Chp.
    elim (eq_dart_dec x z). 
      elim (eq_dart_dec y z). intros. rewrite <-a in a0. tauto. 
        tauto. tauto. tauto. 
     generalize (exd_Chp m x pxff y). tauto.
Qed.

Lemma fpoint_Flip: forall (m:fmap)(x z:dart), 
 inv_hmap m -> isMap m ->
    let y := cA m zero x in
    let xff:= cF m (cF m x) in
    let yff:= cF m (cF m y) in
    let pxff:= fpoint m xff in
    let pyff:= fpoint m yff in
exd m x -> x <> y -> 
  fpoint (Flip m x) z =
     if eq_dart_dec x z then pxff
     else if eq_dart_dec y z then pyff
          else fpoint m z.
Proof. 
   intros. unfold Flip. 
     rewrite fpoint_Flip_emb. 
    fold y. rewrite fpoint_Flip_topo.  rewrite fpoint_Flip_topo. 
         rewrite fpoint_Flip_topo. 
    assert (exd m y). unfold y. generalize (exd_cA m zero x). tauto. 
   unfold isMap in H0. 
     assert (degreee m x = 2). apply H0. tauto. 
   generalize (degreee_invol_nofixpt m x H H1). intro. 
         assert (cA m zero x <> x /\ cA m zero (cA m zero x) = x).
            tauto. clear H5. fold y in H6. 
       decompose [and] H6. clear H6.
   generalize (invol_inverse m zero x H H1). intro. 
        assert (cA m zero x = cA_1 m zero x). tauto. clear H6. 
                fold y in H8. 
          assert (cF m x = cA_1 m one y). 
             unfold cF. rewrite H8. tauto. rewrite <-H6. 
        assert (degreee m y = 2). apply H0. tauto. 
    generalize (degreee_invol_nofixpt m y H H3). intro. 
         assert (cA m zero y <> y /\ cA m zero (cA m zero y) = y).
            tauto. clear H10. 
       decompose [and] H11. clear H11.
   generalize (invol_inverse m zero y H H3). intro. 
        assert (cA m zero y = cA_1 m zero y). tauto. clear H11. 
          assert (cF m y = cA_1 m one x). 
             unfold cF.  rewrite <-H13. rewrite H7. tauto. 
            rewrite <-H11. fold xff yff pxff pyff.
tauto.
generalize (exd_Flip_topo m x x). tauto. 
  fold y. generalize (exd_Flip_topo m x y). 
   generalize (exd_cA m zero x). fold y. tauto. 
   fold y. tauto.
Qed.

(*=========================================================
                 prec_Flip_emb and its Properties -
                    Implies prec_Flip:
==========================================================*)

Definition prec_Flip_emb(m:fmap)(x:dart):Prop :=
   let y := cA m zero x in
   let px := fpoint m x in
   let py := fpoint m y in
   let pxff := fpoint m (cF m (cF m x)) in
   let pyff := fpoint m (cF m (cF m y)) in
    ccw px py pxff /\ ccw py px pyff /\ 
       ccw px pyff pxff /\ ccw py pxff pyff.
  
(* Because isMap m: *)

Lemma x_neq_y: forall (m:fmap)(x:dart),
   inv_Triangulation m -> exd m x -> 
       x <> cA m zero x. 
Proof.
  unfold inv_Triangulation. intros m x. 
  set(y:= cA m zero x). intros. 
  decompose [and] H. clear H. unfold isMap in H3. 
  generalize (H3 x H0). intro. 
   generalize (degreee_invol_nofixpt m x H1 H0). 
    fold y. intros. intro. symmetry in H6. tauto. 
Qed.
    
Lemma px_neq_py: forall (m:fmap)(x:dart),
  isWellembede m -> exd m x ->
    fpoint m x <> fpoint m (cA m zero x). 
Proof.
  unfold isWellembede. intros. 
   apply H. tauto.
Qed.

(* Proofs that illegal entails prec_Flip: *)

Lemma prec_Flip_emb_pxff_neq_pyff: forall (m:fmap)(x:dart),
 exd m x -> isWellembede m -> prec_Flip_emb m x ->
   let y := cA m zero x in
   let px := fpoint m x in
   let py := fpoint m y in
   let pxff := fpoint m (cF m (cF m x)) in
   let pyff := fpoint m  (cF m (cF m y)) in
    pxff <> pyff.
Proof.
   unfold prec_Flip_emb.
   intros m x. set (y:=cA m zero x). 
   intros. decompose [and] H1. clear H1. 
   generalize (ccw_axiom_1
         (fpoint m y) (fpoint m (cF m (cF m x))) (fpoint m (cF m (cF m y))) H6). 
   intro. eapply ccw_axiom_6. apply H1. 
Qed.

Lemma cA_expv: forall m z, 
     exd m z -> expv m z (cA m one z). 
Proof.
   intros. unfold expv. unfold MA1.MfcA.expo. 
    split. tauto. split with 1%nat. simpl. tauto.
Qed.

Open Scope nat_scope.

(* Because isWellembed and prec_Flip_emb, OK: *)

Lemma prec_Flip_emb_degreev: forall (m:fmap)(x:dart),
  inv_Triangulation m -> isWellembede m -> isWellembedv m ->
    exd m x -> prec_Flip_emb m x ->
      (3 <= degreev m x /\ 3 <= degreev m (cA m zero x)). 
Proof.
  unfold inv_Triangulation. unfold prec_Flip_emb. intros m x H. intro Eme. 
  set (y:= cA m zero x). intros. 
  decompose [and] H. clear H.
   decompose [and] H2. clear H2. 
  rename H6 into C6. rename H10 into C10. 
    assert (exd m y). unfold y. generalize (exd_cA m zero x). tauto. 
        rename H2 into Ey. 
   generalize (degreee_invol_nofixpt m x H3 H1). intro. 
         assert (cA m zero x <> x /\ cA m zero (cA m zero x) = x).
           unfold isMap in H5. 
            generalize (H5 x H1). 
            tauto. clear H2. fold y in H6. 
   generalize (invol_inverse m zero x H3 H1). intro. 
        assert (cA m zero x = cA_1 m zero x). tauto. clear H2. 
                fold y in H9. 
  decompose [and] H6. clear H6. 
 generalize (degreee_invol_nofixpt m y H3 Ey). intro. 
         assert (cA m zero y <> y /\ cA m zero (cA m zero y) = y).
           unfold isMap in H5. 
            generalize (H5 y Ey). 
            tauto. clear H6. decompose [and] H11. clear H11. 
   generalize (invol_inverse m zero y H3 Ey). intro. 
        assert (cA m zero y = cA_1 m zero y). tauto. clear H11. 
   assert (x=cA_1 m zero y). unfold y. rewrite cA_1_cA. tauto. tauto. tauto.      
(* 1st PART: *)       
elim (Nat.eq_dec (degreev m x)  2). intro. 
   generalize (degreev_invol_nofixpt m x H3 H1). intro. 
        assert (cA m one x <> x /\ cA m one (cA m one x) = x). tauto. clear H14. 
     generalize (invol_inverse m one x H3 H1). intro. 
        assert (cA m one x = cA_1 m one x). tauto. 
      set(x1:= cA m one x). fold x1 in H16, H15, H14. 
     decompose [and] H15. clear H15. clear H14. 
         assert (exd m x1). unfold x1. generalize (exd_cA m one x). tauto. 
               rename H14 into Ex1. 
           assert (cF m y = x1). unfold cF. rewrite <-H11. symmetry. tauto. 
              set (x10:= cA m zero x1). 
               assert (x1 = cA_1 m zero x10). unfold x10. 
                 rewrite cA_1_cA. tauto. tauto. tauto. 
       generalize (degreee_invol_nofixpt m x1 H3 Ex1). intro. 
         assert (cA m zero x1 <> x1 /\ cA m zero (cA m zero x1) = x1).
            generalize (H5 x1 Ex1). 
            tauto. clear H19. decompose [and] H20. clear H20. 
               fold x10 in H21. 
     generalize (invol_inverse m zero x1 H3 Ex1). intro. 
        assert (cA m zero x1 = cA_1 m zero x1). tauto. clear H20. 
    assert (cF m (cF m y) = cA_1 m one x10). 
       unfold cF. fold x10 in H22. fold (cF m y). 
          rewrite H22. rewrite <-H14. tauto. 
        assert (cF = MF0Tr.MfM.f). tauto. 
     assert (x10 = cF_1 m x). unfold cF_1. fold x1. fold x10. tauto. 
       assert (degreef m x = 3). unfold isTriangulation in H7. 
          generalize (H7 x H1). unfold isTri. tauto. 
         assert (x10 = Iter (cF_1 m) 1 x). simpl. tauto. 
      assert (Iter (cF m) 3 x = x).  rewrite H23. 
         rewrite <-H25. unfold degreef. 
         rewrite MF0Tr.MfM.degree_per. tauto. tauto. tauto. 
       assert (x10 =  Iter (cF m) 2 x). 
          assert (2 = 3  - 1). lia. rewrite H28. 
             rewrite <-MF0Tr.MfM.Iter_f_f_1. 
               rewrite <-H23. rewrite H27. simpl. tauto. tauto. tauto.
               lia. simpl in H28. 
          assert (x10 = cA m one (cF m (cF m y))). rewrite H20. 
                 rewrite cA_cA_1. tauto. tauto. unfold x10. 
             generalize (exd_cA m zero x1). tauto. 
         unfold isWellembedv in H0. 
              assert (fpoint m (cF m (cF m y)) = 
                fpoint m (cA m one (cF m (cF m y)))). 
     apply H0. rewrite H14. generalize (exd_cF m x1). tauto. 
         apply cA_expv. 
              generalize (exd_cF m y). generalize (exd_cF m (cF m y)). tauto. 
             rewrite <-H29 in H30. rewrite H28 in H30. 
      symmetry in H30. absurd ( fpoint m (cF m (cF m x)) = fpoint m (cF m (cF m y))).
          apply  prec_Flip_emb_pxff_neq_pyff. tauto. tauto. 
             unfold prec_Flip_emb. tauto. tauto. 
            intro. 
(* 2nd PART: *)
 elim (Nat.eq_dec (degreev m y)  2). intro. 
   generalize (degreev_invol_nofixpt m y H3 Ey). intro. 
        assert (cA m one y <> y /\ cA m one (cA m one y) = y). tauto. clear H14. 
     generalize (invol_inverse m one y H3 Ey). intro. 
        assert (cA m one y = cA_1 m one y). tauto. 
      set(y1:= cA m one y). fold y1 in H16, H15, H14. 
     decompose [and] H15. clear H15. clear H14. 
         assert (exd m y1). unfold y1. generalize (exd_cA m one y). tauto. 
               rename H14 into Ey1. 
           assert (cF m x = y1). unfold cF. rewrite <-H9. symmetry. tauto. 
              set (y10:= cA m zero y1). 
               assert (y1 = cA_1 m zero y10). unfold y10. 
                 rewrite cA_1_cA. tauto. tauto. tauto. 
       generalize (degreee_invol_nofixpt m y1 H3 Ey1). intro. 
         assert (cA m zero y1 <> y1 /\ cA m zero (cA m zero y1) = y1).
            generalize (H5 y1 Ey1). 
            tauto. clear H19. decompose [and] H20. clear H20. 
               fold y10 in H21. 
     generalize (invol_inverse m zero y1 H3 Ey1). intro. 
        assert (cA m zero y1 = cA_1 m zero y1). tauto. clear H20. 
    assert (cF m (cF m x) = cA_1 m one y10). 
       unfold cF. fold y10 in H22. fold (cF m x). 
          rewrite H14. rewrite <-H22. tauto. 
        assert (cF = MF0Tr.MfM.f). tauto. 
     assert (y10 = cF_1 m y). unfold cF_1. fold y1. fold y10. tauto. 
       assert (degreef m y = 3). unfold isTriangulation in H7. 
          generalize (H7 y Ey). unfold isTri. tauto. 
         assert (y10 = Iter (cF_1 m) 1 y). simpl. tauto. 
      assert (Iter (cF m) 3 y = y).  rewrite H23. 
         rewrite <-H25. unfold degreef. 
         rewrite MF0Tr.MfM.degree_per. tauto. tauto. tauto. 
       assert (y10 =  Iter (cF m) 2 y). 
          assert (2 = 3  - 1). lia. rewrite H28. 
             rewrite <-MF0Tr.MfM.Iter_f_f_1. 
               rewrite <-H23. rewrite H27. simpl. tauto. tauto. tauto.
               lia. simpl in H28. 
          assert (y10 = cA m one (cF m (cF m x))). rewrite H20. 
                 rewrite cA_cA_1. tauto. tauto. unfold y10. 
             generalize (exd_cA m zero y1). tauto. 
         unfold isWellembedv in H0. 
              assert (fpoint m (cF m (cF m x)) = 
                fpoint m (cA m one (cF m (cF m x)))). 
     apply H0. rewrite H14. generalize (exd_cF m y1). tauto. 
       apply cA_expv. 
              generalize (exd_cF m x). generalize (exd_cF m (cF m x)). tauto. 
             rewrite <-H29 in H30. rewrite H28 in H30. 
     absurd ( fpoint m (cF m (cF m x)) = fpoint m (cF m (cF m y))).
          apply  prec_Flip_emb_pxff_neq_pyff. tauto. tauto. 
             unfold prec_Flip_emb. tauto. tauto. 
            intro. 
  unfold isPoly in H4. 
    generalize (H4 x H1).   generalize (H4 y Ey). intros. 
    split. lia. lia.
Qed.

(* THEN: *)

Lemma prec_Flip_emb_expf: forall (m:fmap)(x:dart),
  inv_Triangulation m -> isWellembedv m -> 
    exd m x -> prec_Flip_emb m x ->
      ~expf m x (cA m zero x). 
Proof. 
   unfold inv_Triangulation. intros m x H We. intros. 
     decompose [and] H. clear H. 
   set(y:=cA m zero x). intro. 
    assert (exd m y). unfold y. generalize (exd_cA m zero x). tauto. 
  rename H5 into Ey.
   assert (degreef m x = 3). 
    unfold isTriangulation in H6. unfold isTri in H6. 
    apply H6. tauto. 
    unfold expf in H. 
     assert (MF.expo2 m x y).  generalize (MF.expo_expo2 m x y). tauto. 
       unfold MF.expo2 in H7. 
    decompose [and] H7. clear H7. 
     elim H9. clear H9. intros j Hj. decompose [and] Hj. clear Hj. 
    assert (degreef=MF.degree). tauto. rewrite <-H10 in H7. 
       rewrite H5 in H7. 
     assert (MF.f = cF). tauto. 
  elim (Nat.eq_dec j 0). intro. rewrite a in H9. simpl in H9. 
   generalize H9; clear H9. apply x_neq_y. unfold inv_Triangulation.
           tauto. tauto. intro. 
  elim (Nat.eq_dec j 1). intro. rewrite a in H9. simpl in H9. 
          rewrite H11 in H9. unfold cF in H9. 
     generalize (degreee_invol_nofixpt m x H2 H0). intro. 
         assert (cA m zero x <> x /\ cA m zero (cA m zero x) = x).
           unfold isMap in H4. 
            generalize (H4 x H0). 
            tauto. clear H12. fold y in H13. 
   generalize (invol_inverse m zero x H2 H0). intro. 
        assert (cA m zero x = cA_1 m zero x). tauto. clear H12. 
                fold y in H14. 
           decompose [and] H13. clear H13. 
          rewrite <-H15 in H9. rewrite cA_1_cA in H9. 
           assert (y = cA m one y). rewrite <-H9. rewrite cA_cA_1. tauto. tauto. 
                tauto. symmetry in H13. 
          generalize (degreev_fixpt m y). intro. 
          assert (degreev m y = 1). tauto. clear H16. 
         unfold isPoly in H3. generalize (H3 y Ey). lia. tauto. tauto. intro.
  assert (j = 2). lia. 
    rewrite H12 in H9; simpl in H9. 
    generalize (degreee_invol_nofixpt m x H2 H0). intro. 
         assert (cA m zero x <> x /\ cA m zero (cA m zero x) = x).
           unfold isMap in H4. 
            generalize (H4 x H0). 
            tauto. clear H13. fold y in H14. 
       decompose [and] H14. clear H14.
   generalize (invol_inverse m zero x H2 H0). intro. 
        assert (cA m zero x = cA_1 m zero x). tauto. clear H14. 
                fold y in H16. 
          assert (cF m x = cA_1 m one y). 
             unfold cF. 
          rewrite <-H16. tauto. 
       assert (cA m one (cF m x) = y). unfold cF. 
         rewrite cA_cA_1. symmetry. tauto.   tauto. 
         generalize (exd_cA_1 m zero x). tauto. 
          unfold isWellembedv in We. 
     assert (fpoint m y = fpoint m (cF m x)). 
     rewrite <-H17. symmetry. apply We. 
         generalize (exd_cF m x). tauto. 
 apply cA_expv. generalize (exd_cF m x). tauto. 
      assert (fpoint m y = fpoint m (cF m (cF m x))).  
         rewrite <-H11. rewrite H9. tauto. 
       unfold prec_Flip_emb in H1. decompose [and] H1. 
       generalize (ccw_axiom_6_bis (fpoint m x)
               (fpoint m (cA m zero x)) (fpoint m (cF m (cF m x))) H20). 
         intros. 
     assert (fpoint m (cA m zero x) <> fpoint m (cF m (cF m x))). tauto. 
         fold y in H24. tauto. 
Qed.
        
Lemma isWellembed_expv: forall (m:fmap)(x:dart),
  inv_Triangulation m -> isWellembede m ->  isWellembedv m -> 
    exd m x -> ~expv m x (cA m zero x). 
Proof. 
   intros m x. set(y:=cA m zero x). 
     intros. intro. 
   unfold isWellembedv in H1. 
     assert ( fpoint m x = fpoint m y). 
        apply H1. tauto. tauto. 
     unfold isWellembede in H0. generalize (H0 x H2). fold y. tauto.
Qed.
      
(* Finally: *)

Theorem prec_Flip_emb_prec_Flip:  forall (m:fmap)(x:dart),
  inv_Triangulation m -> isWellembede m -> isWellembedv m -> 
    exd m x -> prec_Flip_emb m x ->
      prec_Flip m x. 
Proof.
    unfold prec_Flip. intros m x. 
     set (y:=cA m zero x). intros.
   split. tauto. split. 
   apply prec_Flip_emb_expf. tauto. tauto. tauto. tauto. 
    split. apply isWellembed_expv. tauto. tauto. tauto. tauto. 
  apply prec_Flip_emb_degreev.  tauto. tauto. tauto. tauto. tauto.
Qed.

(*===================================================
                cA0 and embedding
====================================================*)

Lemma cA0_Flip_topo : forall m x z,
   let m4:= Flip_topo m x in
  inv_Triangulation m -> prec_Flip m x -> exd m z -> 
       cA m4 zero z = cA m zero z.
Proof.
  unfold Flip_topo. intros. 
   generalize (exd_Flip_1_4 m x z).  intro. elim H2. clear H2.
 generalize (exd_Flip_1_4 m x x).   intro. elim H2. clear H2.
 generalize (inv_hmap_Flip_1_4 m x H H0). 
  set (x_1 := cA_1 m one x).
  set (y := cA m zero x).
  set (y_1 := cA_1 m one y).
  set (xff := cF m y_1).
  set (yff := cF m x_1).
  set (m1 := Split m one x x_1).
  set (m2 := Split m1 one y y_1). 
  set (m3 := Merge m2 one xff x). 
  set (m4 := Merge m3 one yff y).
   intros. unfold inv_Triangulation in H. decompose [and] H. clear H. 
  unfold prec_Flip in H0.  fold y in H0. decompose [and] H0. clear H0. 
   clear H4 H6. 
 assert (exd m y). unfold y. generalize (exd_cA m zero x). tauto. 
  rename H0 into Ey.
 generalize (exd_Flip_1_4 m x y). intro. elim H0. 
 fold x_1. fold y. fold y_1. fold xff. fold yff. fold m1. fold m2. fold m3. fold m4. 
intros. clear H0 H6. rename H4 into Em1y. 
  assert (exd m y_1). unfold y_1. generalize (exd_cA_1 m one y). tauto. 
   rename H0 into Ey_1. 
   assert (exd m xff). unfold xff. generalize (exd_cF m y_1). tauto. 
    rename H0 into Exff. 
  generalize (exd_Flip_1_4 m x xff). intro. elim H0. 
 fold x_1. fold y. fold y_1. fold xff. fold yff. fold m1. fold m2. fold m3. fold m4. 
   intros. clear H0 H6.  rename H5 into Em1xff.
  assert (exd m x_1). unfold x_1. generalize (exd_cA_1 m one x). tauto. 
   rename H0 into Ex_1. 
     assert (exd m yff). unfold yff. generalize (exd_cF m x_1). tauto. 
    rename H0 into Eyff. 
  generalize (exd_Flip_1_4 m x yff). intro. elim H0. 
 fold x_1. fold y. fold y_1. fold xff. fold yff. fold m1. fold m2. fold m3. fold m4. 
   intros. clear H0 H6.  rename H5 into Em1yff.
 unfold m4. rewrite cA0_Flip4. 
  unfold m3. rewrite cA0_Flip3. 
   unfold m2. unfold y_1. 
    assert (cA_1 m1 one y = cA_1 m one y). 
      unfold m1. unfold x_1. rewrite cA1_1_Flip1. 
         elim (eq_dart_dec (cA m one x) y). 
             intro. elim H10. unfold expv. unfold MA1.MfcA.expo.
              split. tauto. split with 1. simpl. tauto. 
           elim (eq_dart_dec x y). intro. elim H10. rewrite <-a. 
             apply expv_refl. tauto. tauto. tauto. lia. tauto. 
                unfold y. generalize (exd_cA m zero x). tauto. 
             rewrite <-H0. rewrite cA0_Flip2. 
    unfold m1. unfold x_1. rewrite cA0_Flip1. tauto.
   tauto. tauto. tauto. tauto. 
   tauto. tauto. tauto. tauto. tauto. tauto. tauto. tauto. tauto. tauto. 
Qed.

Lemma cA0_Flip : forall m x z,
  inv_Triangulation m -> prec_Flip m x -> exd m z -> 
       cA (Flip m x) zero z = cA m zero z.
Proof.
   intros. 
    unfold Flip. unfold Flip_emb. 
     rewrite cA_Chp. rewrite cA_Chp. 
        rewrite cA0_Flip_topo. tauto. tauto. tauto. 
     tauto. 
Qed.

Theorem embede_Flip: forall m x,
   inv_Triangulation m -> isWellembede m -> isWellembedv m -> 
     exd m x -> prec_Flip_emb m x -> 
            isWellembede (Flip m x). 
Proof.
   unfold isWellembede. intros m x H H0. intro Iwev. intros. 
    set(y:=cA m zero x). 
     assert (exd m z). generalize (exd_Flip m x z). tauto. 
   unfold inv_Triangulation in H. 
    decompose [and] H. clear H. 
     unfold prec_Flip_emb in H2. fold y in H2.
     decompose [and] H2. clear H2. 
     rename H12 into C12.
   assert (degreee m x = 2).
       unfold isMap in H7. apply H7. tauto.
       generalize (degreee_invol_nofixpt m x H5 H1). intro.
       assert 
             (cA m zero x <> x /\ cA m zero (cA m zero x) = x). tauto.
       fold y in H12. elim H12. clear H12. intros.
      generalize (invol_inverse m zero x H5 H1).
        fold y. intro. assert (y = cA_1 m zero x). tauto. clear H14.           
  rewrite cA0_Flip. rewrite fpoint_Flip. rewrite fpoint_Flip. 
    elim (eq_dart_dec x z). 
            elim (eq_dart_dec x (cA m zero z)).
                intros. rewrite <-a0 in a. fold y in a.
                      symmetry in a. tauto. 
            elim (eq_dart_dec (cA m zero x) (cA m zero z)). 
               intros. fold y. 
               apply prec_Flip_emb_pxff_neq_pyff. tauto. 
                 unfold isWellembed. tauto. unfold prec_Flip_emb. tauto. 
              intros. rewrite a in b. tauto. 
    elim (eq_dart_dec (cA m zero x) z). 
           elim (eq_dart_dec x (cA m zero z)). intros. fold y. 
                   intro. symmetry in H14. generalize H14. 
                    apply prec_Flip_emb_pxff_neq_pyff. tauto. 
                 unfold isWellembed. tauto. unfold prec_Flip_emb. tauto. 
          elim (eq_dart_dec (cA m zero x) (cA m zero z)). intros.
                   elim b0. rewrite <-(cA_1_cA m zero x). rewrite a. 
                     rewrite cA_1_cA. tauto. tauto. tauto. tauto. 
                             tauto. intros. fold y in a. rewrite <-a in b0. 
                           symmetry in H13. tauto. 
   elim (eq_dart_dec x (cA m zero z)). intros. 
              assert (y = z). rewrite  <-(cA_1_cA m zero z). 
                   rewrite <-a. tauto. tauto. tauto. fold y in b. tauto. 
 elim (eq_dart_dec (cA m zero x) (cA m zero z)). fold y. intros. 
        assert (degreee m z = 2). 
       unfold isMap in H7. apply H7. tauto.
       generalize (degreee_invol_nofixpt m z H5 H4). intro.
       assert 
             (cA m zero z <> z /\ cA m zero (cA m zero z) = z). tauto.
           rewrite <-a in H17. rewrite H13 in H17. tauto. 
         intros. apply H0. tauto. 
         tauto. tauto. tauto. fold y. intro. symmetry in H14. tauto. 
             tauto. tauto. tauto. fold y. intro. symmetry in H14. tauto. 
            unfold inv_Triangulation. tauto. 
            apply prec_Flip_emb_prec_Flip.  
            unfold inv_Triangulation. tauto. 
                 unfold isWellembede. tauto. 
        tauto. tauto. unfold prec_Flip_emb. tauto. tauto.
Qed.

(*===================================================
                cA1 and embedding
====================================================*)

(* OK: *)

Lemma cA1_Iter_fpoint :  forall m, 
 inv_hmap m -> 
  (forall z, exd m z -> fpoint m (cA m one z) = fpoint m z) ->
     (forall z i, exd m z -> let t := Iter (cA m one) i z in fpoint m z = fpoint m t).
Proof. 
  intros. induction i. unfold t. simpl. tauto. 
    unfold t. simpl. rewrite H0. apply IHi. 
     rewrite <-MA1.Iter_f_cA. 
     generalize (MA1.MfcA.exd_Iter_f m i z). tauto. 
Qed.

Lemma cA1_expv_fpoint :  forall m, inv_hmap m -> 
  (forall z, exd m z -> fpoint m (cA m one z) = fpoint m z) ->
     (forall z t, expv m z t -> fpoint m z = fpoint m t).
Proof.
  intros. unfold expv in H1. unfold MA1.MfcA.expo in H1. 
   decompose [and] H1. clear H1. elim H3. intros i Hi. clear H3. 
     rewrite <-Hi. rewrite MA1.Iter_f_cA. apply cA1_Iter_fpoint. 
         tauto. tauto. tauto. 
Qed.

Lemma cA1_Flip_1_4: forall(m:fmap)(x z:dart),
   let x_1 := cA_1 m one x in
   let y := cA m zero x in
   let y_1 := cA_1 m one y in
   let xff := cF m y_1 in
   let yff :=  cF m x_1 in
   let m1 := Split m one x x_1 in
   let m2 := Split m1 one y y_1 in 
   let m3 := Merge m2 one xff x in  
   let m4 := Merge m3 one yff y in
 inv_Triangulation m -> prec_Flip m x -> exd m z ->
  cA m4 one z = 
    if eq_dart_dec yff z then y 
    else if eq_dart_dec xff z then x
          else if eq_dart_dec y_1 z then cA m one y
                else if eq_dart_dec x_1 z then cA m one x
                      else if eq_dart_dec y z then cA m zero x_1
                           else if eq_dart_dec x z then cA m zero y_1
                                else cA m one z.
Proof.
 intros. rename H1 into Ez. 
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
intro. simpl in H14. 
assert (exd m y). tauto.
generalize (Tri_diff_face m y H2 H16 H5). 
intro Ty. simpl in Ty. 
generalize (Tri_diff_2faces m x y H2 H12 H16 H1 H5 H8). intro. 
   simpl in H18.
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
fold xff in H14. fold y in H11. 
generalize (Tri_diff_face m y H2 H16  H5). intro. simpl in H32. 
   rewrite <-H30 in H32. fold yff in H32. 
 assert (cA_1 m1 one y = cA_1 m one y). 
      unfold m1. unfold x_1. rewrite cA1_1_Flip1. 
         elim (eq_dart_dec (cA m one x) y). 
             intro. elim H7. unfold expv. unfold MA1.MfcA.expo.
              split. tauto. split with 1. simpl. tauto. 
           elim (eq_dart_dec x y). tauto. tauto. tauto.
           clear -H9; lia.
              tauto. tauto. 
 assert (exd m x_1). unfold x_1. generalize (exd_cA_1 m one x). tauto. 
            rename H34 into Ex_1. 
 assert (exd m yff). unfold yff. 
generalize (exd_cF m x_1). fold yff. tauto.
generalize (exd_Flip_1_4 m x yff). 
intro.
elim H35. fold y. fold y_1.
fold x_1. fold xff. fold yff.
fold m1. fold m2. fold m3. fold m4.
clear H35. intros.
assert (exd m yff /\ exd m1 yff /\ exd m2 yff /\ exd m3 yff /\ exd m4 yff). 
tauto. clear H36 H34 H35. rename H37 into Eyff. 
rename H14 into Tx. clear H5 H1 H12.
generalize (exd_Flip_1_4 m x z). 
intro.
elim H1. fold y. fold y_1.
fold x_1. fold xff. fold yff.
fold m1. fold m2. fold m3. fold m4.
clear H1. intros.
clear H5. rename H1 into Emz. 
 assert (2 <= degreev m1 y).
       unfold m1. unfold x_1. rewrite (degreev_Flip1 m x y H2). 
             elim (eq_dart_dec x y). tauto. fold x_1. 
               elim (expv_dec m x_1 y H2). intros.
  clear -H9; lia. intros. clear -H11; lia. tauto. tauto. 
  clear -H9; lia. rename H1 into Dm1y.  
assert (cA m1 one x = x). unfold m1. unfold x_1.  rewrite cA1_Flip1.
     elim (eq_dart_dec x x). tauto. tauto. tauto.
    clear -H9; lia. tauto. tauto. 
    rename H1 into cAm1x.
assert (cA m2 one x = x). 
   unfold m2. unfold y_1. rewrite <-H33. rewrite cA1_Flip2. 
       elim (eq_dart_dec y x). tauto. rewrite H33. fold y_1. 
      elim ( eq_dart_dec y_1 x ). intro. symmetry in a. tauto. tauto. 
          tauto. tauto. tauto. tauto. rename H1 into cAm2x. 
assert (cA m2 one y = y). 
    unfold m2. unfold y_1. rewrite <-H33. rewrite cA1_Flip2. 
       elim (eq_dart_dec y y). tauto. tauto. tauto. tauto. tauto. 
     tauto. rename H1 into cAm2y. 
assert (cA m3 one y = y). 
   unfold m3. rewrite cA1_Flip3. 
    elim (eq_dart_dec xff y). tauto.
    elim (eq_dart_dec x y). tauto. tauto. 
            tauto. tauto. tauto. tauto. tauto. 
      rename H1 into cAm3y.
(* PART 1*)
unfold m4. rewrite cA1_Flip4.
elim ( eq_dart_dec yff z). tauto. 
elim (eq_dart_dec y z). 
   elim (eq_dart_dec xff z). intros. 
      rewrite <-a0 in a. tauto. 
   elim (eq_dart_dec y_1 z). intros. 
       rewrite <-a0 in a. tauto. 
  elim (eq_dart_dec x_1 z). intros. rewrite <-a0 in a. 
         rewrite a in H30. symmetry in a. tauto. intros. 
           unfold m3. 
              rewrite cA1_Flip3. 
                  elim (eq_dart_dec xff yff). tauto. 
                       elim (eq_dart_dec x yff). tauto. intros.
               unfold m2.  
         unfold y_1. rewrite <-H33. 
        rewrite cA1_Flip2.
    elim (eq_dart_dec y yff). tauto. rewrite H33. 
     fold y_1. elim (eq_dart_dec y_1 yff). tauto. intros. 
       unfold m1. unfold x_1. 
            rewrite cA1_Flip1. 
         elim (eq_dart_dec x yff). tauto. fold x_1. 
          elim (eq_dart_dec x_1 yff). tauto. intros. 
              unfold yff. unfold cF. rewrite cA_cA_1. 
   assert (degreee m x_1 = 2). 
       unfold isMap in H4. apply H4. tauto. 
  generalize (degreee_invol_nofixpt m x_1 H2 Ex_1). intro.
assert 
 (cA m zero x_1 <> x_1 /\ cA m zero (cA m zero x_1) = x_1).
tauto.
clear H5. 
  generalize (invol_inverse m zero x_1 H2 Ex_1). intro. 
     assert (cA m zero x_1 = cA_1 m zero x_1). tauto. 
      symmetry. tauto. tauto. 
               generalize (exd_cA_1 m zero x_1). tauto. tauto.
   clear -H9; lia. tauto. 
                   tauto. tauto. tauto. tauto. tauto. 
             tauto. tauto. tauto. 
             unfold m2. unfold y_1. rewrite <-H33. 
             rewrite cA1_Flip2. elim (eq_dart_dec y x). tauto. 
                  rewrite H33. fold y_1. elim eq_dart_dec. intros. 
                symmetry in a0. tauto. 
           unfold m1. unfold x_1. rewrite cA1_Flip1.
              elim ( eq_dart_dec x x). tauto. tauto. tauto.
              clear -H9; lia. 
                  tauto. tauto. tauto. tauto. tauto. tauto. tauto. 
        intros. 
(* PART 2: *)
   assert (exd m y_1). tauto. rename H1 into Ey_1. 
    unfold m3. 
     rewrite cA1_Flip3. 
    elim (eq_dart_dec xff z). tauto. 
    elim (eq_dart_dec x z). 
          elim (eq_dart_dec y_1 z). intros. rewrite <-a in a0. tauto. 
          elim (eq_dart_dec x_1 z). intros. rewrite <-a in a0. tauto. intros. 
             unfold m2. unfold y_1. rewrite <-H33. 
               rewrite cA1_Flip2. 
          elim (eq_dart_dec y xff). intro. symmetry in a0. tauto. 
                 rewrite H33. fold y_1. 
          elim ( eq_dart_dec y_1 xff). tauto. intros. 
             unfold m1. unfold x_1. 
               rewrite cA1_Flip1. 
         elim (eq_dart_dec x xff). tauto. fold x_1. 
         elim (eq_dart_dec x_1 xff). intro. symmetry in a0. tauto. 
                intros. unfold xff. unfold cF. rewrite cA_cA_1. 
 assert (degreee m y_1 = 2). 
       unfold isMap in H4. apply H4. tauto. 
  generalize (degreee_invol_nofixpt m y_1 H2 Ey_1). intro.
assert 
 (cA m zero y_1 <> y_1 /\ cA m zero (cA m zero y_1) = y_1).
tauto.
clear H5. 
  generalize (invol_inverse m zero y_1 H2 Ey_1). intro. 
     assert (cA m zero y_1 = cA_1 m zero y_1). tauto. 
          symmetry. tauto. tauto. 
         generalize (exd_cA_1 m zero y_1). tauto. 
         tauto. clear -H9; lia. tauto.  tauto. tauto.  tauto. tauto. 
        tauto. 
       intros. 
(* PART 3: *)
      unfold m2. unfold y_1. rewrite <-H33. 
     rewrite cA1_Flip2. rewrite H33. fold y_1. 
    elim (eq_dart_dec y z). 
          elim (eq_dart_dec y_1 z). intros. 
              rewrite <-a0 in a. tauto. 
          elim (eq_dart_dec x_1 z). intros. 
                   rewrite <-a in a0. tauto. tauto.  
          elim (eq_dart_dec y_1 z). intros. 
                  unfold m1. unfold x_1. 
                  rewrite cA1_Flip1. 
                elim (eq_dart_dec x y). tauto. 
                fold x_1. 
                elim (eq_dart_dec x_1 y). 
                   intro. symmetry in a0. tauto. tauto. 
                tauto. clear -H9; lia. tauto. tauto. intros.
 (* PART 4: *)
       unfold m1. unfold x_1. 
       rewrite cA1_Flip1. fold x_1. 
        elim (eq_dart_dec x z). 
               elim (eq_dart_dec x_1 z). intros. 
                          rewrite <-a in a0. tauto. tauto. 
           tauto. tauto. clear -H9; lia. tauto. 
              tauto. tauto. tauto. tauto. tauto. 
                 tauto. tauto. tauto. 
             tauto. tauto. tauto. tauto. tauto. 
          tauto. tauto. 
Qed.

(* OK: *)

Lemma cA1_Flip: forall(m:fmap)(x z:dart),
   let x_1 := cA_1 m one x in
   let y := cA m zero x in
   let y_1 := cA_1 m one y in
   let xff := cF m y_1 in
   let yff :=  cF m x_1 in
 inv_Triangulation m -> prec_Flip m x -> exd m z ->
  cA (Flip m x) one z = 
    if eq_dart_dec yff z then y 
     else if eq_dart_dec xff z then x
            else if eq_dart_dec y_1 z then cA m one y
                   else if eq_dart_dec x_1 z then cA m one x
                    else if eq_dart_dec y z then cA m zero x_1
                     else if eq_dart_dec x z then cA m zero y_1
                            else cA m one z.
Proof. 
   intros. unfold Flip. 
   unfold Flip_emb. 
    rewrite cA_Chp.  rewrite cA_Chp.
    unfold Flip_topo. 
    apply cA1_Flip_1_4. tauto. tauto. tauto.
Qed.
   
(* OK: *)

Lemma fpoint_cA_Flip : forall m x z,
  let x_1 := cA_1 m one x in
   let y := cA m zero x in
   let y_1 := cA_1 m one y in
   let xff := cF m y_1 in
   let yff :=  cF m x_1 in
  let m6:= Flip m x in
  inv_Triangulation m -> prec_Flip m x -> exd m z ->
    fpoint m6 (cA m6 one z) =
       if eq_dart_dec yff z then fpoint m yff 
       else if eq_dart_dec xff z then fpoint m xff
              else if eq_dart_dec y_1 z then fpoint m (cA m one y)
                    else if eq_dart_dec x_1 z then fpoint m (cA m one x)
                          else if eq_dart_dec y z then fpoint m (cA m zero x_1)
                                 else if eq_dart_dec x z then  fpoint m (cA m zero y_1)
                                        else fpoint m (cA m one z).
Proof.
intros.  
  set (m1 := Split m one x x_1).
   set (m2 := Split m1 one y y_1). 
   set (m3 := Merge m2 one xff x). 
 set (m4 := Merge m3 one yff y). 
   unfold m6. 
   unfold Flip. 
rename H1 into Ez. 
   assert (inv_Triangulation m). tauto. 
unfold inv_Triangulation in  H1. 
decompose [and] H1. clear H1.
   assert (prec_Flip m x). tauto.
unfold prec_Flip in H1. decompose [and] H1. clear H1.
fold y in H7. fold y in H8.
   assert (exd m y).
generalize (exd_cA m zero x). fold y. tauto.
  assert (isTri m x). unfold isTriangulation in H6.
apply H6. tauto.
assert (isTri m y). unfold isTriangulation in H6. apply H6. tauto.
  generalize (Tri_diff_face m x H2 H5 H10). 
intro. simpl in H13. 
  generalize (Tri_diff_face m y H2 H1 H12). 
intro Ty. simpl in Ty. 
generalize (Tri_diff_2faces m x y H2 H5 H1 H10 H12 H8). intro. 
   simpl in H14.
  assert (degreee m x = 2).
unfold isMap in H4. apply H4. tauto.
generalize (degreee_invol_nofixpt m x H2 H5). intro.
assert 
(cA m zero x <> x /\ cA m zero (cA m zero x) = x).
tauto.
clear H16. fold y in H17. elim H17. clear H17. intros.
generalize (invol_inverse m zero x H2 H5).
fold y. intro. assert (y = cA_1 m zero x). tauto. clear H18.
assert (y_1=cF m x). unfold cF. rewrite <-H19; fold y_1. tauto.
assert (degreee m y = 2).
unfold isMap in H4. apply H4. tauto.
  generalize (degreee_invol_nofixpt m y H2 H1). intro.
assert 
 (cA m zero y <> y /\ cA m zero (cA m zero y) = y).
tauto.
clear H21. rewrite H17 in H22. elim H22. clear H22. intros.
  generalize (invol_inverse m zero y H2 H1).
rewrite H17. intro. assert (x = cA_1 m zero y). tauto. clear H23.
  assert (x_1=cF m y). 
unfold cF. rewrite <-H24; fold x_1. tauto.
rewrite fpoint_Flip_emb. 
  rewrite fpoint_Flip_topo. rewrite fpoint_Flip_topo.
    rewrite fpoint_Flip_topo.
  unfold Flip_topo. 
  fold y. fold y_1.
fold x_1. fold xff. fold yff.
   fold m1. fold m2. fold m3. fold m4. 
   unfold Flip_emb. rewrite cA_Chp. rewrite cA_Chp.
  unfold m4; unfold m3; unfold m2; unfold m1.
rewrite cA1_Flip_1_4. 
    fold y. fold y_1.
fold x_1. fold xff. fold yff.
(* TRUE BEGIN: *)
elim (eq_dart_dec yff z). 
   elim (eq_dart_dec x y). tauto. 
   elim (eq_dart_dec y y). tauto. tauto. 
elim (eq_dart_dec xff z). 
   elim (eq_dart_dec x x). tauto. tauto. 
elim (eq_dart_dec y_1 z). 
   elim (eq_dart_dec x (cA m one y)). 
    intros. 
     assert (y = cF_1 m y). unfold cF_1. rewrite <-a. tauto. 
       assert (y =  cF m y). rewrite H25 at 2. 
          rewrite cF_cF_1. tauto. tauto. tauto. tauto.
   elim (eq_dart_dec y (cA m one y)). intros. 
      assert (x = cF_1 m y).  unfold cF_1. rewrite <-a. 
             symmetry. tauto. 
                 assert (cF m x = y). rewrite H25. rewrite cF_cF_1. 
                      tauto. tauto. tauto. tauto.
    tauto. 
elim ( eq_dart_dec x_1 z). 
    elim (eq_dart_dec x (cA m one x)).
        intros. assert (y = cF_1 m x). unfold cF_1. 
            rewrite <-a. fold y. tauto. 
        assert (cF m y = x). rewrite H25. rewrite cF_cF_1. 
                      tauto. tauto. tauto. symmetry in H26. tauto. 
   elim (eq_dart_dec y (cA m one x)). intros. 
       assert (x = cF m x). unfold cF. rewrite <-H19. 
        rewrite a. rewrite cA_1_cA. tauto. tauto. tauto. tauto.
   intros. tauto.
elim (eq_dart_dec y z). 
    elim (eq_dart_dec x (cA m zero x_1)). intros. 
        assert (x_1=cA_1 m zero x). rewrite a.
            rewrite cA_1_cA. tauto. tauto. 
          unfold x_1. generalize (exd_cA_1 m one x). tauto. 
            rewrite <-H17 in H25. rewrite cA_1_cA in H25. 
              rewrite H25 in H23. tauto. tauto. tauto. 
   elim (eq_dart_dec y (cA m zero x_1)). intros. 
        assert (x_1 = cA_1 m zero y).  rewrite a.
            rewrite cA_1_cA. tauto. tauto. 
               unfold x_1. generalize (exd_cA_1 m one x). tauto. 
            rewrite <-H24 in  H25. rewrite H25 in H23. tauto. 
  tauto. intros.
elim (eq_dart_dec x z). 
    elim (eq_dart_dec x (cA m zero y_1)). intros. 
        assert (y_1 = cA_1 m zero x).  rewrite a.
             rewrite cA_1_cA. tauto. tauto. 
        unfold y_1. generalize (exd_cA_1 m one y). tauto. 
               rewrite <-H19 in H25. rewrite H18 in H25. tauto. 
   elim (eq_dart_dec y (cA m zero y_1)). intros. 
        assert (y_1=cA_1 m zero y). rewrite a.
            rewrite cA_1_cA. tauto. tauto. 
          unfold y_1. generalize (exd_cA_1 m one y). tauto. 
            rewrite <-H22 in H25. rewrite cA_1_cA in H25. 
              rewrite H25 in H18. tauto. tauto. tauto. 
   tauto. 
elim (eq_dart_dec x (cA m one z)). 
   intros. elim b0. unfold x_1. rewrite a. rewrite cA_1_cA. 
         tauto. tauto. tauto. 
elim (eq_dart_dec y (cA m one z)). 
    intros. elim b1. unfold y_1. rewrite a. rewrite cA_1_cA. 
         tauto. tauto. tauto. 
tauto. tauto. tauto. tauto. 
   generalize (exd_Flip_topo m x x). tauto. 
  generalize (exd_Flip_topo m x y). tauto. 
tauto.
Qed.

(* THEN, OK!! *)

Lemma fpoint_cA_Flip_fpoint_Flip : forall m x z,
 let m6:= Flip m x in
  inv_Triangulation m -> prec_Flip m x -> exd m z ->
      (forall t, exd m t -> fpoint m (cA m one t) = fpoint m t) ->
         fpoint m6 (cA m6 one z) = fpoint m6 z.
Proof.
intros.  rename H2 into Emv. 
 set (x_1 := cA_1 m one x).
  set (y := cA m zero x).
  set (y_1 := cA_1 m one y).
  set (xff := cF m y_1).
  set (yff := cF m x_1).
   set (m1 := Split m one x x_1).
   set (m2 := Split m1 one y y_1). 
   set (m3 := Merge m2 one xff x). 
   set (m4 := Merge m3 one yff y). 
   unfold m6. 
   unfold Flip. 
rename H1 into Ez. 
   assert (inv_Triangulation m). tauto. 
unfold inv_Triangulation in  H1. 
decompose [and] H1. clear H1.
   assert (prec_Flip m x). tauto.
unfold prec_Flip in H1. decompose [and] H1. clear H1.
fold y in H7. fold y in H8.
   assert (exd m y).
generalize (exd_cA m zero x). fold y. tauto.
assert (exd (Flip_topo m x) x). generalize (exd_Flip_topo m x x). tauto.
rename H10 into EFx.
assert (exd (Flip_topo m x) y). generalize (exd_Flip_topo m x y). tauto.
rename H10 into EFy.
  assert (isTri m x). unfold isTriangulation in H6.
apply H6. tauto.
assert (isTri m y). unfold isTriangulation in H6. apply H6. tauto.
  generalize (Tri_diff_face m x H2 H5 H10). 
intro. simpl in H13. 
  generalize (Tri_diff_face m y H2 H1 H12). 
intro Ty. simpl in Ty. 
generalize (Tri_diff_2faces m x y H2 H5 H1 H10 H12 H8). intro. 
   simpl in H14.
  assert (degreee m x = 2).
unfold isMap in H4. apply H4. tauto.
generalize (degreee_invol_nofixpt m x H2 H5). intro.
assert 
(cA m zero x <> x /\ cA m zero (cA m zero x) = x).
tauto.
clear H16. fold y in H17. elim H17. clear H17. intros.
generalize (invol_inverse m zero x H2 H5).
fold y. intro. assert (y = cA_1 m zero x). tauto. clear H18.
assert (y_1=cF m x). unfold cF. rewrite <-H19; fold y_1. tauto.
assert (degreee m y = 2).
unfold isMap in H4. apply H4. tauto.
  generalize (degreee_invol_nofixpt m y H2 H1). intro.
assert 
 (cA m zero y <> y /\ cA m zero (cA m zero y) = y).
tauto.
clear H21. rewrite H17 in H22. elim H22. clear H22. intros.
  generalize (invol_inverse m zero y H2 H1).
rewrite H17. intro. assert (x = cA_1 m zero y). tauto. clear H23.
  assert (x_1=cF m y). 
unfold cF. rewrite <-H24; fold x_1. tauto.
rewrite fpoint_Flip_emb. 
  rewrite fpoint_Flip_topo. rewrite fpoint_Flip_topo.
    rewrite fpoint_Flip_topo.
  unfold Flip_topo. 
  fold y. fold y_1.
fold x_1. fold xff. fold yff.
   fold m1. fold m2. fold m3. fold m4. 
   unfold Flip_emb. rewrite cA_Chp. rewrite cA_Chp.
  unfold m4; unfold m3; unfold m2; unfold m1.
rewrite cA1_Flip_1_4. 
    fold y. fold y_1.
fold x_1. fold xff. fold yff.
(* TRUE BEGIN: *)
rewrite fpoint_Chp. rewrite fpoint_Chp.
rewrite fpoint_Merge. rewrite fpoint_Merge.
rewrite fpoint_Merge. rewrite fpoint_Merge.
rewrite fpoint_Merge. rewrite fpoint_Merge.
rewrite fpoint_Split. rewrite fpoint_Split.
rewrite fpoint_Split. rewrite fpoint_Split.
rewrite fpoint_Split. rewrite fpoint_Split.
rewrite <-H18 in H14, H13. 
rewrite <-H23 in H14, Ty.
fold xff in H13, H14. 
fold yff in Ty, H14. 
elim (eq_dart_dec yff z). 
   elim (eq_dart_dec x y). tauto. 
   elim (eq_dart_dec y y). 
        elim (eq_dart_dec y z). intros. 
            tauto. 
        elim (eq_dart_dec x z). intros. 
       rewrite <-a1 in a. tauto. intros.
         rewrite <-a0. tauto. 
        tauto. 
elim (eq_dart_dec xff z). 
   elim (eq_dart_dec x x). 
       elim (eq_dart_dec y z). intros. rewrite <-a in a1. tauto. 
      elim (eq_dart_dec x z). intros.  rewrite <-a in a1. tauto. 
        intros. rewrite a0; tauto. 
        tauto. 
elim (eq_dart_dec y_1 z). 
   elim (eq_dart_dec x (cA m one y)). 
    intros. 
     assert (y = cF_1 m y). unfold cF_1. rewrite <-a. tauto. 
       assert (y =  cF m y). rewrite H25 at 2. 
          rewrite cF_cF_1. tauto. tauto. tauto. rewrite <-H23 in H26. 
             tauto.
   elim (eq_dart_dec y (cA m one y)). intros. 
      assert (x = cF_1 m y).  unfold cF_1. rewrite <-a. 
             symmetry. tauto. 
                 assert (cF m x = y). rewrite H25. rewrite cF_cF_1. 
                      tauto. tauto. tauto. rewrite <-H18 in H26. tauto.
    intros. 
elim (eq_dart_dec y z). intro. rewrite <-a0 in a. tauto. 
elim (eq_dart_dec x z). intros. rewrite <-a in a0. tauto. 
  intros. rewrite <-a. rewrite Emv. 
     assert (y = cA m one y_1). unfold y_1. 
         rewrite cA_cA_1. tauto. tauto. tauto. rewrite H25. 
          apply Emv. unfold y_1. generalize (exd_cA_1 m one y). tauto. 
            tauto. 
elim ( eq_dart_dec x_1 z). 
    elim (eq_dart_dec x (cA m one x)).
        intros. assert (y = cF_1 m x). unfold cF_1. 
            rewrite <-a. fold y. tauto. 
        assert (cF m y = x). rewrite H25. rewrite cF_cF_1. 
                      tauto. tauto. tauto. rewrite <-H23 in H26. 
                       symmetry in H26. tauto. 
   elim (eq_dart_dec y (cA m one x)). intros. 
       assert (x = cF m x). unfold cF. rewrite <-H19. 
        rewrite a. rewrite cA_1_cA. tauto. tauto. tauto. 
           rewrite <-H18 in H25. tauto. 
elim (eq_dart_dec y z). intros. rewrite <-a0 in a. tauto. 
elim (eq_dart_dec x z). intros. rewrite <-a0 in a. tauto. 
  intros. rewrite <-a. 
          rewrite Emv.  assert (x = cA m one x_1). unfold x_1. 
         rewrite cA_cA_1. tauto. tauto. tauto. rewrite H25. 
          apply Emv. unfold x_1. generalize (exd_cA_1 m one x). tauto. 
            tauto. 
 elim (eq_dart_dec y z). intros. 
     elim (eq_dart_dec x (cA m zero x_1)). 
        intros. 
        assert (x_1=cA_1 m zero x). rewrite a0.
            rewrite cA_1_cA. tauto. tauto. 
          unfold x_1. generalize (exd_cA_1 m one x). tauto. 
            rewrite <-H17 in H25. rewrite cA_1_cA in H25. 
              rewrite H25 in H23. symmetry in H25. tauto. tauto. tauto. 
   elim (eq_dart_dec y (cA m zero x_1)). intros. 
        assert (x_1 = cA_1 m zero y).  rewrite a0.
            rewrite cA_1_cA. tauto. tauto. 
               unfold x_1. generalize (exd_cA_1 m one x). tauto. 
            rewrite <-H24 in  H25. tauto. intros. 
         assert (exd m x_1). generalize (exd_cA_1 m one x). tauto. 
             assert (degreee m x_1 = 2).
               unfold isMap in H4. apply H4. tauto.
             generalize (degreee_invol_nofixpt m x_1 H2 H25). intro.
          assert 
                  (cA m zero x_1 <> x_1 /\ cA m zero (cA m zero x_1) = x_1).
                 tauto.
             clear H27. 
               generalize (invol_inverse m zero x_1 H2 H25). intro. 
                   assert (cA m zero x_1 = cA_1 m zero x_1). tauto. 
                    assert (cA m zero x_1 = cA m one yff). 
                   unfold yff. unfold cF. rewrite cA_cA_1. tauto. 
                 tauto. generalize (exd_cA_1 m zero x_1). tauto. 
                   rewrite H30. apply Emv. unfold yff. 
                   generalize (exd_cF m x_1). tauto. 
  elim (eq_dart_dec x z). 
    elim (eq_dart_dec x (cA m zero y_1)). intros. tauto. 
    elim (eq_dart_dec y (cA m zero y_1)). intros. 
        assert (y_1=cA_1 m zero y). rewrite a.
            rewrite cA_1_cA. tauto. tauto. 
          unfold y_1. generalize (exd_cA_1 m one y). tauto. 
            rewrite <-H22 in H25. rewrite cA_1_cA in H25. 
            symmetry in H25. tauto. tauto. tauto. intros. 
          assert (exd m y_1). generalize (exd_cA_1 m one y). tauto. 
             assert (degreee m y_1 = 2).
               unfold isMap in H4. apply H4. tauto.
             generalize (degreee_invol_nofixpt m y_1 H2 H25). intro.
          assert 
                  (cA m zero y_1 <> y_1 /\ cA m zero (cA m zero y_1) = y_1).
                 tauto.
             clear H27. 
               generalize (invol_inverse m zero y_1 H2 H25). intro. 
                   assert (cA m zero y_1 = cA_1 m zero y_1). tauto. 
                    assert (cA m zero y_1 = cA m one xff). 
                   unfold xff. unfold cF. rewrite cA_cA_1. tauto. 
                 tauto. generalize (exd_cA_1 m zero y_1). tauto. 
                   rewrite H30. apply Emv. unfold xff. 
                   generalize (exd_cF m y_1). tauto. 
 elim (eq_dart_dec x (cA m one z)). 
   intros. elim b1. unfold x_1. rewrite a. rewrite cA_1_cA. 
         tauto. tauto. tauto. 
elim (eq_dart_dec y (cA m one z)). 
    intros. elim b3. unfold y_1. rewrite a. rewrite cA_1_cA. 
         tauto. tauto. tauto. 
intros. 
apply Emv. tauto. 
  unfold Flip_topo in EFx. fold x_1 y y_1 xff yff in EFx. tauto.
  unfold Flip_topo in EFy. fold x_1 y y_1 xff yff in EFy. 
  set (M:= (Merge (Merge (Split (Split m one x x_1) one y y_1) one xff x) one yff y)).  
  generalize (exd_Chp M x (fpoint M xff) y). 
  unfold M. tauto. 
tauto. tauto. tauto. 
apply EFx. apply EFy. tauto. 
Qed.

Theorem isWellembedv_Flip: forall (m:fmap)(x:dart), 
  inv_Triangulation m -> isWellembede m -> isWellembedv m -> 
      exd m x -> prec_Flip_emb m x -> isWellembedv (Flip m x).   
Proof.
  intros. unfold isWellembedv. intros. 
   assert (prec_Flip m x). 
       apply prec_Flip_emb_prec_Flip. 
             tauto. tauto. tauto. tauto. tauto. 
   apply cA1_expv_fpoint. 
    apply inv_hmap_Flip. tauto. tauto. 
        intros. 
    apply fpoint_cA_Flip_fpoint_Flip. 
        tauto. tauto. generalize (exd_Flip m x z0). tauto. 
              intros. 
           assert (expv m t0 (cA m one t0)). 
            unfold expv. unfold MA1.MfcA.expo. 
             split. tauto. split with 1%nat. simpl. tauto. 
             unfold isWellembedv in H1. 
          apply H1. generalize (exd_cA m one t0). 
            unfold inv_Triangulation in H. tauto. 
            apply expv_symm.    unfold inv_Triangulation in H. tauto. tauto. 
        tauto.
Qed.

(*===================================================
               Properties of cF and embedding
====================================================*)

Lemma cw_dart_cF : forall m z, 
   inv_hmap m -> exd m z -> isTri m z ->  
      cw_triangle m z -> cw_triangle m (cF m z).
Proof.
   unfold cw_triangle. intros m0 z Im Ez. intros. 
       unfold isTri in H. assert (MF.degree = degreef). tauto.
   assert (MF.f = cF). tauto. 
   assert (cF m0 (cF m0 (cF m0 z)) = Iter (cF m0) 3 z). 
    simpl. tauto. rewrite <-H in H3. 
     rewrite <-H2 in H3. rewrite <-H1 in H3. 
        rewrite MF.degree_per in H3.  
           rewrite H2 in H3. rewrite H3. 
               apply  ccw_axiom_1.  apply  ccw_axiom_1. tauto. 
            tauto. tauto.
Qed.
               
Lemma ccw_dart_cF : forall m z, 
   inv_hmap m -> exd m z -> isTri m z ->  
      ccw_triangle m z -> ccw_triangle m (cF m z).
Proof.
  unfold ccw_triangle. intros m0 z Im Ez. intros. 
       unfold isTri in H. assert (MF.degree = degreef). tauto.
   assert (MF.f = cF). tauto. 
   assert (cF m0 (cF m0 (cF m0 z)) = Iter (cF m0) 3 z). 
    simpl. tauto. rewrite <-H in H3. 
     rewrite <-H2 in H3. rewrite <-H1 in H3. 
        rewrite MF.degree_per in H3.  
           rewrite H2 in H3. rewrite H3. 
               apply  ccw_axiom_1. tauto. 
            tauto. tauto.
Qed.

(*===================================================
                Faces: cF and embedding
====================================================*)

Section embed_faces.

Variables (m:fmap)(x:dart).

Hypothesis inv_Triangulation_m: inv_Triangulation m.
Hypothesis isWellembed_m: isWellembed m.
Hypothesis prec_Flip_emb_x: prec_Flip_emb m x.
Hypothesis exd_x: exd m x.

Definition x_1:= cA_1 m one x.
Definition y:= cA m zero x.
Definition y_1:= cA_1 m one y.
Definition xff:= cF m y_1.
Definition yff:= cF m x_1.
Definition m1 := Split m one x x_1.
Definition m2 := Split m1 one y y_1. 
Definition m3 := Merge m2 one xff x. 
Definition m4 := Merge m3 one yff y. 

Lemma exd_y: exd m y.
   unfold y. generalize (exd_cA m zero x). 
Proof.
       unfold inv_Triangulation in inv_Triangulation_m. tauto. 
Qed.

Lemma exd_x_1: exd m x_1.
Proof.
   unfold x_1. generalize (exd_cA_1 m one x). 
       unfold inv_Triangulation in inv_Triangulation_m. tauto. 
Qed.

Lemma exd_y_1: exd m y_1.
Proof.
   unfold y_1. generalize (exd_cA_1 m one y). 
       unfold inv_Triangulation in inv_Triangulation_m. 
      generalize exd_y. tauto. 
Qed.

Lemma exd_xff: exd m xff.
Proof.
   unfold xff. generalize (exd_cF m y_1). 
       unfold inv_Triangulation in inv_Triangulation_m. 
      generalize exd_y_1. tauto. 
Qed.

Lemma exd_yff: exd m yff.
Proof.
   unfold yff. generalize (exd_cF m x_1). 
       unfold inv_Triangulation in inv_Triangulation_m. 
      generalize exd_x_1. tauto. 
Qed.

Lemma exd_m1_m4: forall z, 
    exd m z -> exd m1 z /\ exd m2 z /\ exd m3 z /\ exd m4 z.
Proof.
  intro. generalize (exd_Flip_1_4 m x z). intro. 
   elim H. unfold m4, m3, m2, m1.
   unfold xff, yff, x_1, y_1, y. tauto.
Qed.

Lemma isTri_x : isTri m x.
Proof.
   unfold inv_Triangulation in inv_Triangulation_m.
    decompose [and] inv_Triangulation_m.
    unfold isTriangulation in H3. apply H3. 
tauto.
Qed.
  
Lemma isTri_y : isTri m y.
Proof.
  unfold inv_Triangulation in inv_Triangulation_m.
    decompose [and] inv_Triangulation_m.
    unfold isTriangulation in H3. apply H3. 
  apply exd_y. 
Qed.

Lemma inv_hmap_m: inv_hmap m.
Proof. 
   unfold inv_Triangulation in inv_Triangulation_m. tauto.
Qed.

Lemma y_diff_x: y <> x.
Proof. 
  unfold inv_Triangulation in inv_Triangulation_m.
   decompose [and] inv_Triangulation_m. 
   unfold isMap in H1. 
   assert (degreee m x = 2). apply H1. tauto. 
    generalize (degreee_invol_nofixpt m x H exd_x). 
    intro. fold y in H4. tauto.
Qed.

Lemma cA0_y_x: cA m zero y = x.
Proof. 
  unfold inv_Triangulation in inv_Triangulation_m.
   decompose [and] inv_Triangulation_m. 
   unfold isMap in H1. 
   assert (degreee m x = 2). apply H1. tauto. 
    generalize (degreee_invol_nofixpt m x H exd_x). 
    intro. fold y in H4. tauto.
Qed.

Lemma y_cA0_1_x: y = cA_1 m zero x.
Proof.
   unfold inv_Triangulation in inv_Triangulation_m.
   decompose [and] inv_Triangulation_m. 
    assert (cA m zero y = x). apply cA0_y_x.
      generalize (invol_inverse m zero x H exd_x). fold y. 
    tauto.
Qed.

Lemma y_1_cF_x : y_1 = cF m x.
Proof.
   unfold cF. unfold y_1. rewrite <-y_cA0_1_x.
tauto.
Qed.

Lemma cA0_x_y: cA m zero x = y.
Proof. 
  unfold inv_Triangulation in inv_Triangulation_m.
   decompose [and] inv_Triangulation_m. 
   unfold isMap in H1. 
   assert (degreee m y = 2). apply H1. apply exd_y. 
    generalize (degreee_invol_nofixpt m y H exd_y). 
    intro. rewrite cA0_y_x in H4. tauto.
Qed.

Lemma x_cA0_1_y: x = cA_1 m zero y.
Proof.
   unfold inv_Triangulation in inv_Triangulation_m.
   decompose [and] inv_Triangulation_m. 
    assert (cA m zero x = y). apply cA0_x_y.
      generalize (invol_inverse m zero y H exd_y). 
    rewrite cA0_y_x. 
    tauto.
Qed.

Lemma x_1_cF_y : x_1 = cF m y.
Proof.
   unfold cF. unfold x_1. rewrite <-x_cA0_1_y.
tauto.
Qed.
    
Lemma diff_x: x <> y_1 /\ x <> xff /\ y_1 <> xff.
Proof.
     generalize (Tri_diff_face m x inv_hmap_m exd_x isTri_x). 
     intro. simpl in H. unfold yff, xff. rewrite y_1_cF_x. tauto.
Qed.

Lemma diff_y:  y <> x_1 /\ y <> yff /\ x_1 <> yff.
Proof.
     generalize (Tri_diff_face m y inv_hmap_m exd_y isTri_y). 
     intro. simpl in H. unfold yff, xff. rewrite x_1_cF_y. tauto.
Qed.

Lemma prec_Flip_x: prec_Flip m x.
Proof.
  unfold isWellembed in isWellembed_m.
   apply prec_Flip_emb_prec_Flip. tauto. 
  tauto. tauto. tauto. tauto.
Qed.

Lemma not_expv_x_y: ~expv m x y.
Proof.
  generalize  prec_Flip_x. unfold prec_Flip. 
   unfold y. tauto.
Qed.

Lemma not_expf_x_y: ~expf m x y.
Proof.
  generalize  prec_Flip_x. unfold prec_Flip. 
   unfold y. tauto.
Qed.

Lemma diff_2faces_x_y: (x <> y /\ x <> x_1 /\ x <> yff) /\
  (y_1 <> y /\ y_1 <> x_1 /\ y_1 <> yff) /\
  (xff <> y /\ xff <> x_1 /\ xff <> yff).
Proof.
    unfold xff, yff.
    rewrite x_1_cF_y.  rewrite y_1_cF_x. 
   apply Tri_diff_2faces.
  apply inv_hmap_m. apply exd_x. 
apply exd_y. apply isTri_x. apply isTri_y. 
  apply not_expf_x_y. 
Qed.

Lemma inv_hmap_m_m4: 
    inv_hmap m /\ inv_hmap m1 /\ inv_hmap m2  /\ 
     inv_hmap m3 /\ inv_hmap m4.
Proof. 
 unfold inv_Triangulation in inv_Triangulation_m. 
  split. tauto. 
   apply inv_hmap_Flip_1_4. unfold inv_Triangulation. tauto.
    apply prec_Flip_x.
Qed.

Lemma isMap_m_m4:
    isMap m /\ isMap m1 /\ isMap m2  /\ 
     isMap m3 /\ isMap m4.
Proof. 
 unfold inv_Triangulation in inv_Triangulation_m. 
  split. tauto. 
   apply isMap_Flip_1_4. unfold inv_Triangulation. tauto.
    apply prec_Flip_x.
Qed.

Lemma isSubd_m1_m4: isHexa m1 x /\
       isBar m2 x /\ isQuad m2 y_1 /\ isHexa m3 y /\ isTri m4 x /\ isTri m4 y.
Proof.
  apply isSubd_Flip_1_4. tauto. apply prec_Flip_emb_prec_Flip. 
   tauto. unfold isWellembed in  isWellembed_m. tauto. 
    unfold isWellembed in  isWellembed_m. tauto. 
   tauto. tauto.
Qed.
 
Lemma degreev_m1_x: degreev m1 x = 1.
Proof.
  unfold m1, x_1.
rewrite (degreev_Flip1 m x x inv_hmap_m).  
   elim (eq_dart_dec x x). tauto. tauto. 
    apply exd_x. apply exd_x. 
    unfold  inv_Triangulation in inv_Triangulation_m. 
    unfold isPoly in  inv_Triangulation_m. 
   decompose [and]  inv_Triangulation_m. 
     apply H0. apply exd_x. 
Qed.

Lemma degreev_m1_y: 2 <= degreev m1 y.
Proof.
  unfold m1, x_1. 
rewrite (degreev_Flip1 m x y inv_hmap_m).  
   elim (eq_dart_dec x y). intro. 
       generalize y_diff_x. symmetry in a. tauto. 
   fold x_1. 
   elim (expv_dec m x_1 y inv_hmap_m). 
    intros. generalize prec_Flip_x. 
    unfold prec_Flip. intros. lia. 
      intros. generalize prec_Flip_x. 
    unfold prec_Flip. unfold y. intros. lia. 
     apply exd_x. apply exd_y. 
    unfold  inv_Triangulation in inv_Triangulation_m. 
    unfold isPoly in  inv_Triangulation_m. 
   decompose [and]  inv_Triangulation_m. 
     apply H0. apply exd_x. 
Qed.

Lemma y_1_y_1_m1: y_1 = cA_1 m1 one y.
Proof. 
  unfold m1. rewrite cA1_1_Flip1. 
   elim (eq_dart_dec (cA m one x) y). 
   intro. generalize not_expv_x_y. intro. 
   elim H. apply expv_trans with (cA m one x). 
   unfold MA1.MfcA.expo. split. tauto. 
     split with 1%nat. simpl. tauto. rewrite a. 
         apply MA1.MfcA.expo_refl. apply exd_y. 
    elim (eq_dart_dec x y). generalize y_diff_x. 
      intros. symmetry in a. tauto. unfold y_1. tauto. 
    apply inv_hmap_m. 
    unfold  inv_Triangulation in inv_Triangulation_m. 
    unfold isPoly in  inv_Triangulation_m. 
  decompose [and]  inv_Triangulation_m. 
  apply H0. apply exd_x. apply exd_x. apply exd_y. 
Qed.
   
Lemma cF_m1: 
 cF m1 y = x /\
 cF m1 x = y_1 /\
 cF m1 y_1 = xff /\ 
 cF m1 xff = x_1 /\ 
 cF m1 x_1 = yff /\ 
 cF m1 yff = y.
Proof. 
  unfold inv_Triangulation in inv_Triangulation_m.
   decompose [and] inv_Triangulation_m.
   apply cF_Flip1_detail_1.
     tauto. tauto. tauto. unfold isPoly in H0. 
          apply H0. tauto. 
          fold y. unfold isPoly in H0. 
          apply H0. apply exd_y. 
          fold y.  apply not_expv_x_y. 
             fold y.  apply not_expf_x_y. 
        apply isTri_x. fold y. apply isTri_y. 
Qed.

Definition x_f := cF_1 m x.

Lemma xff_x_f: xff = x_f.
Proof.
   unfold xff, x_f. rewrite y_1_cF_x.  
   generalize isTri_x. unfold isTri. intro. 
   assert (Iter (cF m) 2 x = cF m (cF m x)). simpl. tauto. 
    rewrite <-H0. 
   assert (2 = 3 - 1). lia. rewrite H1. rewrite <-H. 
    assert (cF = MF.f). tauto. rewrite H2. 
   rewrite <- MF.Iter_f_f_1. 
    assert (degreef = MF.degree). tauto. 
    rewrite H3. rewrite MF.degree_per. simpl. tauto. 
    apply inv_hmap_m. tauto.  apply inv_hmap_m. tauto. lia.
Qed.

Lemma cFm1_z: forall z, exd m z ->
    y <> z -> xff <> z -> cF m1 z = cF m z.
Proof. 
  unfold inv_Triangulation in inv_Triangulation_m.
   decompose [and] inv_Triangulation_m.
   unfold m1. intros. 
   rewrite cF_Flip1. fold x_f. rewrite <-xff_x_f. fold y. 
   elim (eq_dart_dec xff z). tauto. 
   elim (eq_dart_dec y z). tauto. 
     tauto. apply inv_hmap_m. 
   unfold isPoly in H0. 
          apply H0. tauto. tauto. tauto. 
Qed.
   
Lemma cF_m2:
   x = cF m2 y /\
   y = cF m2 x /\
   y_1 = cF m2 yff /\
   xff = cF m2 y_1 /\ 
   x_1 = cF m2 xff /\ 
   yff = cF m2 x_1.
Proof.
  unfold inv_Triangulation in inv_Triangulation_m.
   decompose [and] inv_Triangulation_m.
  generalize cF_m1. 
   intro. decompose [and] H2. 
   generalize inv_hmap_m_m4. intro. 
  generalize isMap_m_m4. intro. 
 generalize (exd_m1_m4 x exd_x). intro. 
generalize (exd_m1_m4 y exd_y). intro. 
 generalize (cF_Flip2_detail_1 m1 y). intro.
   simpl in H14. 
   assert (inv_hmap m1). tauto. 
   assert ( isMap m1). tauto. 
    assert ( exd m1 y). tauto. 
    assert ( isHexa m1 x). 
   generalize isSubd_m1_m4. tauto. 
   assert (degreev m1 x = 1). 
     apply degreev_m1_x. 
   assert (2 <= degreev m1 y). apply degreev_m1_y. 
    rewrite H4 in H14. rewrite H6 in H14. fold m2 in H14. 
  decompose [and] (H14 H15 H16 H17 H18 H19 H20). clear H14. 
    split. tauto.  split. tauto. 
    split. rewrite H22. rewrite H5. rewrite H7. 
    rewrite H8. tauto. 
      split. rewrite H5 in H24. tauto. 
      split. rewrite H5 in H25. rewrite H7 in H25. tauto. 
      rewrite H5 in H27. rewrite H7 in H27. rewrite H8 in H27. 
      tauto.
Qed.

Lemma cFm2_z: forall z, exd m z ->
    yff <> z -> x <> z -> cF m2 z = cF m1 z.
Proof. 
  intros. 
  generalize inv_hmap_m_m4. intro. 
 generalize (exd_m1_m4 x exd_x). intro. 
generalize (exd_m1_m4 y exd_y). intro.
generalize (exd_m1_m4 z H). intro.
   assert (inv_hmap m1). tauto. 
 assert (exd m1 y). tauto. 
assert (exd m1 z). tauto. 
generalize (cF_m1). intro. 
   decompose [and] H9. 
  generalize (cF_Flip2 m1 y z H6 H7 H8 degreev_m1_y).
    rewrite <- y_1_y_1_m1. 
   assert (cF_1 m1 y = yff). rewrite <-H16. 
    rewrite cF_1_cF. tauto. tauto. 
   assert (exd m yff). unfold yff. generalize (exd_cF m x_1).
    generalize (exd_cA_1 m one x). fold x_1. tauto. 
   generalize (exd_m1_m4 yff H15). tauto.
    rewrite H15. 
   assert (cA m1 zero y = x). 
   unfold m1. rewrite cA0_Flip1. 
     apply cA0_y_x. apply inv_hmap_m. tauto. 
      apply exd_y. 
   rewrite H17. fold m2. 
  elim (eq_dart_dec yff z). tauto. 
  elim (eq_dart_dec x z). tauto.
tauto. 
Qed.
 
Lemma cF_m3: 
     y = cF m3 x /\
    xff = cF m3 y /\
    x_1 = cF m3 xff /\ 
   yff = cF m3 x_1 /\ 
   y_1 = cF m3 yff /\ 
     x = cF m3 y_1.
Proof.
   unfold inv_Triangulation in inv_Triangulation_m.
   decompose [and] inv_Triangulation_m.
  generalize cF_m2. 
   intro. decompose [and] H2. 
   generalize inv_hmap_m_m4. intro. 
 generalize isMap_m_m4. intro isM. 
 generalize (exd_m1_m4 x exd_x). intro. 
  assert (exd m xff). 
  unfold xff. generalize (exd_cF m y_1). 
   generalize (exd_cA_1 m one y).
   generalize (exd_y).  fold y_1. tauto. 
generalize (exd_m1_m4 xff H12). intro. 
 generalize isSubd_m1_m4. intro. 
  decompose [and] H14. clear H14. 
    assert (isQuad m2 xff). 
     unfold isQuad. 
     unfold isQuad in H16. 
     assert (degreef = MF.degree). tauto. rewrite H14. 
     rewrite (MF.expo_degree m2 xff y_1). tauto. tauto. 
        apply MF.expo_symm. tauto. 
     rewrite H7. unfold MF.expo. split. 
   assert (exd m y_1).  generalize (exd_cA_1 m one y).
   generalize (exd_y).  fold y_1. tauto. 
   generalize (exd_m1_m4 y_1 H20). tauto. 
         split with 1%nat. simpl. tauto. 
assert (exd m2 x). tauto.
assert (exd m2 xff). tauto. 
assert (inv_hmap m2). tauto. 
assert (isMap m2). tauto. 
  generalize (cF_Flip3_detail_1 m2 xff x H23 H24 H17 H14 H20 H22). 
intro. cbv zeta in H25. fold m3 in H25. 
  generalize cF_m2. intro. decompose [and] H26. clear H26. 
    rewrite <-H29 in H25. rewrite <-H31 in H25. rewrite <-H33 in H25. 
        rewrite <-H28 in H25. apply H25. 
Qed.
  
Lemma cFm3_z: forall z, exd m z ->
    y <> z -> y_1 <> z -> cF m3 z = cF m2 z.
Proof.
   unfold inv_Triangulation in inv_Triangulation_m.
   decompose [and] inv_Triangulation_m.
   generalize inv_hmap_m_m4. intro. 
 generalize (exd_m1_m4 x exd_x). intro. 
  assert (exd m xff). 
  unfold xff. generalize (exd_cF m y_1). 
   generalize (exd_cA_1 m one y).
   generalize (exd_y).  fold y_1. tauto. 
generalize (exd_m1_m4 xff H5). intros. 
generalize (exd_m1_m4 z H7). intro. 
 assert (cA m2 one x = x). 
    unfold m2. rewrite y_1_y_1_m1.  
     rewrite cA1_Flip2. 
    elim ( eq_dart_dec y x). tauto. 
    rewrite <-y_1_y_1_m1.
    elim (eq_dart_dec y_1 x). intros. 
    generalize diff_x. symmetry in a. tauto. 
     unfold m1. rewrite cA1_Flip1. elim (eq_dart_dec x x). tauto. tauto. 
   tauto. unfold isPoly in H0. apply H0. tauto. tauto. tauto. tauto. 
      generalize (exd_m1_m4 y exd_y). tauto. tauto. 
     apply degreev_m1_y. 
  assert (cA m2 zero x = y). 
    unfold m2. rewrite y_1_y_1_m1. rewrite cA0_Flip2. 
  unfold m1. rewrite cA0_Flip1. apply cA0_x_y. tauto. tauto. tauto. 
      tauto. generalize (exd_m1_m4 y exd_y). tauto. tauto. 
    unfold m3. rewrite cF_Flip3. 
   rewrite H12. 
   elim (eq_dart_dec y z). tauto. 
  generalize (cF_m2). intro. decompose [and] H13. clear H13. 
     rewrite H17. rewrite cF_1_cF. 
     elim (eq_dart_dec y_1 z). tauto. tauto.
tauto. 
   assert (exd m y_1). generalize (exd_cA_1 m one y). fold y_1.
    generalize exd_y. tauto. 
   generalize (exd_m1_m4 y_1 H13). tauto. 
  tauto. tauto.   tauto. tauto.  
 generalize (exd_m1_m4 z H7). tauto. 
Qed.

Lemma cF_m4:
   xff = cF m4 y /\
  x_1 = cF m4 xff /\
    y = cF m4 x_1 /\ 
  yff = cF m4 x /\ 
  y_1 = cF m4 yff /\ 
    x = cF m4 y_1.
Proof.
 unfold inv_Triangulation in inv_Triangulation_m.
   decompose [and] inv_Triangulation_m.
 generalize cF_m3. 
   intro. decompose [and] H2. 
 generalize inv_hmap_m_m4. intro. 
 generalize isMap_m_m4. intro isM. 
 generalize (exd_m1_m4 x exd_x). intro. 
generalize (exd_m1_m4 y exd_y). intro Ey. 
 assert (exd m yff). 
  unfold yff. generalize (exd_cF m x_1). 
   generalize (exd_cA_1 m one x).  fold x_1. tauto. 
 assert (exd m xff). 
  unfold xff. generalize (exd_cF m y_1). 
   generalize (exd_cA_1 m one y).
   generalize (exd_y).  fold y_1. tauto. 
 rename H13 into Exff. 
generalize (exd_m1_m4 xff Exff). intro Exff_m1_m4. 
generalize (exd_m1_m4 yff H12). intro. 
 generalize isSubd_m1_m4. intro. 
decompose [and] H14. clear H14. 
clear H2. 
generalize diff_2faces_x_y. intro D2.
  assert (cF = MF.f). tauto. rename H2 into cF_f. 
 assert (degreef = MF.degree). tauto.
assert (isHexa m3 yff). 
     unfold isHexa. 
     unfold isHexa in H18. rewrite H2. 
     rewrite (MF.expo_degree m3 yff y). tauto. tauto. 
        apply MF.expo_symm. tauto. 
     rewrite H7. rewrite H5. rewrite H6. 
     unfold MF.expo. split. tauto. 
    split with 3. unfold Iter; fold Iter. tauto. 
assert (cA m2 one x = x). 
    unfold m2. rewrite y_1_y_1_m1.  
     rewrite cA1_Flip2. 
    elim ( eq_dart_dec y x). tauto. 
    rewrite <-y_1_y_1_m1.
    elim (eq_dart_dec y_1 x). intros. 
    generalize diff_x. symmetry in a. tauto. 
     unfold m1. rewrite cA1_Flip1. elim (eq_dart_dec x x). tauto. tauto. 
     tauto. unfold isPoly in H0. 
     apply H0. tauto. tauto. tauto. tauto. tauto. tauto. 
     apply degreev_m1_y. rename H20 into cAm2x. 
  assert (cA m3 one y = y). 
  unfold m3. 
   rewrite cA1_Flip3. 
    elim (eq_dart_dec xff y). tauto. 
  elim (eq_dart_dec x y). tauto. 
   intros. unfold m2. rewrite y_1_y_1_m1. 
   rewrite cA1_Flip2. 
   elim (eq_dart_dec y y). tauto. tauto. 
     tauto. tauto. tauto. apply degreev_m1_y. 
          tauto. tauto. tauto. apply cAm2x. tauto. 
   assert (  yff = Iter (cF m3) 4 x). 
    rewrite H7. rewrite H5. rewrite H6. rewrite H4. unfold Iter; fold Iter. tauto. 
    assert (inv_hmap m3). tauto. 
     assert (isMap m3). tauto. 
    assert (exd m3 y). tauto.   assert (exd m3 yff). tauto. 
assert (cF_1 m3 y = x). rewrite H4. rewrite cF_1_cF. tauto. tauto. tauto. 
   rewrite <-H27 in H22. 
    generalize (cF_Flip4_detail_1 m3 yff y H23 H24 H25 H26 H14 H20 H22). 
     fold m4. 
     rewrite <-H6. rewrite <-H5. rewrite H27. rewrite <-H8. tauto. 
Qed.

Lemma cFm4_z: forall z, exd m z ->
    x <> z -> x_1 <> z -> cF m4 z = cF m3 z.
Proof.
  unfold inv_Triangulation in inv_Triangulation_m.
   decompose [and] inv_Triangulation_m.
 generalize cF_m3. 
   intro. decompose [and] H2. 
 generalize inv_hmap_m_m4. intro. 
 generalize isMap_m_m4. intro isM. 
 generalize (exd_m1_m4 x exd_x). intro. 
generalize (exd_m1_m4 y exd_y). intro Ey. 
 assert (exd m yff). 
  unfold yff. generalize (exd_cF m x_1). 
   generalize (exd_cA_1 m one x).  fold x_1. tauto. 
 assert (exd m xff). 
  unfold xff. generalize (exd_cF m y_1). 
   generalize (exd_cA_1 m one y).
   generalize (exd_y).  fold y_1. tauto. 
 rename H13 into Exff. 
generalize (exd_m1_m4 xff Exff). intro Exff_m1_m4. 
generalize (exd_m1_m4 yff H12). intro. 
 generalize isSubd_m1_m4. intro. 
decompose [and] H14. clear H14. 
clear H2. 
generalize diff_2faces_x_y. intro D2.
  assert (cF = MF.f). tauto. rename H2 into cF_f. 
 assert (degreef = MF.degree). tauto.
assert (isHexa m3 yff). 
     unfold isHexa. 
     unfold isHexa in H18. rewrite H2. 
     rewrite (MF.expo_degree m3 yff y). tauto. tauto. 
        apply MF.expo_symm. tauto. 
     rewrite H7. rewrite H5. rewrite H6. 
     unfold MF.expo. split. tauto. 
    split with 3. unfold Iter; fold Iter. tauto. 
assert (cA m2 one x = x). 
    unfold m2. rewrite y_1_y_1_m1.  
     rewrite cA1_Flip2. 
    elim ( eq_dart_dec y x). tauto. 
    rewrite <-y_1_y_1_m1.
    elim (eq_dart_dec y_1 x). intros. 
    generalize diff_x. symmetry in a. tauto. 
     unfold m1. rewrite cA1_Flip1. elim (eq_dart_dec x x). tauto. tauto. 
     tauto. unfold isPoly in H0. 
     apply H0. tauto. tauto. tauto. tauto. tauto. tauto. 
     apply degreev_m1_y. rename H20 into cAm2x. 
  assert (cA m3 one y = y). 
  unfold m3. 
   rewrite cA1_Flip3. 
    elim (eq_dart_dec xff y). tauto. 
  elim (eq_dart_dec x y). tauto. 
   intros. unfold m2. rewrite y_1_y_1_m1. 
   rewrite cA1_Flip2. 
   elim (eq_dart_dec y y). tauto. tauto. 
     tauto. tauto. tauto. apply degreev_m1_y. 
          tauto. tauto. tauto. apply cAm2x. tauto. 
   assert (  yff = Iter (cF m3) 4 x). 
    rewrite H7. rewrite H5. rewrite H6. rewrite H4. unfold Iter; fold Iter. tauto. 
    assert (inv_hmap m3). tauto. 
     assert (isMap m3). tauto. 
    assert (exd m3 y). tauto.   assert (exd m3 yff). tauto. 
assert (cF_1 m3 y = x). rewrite H4. rewrite cF_1_cF. tauto. tauto. tauto. 
   rewrite <-H27 in H22. 
   intros. 
generalize (exd_m1_m4 z H28). intro. 
  unfold m4. rewrite cF_Flip4. 
    assert (cA m3 zero y = x). 
   unfold m3. rewrite cA0_Flip3. 
   unfold m2. rewrite y_1_y_1_m1. rewrite cA0_Flip2. 
   unfold m1. unfold x_1. rewrite cA0_Flip1. 
    apply cA0_y_x. tauto. tauto. apply exd_y. 
       tauto. tauto. tauto. tauto. tauto. tauto. tauto. 
     rewrite H32. 
    assert (cF_1 m3 yff = x_1). 
     rewrite H7. rewrite cF_1_cF. tauto. tauto. 
   assert (exd m x_1). unfold x_1. 
      generalize (exd_cA_1 m one x). fold x_1. tauto. 
       generalize (exd_m1_m4 x_1 H33). tauto.
   rewrite H33. 
   elim (eq_dart_dec x z). tauto. 
   elim (eq_dart_dec x_1 z). tauto. tauto.
  tauto. tauto. tauto. 
   apply H20. tauto. 
Qed.

Lemma cFm4_z_bis: forall z, exd m z ->
  y <> z -> xff <> z ->  yff <> z -> x <> z -> y_1 <> z -> x_1 <> z -> 
     cF m4 z = cF m z.
Proof.
  intros. 
   rewrite cFm4_z. rewrite cFm3_z.  rewrite cFm2_z. rewrite cFm1_z.
   tauto. tauto. tauto. tauto.  tauto. tauto. tauto. tauto.  
    tauto. tauto. tauto. tauto. tauto.
Qed.

Lemma Flip_topo_m4: Flip_topo m x = m4.
Proof. 
    unfold Flip_topo.
  unfold m4. unfold m3. unfold m2. unfold m1.
  unfold xff. unfold yff. unfold x_1. unfold y_1. unfold y. 
  tauto. 
Qed.

Theorem cF_Flip_topo: 
let m':= Flip_topo m x in
   xff = cF m' y /\
  x_1 = cF m' xff /\
    y = cF m' x_1 /\ 
  yff = cF m' x /\ 
  y_1 = cF m' yff /\ 
    x = cF m' y_1.
Proof.
 intros. unfold m'. rewrite Flip_topo_m4. 
  apply cF_m4. 
Qed.

Theorem cF_Flip_topo_z: forall z, exd m z ->
  y <> z -> xff <> z ->  yff <> z -> x <> z -> y_1 <> z -> x_1 <> z -> 
     cF (Flip_topo m x) z = cF m z.
Proof. 
   intros. rewrite Flip_topo_m4. 
  apply cFm4_z_bis.  
   tauto.  tauto.  tauto.  tauto.  tauto.  tauto.  tauto.  
Qed.

Theorem cF_Flip: 
let m':= Flip m x in
   xff = cF m' y /\
  x_1 = cF m' xff /\
    y = cF m' x_1 /\ 
  yff = cF m' x /\ 
  y_1 = cF m' yff /\ 
    x = cF m' y_1.
Proof.
 intros. unfold m'. unfold Flip. 
   fold y. fold x_1. fold y_1. fold xff. fold yff.
  unfold Flip_emb. 
   do 12 rewrite cF_Chp. 
  apply cF_Flip_topo.
Qed.

Theorem cF_Flip_z: forall z, exd m z ->
  y <> z -> xff <> z ->  yff <> z -> x <> z -> y_1 <> z -> x_1 <> z -> 
     cF (Flip m x) z = cF m z.
Proof. 
  intros. unfold Flip. 
   fold y. fold x_1. fold y_1. fold xff. fold yff.
  unfold Flip_emb. 
   do 2 rewrite cF_Chp. 
  apply cF_Flip_topo_z. 
 tauto. tauto. tauto. tauto. tauto. tauto. tauto. 
Qed.

Lemma diff_z : forall z, exd m z -> cw_triangle m z ->
   y <> z /\ xff <> z /\ yff <> z /\ x <> z /\ y_1 <> z /\ x_1 <> z.
Proof.
  unfold prec_Flip_emb in prec_Flip_emb_x. 
   fold y in prec_Flip_emb_x. 
    decompose [and] prec_Flip_emb_x. clear prec_Flip_emb_x.  
      rename H3 into C3. 
      rewrite <-x_1_cF_y in H1. rewrite <-y_1_cF_x in H. 
  intros z Ez Cz.
  fold xff in H. fold yff in H1.  
     unfold  isWellembed in  isWellembed_m. 
    decompose [and]  isWellembed_m. 
     unfold isWellembedf in H6. 
      decompose [and] H6. clear H6. 
     assert (~ccw_triangle m z). 
     generalize (cw_ccw_triangle m z). tauto. 
   unfold isWellembedv in H3. 
   assert (exd m x_1). 
     generalize (exd_cA_1 m one x). fold x_1.
            generalize inv_hmap_m. tauto. 
    assert (exd m y_1). 
     generalize (exd_cA_1 m one y). fold y_1.
              generalize exd_y. generalize inv_hmap_m. tauto. 
    assert (fpoint m y_1 = fpoint m y).
         apply H3. tauto. unfold expv. unfold  MA1.MfcA.expo.
           split. tauto. split with 1. simpl. unfold y_1. 
                assert (MA1.MfcA.f m (cA_1 m one y) = cA m one (cA_1 m one y)). 
                 tauto. rewrite H10. rewrite cA_cA_1. tauto. apply inv_hmap_m. 
                  apply exd_y.
   assert (fpoint m x_1 = fpoint m x).
         apply H3. tauto. unfold expv. unfold  MA1.MfcA.expo.
           split. tauto. split with 1. simpl. unfold x_1. 
                assert (MA1.MfcA.f m (cA_1 m one x) = cA m one (cA_1 m one x)). 
                 tauto. rewrite H11. rewrite cA_cA_1. tauto. apply inv_hmap_m. 
                  apply exd_x.
    rewrite <-H11 in H1. unfold yff in H1. rewrite x_1_cF_y in H1.
    rewrite <-H10 in H. unfold xff in H. rewrite y_1_cF_x in H.
      unfold yff. rewrite x_1_cF_y.
          unfold xff. rewrite y_1_cF_x. 
    unfold ccw_triangle in H6. 
     unfold inv_Triangulation in inv_Triangulation_m. 
         decompose [and] inv_Triangulation_m. 
            unfold isTriangulation in H16.
  assert (degreef = MF.degree). tauto. 
          assert (MF.f = cF). tauto. 
       generalize isTri_x. intro. 
            assert (cF m (cF m (cF m x)) = x). 
          unfold isTri in H18. 
     assert (Iter (cF m) 3 x = cF m (cF m (cF m x))). simpl. tauto. 
       rewrite <-H19. rewrite <-H18. rewrite <-H17. rewrite H15.
         rewrite MF.degree_per. tauto. tauto. tauto. 
  generalize isTri_y. intro. 
            assert (cF m (cF m (cF m y)) = y). 
          unfold isTri in H20. 
     assert (Iter (cF m) 3 y = cF m (cF m (cF m y))). simpl. tauto. 
       rewrite <-H21. rewrite <-H20. rewrite <-H17. rewrite H15.
         rewrite MF.degree_per. tauto. tauto. apply exd_y. 
(* TRUE BEGIN: *)
split. intro. rewrite H22 in H1. tauto. 
split. intro. rewrite <-H22 in H6. 
   rewrite H19 in H6. 
    elim H6. apply ccw_axiom_1. apply ccw_axiom_1. tauto. 
split. intro. rewrite <-H22 in H6. 
   rewrite H21 in H6. 
    elim H6. apply ccw_axiom_1. apply ccw_axiom_1. tauto. 
split. intro. rewrite H22 in H. tauto. 
split. intro. rewrite <-H22 in H6.  rewrite H19 in H6. 
     elim H6. apply ccw_axiom_1. tauto.
intro. rewrite <-H22 in H6.  rewrite H21 in H6. 
     elim H6. apply ccw_axiom_1. tauto.
Qed.

Lemma diff_1 : 
  let z:= 1 in 
   y <> z /\ xff <> z /\ yff <> z /\ x <> z /\ y_1 <> z /\ x_1 <> z.
Proof.
   simpl. unfold isWellembed in isWellembed_m.
    unfold isWellembedf in isWellembed_m.
   decompose [and] isWellembed_m.
     apply diff_z. tauto. tauto.
Qed.

Lemma diff_cF_1 : 
  let z:= cF m 1 in 
   y <> z /\ xff <> z /\ yff <> z /\ x <> z /\ y_1 <> z /\ x_1 <> z.
Proof.
    simpl. unfold isWellembed in isWellembed_m.
    unfold isWellembedf in isWellembed_m.
   decompose [and] isWellembed_m. 
unfold inv_Triangulation in inv_Triangulation_m. 
   decompose [and] inv_Triangulation_m. 
    assert ( cw_triangle m (cF m 1)). 
   apply cw_dart_cF. tauto. tauto. 
    unfold isTriangulation in H8. 
   apply H8. tauto. tauto. 
    apply diff_z. generalize (exd_cF m 1). tauto. tauto.
Qed.

Lemma diff_cF_cF_1 : 
  let z:= cF m (cF m 1) in 
   y <> z /\ xff <> z /\ yff <> z /\ x <> z /\ y_1 <> z /\ x_1 <> z.
Proof.
    simpl. unfold isWellembed in isWellembed_m.
    unfold isWellembedf in isWellembed_m.
   decompose [and] isWellembed_m. 
unfold inv_Triangulation in inv_Triangulation_m. 
   decompose [and] inv_Triangulation_m. 
    assert ( cw_triangle m (cF m 1)). 
   apply cw_dart_cF. tauto. 
    unfold isTriangulation in H8. tauto. 
   apply H8. tauto. tauto. 
   assert ( cw_triangle m (cF m (cF m 1))). 
   apply cw_dart_cF. tauto. generalize (exd_cF m 1). tauto.
    unfold isTriangulation in H8. 
   apply H8. generalize (exd_cF m 1). tauto. tauto.
    apply diff_z. generalize (exd_cF m 1). 
      generalize (exd_cF m (cF m 1)). tauto. tauto.
Qed.

Lemma cF_Flip_1: cF (Flip m x) 1 = cF m 1.
Proof. 
  unfold isWellembed in isWellembed_m. 
  generalize diff_1. intro. simpl in H. 
  rewrite cF_Flip_z. tauto. 
    tauto. tauto. tauto. tauto. tauto. tauto. tauto.
Qed.

Lemma cF_Flip_cF_1: cF (Flip m x) (cF m 1) = cF m (cF m 1).
Proof. 
  unfold isWellembed in isWellembed_m. 
  generalize diff_cF_1. intro. simpl in H. 
  rewrite cF_Flip_z. tauto. 
    generalize (exd_cF m 1). generalize inv_hmap_m. tauto. 
    tauto. tauto. tauto. tauto. tauto. tauto. 
Qed.

Lemma cF_Flip_cF_cF_1: cF (Flip m x) (cF m (cF m 1)) = 1.
Proof. 
  unfold isWellembed in isWellembed_m. 
  generalize diff_cF_cF_1. intro. simpl in H. 
   unfold isWellembedf in isWellembed_m. 
 unfold inv_Triangulation in inv_Triangulation_m. 
   decompose [and] inv_Triangulation_m. 
   unfold isTriangulation in H4.
   assert (isTri m 1). apply H4. tauto. 
   unfold isTri in H3. 
    assert (degreef = MF.degree). tauto. 
          assert (MF.f = cF). tauto. 
       assert (cF m (cF m (cF m 1)) = 1). 
     assert (Iter (cF m) 3 1 = cF m (cF m (cF m 1))). simpl. tauto. 
       rewrite <-H7. rewrite <-H3. rewrite H5. rewrite <-H6.
         rewrite MF.degree_per. tauto. tauto. tauto. 
 rewrite cF_Flip_z. tauto. 
   assert (exd m (cF m 1)). 
    generalize (exd_cF m 1). tauto. 
     generalize (exd_cF m (cF m 1)). tauto. 
    tauto. tauto. tauto. tauto. tauto. tauto. 
Qed.

Lemma fpoint_Flip_1: fpoint (Flip m x) 1 = fpoint m 1.
Proof.
  unfold  inv_Triangulation in  inv_Triangulation_m.
  decompose [and]  inv_Triangulation_m. 
   generalize diff_1. intro. simpl in H2. 
  rewrite fpoint_Flip. 
   elim (eq_dart_dec x 1). tauto. 
   fold y. elim (eq_dart_dec y 1). tauto. tauto.
    tauto. tauto. tauto. fold y. 
   generalize y_diff_x. intro. intro. 
         symmetry in H5. tauto. 
Qed.
 
Lemma fpoint_Flip_cF_1:
    fpoint (Flip m x) (cF m 1) = fpoint m (cF m 1).
Proof.
  unfold  inv_Triangulation in  inv_Triangulation_m.
  decompose [and]  inv_Triangulation_m. 
   generalize diff_cF_1. intro. simpl in H2. 
  rewrite fpoint_Flip. 
   elim (eq_dart_dec x (cF m 1)). tauto. 
   fold y. elim (eq_dart_dec y (cF m 1)). tauto. tauto.
    tauto. tauto. tauto. fold y. 
   generalize y_diff_x. intro. intro. 
         symmetry in H5. tauto. 
Qed.

Lemma fpoint_Flip_cF_cF_1:
    fpoint (Flip m x) (cF m (cF m 1)) = fpoint m (cF m (cF m 1)).
Proof.
  unfold  inv_Triangulation in  inv_Triangulation_m.
  decompose [and]  inv_Triangulation_m. 
   generalize diff_cF_cF_1. intro. simpl in H2. 
   generalize diff_cF_1. intro. simpl in H4. 
  rewrite fpoint_Flip. 
   elim (eq_dart_dec x (cF m (cF m 1))). tauto. 
   fold y. elim (eq_dart_dec y (cF m(cF m 1))). tauto. 
   elim (eq_dart_dec x (cF m (cF m 1))). tauto.
    tauto. 
    tauto. tauto. tauto. fold y. 
   generalize y_diff_x. intro. intro. 
         symmetry in H6.  tauto. 
Qed.

Lemma cw_Flip_1: cw_triangle (Flip m x) 1.
Proof.
   unfold cw_triangle. 
   rewrite fpoint_Flip_1.
   rewrite cF_Flip_1. rewrite fpoint_Flip_cF_1.
   rewrite cF_Flip_cF_1. rewrite fpoint_Flip_cF_cF_1.
  unfold isWellembed in isWellembed_m. 
   decompose [and] isWellembed_m. 
  unfold  inv_Triangulation in  inv_Triangulation_m.
  decompose [and]  inv_Triangulation_m. 
   unfold isWellembedf in H3. 
   decompose [and] H3. 
   unfold cw_triangle in H6. tauto.
Qed.

Lemma isTri_expf_eq: forall m z t,
  inv_hmap m -> exd m z -> isTri m z -> 
    (expf m z t <-> z = t \/ cF m z = t \/ cF m (cF m z) = t).
Proof.
  intros. 
   assert (cF = MF.f). tauto. assert (degreef = MF.degree). tauto.
   unfold isTri in H1. unfold expf. 
split. intros. assert (MF.expo2 m0 z t). 
   generalize (MF.expo_expo2 m0 z t). tauto. 
     unfold MF.expo2 in H5. 
       elim H5. clear H5. intros i Hi. 
         decompose [and] Hi. 
            elim Hi. clear Hi. intros j Hj. 
                decompose [and] Hj. clear Hj. 
rewrite <-H2 in H6. rewrite <-H3 in H5. rewrite H1 in H5. 
elim (Nat.eq_dec j 0). intro. rewrite a in H6. simpl in H6. tauto. 
elim (Nat.eq_dec j 1). intro. rewrite a in H6. simpl in H6. tauto. 
intros. assert (j = 2). lia. rewrite H7 in H6. simpl in H6. tauto.  
intro. 
split. tauto. 
elim H4. clear H4. intro. rewrite <-H4. apply MF.expo_refl. tauto. 
clear H4. intro. elim H4. clear H4. intro. 
    unfold MF.expo. split. tauto. split with 1. simpl. tauto. 
intro. 
    unfold MF.expo. split. tauto. split with 2. simpl. tauto. 
Qed.
   
Lemma expf_1: forall m z,
  inv_hmap m -> exd m 1-> isTri m 1 -> 
   (expf m 1 z <-> (1 = z \/ cF m 1 = z \/ cF m (cF m 1) = z)).
Proof.
  intros. 
    apply isTri_expf_eq. tauto. tauto. tauto. 
Qed.

Lemma ccw_triangle_x: ccw_triangle (Flip m x) x.
Proof.
(* TODO : This proof must be cleaned up, because hypothese names aren't stable
  as detected when porting from 8.2 to 8.5. *)
generalize diff_x. 
generalize diff_y. 
generalize diff_2faces_x_y.
generalize cF_Flip. 
    unfold prec_Flip_emb in prec_Flip_emb_x. 
     fold y x_1 y_1 in prec_Flip_emb_x.
      rewrite <-x_1_cF_y in  prec_Flip_emb_x. 
      rewrite <-y_1_cF_x in  prec_Flip_emb_x. 
       fold xff yff in  prec_Flip_emb_x. 
    unfold inv_Triangulation in inv_Triangulation_m. 
    unfold isWellembed in isWellembed_m. 
intros. cbv zeta in H. 
     decompose [and] H. clear H. 
  assert (exd m y_1). unfold y_1. generalize (exd_cA_1 m one y). 
       generalize exd_y. tauto. rename H2 into Ey_1. 
  assert (fpy_1 : fpoint m y_1 = fpoint m y). 
   assert (H2 : isWellembedv m). tauto. unfold isWellembedv in H2. 
     apply H2. tauto. unfold expv. unfold MA1.MfcA.expo. 
       split. tauto. split with 1. simpl. 
          assert (H8 : MA1.MfcA.f m y_1 = cA m one y_1). tauto. rewrite H8. 
           unfold y_1. rewrite cA_cA_1. tauto. tauto. apply exd_y. 
assert (Exch : ccw (fpoint m xff) (fpoint m yff) (fpoint m y) /\
            ccw (fpoint m yff) (fpoint m xff) (fpoint m x)).
  split. apply ccw_axiom_1. tauto. apply ccw_axiom_1. tauto.
   unfold ccw_triangle.
    rewrite <-H6. rewrite <-H7. 
   rewrite fpoint_Flip. 
     elim (eq_dart_dec x x). 
       rewrite fpoint_Flip. 
    elim (eq_dart_dec x yff). tauto.
    fold y.  elim (eq_dart_dec y yff). tauto. 
       rewrite fpoint_Flip. 
   elim (eq_dart_dec x y_1). tauto. fold y. 
   elim ( eq_dart_dec y y_1). intro. symmetry in a. tauto. intros.
     rewrite <-y_1_cF_x. fold xff. rewrite fpy_1. tauto. tauto. tauto. tauto. 
     fold y. tauto. tauto. tauto. tauto. fold y. tauto. tauto. 
    tauto. tauto. tauto. fold y. tauto. 
Qed.
    
Lemma ccw_triangle_y: ccw_triangle (Flip m x) y.
Proof.
    generalize diff_x. 
     generalize diff_y. 
    generalize diff_2faces_x_y.
    generalize cF_Flip. intros. cbv zeta in H.
    unfold prec_Flip_emb in prec_Flip_emb_x. 
     fold y x_1 y_1 in prec_Flip_emb_x.
      rewrite <-x_1_cF_y in  prec_Flip_emb_x. 
      rewrite <-y_1_cF_x in  prec_Flip_emb_x. 
       fold xff yff in  prec_Flip_emb_x. 
    unfold inv_Triangulation in inv_Triangulation_m. 
    unfold isWellembed in isWellembed_m. 
     decompose [and] H. clear H. 
  assert (exd m x_1). unfold x_1. generalize (exd_cA_1 m one x). 
       tauto. rename H2 into Ex_1. 
  assert (fpoint m x_1 = fpoint m x). 
   assert (isWellembedv m). tauto. unfold isWellembedv in H2. 
     apply H2. tauto. unfold expv. unfold MA1.MfcA.expo. 
       split. tauto. split with 1. simpl. 
          assert (MA1.MfcA.f m x_1 = cA m one x_1). tauto. rewrite H8. 
           unfold x_1. rewrite cA_cA_1. tauto. tauto. apply exd_x. 
     rename H2 into fpx_1. 
assert (ccw (fpoint m xff) (fpoint m yff) (fpoint m y) /\
            ccw (fpoint m yff) (fpoint m xff) (fpoint m x)).
  split. apply ccw_axiom_1. tauto. apply ccw_axiom_1. tauto.
 rename H2 into Exch. 
   unfold ccw_triangle.
    rewrite <-H3. rewrite <-H5. 
   rewrite fpoint_Flip. 
     elim (eq_dart_dec x y). tauto. fold y. 
      elim (eq_dart_dec y y). 
       rewrite fpoint_Flip. 
    elim (eq_dart_dec x xff). tauto.
    fold y.  elim (eq_dart_dec y xff). intro. symmetry in a. tauto. 
       rewrite fpoint_Flip. 
 elim (eq_dart_dec x x_1). tauto. fold y. 
   elim ( eq_dart_dec y x_1). tauto. intros. 
     rewrite <-x_1_cF_y. fold yff. rewrite fpx_1. tauto. tauto. tauto. tauto. 
     fold y. tauto. tauto. tauto. tauto. fold y. tauto. tauto. 
    tauto. tauto. tauto. fold y. tauto. 
Qed.

Lemma ccw_triangle_yff: ccw_triangle (Flip m x) yff.
Proof.
    generalize inv_Triangulation_m. intro ITm. 
    unfold inv_Triangulation in inv_Triangulation_m.
     decompose [and] inv_Triangulation_m.
    unfold isWellembed in isWellembed_m. 
    generalize cF_Flip. intro. cbv zeta in H2. 
     assert ( yff = cF (Flip m x) x). tauto. rewrite H4. 
   assert (prec_Flip m x).   
     apply prec_Flip_emb_prec_Flip. tauto. 
        tauto. tauto. tauto. tauto. rename H5 into PF. 
     generalize ccw_dart_cF. intro. 
     apply H5. apply inv_hmap_Flip.
     unfold inv_Triangulation. tauto. 
        tauto. 
        generalize (exd_Flip m x x). tauto. 
       generalize (isTri_Flip m x ITm PF). tauto. 
    apply ccw_triangle_x.
Qed.

Lemma ccw_triangle_xff: ccw_triangle (Flip m x) xff.
Proof.
    generalize inv_Triangulation_m. intro ITm. 
    unfold inv_Triangulation in inv_Triangulation_m.
     decompose [and] inv_Triangulation_m.
    unfold isWellembed in isWellembed_m. 
    generalize cF_Flip. intro. cbv zeta in H2. 
     assert (xff = cF (Flip m x) y). tauto. rewrite H4. 
   assert (prec_Flip m x). apply prec_Flip_emb_prec_Flip. tauto. 
        tauto. tauto. tauto. tauto. rename H5 into PF. 
     generalize ccw_dart_cF. intro. 
     apply H5. apply inv_hmap_Flip.
     unfold inv_Triangulation. tauto. 
        tauto. 
        generalize (exd_Flip m x y). generalize exd_y. tauto. 
       generalize (isTri_Flip m x ITm PF). tauto. 
    apply ccw_triangle_y.
Qed.

Lemma ccw_triangle_x_1: ccw_triangle (Flip m x) x_1.
Proof.
    generalize inv_Triangulation_m. intro ITm. 
    unfold inv_Triangulation in inv_Triangulation_m.
     decompose [and] inv_Triangulation_m.
    unfold isWellembed in isWellembed_m. 
    generalize cF_Flip. intro. cbv zeta in H2. 
    assert (exd m y_1).
      generalize (exd_cA_1 m one y). generalize (exd_y). tauto.
        rename H4 into Ey_1. 
    assert (exd m xff). unfold xff. 
        generalize (exd_cF m y_1). tauto.
          rename H4 into Exff. 
    assert (exd  (Flip m x) xff). 
           generalize (exd_Flip m x xff). tauto. 
              rename H4 into EFxff. 
     assert (x_1 = cF (Flip m x) xff). tauto. rewrite H4. 
   assert (prec_Flip m x).  apply prec_Flip_emb_prec_Flip. tauto. 
        tauto. tauto. tauto. tauto. rename H5 into PF. 
     generalize ccw_dart_cF. intro. 
 assert (xff = cF (Flip m x) y). tauto. 
       generalize (isTri_Flip m x ITm PF). fold y. intro. 
            assert (isTri (Flip m x) y). tauto. 
               unfold isTri in H8. 
 assert (degreef = MF.degree). tauto. 
 set(m':=Flip m x).
 assert (degreef m' xff = 3). 
     rewrite H6. fold m'. 
      rewrite H9. 
        rewrite (MF.expo_degree m' (cF m' y) y). 
     rewrite <-H9. tauto. unfold m'. apply inv_hmap_Flip.
          tauto. tauto. 
         apply MF.expo_symm.  
       unfold m'. apply inv_hmap_Flip. tauto. tauto. 
        unfold MF.expo. split. unfold m'. 
        generalize (exd_Flip m x y). generalize exd_y. tauto. 
     split with 1. unfold Iter; fold Iter. tauto. 
          apply H5.  unfold m'. apply inv_hmap_Flip. tauto. tauto. 
            apply EFxff.  unfold isTri. tauto. 
apply ccw_triangle_xff.
Qed.
   
Lemma ccw_triangle_y_1: ccw_triangle (Flip m x) y_1.
Proof.
    generalize inv_Triangulation_m. intro ITm. 
    unfold inv_Triangulation in inv_Triangulation_m.
     decompose [and] inv_Triangulation_m.
    unfold isWellembed in isWellembed_m. 
    generalize cF_Flip. intro. cbv zeta in H2. 
    assert (exd m x_1).
      generalize (exd_cA_1 m one x). tauto.
        rename H4 into Ex_1. 
    assert (exd m yff). unfold yff. 
        generalize (exd_cF m x_1). tauto.
          rename H4 into Eyff. 
    assert (exd  (Flip m x) yff). 
           generalize (exd_Flip m x yff). tauto. 
              rename H4 into EFyff. 
     assert (y_1 = cF (Flip m x) yff). tauto. rewrite H4. 
   assert (prec_Flip m x).  apply prec_Flip_emb_prec_Flip. tauto. 
        tauto. tauto. tauto. tauto. rename H5 into PF. 
     generalize ccw_dart_cF. intro. 
 assert (yff = cF (Flip m x) x). tauto. 
       generalize (isTri_Flip m x ITm PF). fold y. intro. 
            assert (isTri (Flip m x) x). tauto. 
               unfold isTri in H8. 
 assert (degreef = MF.degree). tauto. 
 set(m':=Flip m x).
 assert (degreef m' yff = 3). 
     rewrite H6. fold m'. 
      rewrite H9. 
        rewrite (MF.expo_degree m' (cF m' x) x). 
     rewrite <-H9. tauto. unfold m'. apply inv_hmap_Flip.
          tauto. tauto. 
         apply MF.expo_symm.  
       unfold m'. apply inv_hmap_Flip. tauto. tauto. 
        unfold MF.expo. split. unfold m'. 
        generalize (exd_Flip m x x). tauto. 
     split with 1. unfold Iter; fold Iter. tauto. 
          apply H5.  unfold m'. apply inv_hmap_Flip. tauto. tauto. 
            apply EFyff.  unfold isTri. tauto. 
apply ccw_triangle_yff.
Qed.

(* TO RECOMPILE IN TRIANG02 : *)

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
  assert (0 < ndN m0).
 apply MF.ndN_pos with z.
    tauto.
assert (cF = MF.f).
  tauto.
generalize (MF.degree_bound m0 z H H0).
  intro.
  generalize (MF.degree_lub m0 z H H0).
  simpl in |- *.
  intros.
  decompose [and] H8.
  rewrite MF.degree_aux_equation in |- *.
  clear H8.
  elim (Arith.Compare_dec.le_lt_dec 1 (ndN m0)).
 intro.
   elim (eq_dart_dec z (Iter (MF.f m0) 1 z)).
  intro.
    simpl in a0.
    rewrite <- H6 in a0.
    fold zf in a0.
     tauto.
 elim (Nat.eq_dec 1 (ndN m0)).
  intros.
    assert (MF.degree m0 z = 1).
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
   elim (Arith.Compare_dec.le_lt_dec 2 (ndN m0)).
  intro.
    elim (eq_dart_dec z (Iter (MF.f m0) 2 z)).
   rewrite <- H6 in |- *.
     simpl in |- *.
     fold zf in |- *.
     fold zff in |- *.
      tauto.
  elim (Nat.eq_dec 2 (ndN m0)).
   intros.
     elim (Nat.eq_dec (MF.degree m0 z) 1).
    intro.
      rewrite a2 in H11.
      simpl in H11.
      rewrite <- H6 in H11.
      fold zf in H11.
      symmetry  in H11.
       tauto.
   intro.
     assert (MF.degree m0 z = 2).
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
    elim (Arith.Compare_dec.le_lt_dec (2 + 1) (ndN m0)).
   intro.
     elim (eq_dart_dec z (Iter (MF.f m0) (2 + 1) z)).
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

Lemma expf_Flip_1: 
  forall z, 
     (expf (Flip m x) 1 z <-> expf m 1 z).
Proof.
generalize cF_Flip_1; intros cF_Flip_1'.
generalize cF_Flip_cF_1; intros cF_Flip_cF_1'.
generalize cF_Flip_cF_cF_1; intros cF_Flip_cF_cF_1'.
   generalize inv_Triangulation_m. intro ITm. 
  unfold inv_Triangulation in inv_Triangulation_m.
  unfold isWellembed in isWellembed_m. 
    assert (prec_Flip m x). 
  apply prec_Flip_emb_prec_Flip. tauto. tauto. tauto. tauto. tauto. 
   decompose [and] inv_Triangulation_m. clear inv_Triangulation_m. 
   unfold isTriangulation in H4. intros. 
   assert (inv_hmap (Flip m x)). 
    apply inv_hmap_Flip. tauto. tauto. 
  assert (exd (Flip m x) 1). 
    generalize (exd_Flip m x 1). tauto. 
    assert (isTri m 1). apply H4. tauto. 
    assert (exd m 1). tauto. 
     generalize (Tri_diff_face m 1 H0 H7 H6). 
     intro. simpl in H8. 
         assert (cF m (cF m (cF m 1)) = 1). 
        assert (Iter (MF.f m) 3 1 = 1). 
            unfold isTri in H6. 
       assert (degreef = MF.degree). tauto. 
        rewrite <-H6. rewrite H9. 
          rewrite MF.degree_per. tauto. tauto. tauto. 
        simpl in H9. tauto.  
      set(m':= Flip m x). 
     assert (1 <> cF m' 1 /\ 1 <> cF m' (cF m' 1) /\ cF m' 1 <> cF m' (cF m' 1)). 
       unfold m'. 
      rewrite cF_Flip_1'.  
     rewrite cF_Flip_cF_1'. tauto. 
     assert (cF m' (cF m' (cF m' 1)) = 1). 
   unfold m'.    rewrite cF_Flip_1'.  
      rewrite cF_Flip_cF_1'. rewrite cF_Flip_cF_cF_1'. tauto. 
    assert (isTri m' 1). 
    unfold m'. unfold m' in H10, H11. 
     apply diff3_Tri. tauto. apply H5.   tauto. tauto. 
       tauto. tauto. 
     generalize (expf_1 m z H0 H7 H6). 
 generalize (expf_1 m' z H3 H5 H12).
    unfold m'. rewrite cF_Flip_1'.  rewrite cF_Flip_cF_1'. 
        tauto. 
Qed.
     
Lemma not_expf_1_diff_ccw_triangle:
  let m' := Flip m x in
    forall z : dart, 
      exd m' z -> ~ expf m' z 1 ->
          (y <> z /\ xff <> z /\ yff <> z /\ x <> z /\ y_1 <> z /\ x_1 <> z) ->
           ccw_triangle m' z.
Proof.
    unfold inv_Triangulation in inv_Triangulation_m. 
     decompose [and] inv_Triangulation_m. 
       unfold  isTriangulation in H3. 
     unfold ccw_triangle. intros. 
       generalize diff_x. 
     generalize diff_y. 
    generalize diff_2faces_x_y. intros. 
        assert (exd m z). 
     generalize (exd_Flip m x z). tauto. 
     generalize (expf_Flip_1 z). intro. 
     assert (~expf  (Flip m x) 1 z). intro. elim H4. apply expf_symm. tauto.
    assert (~expf m 1 z). 
      elim (expf_dec m 1 z). intro. tauto. tauto. 
        rewrite fpoint_Flip. fold y. 
    assert (isTri m z). apply H3. tauto. 
     assert (cF = MF.f). tauto. 
    assert (degreef = MF.degree). tauto. 
     generalize (Tri_diff_face m z H H9 H13). intro. simpl in H16. 
       assert (cF m (cF m (cF m z)) = z). 
       assert (Iter (MF.f m) 3 z = z). unfold isTri in H13. 
        rewrite <-H13. rewrite H15. rewrite MF.degree_per. tauto. 
             tauto. tauto. simpl in H17. tauto. 
     elim (eq_dart_dec x z). tauto. 
     elim (eq_dart_dec y z). tauto. 
      rewrite cF_Flip_z. 
    rewrite cF_Flip_z. 
      rewrite fpoint_Flip.  rewrite fpoint_Flip. 
     fold y. 
  elim (eq_dart_dec x (cF m z)). 
     intros. assert (z = cF m (cF m x)). rewrite a. symmetry. tauto. 
           rewrite <-y_1_cF_x in H18. fold xff in H18. symmetry in H18. tauto.
  elim (eq_dart_dec y (cF m (cF m z))). intros. 
     assert (z = cF m y). rewrite a. symmetry. tauto. 
    rewrite <-x_1_cF_y in H18. symmetry in H18. tauto. 
 elim (eq_dart_dec y (cF m z)). intros. 
     assert (z = cF m (cF m y)). rewrite a. symmetry. tauto. 
           rewrite <-x_1_cF_y in H18. fold yff in H18. symmetry in H18. tauto.
 elim (eq_dart_dec x (cF m (cF m z))). intros. 
     assert (z = cF m x). rewrite a. symmetry. tauto. 
    rewrite <-y_1_cF_x in H18. symmetry in H18. tauto. 
 intros. unfold isWellembed in isWellembed_m. 
   assert (isWellembedf m). tauto. 
    unfold isWellembedf in H18. 
    elim H18. clear H18. intros. 
    unfold  ccw_triangle in H; apply H19. tauto. intro. 
    elim H12. apply expf_symm. tauto. tauto. tauto. tauto. 
        fold y. tauto. tauto. tauto. tauto. fold y. tauto. 
         generalize (exd_cF m z). tauto. intro. 
 assert (z = cF m (cF m y)). rewrite H18. symmetry. tauto. 
           rewrite <-x_1_cF_y in H19. fold yff in H19. symmetry in H19. tauto.
 intro. unfold xff in H18. 
     assert (y_1 = cF_1 m (cF m z)). rewrite <-H18. 
        rewrite cF_1_cF. tauto. tauto. 
     generalize (exd_cA_1 m one y). fold y_1. generalize exd_y. tauto. 
         rewrite cF_1_cF in H19. tauto. tauto. tauto. 
intro. unfold yff in H18. 
     assert (x_1 = cF_1 m (cF m z)). rewrite <-H18. 
        rewrite cF_1_cF. tauto. tauto. 
     generalize (exd_cA_1 m one x). fold x_1. tauto. 
         rewrite cF_1_cF in H19. tauto. tauto. tauto. 
intro. assert (z = cF m (cF m x)). rewrite H18. symmetry. tauto. 
           rewrite <-y_1_cF_x in H19. fold xff in H19. symmetry in H19. tauto.
intro. 
     rewrite y_1_cF_x in H18. assert (x = cF_1 m (cF m z)). 
         rewrite <-H18. rewrite cF_1_cF. tauto. tauto. tauto. 
              rewrite cF_1_cF in H19. tauto. tauto. tauto.
intro. 
     rewrite x_1_cF_y in H18. assert (y = cF_1 m (cF m z)). 
         rewrite <-H18. rewrite cF_1_cF. tauto. tauto. apply exd_y. 
              rewrite cF_1_cF in H19. tauto. tauto. tauto. 
  tauto. tauto.  tauto. tauto.  tauto. tauto.  tauto. tauto.  
    tauto. tauto. fold y. tauto.
Qed.

Lemma not_expf_1_ccw_triangle:
  let m' := Flip m x in
    forall z : dart, 
      exd m' z -> ~expf m' z 1 -> ccw_triangle m' z.
Proof.
  intros. 
  elim (eq_dart_dec y z). intro. rewrite <-a. 
       apply ccw_triangle_y. intro. 
  elim (eq_dart_dec xff z). intro. rewrite <- a. 
         apply ccw_triangle_xff. intro.  
  elim (eq_dart_dec yff z). intro. rewrite <- a. 
         apply ccw_triangle_yff. intro.  
 elim (eq_dart_dec x z). intro. rewrite <- a. 
         apply ccw_triangle_x. intro.  
  elim (eq_dart_dec y_1 z). intro. rewrite <- a. 
         apply ccw_triangle_y_1. intro.
 elim (eq_dart_dec x_1 z). intro. rewrite <- a. 
         apply ccw_triangle_x_1. intro.
  apply not_expf_1_diff_ccw_triangle. 
   tauto. tauto. 
   tauto.
Qed.

Theorem isWellembedf_Flip: isWellembedf (Flip m x).   
Proof.
  unfold isWellembedf. split. 
   apply cw_Flip_1. 
    apply  not_expf_1_ccw_triangle. 
Qed.

End embed_faces.

(*====================================================
    Preservation of the embedding properties by Flip: 
=====================================================*)

(* OK! *)

Theorem isWellembed_Flip: forall (m:fmap)(x:dart), 
  inv_Triangulation m -> isWellembed m -> 
      exd m x -> prec_Flip_emb m x -> isWellembed (Flip m x).   
Proof.
  unfold isWellembed. intros. 
    split. generalize (exd_Flip m x 1). tauto. 
    split. apply embede_Flip. tauto. tauto. tauto. tauto. tauto. 
    split. apply isWellembedv_Flip.  tauto. tauto. tauto. tauto.
         tauto. 
    apply  isWellembedf_Flip. tauto. unfold isWellembed. 
        tauto. tauto. tauto. 
Qed.    

(*==================================================
                         END TRIANG04
====================================================*)



(*==================================================
                  SUPPLEMENTS (POUR PLUS TARD)
====================================================*)

(* 

(* inCircle, onCircle, outCircle, A FAIRE COMME KnuthAxioms et
ModelOfKnuth: *)

Definition det2 a11 a12 a21 a22 := a11 * a22 - a12 * a21. 

Definition det3 a11 a12 a13 
                      a21 a22 a23
                      a31 a32 a33 := 
   a11 * (det2 a22 a23 a32 a33)
 - a21 * (det2 a12 a13 a32 a33)
+ a31 * (det2 a12 a13 a22 a23).

Definition det4 a11 a12 a13 a14 
                      a21 a22 a23 a24
                      a31 a32 a33 a34
                      a41 a42 a43 a44  := 
   a11 * (det3 a22 a23 a24 a32 a33 a34 a42 a43 a44)
 - a21 * (det3 a12 a13 a14 a32 a33 a34 a42 a43 a44)
+ a31 * (det3 a12 a13 a14 a22 a23 a24 a42 a43 a44)
 - a41 * (det3 a12 a13 a14 a22 a23 a24 a32 a33 a34).

Lemma neq_det2 : forall (a11 a12 a21 a22 : R),
  det2 a11 a12 a21 a22 = - det2 a21 a22 a11 a12.
Proof.
intros.
unfold det2; ring.
Qed.

Lemma eq_det2_0 : forall (a11 a12 : R),
  det2 a11 a12 a11 a12 = 0.
Proof.
intros.
unfold det2; ring.
Qed.

Lemma neq_det3 : 
  forall (a11 a12 a13 
           a21 a22 a23
           a31 a32 a33: R),
  det3  a11 a12 a13 
           a21 a22 a23
           a31 a32 a33 = 
- det3  a21 a22 a23
           a11 a12 a13
           a31 a32 a33.
Proof.
intros.
unfold det3; unfold det2; ring.
Qed.

Lemma eq_det3_0 : 
  forall (a11 a12 a13 
           a31 a32 a33: R),
  det3  a11 a12 a13 
           a11 a12 a13
           a31 a32 a33 = 0.
Proof.
  intros.
  unfold det3; unfold det2; ring.
Qed.

Lemma neq_det4 : 
  forall (a11 a12 a13 a14 
          a21 a22 a23 a24
          a31 a32 a33 a34
          a41 a42 a43 a44 : R),
  det4 a11 a12 a13 a14 
          a21 a22 a23 a24
          a31 a32 a33 a34
          a41 a42 a43 a44 =
- det4 a21 a22 a23 a24
          a11 a12 a13 a14 
          a31 a32 a33 a34
          a41 a42 a43 a44.
Proof.
 intros.
  unfold det4; unfold det3; unfold det2; ring.
Qed.

Lemma eq_det4_perm : 
  forall (a11 a12 a13 a14 
          a21 a22 a23 a24
          a31 a32 a33 a34
          a41 a42 a43 a44 : R),
  det4 a11 a12 a13 a14 
          a21 a22 a23 a24
          a31 a32 a33 a34
          a41 a42 a43 a44 =
  det4 a21 a22 a23 a24
          a31 a32 a33 a34
          a11 a12 a13 a14
          a41 a42 a43 a44.
Proof.
 intros.
  unfold det4; unfold det3; unfold det2; ring.
Qed.

Lemma eq_det4_0 : 
  forall (a11 a12 a13 a14 
          a31 a32 a33 a34
          a41 a42 a43 a44 : R),
  det4 a11 a12 a13 a14 
          a11 a12 a13 a14 
          a31 a32 a33 a34
          a41 a42 a43 a44 = 0.
Proof.
 intros.
  unfold det4; unfold det3; unfold det2; ring.
Qed.

Lemma eq_det4_0_bis : 
  forall (a11 a12 a13 a14 
           a21 a22 a23 a24
           a31 a32 a33 a34 : R),
  det4 a11 a12 a13 a14 
          a21 a22 a23 a24 
          a31 a32 a33 a34
          a11 a12 a13 a14 = 0.
Proof.
 intros.
  unfold det4; unfold det3; unfold det2.
  ring.
Qed.

Definition mod2 (p:point) := let (x, y) := p in x * x + y * y.

Definition inCircle p q r s := 
    det4 (fst p) (snd p) (mod2 p) 1 
            (fst q) (snd q) (mod2 q) 1 
            (fst r) (snd r) (mod2 r) 1
            (fst s) (snd s) (mod2 s) 1 > 0.

Lemma inCircle_perm :  forall (p q r s:point),
    inCircle p q r s -> inCircle q r p s.
Proof.
 unfold inCircle. intros.
 rewrite eq_det4_perm in H. tauto. 
Qed. 

(*
Definition onCircle p q r s := 
    det4 (fst p) (snd p) (mod2 p) 1 
            (fst p) (snd q) (mod2 q) 1 
            (fst r) (snd r) (mod2 r) 1
            (fst s) (snd s) (mod2 s) 1 = 0.
*)

Lemma inCircle_dec: forall (p q r s:point),
    {inCircle p q r s} + {~inCircle p q r s}.
Proof.
   intros. unfold inCircle.
   apply Rgt_dec.
Qed.

(*
Lemma onCircle_dec: forall (p q r s:point),
    {onCircle p q r s} + {~onCircle p q r s}.
Proof.
   intros. unfold onCircle.
   apply Req_dec.
Qed.

Definition outCircle(p q r s:point):=
   ~inCircle p q r s /\ ~onCircle p q r s.

Hypothesis outCircle_dec :
    forall p q r s, {outCircle p q r s} + {~outCircle p q r s}.

Hypothesis in_on_outCircle_dec :
    forall p q r s, 
     {inCircle p q r s} + {onCircle p q r s} + {outCircle p q r s}.
*)

(* THE ONLY THING TO PROVE: *)

(* ALGEBRAICLY FEASIBLE ???   TO DO... AFTER *)

Lemma ccw_exchange: forall (p q r s: point),
  ccw p q r -> ccw q p s -> inCircle p q r s ->
      (ccw r s q /\ ccw s r p).
Admitted.

Lemma ccw_exchange_1: forall (p q r s: point),
  ccw p q r -> ccw q p s -> inCircle p q r s ->
      ~inCircle p s r q.
Admitted.

(* ABSOLUTELY NECESSARY: 
Pose as Axioms in Knuth's Axiomatics: *)


Lemma inCircle_neq_aux: forall p q r s, 
    inCircle p q r s -> p <> q.
Proof.
unfold inCircle. 
intros. intro. 
   rewrite <-H0 in H. 
   rewrite eq_det4_0 in H.
   generalize H. apply Rgt_irrefl. 
Qed.

Lemma inCircle_neq: forall p q r s, 
    inCircle p q r s -> (p <> q  /\ q <> r /\ r <> p).
Proof.
intros. 
generalize (inCircle_perm p q r s H). intro.
 generalize (inCircle_perm q r p s H0). intro.
split. apply  (inCircle_neq_aux p q r s H). 
split. apply  (inCircle_neq_aux q r p s H0). 
 apply  (inCircle_neq_aux r p q s H1). 
Qed.

Lemma inCircle_axiom_x_aux: forall p q r s, 
    inCircle p q r s -> p <> s.
Proof.
unfold inCircle. 
intros. intro. 
   rewrite <-H0 in H. 
   rewrite eq_det4_0_bis in H.
   generalize H. apply Rgt_irrefl. 
Qed.

Lemma inCircle_axiom_x: forall p q r s, 
    inCircle p q r s -> (p <> s /\ q <> s /\ r <> s).
Proof.
 intros. 
generalize (inCircle_perm p q r s H). intro.
 generalize (inCircle_perm q r p s H0). intro.
split. apply  (inCircle_axiom_x_aux p q r s H). 
split. apply (inCircle_axiom_x_aux q r p s H0).
apply (inCircle_axiom_x_aux r p q s H1).
Qed.




(* PREMATURE... *)
(*=========================================================
                     Illegal and its Properties -
                       Implies prec_Flip:
==========================================================*)

(* Definition of illegal: only used when x is in m: *)

Definition illegal (m:fmap)(x:dart):Prop :=
   let y := cA m zero x in
   let px := fpoint m x in
   let py := fpoint m y in
   let pxff := fpoint m (cF m (cF m x)) in
   let pyff := fpoint m (cF m (cF m y)) in
  ccw px py pxff /\ ccw py px pyff /\ inCircle px py pxff pyff.
  
Lemma illegal_dec :
    forall m x, {illegal m x} + {~illegal m x}.
Proof.
   unfold illegal. intros.
    generalize (ccw_dec (fpoint m x) 
           (fpoint m (cA m zero x)) (fpoint m (cF m (cF m x)))). 
    generalize (ccw_dec (fpoint m (cA m zero x)) (fpoint m x) 
          (fpoint m (cF m (cF m (cA m zero x))))).
    generalize (inCircle_dec (fpoint m x) (fpoint m (cA m zero x))
          (fpoint m (cF m (cF m x))) (fpoint m (cF m (cF m (cA m zero x))))).
   tauto.
Qed.

(* Determination of an illegal dart (order without importance): *)

Fixpoint illegal_first (m mr:fmap){struct m}:dart:=
  match m with
    V => Del01.nil
   |  I m0 x t p =>
           if illegal_dec mr x then x else illegal_first m0 mr 
   |  L m0 k x y => illegal_first m0 mr
 end.

Lemma exd_illegal_first: forall m mr, 
  let x := illegal_first m mr in
    x <> Del01.nil -> exd m x. 
Proof.
   induction m. simpl. tauto. 
    simpl. intro mr. 
      elim (illegal_dec mr d). 
        intros. tauto. 
        intros. right. apply IHm. tauto.
      simpl. intros. apply IHm. tauto.
Qed.

Definition no_dart_illegal(m:fmap):Prop:= 
    illegal_first m m = Del01.nil.

Lemma illegal_first_illegal_aux:
 forall m mr, 
   let x := illegal_first m mr in
    x <> Del01.nil -> illegal mr x.
Proof.
   intros. unfold x. 
    induction m. simpl. simpl in x. unfold x. tauto. 
    simpl. simpl in x. 
       elim (illegal_dec mr d). intro. assert (x = d). unfold x.
            elim (illegal_dec mr d). tauto. intro. tauto. tauto. 
            intro. apply IHm. 
      assert (x = illegal_first m mr). unfold x.
           elim (illegal_dec mr d). tauto. intro. tauto. rewrite <-H0. tauto. 
    simpl. simpl in x. apply IHm. simpl in H. tauto. 
Qed.
    
Lemma illegal_first_illegal:
 forall m,
   let x := illegal_first m m in
      x <> Del01.nil -> illegal m x.
Proof.
   intros. apply illegal_first_illegal_aux. fold x. tauto.
Qed.
 
(* Stopping test: *)

Lemma no_dart_illegal_dec: 
   forall m, {no_dart_illegal m} + {~no_dart_illegal m}.
Proof.
   unfold no_dart_illegal. intro.
    apply eq_dart_dec.
Qed.

(* Next map: *)

Definition next_fmap (m:fmap): fmap := 
   let z:= illegal_first m m in 
   if eq_dart_dec z Del01.nil then m else Flip m z.

(* Because isMap m: *)

Lemma x_neq_y: forall (m:fmap)(x:dart),
   inv_Triangulation m -> exd m x -> 
       x <> cA m zero x. 
Proof.
  unfold inv_Triangulation. unfold illegal. intros m x. 
  set(y:= cA m zero x). intros. 
  decompose [and] H. clear H. unfold isMap in H3. 
  generalize (H3 x H0). intro. 
   generalize (degreee_invol_nofixpt m x H1 H0). 
    fold y. intros. intro. symmetry in H6. tauto. 
Qed.
    
Lemma px_neq_py: forall (m:fmap)(x:dart),
  isWellembede m -> exd m x ->
    fpoint m x <> fpoint m (cA m zero x). 
Proof.
  unfold isWellembede. intros. 
   apply H. tauto.
Qed.

(* Proofs that illegal entails prec_Flip: *)

Lemma illegal_pxff_neq_pyff: forall (m:fmap)(x:dart),
 exd m x -> isWellembede m -> illegal m x ->
   let y := cA m zero x in
   let px := fpoint m x in
   let py := fpoint m y in
   let pxff := fpoint m (cF m (cF m x)) in
   let pyff := fpoint m  (cF m (cF m y)) in
    pxff <> pyff.
Proof.
   unfold illegal.
   intros m x. set (y:=cA m zero x). 
   intros. decompose [and] H1. clear H1. 
   intro. rewrite <-H1 in H5. 
     assert (fpoint m x <> fpoint m y). 
       apply px_neq_py. tauto. tauto. 
      generalize   
       (ccw_axiom_6_bis (fpoint m x) (fpoint m y) (fpoint m (cF m (cF m x))) H2). intro. 
     generalize   
       (ccw_axiom_6_bis (fpoint m y) (fpoint m x) (fpoint m (cF m (cF m y))) H4). intro.
      generalize (inCircle_axiom_x (fpoint m x) (fpoint m y) (fpoint m (cF m (cF m x)))
       (fpoint m (cF m (cF m x)))). intros. 
     tauto. 
Qed.

Lemma cA_expv: forall m z, 
     exd m z -> expv m z (cA m one z). 
Proof.
   intros. unfold expv. unfold MA1.MfcA.expo. 
    split. tauto. split with 1%nat. simpl. tauto.
Qed.

Open Scope nat_scope.

(* Because isWellembed and illegal, OK: *)

Lemma illegal_degreev: forall (m:fmap)(x:dart),
  inv_Triangulation m -> isWellembede m -> isWellembedv m ->
    exd m x -> illegal m x ->
      (3 <= degreev m x /\ 3 <= degreev m (cA m zero x)). 
Proof.
  unfold inv_Triangulation. unfold illegal. intros m x H. intro Eme. 
  set (y:= cA m zero x). intros. 
  decompose [and] H. clear H.
   decompose [and] H2. clear H2.
    assert (exd m y). unfold y. generalize (exd_cA m zero x). tauto. 
        rename H2 into Ey. 
   generalize (degreee_invol_nofixpt m x H3 H1). intro. 
         assert (cA m zero x <> x /\ cA m zero (cA m zero x) = x).
           unfold isMap in H5. 
            generalize (H5 x H1). 
            tauto. clear H2. fold y in H6. 
   generalize (invol_inverse m zero x H3 H1). intro. 
        assert (cA m zero x = cA_1 m zero x). tauto. clear H2. 
                fold y in H10. 
  decompose [and] H6. clear H6. 
 generalize (degreee_invol_nofixpt m y H3 Ey). intro. 
         assert (cA m zero y <> y /\ cA m zero (cA m zero y) = y).
           unfold isMap in H5. 
            generalize (H5 y Ey). 
            tauto. clear H6. decompose [and] H12. clear H12. 
   generalize (invol_inverse m zero y H3 Ey). intro. 
        assert (cA m zero y = cA_1 m zero y). tauto. clear H12. 
   assert (x=cA_1 m zero y). unfold y. rewrite cA_1_cA. tauto. tauto. tauto.      
(* 1st PART: *)       
elim (eq_nat_dec (degreev m x)  2). intro. 
   generalize (degreev_invol_nofixpt m x H3 H1). intro. 
        assert (cA m one x <> x /\ cA m one (cA m one x) = x). tauto. clear H15. 
     generalize (invol_inverse m one x H3 H1). intro. 
        assert (cA m one x = cA_1 m one x). tauto. 
      set(x1:= cA m one x). fold x1 in H16, H15, H17. 
     decompose [and] H16. clear H15. clear H16. 
         assert (exd m x1). unfold x1. generalize (exd_cA m one x). tauto. 
               rename H15 into Ex1. 
           assert (cF m y = x1). unfold cF. rewrite <-H12. symmetry. tauto. 
              set (x10:= cA m zero x1). 
               assert (x1 = cA_1 m zero x10). unfold x10. 
                 rewrite cA_1_cA. tauto. tauto. tauto. 
       generalize (degreee_invol_nofixpt m x1 H3 Ex1). intro. 
         assert (cA m zero x1 <> x1 /\ cA m zero (cA m zero x1) = x1).
            generalize (H5 x1 Ex1). 
            tauto. clear H20. decompose [and] H21. clear H21. 
               fold x10 in H22. 
     generalize (invol_inverse m zero x1 H3 Ex1). intro. 
        assert (cA m zero x1 = cA_1 m zero x1). tauto. clear H21. 
    assert (cF m (cF m y) = cA_1 m one x10). 
       unfold cF. fold x10 in H23. fold (cF m y). 
          rewrite H15. rewrite <-H23. tauto. 
        assert (cF = MF0Tr.MfM.f). tauto. 
     assert (x10 = cF_1 m x). unfold cF_1. fold x1. fold x10. tauto. 
       assert (degreef m x = 3). unfold isTriangulation in H7. 
          generalize (H7 x H1). unfold isTri. tauto. 
         assert (x10 = Iter (cF_1 m) 1 x). simpl. tauto. 
      assert (Iter (cF m) 3 x = x).  rewrite H24. 
         rewrite <-H26. unfold degreef. 
         rewrite MF0Tr.MfM.degree_per. tauto. tauto. tauto. 
       assert (x10 =  Iter (cF m) 2 x). 
          assert (2 = 3  - 1). lia. rewrite H29. 
             rewrite <-MF0Tr.MfM.Iter_f_f_1. 
               rewrite <-H24. rewrite H28. simpl. tauto. tauto. tauto.
               lia. simpl in H29. 
          assert (x10 = cA m one (cF m (cF m y))). rewrite H21. 
                 rewrite cA_cA_1. tauto. tauto. unfold x10. 
             generalize (exd_cA m zero x1). tauto. 
         unfold isWellembedv in H0. 
              assert (fpoint m (cF m (cF m y)) = 
                fpoint m (cA m one (cF m (cF m y)))). 
     apply H0. rewrite H15. generalize (exd_cF m x1). tauto. 
         apply cA_expv. 
              generalize (exd_cF m y). generalize (exd_cF m (cF m y)). tauto. 
             rewrite <-H30 in H31. rewrite H29 in H31. 
      symmetry in H31. absurd ( fpoint m (cF m (cF m x)) = fpoint m (cF m (cF m y))).
          apply  illegal_pxff_neq_pyff. tauto. tauto. unfold illegal. tauto. tauto. 
            intro. 
(* 2nd PART: *)
 elim (eq_nat_dec (degreev m y)  2). intro. 
   generalize (degreev_invol_nofixpt m y H3 Ey). intro. 
        assert (cA m one y <> y /\ cA m one (cA m one y) = y). tauto. clear H15. 
     generalize (invol_inverse m one y H3 Ey). intro. 
        assert (cA m one y = cA_1 m one y). tauto. 
      set(y1:= cA m one y). fold y1 in H16, H15, H17. 
     decompose [and] H16. clear H15. clear H16. 
         assert (exd m y1). unfold y1. generalize (exd_cA m one y). tauto. 
               rename H15 into Ey1. 
           assert (cF m x = y1). unfold cF. rewrite <-H10. symmetry. tauto. 
              set (y10:= cA m zero y1). 
               assert (y1 = cA_1 m zero y10). unfold y10. 
                 rewrite cA_1_cA. tauto. tauto. tauto. 
       generalize (degreee_invol_nofixpt m y1 H3 Ey1). intro. 
         assert (cA m zero y1 <> y1 /\ cA m zero (cA m zero y1) = y1).
            generalize (H5 y1 Ey1). 
            tauto. clear H20. decompose [and] H21. clear H21. 
               fold y10 in H22. 
     generalize (invol_inverse m zero y1 H3 Ey1). intro. 
        assert (cA m zero y1 = cA_1 m zero y1). tauto. clear H21. 
    assert (cF m (cF m x) = cA_1 m one y10). 
       unfold cF. fold y10 in H23. fold (cF m x). 
          rewrite H15. rewrite <-H23. tauto. 
        assert (cF = MF0Tr.MfM.f). tauto. 
     assert (y10 = cF_1 m y). unfold cF_1. fold y1. fold y10. tauto. 
       assert (degreef m y = 3). unfold isTriangulation in H7. 
          generalize (H7 y Ey). unfold isTri. tauto. 
         assert (y10 = Iter (cF_1 m) 1 y). simpl. tauto. 
      assert (Iter (cF m) 3 y = y).  rewrite H24. 
         rewrite <-H26. unfold degreef. 
         rewrite MF0Tr.MfM.degree_per. tauto. tauto. tauto. 
       assert (y10 =  Iter (cF m) 2 y). 
          assert (2 = 3  - 1). lia. rewrite H29. 
             rewrite <-MF0Tr.MfM.Iter_f_f_1. 
               rewrite <-H24. rewrite H28. simpl. tauto. tauto. tauto.
               lia. simpl in H29. 
          assert (y10 = cA m one (cF m (cF m x))). rewrite H21. 
                 rewrite cA_cA_1. tauto. tauto. unfold y10. 
             generalize (exd_cA m zero y1). tauto. 
         unfold isWellembedv in H0. 
              assert (fpoint m (cF m (cF m x)) = 
                fpoint m (cA m one (cF m (cF m x)))). 
     apply H0. rewrite H15. generalize (exd_cF m y1). tauto. 
       apply cA_expv. 
              generalize (exd_cF m x). generalize (exd_cF m (cF m x)). tauto. 
             rewrite <-H30 in H31. rewrite H29 in H31. 
     absurd ( fpoint m (cF m (cF m x)) = fpoint m (cF m (cF m y))).
          apply  illegal_pxff_neq_pyff. tauto. tauto. unfold illegal. tauto. tauto. 
            intro. 
  unfold isPoly in H4. 
    generalize (H4 x H1).   generalize (H4 y Ey). intros. 
    split. lia. lia.
Qed.

(* THEN: *)

Lemma illegal_expf: forall (m:fmap)(x:dart),
  inv_Triangulation m -> isWellembedv m -> 
    exd m x -> illegal m x ->
      ~expf m x (cA m zero x). 
Proof. 
   unfold inv_Triangulation. intros m x H We. intros. 
     decompose [and] H. clear H. 
   set(y:=cA m zero x). intro. 
    assert (exd m y). unfold y. generalize (exd_cA m zero x). tauto. 
  rename H5 into Ey.
   assert (degreef m x = 3). 
    unfold isTriangulation in H6. unfold isTri in H6. 
    apply H6. tauto. 
    unfold expf in H. 
     assert (MF.expo2 m x y).  generalize (MF.expo_expo2 m x y). tauto. 
       unfold MF.expo2 in H7. 
    decompose [and] H7. clear H7. 
     elim H9. clear H9. intros j Hj. decompose [and] Hj. clear Hj. 
    assert (degreef=MF.degree). tauto. rewrite <-H10 in H7. 
       rewrite H5 in H7. 
     assert (MF.f = cF). tauto. 
  elim (eq_nat_dec j 0). intro. rewrite a in H9. simpl in H9. 
   generalize H9; clear H9. apply x_neq_y. unfold inv_Triangulation.
           tauto. tauto. intro. 
  elim (eq_nat_dec j 1). intro. rewrite a in H9. simpl in H9. 
          rewrite H11 in H9. unfold cF in H9. 
     generalize (degreee_invol_nofixpt m x H2 H0). intro. 
         assert (cA m zero x <> x /\ cA m zero (cA m zero x) = x).
           unfold isMap in H4. 
            generalize (H4 x H0). 
            tauto. clear H12. fold y in H13. 
   generalize (invol_inverse m zero x H2 H0). intro. 
        assert (cA m zero x = cA_1 m zero x). tauto. clear H12. 
                fold y in H14. 
           decompose [and] H13. clear H13. 
          rewrite <-H15 in H9. rewrite cA_1_cA in H9. 
           assert (y = cA m one y). rewrite <-H9. rewrite cA_cA_1. tauto. tauto. 
                tauto. symmetry in H13. 
          generalize (degreev_fixpt m y). intro. 
          assert (degreev m y = 1). tauto. clear H16. 
         unfold isPoly in H3. generalize (H3 y Ey). lia. tauto. tauto. intro.
  assert (j = 2). lia. 
    rewrite H12 in H9; simpl in H9. 
    generalize (degreee_invol_nofixpt m x H2 H0). intro. 
         assert (cA m zero x <> x /\ cA m zero (cA m zero x) = x).
           unfold isMap in H4. 
            generalize (H4 x H0). 
            tauto. clear H13. fold y in H14. 
       decompose [and] H14. clear H14.
   generalize (invol_inverse m zero x H2 H0). intro. 
        assert (cA m zero x = cA_1 m zero x). tauto. clear H14. 
                fold y in H16. 
          assert (cF m x = cA_1 m one y). 
             unfold cF. 
          rewrite <-H16. tauto. 
       assert (cA m one (cF m x) = y). unfold cF. 
         rewrite cA_cA_1. symmetry. tauto.   tauto. 
         generalize (exd_cA_1 m zero x). tauto. 
          unfold isWellembedv in We. 
     assert (fpoint m y = fpoint m (cF m x)). 
     rewrite <-H17. symmetry. apply We. 
         generalize (exd_cF m x). tauto. 
 apply cA_expv. generalize (exd_cF m x). tauto. 
      assert (fpoint m y = fpoint m (cF m (cF m x))).  
         rewrite <-H11. rewrite H9. tauto. 
       unfold illegal in H1. decompose [and] H1. 
       generalize (ccw_axiom_6_bis (fpoint m x)
               (fpoint m (cA m zero x)) (fpoint m (cF m (cF m x))) H20). 
         intros. 
     assert (fpoint m (cA m zero x) <> fpoint m (cF m (cF m x))). tauto. 
         fold y in H24. tauto. 
Qed.
        
Lemma isWellembed_expv: forall (m:fmap)(x:dart),
  inv_Triangulation m -> isWellembede m ->  isWellembedv m -> 
    exd m x -> ~expv m x (cA m zero x). 
Proof. 
   intros m x. set(y:=cA m zero x). 
     intros. intro. 
   unfold isWellembedv in H1. 
     assert ( fpoint m x = fpoint m y). 
        apply H1. tauto. tauto. 
     unfold isWellembede in H0. generalize (H0 x H2). fold y. tauto.
Qed.
      
(* Finally: *)

Theorem illegal_prec_Flip:  forall (m:fmap)(x:dart),
  inv_Triangulation m -> isWellembede m -> isWellembedv m -> 
    exd m x -> illegal m x ->
      prec_Flip m x. 
Proof.
    unfold prec_Flip. intros m x. 
     set (y:=cA m zero x). intros.
   split. tauto. split. 
   apply illegal_expf. tauto. tauto. tauto. tauto. 
    split. apply isWellembed_expv. tauto. tauto. tauto. tauto. 
  apply illegal_degreev.  tauto. tauto. tauto. tauto. tauto.
Qed.

(* USELESS??
Lemma cA0_Split : forall m x x' z,
   let m1:= Split m one x x' in
  inv_hmap m -> exd m x -> x <> x' -> expv m x x' -> exd m z -> 
       cA m1 zero z = cA m zero z.
Proof.
   intros. unfold m1. 
   rewrite cA_Split. 
   elim (eq_dim_dec one zero). intro. discriminate a. 
   tauto. tauto. unfold crack. unfold crackv. 
    unfold MA1.crack. 
  elim (eq_dim_dec one zero). intro. discriminate a. 
     tauto. 
Qed.

Lemma cA0_Merge : forall m x y z,
   let m1:= Merge m one x y in
  inv_hmap m -> exd m x -> exd m z -> 
       cA m1 zero z = cA m zero z.
Proof.
   intros. unfold m1. 
   rewrite cA_Merge. 
   elim (eq_dim_dec one zero). intro. discriminate a. 
   tauto. tauto. 
Qed.
*)






*)
