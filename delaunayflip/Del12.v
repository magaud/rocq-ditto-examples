(*=====================================================
=======================================================
                 TOPOLOGICAL FMAPS, HMAPS -
                 WITH TAGS AND EMBEDDINGS
                      
           PART 12: GLUEING AND MERGING
          
            DEFINITIONS, OPERATIONS AND PROPERTIES:
              GLUEING, MERGING TWO k-ORBITS


=======================================================
=====================================================*)

Require Export Del11.

(*==================================================
    USE MTr TO PROVE THE PROPERTIES OF G(LUEING).
==================================================*)

(*==================================================
        top_Shift_bis, bottom_Shift_bis
===================================================*)

Lemma bottom_Shift0_bis: 
 forall(m:fmap)(x z:dart)(H:inv_hmap m), 
  succ m zero x -> exd m z ->
  bottom (Shift m zero x) zero z = 
    if expe_dec m x z H then (A m zero x) 
    else bottom m zero z.
Proof.
intros.
assert (exd m x).
 apply succ_exd with zero.
   tauto.
  tauto.
assert (exd m (top m zero x)).
 generalize (exd_top m zero x).
    tauto.
assert (x <> top m zero x).
 intro.
   rewrite H4 in H0.
    absurd (succ m zero (top m zero x)).
  apply not_succ_top.
     tauto.
  tauto.
unfold Shift in |- *.
  simpl in |- *.
  set (m0 := B m zero x) in |- *.
  set (bx0 := bottom m zero x) in |- *.
  elim (eq_dart_dec x z).
 intros.
   rewrite <- a in |- *.
   unfold m0 in |- *.
   rewrite bottom_B in |- *.
  fold bx0 in |- *.
    elim (eq_dart_dec bx0 bx0).
   intros.
     generalize (MA0.between_bottom_B_bis m x 
       (top m zero x) H H3 H2 H4).
     simpl in |- *.
     rewrite bottom_top_bottom in |- *.
    intros.
      decompose [and] H5.
      clear H5.
      elim (expe_dec m x x H).
     intro.
       apply H6.
       apply MA0.between_bottom_x_top.
       tauto.
      tauto.
    intros.
      elim b.
      apply MA0.MfcA.expo_refl.
       tauto.
    tauto.
    tauto.
   tauto.
  tauto.
  tauto.
unfold m0 in |- *.
  intro.
  generalize (bottom_Shift0 m x z H H0 H1 b).
  unfold Shift in |- *.
  simpl in |- *.
  fold bx0 in |- *.
   tauto.
Qed.

(* OK: *)

Lemma bottom_Shift1_bis: 
 forall(m:fmap)(x z:dart)(H:inv_hmap m), 
  succ m one x -> exd m z ->
  bottom (Shift m one x) one z = 
    if expv_dec m x z H then (A m one x) 
    else bottom m one z.
Proof.
intros.
assert (exd m x).
 apply succ_exd with one.
   tauto.
  tauto.
assert (exd m (top m one x)).
 generalize (exd_top m one x).
    tauto.
assert (x <> top m one x).
 intro.
   rewrite H4 in H0.
    absurd (succ m one (top m one x)).
  apply not_succ_top.
     tauto.
  tauto.
unfold Shift in |- *.
  simpl in |- *.
  set (m0 := B m one x) in |- *.
  set (bx0 := bottom m one x) in |- *.
  elim (eq_dart_dec x z).
 intros.
   rewrite <- a in |- *.
   unfold m0 in |- *.
   rewrite bottom_B in |- *.
  fold bx0 in |- *.
    elim (eq_dart_dec bx0 bx0).
   intros.
     generalize (MA1.between_bottom_B_bis m x 
       (top m one x) H H3 H2 H4).
     simpl in |- *.
     rewrite bottom_top_bottom in |- *.
    intros.
      decompose [and] H5.
      clear H5.
      elim (expv_dec m x x H).
     intro.
       apply H6.
       apply MA1.between_bottom_x_top.
       tauto.
      tauto.
    intros.
      elim b.
      apply MA1.MfcA.expo_refl.
       tauto.
    tauto.
    tauto.
   tauto.
  tauto.
  tauto.
unfold m0 in |- *.
  intro.
  generalize (bottom_Shift1 m x z H H0 H1 b).
  unfold Shift in |- *.
  simpl in |- *.
  fold bx0 in |- *.
   tauto.
Qed.

(* OK: *)

Lemma top_Shift0_bis:
 forall(m:fmap)(x z:dart)(H:inv_hmap m),
 succ m zero x -> exd m z -> 
   top (Shift m zero x) zero z =
     if expe_dec m x z H then x 
     else top m zero z.
Proof.
intros.
assert (exd m x).
 apply succ_exd with zero.
   tauto.
  tauto.
assert (exd m (bottom m zero x)).
 generalize (exd_bottom m zero x).
    tauto.
assert (x <> top m zero x).
 intro.
   rewrite H4 in H0.
    absurd (succ m zero (top m zero x)).
  apply not_succ_top.
     tauto.
  tauto.
unfold Shift in |- *.
  simpl in |- *.
  set (m0 := B m zero x) in |- *.
  set (tx0 := top m zero x) in |- *.
  elim (eq_dart_dec x z).
 intro.
   rewrite <- a in |- *.
   unfold m0 in |- *.
   rewrite top_B in |- *.
  elim (eq_dart_dec tx0 x).
   unfold tx0 in |- *.
     intro.
     symmetry  in a0.
      tauto.
  elim (expe_dec m x x H).
    tauto.
  intros.
    elim b.
    apply MA0.MfcA.expo_refl.
     tauto.
  tauto.
  tauto.
intro.
  generalize (top_Shift0 m x z H H0 H1 b).
  unfold Shift in |- *.
  simpl in |- *.
  unfold tx0 in |- *.
   tauto.
Qed.

(* OK: *)

Lemma top_Shift1_bis:
 forall(m:fmap)(x z:dart)(H:inv_hmap m),
 succ m one x -> exd m z -> 
   top (Shift m one x) one z =
     if expv_dec m x z H then x 
     else top m one z.
Proof.
intros.
assert (exd m x).
 apply succ_exd with one.
   tauto.
  tauto.
assert (exd m (bottom m one x)).
 generalize (exd_bottom m one x).
    tauto.
assert (x <> top m one x).
 intro.
   rewrite H4 in H0.
    absurd (succ m one (top m one x)).
  apply not_succ_top.
     tauto.
  tauto.
unfold Shift in |- *.
  simpl in |- *.
  set (m0 := B m one x) in |- *.
  set (tx0 := top m one x) in |- *.
  elim (eq_dart_dec x z).
 intro.
   rewrite <- a in |- *.
   unfold m0 in |- *.
   rewrite top_B in |- *.
  elim (eq_dart_dec tx0 x).
   unfold tx0 in |- *.
     intro.
     symmetry  in a0.
      tauto.
  elim (expv_dec m x x H).
    tauto.
  intros.
    elim b.
    apply MA1.MfcA.expo_refl.
     tauto.
  tauto.
  tauto.
intro.
  generalize (top_Shift1 m x z H H0 H1 b).
  unfold Shift in |- *.
  simpl in |- *.
  unfold tx0 in |- *.
   tauto.
Qed.

(*====================================================
       G(LUEING) TWO k-ORBITS, FOR x AND y
            WITH precondition ~pred m y
=====================================================*)

(* PRECONDITION : x AND y ARE IN DIFFERENT k-ORBITS
AND y HAS NO k-PREDECESSOR *)

Definition G(m:fmap)(k:dim)(x y:dart):=
 let m0:= if succ_dec m k x then Shift m k x else m in
  L m0 k x y.

(* OK: *)

Lemma exd_G: forall(m:fmap)(k:dim)(x y z:dart),
  exd m z <-> exd (G m k x y) z.
Proof.
intros.
unfold G in |- *.
elim (succ_dec m k x).
 simpl in |- *.
   generalize (exd_B m k x z).
    tauto.
simpl in |- *.
tauto.
Qed.

Lemma exd_G_bis: forall(m:fmap)(k:dim)(x y z:dart),
  inv_hmap m -> (exd m z <-> exd (G m k x y) z).
Proof. intros. apply exd_G. Qed.

(* OK: *)

Lemma A_G: forall(m:fmap)(k:dim)(x y z:dart),
 inv_hmap m -> exd m x -> 
  A (G m k x y) k z = 
    if eq_dart_dec x z then y
    else if eq_dart_dec (top m k x) z 
         then bottom m k x
         else A m k z.
Proof.
intros.
unfold G in |- *.
unfold Shift in |- *.
simpl in |- *.
elim (eq_dim_dec k k).
 elim (succ_dec m k x).
  simpl in |- *.
    elim (eq_dim_dec k k).
   intros.
     clear a a1.
     elim (eq_dart_dec x z).
     tauto.
   intro.
     rewrite A_B_bis in |- *.
     tauto.
   intro.
     symmetry in H1.
      tauto.
   tauto.
 elim (eq_dart_dec x z).
   tauto.
 intros.
   elim (eq_dart_dec (top m k x) z).
  intro.
    assert (top m k x = x).
   apply nosucc_top.
  tauto.
  tauto.
    tauto.
  rewrite H1 in a0.
     tauto.
  tauto.
 tauto.
Qed.

(* OK: *)

Lemma A_1_G: forall(m:fmap)(k:dim)(x y z:dart),
 inv_hmap m -> exd m x -> 
  A_1 (G m k x y) k z = 
    if eq_dart_dec y z then x
    else if eq_dart_dec (cA m k x) z then nil 
         else if eq_dart_dec (bottom m k x) z 
              then top m k x
              else A_1 m k z.
Proof.
intros.
unfold G in |- *.
simpl in |- *.
elim (eq_dim_dec k k).
 intro.
   elim (succ_dec m k x).
  intro.
    rewrite A_1_Shift in |- *.
   assert (cA m k x = A m k x).
    rewrite cA_eq in |- *.
     elim (succ_dec m k x).
       tauto.
      tauto.
     tauto.
   rewrite H1 in |- *.
      tauto.
   tauto.
   tauto.
 intro.
   elim (eq_dart_dec y z).
   tauto.
 elim (eq_dart_dec (cA m k x) z).
  intros.
    generalize a0.
    clear a0.
    rewrite cA_eq in |- *.
   elim (succ_dec m k x).
     tauto.
   intros.
     rewrite <- a0 in |- *.
     generalize (not_pred_bottom m k x).
     unfold pred in |- *.
     intros.
     generalize 
   (eq_dart_dec (A_1 m k (bottom m k x)) nil).
      tauto.
   tauto.
 elim (eq_dart_dec (bottom m k x) z).
  intros.
    elim b0.
    rewrite cA_eq in |- *.
   elim (succ_dec m k x).
     tauto.
    tauto.
   tauto.
  tauto.
 tauto.
Qed.

(* OK: *)

Lemma A_G_ter: forall(m:fmap)(k:dim)(x y z:dart),
 inv_hmap m ->
  A (G m k x y) (dim_opp k) z = A m (dim_opp k) z.
Proof.
simpl in |- *.
intros.
elim (eq_dim_dec k (dim_opp k)).
 elim k.
  simpl in |- *.
    intro.
    inversion a.
 simpl in |- *.
   intro.
   inversion a.
intro.
  elim (succ_dec m k x).
 intro.
   rewrite A_Shift_ter in |- *.
   tauto.
  tauto.
  tauto.
 tauto.
Qed.

(* OK: *)

Lemma A_1_G_ter: forall(m:fmap)(k:dim)(x y z:dart),
 inv_hmap m ->
  A_1 (G m k x y) (dim_opp k) z = 
       A_1 m (dim_opp k) z.
Proof.
simpl in |- *.
intros.
elim (eq_dim_dec k (dim_opp k)).
 elim k.
  simpl in |- *.
    intro.
    inversion a.
 simpl in |- *.
   intro.
   inversion a.
intro.
  elim (succ_dec m k x).
 intro.
   rewrite A_1_Shift_ter in |- *.
   tauto.
  tauto.
  tauto.
 tauto.
Qed.

(* OK: *)

Lemma cA_G: forall(m:fmap)(k:dim)(x y z:dart),
 inv_hmap m ->
  cA (G m k x y) k z = 
    if eq_dart_dec x z then y
    else if eq_dart_dec (cA_1 m k y) z then cA m k x
         else cA m k z.
Proof.
intros.
unfold G in |- *.
simpl in |- *.
elim (eq_dim_dec k k).
 elim (succ_dec m k x).
  intros.
    clear a0.
    rewrite cA_1_Shift in |- *.
   rewrite cA_Shift in |- *.
    rewrite cA_Shift in |- *.
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

Lemma cA_1_G: forall(m:fmap)(k:dim)(x y z:dart),
 inv_hmap m ->
  cA_1 (G m k x y) k z = 
    if eq_dart_dec y z then x
    else if eq_dart_dec (cA m k x) z then cA_1 m k y
         else cA_1 m k z.
Proof.
intros.
unfold G in |- *.
simpl in |- *.
elim (eq_dim_dec k k).
 elim (succ_dec m k x).
  intros.
    clear a0.
    rewrite cA_Shift in |- *.
   rewrite cA_1_Shift in |- *.
    rewrite cA_1_Shift in |- *.
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

Lemma cA_G_ter: forall(m:fmap)(k:dim)(x y z:dart),
 inv_hmap m ->
  cA (G m k x y) (dim_opp k) z = cA m (dim_opp k) z.
Proof.
intros.
unfold G in |- *.
simpl in |- *.
elim (eq_dim_dec k (dim_opp k)).
 induction k.
  simpl in |- *.
    intro.
    inversion a.
 simpl in |- *.
   intro.
   inversion a.
elim (succ_dec m k x).
 intros.
   rewrite cA_Shift_ter in |- *.
   tauto.
  tauto.
  tauto.
 tauto.
Qed.

(* OK: *)

Lemma cA_1_G_ter: forall(m:fmap)(k:dim)(x y z:dart),
 inv_hmap m ->
  cA_1 (G m k x y) (dim_opp k) z = 
     cA_1 m (dim_opp k) z.
Proof.
intros.
unfold G in |- *.
simpl in |- *.
elim (eq_dim_dec k (dim_opp k)).
 induction k.
  simpl in |- *.
    intro.
    inversion a.
 simpl in |- *.
   intro.
   inversion a.
elim (succ_dec m k x).
 intros.
   rewrite cA_1_Shift_ter in |- *.
   tauto.
  tauto.
  tauto.
 tauto.
Qed.

(* OK: *)

Lemma inv_hmap_G_aux: 
forall(m:fmap)(k:dim)(x y:dart),
 inv_hmap m -> exd m x -> exd m y -> 
   ~pred m k y -> bottom m k x <> y ->
      inv_hmap (G m k x y).
Proof.
intros.
unfold G in |- *.
simpl in |- *.
elim (succ_dec m k x).
 intro.
   split.
  apply inv_hmap_Shift.
    tauto.
   tauto.
 unfold prec_L in |- *.
   split.
  generalize (exd_Shift m k x x).
     tauto.
 split.
  generalize (exd_Shift m k x y).
     tauto.
 split.
  unfold succ in |- *.
    rewrite A_Shift in |- *.
   elim (eq_dart_dec x x).
     tauto.
    tauto.
   tauto.
   tauto.
 split.
  unfold pred in |- *.
    rewrite A_1_Shift in |- *.
   elim (eq_dart_dec (A m k x) y).
     tauto.
   intro.
     elim (eq_dart_dec (bottom m k x) y).
     tauto.
   intros.
     unfold pred in H2.
      tauto.
   tauto.
   tauto.
 rewrite cA_Shift in |- *.
  rewrite cA_eq in |- *.
   elim (succ_dec m k x).
    intro.
      clear a0.
      intro.
      rewrite <- H4 in H2.
      unfold pred in H2.
      rewrite A_1_A in H2.
     elim H2.
       apply exd_not_nil with m.
       tauto.
      tauto.
     tauto.
     tauto.
    tauto.
   tauto.
  tauto.
  tauto.
split.
  tauto.
assert (cA m k x <> y).
 rewrite cA_eq in |- *.
  elim (succ_dec m k).
    tauto.
   tauto.
  tauto.
unfold prec_L in |-*.
 tauto.
Qed.

Lemma inv_hmap_G0: forall(m:fmap)(x y:dart),
 inv_hmap m -> exd m x -> exd m y -> 
   ~pred m zero y -> ~expe m x y ->
      inv_hmap (G m zero x y).
Proof.
intros.
assert (bottom m zero x <> y).
 intro.
   elim H3.
   rewrite <- H4 in |- *.
   apply expe_symm.
   tauto.
 apply MA0.expo_bottom_z.
   tauto.
  tauto.
apply (inv_hmap_G_aux m zero x y H H0 H1 H2 H4). 
Qed.

Lemma inv_hmap_G1: forall(m:fmap)(x y:dart),
 inv_hmap m -> exd m x -> exd m y -> 
   ~pred m one y -> ~expv m x y ->
      inv_hmap (G m one x y).
Proof.
intros.
assert (bottom m one x <> y).
 intro.
   elim H3.
   rewrite <- H4 in |- *.
   apply expv_symm.
   tauto.
 apply MA1.expo_bottom_z.
   tauto.
  tauto.
apply (inv_hmap_G_aux m one x y H H0 H1 H2 H4). 
Qed.

Lemma ndN_G: forall(m:fmap)(k:dim)(x y:dart), 
  ndN (G m k x y) = ndN m.
Proof.
intros.
unfold G in |- *.
simpl in |- *.
elim (succ_dec m k x).
 unfold Shift in |- *.
   simpl in |- *.
   rewrite ndN_B in |- *.
    tauto.
 tauto.
Qed.

Lemma top_G0:
 forall(m:fmap)(x y z:dart)(H :inv_hmap m) ,
  exd m x -> exd m y -> exd m z ->
   ~ expe m x y -> ~pred m zero y -> 
  let y_0:= cA_1 m zero y in
  top (G m zero x y) zero z = 
    if expe_dec m x z H then y_0
    else if expe_dec m y z H then y_0
         else top m zero z.
Proof.
intros.
unfold G in |- *.
simpl in |- *.
elim (succ_dec m zero x).
 intro.
   rewrite (top_Shift0_bis m x z H a H2) in |- *.
   rewrite (top_Shift0_bis m x y H a H1) in |- *.
   elim (expe_dec m x y H).
   tauto.
 elim (expe_dec m x z H).
  elim (eq_dart_dec x x).
   intros.
     unfold y_0 in |- *.
     rewrite cA_1_eq in |- *.
    elim (pred_dec m zero y).
      tauto.
     tauto.
    tauto.
   tauto.
 intros.
   elim (eq_dart_dec x (top m zero z)).
  intro.
    elim b.
    rewrite a0 in |- *.
    apply MA0.expo_top_z.
    tauto.
   tauto.
 elim (expe_dec m y z H).
  intro.
    intro.
    assert (y_0 = top m zero y).
   unfold y_0 in |- *; rewrite cA_1_eq in |- *.
    elim (pred_dec m zero y).
      tauto.
     tauto.
    tauto.
  rewrite H5 in |- *.
    apply expe_top.
    tauto.
  apply expe_symm.
    tauto.
   tauto.
  tauto.
intro.
  elim (eq_dart_dec x (top m zero z)).
 intro.
   elim (expe_dec m x z H).
  intro.
    unfold y_0 in |- *; rewrite cA_1_eq in |- *.
   elim (pred_dec m zero y).
     tauto.
    tauto.
   tauto.
 intro.
   elim b0; rewrite a in |- *.
   apply MA0.expo_top_z.
   tauto.
  tauto.
elim (expe_dec m x z H).
 intros.
   assert (x = top m zero x).
  rewrite nosucc_top in |- *.
    tauto.
   tauto.
   tauto.
   tauto.
 elim b0.
   rewrite H5 in |- *.
   apply MA0.expo_top.
   tauto.
  tauto.
elim (expe_dec m y z H).
 intros.
   assert (y_0 = top m zero y).
  unfold y_0 in |- *; rewrite cA_1_eq in |- *.
   elim (pred_dec m zero y).
     tauto.
    tauto.
   tauto.
 rewrite H5 in |- *.
   apply MA0.expo_top.
   tauto.
 apply MA0.MfcA.expo_symm.
   tauto.
  tauto.
 tauto.
Qed.

Lemma top_G1: 
 forall(m:fmap)(x y z:dart)(H :inv_hmap m) ,
  exd m x -> exd m y -> exd m z ->
   ~ expv m x y -> ~pred m one y -> 
  let y_1:= cA_1 m one y in
  top (G m one x y) one z = 
    if expv_dec m x z H then y_1
    else if expv_dec m y z H then y_1
         else top m one z.
Proof.
intros.
unfold G in |- *.
simpl in |- *.
elim (succ_dec m one x).
 intro.
   rewrite (top_Shift1_bis m x z H a H2) in |- *.
   rewrite (top_Shift1_bis m x y H a H1) in |- *.
   elim (expv_dec m x y H).
   tauto.
 elim (expv_dec m x z H).
  elim (eq_dart_dec x x).
   intros.
     unfold y_1 in |- *.
     rewrite cA_1_eq in |- *.
    elim (pred_dec m one y).
      tauto.
     tauto.
    tauto.
   tauto.
 intros.
   elim (eq_dart_dec x (top m one z)).
  intro.
    elim b.
    rewrite a0 in |- *.
    apply MA1.expo_top_z.
    tauto.
   tauto.
 elim (expv_dec m y z H).
  intro.
    intro.
    assert (y_1 = top m one y).
   unfold y_1 in |- *; rewrite cA_1_eq in |- *.
    elim (pred_dec m one y).
      tauto.
     tauto.
    tauto.
  rewrite H5 in |- *.
    apply expv_top.
    tauto.
  apply expv_symm.
    tauto.
   tauto.
  tauto.
intro.
  elim (eq_dart_dec x (top m one z)).
 intro.
   elim (expv_dec m x z H).
  intro.
    unfold y_1 in |- *; rewrite cA_1_eq in |- *.
   elim (pred_dec m one y).
     tauto.
    tauto.
   tauto.
 intro.
   elim b0; rewrite a in |- *.
   apply MA1.expo_top_z.
   tauto.
  tauto.
elim (expv_dec m x z H).
 intros.
   assert (x = top m one x).
  rewrite nosucc_top in |- *.
    tauto.
   tauto.
   tauto.
   tauto.
 elim b0.
   rewrite H5 in |- *.
   apply MA1.expo_top.
   tauto.
  tauto.
elim (expv_dec m y z H).
 intros.
   assert (y_1 = top m one y).
  unfold y_1 in |- *; rewrite cA_1_eq in |- *.
   elim (pred_dec m one y).
     tauto.
    tauto.
   tauto.
 rewrite H5 in |- *.
   apply MA1.expo_top.
   tauto.
 apply MA1.MfcA.expo_symm.
   tauto.
  tauto.
 tauto.
Qed.

Lemma bottom_G0: 
 forall(m:fmap)(x y z:dart)(H :inv_hmap m) ,
  exd m x -> exd m y -> exd m z ->
   ~ expe m x y -> ~pred m zero y -> 
  let x0:= cA m zero x in
  bottom (G m zero x y) zero z = 
    if expe_dec m x z H then x0
    else if expe_dec m y z H then x0
         else bottom m zero z.
Proof.
intros.
assert (bottom m zero y = y).
 apply nopred_bottom.
   tauto.
  tauto.
  tauto.
unfold G in |- *.
  simpl in |- *.
  elim (succ_dec m zero x).
 intro.
   rewrite (bottom_Shift0_bis m x z H a H2) in |- *.
   rewrite (bottom_Shift0_bis m x x H a H0) in |- *.
   elim (expe_dec m x x H).
  intros.
    elim (expe_dec m x z H).
   assert (x0 = A m zero x).
    unfold x0 in |- *; rewrite cA_eq in |- *.
     elim (succ_dec m zero x).
       tauto.
      tauto.
     tauto.
   rewrite <- H6 in |- *.
     elim (eq_dart_dec y x0).
     tauto.
    tauto.
  elim (eq_dart_dec y (bottom m zero z)).
   elim (expe_dec m y z H).
    unfold x0 in |- *; rewrite cA_eq in |- *.
     elim (succ_dec m zero x).
       tauto.
      tauto.
     tauto.
   intros.
     elim b.
     rewrite a1 in |- *.
     apply MA0.expo_bottom_z.
     tauto.
    tauto.
  elim (expe_dec m y z H).
   intros.
     elim b.
     rewrite <- H5 in |- *.
     apply expe_bottom.
     tauto.
    tauto.
   tauto.
 intro.
   elim b.
   apply MA0.MfcA.expo_refl.
    tauto.
intros.
  assert (x0 = bottom m zero x).
 unfold x0 in |- *.
   rewrite cA_eq in |- *.
  elim (succ_dec m zero x).
    tauto.
   tauto.
  tauto.
elim (eq_dart_dec y (bottom m zero z)).
 elim (expe_dec m x z H).
  intros.
    elim H3.
    apply expe_trans with z.
    tauto.
  rewrite a0 in |- *.
    apply MA0.MfcA.expo_symm.
    tauto.
  apply MA0.expo_bottom_z.
    tauto.
   tauto.
 intros.
   elim (expe_dec m y z H).
  intros.
    symmetry  in |- *.
     tauto.
 intros.
   elim b1.
   rewrite a in |- *.
   apply MA0.expo_bottom_z.
   tauto.
  tauto.
elim (expe_dec m x z H).
 intros.
   rewrite H6 in |- *.
   symmetry  in |- *.
   apply expe_bottom.
   tauto.
  tauto.
elim (expe_dec m y z H).
 intros.
   elim b1.
   rewrite <- H5 in |- *.
   apply expe_bottom.
   tauto.
  tauto.
 tauto.
Qed.

Lemma bottom_G1: 
 forall(m:fmap)(x y z:dart)(H :inv_hmap m) ,
  exd m x -> exd m y -> exd m z ->
   ~ expv m x y -> ~pred m one y -> 
  let x1:= cA m one x in
  bottom (G m one x y) one z = 
    if expv_dec m x z H then x1
    else if expv_dec m y z H then x1
         else bottom m one z.
Proof.
intros.
assert (bottom m one y = y).
 apply nopred_bottom.
   tauto.
  tauto.
  tauto.
unfold G in |- *.
  simpl in |- *.
  elim (succ_dec m one x).
 intro.
   rewrite (bottom_Shift1_bis m x z H a H2) in |- *.
   rewrite (bottom_Shift1_bis m x x H a H0) in |- *.
   elim (expv_dec m x x H).
  intros.
    elim (expv_dec m x z H).
   assert (x1 = A m one x).
    unfold x1 in |- *; rewrite cA_eq in |- *.
     elim (succ_dec m one x).
       tauto.
      tauto.
     tauto.
   rewrite <- H6 in |- *.
     elim (eq_dart_dec y x1).
     tauto.
    tauto.
  elim (eq_dart_dec y (bottom m one z)).
   elim (expv_dec m y z H).
    unfold x1 in |- *; rewrite cA_eq in |- *.
     elim (succ_dec m one x).
       tauto.
      tauto.
     tauto.
   intros.
     elim b.
     rewrite a1 in |- *.
     apply MA1.expo_bottom_z.
     tauto.
    tauto.
  elim (expv_dec m y z H).
   intros.
     elim b.
     rewrite <- H5 in |- *.
     apply expv_bottom.
     tauto.
    tauto.
   tauto.
 intro.
   elim b.
   apply MA1.MfcA.expo_refl.
    tauto.
intros.
  assert (x1 = bottom m one x).
 unfold x1 in |- *.
   rewrite cA_eq in |- *.
  elim (succ_dec m one x).
    tauto.
   tauto.
  tauto.
elim (eq_dart_dec y (bottom m one z)).
 elim (expv_dec m x z H).
  intros.
    elim H3.
    apply expv_trans with z.
    tauto.
  rewrite a0 in |- *.
    apply MA1.MfcA.expo_symm.
    tauto.
  apply MA1.expo_bottom_z.
    tauto.
   tauto.
 intros.
   elim (expv_dec m y z H).
  intros.
    symmetry  in |- *.
     tauto.
 intros.
   elim b1.
   rewrite a in |- *.
   apply MA1.expo_bottom_z.
   tauto.
  tauto.
elim (expv_dec m x z H).
 intros.
   rewrite H6 in |- *.
   symmetry  in |- *.
   apply expv_bottom.
   tauto.
  tauto.
elim (expv_dec m y z H).
 intros.
   elim b1.
   rewrite <- H5 in |- *.
   apply expv_bottom.
   tauto.
  tauto.
 tauto.
Qed.

Lemma ne_G0 : 
 forall(m:fmap)(x y:dart), 
  inv_hmap m -> 
   ne (G m zero x y) = ne m - 1. 
Proof.
unfold G in |- *.
simpl in |- *.
intros.
elim (succ_dec m zero x).
 intro.
 rewrite ne_Shift0 in |- *.
   tauto.
  tauto.
tauto.
tauto.
Qed.


(* NOUVEAU: *)

Lemma ne_G1 : forall(m:fmap)(x y:dart), 
  inv_hmap m ->  
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

Lemma nv_G0 : forall(m:fmap)(x y:dart), 
  inv_hmap m -> 
   nv (G m zero x y) = nv m. 
Proof.
intros.
unfold G in |- *.
simpl in |- *.
elim (succ_dec m zero x).
 intro.
 rewrite nv_Shift0 in |- *.
   tauto.
  tauto.
tauto.
tauto.
Qed.

Lemma nv_G1 : 
 forall(m:fmap)(x y:dart), 
  inv_hmap m -> 
   nv (G m one x y) = nv m - 1. 
Proof.
unfold G in |- *.
simpl in |- *.
intros.
elim (succ_dec m one x).
 intro.
 rewrite nv_Shift1 in |- *.
   tauto.
  tauto.
tauto.
tauto.
Qed.

(*====================================================
                 k-ORBITS FOR G
    INSTANTIATIONS OF MTr WITH Tr = Gk, G0, G1
            WRT TO  cAk, cA0, cA1 
=====================================================*)

Lemma cA_Gk:forall(m:fmap)(k:dim)(x y z:dart), 
 True -> 
  inv_hmap m -> exd m x -> exd m y -> exd m z -> 
  cA (G m k x y) k z =  
     if eq_dart_dec x z then y
     else if eq_dart_dec (cA_1 m k y) z 
          then cA m k x 
          else cA m k z.
Proof. intros. apply cA_G. tauto. Qed.

Lemma cA_1_Gk:forall(m:fmap)(k:dim)(x y z:dart), 
 True -> 
  inv_hmap m -> exd m x -> exd m y -> exd m z -> 
  cA_1 (G m k x y) k z =
    if eq_dart_dec y z then x
    else if eq_dart_dec (cA m k x) z then cA_1 m k y 
         else cA_1 m k z.
Proof. intros. apply cA_1_G. tauto. Qed.

Module ModcAG(Md:Sigd)<:SigTr 
 with Definition Tr:=fun(m:fmap)(x y:dart) => 
    G m Md.kd x y
 with Definition Prec_Tr:=fun(m:fmap)(x y:dart) =>
    True.
Module M := McA Md.    (* : Sigf *)
Definition Tr(m:fmap)(x y:dart):= G m Md.kd x y.
Definition Prec_Tr(m:fmap)(x y:dart):= True.
Definition f_Tr(m:fmap):= cA_Gk m Md.kd.
Definition f_1_Tr(m:fmap):= cA_1_Gk m Md.kd.
Definition exd_Tr(m:fmap):= exd_G_bis m Md.kd.
Definition ndN_Tr(m:fmap):= ndN_G m Md.kd.
End ModcAG.

(*===================================================
   INSTANTIATIONS FOR Tr = L0, L1 WRT TO cA0, cA1
====================================================*)

(* IMMEDIATE: *)

Module ModcAG0 := ModcAG Md0.
Module MG0Tr := MTr ModcAG0.

Module ModcAG1 := ModcAG Md1.
Module MG1Tr := MTr ModcAG1.

(*==================================================
         DIMENSION 0: expe_G0, degreee_G0
             (MERGE ONLY)
===================================================*)

(* OK: *)

Theorem expe_G0_CNS:
 forall (m:fmap)(x y z t:dart)(H:inv_hmap m),
   exd m x -> exd m y -> exd m z -> 
    ~ pred m zero y -> ~ expe m x y -> 
     let m1 := G m zero x y in
      (expe m1 z t <->
         expe m z t \/
         expe m x z /\ expe m y t \/
         expe m x t /\ expe m y z).
Proof.
intros.
assert (inv_hmap m1).
 unfold m1 in |- *.
   apply (inv_hmap_G0 m x y H H0 H1 H3 H4).
assert (ModcAG0.Prec_Tr m x y).
 unfold ModcAG0.Prec_Tr in |- *.
    tauto.
generalize (MG0Tr.expo_Tr_CNS m x y z t H H6 H0 H1 H2 H5).
  elim (MG0Tr.MfM.expo_dec m x y H).
  tauto.
intro.
   tauto.
Qed.

Open Scope nat_scope.

(* OK: *)

Theorem degreee_G0_merge:
 forall (m:fmap)(x y:dart)(H:inv_hmap m),
   exd m x -> exd m y ->
    ~ pred m zero y -> ~ expe m x y -> 
     let m1 := G m zero x y in
      degreee m1 y = degreee m y + degreee m x.
Proof.
intros.
assert (ModcAG0.Prec_Tr m x y).
 unfold ModcAG0.Prec_Tr in |- *.
    tauto.
unfold m1 in |- *.
  assert (degreee = MG0Tr.MfM.degree).
  tauto.
rewrite H5 in |- *.
  assert (m1 = ModcAG0.Tr m x y).
 unfold m1 in |- *.
    tauto.
unfold m1 in H6.
  rewrite H6 in |- *.
  apply MG0Tr.degree_Tr_merge_y.
  tauto.
 tauto.
 tauto.
 tauto.
 tauto.
Qed.

(*==================================================
         DIMENSION 1: expe_G1, degreee_G1
                (MERGE ONLY)
===================================================*)

(* OK: *)

Theorem expv_G1_CNS:
 forall (m:fmap)(x y z t:dart)(H:inv_hmap m),
   exd m x -> exd m y -> exd m z -> 
    ~ pred m one y -> ~ expv m x y -> 
     let m1 := G m one x y in
      (expv m1 z t <->
         expv m z t \/
         expv m x z /\ expv m y t \/
         expv m x t /\ expv m y z).
Proof.
intros.
assert (inv_hmap m1).
 unfold m1 in |- *.
   apply (inv_hmap_G1 m x y H H0 H1 H3 H4).
assert (ModcAG1.Prec_Tr m x y).
 unfold ModcAG1.Prec_Tr in |- *.
    tauto.
generalize (MG1Tr.expo_Tr_CNS m x y z t H H6 H0 H1 H2 H5).
  elim (MG1Tr.MfM.expo_dec m x y H).
  tauto.
intro.
   tauto.
Qed.

(* OK: *)

Theorem degreev_G1_merge:
 forall (m:fmap)(x y:dart)(H:inv_hmap m),
   exd m x -> exd m y ->
    ~ pred m one y -> ~ expv m x y -> 
     let m1 := G m one x y in
      degreev m1 y = degreev m y + degreev m x.
Proof.
intros.
assert (ModcAG1.Prec_Tr m x y).
 unfold ModcAG1.Prec_Tr in |- *.
    tauto.
unfold m1 in |- *.
  assert (degreev = MG1Tr.MfM.degree).
  tauto.
rewrite H5 in |- *.
  assert (m1 = ModcAG1.Tr m x y).
 unfold m1 in |- *.
    tauto.
unfold m1 in H6.
  rewrite H6 in |- *.
  apply MG1Tr.degree_Tr_merge_y.
  tauto.
 tauto.
 tauto.
 tauto.
 tauto.
Qed.

(* =================================================
                 FACES / G0, G1  
===================================================*)
(* OK: *)

Lemma cF_G0 : forall(m:fmap)(x y z:dart), 
 inv_hmap m -> 
  cF (G m zero x y) z = 
    if eq_dart_dec y z then cA_1 m one x
    else if eq_dart_dec (cA m zero x) z 
         then cF m y else cF m z.
Proof.
unfold G in |- *.
intros.
elim (succ_dec m zero x).
 intro.
   rewrite cF_L in |- *.
   elim (eq_dim_dec zero zero).
  intro.
    rewrite cA_1_Shift in |- *.
   rewrite cA_1_Shift in |- *.
    rewrite cA_Shift in |- *.
     assert (one = dim_opp zero).
      simpl in |- *.
         tauto.
     rewrite H0 in |- *.
       rewrite cA_1_Shift_ter in |- *.
      simpl in |- *.
        elim (eq_dart_dec y z).
        tauto.
      elim (eq_dart_dec (cA m zero x) z).
       fold (cF m y) in |- *.
          tauto.
      fold (cF m z) in |- *.
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
  intro.
  rewrite cF_L in |- *.
  elim (eq_dim_dec zero zero).
   elim (eq_dart_dec y z).
   tauto.
 elim (eq_dart_dec (cA m zero x) z).
  fold (cF m y) in |- *.
     tauto.
 fold (cF m z) in |- *.
    tauto.
 tauto.
Qed.

Lemma cF_1_G0 : forall(m:fmap)(x y z:dart), 
 inv_hmap m -> exd m x -> exd m y -> exd m z ->
  cF_1 (G m zero x y) z = 
    if eq_dart_dec (cA_1 m one x) z then y
    else if eq_dart_dec (cF m y) z 
         then (cA m zero x) else cF_1 m z.
Proof.
intros.
unfold G in |- *.
elim (succ_dec m zero x).
 intro.
   rewrite cF_1_L0 in |- *.
   rewrite cA_Shift in |- *.
  rewrite cA_Shift in |- *.
   assert (one = dim_opp zero).
    simpl in |- *.
       tauto.
   rewrite H3 in |- *.
     rewrite cA_Shift_ter in |- *.
    rewrite <- H3 in |- *.
      rewrite cA_1_Shift in |- *.
     elim (eq_dart_dec x (cA m one z)).
      elim (eq_dart_dec (cA_1 m one x) z).
        tauto.
      intros.
        elim b.
        rewrite a0 in |- *.
        rewrite cA_1_cA in |- *.
        tauto.
       tauto.
       tauto.
     elim (eq_dart_dec (cA_1 m one x) z).
      intros.
        elim b.
        rewrite <- a0 in |- *.
        rewrite cA_cA_1 in |- *.
        tauto.
       tauto.
       tauto.
     elim (eq_dart_dec (cA_1 m zero y) (cA m one z)).
      elim (eq_dart_dec (cF m y) z).
        tauto.
      intros.
        elim b.
        unfold cF in |- *.
        rewrite a0 in |- *.
        rewrite cA_1_cA in |- *.
        tauto.
       tauto.
       tauto.
     elim (eq_dart_dec (cF m y) z).
      intros.
        elim b.
        rewrite <- a0 in |- *.
        unfold cF in |- *.
        rewrite cA_cA_1 in |- *.
        tauto.
       tauto.
      generalize (exd_cA_1 m zero y).
         tauto.
     fold (cF_1 m z) in |- *.
        tauto.
     tauto.
     tauto.
    tauto.
    tauto.
   tauto.
   tauto.
  tauto.
  tauto.
intro.
  rewrite cF_1_L0 in |- *.
  elim (eq_dart_dec x (cA m one z)).
 elim (eq_dart_dec (cA_1 m one x) z).
   tauto.
 intros.
   elim b0.
   rewrite a in |- *.
   rewrite cA_1_cA in |- *.
   tauto.
  tauto.
  tauto.
elim (eq_dart_dec (cA_1 m zero y) (cA m one z)).
 elim (eq_dart_dec (cA_1 m one x) z).
  intros.
    elim b0.
    rewrite <- a in |- *.
    rewrite cA_cA_1 in |- *.
    tauto.
   tauto.
   tauto.
 elim (eq_dart_dec (cF m y) z).
   tauto.
 intros.
   elim b0.
   unfold cF in |- *.
   rewrite a in |- *.
   rewrite cA_1_cA in |- *.
   tauto.
  tauto.
  tauto.
elim (eq_dart_dec (cA_1 m one x) z).
 intros.
   elim b1.
   rewrite <- a in |- *.
   rewrite cA_cA_1 in |- *.
   tauto.
  tauto.
  tauto.
elim (eq_dart_dec (cF m y) z).
 intros.
   elim b1.
   rewrite <- a in |- *.
   unfold cF in |- *.
   rewrite cA_cA_1 in |- *.
   tauto.
  tauto.
 generalize (exd_cA_1 m zero y).
    tauto.
fold (cF_1 m z) in |- *.
   tauto.
Qed.

Lemma cF_G1 : forall(m:fmap)(x y z:dart), 
 inv_hmap m -> exd m x -> exd m y -> exd m z ->
  cF (G m one x y) z = 
    if eq_dart_dec (cA m zero y) z then x
    else
     if eq_dart_dec (cF_1 m x) z
     then cA_1 m one y
     else cF m z.
Proof.
intros.
unfold G in |- *.
intros.
elim (succ_dec m one x).
 intro.
   rewrite cF_L in |- *.
   elim (eq_dim_dec one zero).
  intro.
    inversion a0.
 intro.
   clear b.
   assert (zero = dim_opp one).
  simpl in |- *.
     tauto.
 rewrite H3 in |- *.
   rewrite cA_1_Shift in |- *.
  rewrite cA_1_Shift in |- *.
   rewrite cA_1_Shift_ter in |- *.
    rewrite cA_Shift in |- *.
     rewrite <- H3 in |- *.
       elim (eq_dart_dec y (cA_1 m zero z)).
      elim (eq_dart_dec (cA m zero y) z).
        tauto.
      intros.
        elim b.
        rewrite a0 in |- *.
        rewrite cA_cA_1 in |- *.
        tauto.
       tauto.
       tauto.
     elim (eq_dart_dec (cA m one x) (cA_1 m zero z)).
      elim (eq_dart_dec (cA m zero y) z).
       intros.
         elim b.
         rewrite <- a0 in |- *.
         rewrite cA_1_cA in |- *.
         tauto.
        tauto.
        tauto.
      elim (eq_dart_dec (cF_1 m x) z).
        tauto.
      intros.
        elim b.
        unfold cF_1 in |- *.
        rewrite a0 in |- *.
        rewrite cA_cA_1 in |- *.
        tauto.
       tauto.
       tauto.
     elim (eq_dart_dec (cA m zero y) z).
      intros.
        elim b0.
        rewrite <- a0 in |- *; rewrite cA_1_cA in |- *.
        tauto.
       tauto.
       tauto.
     elim (eq_dart_dec (cF_1 m x) z).
      intros.
        elim b0.
        rewrite <- a0 in |- *.
        unfold cF_1 in |- *.
        rewrite cA_1_cA in |- *.
        tauto.
       tauto.
      generalize (exd_cA m one x).
         tauto.
     fold (cF m z) in |- *.
        tauto.
     tauto.
     tauto.
    tauto.
    tauto.
   tauto.
   tauto.
  tauto.
  tauto.
intro.
  rewrite cF_L in |- *.
  elim (eq_dim_dec one zero).
 intro.
   inversion a.
intro.
  clear b0.
  elim (eq_dart_dec y (cA_1 m zero z)).
 elim (eq_dart_dec (cA m zero y) z).
   tauto.
 intros.
   elim b0.
   rewrite a in |- *.
   rewrite cA_cA_1 in |- *.
   tauto.
  tauto.
  tauto.
elim (eq_dart_dec (cA m one x) (cA_1 m zero z)).
 elim (eq_dart_dec (cA m zero y) z).
  intros.
    elim b0.
    rewrite <- a in |- *.
    rewrite cA_1_cA in |- *.
    tauto.
   tauto.
   tauto.
 elim (eq_dart_dec (cF_1 m x) z).
   tauto.
 intros.
   elim b0.
   unfold cF_1 in |- *.
   rewrite a in |- *.
   rewrite cA_cA_1 in |- *.
   tauto.
  tauto.
  tauto.
elim (eq_dart_dec (cA m zero y) z).
 intros.
   elim b1.
   rewrite <- a in |- *.
   rewrite cA_1_cA in |- *.
   tauto.
  tauto.
  tauto.
elim (eq_dart_dec (cF_1 m x) z).
 intros.
   elim b1.
   rewrite <- a in |- *.
   unfold cF_1 in |- *.
   rewrite cA_1_cA in |- *.
   tauto.
  tauto.
 generalize (exd_cA m one x).
    tauto.
fold (cF m x) in |- *.
   tauto.
Qed.

(* OK: *)

Lemma cF_1_G1 : forall(m:fmap)(x y z:dart), 
 inv_hmap m -> exd m x -> exd m y -> exd m z ->
  cF_1 (G m one x y) z = 
    if eq_dart_dec x z then cA m zero y
    else if eq_dart_dec (cA_1 m one y) z
         then cF_1 m x
         else cF_1 m z.
Proof.
intros.
unfold G in |- *.
intros.
elim (succ_dec m one x).
 intro.
   rewrite cF_1_L1 in |- *.
   rewrite cA_Shift in |- *.
  rewrite cA_Shift in |- *.
   rewrite cA_1_Shift in |- *.
    assert (zero = dim_opp one).
     simpl in |- *.
        tauto.
    rewrite H3 in |- *.
      rewrite cA_Shift_ter in |- *.
     rewrite <- H3 in |- *.
       elim (eq_dart_dec x z).
       tauto.
     elim (eq_dart_dec (cA_1 m one y) z).
      fold (cF_1 m x) in |- *.
         tauto.
     fold (cF_1 m z) in |- *.
        tauto.
     tauto.
     tauto.
    tauto.
    tauto.
   tauto.
   tauto.
  tauto.
  tauto.
intro.
  rewrite cF_1_L1 in |- *.
elim (eq_dart_dec x z).
  tauto.
elim (eq_dart_dec (cA_1 m one y) z).
 fold (cF_1 m x) in |- *.
    tauto.
fold (cF_1 m z) in |- *.
   tauto.
Qed.

(*=====================================================
     INSTANTIATIONS OF MTr FOR Tr = G0, G1, 
             WRT cF, cF_1 : expof_G0, expof_G1
                degreef_G0, degreef_G1
 ====================================================*)

(* DIM 0: OK *)

Lemma cF_G0_y1_x: forall(m:fmap)(x y z:dart),
 True ->
  inv_hmap m -> exd m x -> exd m y -> exd m z ->
  cF (G m zero (cA m one y) x) z =
    if eq_dart_dec x z then y
    else if eq_dart_dec (cF_1 m y) z then cF m x 
         else cF m z.
Proof.
intros.
rewrite cF_G0 in |- *.
 rewrite cA_1_cA in |- *.
  fold (cF_1 m y) in |- *.
     tauto.
  tauto.
  tauto.
 tauto.
Qed.

(* OK: *)

Lemma cF_1_G0_y1_x: forall(m:fmap)(x y z:dart),
 True ->
 inv_hmap m -> exd m x -> exd m y -> exd m z ->
  cF_1 (G m zero (cA m one y) x) z =
    if eq_dart_dec y z then x
    else if eq_dart_dec (cF m x) z then cF_1 m y 
         else cF_1 m z.
Proof.
intros.
rename H2 into Ez.
rewrite cF_1_G0 in |- *.
 rewrite cA_1_cA in |- *.
  fold (cF_1 m y) in |- *.
     tauto.
  tauto.
  tauto.
 tauto.
generalize (exd_cA m one y).
   tauto.
 tauto.
 tauto.
Qed.

Lemma exd_G0_y1_x: forall (m : fmap)(x y z : dart),
  inv_hmap m -> 
    (exd m z <-> exd (G m zero (cA m one y) x) z).
Proof. 
intros.
generalize (exd_G m zero (cA m one y) x z).
 tauto.
Qed.

(* OK: *)

Lemma ndN_G0_y1_x: forall (m : fmap)(x y:dart),
  ndN (G m zero (cA m one y) x) = ndN m.
Proof.
intros.
rewrite ndN_G in |- *.
 tauto.
Qed.

Module ModcFG0<:SigTr 
 with Definition Tr:= 
   fun(m:fmap)(x y:dart) => G m zero (cA m one y) x
 with Definition Prec_Tr:= 
  fun(m:fmap)(x y:dart) => True.
Module M:=McF.
Definition Tr(m:fmap)(x y:dart):= 
  G m zero (cA m one y) x.
Definition Prec_Tr(m:fmap)(x y:dart):= True.
Definition f_Tr := cF_G0_y1_x.
Definition f_1_Tr := cF_1_G0_y1_x.
Definition exd_Tr := exd_G0_y1_x.
Definition ndN_Tr := ndN_G0_y1_x.
End ModcFG0.

(* OK: *)

Module MFG0Tr := MTr ModcFG0.

(* DIM 1: *)

Lemma cF_G1_y_x_0: forall(m:fmap)(x y z:dart),
 True ->
  inv_hmap m -> exd m x -> exd m y -> exd m z ->
  cF (G m one y (cA_1 m zero x)) z =
    if eq_dart_dec x z then y
    else if eq_dart_dec (cF_1 m y) z then cF m x 
         else cF m z.
Proof.
intros.
rewrite cF_G1 in |- *.
 rewrite cA_cA_1 in |- *.
  fold (cF m x) in |- *.
     tauto.
  tauto.
  tauto.
 tauto.
 tauto.
generalize (exd_cA_1 m zero x).
   tauto.
 tauto.
Qed.

Lemma cF_1_G1_y_x_0: forall(m:fmap)(x y z:dart),
 True ->
 inv_hmap m -> exd m x -> exd m y -> exd m z ->
   cF_1 (G m one y (cA_1 m zero x)) z =
    if eq_dart_dec y z then x
    else if eq_dart_dec (cF m x) z then cF_1 m y 
         else cF_1 m z.
Proof.
intros.
rewrite cF_1_G1 in |- *.
 fold (cF m x) in |- *.
   rewrite cA_cA_1 in |- *.
   tauto.
  tauto.
  tauto.
 tauto.
 tauto.
generalize (exd_cA_1 m zero x).
   tauto.
 tauto.
Qed.

Lemma exd_G1_y_x_0: forall (m : fmap)(x y z : dart),
  inv_hmap m -> 
    (exd m z <-> exd (G m one y (cA_1 m zero x)) z).
Proof.
intros.
generalize (exd_G m one y (cA_1 m zero x) z).
 tauto.
Qed.

(* OK: *)

Lemma ndN_G1_y_x_0: forall (m : fmap)(x y:dart),
  ndN (G m one y (cA_1 m zero x)) = ndN m.
Proof. intros. rewrite ndN_G. tauto. Qed.

(* INSTANTIATION: *)

Module ModcFG1<:SigTr 
 with Definition Tr:= 
  fun(m:fmap)(x y:dart) => G m one y (cA_1 m zero x)
 with Definition Prec_Tr:= 
  fun(m:fmap)(x y:dart) => True.
Module M:=McF.
Definition Tr(m:fmap)(x y:dart):=
  G m one y (cA_1 m zero x).
Definition Prec_Tr(m:fmap)(x y:dart):= True.
Definition f_Tr := cF_G1_y_x_0.
Definition f_1_Tr := cF_1_G1_y_x_0.
Definition exd_Tr := exd_G1_y_x_0.
Definition ndN_Tr:=ndN_G1_y_x_0.
End ModcFG1.

(* OK: *)

Module MFG1Tr := MTr ModcFG1.

(*=====================================================
           CORRESPONDENCES BETWEEN MODULES
=====================================================*)

(* DIMENSION 0: *)

(* OK: *)

Lemma ModcFG0_Tr_G: forall(m:fmap)(x y:dart),
 inv_hmap m -> exd m x -> 
   ModcFG0.Tr m y (cA_1 m one x) = G m zero x y.
Proof.
intros.
unfold ModcFG0.Tr in |- *.
rewrite cA_cA_1 in |- *.
  tauto.
 tauto.
 tauto.
Qed.

Lemma MFG0Tr_expo_expof:
  MFG0Tr.MfM.expo = expof.
Proof. tauto. Qed.

(* OK: *)

Lemma cF_G0_ModcFG0: forall(m:fmap)(x y z:dart),
  inv_hmap m -> exd m x -> 
     cF (G m zero x y) z = 
       MFG0Tr.MfM.f (ModcFG0.Tr m y (cA_1 m one x)) z.
Proof.
intros.
assert (MFG0Tr.MfM.f = cF).
  tauto.
rewrite H1 in |- *.
  rewrite ModcFG0_Tr_G in |- *.
  tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma exd_ModcFG0: forall(m : fmap)(x y z : dart),
 inv_hmap m -> exd m x -> 
  (exd (ModcFG0.Tr m y (cA_1 m one x)) z <-> 
     exd (G m zero x y) z).
Proof. 
intros.
rewrite ModcFG0_Tr_G in |- *.
  tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma cA_ModcFG0: forall(m:fmap)(x y:dart)(z:dart),
  inv_hmap m -> exd m x ->
    cA (ModcFG0.Tr m y (cA_1 m one x)) zero z = 
        cA (G m zero x y) zero z.
Proof.
intros.
rewrite ModcFG0_Tr_G in |- *.
  tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma Iter_ModcFG0_Tr: 
forall(m:fmap)(x y z:dart)(i:nat),
 inv_hmap m -> exd m x -> 
  Iter (cF (G m zero x y)) i z = 
   Iter (ModcFG0.M.f 
    (ModcFG0.Tr m y (cA_1 m one x))) i z.
Proof.
intros.
rewrite ModcFG0_Tr_G in |- *.
  tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma expo_ModcFG0_Tr: forall(m:fmap)(x y z t:dart),
  inv_hmap m -> exd m x -> 
   (MFG0Tr.MfM.expo 
    (ModcFG0.Tr m y (cA_1 m one x)) z t
     <-> expof (G m zero x y) z t).
Proof.
intros.
assert (MFG0Tr.MfM.expo = expof).
  tauto.
rewrite H1 in |- *.
  rewrite ModcFG0_Tr_G in |- *.
  tauto.
 tauto.
 tauto.
Qed.

(* DIM 1: *)

(* OK: *)

Lemma ModcFG1_Tr_G: forall(m:fmap)(x y:dart),
 inv_hmap m -> exd m y -> 
   ModcFG1.Tr m (cA m zero y) x = G m one x y.
Proof.
intros.
unfold ModcFG1.Tr in |- *.
rewrite cA_1_cA in |- *.
  tauto.
 tauto.
 tauto.
Qed.

Lemma MFG1Tr_expo_expof:
  MFG1Tr.MfM.expo = expof.
Proof. tauto. Qed.

(* OK: *)

Lemma cF_G1_ModcFG1: forall(m:fmap)(x y z:dart),
  inv_hmap m -> exd m y -> 
    cF (G m one x y) z = 
      MFG1Tr.MfM.f (ModcFG1.Tr m (cA m zero y) x) z.
Proof.
intros.
assert (MFG1Tr.MfM.f = cF).
  tauto.
rewrite H1 in |- *.
  rewrite ModcFG1_Tr_G in |- *.
  tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma exd_ModcFG1: forall(m : fmap)(x y z : dart),
 inv_hmap m -> exd m y -> 
  (exd (ModcFG1.Tr m (cA m zero y) x) z <-> 
     exd (G m one x y) z).
Proof. 
intros.
rewrite ModcFG1_Tr_G in |- *.
  tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma cA_ModcFG1: forall(m:fmap)(x y:dart)(z:dart),
  inv_hmap m -> exd m y ->
    cA (ModcFG1.Tr m (cA m zero y) x) one z = 
        cA (G m one x y) one z.
Proof.
intros.
rewrite ModcFG1_Tr_G in |- *.
  tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma Iter_ModcFG1_Tr: 
forall(m:fmap)(x y z:dart)(i:nat),
 inv_hmap m -> exd m y -> 
  Iter (cF (G m one x y)) i z = 
   Iter (ModcFG1.M.f 
    (ModcFG1.Tr m (cA m zero y) x)) i z.
Proof.
intros.
rewrite ModcFG1_Tr_G in |- *.
  tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma expo_ModcFG1_Tr: forall(m:fmap)(x y z t:dart),
  inv_hmap m -> exd m y -> 
   (MFG1Tr.MfM.expo 
    (ModcFG1.Tr m (cA m zero y) x) z t
     <-> expof (G m one x y) z t).
Proof.
intros.
assert (MFG1Tr.MfM.expo = expof).
  tauto.
rewrite H1 in |- *.
  rewrite ModcFG1_Tr_G in |- *.
  tauto.
 tauto.
 tauto.
Qed.

(*=====================================================
     INSTANTIATIONS "IN CLEAR" : expof_L0, expof_L1
                degreef_L0, degreef_L1

 ====================================================*)

(*===================================================
                     DIM 0:
====================================================*)

(* OK: *)

Lemma MFG0Tr_expo_dec_expof_dec: 
 forall(m:fmap)(x y:dart)(H:inv_hmap m)(A B:Prop),
  (if MFG0Tr.MfM.expo_dec m x y H then A else B) <->
  (if expof_dec m x y H then A else B).
Proof. 
intros.
elim (MFG0Tr.MfM.expo_dec m x y H).
 elim (expof_dec m x y H).
   tauto.
  tauto.
elim (expof_dec m x y H).
  tauto.
 tauto.
Qed.

Lemma MFG0Tr_between_betweenf: 
  MFG0Tr.MfM.between = betweenf.
Proof. tauto. Qed.

Lemma MFG0Tr_Prec_Tr_True: forall(m:fmap)(x y:dart),
  ModcFG0.Prec_Tr m x y = True.
Proof. tauto. Qed.

(* OK: *)

Theorem expof_G0_y0_x_CNS: 
  forall (m : fmap) (x y z t : dart) (H : inv_hmap m),
   exd m x -> exd m y -> ~ pred m zero x -> 
    ~ expe m (cA m one y) x -> exd m z ->
    let m1 := G m zero (cA m one y) x in
       let x1 := cF m x in
       let y_1 := cF_1 m y in
       (expof m1 z t <->
        (if expof_dec m x y H
         then
          betweenf m y z x /\ betweenf m y t x \/
          betweenf m x1 z y_1 /\ betweenf m x1 t y_1 \/
          ~ expof m x z /\ expof m z t
         else
          expof m z t \/
          expof m x z /\ expof m y t \/
          expof m x t /\ expof m y z)).
Proof.
intros.
assert (y_1 = MFG0Tr.MfM.f_1 m y).
  tauto.
assert (m1 = ModcFG0.Tr m x y).
  tauto.
rewrite <- MFG0Tr_between_betweenf in |- *.
  set
   (A0 :=
    MFG0Tr.MfM.between m y z x /\ 
      MFG0Tr.MfM.between m y t x \/
    MFG0Tr.MfM.between m x1 z y_1 /\
      MFG0Tr.MfM.between m x1 t y_1 \/
    ~ expof m x z /\ expof m z t) in |- *.
  set
   (B0 :=
    expof m z t \/ expof m x z /\ 
      expof m y t \/ expof m x t /\ expof m y z)
   in |- *.
  cut (expof m1 z t <->
  (if MFG0Tr.MfM.expo_dec m x y H then A0 else B0)).
 generalize 
   (MFG0Tr_expo_dec_expof_dec m x y H A0 B0).
    tauto.
unfold A0 in |- *.
  rewrite <- MFG0Tr_expo_expof in |- *.
  unfold B0 in |- *.
  rewrite <- MFG0Tr_expo_expof in |- *.
  assert (x1 = MFG0Tr.MfM.f m x).
  tauto.
rewrite H5 in |- *.
  rewrite H6 in |- *.
  rewrite H7 in |- *.
  apply MFG0Tr.expo_Tr_CNS.
 unfold ModcFG0.Prec_Tr in |- *.
    tauto.
 tauto.
 tauto.
 tauto.
rewrite <- H6 in |- *.
  unfold m1 in |- *.
  apply inv_hmap_G0.
  tauto.
generalize (exd_cA m one y).
   tauto.
 tauto.
tauto.
 tauto.
Qed.

(*
X = cA m one y  ; Y = x;
x = Y             y = cA_1 m one X = X_1   
y_1 := cF_1 m (cA_1 m one X) = cA m zero X = X0
x1  := cF m x = cF m Y = Y_0_1
*)

(* USUAL FORM: *)

Theorem expof_G0_CNS: 
  forall(m : fmap)(X Y z t : dart)(H : inv_hmap m),
   exd m X -> exd m Y -> ~ pred m zero Y -> 
    ~ expe m X Y -> exd m z ->
       let m1 := G m zero X Y in
       let Y_0_1 := cF m Y in
       let X0 := cA m zero X in
       let X_1:= cA_1 m one X in
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
Proof.
intros.
set (x := Y) in |- *.
set (y := X_1) in |- *.
set (x1 := Y_0_1) in |- *.
set (y_1 := X0) in |- *.
unfold m1 in |- *.
assert (X = cA m one y).
 unfold y in |- *.
   unfold X_1 in |- *.
   rewrite cA_cA_1 in |- *.
   tauto.
  tauto.
  tauto.
rewrite H5 in |- *.
  fold x in |- *.
  rewrite H5 in H3.
  fold x in H3.
  fold x in H1.
  assert (exd m y).
 unfold y in |- *.
   unfold X_1 in |- *.
   generalize (exd_cA_1 m one X).
    tauto.
fold x in H2.
  assert (x1 = cF m x).
 unfold x1 in |- *.
   unfold x in |- *.
   fold Y_0_1 in |- *.
    tauto.
assert (y_1 = cF_1 m y).
 unfold y_1 in |- *.
   unfold y in |- *.
   unfold X_1 in |- *.
   unfold cF_1 in |- *.
   rewrite cA_cA_1 in |- *.
  fold X0 in |- *.
     tauto.
  tauto.
  tauto.
rewrite H7 in |- *.
  rewrite H8 in |- *.
  apply expof_G0_y0_x_CNS.
  tauto.
 tauto.
 tauto.
 tauto.
 tauto.
Qed.

Lemma degreef_G0_G1:
  MFG0Tr.MfM.degree = MFG1Tr.MfM.degree.
Proof. tauto. Qed.

(* FACE DEGREES / G0, MERGE : *) 

Open Scope nat_scope.

(* OK: *)

Theorem degreef_G0_merge_summary:
 forall (m : fmap) (X Y Z : dart)(H:inv_hmap m),
    exd m X -> exd m Y -> ~ pred m zero Y -> 
    ~ expe m X Y -> exd m Z ->
       let m1 := G m zero X Y in
       let X_1:= cA_1 m one X in
       let dY := degreef m Y in
       let dX_1 := degreef m X_1 in
    ~ expof m Y X_1 ->
     degreef m1 Z =
       (if expof_dec m Y Z H
        then dY + dX_1
        else
         if expof_dec m X_1 Z H then dY + dX_1 
         else degreef m Z).
Proof.
intros.
assert (inv_hmap m1).
 unfold m1 in |- *.
   apply inv_hmap_G0.
   tauto.
  tauto.
  tauto.
  tauto.
  tauto.
assert (m1 = ModcFG0.Tr m Y X_1).
 unfold ModcFG0.Tr in |- *.
   unfold X_1 in |- *.
   rewrite cA_cA_1 in |- *.
  fold m1 in |- *.
     tauto.
  tauto.
  tauto.
assert (ModcFG0.Prec_Tr m Y X_1).
 unfold ModcFG0.Prec_Tr in |- *.
    tauto.
assert (exd m X_1).
 unfold X_1 in |- *.
   generalize (exd_cA_1 m one X).
    tauto.
assert (~ MFG0Tr.MfM.expo m Y X_1).
  tauto.
assert (degreef = MFG0Tr.MfM.degree).
  tauto.
rewrite H11 in |- *.
  rewrite H7 in H6.
  generalize
   (MFG0Tr.degree_Tr_merge_summary 
       m Y X_1 Z H H8 H1 H9 H4 H6 H10).
  rewrite <- H11 in |- *.
  rewrite <- H7 in |- *.
  fold dY in |- *.
  fold dX_1 in |- *.
  elim (MFG0Tr.MfM.expo_dec m Y Z H).
 elim (expof_dec m Y Z H).
   tauto.
  tauto.
elim (expof_dec m Y Z H).
  tauto.
elim (MFG0Tr.MfM.expo_dec m X_1 Z H).
 elim (expof_dec m X_1 Z H).
   tauto.
  tauto.
elim (expof_dec m X_1 Z H).
  tauto.
 tauto.
Qed.

(* OK: *)

Theorem degreef_G0_split_summary:
 forall (m : fmap) (X Y Z : dart) (j : nat) 
        (H : inv_hmap m), 
  exd m X -> exd m Y -> ~ pred m zero Y -> 
    ~ expe m X Y -> exd m Z ->
       let m1 := G m zero X Y in
       let X_1:= cA_1 m one X in
       let dY := degreef m Y in
       let dX_1 := degreef m X_1 in
       let Y1 := cF m Y in
       X_1 = Iter (cF m) j Y ->
       2 <= j <= dX_1 ->
    degreef m Z =
       (if expof_dec m X_1 Z H
        then degreef m1 X_1 + degreef m1 Y1
        else degreef m1 Z).
Proof.
intros.
assert (inv_hmap m1).
 unfold m1 in |- *.
   apply inv_hmap_G0.
   tauto.
  tauto.
  tauto.
  tauto.
  tauto.
assert (ModcFG0.Prec_Tr m Y X_1).
 unfold ModcFG0.Prec_Tr in |- *.
    tauto.
assert (exd m X_1).
 unfold X_1 in |- *.
   generalize (exd_cA_1 m one X).
    tauto.
assert (degreef = MFG0Tr.MfM.degree).
  tauto.
assert (cF = MFG0Tr.MfM.f).
  tauto.
rewrite H11 in H5.
  assert (m1 = ModcFG0.Tr m Y X_1).
 unfold m1 in |- *.
   unfold X_1 in |- *.
   unfold ModcFG0.Tr in |- *.
   rewrite cA_cA_1 in |- *.
   tauto.
  tauto.
  tauto.
rewrite H12 in |- *.
  rewrite H12 in H7.
  generalize
   (MFG0Tr.degree_Tr_split_summary 
       m Y X_1 Z j H H8 H1 H9 H4 H5 H6 H7).
  rewrite <- H12 in |- *.
  rewrite <- H10 in |- *.
  rewrite <- H11 in |- *.
  fold Y1 in |- *.
  elim (MFG0Tr.MfM.expo_dec m X_1 Z H).
 elim (expof_dec m X_1 Z H).
   tauto.
  tauto.
elim (expof_dec m X_1 Z H).
  tauto.
 tauto.
Qed.

(*===================================================
                     DIM 1:
====================================================*)

(* OK: *)

Lemma MFG1Tr_expo_dec_expof_dec: 
 forall(m:fmap)(x y:dart)(H:inv_hmap m)(A B:Prop),
  (if MFG1Tr.MfM.expo_dec m x y H then A else B) <->
  (if expof_dec m x y H then A else B).
Proof. 
intros.
elim (MFG1Tr.MfM.expo_dec m x y H).
 elim (expof_dec m x y H).
   tauto.
  tauto.
elim (expof_dec m x y H).
  tauto.
 tauto.
Qed.

Lemma MFG1Tr_between_betweenf: 
  MFG1Tr.MfM.between = betweenf.
Proof. tauto. Qed.

Lemma MFG1Tr_Prec_Tr_True: forall(m:fmap)(x y:dart),
  ModcFG1.Prec_Tr m x y = True.
Proof. tauto. Qed.

(* OK: *)

(*

X = y ; Y = cA_1 m zero x
x = cA m zero Y ; y = X
x1 = cF m (cA m zero Y) = cA_1 m one Y = Y_1
y_1 = cF_1 X

*)

Theorem expof_G1_y_x_0_CNS: 
  forall (m : fmap) (x y z t : dart) (H : inv_hmap m),
  exd m x -> exd m y -> 
   ~ pred m one (cA_1 m zero x) -> 
    ~ expv m y (cA_1 m zero x) -> exd m z ->
       let m1 := G m one y (cA_1 m zero x) in 
       let x1 := cF m x in
       let y_1 := cF_1 m y in
       (expof m1 z t <->
        (if expof_dec m x y H
         then
          betweenf m y z x /\ betweenf m y t x \/
          betweenf m x1 z y_1 /\ betweenf m x1 t y_1 \/
          ~ expof m x z /\ expof m z t
         else
          expof m z t \/
          expof m x z /\ expof m y t \/
          expof m x t /\ expof m y z)).
Proof.
intros.
assert (y_1 = MFG1Tr.MfM.f_1 m y).
  tauto.
assert (m1 = ModcFG1.Tr m x y).
  tauto.
rewrite <- MFG1Tr_between_betweenf in |- *.
  set
   (A0 :=
    MFG1Tr.MfM.between m y z x /\ 
        MFG1Tr.MfM.between m y t x \/
    MFG1Tr.MfM.between m x1 z y_1 /\
        MFG1Tr.MfM.between m x1 t y_1 \/
    ~ expof m x z /\ expof m z t) in |- *.
  set
   (B0 :=
    expof m z t \/ expof m x z /\ expof m y t \/ 
     expof m x t /\ expof m y z)
   in |- *.
  cut (expof m1 z t <->
  (if MFG1Tr.MfM.expo_dec m x y H then A0 else B0)).
 generalize 
  (MFG1Tr_expo_dec_expof_dec m x y H A0 B0).
    tauto.
unfold A0 in |- *.
  rewrite <- MFG1Tr_expo_expof in |- *.
  unfold B0 in |- *.
  rewrite <- MFG1Tr_expo_expof in |- *.
  assert (x1 = MFG1Tr.MfM.f m x).
  tauto.
rewrite H5 in |- *.
  rewrite H6 in |- *.
  rewrite H7 in |- *.
  apply MFG1Tr.expo_Tr_CNS.
 unfold ModcFG1.Prec_Tr in |- *.
    tauto.
 tauto.
 tauto.
 tauto.
rewrite <- H6 in |- *.
  unfold m1 in |- *.
  apply inv_hmap_G1.
  tauto.
 tauto.
generalize (exd_cA_1 m zero x).
   tauto.
 tauto.
 tauto.
Qed.

(* USUAL FORM: OK *)

Theorem expof_G1_CNS: 
  forall (m : fmap) (X Y z t : dart) (H : inv_hmap m),
  exd m X -> exd m Y -> 
   ~ pred m one Y -> 
    ~ expv m X Y -> exd m z ->
       let m1 := G m one X Y in 
       let Y_1 := cA_1 m one Y in
       let X10 := cF_1 m X in
       let Y0 := cA m zero Y in
       (expof m1 z t <->
     (if expof_dec m Y0 X H
      then
       betweenf m X z Y0 /\ betweenf m X t Y0 \/
       betweenf m Y_1 z X10 /\ betweenf m Y_1 t X10 \/
       ~ expof m Y0 z /\ expof m z t
      else
       expof m z t \/
       expof m Y0 z /\ expof m X t \/
       expof m Y0 t /\ expof m X z)).
Proof.
intros.
set (x := Y0) in |- *.
set (x1 := Y_1) in |- *.
set (y_1 := X10) in |- *.
set (y := X) in |- *.
unfold m1 in |- *.
fold y in |- *.
assert (Y = cA_1 m zero x).
 unfold x in |- *.
   unfold Y0 in |- *.
   rewrite cA_1_cA in |- *.
   tauto.
  tauto.
  tauto.
rewrite H5 in |- *.
  fold y in H3.
  rewrite H5 in H3.
  rewrite H5 in H1.
  rewrite H5 in H2.
  assert (x1 = cF m x).
 unfold x in |- *.
   unfold x1 in |- *.
   unfold Y0 in |- *.
   unfold cF in |- *.
   rewrite cA_1_cA in |- *.
  fold Y_1 in |- *.
     tauto.
  tauto.
 rewrite H5 in |- *.
    tauto.
assert (y_1 = cF_1 m y).
 unfold y in |- *.
   unfold y_1 in |- *.
   unfold X10 in |- *.
    tauto.
rewrite H6 in |- *.
  rewrite H7 in |- *.
  apply expof_G1_y_x_0_CNS.
 generalize (exd_cA_1 m zero x).
    tauto.
unfold y in |- *.
   tauto.
 tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Theorem degreef_G1_merge_summary:
 forall (m : fmap) (X Y Z : dart)(H:inv_hmap m),
   exd m X -> exd m Y -> ~ pred m one Y -> 
    ~ expv m X Y -> exd m Z ->
       let m1 := G m one X Y in 
       let Y0 := cA m zero Y in 
       let dY0 := degreef m Y0 in
       let dX := degreef m X in
    ~ expof m Y0 X ->
      degreef m1 Z =
        if expof_dec m Y0 Z H
        then dY0 + dX
        else
          if expof_dec m X Z H then dY0 + dX 
          else degreef m Z.
Proof.
intros.
assert (inv_hmap m1).
 unfold m1 in |- *.
   apply inv_hmap_G1.
   tauto.
  tauto.
  tauto.
  tauto.
  tauto.
assert (m1 = ModcFG1.Tr m Y0 X).
 unfold ModcFG1.Tr in |- *.
   unfold Y0 in |- *.
   rewrite cA_1_cA in |- *.
  fold m1 in |- *.
     tauto.
  tauto.
  tauto.
assert (ModcFG1.Prec_Tr m Y0 X).
 unfold ModcFG1.Prec_Tr in |- *.
    tauto.
assert (exd m Y0).
 unfold Y0 in |- *.
   generalize (exd_cA m zero Y).
    tauto.
assert (~ MFG1Tr.MfM.expo m Y0 X).
  tauto.
assert (degreef = MFG1Tr.MfM.degree).
  tauto.
rewrite H11 in |- *.
  rewrite H7 in H6.
  generalize 
 (MFG1Tr.degree_Tr_merge_summary 
      m Y0 X Z H H8 H9 H0 H4 H6 H10).
  rewrite <- H11 in |- *.
  rewrite <- H7 in |- *.
  fold dX in |- *.
  fold dY0 in |- *.
  elim (MFG1Tr.MfM.expo_dec m Y0 Z H).
 elim (expof_dec m Y0 Z H).
   tauto.
  tauto.
elim (expof_dec m Y0 Z H).
  tauto.
elim (MFG1Tr.MfM.expo_dec m X Z H).
 elim (expof_dec m X Z H).
   tauto.
  tauto.
elim (expof_dec m X Z H).
  tauto.
 tauto.
Qed.

(* OK: *)

Theorem degreef_G1_split_summary:
 forall (m : fmap) (X Y Z : dart) (j : nat) 
        (H : inv_hmap m), 
   exd m X -> exd m Y -> ~ pred m one Y -> 
    ~ expv m X Y -> exd m Z ->
       let m1 := G m one X Y in 
       let Y0 := cA m zero Y in 
       let Y01 := cF m Y0 in
       let dX := degreef m X in
       X = Iter (cF m) j Y0 ->
       2 <= j <= dX ->
    degreef m Z =
        if expof_dec m X Z H
        then degreef m1 X + degreef m1 Y01
        else degreef m1 Z.
Proof.
intros.
assert (inv_hmap m1).
 unfold m1 in |- *.
   apply inv_hmap_G1.
   tauto.
  tauto.
  tauto.
  tauto.
  tauto.
assert (ModcFG1.Prec_Tr m Y0 X).
 unfold ModcFG1.Prec_Tr in |- *.
    tauto.
assert (exd m Y0).
 unfold Y0 in |- *.
   generalize (exd_cA m zero Y).
    tauto.
assert (degreef = MFG1Tr.MfM.degree).
  tauto.
assert (cF = MFG1Tr.MfM.f).
  tauto.
rewrite H11 in H5.
  assert (m1 = ModcFG1.Tr m Y0 X).
 unfold m1 in |- *.
   unfold Y0 in |- *.
   unfold ModcFG1.Tr in |- *.
   rewrite cA_1_cA in |- *.
   tauto.
  tauto.
  tauto.
rewrite H12 in |- *.
  rewrite H12 in H7.
  generalize
   (MFG1Tr.degree_Tr_split_summary 
     m Y0 X Z j H H8 H9 H0 H4 H5 H6 H7).
  rewrite <- H12 in |- *.
  rewrite <- H10 in |- *.
  rewrite <- H11 in |- *.
  fold Y01 in |- *.
  elim (MFG1Tr.MfM.expo_dec m X Z H).
 elim (expof_dec m X Z H).
   tauto.
  tauto.
elim (expof_dec m X Z H).
  tauto.
 tauto.
Qed.

(*===================================================
              nf_G0, nf_G1
===================================================*)

Open Scope Z_scope.

(* OK: *)

Theorem nf_G0:
 forall (m : fmap) (x y: dart) (H : inv_hmap m), 
   let x_1 := cA_1 m one x in
     nf (G m zero x y) = 
      nf m + if (expf_dec m x_1 y) then 1 else -1.
Proof.
intros.
unfold G in |- *.
elim (succ_dec m zero x).
 intro.
   set (m0 := Shift m zero x) in |- *.
   assert (x_1 = cA_1 m0 one x).
  unfold m0 in |- *.
    assert (one = dim_opp zero).
   simpl in |- *.
      tauto.
  rewrite H0 in |- *.
    rewrite cA_1_Shift_ter in |- *.
   simpl in |- *.
      tauto.
   tauto.
   tauto.
 rewrite H0 in |- *.
   assert
    (nf (L m0 zero x y) =
     nf m + 
 (if expf_dec m0 (cA_1 m0 one x) y then 1 else -1)).
  unfold nf in |- *.
    fold nf in |- *.
    unfold m0 in |- *.
    rewrite nf_Shift in |- *.
    tauto.
   tauto.
   tauto.
 assert
  ((if expf_dec m0 (cA_1 m0 one x) y then 1 else -1) =
   (if expf_dec m (cA_1 m0 one x) y then 1 else -1)).
  generalize 
 (expf_Shift m zero x (cA_1 m0 one x) y H a).
    intro.
    fold m0 in H2.
    elim (expf_dec m0 (cA_1 m0 one x) y).
   elim (expf_dec m (cA_1 m0 one x) y).
     tauto.
    tauto.
  elim (expf_dec m (cA_1 m0 one x) y).
    tauto.
   tauto.
 rewrite <- H2 in |- *.
    tauto.
intros.
  simpl in |- *.
  fold x_1 in |- *.
   tauto.
Qed.

(* OK: *)

Theorem nf_G1:
 forall (m : fmap) (x y: dart) (H : inv_hmap m), 
   let y0 := cA m zero y in
     nf (G m one x y) = 
      nf m + if (expf_dec m x y0) then 1 else -1.
Proof.
intros.
unfold G in |- *.
elim (succ_dec m one x).
 intro.
   set (m0 := Shift m one x) in |- *.
   assert (y0 = cA m0 zero y).
  unfold m0 in |- *.
    assert (zero = dim_opp one).
   simpl in |- *.
      tauto.
  rewrite H0 in |- *.
    rewrite cA_Shift_ter in |- *.
   simpl in |- *.
      tauto.
   tauto.
   tauto.
 rewrite H0 in |- *.
   rewrite <- H0 in |- *.
   assert
    ((if expf_dec m0 x y0 then 1 else -1) =
     (if expf_dec m x y0 then 1 else -1)).
  generalize (expf_Shift m one x x y0 H a).
    fold m0 in |- *.
    intro.
    elim (expf_dec m0 x y0).
   elim (expf_dec m x y0).
     tauto.
    tauto.
  elim (expf_dec m x y0).
    tauto.
   tauto.
 rewrite <- H1 in |- *.
   rewrite H0 in |- *.
   assert (nf m0 = nf m).
  unfold m0 in |- *.
    apply nf_Shift.
    tauto.
   tauto.
 rewrite <- H2 in |- *.
   simpl in |- *.
    tauto.
intro.
  unfold y0 in |- *.
  simpl in |- *.
   tauto.
Qed.

(* OK: *)

Lemma eqc_G: 
 forall (m : fmap)(k:dim)(x y z t: dart),
  inv_hmap m ->
   (eqc (G m k x y) z t <->
    (eqc m z t \/ 
        eqc m z x /\ eqc m y t \/ 
            eqc m z y /\ eqc m x t)).
Proof.
intros.
unfold G in |- *.
elim (succ_dec m k x).
 intro.
   set (m0 := Shift m k x) in |- *.
   unfold G in |- *.
   assert
    (eqc m0 z t \/ eqc m0 z x /\ eqc m0 y t \/ 
     eqc m0 z y /\ eqc m0 x t <->
     eqc m z t \/ eqc m z x /\ eqc m y t \/ 
      eqc m z y /\ eqc m x t).
  assert (eqc m z t <-> eqc m0 z t).
   unfold m0 in |- *.
     generalize (eqc_Shift m k x z t).
      tauto.
  assert (eqc m z x <-> eqc m0 z x).
   unfold m0 in |- *.
     generalize (eqc_Shift m k x z x).
      tauto.
  assert (eqc m y t <-> eqc m0 y t).
   unfold m0 in |- *.
     generalize (eqc_Shift m k x y t).
      tauto.
  assert (eqc m z y <-> eqc m0 z y).
   unfold m0 in |- *.
     generalize (eqc_Shift m k x z y).
      tauto.
  assert (eqc m x t <-> eqc m0 x t).
   unfold m0 in |- *.
     generalize (eqc_Shift m k x x t).
      tauto.
   tauto.
 assert
  (eqc (L m k x y) z t <->
   eqc m z t \/ eqc m z x /\ eqc m y t \/ 
       eqc m z y /\ eqc m x t).
  simpl in |- *.
     tauto.
 assert
  (eqc (L m0 k x y) z t <->
   eqc m0 z t \/ eqc m0 z x /\ eqc m0 y t \/ 
      eqc m0 z y /\ eqc m0 x t).
  simpl in |- *.
     tauto.
 set (A0 := eqc m z t \/ eqc m z x /\ eqc m y t \/ 
     eqc m z y /\ eqc m x t)
  in |- *.
   set
    (B0 :=
     eqc m0 z t \/ eqc m0 z x /\ eqc m0 y t 
     \/ eqc m0 z y /\ eqc m0 x t)
    in |- *.
   fold A0 in H1.
   fold B0 in H2.
   fold A0 in H0.
   fold B0 in H0.
    tauto.
intro.
  simpl in |- *.
   tauto.
Qed.

Lemma nd_B: forall (m : fmap)(k:dim)(z: dart),
   nd (B m k z) = nd m.
Proof.
intros.
induction m.
 simpl in |- *.
    tauto.
simpl in |- *.
  rewrite IHm in |- *.
   tauto.
simpl in |- *.
  elim (eq_dim_dec d k).
 elim (eq_dart_dec d0 z).
  simpl in |- *;  tauto.
 simpl in |- *.
    tauto.
simpl in |- *.
   tauto.
Qed.

Lemma nd_G: forall (m : fmap)(k:dim)(x y: dart),
   nd (G m k x y) = nd m.
Proof.
intros.
unfold G in |- *.
simpl in |- *.
elim (succ_dec m k x).
 unfold Shift in |- *.
   simpl in |- *.
   rewrite nd_B in |- *.
    tauto.
 tauto.
Qed.

(* OK: *)

Theorem planarity_criterion_G0: 
 forall (m:fmap)(x y:dart), 
  inv_hmap m -> exd m x -> exd m y -> 
   ~ pred m zero y -> ~ expe m x y -> 
     planar m ->
      (planar (G m zero x y) <->
        (~ eqc m x y \/ expf m (cA_1 m one x) y)).
Proof.
intros.
unfold G in |- *.
elim (succ_dec m zero x).
 intro.
   set (m0 := Shift m zero x) in |- *.
   assert (inv_hmap m0).
  unfold m0 in |- *.
    apply inv_hmap_Shift.
    tauto.
   tauto.
 assert (prec_L m0 zero x y).
  unfold prec_L in |- *.
    split.
   unfold m0 in |- *.
     generalize (exd_Shift m zero x x).
      tauto.
  split.
   unfold m0 in |- *.
     generalize (exd_Shift m zero x y).
      tauto.
  split.
   unfold succ in |- *.
     unfold m0 in |- *.
     rewrite A_Shift in |- *.
    elim (eq_dart_dec x x).
      tauto.
     tauto.
    tauto.
    tauto.
  split.
   unfold m0 in |- *.
     unfold pred in |- *.
     rewrite A_1_Shift in |- *.
    elim (eq_dart_dec (A m zero x) y).
      tauto.
    elim (eq_dart_dec (bottom m zero x) y).
     intros.
       elim H3.
       rewrite <- a0 in |- *.
       apply expe_symm.
       tauto.
     apply MA0.expo_bottom_z.
       tauto.
      tauto.
    intros.
      unfold pred in H2.
       tauto.
    tauto.
    tauto.
  unfold m0 in |- *.
    rewrite cA_Shift in |- *.
   intro.
     apply H3.
     rewrite <- H6 in |- *.
     unfold expe in |- *.
     unfold MA0.MfcA.expo in |- *.
     split.
     tauto.
   split with 1%nat.
     simpl in |- *.
      tauto.
   tauto.
   tauto.
 assert (eqc m0 x y <-> eqc m x y).
  unfold m0 in |- *.
    generalize (eqc_Shift m zero x x y).
     tauto.
 assert (expf m0 (cA_1 m one x) y <->
  expf m (cA_1 m one x) y).
  unfold m0 in |- *; 
 generalize (expf_Shift m zero x (cA_1 m one x) y).
     tauto.
 assert (planar m0).
  unfold m0 in |- *.
    apply planar_Shift.
    tauto.
   tauto.
   tauto.
 assert (cA_1 m0 one x = cA_1 m one x).
  unfold m0 in |- *.
    assert (one = dim_opp zero).
   simpl in |- *.
      tauto.
  rewrite H10 in |- *.
    rewrite cA_1_Shift_ter in |- *.
    tauto.
   tauto.
   tauto.
 generalize (planarity_criterion_0 m0 x y).
   rewrite H10 in |- *.
    tauto.
intro.
  generalize (planarity_criterion_0 m x y).
  intro.
  apply H5.
  tauto.
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
  apply H3.
  rewrite <- H6 in |- *.
  unfold expe in |- *.
  unfold MA0.MfcA.expo in |- *.
  split.
  tauto.
split with 1%nat.
  simpl in |- *.
   tauto.
 tauto.
Qed.

(* OK: *)

Theorem planarity_crit_G0: 
 forall (m:fmap)(x y:dart), 
  inv_hmap m -> exd m x -> exd m y -> 
   ~ pred m zero y -> ~ expe m x y -> 
      (planar (G m zero x y) <-> 
  (planar m /\
        (~ eqc m x y \/ expf m (cA_1 m one x) y))).
Proof.
intros.
unfold G in |- *.
elim (succ_dec m zero x).
 intro.
   set (m0 := Shift m zero x) in |- *.
   assert (inv_hmap m0).
  unfold m0 in |- *.
    apply inv_hmap_Shift.
    tauto.
   tauto.
 assert (prec_L m0 zero x y).
  unfold prec_L in |- *.
    split.
   unfold m0 in |- *.
     generalize (exd_Shift m zero x x).
      tauto.
  split.
   unfold m0 in |- *.
     generalize (exd_Shift m zero x y).
      tauto.
  split.
   unfold succ in |- *.
     unfold m0 in |- *.
     rewrite A_Shift in |- *.
    elim (eq_dart_dec x x).
      tauto.
     tauto.
    tauto.
    tauto.
  split.
   unfold m0 in |- *.
     unfold pred in |- *.
     rewrite A_1_Shift in |- *.
    elim (eq_dart_dec (A m zero x) y).
      tauto.
    elim (eq_dart_dec (bottom m zero x) y).
     intros.
       elim H3.
       rewrite <- a0 in |- *.
       apply expe_symm.
       tauto.
     apply MA0.expo_bottom_z.
       tauto.
      tauto.
    intros.
      unfold pred in H2.
       tauto.
    tauto.
    tauto.
  unfold m0 in |- *.
    rewrite cA_Shift in |- *.
   intro.
     apply H3.
     unfold expe in |- *.
     unfold MA0.MfcA.expo in |- *.
     split.
     tauto.
   split with 1%nat.
     simpl in |- *.
      tauto.
   tauto.
   tauto.
 assert (eqc m0 x y <-> eqc m x y).
  unfold m0 in |- *.
    generalize (eqc_Shift m zero x x y).
     tauto.
 assert (expf m0 (cA_1 m one x) y <-> expf m (cA_1 m one x) y).
  unfold m0 in |- *; generalize (expf_Shift m zero x (cA_1 m one x) y).
     tauto.
 assert (cA_1 m0 one x = cA_1 m one x).
  unfold m0 in |- *.
    assert (one = dim_opp zero).
   simpl in |- *.
      tauto.
  rewrite H8 in |- *.
    rewrite cA_1_Shift_ter in |- *.
    tauto.
   tauto.
   tauto.
 generalize (planarity_crit_0 m0 x y).
   rewrite H8 in |- *.
   generalize (planarity_crit_Shift0 m x).
   fold m0 in |- *.
    tauto.
intro.
  generalize (planarity_crit_0 m x y).
  intro.
  apply H4.
  tauto.
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
  apply H3.
  rewrite <- H5 in |- *.
  unfold expe in |- *.
  unfold MA0.MfcA.expo in |- *.
  split.
  tauto.
split with 1%nat.
  simpl in |- *.
   tauto.
Qed.

(* OK: *)

Theorem planarity_criterion_G1: 
 forall (m:fmap)(x y:dart),
 inv_hmap m -> exd m x -> exd m y -> 
   ~ pred m one y -> ~ expv m x y -> 
  planar m ->
   (planar (G m one x y) <->
      (~ eqc m x y \/ expf m x (cA m zero y))).
Proof.
intros.
unfold G in |- *.
elim (succ_dec m one x).
 intro.
   set (m0 := Shift m one x) in |- *.
   assert (inv_hmap m0).
  unfold m0 in |- *.
    apply inv_hmap_Shift.
    tauto.
   tauto.
 assert (prec_L m0 one x y).
  unfold prec_L in |- *.
    split.
   unfold m0 in |- *.
     generalize (exd_Shift m one x x).
      tauto.
  split.
   unfold m0 in |- *.
     generalize (exd_Shift m one x y).
      tauto.
  split.
   unfold succ in |- *.
     unfold m0 in |- *.
     rewrite A_Shift in |- *.
    elim (eq_dart_dec x x).
      tauto.
     tauto.
    tauto.
    tauto.
  split.
   unfold m0 in |- *.
     unfold pred in |- *.
     rewrite A_1_Shift in |- *.
    elim (eq_dart_dec (A m one x) y).
      tauto.
    elim (eq_dart_dec (bottom m one x) y).
     intros.
       elim H3.
       rewrite <- a0 in |- *.
       apply expv_symm.
       tauto.
     apply MA1.expo_bottom_z.
       tauto.
      tauto.
    intros.
      unfold pred in H2.
       tauto.
    tauto.
    tauto.
  unfold m0 in |- *.
    rewrite cA_Shift in |- *.
   intro.
     apply H3.
     rewrite <- H6 in |- *.
     unfold MA1.MfcA.expo in |- *.
     split.
     tauto.
   split with 1%nat.
     simpl in |- *.
      tauto.
   tauto.
   tauto.
 assert (eqc m0 x y <-> eqc m x y).
  unfold m0 in |- *.
    generalize (eqc_Shift m one x x y).
     tauto.
 assert (expf m0 x (cA m zero y) <-> expf m x (cA m zero y)).
  generalize (expf_Shift m one x x (cA m zero y)).
     tauto.
 assert (planar m0).
  unfold m0 in |- *.
    apply planar_Shift.
    tauto.
   tauto.
   tauto.
 assert (cA m0 zero y = cA m zero y).
  unfold m0 in |- *.
    assert (zero = dim_opp one).
   simpl in |- *.
      tauto.
  rewrite H10 in |- *.
    rewrite cA_Shift_ter in |- *.
    tauto.
   tauto.
   tauto.
 generalize (planarity_criterion_1 m0 x y).
   rewrite H10 in |- *.
    tauto.
intro.
  generalize (planarity_criterion_1 m x y).
  intro.
  apply H5.
  tauto.
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
  apply H3.
  rewrite <- H6 in |- *.
  unfold expv in |- *.
  unfold MA1.MfcA.expo in |- *.
  split.
  tauto.
split with 1%nat.
  simpl in |- *.
   tauto.
 tauto.
Qed.

(* OK: *)

Theorem planarity_crit_G1: 
 forall (m:fmap)(x y:dart),
 inv_hmap m -> exd m x -> exd m y -> 
   ~ pred m one y -> ~ expv m x y -> 
   (planar (G m one x y) <->  
 (planar m /\ 
    (~ eqc m x y \/ expf m x (cA m zero y)))).
Proof.
intros.
unfold G in |- *.
elim (succ_dec m one x).
 intro.
   set (m0 := Shift m one x) in |- *.
   assert (inv_hmap m0).
  unfold m0 in |- *.
    apply inv_hmap_Shift.
    tauto.
   tauto.
 assert (prec_L m0 one x y).
  unfold prec_L in |- *.
    split.
   unfold m0 in |- *.
     generalize (exd_Shift m one x x).
      tauto.
  split.
   unfold m0 in |- *.
     generalize (exd_Shift m one x y).
      tauto.
  split.
   unfold succ in |- *.
     unfold m0 in |- *.
     rewrite A_Shift in |- *.
    elim (eq_dart_dec x x).
      tauto.
     tauto.
    tauto.
    tauto.
  split.
   unfold m0 in |- *.
     unfold pred in |- *.
     rewrite A_1_Shift in |- *.
    elim (eq_dart_dec (A m one x) y).
      tauto.
    elim (eq_dart_dec (bottom m one x) y).
     intros.
       elim H3.
       rewrite <- a0 in |- *.
       apply expv_symm.
       tauto.
     apply MA1.expo_bottom_z.
       tauto.
      tauto.
    intros.
      unfold pred in H2.
       tauto.
    tauto.
    tauto.
  unfold m0 in |- *.
    rewrite cA_Shift in |- *.
   intro.
     apply H3.
     rewrite <- H5 in |- *.
     unfold MA1.MfcA.expo in |- *.
     split.
     tauto.
   split with 1%nat.
     simpl in |- *.
      tauto.
   tauto.
   tauto.
 assert (eqc m0 x y <-> eqc m x y).
  unfold m0 in |- *.
    generalize (eqc_Shift m one x x y).
     tauto.
 assert (expf m0 x (cA m zero y) <-> expf m x (cA m zero y)).
  generalize (expf_Shift m one x x (cA m zero y)).
     tauto.
 assert (cA m0 zero y = cA m zero y).
  unfold m0 in |- *.
    assert (zero = dim_opp one).
   simpl in |- *.
      tauto.
  rewrite H8 in |- *.
    rewrite cA_Shift_ter in |- *.
    tauto.
   tauto.
   tauto.
 generalize (planarity_crit_1 m0 x y).
   rewrite H8 in |- *.
   generalize (planarity_crit_Shift1 m x).
   fold m0 in |- *.
    tauto.
intro.
  generalize (planarity_crit_1 m x y).
  intro.
  apply H4.
  tauto.
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
  apply H3.
  rewrite <- H5 in |- *.
  unfold expv in |- *.
  unfold MA1.MfcA.expo in |- *.
  split.
  tauto.
split with 1%nat.
  simpl in |- *.
   tauto.
Qed.

(*================================================
  =================================================
            SUITE : Merge: (EN COURS)

     WITHOUT PRECONDITION ~pred m k y
=================================================
==================================================*)

Definition Merge(m:fmap)(k:dim)(x y:dart):=
  let m1 := if pred_dec m k y 
            then Shift m k (cA_1 m k y)
            else m in
  G m1 k x y.

(* OK: *)

Lemma exd_Merge: forall(m:fmap)(k:dim)(x y z:dart),
  exd m z <-> exd (Merge m k x y) z.
Proof.
unfold Merge in |- *.
intros.
elim (pred_dec m k y).
 generalize (exd_G (Shift m k (cA_1 m k y)) k x y z).
   generalize (exd_Shift m k (cA_1 m k y) z).
    tauto.
generalize (exd_G m k x y z).
   tauto.
Qed.

(* OK: *)

Lemma exd_Merge_bis: forall(m:fmap)(k:dim)(x y z:dart),
  inv_hmap m -> (exd m z <-> exd (Merge m k x y) z).
Proof. intros. apply exd_Merge. Qed.

(* OK!: *)

Lemma A_Merge0: forall(m:fmap)(x y z:dart),
 ~expe m x y ->
  inv_hmap m -> exd m x -> exd m y ->
   A (Merge m zero x y) zero z = 
    if eq_dart_dec x z then y
    else if eq_dart_dec (cA_1 m zero y) z then nil
         else if eq_dart_dec (top m zero x) z 
              then bottom m zero x
              else if eq_dart_dec (top m zero y) z
                   then bottom m zero y
                   else A m zero z.
Proof.
intros.
unfold Merge in |- *.
elim (pred_dec m zero y).
 intro.
   assert (A_1 m zero y = cA_1 m zero y).
  rewrite cA_1_eq in |- *.
   elim (pred_dec m zero y);  tauto.
   tauto.
 assert (exd m (cA_1 m zero y)).
  generalize (exd_cA_1 m zero y).
     tauto.
 assert (expe m (cA_1 m zero y) y).
  unfold expe in |- *.
    unfold MA0.MfcA.expo in |- *.
    split.
    tauto.
  split with 1%nat.
    simpl in |- *.
    assert (MA0.MfcA.f m (cA_1 m zero y) = 
   cA m zero (cA_1 m zero y)).
    tauto.
  rewrite cA_cA_1 in H5.
    tauto.
   tauto.
   tauto.
 set (m0 := Shift m zero (cA_1 m zero y)) in |- *.
   rewrite A_G in |- *.
  elim (eq_dart_dec x z).
    tauto.
  intro.
    assert (top m0 zero x = top m zero x).
   unfold m0 in |- *.
     rewrite (top_Shift0 m (cA_1 m zero y) x H0)
       in |- *.
    elim (expe_dec m (cA_1 m zero y) x).
     intro.
       elim H.
       apply expe_trans with (cA_1 m zero y).
      apply expe_symm.
        tauto.
       tauto.
      tauto.
     tauto.
   unfold succ in |- *.
     rewrite <- H3 in |- *.
     rewrite A_A_1 in |- *.
    apply exd_not_nil with m.
      tauto.
     tauto.
    tauto.
    tauto.
    tauto.
   intro.
     elim H.
     rewrite <- H6 in |- *.
      tauto.
  rewrite H6 in |- *.
    assert (bottom m0 zero x = bottom m zero x).
   unfold m0 in |- *.
     rewrite 
  (bottom_Shift0 m (cA_1 m zero y) x H0) in |- *.
    elim (expe_dec m (cA_1 m zero y) x H0).
     intro.
       elim H.
       apply expe_trans with (cA_1 m zero y).
      apply expe_symm.
        tauto.
       tauto.
      tauto.
     tauto.
   unfold succ in |- *.
     rewrite <- H3 in |- *.
     rewrite A_A_1 in |- *.
    apply exd_not_nil with m.
      tauto.
     tauto.
    tauto.
    tauto.
    tauto.
   intro.
     elim H.
     rewrite <- H7 in |- *.
      tauto.
  rewrite H7 in |- *.
    elim (eq_dart_dec (top m zero x) z).
   intros.
     elim (eq_dart_dec (cA_1 m zero y) z).
    rewrite cA_1_eq in |- *.
     elim (pred_dec m zero y).
      intros.
        rewrite <- a2 in a0.
        rewrite H3 in a0.
        rewrite cA_1_eq in a0.
       generalize a0.
         elim (pred_dec m zero y).
        intros.
          clear a0.
          rewrite H3 in a4.
          elim H.
          apply expe_trans with (top m zero x).
         apply MA0.MfcA.expo_symm.
           tauto.
         apply MA0.expo_top_z.
           tauto.
          tauto.
        rewrite a4 in |- *.
           tauto.
        tauto.
       tauto.
      tauto.
     tauto.
    tauto.
  intros.
    unfold m0 in |- *.
    rewrite A_Shift in |- *.
   elim (eq_dart_dec (cA_1 m zero y) z).
     tauto.
   intro.
     rewrite <- H3 in |- *.
     rewrite top_A_1 in |- *.
    elim (eq_dart_dec (top m zero y) z).
     intros.
       apply bottom_A_1.
       tauto.
      tauto.
     tauto.
    tauto.
    tauto.
   tauto.
  unfold succ in |- *.
    rewrite <- H3 in |- *.
    rewrite A_A_1 in |- *.
   apply exd_not_nil with m.
     tauto.
    tauto.
   tauto.
   tauto.
 unfold m0 in |- *.
   apply inv_hmap_Shift.
   tauto.
 unfold succ in |- *.
   rewrite <- H3 in |- *.
   rewrite A_A_1 in |- *.
  apply exd_not_nil with m.
    tauto.
   tauto.
  tauto.
  tauto.
 unfold m0 in |- *.
   generalize (exd_Shift m zero (cA_1 m zero y) x).
    tauto.
intro.
  rewrite A_G in |- *.
 elim (eq_dart_dec x z).
   tauto.
 elim (eq_dart_dec (top m zero x) z).
  intros.
    elim (eq_dart_dec (cA_1 m zero y) z).
   intro.
     rewrite cA_1_eq in a0.
    generalize a0.
      elim (pred_dec m zero y).
      tauto.
    intros.
      elim H.
      generalize (MA0.top_top_expo m x y).
      assert (Md0.kd = zero).
      tauto.
    rewrite H3 in |- *.
      rewrite a1 in |- *.
       tauto.
    tauto.
   tauto.
 intros.
   elim (eq_dart_dec (cA_1 m zero y) z).
  rewrite cA_1_eq in |- *.
   elim (pred_dec m zero y).
     tauto.
   intros.
     rewrite <- a in |- *.
     generalize (not_succ_top m zero y).
     unfold succ in |- *.
     generalize 
  (eq_dart_dec (A m zero (top m zero y)) nil).
      tauto.
   tauto.
 elim (eq_dart_dec (top m zero y) z).
  rewrite cA_1_eq in |- *.
   elim (pred_dec m zero y).
     tauto.
    tauto.
   tauto.
  tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma A_1_Merge0: forall(m:fmap)(x y z:dart),
 ~expe m x y ->
  inv_hmap m -> exd m x -> exd m y ->
   A_1 (Merge m zero x y) zero z = 
    if eq_dart_dec y z then x
    else if eq_dart_dec (cA m zero x) z then nil
         else if eq_dart_dec (bottom m zero x) z 
              then top m zero x
              else if eq_dart_dec (bottom m zero y) z
                   then top m zero y
                   else A_1 m zero z.
Proof.
intros.
unfold Merge in |- *.
elim (pred_dec m zero y).
 intro.
   assert (A_1 m zero y = cA_1 m zero y).
  rewrite cA_1_eq in |- *.
   elim (pred_dec m zero y);  tauto.
   tauto.
 assert (exd m (cA_1 m zero y)).
  generalize (exd_cA_1 m zero y).
     tauto.
 assert (expe m (cA_1 m zero y) y).
  unfold expe in |- *.
    unfold MA0.MfcA.expo in |- *.
    split.
    tauto.
  split with 1%nat.
    simpl in |- *.
    assert (MA0.MfcA.f m (cA_1 m zero y) =
  cA m zero (cA_1 m zero y)).
    tauto.
  rewrite cA_cA_1 in H5.
    tauto.
   tauto.
   tauto.
 assert (succ m zero (cA_1 m zero y)).
  unfold succ in |- *.
    rewrite <- H3 in |- *.
    rewrite A_A_1 in |- *.
   apply exd_not_nil with m.
     tauto.
    tauto.
   tauto.
   tauto.
 rename H6 into Hsuc.
   set (m0 := Shift m zero (cA_1 m zero y)) in |- *.
   rewrite A_1_G in |- *.
  elim (eq_dart_dec y z).
    tauto.
  intro.
    assert (cA m0 zero x = cA m zero x).
   unfold m0 in |- *.
     rewrite cA_Shift in |- *.
     tauto.
    tauto.
    tauto.
  rewrite H6 in |- *.
    assert (top m0 zero x = top m zero x).
   unfold m0 in |- *.
     rewrite (top_Shift0 m (cA_1 m zero y) x H0) 
    in |- *.
    elim (expe_dec m (cA_1 m zero y) x).
     intro.
       elim H.
       apply expe_trans with (cA_1 m zero y).
      apply expe_symm.
        tauto.
       tauto.
      tauto.
     tauto.
    tauto.
    tauto.
   intro.
     elim H.
     rewrite <- H7 in |- *.
      tauto.
  rewrite H7 in |- *.
    assert (bottom m0 zero x = bottom m zero x).
   unfold m0 in |- *.
     rewrite (bottom_Shift0 m (cA_1 m zero y) x H0) 
  in |- *.
    elim (expe_dec m (cA_1 m zero y) x H0).
     intro.
       elim H.
       apply expe_trans with (cA_1 m zero y).
      apply expe_symm.
        tauto.
       tauto.
      tauto.
     tauto.
    tauto.
    tauto.
   intro.
     elim H.
     rewrite <- H8 in |- *.
      tauto.
  rewrite H8 in |- *.
    elim (eq_dart_dec (cA m zero x) z).
    tauto.
  elim (eq_dart_dec (bottom m zero x) z).
    tauto.
  unfold m0 in |- *.
    rewrite A_1_Shift in |- *.
   rewrite <- H3 in |- *.
     rewrite bottom_A_1 in |- *.
    rewrite A_A_1 in |- *.
     elim (eq_dart_dec y z).
       tauto.
     rewrite top_A_1 in |- *.
       tauto.
      tauto.
      tauto.
     tauto.
     tauto.
    tauto.
    tauto.
   tauto.
   tauto.
 unfold m0 in |- *.
   apply inv_hmap_Shift.
   tauto.
  tauto.
 unfold m0 in |- *.
   generalize (exd_Shift m zero (cA_1 m zero y) x).
    tauto.
intro.
  rewrite A_1_G in |- *.
 elim (eq_dart_dec y z).
   tauto.
 elim (eq_dart_dec (cA m zero x) z).
   tauto.
 elim (eq_dart_dec (bottom m zero x) z).
   tauto.
 elim (eq_dart_dec (bottom m zero y) z).
  intros.
    assert (bottom m zero y = y).
   apply nopred_bottom.
     tauto.
    tauto.
    tauto.
  rewrite <- H3 in b2.
     tauto.
  tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma A_Merge1: forall(m:fmap)(x y z:dart),
 ~expv m x y ->
  inv_hmap m -> exd m x -> exd m y ->
   A (Merge m one x y) one z = 
    if eq_dart_dec x z then y
    else if eq_dart_dec (cA_1 m one y) z then nil
         else if eq_dart_dec (top m one x) z 
              then bottom m one x
              else if eq_dart_dec (top m one y) z
                   then bottom m one y
                   else A m one z.
Proof.
intros.
unfold Merge in |- *.
elim (pred_dec m one y).
 intro.
   assert (A_1 m one y = cA_1 m one y).
  rewrite cA_1_eq in |- *.
   elim (pred_dec m one y);  tauto.
   tauto.
 assert (exd m (cA_1 m one y)).
  generalize (exd_cA_1 m one y).
     tauto.
 assert (expv m (cA_1 m one y) y).
  unfold expv in |- *.
    unfold MA1.MfcA.expo in |- *.
    split.
    tauto.
  split with 1%nat.
    simpl in |- *.
    assert (MA1.MfcA.f m (cA_1 m one y) = 
   cA m one (cA_1 m one y)).
    tauto.
  rewrite cA_cA_1 in H5.
    tauto.
   tauto.
   tauto.
 set (m0 := Shift m one (cA_1 m one y)) in |- *.
   rewrite A_G in |- *.
  elim (eq_dart_dec x z).
    tauto.
  intro.
    assert (top m0 one x = top m one x).
   unfold m0 in |- *.
     rewrite (top_Shift1 m (cA_1 m one y) x H0)
       in |- *.
    elim (expv_dec m (cA_1 m one y) x).
     intro.
       elim H.
       apply expv_trans with (cA_1 m one y).
      apply expv_symm.
        tauto.
       tauto.
      tauto.
     tauto.
   unfold succ in |- *.
     rewrite <- H3 in |- *.
     rewrite A_A_1 in |- *.
    apply exd_not_nil with m.
      tauto.
     tauto.
    tauto.
    tauto.
    tauto.
   intro.
     elim H.
     rewrite <- H6 in |- *.
      tauto.
  rewrite H6 in |- *.
    assert (bottom m0 one x = bottom m one x).
   unfold m0 in |- *.
     rewrite 
  (bottom_Shift1 m (cA_1 m one y) x H0) in |- *.
    elim (expv_dec m (cA_1 m one y) x H0).
     intro.
       elim H.
       apply expv_trans with (cA_1 m one y).
      apply expv_symm.
        tauto.
       tauto.
      tauto.
     tauto.
   unfold succ in |- *.
     rewrite <- H3 in |- *.
     rewrite A_A_1 in |- *.
    apply exd_not_nil with m.
      tauto.
     tauto.
    tauto.
    tauto.
    tauto.
   intro.
     elim H.
     rewrite <- H7 in |- *.
      tauto.
  rewrite H7 in |- *.
    elim (eq_dart_dec (top m one x) z).
   intros.
     elim (eq_dart_dec (cA_1 m one y) z).
    rewrite cA_1_eq in |- *.
     elim (pred_dec m one y).
      intros.
        rewrite <- a2 in a0.
        rewrite H3 in a0.
        rewrite cA_1_eq in a0.
       generalize a0.
         elim (pred_dec m one y).
        intros.
          clear a0.
          rewrite H3 in a4.
          elim H.
          apply expv_trans with (top m one x).
         apply MA1.MfcA.expo_symm.
           tauto.
         apply MA1.expo_top_z.
           tauto.
          tauto.
        rewrite a4 in |- *.
           tauto.
        tauto.
       tauto.
      tauto.
     tauto.
    tauto.
  intros.
    unfold m0 in |- *.
    rewrite A_Shift in |- *.
   elim (eq_dart_dec (cA_1 m one y) z).
     tauto.
   intro.
     rewrite <- H3 in |- *.
     rewrite top_A_1 in |- *.
    elim (eq_dart_dec (top m one y) z).
     intros.
       apply bottom_A_1.
       tauto.
      tauto.
     tauto.
    tauto.
    tauto.
   tauto.
  unfold succ in |- *.
    rewrite <- H3 in |- *.
    rewrite A_A_1 in |- *.
   apply exd_not_nil with m.
     tauto.
    tauto.
   tauto.
   tauto.
 unfold m0 in |- *.
   apply inv_hmap_Shift.
   tauto.
 unfold succ in |- *.
   rewrite <- H3 in |- *.
   rewrite A_A_1 in |- *.
  apply exd_not_nil with m.
    tauto.
   tauto.
  tauto.
  tauto.
 unfold m0 in |- *.
   generalize (exd_Shift m one (cA_1 m one y) x).
    tauto.
intro.
  rewrite A_G in |- *.
 elim (eq_dart_dec x z).
   tauto.
 elim (eq_dart_dec (top m one x) z).
  intros.
    elim (eq_dart_dec (cA_1 m one y) z).
   intro.
     rewrite cA_1_eq in a0.
    generalize a0.
      elim (pred_dec m one y).
      tauto.
    intros.
      elim H.
      generalize (MA1.top_top_expo m x y).
      assert (Md1.kd = one).
      tauto.
    rewrite H3 in |- *.
      rewrite a1 in |- *.
       tauto.
    tauto.
   tauto.
 intros.
   elim (eq_dart_dec (cA_1 m one y) z).
  rewrite cA_1_eq in |- *.
   elim (pred_dec m one y).
     tauto.
   intros.
     rewrite <- a in |- *.
     generalize (not_succ_top m one y).
     unfold succ in |- *.
     generalize 
  (eq_dart_dec (A m one (top m one y)) nil).
      tauto.
   tauto.
 elim (eq_dart_dec (top m one y) z).
  rewrite cA_1_eq in |- *.
   elim (pred_dec m one y).
     tauto.
    tauto.
   tauto.
  tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma A_1_Merge1: forall(m:fmap)(x y z:dart),
 ~expv m x y ->
  inv_hmap m -> exd m x -> exd m y ->
   A_1 (Merge m one x y) one z = 
    if eq_dart_dec y z then x
    else if eq_dart_dec (cA m one x) z then nil
         else if eq_dart_dec (bottom m one x) z 
              then top m one x
              else if eq_dart_dec (bottom m one y) z
                   then top m one y
                   else A_1 m one z.
Proof.
intros.
unfold Merge in |- *.
elim (pred_dec m one y).
 intro.
   assert (A_1 m one y = cA_1 m one y).
  rewrite cA_1_eq in |- *.
   elim (pred_dec m one y);  tauto.
   tauto.
 assert (exd m (cA_1 m one y)).
  generalize (exd_cA_1 m one y).
     tauto.
 assert (expv m (cA_1 m one y) y).
  unfold expv in |- *.
    unfold MA1.MfcA.expo in |- *.
    split.
    tauto.
  split with 1%nat.
    simpl in |- *.
    assert (MA1.MfcA.f m (cA_1 m one y) =
  cA m one (cA_1 m one y)).
    tauto.
  rewrite cA_cA_1 in H5.
    tauto.
   tauto.
   tauto.
 assert (succ m one (cA_1 m one y)).
  unfold succ in |- *.
    rewrite <- H3 in |- *.
    rewrite A_A_1 in |- *.
   apply exd_not_nil with m.
     tauto.
    tauto.
   tauto.
   tauto.
 rename H6 into Hsuc.
   set (m0 := Shift m one (cA_1 m one y)) in |- *.
   rewrite A_1_G in |- *.
  elim (eq_dart_dec y z).
    tauto.
  intro.
    assert (cA m0 one x = cA m one x).
   unfold m0 in |- *.
     rewrite cA_Shift in |- *.
     tauto.
    tauto.
    tauto.
  rewrite H6 in |- *.
    assert (top m0 one x = top m one x).
   unfold m0 in |- *.
     rewrite (top_Shift1 m (cA_1 m one y) x H0) 
    in |- *.
    elim (expv_dec m (cA_1 m one y) x).
     intro.
       elim H.
       apply expv_trans with (cA_1 m one y).
      apply expv_symm.
        tauto.
       tauto.
      tauto.
     tauto.
    tauto.
    tauto.
   intro.
     elim H.
     rewrite <- H7 in |- *.
      tauto.
  rewrite H7 in |- *.
    assert (bottom m0 one x = bottom m one x).
   unfold m0 in |- *.
     rewrite (bottom_Shift1 m (cA_1 m one y) x H0) 
  in |- *.
    elim (expv_dec m (cA_1 m one y) x H0).
     intro.
       elim H.
       apply expv_trans with (cA_1 m one y).
      apply expv_symm.
        tauto.
       tauto.
      tauto.
     tauto.
    tauto.
    tauto.
   intro.
     elim H.
     rewrite <- H8 in |- *.
      tauto.
  rewrite H8 in |- *.
    elim (eq_dart_dec (cA m one x) z).
    tauto.
  elim (eq_dart_dec (bottom m one x) z).
    tauto.
  unfold m0 in |- *.
    rewrite A_1_Shift in |- *.
   rewrite <- H3 in |- *.
     rewrite bottom_A_1 in |- *.
    rewrite A_A_1 in |- *.
     elim (eq_dart_dec y z).
       tauto.
     rewrite top_A_1 in |- *.
       tauto.
      tauto.
      tauto.
     tauto.
     tauto.
    tauto.
    tauto.
   tauto.
   tauto.
 unfold m0 in |- *.
   apply inv_hmap_Shift.
   tauto.
  tauto.
 unfold m0 in |- *.
   generalize (exd_Shift m one (cA_1 m one y) x).
    tauto.
intro.
  rewrite A_1_G in |- *.
 elim (eq_dart_dec y z).
   tauto.
 elim (eq_dart_dec (cA m one x) z).
   tauto.
 elim (eq_dart_dec (bottom m one x) z).
   tauto.
 elim (eq_dart_dec (bottom m one y) z).
  intros.
    assert (bottom m one y = y).
   apply nopred_bottom.
     tauto.
    tauto.
    tauto.
  rewrite <- H3 in b2.
     tauto.
  tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma A_Merge_ter: forall(m:fmap)(k:dim)(x y z:dart),
 inv_hmap m -> exd m x -> exd m y ->
  A (Merge m k x y) (dim_opp k) z = A m (dim_opp k) z.
Proof.
intros.
unfold Merge in |- *.
elim (pred_dec m k y).
 intro.
   assert (A_1 m k y = cA_1 m k y).
  rewrite cA_1_eq in |- *.
   elim (pred_dec m k).
     tauto.
    tauto.
   tauto.
 assert (exd m (cA_1 m k y)).
  generalize (exd_cA_1 m k y).
     tauto.
 assert (succ m k (cA_1 m k y)).
  unfold succ in |- *.
    rewrite <- H2 in |- *.
    rewrite A_A_1 in |- *.
   apply exd_not_nil with m.
     tauto.
    tauto.
   tauto.
   tauto.
 rewrite A_G_ter in |- *.
  rewrite A_Shift_ter in |- *.
    tauto.
   tauto.
   tauto.
 apply inv_hmap_Shift.
   tauto.
  tauto.
intro.
  rewrite A_G_ter in |- *.
  tauto.
tauto.
Qed.

(* OK: *)

Lemma A_1_Merge_ter: forall(m:fmap)(k:dim)(x y z:dart),
 inv_hmap m -> exd m x -> exd m y ->
  A_1 (Merge m k x y) (dim_opp k) z = 
        A_1 m (dim_opp k) z.
Proof.
intros.
unfold Merge in |- *.
elim (pred_dec m k y).
 intro.
   assert (A_1 m k y = cA_1 m k y).
  rewrite cA_1_eq in |- *.
   elim (pred_dec m k).
     tauto.
    tauto.
   tauto.
 assert (exd m (cA_1 m k y)).
  generalize (exd_cA_1 m k y).
     tauto.
 assert (succ m k (cA_1 m k y)).
  unfold succ in |- *.
    rewrite <- H2 in |- *.
    rewrite A_A_1 in |- *.
   apply exd_not_nil with m.
     tauto.
    tauto.
   tauto.
   tauto.
 rewrite A_1_G_ter in |- *.
  rewrite A_1_Shift_ter in |- *.
    tauto.
   tauto.
   tauto.
 apply inv_hmap_Shift.
   tauto.
  tauto.
intro.
  rewrite A_1_G_ter in |- *.
  tauto.
tauto.
Qed.

(* OK!! *)

Lemma cA_Merge: 
forall(m:fmap)(k:dim)(x y:dart)(j:dim)(z:dart),
 inv_hmap m -> 
  cA (Merge m k x y) j z = 
   if eq_dim_dec k j 
   then  if eq_dart_dec x z then y
           else if eq_dart_dec (cA_1 m k y) z then cA m k x
                  else cA m k z
   else cA m j z.
Proof.
intros.
elim (eq_dim_dec k j). intro. rewrite <-a. 
unfold Merge in |- *.
elim (pred_dec m k y).
 intro.
   assert (succ m k (cA_1 m k y)).
   unfold succ. rewrite cA_1_eq. 
          elim (pred_dec m k y). rewrite A_A_1. intro. 
          intro. rewrite H0 in a0. unfold pred in a0. 
          rewrite A_1_nil in a0.
        tauto. tauto. tauto. tauto. tauto. tauto. 
  set (m0 := Shift m k (cA_1 m k y)) in |- *.
   rewrite cA_G in |- *. 
      unfold m0. rewrite cA_Shift. 
          rewrite cA_1_Shift. rewrite cA_Shift. tauto.
            tauto. tauto. tauto. tauto. tauto. tauto. 
      unfold m0. apply inv_hmap_Shift. tauto. tauto. 
       rewrite cA_G in |- *. tauto. tauto.
  intro. unfold Merge in |- *.
    elim (pred_dec m k y).  intro. 
      assert (succ m k (cA_1 m k y)).
   unfold succ. rewrite cA_1_eq. 
          elim (pred_dec m k y). rewrite A_A_1. intro. 
          intro. rewrite H0 in a0. unfold pred in a0. 
          rewrite A_1_nil in a0.
        tauto. tauto. tauto. tauto. tauto. tauto. 
      assert (j = dim_opp k). induction k. simpl. 
           induction j. tauto. tauto. simpl. 
              induction j. tauto. tauto. rewrite H1. 
         rewrite cA_G_ter in |- *. 
         rewrite cA_Shift_ter. tauto.  tauto. tauto.
             apply inv_hmap_Shift. tauto. tauto. 
            assert (j = dim_opp k). induction k. simpl. 
           induction j. tauto. tauto. simpl. 
              induction j. tauto. tauto. rewrite H0. 
         rewrite cA_G_ter in |- *. tauto. tauto. 
Qed.
  

(* OK: *)

Lemma cA_1_Merge: 
forall(m:fmap)(k:dim)(x y:dart)(j:dim)( z:dart),
 inv_hmap m -> 
  cA_1 (Merge m k x y) j z = 
   if eq_dim_dec k j 
   then if eq_dart_dec y z then x
          else if eq_dart_dec (cA m k x) z then cA_1 m k y 
         else cA_1 m k z
   else cA_1 m j z.
Proof.
intros.
elim (eq_dim_dec k j). intro. rewrite <-a. 
unfold Merge in |- *.
elim (pred_dec m k y).
 intro.
   assert (succ m k (cA_1 m k y)).
   unfold succ. rewrite cA_1_eq. 
          elim (pred_dec m k y). rewrite A_A_1. intro. 
          intro. rewrite H0 in a0. unfold pred in a0. 
          rewrite A_1_nil in a0.
        tauto. tauto. tauto. tauto. tauto. tauto. 
  set (m0 := Shift m k (cA_1 m k y)) in |- *.
   rewrite cA_1_G in |- *. 
      unfold m0. rewrite cA_1_Shift. 
          rewrite cA_1_Shift. rewrite cA_Shift. tauto.
            tauto. tauto. tauto. tauto. tauto. tauto. 
      unfold m0. apply inv_hmap_Shift. tauto. tauto. 
       rewrite cA_1_G in |- *. tauto. tauto.
intro. 
    assert (j = dim_opp k). induction k. simpl. 
           induction j. tauto. tauto. simpl. 
              induction j. tauto. tauto. rewrite H0. 
    unfold Merge. 
     elim (pred_dec m k y).  intro. 
      assert (succ m k (cA_1 m k y)).
   unfold succ. rewrite cA_1_eq. 
          elim (pred_dec m k y). rewrite A_A_1. intro. 
          intro. rewrite H1 in a0. unfold pred in a0. 
          rewrite A_1_nil in a0.
        tauto. tauto. tauto. tauto. tauto. tauto. 
    set (m0 := Shift m k (cA_1 m k y)) in |- *.
   rewrite cA_1_G_ter in |- *.
   unfold m0. rewrite cA_1_Shift_ter. 
 tauto. tauto. tauto. 
 unfold m0. apply inv_hmap_Shift. tauto. tauto. 
    rewrite cA_1_G_ter in |- *.
 tauto. tauto.
Qed.

(* OK: *)

Lemma inv_hmap_Merge: forall(m:fmap)(x y:dart),
 inv_hmap m -> exd m x -> exd m y -> 
   ~expe m x y ->
      inv_hmap (Merge m zero x y).
Proof.
intros.
unfold Merge in |- *.
elim (pred_dec m zero y).
 intro.
   assert (A_1 m zero y = cA_1 m zero y).
  rewrite cA_1_eq in |- *.
   elim (pred_dec m zero y);  tauto.
   tauto.
 assert (exd m (cA_1 m zero y)).
  generalize (exd_cA_1 m zero y).
     tauto.
 assert (succ m zero (cA_1 m zero y)).
  unfold succ in |- *.
    rewrite <- H3 in |- *.
    rewrite A_A_1 in |- *.
   apply exd_not_nil with m.
     tauto.
    tauto.
   tauto.
   tauto.
 apply inv_hmap_G0.
  apply inv_hmap_Shift.
    tauto.
   tauto.
 generalize (exd_Shift m zero (cA_1 m zero y) x).
    tauto.
 generalize (exd_Shift m zero (cA_1 m zero y) y).
    tauto.
 unfold pred in |- *.
   rewrite A_1_Shift in |- *.
  rewrite <- H3 in |- *.
    rewrite A_A_1 in |- *.
   elim (eq_dart_dec y y).
     tauto.
    tauto.
   tauto.
   tauto.
  tauto.
  tauto.
 intro.
   generalize (expe_Shift m (cA_1 m zero y) x y).
    tauto.
intro.
  apply inv_hmap_G0.
  tauto.
 tauto.
 tauto.
 tauto.
 tauto.
Qed.


Lemma inv_hmap_Merge0: forall(m:fmap)(x y:dart),
 inv_hmap m -> exd m x -> exd m y -> 
   ~expe m x y ->
      inv_hmap (Merge m zero x y).
Proof.
intros.
unfold Merge in |- *.
elim (pred_dec m zero y).
 intro.
   assert (A_1 m zero y = cA_1 m zero y).
  rewrite cA_1_eq in |- *.
   elim (pred_dec m zero y);  tauto.
   tauto.
 assert (exd m (cA_1 m zero y)).
  generalize (exd_cA_1 m zero y).
     tauto.
 assert (succ m zero (cA_1 m zero y)).
  unfold succ in |- *.
    rewrite <- H3 in |- *.
    rewrite A_A_1 in |- *.
   apply exd_not_nil with m.
     tauto.
    tauto.
   tauto.
   tauto.
 apply inv_hmap_G0.
  apply inv_hmap_Shift.
    tauto.
   tauto.
 generalize (exd_Shift m zero (cA_1 m zero y) x).
    tauto.
 generalize (exd_Shift m zero (cA_1 m zero y) y).
    tauto.
 unfold pred in |- *.
   rewrite A_1_Shift in |- *.
  rewrite <- H3 in |- *.
    rewrite A_A_1 in |- *.
   elim (eq_dart_dec y y).
     tauto.
    tauto.
   tauto.
   tauto.
  tauto.
  tauto.
 intro.
   generalize (expe_Shift m (cA_1 m zero y) x y).
    tauto.
intro.
  apply inv_hmap_G0.
  tauto.
 tauto.
 tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma inv_hmap_Merge1: forall(m:fmap)(x y:dart),
 inv_hmap m -> exd m x -> exd m y -> 
   ~expv m x y ->
      inv_hmap (Merge m one x y).
Proof.
intros.
unfold Merge in |- *.
elim (pred_dec m one y).
 intro.
   assert (A_1 m one y = cA_1 m one y).
  rewrite cA_1_eq in |- *.
   elim (pred_dec m one y);  tauto.
   tauto.
 assert (exd m (cA_1 m one y)).
  generalize (exd_cA_1 m one y).
     tauto.
 assert (succ m one (cA_1 m one y)).
  unfold succ in |- *.
    rewrite <- H3 in |- *.
    rewrite A_A_1 in |- *.
   apply exd_not_nil with m.
     tauto.
    tauto.
   tauto.
   tauto.
 apply inv_hmap_G1.
  apply inv_hmap_Shift.
    tauto.
   tauto.
 generalize (exd_Shift m one (cA_1 m one y) x).
    tauto.
 generalize (exd_Shift m one (cA_1 m one y) y).
    tauto.
 unfold pred in |- *.
   rewrite A_1_Shift in |- *.
  rewrite <- H3 in |- *.
    rewrite A_A_1 in |- *.
   elim (eq_dart_dec y y).
     tauto.
    tauto.
   tauto.
   tauto.
  tauto.
  tauto.
 intro.
   generalize (expv_Shift m (cA_1 m one y) x y).
    tauto.
intro.
  apply inv_hmap_G1.
  tauto.
 tauto.
 tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma ndN_Merge: forall(m:fmap)(k:dim)(x y:dart), 
  ndN (Merge m k x y) = ndN m.
Proof.
intros.
unfold Merge in |- *.
elim (pred_dec m k y).
 rewrite ndN_G in |- *.
   unfold Shift in |- *.
   simpl in |- *.
   rewrite ndN_B in |- *.
    tauto.
rewrite ndN_G in |- *.
   tauto.
Qed.

(* OK: *)

Lemma top_Merge0: 
 forall(m:fmap)(x y z:dart)(H :inv_hmap m) ,
  exd m x -> exd m y -> exd m z ->
   ~ expe m x y ->  
  let y_0:= cA_1 m zero y in
  top (Merge m zero x y) zero z = 
    if expe_dec m x z H then y_0
    else if expe_dec m y z H then y_0
         else top m zero z.
Proof.
intros.
unfold Merge in |- *.
elim (pred_dec m zero y).
 intro.
   assert (A_1 m zero y = cA_1 m zero y).
  rewrite cA_1_eq in |- *.
   elim (pred_dec m zero y);  tauto.
   tauto.
 assert (exd m (cA_1 m zero y)).
  generalize (exd_cA_1 m zero y).
     tauto.
 assert (succ m zero (cA_1 m zero y)).
  unfold succ in |- *.
    apply exd_not_nil with m.
    tauto.
  rewrite <- H4 in |- *.
    rewrite A_A_1 in |- *.
    tauto.
   tauto.
   tauto.
 set (m0 := Shift m zero (cA_1 m zero y)) in |- *.
   assert (inv_hmap m0).
  unfold m0 in |- *.
    apply inv_hmap_Shift.
    tauto.
   tauto.
 rewrite (top_G0 m0 x y z H7) in |- *.
  generalize (MA0.expo_Shift m (cA_1 m zero y) x z).
    assert (Md0.kd = zero).
    tauto.
  rewrite H8 in |- *.
    intro.
    simpl in H9.
    fold m0 in H9.
    elim (expe_dec m0 x z H7).
   elim (expe_dec m x z H).
    intros.
      unfold m0 in |- *.
      rewrite cA_1_Shift in |- *.
     fold y_0 in |- *.
        tauto.
     tauto.
     tauto.
    tauto.
  elim (expe_dec m x z H).
    tauto.
  intros.
    unfold m0 in |- *.
    rewrite cA_1_Shift in |- *.
   fold m0 in |- *.
     fold y_0 in |- *.
     generalize (MA0.expo_Shift m (cA_1 m zero y) y z).
     intro.
     simpl in H10.
     rewrite H8 in H10.
     fold m0 in H10.
     elim (expe_dec m0 y z H7).
    elim (expe_dec m y z H).
      tauto.
     tauto.
   elim (expe_dec m y z H).
     tauto.
   intros.
     unfold m0 in |- *.
     rewrite (top_Shift0_bis m (cA_1 m zero y) z H)
    in |- *.
    elim (expe_dec m (cA_1 m zero y) z).
     intro.
       assert (expe m (cA_1 m zero y) y).
      unfold expe in |- *.
        unfold MA0.MfcA.expo in |- *.
        split.
        tauto.
      split with 1%nat.
        simpl in |- *.
        assert (MA0.MfcA.f m (cA_1 m zero y) =
      cA m zero (cA_1 m zero y)).
        tauto.
      rewrite cA_cA_1 in H11.
        tauto.
       tauto.
       tauto.
     elim b1.
       apply MA0.MfcA.expo_trans with (cA_1 m zero y).
      apply expe_symm.
        tauto.
       tauto.
      tauto.
     tauto.
    tauto.
    tauto.
   tauto.
   tauto.
 unfold m0 in |- *.
   generalize (exd_Shift m zero (cA_1 m zero y) x).
    tauto.
 generalize (exd_Shift m zero (cA_1 m zero y) y).
   fold m0 in |- *.
    tauto.
 generalize (exd_Shift m zero (cA_1 m zero y) z).
   fold m0 in |- *.
    tauto.
 generalize (MA0.expo_Shift m (cA_1 m zero y) x y).
   simpl in |- *.
   assert (Md0.kd = zero).
   tauto.
 rewrite H8 in |- *.
   fold m0 in |- *.
    tauto.
 unfold m0 in |- *.
   unfold pred in |- *.
   rewrite A_1_Shift in |- *.
  rewrite <- H4 in |- *.
    rewrite A_A_1 in |- *.
   elim (eq_dart_dec y y).
     tauto.
    tauto.
   tauto.
   tauto.
  tauto.
  tauto.
intro.
  unfold y_0 in |- *.
  apply top_G0.
  tauto.
 tauto.
 tauto.
 tauto.
tauto.
Qed.

(* OK: *)

Lemma top_Merge1: 
 forall(m:fmap)(x y z:dart)(H :inv_hmap m) ,
  exd m x -> exd m y -> exd m z ->
   ~ expv m x y ->  
  let y_0:= cA_1 m one y in
  top (Merge m one x y) one z = 
    if expv_dec m x z H then y_0
    else if expv_dec m y z H then y_0
         else top m one z.
Proof.
intros.
unfold Merge in |- *.
elim (pred_dec m one y).
 intro.
   intros.
   assert (A_1 m one y = cA_1 m one y).
  rewrite cA_1_eq in |- *.
   elim (pred_dec m one y);  tauto.
   tauto.
 assert (exd m (cA_1 m one y)).
  generalize (exd_cA_1 m one y).
     tauto.
 assert (succ m one (cA_1 m one y)).
  unfold succ in |- *.
    apply exd_not_nil with m.
    tauto.
  rewrite <- H4 in |- *.
    rewrite A_A_1 in |- *.
    tauto.
   tauto.
   tauto.
 set (m0 := Shift m one (cA_1 m one y)) in |- *.
   assert (inv_hmap m0).
  unfold m0 in |- *.
    apply inv_hmap_Shift.
    tauto.
   tauto.
 rewrite (top_G1 m0 x y z H7) in |- *.
  generalize (MA1.expo_Shift m (cA_1 m one y) x z).
    assert (Md1.kd = one).
    tauto.
  rewrite H8 in |- *.
    intro.
    simpl in H9.
    fold m0 in H9.
    elim (expv_dec m0 x z H7).
   elim (expv_dec m x z H).
    intros.
      unfold m0 in |- *.
      rewrite cA_1_Shift in |- *.
     fold y_0 in |- *.
        tauto.
     tauto.
     tauto.
    tauto.
  elim (expv_dec m x z H).
    tauto.
  intros.
    unfold m0 in |- *.
    rewrite cA_1_Shift in |- *.
   fold m0 in |- *.
     fold y_0 in |- *.
     generalize (MA1.expo_Shift m (cA_1 m one y) y z).
     intro.
     simpl in H10.
     rewrite H8 in H10.
     fold m0 in H10.
     elim (expv_dec m0 y z H7).
    elim (expv_dec m y z H).
      tauto.
     tauto.
   elim (expv_dec m y z H).
     tauto.
   intros.
     unfold m0 in |- *.
     rewrite (top_Shift1_bis m (cA_1 m one y) z H)
    in |- *.
    elim (expv_dec m (cA_1 m one y) z).
     intro.
       assert (expv m (cA_1 m one y) y).
      unfold expv in |- *.
        unfold MA1.MfcA.expo in |- *.
        split.
        tauto.
      split with 1%nat.
        simpl in |- *.
        assert (MA1.MfcA.f m (cA_1 m one y) =
      cA m one (cA_1 m one y)).
        tauto.
      rewrite cA_cA_1 in H11.
        tauto.
       tauto.
       tauto.
     elim b1.
       apply MA1.MfcA.expo_trans with (cA_1 m one y).
      apply expv_symm.
        tauto.
       tauto.
      tauto.
     tauto.
    tauto.
    tauto.
   tauto.
   tauto.
 unfold m0 in |- *.
   generalize (exd_Shift m one (cA_1 m one y) x).
    tauto.
 generalize (exd_Shift m one (cA_1 m one y) y).
   fold m0 in |- *.
    tauto.
 generalize (exd_Shift m one (cA_1 m one y) z).
   fold m0 in |- *.
    tauto.
 generalize (MA1.expo_Shift m (cA_1 m one y) x y).
   simpl in |- *.
   assert (Md1.kd = one).
   tauto.
 rewrite H8 in |- *.
   fold m0 in |- *.
    tauto.
 unfold m0 in |- *.
   unfold pred in |- *.
   rewrite A_1_Shift in |- *.
  rewrite <- H4 in |- *.
    rewrite A_A_1 in |- *.
   elim (eq_dart_dec y y).
     tauto.
    tauto.
   tauto.
   tauto.
  tauto.
  tauto.
intro.
  unfold y_0 in |- *.
  apply top_G1.
  tauto.
 tauto.
 tauto.
 tauto.
tauto.
Qed.

(* OK: *)

Lemma bottom_Merge0: 
 forall(m:fmap)(x y z:dart)(H :inv_hmap m),
  exd m x -> exd m y -> exd m z ->
   ~ expe m x y ->
  let x0:= cA m zero x in
  bottom (Merge m zero x y) zero z = 
    if expe_dec m x z H then x0
    else if expe_dec m y z H then x0
         else bottom m zero z.
Proof.
intros.
unfold Merge in |- *.
elim (pred_dec m zero y).
 intro.
   assert (A_1 m zero y = cA_1 m zero y).
  rewrite cA_1_eq in |- *.
   elim (pred_dec m zero y);  tauto.
   tauto.
 assert (exd m (cA_1 m zero y)).
  generalize (exd_cA_1 m zero y).
     tauto.
 assert (succ m zero (cA_1 m zero y)).
  unfold succ in |- *.
    apply exd_not_nil with m.
    tauto.
  rewrite <- H4 in |- *.
    rewrite A_A_1 in |- *.
    tauto.
   tauto.
   tauto.
 set (m0 := Shift m zero (cA_1 m zero y)) in |- *.
   assert (inv_hmap m0).
  unfold m0 in |- *.
    apply inv_hmap_Shift.
    tauto.
   tauto.
 rewrite (bottom_G0 m0 x y z H7) in |- *.
  assert (Md0.kd = zero).
    tauto.
  generalize (MA0.expo_Shift m (cA_1 m zero y) x z).
    rewrite H8 in |- *.
    intro.
    simpl in H9.
    fold m0 in H9.
    elim (expe_dec m0 x z H7).
   elim (expe_dec m x z H).
    intros.
      unfold m0 in |- *.
      rewrite cA_Shift in |- *.
     fold x0 in |- *.
        tauto.
     tauto.
     tauto.
    tauto.
  elim (expe_dec m x z H).
    tauto.
  intros.
    unfold m0 in |- *.
    rewrite cA_Shift in |- *.
   fold m0 in |- *.
     fold x0 in |- *.
     generalize (MA0.expo_Shift m (cA_1 m zero y) y z).
     intro.
     simpl in H10.
     rewrite H8 in H10.
     fold m0 in H10.
     elim (expe_dec m0 y z H7).
    elim (expe_dec m y z H).
      tauto.
     tauto.
   elim (expe_dec m y z H).
     tauto.
   intros.
     unfold m0 in |- *.
     rewrite 
 (bottom_Shift0_bis m (cA_1 m zero y) z H) in |- *.
    elim (expe_dec m (cA_1 m zero y) z).
     intro.
       assert (expe m (cA_1 m zero y) y).
      unfold expe in |- *.
        unfold MA0.MfcA.expo in |- *.
        split.
        tauto.
      split with 1%nat.
        simpl in |- *.
        assert (MA0.MfcA.f m (cA_1 m zero y) = 
    cA m zero (cA_1 m zero y)).
        tauto.
      rewrite cA_cA_1 in H11.
        tauto.
       tauto.
       tauto.
     elim b1.
       apply MA0.MfcA.expo_trans with (cA_1 m zero y).
      apply expe_symm.
        tauto.
       tauto.
      tauto.
     tauto.
    tauto.
    tauto.
   tauto.
   tauto.
 unfold m0 in |- *.
   generalize (exd_Shift m zero (cA_1 m zero y) x).
    tauto.
 generalize (exd_Shift m zero (cA_1 m zero y) y).
   fold m0 in |- *.
    tauto.
 generalize (exd_Shift m zero (cA_1 m zero y) z).
   fold m0 in |- *.
    tauto.
 generalize (MA0.expo_Shift m (cA_1 m zero y) x y).
   simpl in |- *.
   assert (Md0.kd = zero).
   tauto.
 rewrite H8 in |- *.
   fold m0 in |- *.
    tauto.
 unfold m0 in |- *.
   unfold pred in |- *.
   rewrite A_1_Shift in |- *.
  rewrite <- H4 in |- *.
    rewrite A_A_1 in |- *.
   elim (eq_dart_dec y y).
     tauto.
    tauto.
   tauto.
   tauto.
  tauto.
  tauto.
intro.
  unfold x0 in |- *.
  apply bottom_G0.
  tauto.
 tauto.
 tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma bottom_Merge1: 
 forall(m:fmap)(x y z:dart)(H :inv_hmap m) ,
  exd m x -> exd m y -> exd m z ->
   ~ expv m x y -> 
  let x1:= cA m one x in
  bottom (Merge m one x y) one z = 
    if expv_dec m x z H then x1
    else if expv_dec m y z H then x1
         else bottom m one z.
Proof.
intros.
unfold Merge in |- *.
elim (pred_dec m one y).
 intro.
   assert (A_1 m one y = cA_1 m one y).
  rewrite cA_1_eq in |- *.
   elim (pred_dec m one y);  tauto.
   tauto.
 assert (exd m (cA_1 m one y)).
  generalize (exd_cA_1 m one y).
     tauto.
 assert (succ m one (cA_1 m one y)).
  unfold succ in |- *.
    apply exd_not_nil with m.
    tauto.
  rewrite <- H4 in |- *.
    rewrite A_A_1 in |- *.
    tauto.
   tauto.
   tauto.
 set (m0 := Shift m one (cA_1 m one y)) in |- *.
   assert (inv_hmap m0).
  unfold m0 in |- *.
    apply inv_hmap_Shift.
    tauto.
   tauto.
 rewrite (bottom_G1 m0 x y z H7) in |- *.
  assert (Md1.kd = one).
    tauto.
  generalize (MA1.expo_Shift m (cA_1 m one y) x z).
    rewrite H8 in |- *.
    intro.
    simpl in H9.
    fold m0 in H9.
    elim (expv_dec m0 x z H7).
   elim (expv_dec m x z H).
    intros.
      unfold m0 in |- *.
      rewrite cA_Shift in |- *.
     fold x1 in |- *.
        tauto.
     tauto.
     tauto.
    tauto.
  elim (expv_dec m x z H).
    tauto.
  intros.
    unfold m0 in |- *.
    rewrite cA_Shift in |- *.
   fold m0 in |- *.
     fold x1 in |- *.
     generalize (MA1.expo_Shift m (cA_1 m one y) y z).
     intro.
     simpl in H10.
     rewrite H8 in H10.
     fold m0 in H10.
     elim (expv_dec m0 y z H7).
    elim (expv_dec m y z H).
      tauto.
     tauto.
   elim (expv_dec m y z H).
     tauto.
   intros.
     unfold m0 in |- *.
     rewrite 
 (bottom_Shift1_bis m (cA_1 m one y) z H) in |- *.
    elim (expv_dec m (cA_1 m one y) z).
     intro.
       assert (expv m (cA_1 m one y) y).
      unfold expv in |- *.
        unfold MA1.MfcA.expo in |- *.
        split.
        tauto.
      split with 1%nat.
        simpl in |- *.
        assert (MA1.MfcA.f m (cA_1 m one y) = 
    cA m one (cA_1 m one y)).
        tauto.
      rewrite cA_cA_1 in H11.
        tauto.
       tauto.
       tauto.
     elim b1.
       apply MA1.MfcA.expo_trans with (cA_1 m one y).
      apply expv_symm.
        tauto.
       tauto.
      tauto.
     tauto.
    tauto.
    tauto.
   tauto.
   tauto.
 unfold m0 in |- *.
   generalize (exd_Shift m one (cA_1 m one y) x).
    tauto.
 generalize (exd_Shift m one (cA_1 m one y) y).
   fold m0 in |- *.
    tauto.
 generalize (exd_Shift m one (cA_1 m one y) z).
   fold m0 in |- *.
    tauto.
 generalize (MA1.expo_Shift m (cA_1 m one y) x y).
   simpl in |- *.
   assert (Md1.kd = one).
   tauto.
 rewrite H8 in |- *.
   fold m0 in |- *.
    tauto.
 unfold m0 in |- *.
   unfold pred in |- *.
   rewrite A_1_Shift in |- *.
  rewrite <- H4 in |- *.
    rewrite A_A_1 in |- *.
   elim (eq_dart_dec y y).
     tauto.
    tauto.
   tauto.
   tauto.
  tauto.
  tauto.
intro.
  unfold x1 in |- *.
  apply bottom_G1.
  tauto.
 tauto.
 tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma ne_Merge0 : 
 forall(m:fmap)(x y:dart), 
  inv_hmap m -> exd m y -> 
   ~ expe m x y -> 
   ne (Merge m zero x y) = ne m - 1. 
Proof.
unfold Merge in |- *.
intros.
  set (m0 := Shift m zero (cA_1 m zero y)) in |- *.
elim (pred_dec m zero y).
 intros.
   assert (A_1 m zero y = cA_1 m zero y).
  rewrite cA_1_eq in |- *.
   elim (pred_dec m zero y);  tauto.
   tauto.
 assert (exd m (cA_1 m zero y)).
  generalize (exd_cA_1 m zero y).
     tauto.
 assert (succ m zero (cA_1 m zero y)).
  unfold succ in |- *.
    apply exd_not_nil with m.
    tauto.
  rewrite <- H2 in |- *.
    rewrite A_A_1 in |- *.
    tauto.
   tauto.
   tauto.
 assert (inv_hmap m0).
  unfold m0 in |- *.
    apply inv_hmap_Shift.
    tauto.
   tauto.
 unfold m0 in |- *.
   rewrite ne_G0.
  rewrite ne_Shift0 in |- *.
    tauto.
   tauto.
   tauto.
 fold m0 in |- *.
    tauto.
intro. 
rewrite ne_G0. tauto. tauto. 
Qed.

(* OK: *)

Lemma nv_Merge1 : 
 forall(m:fmap)(x y:dart), 
  inv_hmap m -> exd m y -> 
   ~ expv m x y -> 
   nv (Merge m one x y) = nv m - 1. 
Proof.
unfold Merge in |- *.
intros.
elim (pred_dec m one y).
 intros.
   set (m0 := Shift m one (cA_1 m one y)) in |- *.
   assert (A_1 m one y = cA_1 m one y).
  rewrite cA_1_eq in |- *.
   elim (pred_dec m one y);  tauto.
   tauto.
 assert (exd m (cA_1 m one y)).
  generalize (exd_cA_1 m one y).
     tauto.
 assert (succ m one (cA_1 m one y)).
  unfold succ in |- *.
    apply exd_not_nil with m.
    tauto.
  rewrite <- H2 in |- *.
    rewrite A_A_1 in |- *.
    tauto.
   tauto.
   tauto.
 assert (inv_hmap m0).
  unfold m0 in |- *.
    apply inv_hmap_Shift.
    tauto.
   tauto.
 unfold m0 in |- *.
   rewrite nv_G1.
  rewrite nv_Shift1 in |- *.
    tauto.
   tauto.
   tauto.
 fold m0 in |- *.
    tauto.
rewrite nv_G1. tauto. tauto.
Qed.

(* OK: *)

Lemma nv_Merge0 : forall(m:fmap)(x y:dart), 
  inv_hmap m -> exd m y -> 
   ~ expe m x y -> 
   nv (Merge m zero x y) = nv m. 
Proof.
unfold Merge in |- *.
intros.
elim (pred_dec m zero y).
 intros.
   set (m0 := Shift m zero (cA_1 m zero y)) in |- *.
   assert (A_1 m zero y = cA_1 m zero y).
  rewrite cA_1_eq in |- *.
   elim (pred_dec m zero y);  tauto.
   tauto.
 assert (exd m (cA_1 m zero y)).
  generalize (exd_cA_1 m zero y).
     tauto.
 assert (succ m zero (cA_1 m zero y)).
  unfold succ in |- *.
    apply exd_not_nil with m.
    tauto.
  rewrite <- H2 in |- *.
    rewrite A_A_1 in |- *.
    tauto.
   tauto.
   tauto.
 assert (inv_hmap m0).
  unfold m0 in |- *.
    apply inv_hmap_Shift.
    tauto.
   tauto.
 rewrite nv_G0.
  unfold m0 in |- *.
    rewrite nv_Shift0 in |- *.
    tauto.
   tauto.
   tauto.
  tauto.
rewrite nv_G0. tauto. tauto.
Qed.

Lemma ne_Merge1 : forall(m:fmap)(x y:dart), 
  inv_hmap m -> exd m y -> 
   ~ expv m x y -> 
   ne (Merge m one x y) = ne m. 
Proof.
unfold Merge in |- *.
intros.
elim (pred_dec m one y).
 intros.
   set (m0 := Shift m one (cA_1 m one y)) in |- *.
   assert (A_1 m one y = cA_1 m one y).
  rewrite cA_1_eq in |- *.
   elim (pred_dec m one y).  tauto.
   tauto. tauto.
 assert (exd m (cA_1 m one y)).
  generalize (exd_cA_1 m one y).
     tauto.
 assert (succ m one (cA_1 m one y)).
  unfold succ in |- *.
    apply exd_not_nil with m.
    tauto.
  rewrite <- H2 in |- *.
    rewrite A_A_1 in |- *.
    tauto.
   tauto.
   tauto.
 assert (inv_hmap m0).
  unfold m0 in |- *.
    apply inv_hmap_Shift.
    tauto.
   tauto.
 rewrite ne_G1.
  unfold m0 in |- *.
    rewrite ne_Shift1 in |- *.
    tauto.
   tauto.
   tauto.
  tauto.
rewrite ne_G1. tauto. tauto.
Qed.

(*====================================================
                 k-ORBITS FOR Merge
    INSTANTIATIONS OF MTr WITH Tr = Gk, G0, G1
            WRT TO  cAk, cA0, cA1 
=====================================================*)

Lemma cA_Mergek:forall(m:fmap)(k:dim)(x y z:dart), 
 True -> 
  inv_hmap m -> exd m x -> exd m y -> exd m z -> 
  cA (Merge m k x y) k z =  
     if eq_dart_dec x z then y
     else if eq_dart_dec (cA_1 m k y) z 
          then cA m k x 
          else cA m k z.
Proof. 
intros. rewrite cA_Merge. elim (eq_dim_dec k k). 
tauto. tauto. tauto. 
Qed.

Lemma cA_1_Mergek:forall(m:fmap)(k:dim)(x y z:dart), 
 True -> 
  inv_hmap m -> exd m x -> exd m y -> exd m z -> 
  cA_1 (Merge m k x y) k z =
    if eq_dart_dec y z then x
    else if eq_dart_dec (cA m k x) z then cA_1 m k y 
         else cA_1 m k z.
Proof. 
intros. rewrite cA_1_Merge. elim (eq_dim_dec k k). tauto. tauto. tauto.
Qed.

Module ModcAMerge(Md:Sigd)<:SigTr 
 with Definition Tr:=fun(m:fmap)(x y:dart) => 
    Merge m Md.kd x y
 with Definition Prec_Tr:=fun(m:fmap)(x y:dart) =>
    True.
Module M := McA Md.    (* : Sigf *)
Definition Tr(m:fmap)(x y:dart):= Merge m Md.kd x y.
Definition Prec_Tr(m:fmap)(x y:dart):= True.
Definition f_Tr(m:fmap):= cA_Mergek m Md.kd.
Definition f_1_Tr(m:fmap):= cA_1_Mergek m Md.kd.
Definition exd_Tr(m:fmap):= exd_Merge_bis m Md.kd.
Definition ndN_Tr(m:fmap):= ndN_Merge m Md.kd.
End ModcAMerge.

(*===================================================
   INSTANTIATIONS FOR Tr = L0, L1 WRT TO cA0, cA1
====================================================*)

(* IMMEDIATE: *)

Module ModcAMerge0 := ModcAMerge Md0.
Module MAMerge0Tr := MTr ModcAMerge0.

Module ModcAMerge1 := ModcAMerge Md1.
Module MAMerge1Tr := MTr ModcAMerge1.

(*==================================================
         DIMENSION 0: expe_G0, degreee_G0
             (MERGE ONLY:)
===================================================*)

(* OK: *)

Theorem expe_Merge0_CNS:
 forall (m:fmap)(x y z t:dart)(H:inv_hmap m),
   exd m x -> exd m y -> exd m z -> 
    ~ expe m x y -> 
     let m1 := Merge m zero x y in
      (expe m1 z t <->
         expe m z t \/
         expe m x z /\ expe m y t \/
         expe m x t /\ expe m y z).
Proof.
intros.
assert (inv_hmap m1).
 unfold m1 in |- *.
   apply (inv_hmap_Merge0 m x y H H0 H1 H3).
assert (ModcAMerge0.Prec_Tr m x y).
 unfold ModcAMerge0.Prec_Tr in |- *.
    tauto.
generalize (MAMerge0Tr.expo_Tr_CNS m x y z t H H5 H0 H1 H2 H4).
  elim (MAMerge0Tr.MfM.expo_dec m x y H).
  tauto.
 tauto.
Qed.

(* OK: *)

Lemma Iter_cA0_MAMerge0Tr_f: 
   forall (m : fmap) (x : dart) (j : nat),
       Iter (cA m zero) j x = 
          Iter (MAMerge0Tr.MfM.f m) j x.
Proof.
intros.
induction j.
 simpl in |- *.
    tauto.
simpl in |- *; rewrite IHj in |- *.
   tauto.
Qed.

Lemma Iter_cA1_MAMerge1Tr_f: 
   forall (m : fmap) (x : dart) (j : nat),
       Iter (cA m one) j x = 
          Iter (MAMerge1Tr.MfM.f m) j x.
Proof.
intros.
induction j.
 simpl in |- *.
    tauto.
simpl in |- *; rewrite IHj in |- *.
   tauto.
Qed.

(* DIM 0 *)

(* OK: *)

Theorem degreee_Merge0_summary:
  forall (m:fmap)(x y z:dart)(H:inv_hmap m),
    exd m x -> exd m y -> exd m z ->
       let m1 := Merge m zero x y in
       let dx := degreee m x in
       let dy := degreee m y in
   ~ expe m x y ->
      degreee m1 z =
        if expe_dec m x z H
        then (dx + dy)%nat
        else if expe_dec m y z H
             then (dx + dy)%nat
             else degreee m z.
Proof.
intros.
unfold degreee in |- *.
assert (m1 = ModcAMerge0.Tr m x y).
 unfold m1 in |- *.
    tauto.
rewrite H4 in |- *.
  assert (inv_hmap m1).
 unfold m1 in |- *.
   apply inv_hmap_Merge0.
   tauto.
  tauto.
  tauto.
  tauto.
rewrite H4 in H5.
  assert (ModcAMerge0.Prec_Tr m x y).
 unfold ModcAMerge0.Prec_Tr in |- *.
    tauto.
assert (~ MAMerge0Tr.MfM.expo m x y).
  tauto.
generalize (MAMerge0Tr.degree_Tr_merge_summary m x y z H H6 H0 H1 H2 H5 H7).
  assert (MAMerge0Tr.MfM.degree = degreee).
 unfold degreee in |- *.
    tauto.
assert (MA0Tr.MfM.degree = degreee).
  tauto.
rewrite H8 in |- *.
  rewrite H9 in |- *.
  rewrite <- H4 in |- *.
  fold dx in |- *; fold dy in |- *.
  elim (MAMerge0Tr.MfM.expo_dec m x z H).
 elim (expe_dec m x z H).
   tauto.
  tauto.
elim (MAMerge0Tr.MfM.expo_dec m y z H).
 elim (expe_dec m x z H).
   tauto.
 elim (expe_dec m y z H).
   tauto.
  tauto.
elim (expe_dec m y z H).
  tauto.
elim (expe_dec m x z H).
  tauto.
 tauto.
Qed.

(* OK: *)

Lemma Iter_cA0_Merge1_ter:
 forall(m:fmap)(x x' z:dart)(i:nat),
   inv_hmap m -> exd m x -> exd m x' ->
     Iter (cA (Merge m one x x') zero) i z =
        Iter (cA m zero) i z. 
Proof.
intros.
assert (zero = dim_opp one).
 simpl in |- *;  tauto.
rewrite H2 in |- *.
  induction i.
 simpl in |- *.
    tauto.
set (t := cA (Merge m one x x') (dim_opp one)) in |- *.
  unfold Iter; fold Iter.
  unfold t in |- *.
  rewrite cA_Merge in |- *.
  elim (eq_dim_dec one (dim_opp one)). intro. 
simpl in a. inversion a. 
 rewrite IHi in |- *.
   simpl in |- *.
    tauto.
 tauto.
Qed.

(* OK: *)

Lemma Iter_cA1_Merge0_ter:
 forall(m:fmap)(x x' z:dart)(i:nat),
   inv_hmap m -> exd m x -> exd m x' ->
     Iter (cA (Merge m zero x x') one) i z =
        Iter (cA m one) i z. 
Proof.
intros.
assert (one = dim_opp zero).
 simpl in |- *;  tauto.
rewrite H2 in |- *.
  induction i.
 simpl in |- *.
    tauto.
set (t := cA (Merge m zero x x') (dim_opp zero)) 
   in |- *.
unfold Iter; fold Iter.
  unfold t in |- *.
  rewrite cA_Merge in |- *.
 elim (eq_dim_dec zero (dim_opp zero)). intro. 
simpl in a. inversion a. 
 rewrite IHi in |- *.
   simpl in |- *.
    tauto.
 tauto.
Qed.

(* OK: *)

Open Scope nat_scope.

Lemma degreev_Merge0_summary_aux: 
  forall (m : fmap) (x y z : dart)(n:nat),
   inv_hmap m -> exd m x -> exd m y -> exd m z -> 
 n <= ndN m ->
  MA1Tr.MfM.degree_aux 
    (Merge m zero x y) z (ndN m - n) =
        MA1Tr.MfM.degree_aux m z (ndN m - n).
Proof.
intros.
induction n.
 assert (ndN m - 0 = ndN m).
   lia.
 rewrite H4 in |- *.
   rewrite MA1Tr.MfM.degree_aux_equation in |- *.
   rewrite 
(MA1Tr.MfM.degree_aux_equation m z (ndN m)) in |- *.
   rewrite ndN_Merge in |- *.
   rewrite <- Iter_cA1_MAMerge1Tr_f in |- *.
   rewrite Iter_cA1_Merge0_ter in |- *.
  elim (Arith.Compare_dec.le_lt_dec (ndN m) (ndN m)).
   elim (Nat.eq_dec (ndN m) (ndN m)).
    elim (eq_dart_dec z (Iter (cA m one) (ndN m) z)).
     elim 
  (eq_dart_dec z (Iter (MA1Tr.MfM.f m) (ndN m) z)).
       tauto.
     rewrite Iter_cA1_MAMerge1Tr_f in |- *.
        tauto.
    elim
 (eq_dart_dec z (Iter (MA1Tr.MfM.f m) (ndN m) z)).
     rewrite Iter_cA1_MAMerge1Tr_f in |- *.
        tauto.
     tauto.
    tauto.
   tauto.
  tauto.
  tauto.
  tauto.
rewrite MA1Tr.MfM.degree_aux_equation in |- *.
  rewrite
 (MA1Tr.MfM.degree_aux_equation m z (ndN m - S n))
  in |- *.
  rewrite ndN_Merge in |- *.
  assert (ndN m - S n + 1 = ndN m - n).
  lia.
rewrite H4 in |- *.
  rewrite <- Iter_cA1_MAMerge1Tr_f in |- *.
  rewrite Iter_cA1_Merge0_ter in |- *.
 elim (Arith.Compare_dec.le_lt_dec (ndN m - S n) (ndN m)).
  elim (Nat.eq_dec (ndN m - S n) (ndN m)).
   rewrite <- Iter_cA1_MAMerge1Tr_f in |- *.
      tauto.
  rewrite <- Iter_cA1_MAMerge1Tr_f in |- *.
    rewrite IHn in |- *.
    tauto.
   lia.
  tauto.
 tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Theorem degreev_Merge0_summary: 
 forall (m : fmap) (x y z: dart),
   inv_hmap m -> exd m x -> exd m y -> exd m z ->
     degreev (Merge m zero x y) z = degreev m z.
Proof.
intros.
unfold degreev in |- *.
unfold MA1Tr.MfM.degree in |- *.
assert (0 < ndN m).
 apply MA0.MfcA.ndN_pos with z.
    tauto.
assert (1 = ndN m - (ndN m - 1)).
  lia.
rewrite H4 in |- *.
  apply 
 (degreev_Merge0_summary_aux m x y z (ndN m - 1)).
  tauto.
 tauto.
tauto.
 tauto.
lia.
Qed.

(* OK: *)

Theorem expv_Merge0: forall (m : fmap)(x y z t:dart),
   inv_hmap m -> exd m x -> exd m y ->
     (expv (Merge m zero x y) z t <-> expv m z t).
Proof.
intros.
rename H0 into Ex.
rename H1 into Ey.
unfold expv in |- *.
unfold MA1.MfcA.expo in |- *.
assert (exd m z <-> exd (Merge m zero x y) z).
 generalize (exd_Merge m zero x y z).
    tauto.
cut
 ((exists i : nat,
  Iter (MA1.MfcA.f (Merge m zero x y)) i z = t) <->
  (exists i : nat, Iter (MA1.MfcA.f m) i z = t)).
  tauto.
split.
 intro.
   elim H1.
   clear H1.
   intros i Hi.
   split with i.
   rewrite <- Iter_cA1_MAMerge1Tr_f in Hi.
   rewrite Iter_cA1_Merge0_ter in Hi.
  rewrite <- Iter_cA1_MAMerge1Tr_f in |- *.
     tauto.
  tauto.
  tauto.
  tauto.
intro.
  elim H1.
  clear H1.
  intros i Hi.
  split with i.
  rewrite <- Iter_cA1_MAMerge1Tr_f in |- *.
  rewrite Iter_cA1_Merge0_ter in |- *.
 rewrite <- Iter_cA1_MAMerge1Tr_f in Hi.
    tauto.
 tauto.
 tauto.
 tauto.
Qed.

Open Scope nat_scope.

(* OK: *)

Theorem degreee_Merge0_merge:
 forall (m:fmap)(x y:dart)(H:inv_hmap m),
   exd m x -> exd m y ->
    ~ expe m x y -> 
     let m1 := Merge m zero x y in
      degreee m1 y = degreee m y + degreee m x.
Proof.
intros.
assert (ModcAMerge0.Prec_Tr m x y).
 unfold ModcAMerge0.Prec_Tr in |- *.
    tauto.
unfold m1 in |- *.
  assert (degreee = MAMerge0Tr.MfM.degree).
  tauto.
assert (m1 = ModcAMerge0.Tr m x y).
 unfold m1 in |- *.
    tauto.
unfold m1 in H5.
  rewrite H5 in |- *.
  apply MAMerge0Tr.degree_Tr_merge_y.
  tauto.
 tauto.
 tauto.
 tauto.
 tauto.
Qed.

(*==================================================
         DIMENSION 1: expv_G1, degreev_G1
                          (MERGE ONLY)
===================================================*)

(* OK: *)

Theorem expv_Merge1_CNS:
 forall (m:fmap)(x y z t:dart)(H:inv_hmap m),
   exd m x -> exd m y -> exd m z -> 
    ~ expv m x y -> 
     let m1 := Merge m one x y in
      (expv m1 z t <->
         expv m z t \/
         expv m x z /\ expv m y t \/
         expv m x t /\ expv m y z).
Proof.
intros.
assert (inv_hmap m1).
 unfold m1 in |- *.
   apply (inv_hmap_Merge1 m x y H H0 H1 H3).
assert (ModcAMerge1.Prec_Tr m x y).
 unfold ModcAMerge1.Prec_Tr in |- *.
    tauto.
generalize (MAMerge1Tr.expo_Tr_CNS m x y z t H H5 H0 H1 H2 H4).
  elim (MAMerge1Tr.MfM.expo_dec m x y H).
  tauto.
 tauto.
Qed.

(* OK: *)

Theorem degreev_Merge1_merge:
 forall (m:fmap)(x y:dart)(H:inv_hmap m),
   exd m x -> exd m y ->
    ~ expv m x y -> 
     let m1 := Merge m one x y in
      degreev m1 y = degreev m y + degreev m x.
Proof.
intros.
assert (ModcAMerge1.Prec_Tr m x y).
 unfold ModcAMerge1.Prec_Tr in |- *.
    tauto.
unfold m1 in |- *.
  assert (degreev = MAMerge1Tr.MfM.degree).
  tauto.
assert (m1 = ModcAMerge1.Tr m x y).
 unfold m1 in |- *.
    tauto.
unfold m1 in H5.
  rewrite H5 in |- *.
  apply MAMerge1Tr.degree_Tr_merge_y.
  tauto.
 tauto.
 tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Theorem degreev_Merge1_summary:
  forall (m:fmap)(x y z:dart)(H:inv_hmap m),
    exd m x -> exd m y -> exd m z ->
       let m1 := Merge m one x y in
       let dx := degreev m x in
       let dy := degreev m y in
   ~ expv m x y ->
      degreev m1 z =
        if expv_dec m x z H
        then (dx + dy)%nat
        else if expv_dec m y z H
             then (dx + dy)%nat
             else degreev m z.
Proof.
intros.
unfold degreev in |- *.
assert (m1 = ModcAMerge1.Tr m x y).
 unfold m1 in |- *.
    tauto.
rewrite H4 in |- *.
  assert (inv_hmap m1).
 unfold m1 in |- *.
   apply inv_hmap_Merge1.
   tauto.
  tauto.
  tauto.
  tauto.
rewrite H4 in H5.
  assert (ModcAMerge1.Prec_Tr m x y).
 unfold ModcAMerge1.Prec_Tr in |- *.
    tauto.
assert (~ MAMerge1Tr.MfM.expo m x y).
  tauto.
generalize (MAMerge1Tr.degree_Tr_merge_summary m x y z H H6 H0 H1 H2 H5 H7).
  assert (MAMerge1Tr.MfM.degree = degreev).
 unfold degreev in |- *.
    tauto.
assert (MA1Tr.MfM.degree = degreev).
  tauto.
rewrite H8 in |- *.
  rewrite H9 in |- *.
  rewrite <- H4 in |- *.
  fold dx in |- *; fold dy in |- *.
  elim (MAMerge1Tr.MfM.expo_dec m x z H).
 elim (expv_dec m x z H).
   tauto.
  tauto.
elim (MAMerge1Tr.MfM.expo_dec m y z H).
 elim (expv_dec m x z H).
   tauto.
 elim (expv_dec m y z H).
   tauto.
  tauto.
elim (expv_dec m y z H).
  tauto.
elim (expv_dec m x z H).
  tauto.
 tauto.
Qed.

Open Scope nat_scope.

(* OK: *)

Lemma degreee_Merge1_summary_aux: 
  forall (m : fmap) (x y z : dart)(n:nat),
   inv_hmap m -> exd m x -> exd m y -> exd m z -> 
 n <= ndN m ->
  MA0Tr.MfM.degree_aux 
    (Merge m one x y) z (ndN m - n) =
        MA0Tr.MfM.degree_aux m z (ndN m - n).
Proof.
intros.
induction n.
 assert (ndN m - 0 = ndN m).
   lia.
 rewrite H4 in |- *.
   rewrite MA0Tr.MfM.degree_aux_equation in |- *.
   rewrite 
(MA0Tr.MfM.degree_aux_equation m z (ndN m)) in |- *.
   rewrite ndN_Merge in |- *.
   rewrite <- Iter_cA0_MAMerge0Tr_f in |- *.
   rewrite Iter_cA0_Merge1_ter in |- *.
  elim (Arith.Compare_dec.le_lt_dec (ndN m) (ndN m)).
   elim (Nat.eq_dec (ndN m) (ndN m)).
    elim (eq_dart_dec z (Iter (cA m zero) (ndN m) z)).
     elim 
  (eq_dart_dec z (Iter (MA0Tr.MfM.f m) (ndN m) z)).
       tauto.
     rewrite Iter_cA0_MAMerge0Tr_f in |- *.
        tauto.
    elim
 (eq_dart_dec z (Iter (MA0Tr.MfM.f m) (ndN m) z)).
     rewrite Iter_cA0_MAMerge0Tr_f in |- *.
        tauto.
     tauto.
    tauto.
   tauto.
  tauto.
  tauto.
  tauto.
rewrite MA0Tr.MfM.degree_aux_equation in |- *.
  rewrite
 (MA0Tr.MfM.degree_aux_equation m z (ndN m - S n))
  in |- *.
  rewrite ndN_Merge in |- *.
  assert (ndN m - S n + 1 = ndN m - n).
  lia.
rewrite H4 in |- *.
  rewrite <- Iter_cA0_MAMerge0Tr_f in |- *.
  rewrite Iter_cA0_Merge1_ter in |- *.
 elim (Arith.Compare_dec.le_lt_dec (ndN m - S n) (ndN m)).
  elim (Nat.eq_dec (ndN m - S n) (ndN m)).
   rewrite <- Iter_cA0_MAMerge0Tr_f in |- *.
      tauto.
  rewrite <- Iter_cA0_MAMerge0Tr_f in |- *.
    rewrite IHn in |- *.
    tauto.
   lia.
  tauto.
 tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Theorem degreee_Merge1_summary: 
 forall (m : fmap) (x y z: dart),
   inv_hmap m -> exd m x -> exd m y -> exd m z ->
     degreee (Merge m one x y) z = degreee m z.
Proof.
intros.
unfold degreee in |- *.
unfold MA0Tr.MfM.degree in |- *.
assert (0 < ndN m).
 apply MA1.MfcA.ndN_pos with z.
    tauto.
assert (1 = ndN m - (ndN m - 1)).
  lia.
rewrite H4 in |- *.
  apply 
 (degreee_Merge1_summary_aux m x y z (ndN m - 1)).
  tauto.
 tauto.
tauto.
 tauto.
lia.
Qed.

(* OK: *)

Theorem expe_Merge1: forall (m : fmap)(x y z t:dart),
   inv_hmap m -> exd m x -> exd m y ->
     (expe (Merge m one x y) z t <-> expe m z t).
Proof.
intros.
rename H0 into Ex.
rename H1 into Ey.
unfold expe in |- *.
unfold MA0.MfcA.expo in |- *.
assert (exd m z <-> exd (Merge m one x y) z).
 generalize (exd_Merge m one x y z).
    tauto.
cut
 ((exists i : nat,
  Iter (MA0.MfcA.f (Merge m one x y)) i z = t) <->
  (exists i : nat, Iter (MA0.MfcA.f m) i z = t)).
  tauto.
split.
 intro.
   elim H1.
   clear H1.
   intros i Hi.
   split with i.
   rewrite <- Iter_cA0_MAMerge0Tr_f in Hi.
   rewrite Iter_cA0_Merge1_ter in Hi.
  rewrite <- Iter_cA0_MAMerge0Tr_f in |- *.
     tauto.
  tauto.
  tauto.
  tauto.
intro.
  elim H1.
  clear H1.
  intros i Hi.
  split with i.
  rewrite <- Iter_cA0_MAMerge0Tr_f in |- *.
  rewrite Iter_cA0_Merge1_ter in |- *.
 rewrite <- Iter_cA0_MAMerge0Tr_f in Hi.
    tauto.
 tauto.
 tauto.
 tauto.
Qed.

(* =================================================
                 FACES / Merge0, Merge1
===================================================*)

(* OK: *)

Lemma cF_Merge0 : forall(m:fmap)(x y z:dart), 
 inv_hmap m -> exd m x -> exd m y ->
  cF (Merge m zero x y) z = 
    if eq_dart_dec y z then cA_1 m one x
    else if eq_dart_dec (cA m zero x) z 
         then cF m y else cF m z.
Proof.
intros.
unfold Merge in |- *.
elim (pred_dec m zero y).
 set (m0 := Shift m zero (cA_1 m zero y)) in |- *.
   intro.
   assert (A_1 m zero y = cA_1 m zero y).
  rewrite cA_1_eq in |- *.
   elim (pred_dec m zero y);  tauto.
   tauto.
 assert (exd m (cA_1 m zero y)).
  generalize (exd_cA_1 m zero y).
     tauto.
 assert (succ m zero (cA_1 m zero y)).
  unfold succ in |- *.
    apply exd_not_nil with m.
    tauto.
  rewrite <- H2 in |- *.
    rewrite A_A_1 in |- *.
    tauto.
   tauto.
   tauto.
 assert (inv_hmap m0).
  unfold m0 in |- *.
    apply inv_hmap_Shift.
    tauto.
   tauto.
 rewrite cF_G0 in |- *.
  unfold m0 in |- *.
    assert (one = dim_opp zero).
   simpl in |- *.
      tauto.
  rewrite cA_Shift in |- *.
   rewrite H6 in |- *.
     rewrite cA_1_Shift_ter in |- *.
    rewrite cF_Shift in |- *.
     rewrite cF_Shift in |- *.
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
rewrite cF_G0 in |- *.
  tauto.
 tauto.
Qed.

(* OK: *)

Lemma cF_1_Merge0 : forall(m:fmap)(x y z:dart), 
 inv_hmap m -> exd m x -> exd m y -> exd m z ->
  cF_1 (Merge m zero x y) z = 
    if eq_dart_dec (cA_1 m one x) z then y
    else if eq_dart_dec (cF m y) z 
         then (cA m zero x) else cF_1 m z.
Proof.
intros.
unfold Merge in |- *.
elim (pred_dec m zero y).
 set (m0 := Shift m zero (cA_1 m zero y)) in |- *.
   intro.
   assert (A_1 m zero y = cA_1 m zero y).
  rewrite cA_1_eq in |- *.
   elim (pred_dec m zero y);  tauto.
   tauto.
 assert (exd m (cA_1 m zero y)).
  generalize (exd_cA_1 m zero y).
     tauto.
 assert (succ m zero (cA_1 m zero y)).
  unfold succ in |- *.
    apply exd_not_nil with m.
    tauto.
  rewrite <- H3 in |- *.
    rewrite A_A_1 in |- *.
    tauto.
   tauto.
   tauto.
 assert (inv_hmap m0).
  unfold m0 in |- *.
    apply inv_hmap_Shift.
    tauto.
   tauto.
 rewrite cF_1_G0 in |- *.
  unfold m0 in |- *.
    assert (one = dim_opp zero).
   simpl in |- *.
      tauto.
  rewrite H7 in |- *.
    rewrite cA_1_Shift_ter in |- *.
   rewrite cA_Shift in |- *.
    rewrite cF_Shift in |- *.
     rewrite cF_1_Shift in |- *.
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
 generalize (exd_Shift m zero (cA_1 m zero y) x).
    tauto.
 generalize (exd_Shift m zero (cA_1 m zero y) y).
   fold m0 in |- *.
    tauto.
 generalize (exd_Shift m zero (cA_1 m zero y) z).
   fold m0 in |- *.
    tauto.
intro.
  rewrite cF_1_G0 in |- *.
  tauto.
 tauto.
 tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma cF_Merge1 : forall(m:fmap)(x y z:dart), 
 inv_hmap m -> exd m x -> exd m y -> exd m z ->
  cF (Merge m one x y) z = 
    if eq_dart_dec (cA m zero y) z then x
    else
     if eq_dart_dec (cF_1 m x) z
     then cA_1 m one y
     else cF m z.
Proof.
intros.
unfold Merge in |- *.
elim (pred_dec m one y).
 set (m0 := Shift m one (cA_1 m one y)) in |- *.
   intro.
   assert (A_1 m one y = cA_1 m one y).
  rewrite cA_1_eq in |- *.
   elim (pred_dec m one y);  tauto.
   tauto.
 assert (exd m (cA_1 m one y)).
  generalize (exd_cA_1 m one y).
     tauto.
 assert (succ m one (cA_1 m one y)).
  unfold succ in |- *.
    apply exd_not_nil with m.
    tauto.
  rewrite <- H3 in |- *.
    rewrite A_A_1 in |- *.
    tauto.
   tauto.
   tauto.
 assert (inv_hmap m0).
  unfold m0 in |- *.
    apply inv_hmap_Shift.
    tauto.
   tauto.
 rewrite cF_G1 in |- *.
  unfold m0 in |- *.
    assert (zero = dim_opp one).
   simpl in |- *.
      tauto.
  rewrite H7 in |- *.
    rewrite cA_Shift_ter in |- *.
   rewrite cA_1_Shift in |- *.
    rewrite cF_1_Shift in |- *.
     rewrite cF_Shift in |- *.
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
 generalize (exd_Shift m one (cA_1 m one y) x).
    tauto.
 generalize (exd_Shift m one (cA_1 m one y) y).
   fold m0 in |- *.
    tauto.
 generalize (exd_Shift m one (cA_1 m one y) z).
   fold m0 in |- *.
    tauto.
rewrite cF_G1 in |- *.
  tauto.
 tauto.
 tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma cF_1_Merge1 : forall(m:fmap)(x y z:dart), 
 inv_hmap m -> exd m x -> exd m y -> exd m z ->
  cF_1 (Merge m one x y) z = 
    if eq_dart_dec x z then cA m zero y
    else if eq_dart_dec (cA_1 m one y) z
         then cF_1 m x
         else cF_1 m z.
Proof.
intros.
unfold Merge in |- *.
elim (pred_dec m one y).
 set (m0 := Shift m one (cA_1 m one y)) in |- *.
   intro.
   assert (A_1 m one y = cA_1 m one y).
  rewrite cA_1_eq in |- *.
   elim (pred_dec m one y);  tauto.
   tauto.
 assert (exd m (cA_1 m one y)).
  generalize (exd_cA_1 m one y).
     tauto.
 assert (succ m one (cA_1 m one y)).
  unfold succ in |- *.
    apply exd_not_nil with m.
    tauto.
  rewrite <- H3 in |- *.
    rewrite A_A_1 in |- *.
    tauto.
   tauto.
   tauto.
 assert (inv_hmap m0).
  unfold m0 in |- *.
    apply inv_hmap_Shift.
    tauto.
   tauto.
 rewrite cF_1_G1 in |- *.
  unfold m0 in |- *.
    assert (zero = dim_opp one).
   simpl in |- *.
      tauto.
  rewrite H7 in |- *.
    rewrite cA_Shift_ter in |- *.
   rewrite cA_1_Shift in |- *.
    rewrite cF_1_Shift in |- *.
     rewrite cF_1_Shift in |- *.
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
 generalize (exd_Shift m one (cA_1 m one y) x).
    tauto.
 generalize (exd_Shift m one (cA_1 m one y) y).
   fold m0 in |- *.
    tauto.
 generalize (exd_Shift m one (cA_1 m one y) z).
   fold m0 in |- *.
    tauto.
rewrite cF_1_G1 in |- *.
  tauto.
 tauto.
 tauto.
 tauto.
 tauto.
Qed.

(*=====================================================
     INSTANTIATIONS OF MTr FOR Tr = G0, G1, 
             WRT cF, cF_1 : expof_Merge0, expof_Merge1
                degreef_Merge0, degreef_Merge1
 ====================================================*)

(* DIM 0: OK *)

Lemma cF_Merge0_y1_x: forall(m:fmap)(x y z:dart),
 True ->
  inv_hmap m -> exd m x -> exd m y -> exd m z ->
  cF (Merge m zero (cA m one y) x) z =
    if eq_dart_dec x z then y
    else if eq_dart_dec (cF_1 m y) z then cF m x
         else cF m z.
Proof.
intros.
rewrite cF_Merge0 in |- *.
 rewrite cA_1_cA in |- *.
  fold (cF_1 m y) in |- *.
     tauto.
  tauto.
  tauto.
 tauto.
generalize (exd_cA m one y).
   tauto.
 tauto.
Qed.

(* OK: *)

Lemma cF_1_Merge0_y1_x: forall(m:fmap)(x y z:dart),
 True ->
 inv_hmap m -> exd m x -> exd m y -> exd m z ->
  cF_1 (Merge m zero (cA m one y) x) z =
    if eq_dart_dec y z then x
    else if eq_dart_dec (cF m x) z then cF_1 m y 
         else cF_1 m z.
Proof.
intros.
rename H2 into Ez.
rewrite cF_1_Merge0 in |- *.
 rewrite cA_1_cA in |- *.
  fold (cF_1 m y) in |- *.
     tauto.
  tauto.
  tauto.
 tauto.
generalize (exd_cA m one y).
   tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma exd_Merge0_y1_x: forall (m : fmap)(x y z : dart),
  inv_hmap m -> 
    (exd m z <-> exd (Merge m zero (cA m one y) x) z).
Proof. 
intros.
generalize (exd_Merge m zero (cA m one y) x z).
 tauto.
Qed.

(* OK: *)

Lemma ndN_Merge0_y1_x: forall (m : fmap)(x y:dart),
  ndN (Merge m zero (cA m one y) x) = ndN m.
Proof.
intros.
rewrite ndN_Merge in |- *.
 tauto.
Qed.

Module ModcFMerge0<:SigTr 
 with Definition Tr:= 
   fun(m:fmap)(x y:dart) => Merge m zero (cA m one y) x
 with Definition Prec_Tr:= 
  fun(m:fmap)(x y:dart) => True.
Module M:=McF.
Definition Tr(m:fmap)(x y:dart):= 
  Merge m zero (cA m one y) x.
Definition Prec_Tr(m:fmap)(x y:dart):= True.
Definition f_Tr := cF_Merge0_y1_x.
Definition f_1_Tr := cF_1_Merge0_y1_x.
Definition exd_Tr := exd_Merge0_y1_x.
Definition ndN_Tr := ndN_Merge0_y1_x.
End ModcFMerge0.

(* OK: *)

Module MFMerge0Tr := MTr ModcFMerge0.

(* DIM 1: *)

Lemma cF_Merge1_y_x_0: forall(m:fmap)(x y z:dart),
 True ->
  inv_hmap m -> exd m x -> exd m y -> exd m z ->
  cF (Merge m one y (cA_1 m zero x)) z =
    if eq_dart_dec x z then y
    else if eq_dart_dec (cF_1 m y) z then cF m x 
         else cF m z.
Proof.
intros.
rewrite cF_Merge1 in |- *.
 rewrite cA_cA_1 in |- *.
  fold (cF m x) in |- *.
     tauto.
  tauto.
  tauto.
 tauto.
 tauto.
generalize (exd_cA_1 m zero x).
   tauto.
 tauto.
Qed.

Lemma cF_1_Merge1_y_x_0: forall(m:fmap)(x y z:dart),
 True ->
 inv_hmap m -> exd m x -> exd m y -> exd m z ->
   cF_1 (Merge m one y (cA_1 m zero x)) z =
    if eq_dart_dec y z then x
    else if eq_dart_dec (cF m x) z then cF_1 m y 
         else cF_1 m z.
Proof.
intros.
rewrite cF_1_Merge1 in |- *.
 fold (cF m x) in |- *.
   rewrite cA_cA_1 in |- *.
   tauto.
  tauto.
  tauto.
 tauto.
 tauto.
generalize (exd_cA_1 m zero x).
   tauto.
 tauto.
Qed.

Lemma exd_Merge1_y_x_0: 
forall (m : fmap)(x y z : dart),
  inv_hmap m -> 
 (exd m z <-> exd (Merge m one y (cA_1 m zero x)) z).
Proof.
intros.
generalize (exd_Merge m one y (cA_1 m zero x) z).
 tauto.
Qed.

(* OK: *)

Lemma ndN_Merge1_y_x_0: forall (m : fmap)(x y:dart),
  ndN (Merge m one y (cA_1 m zero x)) = ndN m.
Proof. intros. rewrite ndN_Merge. tauto. Qed.

(* INSTANTIATION: *)

Module ModcFMerge1<:SigTr 
 with Definition Tr:= 
  fun(m:fmap)(x y:dart) => 
     Merge m one y (cA_1 m zero x)
 with Definition Prec_Tr:= 
  fun(m:fmap)(x y:dart) => True.
Module M:=McF.
Definition Tr(m:fmap)(x y:dart):=
  Merge m one y (cA_1 m zero x).
Definition Prec_Tr(m:fmap)(x y:dart):= True.
Definition f_Tr := cF_Merge1_y_x_0.
Definition f_1_Tr := cF_1_Merge1_y_x_0.
Definition exd_Tr := exd_Merge1_y_x_0.
Definition ndN_Tr:=ndN_Merge1_y_x_0.
End ModcFMerge1.

(* OK: *)

Module MFMerge1Tr := MTr ModcFMerge1.

(*=====================================================
           CORRESPONDENCES BETWEEN MODULES
=====================================================*)

(* DIMENSION 0: *)

(* OK: *)

Lemma ModcFMerge0_Tr_Merge: forall(m:fmap)(x y:dart),
 inv_hmap m -> exd m x -> 
   ModcFMerge0.Tr m y (cA_1 m one x) = 
        Merge m zero x y.
Proof.
intros.
unfold ModcFMerge0.Tr in |- *.
rewrite cA_cA_1 in |- *.
  tauto.
 tauto.
 tauto.
Qed.

Lemma MFMerge0Tr_expo_expof:
  MFMerge0Tr.MfM.expo = expof.
Proof. tauto. Qed.

(* OK: *)

Lemma cF_Merge0_ModcFMerge0:
 forall(m:fmap)(x y z:dart),
  inv_hmap m -> exd m x -> 
    cF (Merge m zero x y) z = 
MFMerge0Tr.MfM.f (ModcFMerge0.Tr m y (cA_1 m one x)) z.
Proof.
intros.
assert (MFMerge0Tr.MfM.f = cF).
  tauto.
rewrite H1 in |- *.
  rewrite ModcFMerge0_Tr_Merge in |- *.
  tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma exd_ModcFMerge0: forall(m : fmap)(x y z : dart),
 inv_hmap m -> exd m x -> 
  (exd (ModcFMerge0.Tr m y (cA_1 m one x)) z <-> 
     exd (Merge m zero x y) z).
Proof. 
intros.
rewrite ModcFMerge0_Tr_Merge in |- *.
  tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma cA_ModcFMerge0: forall(m:fmap)(x y:dart)(z:dart),
  inv_hmap m -> exd m x ->
    cA (ModcFMerge0.Tr m y (cA_1 m one x)) zero z = 
        cA (Merge m zero x y) zero z.
Proof.
intros.
rewrite ModcFMerge0_Tr_Merge in |- *.
  tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma Iter_ModcFMerge0_Tr: 
forall(m:fmap)(x y z:dart)(i:nat),
 inv_hmap m -> exd m x -> 
  Iter (cF (Merge m zero x y)) i z = 
   Iter (ModcFMerge0.M.f 
    (ModcFMerge0.Tr m y (cA_1 m one x))) i z.
Proof.
intros.
rewrite ModcFMerge0_Tr_Merge in |- *.
  tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma expo_ModcFMerge0_Tr: 
 forall(m:fmap)(x y z t:dart),
  inv_hmap m -> exd m x -> 
   (MFMerge0Tr.MfM.expo 
    (ModcFMerge0.Tr m y (cA_1 m one x)) z t
     <-> expof (Merge m zero x y) z t).
Proof.
intros.
assert (MFMerge0Tr.MfM.expo = expof).
  tauto.
rewrite H1 in |- *.
  rewrite ModcFMerge0_Tr_Merge in |- *.
  tauto.
 tauto.
 tauto.
Qed.

(* DIM 1: *)

(* OK: *)

Lemma ModcFMerge1_Tr_Merge: forall(m:fmap)(x y:dart),
 inv_hmap m -> exd m y -> 
   ModcFMerge1.Tr m (cA m zero y) x = Merge m one x y.
Proof.
intros.
unfold ModcFMerge1.Tr in |- *.
rewrite cA_1_cA in |- *.
  tauto.
 tauto.
 tauto.
Qed.

Lemma MFMerge1Tr_expo_expof:
  MFMerge1Tr.MfM.expo = expof.
Proof. tauto. Qed.

(* OK: *)

Lemma cF_Merge1_ModcFMerge1: forall(m:fmap)(x y z:dart),
  inv_hmap m -> exd m y -> 
    cF (Merge m one x y) z = 
 MFMerge1Tr.MfM.f (ModcFMerge1.Tr m (cA m zero y) x) z.
Proof.
intros.
assert (MFMerge1Tr.MfM.f = cF).
  tauto.
rewrite H1 in |- *.
  rewrite ModcFMerge1_Tr_Merge in |- *.
  tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma exd_ModcFMerge1: forall(m : fmap)(x y z : dart),
 inv_hmap m -> exd m y -> 
  (exd (ModcFMerge1.Tr m (cA m zero y) x) z <-> 
     exd (Merge m one x y) z).
Proof. 
intros.
rewrite ModcFMerge1_Tr_Merge in |- *.
  tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma cA_ModcFMerge1: forall(m:fmap)(x y:dart)(z:dart),
  inv_hmap m -> exd m y ->
    cA (ModcFMerge1.Tr m (cA m zero y) x) one z = 
        cA (Merge m one x y) one z.
Proof.
intros.
rewrite ModcFMerge1_Tr_Merge in |- *.
  tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma Iter_ModcFMerge1_Tr: 
forall(m:fmap)(x y z:dart)(i:nat),
 inv_hmap m -> exd m y -> 
  Iter (cF (Merge m one x y)) i z = 
   Iter (ModcFMerge1.M.f 
    (ModcFMerge1.Tr m (cA m zero y) x)) i z.
Proof.
intros.
rewrite ModcFMerge1_Tr_Merge in |- *.
  tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma expo_ModcFMerge1_Tr:
 forall(m:fmap)(x y z t:dart),
  inv_hmap m -> exd m y -> 
   (MFMerge1Tr.MfM.expo 
    (ModcFMerge1.Tr m (cA m zero y) x) z t
     <-> expof (Merge m one x y) z t).
Proof.
intros.
assert (MFMerge1Tr.MfM.expo = expof).
  tauto.
rewrite H1 in |- *.
  rewrite ModcFMerge1_Tr_Merge in |- *.
  tauto.
 tauto.
 tauto.
Qed.

(*=====================================================
   INSTANTIATIONS "IN CLEAR" : expof_Merge0, 
    expof_Merge1, degreef_Merge0, degreef_Merge1

 ====================================================*)

(*===================================================
                     DIM 0:
====================================================*)

(* OK: *)

Lemma MFMerge0Tr_expo_dec_expof_dec: 
 forall(m:fmap)(x y:dart)(H:inv_hmap m)(A B:Prop),
  (if MFMerge0Tr.MfM.expo_dec m x y H then A else B)
<->
  (if expof_dec m x y H then A else B).
Proof. 
intros.
elim (MFMerge0Tr.MfM.expo_dec m x y H).
 elim (expof_dec m x y H).
   tauto.
  tauto.
elim (expof_dec m x y H).
  tauto.
 tauto.
Qed.

Lemma MFMerge0Tr_between_betweenf: 
  MFMerge0Tr.MfM.between = betweenf.
Proof. tauto. Qed.

Lemma MFMerge0Tr_Prec_Tr_True: 
forall(m:fmap)(x y:dart),
  ModcFMerge0.Prec_Tr m x y = True.
Proof. tauto. Qed.

(* OK: *)

Theorem expof_Merge0_y0_x_CNS: 
  forall (m : fmap) (x y z t : dart) (H : inv_hmap m),
   exd m x -> exd m y -> 
    ~ expe m (cA m one y) x -> exd m z ->
    let m1 := Merge m zero (cA m one y) x in
       let x1 := cF m x in
       let y_1 := cF_1 m y in
       (expof m1 z t <->
        (if expof_dec m x y H
         then
          betweenf m y z x /\ betweenf m y t x \/
          betweenf m x1 z y_1 /\ betweenf m x1 t y_1 \/
          ~ expof m x z /\ expof m z t
         else
          expof m z t \/
          expof m x z /\ expof m y t \/
          expof m x t /\ expof m y z)).
Proof.
intros.
assert (y_1 = MFMerge0Tr.MfM.f_1 m y).
  tauto.
assert (m1 = ModcFMerge0.Tr m x y).
  tauto.
rewrite <- MFMerge0Tr_between_betweenf in |- *.
  set
   (A0 :=
    MFMerge0Tr.MfM.between m y z x /\
     MFMerge0Tr.MfM.between m y t x \/
    MFMerge0Tr.MfM.between m x1 z y_1 /\
     MFMerge0Tr.MfM.between m x1 t y_1 \/
    ~ expof m x z /\ expof m z t) in |- *.
  set
   (B0 :=
    expof m z t \/ expof m x z /\ expof m y t \/ 
        expof m x t /\ expof m y z)
   in |- *.
  cut (expof m1 z t <-> 
 (if MFMerge0Tr.MfM.expo_dec m x y H then A0 else B0)).
 generalize 
 (MFMerge0Tr_expo_dec_expof_dec m x y H A0 B0).
    tauto.
unfold A0 in |- *.
  unfold B0 in |- *.
  rewrite <- MFMerge0Tr_expo_expof in |- *.
  assert (x1 = MFMerge0Tr.MfM.f m x).
  tauto.
rewrite H4 in |- *.
  rewrite H5 in |- *.
  rewrite H6 in |- *.
  apply MFMerge0Tr.expo_Tr_CNS.
 unfold ModcFMerge0.Prec_Tr in |- *.
    tauto.
 tauto.
 tauto.
 tauto.
rewrite <- H5 in |- *.
  unfold m1 in |- *.
  apply inv_hmap_Merge0.
  tauto.
generalize (exd_cA m one y).
   tauto.
 tauto.
 tauto.
Qed.

(*
X = cA m one y  ; Y = x;
x = Y             y = cA_1 m one X = X_1   
y_1 := cF_1 m (cA_1 m one X) = cA m zero X = X0
x1  := cF m x = cF m Y = Y_0_1
*)

(* USUAL FORM: *)

Theorem expof_Merge0_CNS: 
  forall(m : fmap)(X Y z t : dart)(H : inv_hmap m),
   exd m X -> exd m Y -> 
    ~ expe m X Y -> exd m z ->
       let m1 := Merge m zero X Y in
       let Y_0_1 := cF m Y in
       let X0 := cA m zero X in
       let X_1:= cA_1 m one X in
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
Proof.
intros.
set (x := Y) in |- *.
set (y := X_1) in |- *.
set (x1 := Y_0_1) in |- *.
set (y_1 := X0) in |- *.
unfold m1 in |- *.
assert (X = cA m one y).
 unfold y in |- *.
   unfold X_1 in |- *.
   rewrite cA_cA_1 in |- *.
   tauto.
  tauto.
  tauto.
rewrite H4 in |- *.
  fold x in |- *.
  rewrite H4 in H2.
  fold x in H2.
  fold x in H0.
  assert (exd m y).
 unfold y in |- *.
   unfold X_1 in |- *.
   generalize (exd_cA_1 m one X).
    tauto.
fold x in H1.
  assert (x1 = cF m x).
 unfold x1 in |- *.
   unfold x in |- *.
   fold Y_0_1 in |- *.
    tauto.
assert (y_1 = cF_1 m y).
 unfold y_1 in |- *.
   unfold y in |- *.
   unfold X_1 in |- *.
   unfold cF_1 in |- *.
   rewrite cA_cA_1 in |- *.
  fold X0 in |- *.
     tauto.
  tauto.
  tauto.
rewrite H6 in |- *.
  rewrite H7 in |- *.
  apply expof_Merge0_y0_x_CNS.
  tauto.
 tauto.
 tauto.
 tauto.
Qed.

Lemma degreef_Merge0_Merge1:
  MFMerge0Tr.MfM.degree = MFMerge1Tr.MfM.degree.
Proof. tauto. Qed.

(* FACE DEGREES / G0, MERGE : *) 

Open Scope nat_scope.

(* OK: *)

Theorem degreef_Merge0_merge_summary:
 forall (m : fmap) (X Y Z : dart)(H:inv_hmap m),
    exd m X -> exd m Y -> 
    ~ expe m X Y -> exd m Z ->
       let m1 := Merge m zero X Y in
       let X_1:= cA_1 m one X in
       let dY := degreef m Y in
       let dX_1 := degreef m X_1 in
    ~ expof m Y X_1 ->
     degreef m1 Z =
       (if expof_dec m Y Z H
        then dY + dX_1
        else
         if expof_dec m X_1 Z H then dY + dX_1 
         else degreef m Z).
Proof.
intros.
assert (inv_hmap m1).
 unfold m1 in |- *.
   apply inv_hmap_Merge0.
   tauto.
  tauto.
  tauto.
  tauto.
assert (m1 = ModcFMerge0.Tr m Y X_1).
 unfold ModcFMerge0.Tr in |- *.
   unfold X_1 in |- *.
   rewrite cA_cA_1 in |- *.
  fold m1 in |- *.
     tauto.
  tauto.
  tauto.
assert (ModcFMerge0.Prec_Tr m Y X_1).
 unfold ModcFMerge0.Prec_Tr in |- *.
    tauto.
assert (exd m X_1).
 unfold X_1 in |- *.
   generalize (exd_cA_1 m one X).
    tauto.
assert (~ MFMerge0Tr.MfM.expo m Y X_1).
  tauto.
assert (degreef = MFMerge0Tr.MfM.degree).
  tauto.
rewrite H10 in |- *.
  rewrite H6 in H5.
  generalize
   (MFMerge0Tr.degree_Tr_merge_summary 
       m Y X_1 Z H H7 H1 H8 H3 H5 H9).
  rewrite <- H10 in |- *.
  rewrite <- H6 in |- *.
  fold dY in |- *.
  fold dX_1 in |- *.
  elim (MFMerge0Tr.MfM.expo_dec m Y Z H).
 elim (expof_dec m Y Z H).
   tauto.
  tauto.
elim (expof_dec m Y Z H).
  tauto.
elim (MFMerge0Tr.MfM.expo_dec m X_1 Z H).
 elim (expof_dec m X_1 Z H).
   tauto.
  tauto.
elim (expof_dec m X_1 Z H).
  tauto.
 tauto.
Qed.

(* OK: *)

Theorem degreef_Merge0_split_summary:
 forall (m : fmap) (X Y Z : dart) (j : nat) 
        (H : inv_hmap m), 
  exd m X -> exd m Y ->  
    ~ expe m X Y -> exd m Z ->
       let m1 := Merge m zero X Y in
       let X_1:= cA_1 m one X in
       let dY := degreef m Y in
       let dX_1 := degreef m X_1 in
       let Y1 := cF m Y in
       X_1 = Iter (cF m) j Y ->
       2 <= j <= dX_1 ->
    degreef m Z =
       (if expof_dec m X_1 Z H
        then degreef m1 X_1 + degreef m1 Y1
        else degreef m1 Z).
Proof.
intros.
assert (inv_hmap m1).
 unfold m1 in |- *.
   apply inv_hmap_Merge0.
   tauto.
  tauto.
  tauto.
  tauto.
assert (ModcFMerge0.Prec_Tr m Y X_1).
 unfold ModcFMerge0.Prec_Tr in |- *.
    tauto.
assert (exd m X_1).
 unfold X_1 in |- *.
   generalize (exd_cA_1 m one X).
    tauto.
assert (degreef = MFMerge0Tr.MfM.degree).
  tauto.
assert (cF = MFMerge0Tr.MfM.f).
  tauto.
rewrite H10 in H4.
  assert (m1 = ModcFMerge0.Tr m Y X_1).
 unfold m1 in |- *.
   unfold X_1 in |- *.
   unfold ModcFMerge0.Tr in |- *.
   rewrite cA_cA_1 in |- *.
   tauto.
  tauto.
  tauto.
rewrite H11 in |- *.
  rewrite H11 in H6.
  generalize
   (MFMerge0Tr.degree_Tr_split_summary 
       m Y X_1 Z j H H7 H1 H8 H3 H4 H5 H6).
  rewrite <- H11 in |- *.
  rewrite <- H9 in |- *.
  rewrite <- H10 in |- *.
  fold Y1 in |- *.
  elim (MFMerge0Tr.MfM.expo_dec m X_1 Z H).
 elim (expof_dec m X_1 Z H).
   tauto.
  tauto.
elim (expof_dec m X_1 Z H).
  tauto.
 tauto.
Qed.

(* + VERSION bis : *)

Theorem degreef_Merge0_split_summary_bis:
 forall (m : fmap) (X Y Z : dart) (j : nat) 
        (H : inv_hmap m), 
  exd m X -> exd m Y ->  
    ~ expe m X Y -> exd m Z ->
       let m1 := Merge m zero X Y in
       let X_1:= cA_1 m one X in
       let dY := degreef m Y in
       let dX_1 := degreef m X_1 in
       let Y1 := cF m Y in
       let X0 := cA m zero X in
       X_1 = Iter (cF m) j Y ->
       2 <= j <= dX_1 ->
       (betweenf m X_1 Z Y ->
           degreef m1 Z = dX_1 - j + 1) /\
       (betweenf m Y1 Z X0 ->
           degreef m1 Z = j - 1) /\
       (~ expof m Y Z ->
           degreef m1 Z = degreef m Z).
Proof.
intros.
assert (inv_hmap m1).
 unfold m1 in |- *.
   apply inv_hmap_Merge0.
   tauto.
  tauto.
  tauto.
  tauto.
assert (ModcFMerge0.Prec_Tr m Y X_1).
 unfold ModcFMerge0.Prec_Tr in |- *.
    tauto.
assert (exd m X_1).
 unfold X_1 in |- *.
   generalize (exd_cA_1 m one X).
    tauto.
assert (degreef = MFMerge0Tr.MfM.degree).
  tauto.
assert (cF = MFMerge0Tr.MfM.f).
  tauto.
rewrite H10 in H4.
  assert (m1 = ModcFMerge0.Tr m Y X_1).
 unfold m1 in |- *.
   unfold X_1 in |- *.
   unfold ModcFMerge0.Tr in |- *.
   rewrite cA_cA_1 in |- *.
   tauto.
  tauto.
  tauto.
rewrite H11 in |- *.
  rewrite H11 in H6.
  assert (betweenf = MFMerge0Tr.MfM.between).
  tauto.
assert (expof = MFMerge0Tr.MfM.expo).
  tauto.
rewrite H12 in |- *; rewrite H13 in |- *.
  generalize
   (MFMerge0Tr.degree_Tr_split_summary_bis
  m Y X_1 Z j H H7 H1 H8 H3 H4 H5 H6).
  rewrite <- H11 in |- *.
  rewrite <- H9 in |- *.
  rewrite <- H10 in |- *.
  rewrite <- H12 in |- *.
  rewrite <- H13 in |- *.
  fold Y1 in |- *.
  assert (MFMerge0Tr.MfM.f_1 m X_1 = X0).
 unfold X_1 in |- *.
   assert (cF_1 = MFMerge0Tr.MfM.f_1).
   tauto.
 rewrite <- H14 in |- *.
   unfold cF_1 in |- *.
   rewrite cA_cA_1 in |- *.
  fold X0 in |- *.
     tauto.
  tauto.
  tauto.
rewrite H14 in |- *.
   tauto.
Qed.

(*===================================================
                     DIM 1:
====================================================*)

(* OK: *)

Lemma MFMerge1Tr_expo_dec_expof_dec: 
 forall(m:fmap)(x y:dart)(H:inv_hmap m)(A B:Prop),
  (if MFMerge1Tr.MfM.expo_dec m x y H then A else B)
<->
  (if expof_dec m x y H then A else B).
Proof. 
intros.
elim (MFMerge1Tr.MfM.expo_dec m x y H).
 elim (expof_dec m x y H).
   tauto.
  tauto.
elim (expof_dec m x y H).
  tauto.
 tauto.
Qed.

Lemma MFMerge1Tr_between_betweenf: 
  MFMerge1Tr.MfM.between = betweenf.
Proof. tauto. Qed.

Lemma MFMerge1Tr_Prec_Tr_True: 
forall(m:fmap)(x y:dart),
  ModcFMerge1.Prec_Tr m x y = True.
Proof. tauto. Qed.

(*
X = y ; Y = cA_1 m zero x
x = cA m zero Y ; y = X
x1 = cF m (cA m zero Y) = cA_1 m one Y = Y_1
y_1 = cF_1 X
*)

(* OK: *)

Theorem expof_Merge1_y_x_0_CNS: 
  forall (m : fmap) (x y z t : dart) (H : inv_hmap m),
  exd m x -> exd m y -> 
    ~ expv m y (cA_1 m zero x) -> exd m z ->
       let m1 := Merge m one y (cA_1 m zero x) in 
       let x1 := cF m x in
       let y_1 := cF_1 m y in
       (expof m1 z t <->
        (if expof_dec m x y H
         then
          betweenf m y z x /\ betweenf m y t x \/
          betweenf m x1 z y_1 /\ betweenf m x1 t y_1 \/
          ~ expof m x z /\ expof m z t
         else
          expof m z t \/
          expof m x z /\ expof m y t \/
          expof m x t /\ expof m y z)).
Proof.
intros.
assert (y_1 = MFMerge1Tr.MfM.f_1 m y).
  tauto.
assert (m1 = ModcFMerge1.Tr m x y).
  tauto.
rewrite <- MFMerge1Tr_between_betweenf in |- *.
  set
   (A0 :=
    MFMerge1Tr.MfM.between m y z x /\ 
        MFMerge1Tr.MfM.between m y t x \/
    MFMerge1Tr.MfM.between m x1 z y_1 /\
        MFMerge1Tr.MfM.between m x1 t y_1 \/
    ~ expof m x z /\ expof m z t) in |- *.
  set
   (B0 :=
    expof m z t \/ expof m x z /\ expof m y t \/ 
     expof m x t /\ expof m y z)
   in |- *.
  cut (expof m1 z t <->
(if MFMerge1Tr.MfM.expo_dec m x y H then A0 else B0)).
 generalize 
  (MFMerge1Tr_expo_dec_expof_dec m x y H A0 B0).
    tauto.
unfold A0 in |- *.
  rewrite <- MFMerge1Tr_expo_expof in |- *.
  unfold B0 in |- *.
  rewrite <- MFMerge1Tr_expo_expof in |- *.
  assert (x1 = MFMerge1Tr.MfM.f m x).
  tauto.
rewrite H4 in |- *.
  rewrite H5 in |- *.
  rewrite H6 in |- *.
  apply MFMerge1Tr.expo_Tr_CNS.
 unfold ModcFMerge1.Prec_Tr in |- *.
    tauto.
 tauto.
 tauto.
 tauto.
rewrite <- H5 in |- *.
  unfold m1 in |- *.
  apply inv_hmap_Merge1.
  tauto.
 tauto.
generalize (exd_cA_1 m zero x).
   tauto.
 tauto.
Qed.

(* USUAL FORM: OK *)

Theorem expof_Merge1_CNS: 
  forall (m : fmap) (X Y z t : dart) (H : inv_hmap m),
  exd m X -> exd m Y -> 
    ~ expv m X Y -> exd m z ->
       let m1 := Merge m one X Y in 
       let Y_1 := cA_1 m one Y in
       let X10 := cF_1 m X in
       let Y0 := cA m zero Y in
       (expof m1 z t <->
     (if expof_dec m Y0 X H
      then
       betweenf m X z Y0 /\ betweenf m X t Y0 \/
       betweenf m Y_1 z X10 /\ betweenf m Y_1 t X10 \/
       ~ expof m Y0 z /\ expof m z t
      else
       expof m z t \/
       expof m Y0 z /\ expof m X t \/
       expof m Y0 t /\ expof m X z)).
Proof.
intros.
set (x := Y0) in |- *.
set (x1 := Y_1) in |- *.
set (y_1 := X10) in |- *.
set (y := X) in |- *.
unfold m1 in |- *.
fold y in |- *.
assert (Y = cA_1 m zero x).
 unfold x in |- *.
   unfold Y0 in |- *.
   rewrite cA_1_cA in |- *.
   tauto.
  tauto.
  tauto.
rewrite H4 in |- *.
  fold y in H2.
  rewrite H4 in H2.
  rewrite H4 in H1.
  assert (x1 = cF m x).
 unfold x in |- *.
   unfold x1 in |- *.
   unfold Y0 in |- *.
   unfold cF in |- *.
   rewrite cA_1_cA in |- *.
  fold Y_1 in |- *.
     tauto.
  tauto.
 rewrite H4 in |- *.
    tauto.
assert (y_1 = cF_1 m y).
 unfold y in |- *.
   unfold y_1 in |- *.
   unfold X10 in |- *.
    tauto.
rewrite H5 in |- *.
  rewrite H6 in |- *.
  apply expof_Merge1_y_x_0_CNS.
 generalize (exd_cA_1 m zero x).
    tauto.
unfold y in |- *.
   tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Theorem degreef_Merge1_merge_summary:
 forall (m : fmap) (X Y Z : dart)(H:inv_hmap m),
   exd m X -> exd m Y -> 
    ~ expv m X Y -> exd m Z ->
       let m1 := Merge m one X Y in 
       let Y0 := cA m zero Y in 
       let dY0 := degreef m Y0 in
       let dX := degreef m X in
    ~ expof m Y0 X ->
      degreef m1 Z =
        if expof_dec m Y0 Z H
        then dY0 + dX
        else
          if expof_dec m X Z H then dY0 + dX 
          else degreef m Z.
Proof.
intros.
assert (inv_hmap m1).
 unfold m1 in |- *.
   apply inv_hmap_Merge1.
   tauto.
  tauto.
  tauto.
  tauto.
assert (m1 = ModcFMerge1.Tr m Y0 X).
 unfold ModcFMerge1.Tr in |- *.
   unfold Y0 in |- *.
   rewrite cA_1_cA in |- *.
  fold m1 in |- *.
     tauto.
  tauto.
  tauto.
assert (ModcFMerge1.Prec_Tr m Y0 X).
 unfold ModcFMerge1.Prec_Tr in |- *.
    tauto.
assert (exd m Y0).
 unfold Y0 in |- *.
   generalize (exd_cA m zero Y).
    tauto.
assert (~ MFMerge1Tr.MfM.expo m Y0 X).
  tauto.
assert (degreef = MFMerge1Tr.MfM.degree).
  tauto.
rewrite H10 in |- *.
  rewrite H6 in H5.
  generalize 
 (MFMerge1Tr.degree_Tr_merge_summary 
      m Y0 X Z H H7 H8 H0 H3 H5 H9).
  rewrite <- H10 in |- *.
  rewrite <- H6 in |- *.
  fold dX in |- *.
  fold dY0 in |- *.
  elim (MFMerge1Tr.MfM.expo_dec m Y0 Z H).
 elim (expof_dec m Y0 Z H).
   tauto.
  tauto.
elim (expof_dec m Y0 Z H).
  tauto.
elim (MFMerge1Tr.MfM.expo_dec m X Z H).
 elim (expof_dec m X Z H).
   tauto.
  tauto.
elim (expof_dec m X Z H).
  tauto.
 tauto.
Qed.

(* OK: *)

Theorem degreef_Merge1_split_summary:
 forall (m : fmap) (X Y Z : dart) (j : nat) 
        (H : inv_hmap m), 
   exd m X -> exd m Y ->
    ~ expv m X Y -> exd m Z ->
       let m1 := Merge m one X Y in 
       let Y0 := cA m zero Y in 
       let Y01 := cF m Y0 in
       let dX := degreef m X in
       X = Iter (cF m) j Y0 ->
       2 <= j <= dX ->
    degreef m Z =
        if expof_dec m X Z H
        then degreef m1 X + degreef m1 Y01
        else degreef m1 Z.
Proof.
intros.
assert (inv_hmap m1).
 unfold m1 in |- *.
   apply inv_hmap_Merge1.
   tauto.
  tauto.
  tauto.
  tauto.
assert (ModcFMerge1.Prec_Tr m Y0 X).
 unfold ModcFMerge1.Prec_Tr in |- *.
    tauto.
assert (exd m Y0).
 unfold Y0 in |- *.
   generalize (exd_cA m zero Y).
    tauto.
assert (degreef = MFMerge1Tr.MfM.degree).
  tauto.
assert (cF = MFMerge1Tr.MfM.f).
  tauto.
rewrite H10 in H4.
  assert (m1 = ModcFMerge1.Tr m Y0 X).
 unfold m1 in |- *.
   unfold Y0 in |- *.
   unfold ModcFMerge1.Tr in |- *.
   rewrite cA_1_cA in |- *.
   tauto.
  tauto.
  tauto.
rewrite H11 in |- *.
  rewrite H11 in H6.
  generalize
   (MFMerge1Tr.degree_Tr_split_summary 
     m Y0 X Z j H H7 H8 H0 H3 H4 H5 H6).
  rewrite <- H11 in |- *.
  rewrite <- H9 in |- *.
  rewrite <- H10 in |- *.
  fold Y01 in |- *.
  elim (MFMerge1Tr.MfM.expo_dec m X Z H).
 elim (expof_dec m X Z H).
   tauto.
  tauto.
elim (expof_dec m X Z H).
  tauto.
 tauto.
Qed.

(* + VERSION bis: OK *)

Theorem degreef_Merge1_split_summary_bis:
 forall (m : fmap) (X Y Z : dart) (j : nat) 
        (H : inv_hmap m), 
   exd m X -> exd m Y ->
    ~ expv m X Y -> exd m Z ->
       let m1 := Merge m one X Y in 
       let Y0 := cA m zero Y in 
       let X10 := cF_1 m X in
       let Y_1 := cA_1 m one Y in 
       let dX := degreef m X in
       X = Iter (cF m) j Y0 ->
       2 <= j <= dX ->
       (betweenf m X Z Y0 ->
           degreef m1 Z = dX - j + 1) /\
       (betweenf m Y_1 Z X10 ->
           degreef m1 Z = j - 1) /\
       (~ expof m Y0 Z ->
           degreef m1 Z = degreef m Z).
Proof.
intros.
assert (inv_hmap m1).
 unfold m1 in |- *.
   apply inv_hmap_Merge1.
   tauto.
  tauto.
  tauto.
  tauto.
assert (ModcFMerge1.Prec_Tr m Y0 X).
 unfold ModcFMerge1.Prec_Tr in |- *.
    tauto.
assert (exd m Y0).
 unfold Y0 in |- *.
   generalize (exd_cA m zero Y).
    tauto.
assert (degreef = MFMerge1Tr.MfM.degree).
  tauto.
assert (cF = MFMerge1Tr.MfM.f).
  tauto.
rewrite H10 in H4.
  assert (m1 = ModcFMerge1.Tr m Y0 X).
 unfold m1 in |- *.
   unfold Y0 in |- *.
   unfold ModcFMerge1.Tr in |- *.
   rewrite cA_1_cA in |- *.
   tauto.
  tauto.
  tauto.
rewrite H11 in |- *.
  rewrite H11 in H6.
  assert (betweenf = MFMerge1Tr.MfM.between).
  tauto.
assert (expof = MFMerge1Tr.MfM.expo).
  tauto.
rewrite H12 in |- *.
  rewrite H13 in |- *.
  generalize
   (MFMerge1Tr.degree_Tr_split_summary_bis 
    m Y0 X Z j H H7 H8 H0 H3 H4 H5 H6).
  rewrite <- H11 in |- *.
  rewrite <- H9 in |- *.
  rewrite <- H10 in |- *.
  rewrite <- H12 in |- *.
  rewrite <- H13 in |- *.
  assert (cF m Y0 = Y_1).
 unfold cF in |- *.
   unfold Y0 in |- *.
   rewrite cA_1_cA in |- *.
  fold Y_1 in |- *.
     tauto.
  tauto.
  tauto.
assert (MFMerge1Tr.MfM.f_1 m X = X10).
 unfold X10 in |- *.
    tauto.
rewrite H14 in |- *; rewrite H15 in |- *.
   tauto.
Qed.

(*===================================================
              nf_Merge0, nf_Merge1
===================================================*)

Open Scope Z_scope.

(* OK: *)

Theorem nf_Merge0:
 forall (m : fmap) (x y: dart) (H : inv_hmap m),
  exd m x -> exd m y ->  
   let x_1 := cA_1 m one x in
     nf (Merge m zero x y) = 
      nf m + if (expf_dec m x_1 y) then 1 else -1.
Proof.
intros.
unfold Merge in |- *.
elim (pred_dec m zero y).
 intro.
   set (m0 := Shift m zero (cA_1 m zero y)) in |- *.
   assert (A_1 m zero y = cA_1 m zero y).
  rewrite cA_1_eq in |- *.
   elim (pred_dec m zero y);  tauto.
   tauto.
 assert (exd m (cA_1 m zero y)).
  generalize (exd_cA_1 m zero y).
     tauto.
 assert (succ m zero (cA_1 m zero y)).
  unfold succ in |- *.
    apply exd_not_nil with m.
    tauto.
  rewrite <- H2 in |- *.
    rewrite A_A_1 in |- *.
    tauto.
   tauto.
   tauto.
 assert (inv_hmap m0).
  unfold m0 in |- *.
    apply inv_hmap_Shift.
    tauto.
   tauto.
 assert (nf m0 = nf m).
  unfold m0 in |- *.
    rewrite nf_Shift in |- *.
    tauto.
   tauto.
   tauto.
 rewrite nf_G0 in |- *.
  rewrite H6 in |- *.
    unfold m0 in |- *.
    assert (one = dim_opp zero).
   simpl in |- *.
      tauto.
  rewrite H7 in |- *.
    rewrite cA_1_Shift_ter in |- *.
   fold m0 in |- *.
     simpl in |- *.
     fold x_1 in |- *.
     generalize 
  (expf_Shift m zero (cA_1 m zero y) x_1 y H H4).
     fold m0 in |- *.
     intro.
     elim (expf_dec m0 x_1 y).
    elim (expf_dec m x_1 y).
      tauto.
     tauto.
   elim (expf_dec m x_1 y).
     tauto.
    tauto.
   tauto.
   tauto.
  tauto.
intro.
  unfold x_1 in |- *.
  apply nf_G0.
   tauto.
Qed.

(* OK: *)

Theorem nf_Merge1:
 forall (m : fmap) (x y: dart) (H : inv_hmap m), 
  exd m x -> exd m y ->  
   let y0 := cA m zero y in
     nf (Merge m one x y) = 
      nf m + if (expf_dec m x y0) then 1 else -1.
Proof.
intros.
unfold Merge in |- *.
elim (pred_dec m one y).
 intro.
   set (m0 := Shift m one (cA_1 m one y)) in |- *.
   assert (A_1 m one y = cA_1 m one y).
  rewrite cA_1_eq in |- *.
   elim (pred_dec m one y);  tauto.
   tauto.
 assert (exd m (cA_1 m one y)).
  generalize (exd_cA_1 m one y).
     tauto.
 assert (succ m one (cA_1 m one y)).
  unfold succ in |- *.
    apply exd_not_nil with m.
    tauto.
  rewrite <- H2 in |- *.
    rewrite A_A_1 in |- *.
    tauto.
   tauto.
   tauto.
 assert (inv_hmap m0).
  unfold m0 in |- *.
    apply inv_hmap_Shift.
    tauto.
   tauto.
 assert (nf m0 = nf m).
  unfold m0 in |- *.
    rewrite nf_Shift in |- *.
    tauto.
   tauto.
   tauto.
 rewrite nf_G1 in |- *.
  rewrite H6 in |- *.
    unfold m0 in |- *.
    assert (zero = dim_opp one).
   simpl in |- *.
      tauto.
  rewrite H7 in |- *.
    rewrite cA_Shift_ter in |- *.
   fold m0 in |- *.
     simpl in |- *.
     fold y0 in |- *.
     generalize 
 (expf_Shift m one (cA_1 m one y) x y0 H H4).
     fold m0 in |- *.
     intro.
     elim (expf_dec m0 x y0).
    elim (expf_dec m x y0).
      tauto.
     tauto.
   elim (expf_dec m x y0).
     tauto.
    tauto.
   tauto.
   tauto.
  tauto.
intro.
  rewrite nf_G1 in |- *.
 fold y0 in |- *.
    tauto.
 tauto.
Qed.

(* OK: *)

Lemma eqc_Merge: 
 forall (m : fmap)(k:dim)(x y z t: dart),
  inv_hmap m -> exd m x -> exd m y ->
   (eqc (Merge m k x y) z t <->
    (eqc m z t \/ 
        eqc m z x /\ eqc m y t \/ 
            eqc m z y /\ eqc m x t)).
Proof.
intros.
unfold Merge in |- *.
set (m0 := Shift m k (cA_1 m k y)) in |- *.
elim (pred_dec m k y).
 intro.
   assert (A_1 m k y = cA_1 m k y).
  rewrite cA_1_eq in |- *.
   elim (pred_dec m k y);  tauto.
   tauto.
 assert (exd m (cA_1 m k y)).
  generalize (exd_cA_1 m k y).
     tauto.
 assert (succ m k (cA_1 m k y)).
  unfold succ in |- *.
    apply exd_not_nil with m.
    tauto.
  rewrite <- H2 in |- *.
    rewrite A_A_1 in |- *.
    tauto.
   tauto.
   tauto.
 assert (inv_hmap m0).
  unfold m0 in |- *.
    apply inv_hmap_Shift.
    tauto.
   tauto.
 generalize (eqc_G m0 k x y z t H5).
   intro.
   generalize (eqc_Shift m k (cA_1 m k y) z t H H4).
   generalize (eqc_Shift m k (cA_1 m k y) z x H H4).
   generalize (eqc_Shift m k (cA_1 m k y) y t H H4).
   generalize (eqc_Shift m k (cA_1 m k y) z y H H4).
   generalize (eqc_Shift m k (cA_1 m k y) x t H H4).
   fold m0 in |- *.
    tauto.
intro.
  apply eqc_G.
   tauto.
Qed.

(* OK: *)

Lemma nd_Merge: forall (m : fmap)(k:dim)(x y: dart),
   nd (Merge m k x y) = nd m.
Proof.
intros.
unfold Merge in |- *.
elim (pred_dec m k y).
 rewrite nd_G in |- *.
   intro.
   unfold Shift in |- *.
   simpl in |- *.
   rewrite nd_B in |- *.
    tauto.
rewrite nd_G in |- *.
   tauto.
Qed.

(* OK!: *)

Theorem planarity_crit_Merge0: 
 forall (m:fmap)(x y:dart), 
  inv_hmap m -> exd m x -> exd m y -> 
   ~ expe m x y -> 
      (planar (Merge m zero x y) <->
  (planar m /\ 
      (~ eqc m x y \/ expf m (cA_1 m one x) y))).
Proof.
intros.
unfold Merge in |- *.
elim (pred_dec m zero y).
 intro.
   set (m0 := Shift m zero (cA_1 m zero y)) in |- *.
   assert (exd m0 x).
  unfold m0 in |- *.
    generalize (exd_Shift m zero (cA_1 m zero y) x).
     tauto.
 assert (exd m0 y).
  generalize (exd_Shift m zero (cA_1 m zero y) y).
     tauto.
 set (y_1 := cA_1 m zero y) in |- *.
   assert (y_1 = A_1 m zero y).
  unfold y_1 in |- *.
    rewrite cA_1_eq in |- *.
   elim (pred_dec m zero y).
     tauto.
    tauto.
   tauto.
 assert (succ m zero y_1).
  rewrite H5 in |- *.
    unfold succ in |- *.
    rewrite A_A_1 in |- *.
   apply exd_not_nil with m.
     tauto.
    tauto.
   tauto.
   tauto.
 assert (~ pred m0 zero y).
  unfold m0 in |- *.
    unfold pred in |- *.
    rewrite A_1_Shift in |- *.
   fold y_1 in |- *.
     rewrite H5 in |- *.
     rewrite A_A_1 in |- *.
    elim (eq_dart_dec y y).
      tauto.
     tauto.
    tauto.
    tauto.
   tauto.
  fold y_1 in |- *.
     tauto.
 assert (~ expe m0 x y).
  generalize (expe_Shift m (cA_1 m zero y) x y H H6).
    fold m0 in |- *.
     tauto.
 assert (inv_hmap m0).
  unfold m0 in |- *; apply inv_hmap_Shift.
    tauto.
  fold y_1 in |- *.
     tauto.
 generalize (planarity_crit_G0 m0 x y H9 H3 H4 H7 H8).
   intros.
   generalize 
 (planarity_crit_Shift0 m (cA_1 m zero y) H H6).
   fold m0 in |- *.
   intro.
   generalize
 (eqc_Shift m zero (cA_1 m zero y) x y H H6).
   fold m0 in |- *; intro.
   assert (cA_1 m0 one x = cA_1 m one x).
  unfold m0 in |- *.
    assert (one = dim_opp zero).
   simpl in |- *.
      tauto.
  rewrite H13 in |- *.
    rewrite cA_1_Shift_ter in |- *.
    tauto.
   tauto.
  fold y_1 in |- *.
     tauto.
 rewrite H13 in H10.
   assert 
(expf m0 (cA_1 m one x) y <-> expf m (cA_1 m one x) y).
  generalize 
 (expf_Shift m zero (cA_1 m zero y) 
   (cA_1 m one x) y H H6).
    fold m0 in |- *.
     tauto.
  tauto.
intro.
  apply planarity_crit_G0.
  tauto.
 tauto.
 tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Theorem planarity_crit_Merge1: 
 forall (m : fmap) (x y : dart),
   inv_hmap m -> exd m x -> exd m y ->
     ~ expv m x y ->
   (planar (Merge m one x y) <->
  planar m /\ (~ eqc m x y \/ expf m x (cA m zero y))).
Proof.
intros.
unfold Merge in |- *.
elim (pred_dec m one y).
 intro.
   set (m0 := Shift m one (cA_1 m one y)) in |- *.
   assert (exd m0 x).
  unfold m0 in |- *.
    generalize (exd_Shift m one (cA_1 m one y) x).
     tauto.
 assert (exd m0 y).
  generalize (exd_Shift m one (cA_1 m one y) y).
     tauto.
 set (y_1 := cA_1 m one y) in |- *.
   assert (y_1 = A_1 m one y).
  unfold y_1 in |- *.
    rewrite cA_1_eq in |- *.
   elim (pred_dec m one y).
     tauto.
    tauto.
   tauto.
 assert (succ m one y_1).
  rewrite H5 in |- *.
    unfold succ in |- *.
    rewrite A_A_1 in |- *.
   apply exd_not_nil with m.
     tauto.
    tauto.
   tauto.
   tauto.
 assert (~ pred m0 one y).
  unfold m0 in |- *.
    unfold pred in |- *.
    rewrite A_1_Shift in |- *.
   fold y_1 in |- *.
     rewrite H5 in |- *.
     rewrite A_A_1 in |- *.
    elim (eq_dart_dec y y).
      tauto.
     tauto.
    tauto.
    tauto.
   tauto.
  fold y_1 in |- *.
     tauto.
 assert (~ expv m0 x y).
  generalize (expv_Shift m (cA_1 m one y) x y H H6).
    fold m0 in |- *.
     tauto.
 assert (inv_hmap m0).
  unfold m0 in |- *; apply inv_hmap_Shift.
    tauto.
  fold y_1 in |- *.
     tauto.
 generalize 
(planarity_crit_G1 m0 x y H9 H3 H4 H7 H8).
   intros.
   generalize 
(planarity_crit_Shift1 m (cA_1 m one y) H H6).
   fold m0 in |- *.
   intro.
   generalize 
(eqc_Shift m one (cA_1 m one y) x y H H6).
   fold m0 in |- *; intro.
   assert (cA m0 zero y = cA m zero y).
  unfold m0 in |- *.
    assert (zero = dim_opp one).
   simpl in |- *.
      tauto.
  rewrite H13 in |- *.
    rewrite cA_Shift_ter in |- *.
    tauto.
   tauto.
  fold y_1 in |- *.
     tauto.
 rewrite H13 in H10.
   assert 
(expf m0 x (cA m zero y) <-> expf m x (cA m zero y)).
  generalize 
(expf_Shift m one (cA_1 m one y) x (cA m zero y) H H6).
    fold m0 in |- *.
     tauto.
  tauto.
intro.
  apply planarity_crit_G1.
  tauto.
 tauto.
 tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma nc_G:  forall(m : fmap)(k:dim) (x y : dart),
  inv_hmap m -> exd m x -> exd m y -> 
   nc (G m k x y) = 
      nc m + if (eqc_dec m x y) then 0 else -1.
Proof.
  intros. unfold G. 
   elim (succ_dec m k x). intro. 
    simpl. rewrite nc_B. 
     set (m0:= B m k x). 
    generalize (eqc_Shift m k x x y H a). intro. 
    generalize (eqc_B_bottom m k x H H0).  
     generalize (eqc_B_top m k x H a).  
     fold m0. intros.         
   elim (eqc_dec m0 x (A m k x)). 
     elim (eqc_dec m0 (top m k x) (bottom m k x)). 
         elim (eqc_dec (Shift m k x) x y). 
              elim (eqc_dec m x y). intros. 
                 clear H3 H4 H2 a0 a1 a2 a3. lia.
                 tauto. 
             elim (eqc_dec m x y). tauto. intros. 
                clear H3 H4 H2 a1 a0. lia.
            intros. 
            elim b. apply eqc_trans with x. 
                apply eqc_trans with (A m k x).
                    apply eqc_symm. tauto. 
                    apply eqc_symm. tauto. tauto. 
      elim (eqc_dec m0 (top m k x) (bottom m k x)).    
           intros. 
                 elim b. 
                   apply eqc_trans with (top m k x). 
                   apply eqc_trans with (bottom m k x). tauto. 
                           apply eqc_symm. tauto. 
                           apply eqc_symm. tauto. 
        intros. 
            elim (eqc_dec (Shift m k x) x y). 
              elim (eqc_dec m x y). intros. 
                    clear H3 H4 H2 a0 a1. lia. 
                        tauto. 
              elim (eqc_dec m x y). tauto. intros. 
                        clear H3 H4 H2. lia. 
                     tauto. tauto. 
   simpl. intro. 
          elim (eqc_dec m x y). intro. clear a. lia. 
                 intro. lia.
Qed.

Lemma nc_Merge:  forall(m : fmap)(k:dim) (x y : dart),
  inv_hmap m -> exd m x -> exd m y ->
   nc (Merge m k x y) = 
      nc m + if (eqc_dec m x y) then 0 else -1.
Proof.
  intros. unfold Merge. 
   elim (pred_dec m k y). intro. 
     assert (succ m k (cA_1 m k y)). 
       unfold succ. 
            rewrite cA_1_eq. 
             elim (pred_dec m k y). intro. 
                 rewrite A_A_1. 
              apply exd_not_nil with m. 
              tauto. tauto. tauto. tauto. tauto. tauto. 
     rewrite nc_G.  
         rewrite nc_Shift. 
       generalize (eqc_Shift m k (cA_1 m k y) x y H H2). intro. 
          elim (eqc_dec (Shift m k (cA_1 m k y)) x y). 
                elim (eqc_dec m x y). intros. 
                     clear H3 a0 a1. lia. tauto. 
                elim (eqc_dec m x y). tauto. intros. tauto. 
                   tauto. tauto. apply inv_hmap_Shift. tauto. tauto. 
                 generalize (exd_Shift m k (cA_1 m k y) x). tauto. 
                 generalize (exd_Shift m k (cA_1 m k y) y). tauto. 
          rewrite nc_G. tauto. tauto. tauto. tauto.
Qed.

(* OK: *)

From Stdlib Require Import ZArith.
Open Scope Z_scope.

Theorem genus_variation_Merge0:
 forall(m:fmap)(x y:dart),
  inv_hmap m -> exd m x -> exd m y -> 
    ~expe m x y ->
      genus (Merge m zero x y) = genus m +
        if eqc_dec m x y 
      then if expf_dec m (cA_1 m one x) y then 0
                else 1
        else 0.
Proof.
  intros. 
      unfold genus. 
        unfold ec. 
         rewrite nc_Merge. 
         rewrite ne_Merge0. rewrite nv_Merge0. rewrite nd_Merge. 
       rewrite nf_Merge0. 
    elim (eqc_dec m x y). 
        elim (expf_dec m (cA_1 m one x) y). intros. 
        assert (nv m + (ne m - 1) + (nf m + 1) - nd m =
              nv m + ne m + nf m - nd m). 
              clear a a0. lia. rewrite H3. lia. 
          intros. 
        assert (nv m + (ne m - 1) + (nf m + -1) - nd m =
           nv m + ne m + nf m - nd m + (-1)*2). lia. 
          rewrite H3. 
     rewrite Z_div_plus. lia. lia. 
           elim (expf_dec m (cA_1 m one x) y). intros. 
          elim b. apply eqc_trans with (cA_1 m one x).
                apply eqc_cA_1_r. tauto. tauto. 
                apply expf_eqc. tauto. 
                 unfold expf in a. tauto. 
             intros. 
           assert (nv m + (ne m - 1) + (nf m + -1) - nd m =
                nv m + ne m + nf m - nd m + (-1)*2). lia. 
                rewrite H3. 
               rewrite Z_div_plus. lia. lia. 
                  tauto. tauto. tauto. tauto. tauto. tauto. 
                       tauto. tauto. tauto. tauto. tauto. tauto. 
Qed.

Theorem genus_variation_Merge1:
 forall(m:fmap)(x y:dart),
  inv_hmap m -> exd m x -> exd m y -> 
    ~expv m x y ->
      genus (Merge m one x y) = genus m +
        if eqc_dec m x y 
        then if expf_dec m x (cA m zero y)
               then 0
              else 1
        else 0.
Proof.
  intros. unfold genus. 
        unfold ec. 
         rewrite nc_Merge. 
         rewrite ne_Merge1. rewrite nv_Merge1. rewrite nd_Merge. 
       rewrite nf_Merge1. 
    elim (eqc_dec m x y). 
        elim (expf_dec m x (cA m zero y)). intros. 
        assert (nv m -1  + ne m + (nf m + 1) - nd m =
              nv m + ne m + nf m - nd m). 
              clear a a0. lia. rewrite H3. lia. 
          intros. 
        assert (nv m - 1 + ne m + (nf m + -1) - nd m =
           nv m + ne m + nf m - nd m + (-1)*2). lia. 
          rewrite H3. 
     rewrite Z_div_plus. lia. lia. 
           elim (expf_dec m x (cA m zero y)). intros. 
          elim b. apply eqc_trans with (cA m zero y). 
                apply expf_eqc. tauto. unfold expf in  a. tauto. 
                apply eqc_symm. apply eqc_cA_r. tauto. tauto.
           assert (nv m - 1 + ne m + (nf m + -1) - nd m =
                nv m + ne m + nf m - nd m + (-1)*2). lia. 
                rewrite H3. 
               rewrite Z_div_plus. intros. lia. lia. 
                  tauto. tauto. tauto. tauto. tauto. tauto. 
                       tauto. tauto. tauto. tauto. tauto. tauto. 
Qed.

(*====================================================
======================================================
                  PART 12:  THE END
======================================================
=====================================================*)


