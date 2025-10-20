(*===================================================

     TOPOLOGICAL FMAPS, HMAPS -
              WITH TAGS AND EMBEDDINGS

         PART 4 : INSTANTIATION OF MTr Tr 
                FOR Tr = L, Shift, Split, B 

      expof_B0, expof_B1

          WITH RESPECT TO cAk, cA0, cA1, cF 
===================================================*)

Require Export Del03.

(*====================================================
 INSTANTIATIONS OF MTr WITH Tr = Lk, L0, L1
            WRT TO  cAk, cA0, cA1 
=====================================================*)

Lemma cAk_Lk0:forall(m:fmap)(k:dim)(x y z:dart), 
  cA (L m k x y) k z =  
   if eq_dart_dec x z then y
   else if eq_dart_dec (cA_1 m k y) z 
        then cA m k x 
        else cA m k z.
Proof.
intros.
simpl in |- *.
elim (eq_dim_dec k k).
  tauto.
 tauto.
Qed.

Lemma cAk_Lk:forall(m:fmap)(k:dim)(x y z:dart), 
 True -> 
  inv_hmap m -> exd m x -> exd m y -> exd m z -> 
  cA (L m k x y) k z =  
   if eq_dart_dec x z then y
   else if eq_dart_dec (cA_1 m k y) z 
        then cA m k x 
        else cA m k z.
Proof. intros. apply cAk_Lk0. Qed.

Lemma cA_k_Lk0:forall(m:fmap)(k:dim)(x y z:dart), 
  cA_1 (L m k x y) k z =  
    if eq_dart_dec y z then x
    else if eq_dart_dec (cA m k x) z then cA_1 m k y 
         else cA_1 m k z.
Proof.
intros.
simpl in |- *.
elim (eq_dim_dec k k).
  tauto.
 tauto.
Qed.

Lemma cA_k_Lk:forall(m:fmap)(k:dim)(x y z:dart), 
 True ->
  inv_hmap m -> exd m x -> exd m y -> exd m z -> 
  cA_1 (L m k x y) k z =  
    if eq_dart_dec y z then x
    else if eq_dart_dec (cA m k x) z then cA_1 m k y 
         else cA_1 m k z.
Proof. intros. apply cA_k_Lk0. Qed.

Lemma exd_L:forall(m:fmap)(k:dim)(x y z:dart), 
  inv_hmap m -> (exd m z <-> exd (L m k x y) z).
Proof.
simpl in |- *.
 tauto.
Qed.

Lemma ndN_L:forall(m:fmap)(k:dim)(x y:dart),
  ndN (L m k x y) = ndN m.
Proof.
intros.
simpl in |- *.
 tauto.
Qed.

(* IMMEDIATE: *)

Module ModcA(Md:Sigd)<:SigTr 
 with Definition Tr:=fun(m:fmap)(x y:dart) => 
    L m Md.kd x y
 with Definition Prec_Tr:=fun(m:fmap)(x y:dart) =>
    True.
Module M := McA Md.    (* : Sigf *)
Definition Tr(m:fmap)(x y:dart):= L m Md.kd x y.
Definition Prec_Tr(m:fmap)(x y:dart):= True.
Definition f_Tr(m:fmap):= cAk_Lk m Md.kd.
Definition f_1_Tr(m:fmap):= cA_k_Lk m Md.kd.
Definition exd_Tr(m:fmap):= exd_L m Md.kd.
Definition ndN_Tr(m:fmap):= ndN_L m Md.kd.

(*===================================================
             PROPERTIES FOR DIM Md.kd
====================================================*)


(* To SEE... *)


(*==================================================*)

End ModcA.

(*===================================================
   INSTANTIATIONS FOR Tr = L0, L1 WRT TO cA0, cA1
====================================================*)

(* IMMEDIATE: *)

Module ModcA0 := ModcA Md0.
Module MA0Tr := MTr ModcA0.

Module ModcA1 := ModcA Md1.
Module MA1Tr := MTr ModcA1.

(*==================================================
         DIMENSION 0: expe_L0, degreee_L0
===================================================*)

(* OK: *)

Lemma MA0Tr_expo_expe: 
  MA0Tr.MfM.expo = expe.
Proof. tauto. Qed.

(* MARCHE, MAIS UN PEU COMPLIQUE: *)

Lemma MA0Tr_expo_dec_expe_dec: 
 forall(m:fmap)(x y:dart)(H:inv_hmap m)(A B:Prop),
  (if MA0Tr.MfM.expo_dec m x y H then A else B) <->
  (if expe_dec m x y H then A else B).
Proof. 
intros.
elim (MA0Tr.MfM.expo_dec m x y H).
 elim (expe_dec m x y H).
   tauto.
  tauto.
elim (expe_dec m x y H).
  tauto.
 tauto.
Qed.

(* OK: *)

Lemma MA0Tr_between_betweene: 
  MA0Tr.MfM.between = betweene.
Proof. tauto. Qed.

(* OK: *)

Lemma ModcA0_Prec_Tr_True: forall(m:fmap)(x y:dart),
  ModcA0.Prec_Tr m x y = True.
Proof. tauto. Qed.

(* FROM WHERE: *)

Theorem expe_L0_CNS:
 forall (m:fmap)(x y z t:dart)(H:inv_hmap m),
     prec_L m zero x y -> exd m z ->
       let x0 := cA m zero x in
       let y_0 := cA_1 m zero y in
       let m1 := L m zero x y in
    (expe m1 z t <->
      (if expe_dec m x y H
       then
        betweene m y z x /\ betweene m y t x \/
        betweene m x0 z y_0 /\ betweene m x0 t y_0 \/
        ~ expe m x z /\ expe m z t
       else
        expe m z t \/
        expe m x z /\ expe m y t \/
        expe m x t /\ expe m y z)).
Proof.
intros.
assert (inv_hmap m1).
 unfold m1 in |- *.
   simpl in |- *.
    tauto.
rewrite <- MA0Tr_expo_expe in |- *.
  rewrite <- MA0Tr_between_betweene in |- *.
  set
   (A0 :=
MA0Tr.MfM.between m y z x /\ 
    MA0Tr.MfM.between m y t x \/ 
 MA0Tr.MfM.between m x0 z y_0 /\ 
    MA0Tr.MfM.between m x0 t y_0 \/
    ~ MA0Tr.MfM.expo m x z /\ MA0Tr.MfM.expo m z t)
   in |- *.
  set
   (B0 :=
    MA0Tr.MfM.expo m z t \/
    MA0Tr.MfM.expo m x z /\ MA0Tr.MfM.expo m y t \/
    MA0Tr.MfM.expo m x t /\ MA0Tr.MfM.expo m y z) 
       in |- *.
  cut
   (MA0Tr.MfM.expo m1 z t <-> 
    (if MA0Tr.MfM.expo_dec m x y H then A0 else B0)).
 generalize (MA0Tr_expo_dec_expe_dec m x y H A0 B0).
    tauto.
unfold A0 in |- *; unfold B0 in |- *.
  unfold m1 in |- *.
  assert (ModcA0.Tr m x y = L m zero x y).
  tauto.
rewrite <- H3 in |- *.
  assert (x0 = MA0Tr.MfM.f m x).
 unfold x0 in |- *.
    tauto.
assert (y_0 = MA0Tr.MfM.f_1 m y).
 unfold y_0 in |- *.
    tauto.
rewrite H4 in |- *.
  rewrite H5 in |- *.
  apply MA0Tr.expo_Tr_CNS.
 rewrite ModcA0_Prec_Tr_True in |- *.
    tauto.
unfold prec_L in H0.
   tauto.
unfold prec_L in H0.
   tauto.
 tauto.
assert (m1 = ModcA0.Tr m x y).
 unfold m1 in |- *.
    tauto.
rewrite <- H6 in |- *.
   tauto.
Qed.

(* DEGREES *)

Open Scope nat_scope.

Definition degreee:=MA0Tr.MfM.degree.

(* OK: *)

Theorem degreee_L0_merge:
  forall (m : fmap) (x y : dart),
    inv_hmap m -> exd m x -> exd m y ->
       let m1 := L m zero x y in
    ~ expe m x y ->
  degreee m1 y = degreee m y + degreee m x.
Proof.
simpl in |- *.
intros.
unfold degreee in |- *.
assert (ModcA0.Tr m x y = L m zero x y).
  tauto.
rewrite <- H3 in |- *.
  apply MA0Tr.degree_Tr_merge_y.
 unfold ModcA0.Prec_Tr in |- *.
    tauto.
 tauto.
 tauto.
 tauto.
unfold expe in H2.
  assert (MA0.MfcA.expo = MA0Tr.MfM.expo).
  tauto.
rewrite <- H4 in |- *.
   tauto.
Qed.

(* OK: *)

Lemma MA0Tr_cA0_Iter: forall(m:fmap)(i:nat)(z:dart),
  Iter (MA0Tr.MfM.f m) i z = Iter (cA m zero) i z.
Proof.
induction i.
 simpl in |- *.
    tauto.
intros.
  simpl in |- *.
  rewrite IHi in |- *.
   tauto.
Qed.

(* OK: *)

Theorem degreee_L0_split:
  forall (m : fmap) (x y : dart) (j : nat),
    inv_hmap m -> exd m x -> exd m y ->
       let m1 := L m zero x y in
       let x0 := cA m zero x in
       let dy := degreee m y in
    y = Iter (cA m zero) j x ->
      (2 <= j <= dy) ->
  degreee m1 y + degreee m1 x0 = degreee m y.
Proof.
simpl in |- *.
intros.
unfold degreee in |- *.
assert (ModcA0.Tr m x y = L m zero x y).
  tauto.
rewrite <- H4 in |- *.
  assert (cA m zero x = MA0Tr.MfM.f m x).
  tauto.
rewrite H5 in |- *.
  apply MA0Tr.degree_Tr_split with j.
  tauto.
 tauto.
 tauto.
rewrite MA0Tr_cA0_Iter in |- *.
   tauto.
unfold ModcA0.Prec_Tr in |- *.
   tauto.
fold (degreee m y) in |- *.
   lia.
Qed.

(*=================================================
          DIMENSION 1: expv_L1, degreev_L1
==================================================*)

Lemma MA1Tr_expo_expv: 
  MA1Tr.MfM.expo = expv.
Proof. tauto. Qed.

(* IT WORKS, BUT IT IS A BIT COMPLEX: *)

Lemma MA1Tr_expo_dec_expv_dec: 
 forall(m:fmap)(x y:dart)(H:inv_hmap m)(A B:Prop),
  (if MA1Tr.MfM.expo_dec m x y H then A else B) <->
  (if expv_dec m x y H then A else B).
Proof. 
intros.
elim (MA1Tr.MfM.expo_dec m x y H).
 elim (expv_dec m x y H).
   tauto.
  tauto.
elim (expv_dec m x y H).
  tauto.
 tauto.
Qed.

(* OK: *)

Lemma MA1Tr_between_betweenv: 
  MA1Tr.MfM.between = betweenv.
Proof. tauto. Qed.

(* OK: *)

Lemma ModcA1_Prec_Tr_True: forall(m:fmap)(x y:dart),
  ModcA1.Prec_Tr m x y = True.
Proof. tauto. Qed.

(* FROM WHERE: *)

Theorem expv_L1_CNS:
 forall (m:fmap)(x y z t:dart)(H:inv_hmap m),
     prec_L m one x y -> exd m z ->
       let x1 := cA m one x in
       let y_1 := cA_1 m one y in
       let m1 := L m one x y in
    (expv m1 z t <->
      (if expv_dec m x y H
       then
        betweenv m y z x /\ betweenv m y t x \/
        betweenv m x1 z y_1 /\ betweenv m x1 t y_1 \/
        ~ expv m x z /\ expv m z t
       else
        expv m z t \/
        expv m x z /\ expv m y t \/
        expv m x t /\ expv m y z)).
Proof.
intros.
assert (inv_hmap m1).
 unfold m1 in |- *.
   simpl in |- *.
    tauto.
rewrite <- MA1Tr_expo_expv in |- *.
  rewrite <- MA1Tr_between_betweenv in |- *.
  set
   (A1 :=
MA1Tr.MfM.between m y z x /\ 
    MA1Tr.MfM.between m y t x \/ 
 MA1Tr.MfM.between m x1 z y_1 /\ 
    MA1Tr.MfM.between m x1 t y_1 \/
    ~ MA1Tr.MfM.expo m x z /\ MA1Tr.MfM.expo m z t)
   in |- *.
  set
   (B1 :=
    MA1Tr.MfM.expo m z t \/
    MA1Tr.MfM.expo m x z /\ MA1Tr.MfM.expo m y t \/
    MA1Tr.MfM.expo m x t /\ MA1Tr.MfM.expo m y z) 
       in |- *.
  cut
   (MA1Tr.MfM.expo m1 z t <-> 
    (if MA1Tr.MfM.expo_dec m x y H then A1 else B1)).
 generalize (MA1Tr_expo_dec_expv_dec m x y H A1 B1).
    tauto.
unfold A1 in |- *; unfold B1 in |- *.
  unfold m1 in |- *.
  assert (ModcA1.Tr m x y = L m one x y).
  tauto.
rewrite <- H3 in |- *.
  assert (x1 = MA1Tr.MfM.f m x).
 unfold x1 in |- *.
    tauto.
assert (y_1 = MA1Tr.MfM.f_1 m y).
 unfold y_1 in |- *.
    tauto.
rewrite H4 in |- *.
  rewrite H5 in |- *.
  apply MA1Tr.expo_Tr_CNS.
 rewrite ModcA1_Prec_Tr_True in |- *.
    tauto.
unfold prec_L in H0.
   tauto.
unfold prec_L in H0.
   tauto.
 tauto.
assert (m1 = ModcA1.Tr m x y).
 unfold m1 in |- *.
    tauto.
rewrite <- H6 in |- *.
   tauto.
Qed.

(* DEGREES: *)

Open Scope nat_scope.

Definition degreev:=MA1Tr.MfM.degree.

(* OK: *)

Theorem degreev_L1_merge:
  forall (m : fmap) (x y : dart),
    inv_hmap m -> exd m x -> exd m y ->
       let m1 := L m one x y in
    ~ expv m x y ->
  degreev m1 y = degreev m y + degreev m x.
Proof.
simpl in |- *.
intros.
unfold degreev in |- *.
assert (ModcA1.Tr m x y = L m one x y).
  tauto.
rewrite <- H3 in |- *.
  apply MA1Tr.degree_Tr_merge_y.
 unfold ModcA1.Prec_Tr in |- *.
    tauto.
 tauto.
 tauto.
 tauto.
unfold expv in H2.
  assert (MA1.MfcA.expo = MA1Tr.MfM.expo).
  tauto.
rewrite <- H4 in |- *.
   tauto.
Qed.

(* OK: *)

Lemma MA1Tr_cA1_Iter: forall(m:fmap)(i:nat)(z:dart),
  Iter (MA1Tr.MfM.f m) i z = Iter (cA m one) i z.
Proof.
induction i.
 simpl in |- *.
    tauto.
intros.
  simpl in |- *.
  rewrite IHi in |- *.
   tauto.
Qed.

(* OK: *)

Theorem degreev_L1_split:
  forall (m : fmap) (x y : dart) (j : nat),
    inv_hmap m -> exd m x -> exd m y ->
       let m1 := L m one x y in
       let x1 := cA m one x in
       let dy := degreev m y in
    y = Iter (cA m one) j x ->
      (2 <= j <= dy) ->
  degreev m1 y + degreev m1 x1 = degreev m y.
Proof.
simpl in |- *.
intros.
unfold degreev in |- *.
assert (ModcA1.Tr m x y = L m one x y).
  tauto.
rewrite <- H4 in |- *.
  assert (cA m one x = MA1Tr.MfM.f m x).
  tauto.
rewrite H5 in |- *.
  apply MA1Tr.degree_Tr_split with j.
  tauto.
 tauto.
 tauto.
rewrite MA1Tr_cA1_Iter in |- *.
   tauto.
unfold ModcA1.Prec_Tr in |- *.
   tauto.
fold (degreev m y) in |- *.
   assumption.
Qed.

(*=====================================================
     INSTANTIATIONS OF MTr FOR Tr = L0, L1, 
             WRT cF, cF_1 : expof_L0, expof_L1
                degreef_L0, degreef_L1
 ====================================================*)

(* IN FACT, WE HAVE, WITHOUT PRECONDITION: *)

Lemma cF_L:forall(m:fmap)(k:dim)(x y z:dart),
cF (L m k x y) z =
  if eq_dim_dec k zero
  then
    cA_1 m one
       (if eq_dart_dec y z
        then x
        else
          if eq_dart_dec (cA m zero x) z
          then cA_1 m zero y
          else cA_1 m zero z) 
  else
    (if eq_dart_dec y (cA_1 m zero z)
     then x
     else
      if eq_dart_dec (cA m one x) (cA_1 m zero z)
      then cA_1 m one y
      else cA_1 m one (cA_1 m zero z)). 
Proof.
unfold cF in |- *.
intros.
simpl in |- *.
elim (eq_dim_dec k zero).
 intro.
   elim (eq_dim_dec k one).
  intro.
    rewrite a0 in a.
    inversion a.
  tauto.
 intro.
   elim (eq_dim_dec k one).
  tauto.
  intro.
    induction k.
   tauto.
   tauto.
Qed.

(* DIM 0, OK: *)

Lemma cF_L0_y1_x: forall(m:fmap)(x y z:dart),
 True ->
  inv_hmap m -> exd m x -> exd m y -> exd m z ->
  cF (L m zero (cA m one y) x) z =
    if eq_dart_dec x z then y
    else if eq_dart_dec (cF_1 m y) z then cF m x 
         else cF m z.
Proof.
intros.
rewrite cF_L in |- *.
elim (eq_dim_dec zero zero).
 fold (cF_1 m y) in |- *.
   elim (eq_dart_dec x z).
  rewrite cA_1_cA in |- *.
    tauto.
   tauto.
   tauto.
 elim (eq_dart_dec (cF_1 m y) z).
  fold (cF m x) in |- *.
     tauto.
 fold (cF m z) in |- *.
    tauto.
 tauto.
Qed.

(* OK: *)

Lemma cF_1_L0:forall(m:fmap)(x y z:dart),
  cF_1 (L m zero x y) z = 
    if eq_dart_dec x (cA m one z)
    then y
    else
     if eq_dart_dec (cA_1 m zero y) (cA m one z)
     then cA m zero x
     else cA m zero (cA m one z).
Proof.
intros.
unfold cF_1 in |- *.
simpl in |- *.
tauto.
Qed.

(* OK: *)

Lemma cF_1_L0_y1_x: forall(m:fmap)(x y z:dart),
 True ->
 inv_hmap m -> exd m x -> exd m y -> exd m z ->
  cF_1 (L m zero (cA m one y) x) z =
    if eq_dart_dec y z then x
    else if eq_dart_dec (cF m x) z then cF_1 m y 
         else cF_1 m z.
Proof.
intros.
rename H2 into Ez.
rewrite cF_1_L0 in |- *.
elim (eq_dart_dec (cA m one y) (cA m one z)).
 intro.
   elim (eq_dart_dec y z).
   tauto.
 intro.
   assert (y = cA_1 m one (cA m one z)).
  rewrite <- a in |- *.
    rewrite cA_1_cA in |- *.
    tauto.
   tauto.
   tauto.
 elim (eq_dart_dec (cF m x) z).
  intro.
    rewrite <- a0 in H2.
    rewrite cA_1_cA in H2.
   rewrite H2 in |- *.
     rewrite cF_1_cF in |- *.
     tauto.
    tauto.
    tauto.
   tauto.
  generalize (exd_cF m x).
     tauto.
 intro.
   rewrite cA_1_cA in H2.
   tauto.
  tauto.
  tauto.
elim (eq_dart_dec (cA_1 m zero x) (cA m one z)).
 elim (eq_dart_dec y z).
  intros.
    rewrite a in b.
     tauto.
 elim (eq_dart_dec (cF m x) z).
  fold (cF_1 m y) in |- *.
     tauto.
 intros.
   elim b.
   unfold cF in |- *.
   rewrite a in |- *.
   rewrite cA_1_cA in |- *.
   tauto.
  tauto.
  tauto.
elim (eq_dart_dec y z).
 intros.
   rewrite a in b0.
    tauto.
elim (eq_dart_dec (cF m x) z).
 intros.
   rewrite <- a in b0.
   unfold cF in b0.
   rewrite cA_cA_1 in b0.
   tauto.
  tauto.
 generalize (exd_cA_1 m zero x).
    tauto.
fold (cF_1 m z) in |- *.
   tauto.
Qed.

(* OK: *)

Lemma exd_L0_y1_x: forall (m : fmap)(x y z : dart),
  inv_hmap m -> 
    (exd m z <-> exd (L m zero (cA m one y) x) z).
Proof. intros. simpl in |- *. tauto. Qed.

(* OK: *)

Lemma ndN_L0_y1_x: forall (m : fmap)(x y:dart),
  ndN (L m zero (cA m one y) x) = ndN m.
Proof. simpl in |- *. tauto. Qed.

(* DIMENSION 1: OK: *)

Lemma cF_L1_y_x_0: forall(m:fmap)(x y z:dart),
 True ->
  inv_hmap m -> exd m x -> exd m y -> exd m z ->
  cF (L m one y (cA_1 m zero x)) z =
    if eq_dart_dec x z then y
    else if eq_dart_dec (cF_1 m y) z then cF m x 
         else cF m z.
Proof.
intros m x y z Pr.
intros.
rewrite cF_L in |- *.
elim (eq_dim_dec one zero).
 intro.
   inversion a.
elim (eq_dart_dec (cA_1 m zero x) (cA_1 m zero z)).
 elim (eq_dart_dec x z).
   tauto.
 intros.
   assert (x = cA m zero (cA_1 m zero z)).
  rewrite <- a in |- *.
    rewrite cA_cA_1 in |- *.
    tauto.
   tauto.
   tauto.
 rewrite cA_cA_1 in H3.
   tauto.
  tauto.
  tauto.
elim (eq_dart_dec (cA m one y) (cA_1 m zero z)).
 fold (cF m x) in |- *.
   elim (eq_dart_dec x z).
  intros.
    rewrite a in b.
     tauto.
 elim (eq_dart_dec (cF_1 m y) z).
   tauto.
 intros.
   elim b.
   unfold cF_1 in |- *.
   rewrite a in |- *.
   rewrite cA_cA_1 in |- *.
   tauto.
  tauto.
  tauto.
fold (cF m z) in |- *.
  elim (eq_dart_dec x z).
 intros.
   rewrite a in b0.
    tauto.
elim (eq_dart_dec (cF_1 m y) z).
 intros.
   rewrite <- a in b0.
   unfold cF_1 in b0.
   rewrite cA_1_cA in b0.
   tauto.
  tauto.
 generalize (exd_cA m one y).
    tauto.
 tauto.
Qed.

(* OK: *)

Lemma cF_1_L1:forall(m:fmap)(x y z:dart),
  cF_1 (L m one x y) z =
   cA m zero
     (if eq_dart_dec x z
      then y
      else 
         if eq_dart_dec (cA_1 m one y) z 
         then cA m one x 
         else cA m one z).
Proof.
intros.
unfold cF_1 in |- *.
simpl in |- *.
 tauto.
Qed.

(* OK: *)

Lemma cF_1_L1_y_x_0: forall(m:fmap)(x y z:dart),
 True ->
 inv_hmap m -> exd m x -> exd m y -> exd m z ->
   cF_1 (L m one y (cA_1 m zero x)) z =
    if eq_dart_dec y z then x
    else if eq_dart_dec (cF m x) z then cF_1 m y 
         else cF_1 m z.
Proof.
intros m x y z Pr.
intros.
rename H2 into Ez.
rewrite cF_1_L1 in |- *.
elim (eq_dart_dec y z).
 rewrite cA_cA_1 in |- *.
   tauto.
  tauto.
  tauto.
fold (cF m x) in |- *.
  elim (eq_dart_dec (cF m x) z).
 fold (cF_1 m y) in |- *.
    tauto.
fold (cF_1 m z) in |- *.
   tauto.
Qed.

Lemma exd_L1_y_x_0: forall (m : fmap)(x y z : dart),
  inv_hmap m -> 
    (exd m z <-> exd (L m one y (cA_1 m zero x)) z).
Proof.
intros.
generalize (exd_L m zero y (cA_1 m zero x) z).
 tauto.
Qed.

(* OK: *)

Lemma ndN_L1_y_x_0: forall (m : fmap)(x y:dart),
  ndN (L m one y (cA_1 m zero x)) = ndN m.
Proof. simpl. tauto. Qed.

(* DIM 0: IMMEDIATE *)

Module ModcF0<:SigTr 
 with Definition Tr:= 
   fun(m:fmap)(x y:dart) => L m zero (cA m one y) x
 with Definition Prec_Tr:= 
  fun(m:fmap)(x y:dart) => True.
Module M:=McF.
Definition Tr(m:fmap)(x y:dart):= 
  L m zero (cA m one y) x.
Definition Prec_Tr(m:fmap)(x y:dart):= True.
Definition f_Tr := cF_L0_y1_x.
Definition f_1_Tr := cF_1_L0_y1_x.
Definition exd_Tr := exd_L0_y1_x.
Definition ndN_Tr := ndN_L0_y1_x.
End ModcF0.

(* OK: *)

Module MF0Tr := MTr ModcF0.

(* DIM 1: IDEM *)

Module ModcF1<:SigTr 
 with Definition Tr:= 
  fun(m:fmap)(x y:dart) => L m one y (cA_1 m zero x)
 with Definition Prec_Tr:= 
  fun(m:fmap)(x y:dart) => True.
Module M:=McF.
Definition Tr(m:fmap)(x y:dart):=
  L m one y (cA_1 m zero x).
Definition Prec_Tr(m:fmap)(x y:dart):= True.
Definition f_Tr := cF_L1_y_x_0.
Definition f_1_Tr := cF_1_L1_y_x_0.
Definition exd_Tr := exd_L1_y_x_0.
Definition ndN_Tr:=ndN_L1_y_x_0.
End ModcF1.

(* OK: *)

Module MF1Tr := MTr ModcF1.

(*=====================================================
           CORRESPONDENCES BETWEEN MODULES
=====================================================*)

(* DIM 0, OK: *)

Lemma MF0Tr_expo_expof:
  MF0Tr.MfM.expo = expof.
Proof. tauto. Qed.

Lemma cF_L0_ModcF0: forall(m:fmap)(x y z:dart),
  inv_hmap m -> exd m x -> exd m y -> exd m z ->
     cF (L m zero x y) z = 
       MF0Tr.MfM.f (ModcF0.Tr m y (cA_1 m one x)) z.
Proof.
intros.
assert (MF0Tr.MfM.f = cF).
  tauto.
rewrite H3 in |- *.
  unfold ModcF0.Tr in |- *.
  rewrite cA_cA_1 in |- *.
  tauto.
 tauto.
 tauto.
Qed.

Lemma exd_ModcF0: forall(m : fmap)(x y z : dart),
  exd (ModcF0.Tr m y (cA_1 m one x)) z <-> 
     exd (L m zero x y) z.
Proof. simpl in |- *. tauto. Qed.

Lemma cA_ModcF0: 
forall(m:fmap)(x y:dart)(k:dim)(z:dart),
 let m1 := L m zero x y in
  inv_hmap m1 ->
    cA (ModcF0.Tr m y (cA_1 m one x)) k z = cA m1 k z.
Proof.
intros.
unfold m1 in |- *.
unfold m1 in H; simpl in H; unfold prec_L in H.
elim k.
 simpl in |- *.
   rewrite cA_cA_1 in |- *.
   tauto.
  tauto.
  tauto.
simpl in |- *.
   tauto.
Qed.

(* OK: *)

Lemma inv_hmap_ModcF0: forall(m:fmap)(x y:dart),
 let m1 := L m zero x y in
  inv_hmap (ModcF0.Tr m y (cA_1 m one x)) 
    <-> inv_hmap m1.
Proof.
unfold ModcF0.Tr in |- *.
split.
 intro.
   simpl in H.
   unfold prec_L in H.
   decompose [and] H.
   clear H.
   assert (exd m x).
  generalize (exd_cA m one (cA_1 m one x)).
    generalize (exd_cA_1 m one x).
     tauto.
 rewrite cA_cA_1 in H3.
  rewrite cA_cA_1 in H6.
   simpl in |- *.
     unfold prec_L in |- *.
      tauto.
   tauto.
   tauto.
  tauto.
  tauto.
simpl in |- *.
  intros.
  assert (exd m x).
 unfold prec_L in H.
    tauto.
rewrite cA_cA_1 in |- *.
  tauto.
 tauto.
 tauto.
Qed.

(* OK:*)

Lemma Iter_ModcF0_Tr: 
forall(m:fmap)(x y z:dart)(i:nat),
 let m1:= L m zero x y in inv_hmap m1 -> exd m z ->
  Iter (cF (L m zero x y)) i z = 
  Iter (ModcF0.M.f (ModcF0.Tr m y (cA_1 m one x))) i z.
Proof.
intros.
assert (ModcF0.M.f = cF).
  tauto.
rewrite H1 in |- *.
  assert (cF (L m zero x y) = 
    cF (ModcF0.Tr m y (cA_1 m one x))).
 assert (L m zero x y = ModcF0.Tr m y (cA_1 m one x)).
  unfold ModcF0.Tr in |- *.
    rewrite cA_cA_1 in |- *.
    tauto.
  unfold m1 in H.
    simpl in H.
     tauto.
  unfold m1 in H; simpl in H; unfold prec_L in H.
     tauto.
 rewrite <- H2 in |- *.
    tauto.
rewrite <- H2 in |- *.
   tauto.
Qed.

(* OK: *)

Lemma expo_ModcF0_Tr: forall(m:fmap)(x y z t:dart),
 let m1 := L m zero x y in inv_hmap m1 ->
   (MF0Tr.MfM.expo (ModcF0.Tr m y (cA_1 m one x)) z t
     <-> expof m1 z t).
Proof.
intros.
assert (MF0Tr.MfM.expo = expof).
  tauto.
rewrite H0 in |- *.
  unfold ModcF0.Tr in |- *.
  rewrite cA_cA_1 in |- *.
 fold m1 in |- *.
    tauto.
unfold m1 in H.
  simpl in H.
   tauto.
unfold m1 in H; simpl in H; unfold prec_L in H.
   tauto.
Qed.

(* DIM 1: OK: *)

Lemma MF1Tr_expo_expof:
  MF1Tr.MfM.expo = expof.
Proof. tauto. Qed.

Lemma cF_L1_ModcF1: forall(m:fmap)(x y z:dart),
  inv_hmap m -> exd m x -> exd m y -> exd m z ->
     cF (L m one x y) z = 
       MF1Tr.MfM.f (ModcF1.Tr m (cA m zero y) x) z.
Proof.
intros.
assert (MF1Tr.MfM.f = cF).
  tauto.
rewrite H3 in |- *.
  unfold ModcF1.Tr in |- *.
  rewrite cA_1_cA in |- *.
  tauto.
 tauto.
 tauto.
Qed.

Lemma exd_ModcF1: forall(m : fmap)(x y z : dart),
  exd (ModcF1.Tr m (cA m zero y) x) z <-> 
     exd (L m one x y) z.
Proof. simpl in |- *. tauto. Qed.

Lemma cA_ModcF1: 
forall(m:fmap)(x y:dart)(k:dim)(z:dart),
 let m1 := L m one x y in
  inv_hmap m1 ->
    cA (ModcF1.Tr m (cA m zero y) x) k z = cA m1 k z.
Proof.
intros.
unfold m1 in |- *.
elim k.
 simpl in |- *.
    tauto.
simpl in |- *.
  unfold m1 in H.
  simpl in H.
  unfold prec_L in H.
  decompose [and] H.
  clear H.
  rewrite cA_1_cA in |- *.
  tauto.
 tauto.
 tauto.
Qed.

(* OK!: *)

Lemma inv_hmap_ModcF1: forall(m:fmap)(x y:dart),
 let m1 := L m one x y in
  inv_hmap (ModcF1.Tr m (cA m zero y) x) 
    <-> inv_hmap m1.
Proof.
unfold ModcF1.Tr in |- *.
split.
 intro.
   simpl in H.
   unfold prec_L in H.
   decompose [and] H.
   clear H.
   assert (exd m y).
  generalize (exd_cA m zero y).
    generalize (exd_cA_1 m zero (cA m zero y)).
     tauto.
 rewrite cA_1_cA in H4.
  rewrite cA_1_cA in H6.
   simpl in |- *.
     split.
     tauto.
   unfold prec_L in |- *.
      tauto.
   tauto.
   tauto.
  tauto.
  tauto.
simpl in |- *.
  unfold prec_L in |- *.
  intros.
  rewrite cA_1_cA in |- *.
  tauto.
 tauto.
 tauto.
Qed.

(* OK!! :*)

Lemma Iter_ModcF1_Tr: 
forall(m:fmap)(x y z:dart)(i:nat),
 let m1:= L m one x y in inv_hmap m1 -> exd m z ->
  Iter (cF (L m one x y)) i z = 
   Iter (ModcF1.M.f (ModcF1.Tr m (cA m zero y) x)) i z.
Proof.
intros.
assert (ModcF1.M.f = cF).
  tauto.
rewrite H1 in |- *.
  assert (cF (L m one x y) = 
    cF (ModcF1.Tr m (cA m zero y) x)).
 assert (L m one x y = ModcF1.Tr m (cA m zero y) x).
  unfold ModcF1.Tr in |- *.
    rewrite cA_1_cA in |- *.
    tauto.
  unfold m1 in H.
    simpl in H.
     tauto.
  unfold m1 in H; simpl in H; unfold prec_L in H.
     tauto.
 rewrite <- H2 in |- *.
    tauto.
rewrite <- H2 in |- *.
   tauto.
Qed.

(* OK!! *)

Lemma expo_ModcF1_Tr: forall(m:fmap)(x y z t:dart),
 let m1 := L m one x y in inv_hmap m1 ->
   (MF1Tr.MfM.expo (ModcF1.Tr m (cA m zero y) x) z t
     <-> expof m1 z t).
Proof.
intros.
assert (MF1Tr.MfM.expo = MF.expo).
  tauto.
rewrite H0 in |- *.
  unfold ModcF1.Tr in |- *.
  rewrite cA_1_cA in |- *.
 fold m1 in |- *.
    tauto.
unfold m1 in H.
  simpl in H.
   tauto.
unfold m1 in H; simpl in H; unfold prec_L in H.
   tauto.
Qed.

(*====================================================           
           INSTANTIATIONS "IN CLEAR" OF
                  expof_L0/L1_CNS
       degreef_L0, degreef_L1 (MERGE AND SPLIT)
=====================================================*)

(* DIMENSION 0: /L0 *)

(* WORKS, BUT A BIT COMPLEX: *)

Lemma MF0Tr_expo_dec_expof_dec: 
 forall(m:fmap)(x y:dart)(H:inv_hmap m)(A B:Prop),
  (if MF0Tr.MfM.expo_dec m x y H then A else B) <->
  (if expof_dec m x y H then A else B).
Proof. 
intros.
elim (MF0Tr.MfM.expo_dec m x y H).
 elim (expof_dec m x y H).
   tauto.
  tauto.
elim (expof_dec m x y H).
  tauto.
 tauto.
Qed.

(* OK: *)

Lemma MF0Tr_between_betweenf: 
  MF0Tr.MfM.between = betweenf.
Proof. tauto. Qed.

(* OK: *)

Lemma MF0Tr_Prec_Tr_True: forall(m:fmap)(x y:dart),
  ModcF0.Prec_Tr m x y = True.
Proof. tauto. Qed.

(* OK: *)

Theorem expof_L0_y0_x_CNS: 
  forall (m : fmap) (x y z t : dart) (H : inv_hmap m),
       let m1 := L m zero (cA m one y) x in
       let x1 := cF m x in
       let y_1 := cF_1 m y in
     inv_hmap m1 -> exd m z ->
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
unfold m1 in H0.
simpl in H0.
unfold prec_L in H0.
assert (exd m y).
 generalize (exd_cA m one y).
    tauto.
rewrite <- MF0Tr_between_betweenf in |- *.
  set
   (A0 :=
    MF0Tr.MfM.between m y z x 
     /\ MF0Tr.MfM.between m y t x \/
    MF0Tr.MfM.between m x1 z y_1 
      /\ MF0Tr.MfM.between m x1 t y_1 \/
    ~ expof m x z /\ expof m z t) in |- *.
  set
   (B0 := expof m z t \/ expof m x z /\ expof m y t \/
          expof m x t /\ expof m y z) in |- *.
  cut (expof m1 z t <-> 
   (if MF0Tr.MfM.expo_dec m x y H then A0 else B0)).
 generalize (MF0Tr_expo_dec_expof_dec m x y H A0 B0).
    tauto.
unfold A0 in |- *.
  rewrite <- MF0Tr_expo_expof in |- *.
  unfold B0 in |- *.
  rewrite <- MF0Tr_expo_expof in |- *.
  assert (x1 = MF0Tr.MfM.f m x).
  tauto.
assert (y_1 = MF0Tr.MfM.f_1 m y).
  tauto.
assert (m1 = ModcF0.Tr m x y).
  tauto.
rewrite H5 in |- *.
  rewrite H4 in |- *.
  rewrite H3 in |- *.
  apply MF0Tr.expo_Tr_CNS.
 unfold ModcF0.Prec_Tr in |- *.
    tauto.
 tauto.
 tauto.
 tauto.
rewrite <- H5 in |- *.
  unfold m1 in |- *.
  simpl in |- *.
  unfold prec_L in |- *.
   tauto.
Qed.

(* USUAL FORM: *)

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
Proof.
intros.
assert (exd m X).
 unfold prec_L in H0;  tauto.
set (x := Y) in |- *.
  set (y := cA_1 m one X) in |- *.
  set (x1 := cF m x) in |- *.
  set (y_1 := cF_1 m y) in |- *.
  assert (X_1 = y).
 unfold X_1 in |- *.
   fold y in |- *.
    tauto.
rewrite H3 in |- *.
  assert (Y_0_1 = x1).
 unfold x1 in |- *.
   unfold x in |- *.
   fold Y_0_1 in |- *.
    tauto.
rewrite H4 in |- *.
  assert (X0 = y_1).
 unfold y_1 in |- *.
   unfold y in |- *.
   unfold cF_1 in |- *.
   rewrite cA_cA_1 in |- *.
  fold X0 in |- *.
     tauto.
  tauto.
  tauto.
rewrite H5 in |- *.
  fold x in m1.
  assert (X = cA m one y).
 unfold y in |- *.
   rewrite cA_cA_1 in |- *.
   tauto.
  tauto.
  tauto.
unfold m1 in |- *; rewrite H6 in |- *.
  unfold x1 in |- *; unfold y_1 in |- *.
  apply expof_L0_y0_x_CNS.
 rewrite <- H6 in |- *.
   simpl in |- *.
    tauto.
 tauto.
Qed.

Definition degreef:=MF0Tr.MfM.degree.

Lemma degreef_0_1:
  MF0Tr.MfM.degree = MF1Tr.MfM.degree.
Proof. tauto. Qed.

(* FACE DEGREES / L0, MERGE : *) 

Theorem degree_L0_merge_summary:
 forall (m : fmap) (X Y Z : dart)(H:inv_hmap m),
     prec_L m zero X Y -> exd m Z ->
       let m1 := L m zero X Y in
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
   simpl in |- *.
    tauto.
assert (exd m X /\ exd m Y).
 unfold prec_L in H0.
    tauto.
elim H4.
  clear H4.
  intros.
  assert (m1 = ModcF0.Tr m Y X_1).
 unfold ModcF0.Tr in |- *.
   unfold X_1 in |- *.
   rewrite cA_cA_1 in |- *.
  fold m1 in |- *.
     tauto.
  tauto.
  tauto.
assert (ModcF0.Prec_Tr m Y X_1).
 unfold ModcF0.Prec_Tr in |- *.
    tauto.
assert (exd m X_1).
 unfold X_1 in |- *.
   generalize (exd_cA_1 m one X).
    tauto.
assert (~ MF0Tr.MfM.expo m Y X_1).
  tauto.
assert (degreef = MF0Tr.MfM.degree).
  tauto.
rewrite H10 in |- *.
  rewrite H6 in H3.
  generalize (MF0Tr.degree_Tr_merge_summary 
    m Y X_1 Z H H7 H5 H8 H1 H3 H9).
  rewrite <- H6 in |- *.
  rewrite <- H10 in |- *.
  fold dY in |- *; fold dX_1 in |- *.
  elim (MF0Tr.MfM.expo_dec m Y Z H).
 elim (expof_dec m Y Z H).
   tauto.
  tauto.
elim (expof_dec m Y Z H).
  tauto.
elim (MF0Tr.MfM.expo_dec m X_1 Z H).
 elim (expof_dec m X_1 Z H).
   tauto.
  tauto.
elim (expof_dec m X_1 Z H).
  tauto.
 tauto.
Qed.

(* FACE DEGREES / L0, SPLIT: *) 

Theorem degreef_L0_split_summary:
 forall (m : fmap) (X Y Z : dart) (j : nat) 
        (H : inv_hmap m), 
     prec_L m zero X Y -> exd m Z ->
       let m1 := L m zero X Y in
       let X_1:= cA_1 m one X in
       let Y1 := cF m Y in
       let dX_1 := degreef m X_1 in
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
   simpl in |- *.
    tauto.
assert (exd m X /\ exd m Y).
 unfold prec_L in H0.
    tauto.
elim H5; clear H5; intros.
  assert (m1 = ModcF0.Tr m Y X_1).
 unfold ModcF0.Tr in |- *.
   unfold X_1 in |- *.
   rewrite cA_cA_1 in |- *.
  fold m1 in |- *.
     tauto.
  tauto.
  tauto.
assert (ModcF0.Prec_Tr m Y X_1).
 unfold ModcF0.Prec_Tr in |- *.
    tauto.
assert (exd m X_1).
 unfold X_1 in |- *.
   generalize (exd_cA_1 m one X).
    tauto.
assert (degreef = MF0Tr.MfM.degree).
  tauto.
assert (cF = MF0Tr.MfM.f).
  tauto.
rewrite H11 in H2.
  rewrite H7 in H4.
  generalize
   (MF0Tr.degree_Tr_split_summary 
     m Y X_1 Z j H H8 H6 H9 H1 H2 H3 H4).
  rewrite <- H11 in |- *.
  rewrite <- H7 in |- *.
  rewrite <- H10 in |- *.
  fold Y1 in |- *.
  elim (MF0Tr.MfM.expo_dec m X_1 Z H).
 elim (expof_dec m X_1 Z H).
   tauto.
  tauto.
elim (expof_dec m X_1 Z H).
  tauto.
 tauto.
Qed.

(* DIMENSION 1: /L1 *)

(* WORKS, BUT A BIT COMPLEX: *)

Lemma MF1Tr_expo_dec_expof_dec: 
 forall(m:fmap)(x y:dart)(H:inv_hmap m)(A B:Prop),
  (if MF1Tr.MfM.expo_dec m x y H then A else B) <->
  (if expof_dec m x y H then A else B).
Proof. 
intros.
elim (MF1Tr.MfM.expo_dec m x y H).
 elim (expof_dec m x y H).
   tauto.
  tauto.
elim (expof_dec m x y H).
  tauto.
 tauto.
Qed.

(* OK: *)

Lemma MF1Tr_between_betweenf: 
  MF1Tr.MfM.between = betweenf.
Proof. tauto. Qed.

(* OK: *)

Lemma MF1Tr_Prec_Tr_True: forall(m:fmap)(x y:dart),
  ModcF1.Prec_Tr m x y = True.
Proof. tauto. Qed.

(* OK: *)

Theorem expof_L1_y_x_0_CNS: 
  forall (m : fmap) (x y z t : dart) (H : inv_hmap m),
       let m1 := L m one y (cA_1 m zero x) in 
       let x1 := cF m x in
       let y_1 := cF_1 m y in
     inv_hmap m1 -> exd m z ->
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
unfold m1 in H0.
simpl in H0.
unfold prec_L in H0.
assert (exd m x).
 generalize (exd_cA_1 m zero x).
    tauto.
rewrite <- MF1Tr_between_betweenf in |- *.
  set
   (A0 :=
    MF1Tr.MfM.between m y z x /\
       MF1Tr.MfM.between m y t x \/
    MF1Tr.MfM.between m x1 z y_1 /\
       MF1Tr.MfM.between m x1 t y_1 \/
    ~ expof m x z /\ expof m z t) in |- *.
  set
   (B0 := expof m z t \/ expof m x z /\ expof m y t 
       \/ expof m x t /\ expof m y z)
   in |- *.
  cut (expof m1 z t <->
    (if MF1Tr.MfM.expo_dec m x y H then A0 else B0)).
 generalize (MF1Tr_expo_dec_expof_dec m x y H A0 B0).
    tauto.
unfold A0 in |- *.
  rewrite <- MF1Tr_expo_expof in |- *.
  unfold B0 in |- *.
  rewrite <- MF1Tr_expo_expof in |- *.
  assert (x1 = MF1Tr.MfM.f m x).
  tauto.
assert (y_1 = MF1Tr.MfM.f_1 m y).
  tauto.
assert (m1 = ModcF1.Tr m x y).
  tauto.
rewrite H5 in |- *.
  rewrite H4 in |- *.
  rewrite H3 in |- *.
  apply MF1Tr.expo_Tr_CNS.
 unfold ModcF1.Prec_Tr in |- *.
    tauto.
 tauto.
 tauto.
 tauto.
rewrite <- H5 in |- *.
  unfold m1 in |- *.
  simpl in |- *.
  unfold prec_L in |- *.
   tauto.
Qed.

(* USUAL FORMULATION, OK: *)

Theorem expof_L1_CNS: 
  forall (m : fmap) (X Y z t : dart) (H : inv_hmap m),
     prec_L m one X Y -> exd m z ->
       let m1 := L m one X Y in 
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
assert (exd m Y).
 unfold prec_L in H0;  tauto.
set (y := X) in |- *.
  set (x := cA m zero Y) in |- *.
  set (x1 := cF m x) in |- *.
  set (y_1 := cF_1 m y) in |- *.
  assert (x1 = Y_1).
 unfold Y_1 in |- *.
   unfold x1 in |- *.
   unfold x in |- *.
   unfold cF in |- *.
   rewrite cA_1_cA in |- *.
   tauto.
  tauto.
  tauto.
assert (y_1 = X10).
 unfold X10 in |- *.
   fold y in |- *.
   fold y_1 in |- *.
    tauto.
rewrite <- H3 in |- *.
  rewrite <- H4 in |- *.
  assert (Y0 = x).
 unfold Y0 in |- *.
   fold x in |- *.
    tauto.
rewrite H5 in |- *.
  fold y in m1.
  assert (Y = cA_1 m zero x).
 unfold x in |- *.
   rewrite cA_1_cA in |- *.
   tauto.
  tauto.
  tauto.
unfold m1 in |- *.
  rewrite H6 in |- *.
  unfold x1 in |- *; unfold y_1 in |- *.
  apply expof_L1_y_x_0_CNS.
 rewrite <- H6 in |- *.
   simpl in |- *.
   unfold y in |- *.
 tauto.
 tauto.
Qed.

(* degreef_L1, MERGE: *)

Theorem degreef_L1_merge_summary:
 forall (m : fmap) (X Y Z : dart)(H:inv_hmap m),
     prec_L m one X Y -> exd m Z ->
       let m1 := L m one X Y in
       let Y0 := cA m zero Y in 
       let dY0 := degreef m Y0 in
       let dX := degreef m X in
   ~ expof m Y0 X ->
     degreef m1 Z =
       (if expof_dec m Y0 Z H
        then dY0 + dX
        else
         if expof_dec m X Z H then dY0 + dX 
         else degreef m Z).
Proof.
intros.
assert (inv_hmap m1).
 unfold m1 in |- *.
   simpl in |- *.
    tauto.
assert (exd m X /\ exd m Y).
 unfold prec_L in H0.
    tauto.
elim H4.
  clear H4.
  intros.
  assert (m1 = ModcF1.Tr m Y0 X).
 unfold ModcF1.Tr in |- *.
   unfold Y0 in |- *.
   rewrite cA_1_cA in |- *.
  fold m1 in |- *.
     tauto.
  tauto.
  tauto.
assert (ModcF1.Prec_Tr m Y0 X).
 unfold ModcF1.Prec_Tr in |- *.
    tauto.
assert (exd m Y0).
 unfold Y0 in |- *.
   generalize (exd_cA m zero Y).
    tauto.
assert (~ MF1Tr.MfM.expo m Y0 X).
  tauto.
assert (degreef = MF1Tr.MfM.degree).
  tauto.
rewrite H10 in |- *.
  rewrite H6 in H3.
  generalize (MF1Tr.degree_Tr_merge_summary 
    m Y0 X Z H H7 H8 H4 H1 H3 H9).
  rewrite <- H6 in |- *.
  rewrite <- H10 in |- *.
  fold dX in |- *.
  fold dY0 in |- *.
  elim (MF1Tr.MfM.expo_dec m Y0 Z H).
 elim (expof_dec m Y0 Z H).
   tauto.
  tauto.
elim (expof_dec m Y0 Z H).
  tauto.
elim (MF1Tr.MfM.expo_dec m X Z H).
 elim (expof_dec m X Z H).
   tauto.
  tauto.
elim (expof_dec m X Z H).
  tauto.
 tauto.
Qed.

(* degreef_L1, SPLIT: *)

Theorem degreef_L1_split_summary:
 forall (m : fmap) (X Y Z : dart) (j : nat) 
        (H : inv_hmap m), 
     prec_L m one X Y -> exd m Z ->
       let m1 := L m one X Y in
       let Y0 := cA m zero Y in 
       let Y01 := cF m Y0 in
       let dX := degreef m X in
       X = Iter (cF m) j Y0 ->
       2 <= j <= dX ->
    degreef m Z =
       (if expof_dec m X Z H
        then degreef m1 X + degreef m1 Y01
        else degreef m1 Z).
Proof.
intros.
assert (inv_hmap m1).
 unfold m1 in |- *.
   simpl in |- *.
    tauto.
assert (exd m X /\ exd m Y).
 unfold prec_L in H0.
    tauto.
elim H5.
  clear H5.
  intros.
  assert (m1 = ModcF1.Tr m Y0 X).
 unfold ModcF1.Tr in |- *.
   unfold Y0 in |- *.
   rewrite cA_1_cA in |- *.
  fold m1 in |- *.
     tauto.
  tauto.
  tauto.
assert (ModcF1.Prec_Tr m Y0 X).
 unfold ModcF1.Prec_Tr in |- *.
    tauto.
assert (exd m Y0).
 unfold Y0 in |- *.
   generalize (exd_cA m zero Y).
    tauto.
assert (degreef = MF1Tr.MfM.degree).
  tauto.
assert (cF = MF1Tr.MfM.f).
  tauto.
rewrite H11 in H2.
  rewrite H7 in H4.
  generalize
   (MF1Tr.degree_Tr_split_summary 
       m Y0 X Z j H H8 H9 H5 H1 H2 H3 H4).
  rewrite <- H11 in |- *.
  rewrite <- H7 in |- *.
  rewrite <- H10 in |- *.
  fold Y01 in |- *.
  elim (MF1Tr.MfM.expo_dec m X Z H).
 elim (expof_dec m X Z H).
   tauto.
  tauto.
elim (expof_dec m X Z H).
  tauto.
tauto.
Qed.

(*===================================================
             INSTANTIATION OF MTr 
   FOR Tr = Split (CUTTING) (WITH PREC crack)
              / cA0, cA1
===================================================*)

Lemma ndN_B:forall(m:fmap)(k:dim)(z:dart),
  ndN (B m k z) = ndN m.
Proof.
induction m.
 simpl in |- *.
    tauto.
intros.
  simpl in |- *.
  elim (exd_dec (B m k z) d).
 intro.
   elim (exd_dec m d).
  intro.
    apply IHm.
 intro.
   generalize (exd_B m k z d).
    tauto.
elim (exd_dec m d).
 intros.
   generalize (exd_B m k z d).
    tauto.
rewrite IHm in |- *.
   tauto.
intros.
  simpl in |- *.
  elim (eq_dim_dec d k).
 elim (eq_dart_dec d0 z).
   tauto.
 simpl in |- *.
   intros.
   apply IHm.
simpl in |- *.
  intro.
  apply IHm.
Qed.

Lemma ndN_Split:forall(m:fmap)(k:dim)(x y:dart),
  ndN (Split m k x y) = ndN m.
Proof.
unfold Split in |- *.
intros.
elim (succ_dec m k x).
 elim (succ_dec m k y).
  rewrite ndN_B in |- *.
    simpl in |- *.
    rewrite ndN_B in |- *.
     tauto.
 rewrite ndN_B in |- *.
    tauto.
rewrite ndN_B in |- *.
   tauto.
Qed.

(* DIMENSION 0: *)

Definition cracke:= MA0.crack.

Lemma cA_Split0_x_y_0: forall(m:fmap)(x y z:dart),
 cracke m x (cA_1 m zero y) -> 
  inv_hmap m -> exd m x -> exd m y -> exd m z ->
 cA (Split m zero x (cA_1 m zero y)) zero z =
   if eq_dart_dec x z then y 
   else if eq_dart_dec (cA_1 m zero y) z 
        then (cA m zero x)
        else (cA m zero z).
Proof.
unfold cracke in |- *.
intros.
rewrite MA0.cA_Split in |- *.
 assert (Md0.kd = zero).
   tauto.
 rewrite H4 in |- *.
   rewrite cA_cA_1 in |- *.
   tauto.
  tauto.
  tauto.
 tauto.
 tauto.
Qed.

Lemma cA_1_Split0_x_y_0: forall(m:fmap)(x y z:dart),
 cracke m x (cA_1 m zero y) -> 
  inv_hmap m -> exd m x -> exd m y -> exd m z ->
 cA_1 (Split m zero x (cA_1 m zero y)) zero z =
   if eq_dart_dec y z then x 
   else if eq_dart_dec (cA m zero x) z 
        then (cA_1 m zero y) 
        else (cA_1 m zero z).
Proof.
unfold cracke in |- *.
intros.
rewrite MA0.cA_1_Split in |- *.
 assert (Md0.kd = zero).
   tauto.
 rewrite H4 in |- *.
   rewrite cA_cA_1 in |- *.
  elim (eq_dart_dec (cA m zero x) z).
   elim (eq_dart_dec y z).
    intros.
      unfold MA0.crack in H.
       absurd (x = cA_1 m zero y).
      tauto.
    rewrite a in |- *.
      rewrite <- a0 in |- *.
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
Qed.

Lemma exd_Split0_x_y_0 : forall(m:fmap)(x y z:dart), 
  inv_hmap m -> 
   (exd m z <-> 
     exd (Split m zero x (cA_1 m zero y)) z).
Proof.
intros.
generalize (exd_Split m zero x (cA_1 m zero y) z).
 tauto.
Qed.

Lemma ndN_Split0_x_y_0 : forall (m:fmap)(x y:dart),
  ndN (Split m zero x (cA_1 m zero y)) = ndN m.
Proof. intros. apply ndN_Split. Qed.

Module ModSplit0cA0<:SigTr
 with Definition Tr:= fun(m:fmap)(x y:dart)=> 
    Split m zero x (cA_1 m zero y)
 with Definition Prec_Tr:= fun(m:fmap)(x y:dart)=> 
    cracke m x (cA_1 m zero y).
Module M:= ModcA0.M.
Definition Tr:= fun(m:fmap)(x y:dart)=> 
  Split m zero x (cA_1 m zero y).
Definition Prec_Tr(m:fmap)(x y:dart):= 
  cracke m x (cA_1 m zero y).
Definition f_Tr:= cA_Split0_x_y_0.
Definition f_1_Tr:= cA_1_Split0_x_y_0.
Definition exd_Tr:= exd_Split0_x_y_0.
Definition ndN_Tr:= ndN_Split0_x_y_0.
End ModSplit0cA0.

Module MA0TrSplit0:= MTr ModSplit0cA0.

(* DIMENSION 1: *)

Definition crackv:= MA1.crack.

Lemma cA_Split1_x_y_1: forall(m:fmap)(x y z:dart),
 crackv m x (cA_1 m one y) -> 
  inv_hmap m -> exd m x -> exd m y -> exd m z ->
 cA (Split m one x (cA_1 m one y)) one z =
   if eq_dart_dec x z then y 
   else if eq_dart_dec (cA_1 m one y) z 
        then (cA m one x)
        else (cA m one z).
Proof.
unfold crackv in |- *.
intros.
rewrite MA1.cA_Split in |- *.
 assert (Md1.kd = one).
   tauto.
 rewrite H4 in |- *.
   rewrite cA_cA_1 in |- *.
   tauto.
  tauto.
  tauto.
 tauto.
 tauto.
Qed.

Lemma cA_1_Split1_x_y_1: forall(m:fmap)(x y z:dart),
 crackv m x (cA_1 m one y) -> 
  inv_hmap m -> exd m x -> exd m y -> exd m z ->
 cA_1 (Split m one x (cA_1 m one y)) one z =
   if eq_dart_dec y z then x 
   else if eq_dart_dec (cA m one x) z 
        then (cA_1 m one y) 
        else (cA_1 m one z).
Proof.
unfold crackv in |- *.
intros.
rewrite MA1.cA_1_Split in |- *.
 assert (Md1.kd = one).
   tauto.
 rewrite H4 in |- *.
   rewrite cA_cA_1 in |- *.
  elim (eq_dart_dec (cA m one x) z).
   elim (eq_dart_dec y z).
    intros.
      unfold MA1.crack in H.
       absurd (x = cA_1 m one y).
      tauto.
    rewrite a in |- *.
      rewrite <- a0 in |- *.
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
Qed.

Lemma exd_Split1_x_y_1 : forall(m:fmap)(x y z:dart), 
  inv_hmap m -> 
   (exd m z <-> exd (Split m one x (cA_1 m one y)) z).
Proof.
intros.
generalize (exd_Split m one x (cA_1 m one y) z).
 tauto.
Qed.

Lemma ndN_Split1_x_y_1 : forall (m:fmap)(x y:dart),
  ndN (Split m one x (cA_1 m one y)) = ndN m.
Proof. intros. apply ndN_Split. Qed.

Module ModSplit1cA1<:SigTr
 with Definition Tr:= fun(m:fmap)(x y:dart)=> 
    Split m one x (cA_1 m one y)
 with Definition Prec_Tr:= fun(m:fmap)(x y:dart)=> 
    crackv m x (cA_1 m one y).
Module M:= ModcA1.M.
Definition Tr:= fun(m:fmap)(x y:dart)=> 
  Split m one x (cA_1 m one y).
Definition Prec_Tr(m:fmap)(x y:dart):= 
  crackv m x (cA_1 m one y).
Definition f_Tr:= cA_Split1_x_y_1.
Definition f_1_Tr:= cA_1_Split1_x_y_1.
Definition exd_Tr:= exd_Split1_x_y_1.
Definition ndN_Tr:= ndN_Split1_x_y_1.
End ModSplit1cA1.

Module MA1TrSplit1:= MTr ModSplit1cA1.

(*===================================================
                 CONSEQUENCES: 
                expe_Split0, expv_Split1
====================================================*)

(* DIMENSION 0: *)

Lemma MA0TrSplit0_expo_expe: 
   MA0TrSplit0.MfM.expo = expe.
Proof. tauto. Qed.

(* IT WORKS, BUT IT IS A BIT COMPLEX: *)

Lemma MA0TrSplit0_expo_dec_expe_dec: 
 forall(m:fmap)(x y:dart)(H:inv_hmap m)(A B:Prop),
  (if MA0TrSplit0.MfM.expo_dec m x y H then A 
   else B) <->
  (if expe_dec m x y H then A else B).
Proof. 
intros.
elim (MA0TrSplit0.MfM.expo_dec m x y H).
 elim (expe_dec m x y H).
   tauto.
  tauto.
elim (expe_dec m x y H).
  tauto.
 tauto.
Qed.

(* OK: *)

Lemma MA0TrSplit0_between_betweene: 
  MA0TrSplit0.MfM.between = betweene.
Proof. tauto. Qed.

(* OK: *)

Lemma MA0TrSplit0_Prec_Tr_cracke: forall(m:fmap)(x y:dart),
  ModSplit0cA0.Prec_Tr m x y = 
     cracke m x (cA_1 m zero y).
Proof. tauto. Qed.

(* FROM WHERE: *)

Lemma expe_Split0_x_y_0_CNS: 
  forall (m : fmap) (x y z t : dart) (H : inv_hmap m),
   ModSplit0cA0.Prec_Tr m x y -> 
       let x1 := cA m zero x in
       let y_1 := cA_1 m zero y in
       let m1 := Split m zero x (cA_1 m zero y) in
     exd m z ->
       (expe m1 z t <->
        (if expe_dec m x y H
         then
          betweene m y z x /\ betweene m y t x \/
          betweene m x1 z y_1 /\ betweene m x1 t y_1 \/
          ~ expe m x z /\ expe m z t
         else
          expe m z t \/
          expe m x z /\ expe m y t \/
          expe m x t /\ expe m y z)).
Proof.
intros.
assert (cracke m x (cA_1 m zero y)).
 rewrite <- MA0TrSplit0_Prec_Tr_cracke in |- *.
    tauto.
unfold cracke in H2.
  unfold MA0.crack in H2.
  unfold MA0.MfcA.expo in H2.
  decompose [and] H2.
  elim H6; clear H6.
  intros i Hi.
  assert (exd m (Iter (MA0.MfcA.f m) i x)).
 generalize (MA0.MfcA.exd_Iter_f m i x).
    tauto.
generalize (exd_cA_1 m zero y).
  rewrite <- Hi in |- *.
  intro.
  assert (exd m y).
  tauto.
rewrite <- MA0TrSplit0_between_betweene in |- *.
  rewrite <- MA0TrSplit0_expo_expe in |- *.
  set
   (a0 :=
    MA0TrSplit0.MfM.between m y z x /\
         MA0TrSplit0.MfM.between m y t x \/
    MA0TrSplit0.MfM.between m x1 z y_1 /\
         MA0TrSplit0.MfM.between m x1 t y_1 \/
    ~ MA0TrSplit0.MfM.expo m x z /\
        MA0TrSplit0.MfM.expo m z t)
   in |- *.
  set
   (b0 :=
    MA0TrSplit0.MfM.expo m z t \/
    MA0TrSplit0.MfM.expo m x z /\ 
      MA0TrSplit0.MfM.expo m y t \/
    MA0TrSplit0.MfM.expo m x t /\ 
      MA0TrSplit0.MfM.expo m y z)
   in |- *.
  cut
   (MA0TrSplit0.MfM.expo m1 z t <->
    (if MA0TrSplit0.MfM.expo_dec m x y H then a0 
     else b0)).
 generalize 
(MA0TrSplit0_expo_dec_expe_dec m x y H a0 b0).
    tauto.
unfold a0 in |- *; unfold b0 in |- *.
  assert (x1 = MA0TrSplit0.MfM.f m x).
  tauto.
assert (y_1 = MA0TrSplit0.MfM.f_1 m y).
  tauto.
assert (m1 = ModSplit0cA0.Tr m x y).
  tauto.
rewrite H9 in |- *.
  rewrite H10 in |- *.
  rewrite H8 in |- *.
  apply MA0TrSplit0.expo_Tr_CNS.
  tauto.
 tauto.
 tauto.
 tauto.
rewrite <- H10 in |- *.
  unfold m1 in |- *.
  apply inv_hmap_Split.
   tauto.
Qed.

(* USUAL FORM: *)

Theorem expe_Split0_CNS_aux: 
  forall (m :fmap)(X Y z t: dart)(H:inv_hmap m),
     cracke m X Y -> exd m z ->
       let X0 := cA m zero X in
       let m1 := Split m zero X Y in
       let Y0 := cA m zero Y in
     (expe m1 z t <->
        (if expe_dec m X Y0 H
         then
          betweene m Y0 z X /\ betweene m Y0 t X \/
          betweene m X0 z Y /\ betweene m X0 t Y \/
          ~ expe m X z /\ expe m z t
         else
          expe m z t \/
          expe m X z /\ expe m Y0 t \/
          expe m X t /\ expe m Y0 z)).
Proof.
intros.
assert (exd m X).
 unfold cracke in H0.
   unfold MA0.crack in H0.
   unfold MA0.MfcA.expo in H0.
    tauto.
set (x := X) in |- *.
  set (y := Y0) in |- *.
  set (x1 := cA m zero x) in |- *.
  set (y_1 := cA_1 m zero y) in |- *.
  unfold X0 in |- *.
  fold x in |- *.
  fold x1 in |- *.
  assert (Y = y_1).
 unfold y_1 in |- *.
   unfold y in |- *.
   unfold Y0 in |- *.
   rewrite cA_1_cA in |- *.
   tauto.
  tauto.
 unfold cracke in H0.
   unfold MA0.crack in H0.
   generalize (MA0.MfcA.expo_exd m X Y).
    tauto.
rewrite H3 in |- *.
  unfold m1 in |- *.
  fold x in |- *.
  rewrite H3 in |- *.
  unfold y_1 in |- *.
  unfold x1 in |- *.
  apply expe_Split0_x_y_0_CNS.
 rewrite MA0TrSplit0_Prec_Tr_cracke in |- *.
   fold y_1 in |- *.
   rewrite <- H3 in |- *.
   unfold x in |- *.
    tauto.
 tauto.
Qed.

(* BETTER SIMPLIFIED FORM: *)

Theorem expe_Split0_CNS: 
  forall (m :fmap)(X Y z t: dart)(H:inv_hmap m),
     cracke m X Y -> exd m z ->
       let X0 := cA m zero X in
       let m1 := Split m zero X Y in
       let Y0 := cA m zero Y in
     expe m1 z t <->
        ( betweene m Y0 z X /\ betweene m Y0 t X \/
          betweene m X0 z Y /\ betweene m X0 t Y \/
          ~ expe m X z /\ expe m z t ).
Proof.
intros.
generalize (expe_Split0_CNS_aux m X Y z t H H0 H1).
simpl in |- *.
fold m1 in |- *.
fold X0 in |- *; fold Y0 in |- *.
elim (expe_dec m X Y0 H).
  tauto.
intro.
  elim b.
  unfold cracke in H0.
  unfold MA0.crack in H0.
  clear b.
  apply MA0.MfcA.expo_trans with Y.
  tauto.
unfold MA0.MfcA.expo in |- *.
  split.
 generalize (MA0.MfcA.expo_exd m X Y).
    tauto.
split with 1.
  simpl in |- *.
  unfold Y0 in |- *.
   tauto.
Qed.

(* OK: *)

Lemma Iter_cA0_MA0TrSplit0_f: 
   forall (m : fmap) (x : dart) (j : nat),
       Iter (cA m zero) j x = 
          Iter (MA0TrSplit0.MfM.f m) j x.
Proof.
intros.
induction j.
 simpl in |- *.
    tauto.
simpl in |- *; rewrite IHj in |- *.
   tauto.
Qed.

(* OK: *)

Lemma Iter_cA1_MA1TrSplit1_f: 
   forall (m : fmap) (x : dart) (j : nat),
       Iter (cA m one) j x = 
          Iter (MA1TrSplit1.MfM.f m) j x.
Proof.
intros.
induction j.
 simpl in |- *.
    tauto.
simpl in |- *; rewrite IHj in |- *.
   tauto.
Qed.

(* OK: *)

Theorem degreee_Split0_summary: 
 forall (m : fmap) (X X' Z : dart)(j : nat)
        (H: inv_hmap m),
   let Y := cA m zero X in
   let Y':= cA m zero X' in
   let m1 := Split m zero X X' in
   let dY' := degreee m Y' in
    cracke m X X' ->
      exd m Z ->
       Y' = Iter (cA m zero) j X ->
         2 <= j <= dY' ->
     degreee m Z =
        if expe_dec m Y' Z H
        then degreee m1 Y' + degreee m1 Y
        else degreee m1 Z.
Proof.
intros.
set (x := X) in |- *.
set (y := Y') in |- *.
generalize H0.
intro.
unfold cracke in H4.
unfold MA0.crack in H4.
elim H4.
clear H4.
intros.
assert (exd m X).
 unfold MA0.MfcA.expo in H5.
    tauto.
assert (exd m X').
 generalize (MA0.MfcA.expo_exd m X X').
    tauto.
assert (ModSplit0cA0.Prec_Tr m x y).
 unfold x in |- *.
   unfold y in |- *.
   unfold cracke in H0.
   unfold ModSplit0cA0.Prec_Tr in |- *.
   unfold Y' in |- *.
   rewrite cA_1_cA in |- *.
   tauto.
  tauto.
  tauto.
assert (m1 = ModSplit0cA0.Tr m x y).
 unfold ModSplit0cA0.Tr in |- *.
   unfold y in |- *.
   unfold Y' in |- *.
   rewrite cA_1_cA in |- *.
  unfold x in |- *.
     tauto.
  tauto.
  tauto.
assert (inv_hmap m1).
 unfold m1 in |- *.
   apply inv_hmap_Split.
    tauto.
assert (degreee = MA0TrSplit0.MfM.degree).
  tauto.
set (x1 := cA m zero x) in |- *.
  assert (x1 = MA0TrSplit0.MfM.f m x).
 unfold x1 in |- *.
    tauto.
assert (y = Iter (MA0TrSplit0.MfM.f m) j x).
 rewrite <- Iter_cA0_MA0TrSplit0_f in |- *.
   unfold x in |- *.
   unfold y in |- *.
    tauto.
rewrite H11 in |- *.
  rewrite 
(MA0TrSplit0.degree_Tr_split_summary m x y Z j H) in |- *.
 rewrite <- H11 in |- *.
   rewrite <- H9 in |- *.
   rewrite <- H12 in |- *.
   unfold Y in |- *.
   fold x in |- *.
   fold x1 in |- *.
   elim (MA0TrSplit0.MfM.expo_dec m y Z H).
  elim (expe_dec m y Z H).
    tauto.
   tauto.
 elim (expe_dec m y Z H).
   tauto.
  tauto.
 tauto.
unfold x in |- *.
   tauto.
unfold y in |- *.
  unfold Y' in |- *.
  generalize (exd_cA m zero X').
   tauto.
 tauto.
 tauto.
unfold y in |- *.
  unfold dY' in H3.
   tauto.
rewrite <- H9 in |- *.
   tauto.
Qed.

(* degreee_Split0: BIS: OK *)

Theorem degreee_Split0_summary_bis: 
 forall (m : fmap) (X X' Z : dart)(j : nat)
        (H: inv_hmap m),
   let Y := cA m zero X in
   let Y':= cA m zero X' in
   let m1 := Split m zero X X' in
   let dY' := degreee m Y' in
   cracke m X X' ->
      exd m Z ->
       Y' = Iter (cA m zero) j X ->
         2 <= j <= dY' ->
    (betweene m Y' Z X ->  
        degreee m1 Z = dY' - j + 1) /\
    (betweene m Y Z X' ->
        degreee m1 Z = j - 1) /\
    (~ expe m X Z -> 
        degreee m1 Z = degreee m Z).
Proof.
intros.
set (x := X) in |- *.
set (y := Y') in |- *.
generalize H0.
intro.
unfold cracke in H4.
unfold MA0.crack in H4.
elim H4.
clear H4.
intros.
assert (exd m X).
 unfold MA0.MfcA.expo in H5.
    tauto.
assert (exd m X').
 generalize (MA0.MfcA.expo_exd m X X').
    tauto.
assert (ModSplit0cA0.Prec_Tr m x y).
 unfold x in |- *.
   unfold y in |- *.
   unfold cracke in H0.
   unfold ModSplit0cA0.Prec_Tr in |- *.
   unfold Y' in |- *.
   rewrite cA_1_cA in |- *.
   tauto.
  tauto.
  tauto.
assert (m1 = ModSplit0cA0.Tr m x y).
 unfold ModSplit0cA0.Tr in |- *.
   unfold y in |- *.
   unfold Y' in |- *.
   rewrite cA_1_cA in |- *.
  unfold x in |- *.
     tauto.
  tauto.
  tauto.
assert (inv_hmap m1).
 unfold m1 in |- *.
   apply inv_hmap_Split.
    tauto.
assert (degreee = MA0TrSplit0.MfM.degree).
  tauto.
set (x1 := cA m zero x) in |- *.
  assert (x1 = MA0TrSplit0.MfM.f m x).
 unfold x1 in |- *.
    tauto.
assert (y = Iter (MA0TrSplit0.MfM.f m) j x).
 rewrite <- Iter_cA0_MA0TrSplit0_f in |- *.
   unfold x in |- *.
   unfold y in |- *.
    tauto.
rewrite H11 in |- *.
  assert (betweene = MA0TrSplit0.MfM.between).
  tauto.
assert (expe = MA0TrSplit0.MfM.expo).
  tauto.
rewrite H14 in |- *; rewrite H15 in |- *.
  unfold Y in |- *.
  fold x in |- *.
  fold x1 in |- *.
  rewrite H12 in |- *.
  unfold dY' in |- *.
  fold y in |- *.
  rewrite H11 in |- *.
  assert (X' = MA0TrSplit0.MfM.f_1 m y).
 unfold y in |- *.
   unfold Y' in |- *.
   assert 
(MA0TrSplit0.MfM.f_1 m (cA m zero X') = cA_1 m zero (cA m zero X')).
   tauto.
 rewrite H16 in |- *.
   rewrite cA_1_cA in |- *.
   tauto.
  tauto.
  tauto.
rewrite H16 in |- *.
  rewrite H9 in |- *.
  apply 
(MA0TrSplit0.degree_Tr_split_summary_bis m x y Z j H H8).
 unfold x in |- *.
    tauto.
unfold y in |- *.
  unfold Y' in |- *.
  generalize (exd_cA m zero X').
   tauto.
 tauto.
 tauto.
unfold y in |- *.
  rewrite <- H11 in |- *.
  fold dY' in |- *.
   tauto.
rewrite <- H9 in |- *.
   tauto.
Qed.

Lemma Iter_cA0_Split1_ter:
 forall(m:fmap)(x x' z:dart)(i:nat),
   inv_hmap m ->
     Iter (cA (Split m one x x') zero) i z =
        Iter (cA m zero) i z. 
Proof.
intros.
assert (zero = dim_opp one).
 simpl in |- *;  tauto.
rewrite H0 in |- *.
  induction i.
 simpl in |- *.
    tauto.
simpl in |- *.
  rewrite H0 in |- *.
  rewrite IHi in |- *.
  rewrite MA1.cA_Split_opp in |- *.
  tauto.
tauto.
Qed.

Lemma Iter_cA1_Split0_ter:
 forall(m:fmap)(x x' z:dart)(i:nat),
   inv_hmap m ->
     Iter (cA (Split m zero x x') one) i z =
        Iter (cA m one) i z. 
Proof.
intros.
assert (one = dim_opp zero).
 simpl in |- *;  tauto.
rewrite H0 in |- *.
  induction i.
 simpl in |- *.
    tauto.
simpl in |- *.
  rewrite H0 in |- *.
  rewrite IHi in |- *.
  rewrite MA0.cA_Split_opp in |- *.
  tauto.
tauto.
Qed.

(* OK: *)

Lemma degreev_Split0_summary_aux: 
  forall (m : fmap) (X X' Z : dart)(n:nat),
   inv_hmap m -> exd m Z -> n <= ndN m ->
 MA1Tr.MfM.degree_aux 
    (Split m zero X X') Z (ndN m - n) =
        MA1Tr.MfM.degree_aux m Z (ndN m - n).
Proof.
intros.
induction n.
 assert (ndN m - 0 = ndN m).
   lia.
 rewrite H2 in |- *.
   rewrite MA1Tr.MfM.degree_aux_equation in |- *.
   rewrite
 (MA1Tr.MfM.degree_aux_equation m Z (ndN m)) in |- *.
   rewrite ndN_Split in |- *.
   rewrite <- Iter_cA1_MA1TrSplit1_f in |- *.
   rewrite Iter_cA1_Split0_ter in |- *.
  elim (Arith.Compare_dec.le_lt_dec (ndN m) (ndN m)).
   elim (Nat.eq_dec (ndN m) (ndN m)).
    elim (eq_dart_dec Z (Iter (cA m one) (ndN m) Z)).
     elim (eq_dart_dec Z 
    (Iter (MA1Tr.MfM.f m) (ndN m) Z)).
       tauto.
     rewrite Iter_cA1_MA1TrSplit1_f in |- *.
        tauto.
    elim (eq_dart_dec Z
      (Iter (MA1Tr.MfM.f m) (ndN m) Z)).
     rewrite Iter_cA1_MA1TrSplit1_f in |- *.
        tauto.
     tauto.
    tauto.
   tauto.
  tauto.
rewrite MA1Tr.MfM.degree_aux_equation in |- *.
  rewrite ndN_Split in |- *.
  assert (ndN m - S n + 1 = ndN m - n).
  lia.
rewrite H2 in |- *.
  rewrite <- Iter_cA1_MA1TrSplit1_f in |- *.
  rewrite Iter_cA1_Split0_ter in |- *.
 rewrite 
 (MA1Tr.MfM.degree_aux_equation m Z (ndN m - S n)) 
    in |- *.
   rewrite H2 in |- *.
   elim (Arith.Compare_dec.le_lt_dec (ndN m - S n) (ndN m)).
  elim (eq_dart_dec Z
 (Iter (cA m one) (ndN m - S n) Z)).
   elim (eq_dart_dec Z 
 (Iter (MA1Tr.MfM.f m) (ndN m - S n) Z)).
     tauto.
   rewrite Iter_cA1_MA1TrSplit1_f in |- *.
      tauto.
  elim (eq_dart_dec Z 
   (Iter (MA1Tr.MfM.f m) (ndN m - S n) Z)).
   rewrite Iter_cA1_MA1TrSplit1_f in |- *.
      tauto.
  elim (Nat.eq_dec (ndN m - S n) (ndN m)).
    tauto.
  intros.
    apply IHn.
     lia.
  tauto.
 tauto.
Qed.

(* OK!!: *)

Theorem degreev_Split0_summary: 
  forall (m : fmap) (X X' Z : dart),
    inv_hmap m -> exd m Z ->
      degreev (Split m zero X X') Z = degreev m Z.
Proof.
intros.
unfold degreev in |- *.
unfold MA1Tr.MfM.degree in |- *.
assert (0 < ndN m).
 apply MA0.MfcA.ndN_pos with Z.
    tauto.
assert (1 = ndN m - (ndN m - 1)).
  lia.
rewrite H2 in |- *.
  apply 
 (degreev_Split0_summary_aux m X X' Z (ndN m - 1)).
  tauto.
 tauto.
lia.
Qed.

(* OK: *)

Theorem expv_Split0: forall (m : fmap)(x x' z t:dart),
   inv_hmap m -> 
     (expv (Split m zero x x') z t <-> expv m z t).
Proof.
intros.
unfold expv in |- *.
unfold MA1.MfcA.expo in |- *.
assert (exd m z <-> exd (Split m zero x x') z).
 generalize (exd_Split m zero x x' z).
    tauto.
cut
 ((exists i : nat, 
   Iter (MA1.MfcA.f (Split m zero x x')) i z = t) <->
  (exists i : nat, Iter (MA1.MfcA.f m) i z = t)).
  tauto.
split.
 intro.
   elim H1.
   clear H1.
   intros i Hi.
   split with i.
   rewrite <- Iter_cA1_MA1TrSplit1_f in Hi.
   rewrite Iter_cA1_Split0_ter in Hi.
  rewrite <- Iter_cA1_MA1TrSplit1_f in |- *.
     tauto.
  tauto.
intro.
  elim H1.
  clear H1.
  intros i Hi.
  split with i.
  rewrite <- Iter_cA1_MA1TrSplit1_f in |- *.
  rewrite Iter_cA1_Split0_ter in |- *.
 rewrite <- Iter_cA1_MA1TrSplit1_f in Hi.
    tauto.
 tauto.
Qed.

(* DIMENSION 1: *)

Lemma MA1TrSplit1_expo_expv: 
   MA1TrSplit1.MfM.expo = expv.
Proof. tauto. Qed.

(* IT WORKS, BUT IT IS A BIT COMPLEX: *)

Lemma MA1TrSplit1_expo_dec_expv_dec: 
 forall(m:fmap)(x y:dart)(H:inv_hmap m)(A B:Prop),
  (if MA1TrSplit1.MfM.expo_dec m x y H then A 
   else B) <->  
  (if expv_dec m x y H then A else B).
Proof. 
intros.
elim (MA1TrSplit1.MfM.expo_dec m x y H).
 elim (expv_dec m x y H).
   tauto.
  tauto.
elim (expv_dec m x y H).
  tauto.
 tauto.
Qed.

Lemma MA1TrSplit1_between_betweenv: 
  MA1TrSplit1.MfM.between = betweenv.
Proof. tauto. Qed.

Lemma MA1TrSplit1_Prec_Tr_crackv: forall(m:fmap)(x y:dart),
  ModSplit1cA1.Prec_Tr m x y = 
     crackv m x (cA_1 m one y).
Proof. tauto. Qed.

(* FROM WHERE, OK: *)

Lemma expv_Split1_x_y_1_CNS: 
  forall (m : fmap) (x y z t : dart) (H : inv_hmap m),
   ModSplit1cA1.Prec_Tr m x y -> 
       let x1 := cA m one x in
       let y_1 := cA_1 m one y in
       let m1 := Split m one x (cA_1 m one y) in
     exd m z ->
       (expv m1 z t <->
        (if expv_dec m x y H
         then
          betweenv m y z x /\ betweenv m y t x \/
          betweenv m x1 z y_1 /\ betweenv m x1 t y_1 \/
          ~ expv m x z /\ expv m z t
         else
          expv m z t \/
          expv m x z /\ expv m y t \/
          expv m x t /\ expv m y z)).
Proof.
intros.
assert (crackv m x (cA_1 m one y)).
 rewrite <- MA1TrSplit1_Prec_Tr_crackv in |- *.
    tauto.
unfold crackv in H2.
  unfold MA1.crack in H2.
  unfold MA1.MfcA.expo in H2.
  decompose [and] H2.
  elim H6; clear H6.
  intros i Hi.
  assert (exd m (Iter (MA1.MfcA.f m) i x)).
 generalize (MA1.MfcA.exd_Iter_f m i x).
    tauto.
generalize (exd_cA_1 m one y).
  rewrite <- Hi in |- *.
  intro.
  assert (exd m y).
  tauto.
rewrite <- MA1TrSplit1_between_betweenv in |- *.
  set
   (a0 :=
    MA1TrSplit1.MfM.between m y z x /\
      MA1TrSplit1.MfM.between m y t x \/
    MA1TrSplit1.MfM.between m x1 z y_1 /\
      MA1TrSplit1.MfM.between m x1 t y_1 \/
    ~ MA1TrSplit1.MfM.expo m x z /\
        MA1TrSplit1.MfM.expo m z t)
   in |- *.
  set
   (b0 :=
    MA1TrSplit1.MfM.expo m z t \/
    MA1TrSplit1.MfM.expo m x z /\ 
      MA1TrSplit1.MfM.expo m y t \/
    MA1TrSplit1.MfM.expo m x t /\ 
     MA1TrSplit1.MfM.expo m y z)
   in |- *.
  cut
   (MA1TrSplit1.MfM.expo m1 z t <->
    (if MA1TrSplit1.MfM.expo_dec m x y H then a0 
     else b0)).
 generalize
 (MA1TrSplit1_expo_dec_expv_dec m x y H a0 b0).
    tauto.
unfold a0 in |- *; unfold b0 in |- *.
  assert (x1 = MA1TrSplit1.MfM.f m x).
  tauto.
assert (y_1 = MA1TrSplit1.MfM.f_1 m y).
  tauto.
assert (m1 = ModSplit1cA1.Tr m x y).
  tauto.
rewrite H9 in |- *.
  rewrite H10 in |- *.
  rewrite H8 in |- *.
  apply MA1TrSplit1.expo_Tr_CNS.
  tauto.
 tauto.
 tauto.
 tauto.
rewrite <- H10 in |- *.
  unfold m1 in |- *.
  apply inv_hmap_Split.
   tauto.
Qed.

(* USUAL FORM: OK: *)

Lemma expv_Split1_CNS_aux: 
  forall (m :fmap)(X Y z t: dart)(H:inv_hmap m),
     crackv m X Y -> exd m z ->
       let X1 := cA m one X in
       let m1 := Split m one X Y in
       let Y1 := cA m one Y in
     (expv m1 z t <->
        (if expv_dec m X Y1 H
         then
          betweenv m Y1 z X /\ betweenv m Y1 t X \/
          betweenv m X1 z Y /\ betweenv m X1 t Y \/
          ~ expv m X z /\ expv m z t
         else
          expv m z t \/
          expv m X z /\ expv m Y1 t \/
          expv m X t /\ expv m Y1 z)).
Proof.
intros.
assert (exd m X).
 unfold crackv in H0.
   unfold MA1.crack in H0.
   unfold MA1.MfcA.expo in H0.
    tauto.
set (x := X) in |- *.
  set (y := Y1) in |- *.
  set (x1 := cA m one x) in |- *.
  set (y_1 := cA_1 m one y) in |- *.
  unfold X1 in |- *.
  fold x in |- *.
  fold x1 in |- *.
  assert (Y = y_1).
 unfold y_1 in |- *.
   unfold y in |- *.
   unfold Y1 in |- *.
   rewrite cA_1_cA in |- *.
   tauto.
  tauto.
 unfold crackv in H0.
   unfold MA1.crack in H0.
   generalize (MA1.MfcA.expo_exd m X Y).
    tauto.
rewrite H3 in |- *.
  unfold m1 in |- *.
  fold x in |- *.
  rewrite H3 in |- *.
  unfold y_1 in |- *.
  unfold x1 in |- *.
  apply expv_Split1_x_y_1_CNS.
 rewrite MA1TrSplit1_Prec_Tr_crackv in |- *.
   fold y_1 in |- *.
   rewrite <- H3 in |- *.
   unfold x in |- *.
   tauto.
 tauto.
Qed.

(* OK: *)

Theorem expv_Split1_CNS: 
  forall (m :fmap)(X Y z t: dart)(H:inv_hmap m),
     crackv m X Y -> exd m z ->
       let X1 := cA m one X in
       let m1 := Split m one X Y in
       let Y1 := cA m one Y in
     (expv m1 z t <->
        betweenv m Y1 z X /\ betweenv m Y1 t X \/
        betweenv m X1 z Y /\ betweenv m X1 t Y \/
        ~ expv m X z /\ expv m z t).
Proof.
intros.
generalize (expv_Split1_CNS_aux m X Y z t H H0 H1).
simpl in |- *.
fold m1 in |- *.
fold X1 in |- *; fold Y1 in |- *.
elim (expv_dec m X Y1 H).
  tauto.
intro.
  elim b.
  unfold crackv in H0.
  unfold MA1.crack in H0.
  clear b.
  apply MA1.MfcA.expo_trans with Y.
  tauto.
unfold MA1.MfcA.expo in |- *.
  split.
 generalize (MA1.MfcA.expo_exd m X Y).
    tauto.
split with 1.
  simpl in |- *.
  unfold Y1 in |- *.
   tauto.
Qed.

(* OK: *)

Theorem degreev_Split1_summary: 
 forall (m : fmap) (X X' Z : dart)(j : nat)
        (H: inv_hmap m),
   let Y := cA m one X in
   let Y':= cA m one X' in
   let m1 := Split m one X X' in
   let dY' := degreev m Y' in
    crackv m X X' ->
      exd m Z ->
       Y' = Iter (cA m one) j X ->
         2 <= j <= dY' ->
     degreev m Z =
        if expv_dec m Y' Z H
        then degreev m1 Y' + degreev m1 Y
        else degreev m1 Z.
Proof.
intros.
set (x := X) in |- *.
set (y := Y') in |- *.
generalize H0.
intro.
unfold crackv in H4.
unfold MA1.crack in H4.
elim H4.
clear H4.
intros.
assert (exd m X).
 unfold MA1.MfcA.expo in H5.
    tauto.
assert (exd m X').
 generalize (MA1.MfcA.expo_exd m X X').
    tauto.
assert (ModSplit1cA1.Prec_Tr m x y).
 unfold x in |- *.
   unfold y in |- *.
   unfold crackv in H0.
   unfold ModSplit1cA1.Prec_Tr in |- *.
   unfold Y' in |- *.
   rewrite cA_1_cA in |- *.
   tauto.
  tauto.
  tauto.
assert (m1 = ModSplit1cA1.Tr m x y).
 unfold ModSplit1cA1.Tr in |- *.
   unfold y in |- *.
   unfold Y' in |- *.
   rewrite cA_1_cA in |- *.
  unfold x in |- *.
     tauto.
  tauto.
  tauto.
assert (inv_hmap m1).
 unfold m1 in |- *.
   apply inv_hmap_Split.
    tauto.
assert (degreev = MA1TrSplit1.MfM.degree).
  tauto.
set (x1 := cA m one x) in |- *.
  assert (x1 = MA1TrSplit1.MfM.f m x).
 unfold x1 in |- *.
    tauto.
assert (y = Iter (MA1TrSplit1.MfM.f m) j x).
 rewrite <- Iter_cA1_MA1TrSplit1_f in |- *.
   unfold x in |- *.
   unfold y in |- *.
    tauto.
rewrite H11 in |- *.
  rewrite 
(MA1TrSplit1.degree_Tr_split_summary m x y Z j H) in |- *.
 rewrite <- H11 in |- *.
   rewrite <- H9 in |- *.
   rewrite <- H12 in |- *.
   unfold Y in |- *.
   fold x in |- *.
   fold x1 in |- *.
   elim (MA1TrSplit1.MfM.expo_dec m y Z H).
  elim (expv_dec m y Z H).
    tauto.
   tauto.
 elim (expv_dec m y Z H).
   tauto.
  tauto.
 tauto.
unfold x in |- *.
   tauto.
unfold y in |- *.
  unfold Y' in |- *.
  generalize (exd_cA m one X').
   tauto.
 tauto.
 tauto.
unfold y in |- *.
  unfold dY' in H3.
   tauto.
rewrite <- H9 in |- *.
   tauto.
Qed.

(* degreee_Split1: BIS: OK *)

Theorem degreev_Split1_summary_bis: 
 forall (m : fmap) (X X' Z : dart)(j : nat)
        (H: inv_hmap m),
   let Y := cA m one X in
   let Y':= cA m one X' in
   let m1 := Split m one X X' in
   let dY' := degreev m Y' in
   crackv m X X' ->
      exd m Z ->
       Y' = Iter (cA m one) j X ->
         2 <= j <= dY' ->
    (betweenv m Y' Z X ->  
        degreev m1 Z = dY' - j + 1) /\
    (betweenv m Y Z X' ->
        degreev m1 Z = j - 1) /\
    (~ expv m X Z -> 
        degreev m1 Z = degreev m Z).
Proof.
intros.
set (x := X) in |- *.
set (y := Y') in |- *.
generalize H0.
intro.
unfold crackv in H4.
unfold MA1.crack in H4.
elim H4.
clear H4.
intros.
assert (exd m X).
 unfold MA1.MfcA.expo in H5.
    tauto.
assert (exd m X').
 generalize (MA1.MfcA.expo_exd m X X').
    tauto.
assert (ModSplit1cA1.Prec_Tr m x y).
 unfold x in |- *.
   unfold y in |- *.
   unfold crackv in H0.
   unfold ModSplit1cA1.Prec_Tr in |- *.
   unfold Y' in |- *.
   rewrite cA_1_cA in |- *.
   tauto.
  tauto.
  tauto.
assert (m1 = ModSplit1cA1.Tr m x y).
 unfold ModSplit1cA1.Tr in |- *.
   unfold y in |- *.
   unfold Y' in |- *.
   rewrite cA_1_cA in |- *.
  unfold x in |- *.
     tauto.
  tauto.
  tauto.
assert (inv_hmap m1).
 unfold m1 in |- *.
   apply inv_hmap_Split.
    tauto.
assert (degreev = MA1TrSplit1.MfM.degree).
  tauto.
set (x1 := cA m one x) in |- *.
  assert (x1 = MA1TrSplit1.MfM.f m x).
 unfold x1 in |- *.
    tauto.
assert (y = Iter (MA1TrSplit1.MfM.f m) j x).
 rewrite <- Iter_cA1_MA1TrSplit1_f in |- *.
   unfold x in |- *.
   unfold y in |- *.
    tauto.
rewrite H11 in |- *.
  assert (betweenv = MA1TrSplit1.MfM.between).
  tauto.
assert (expv = MA1TrSplit1.MfM.expo).
  tauto.
rewrite H14 in |- *; rewrite H15 in |- *.
  unfold Y in |- *.
  fold x in |- *.
  fold x1 in |- *.
  rewrite H12 in |- *.
  unfold dY' in |- *.
  fold y in |- *.
  rewrite H11 in |- *.
  assert (X' = MA1TrSplit1.MfM.f_1 m y).
 unfold y in |- *.
   unfold Y' in |- *.
   assert 
(MA1TrSplit1.MfM.f_1 m (cA m one X') = cA_1 m one (cA m one X')).
   tauto.
 rewrite H16 in |- *.
   rewrite cA_1_cA in |- *.
   tauto.
  tauto.
  tauto.
rewrite H16 in |- *.
  rewrite H9 in |- *.
  apply 
(MA1TrSplit1.degree_Tr_split_summary_bis m x y Z j H H8).
 unfold x in |- *.
    tauto.
unfold y in |- *.
  unfold Y' in |- *.
  generalize (exd_cA m one X').
   tauto.
 tauto.
 tauto.
unfold y in |- *.
  rewrite <- H11 in |- *.
  fold dY' in |- *.
   tauto.
rewrite <- H9 in |- *.
   tauto.
Qed.

(* OK: *)

Lemma degreee_Split1_summary_aux: 
  forall (m : fmap) (X X' Z : dart)(n:nat),
   inv_hmap m -> exd m Z -> n <= ndN m ->
 MA0Tr.MfM.degree_aux 
    (Split m one X X') Z (ndN m - n) =
        MA0Tr.MfM.degree_aux m Z (ndN m - n).
Proof.
intros.
induction n.
 assert (ndN m - 0 = ndN m).
   lia.
 rewrite H2 in |- *.
   rewrite MA0Tr.MfM.degree_aux_equation in |- *.
   rewrite
 (MA0Tr.MfM.degree_aux_equation m Z (ndN m)) in |- *.
   rewrite ndN_Split in |- *.
   rewrite <- Iter_cA0_MA0TrSplit0_f in |- *.
   rewrite Iter_cA0_Split1_ter in |- *.
  elim (Arith.Compare_dec.le_lt_dec (ndN m) (ndN m)).
   elim (Nat.eq_dec (ndN m) (ndN m)).
    elim (eq_dart_dec Z (Iter (cA m zero) (ndN m) Z)).
     elim (eq_dart_dec Z 
    (Iter (MA0Tr.MfM.f m) (ndN m) Z)).
       tauto.
     rewrite Iter_cA0_MA0TrSplit0_f in |- *.
        tauto.
    elim (eq_dart_dec Z
      (Iter (MA0Tr.MfM.f m) (ndN m) Z)).
     rewrite Iter_cA0_MA0TrSplit0_f in |- *.
        tauto.
     tauto.
    tauto.
   tauto.
  tauto.
rewrite MA0Tr.MfM.degree_aux_equation in |- *.
  rewrite ndN_Split in |- *.
  assert (ndN m - S n + 1 = ndN m - n).
  lia.
rewrite H2 in |- *.
  rewrite <- Iter_cA0_MA0TrSplit0_f in |- *.
  rewrite Iter_cA0_Split1_ter in |- *.
 rewrite 
 (MA0Tr.MfM.degree_aux_equation m Z (ndN m - S n)) 
    in |- *.
   rewrite H2 in |- *.
   elim (Arith.Compare_dec.le_lt_dec (ndN m - S n) (ndN m)).
  elim (eq_dart_dec Z
 (Iter (cA m zero) (ndN m - S n) Z)).
   elim (eq_dart_dec Z 
 (Iter (MA0Tr.MfM.f m) (ndN m - S n) Z)).
     tauto.
   rewrite Iter_cA0_MA0TrSplit0_f in |- *.
      tauto.
  elim (eq_dart_dec Z 
   (Iter (MA0Tr.MfM.f m) (ndN m - S n) Z)).
   rewrite Iter_cA0_MA0TrSplit0_f in |- *.
      tauto.
  elim (Nat.eq_dec (ndN m - S n) (ndN m)).
    tauto.
  intros.
    apply IHn.
     lia.
  tauto.
 tauto.
Qed.

(* OK: *)

Theorem degreee_Split1_summary: 
  forall (m : fmap) (X X' Z : dart),
    inv_hmap m -> exd m Z ->
      degreee (Split m one X X') Z = degreee m Z.
Proof.
intros.
unfold degreee in |- *.
unfold MA0Tr.MfM.degree in |- *.
assert (0 < ndN m).
 apply MA1.MfcA.ndN_pos with Z.
    tauto.
assert (1 = ndN m - (ndN m - 1)).
  lia.
rewrite H2 in |- *.
  apply 
 (degreee_Split1_summary_aux m X X' Z (ndN m - 1)).
  tauto.
 tauto.
lia.
Qed.

(* OK: *)

Theorem expe_Split1: forall (m : fmap)(x x' z t:dart),
   inv_hmap m -> 
     (expe (Split m one x x') z t <-> expe m z t).
Proof.
intros.
unfold expe in |- *.
unfold MA0.MfcA.expo in |- *.
assert (exd m z <-> exd (Split m one x x') z).
 generalize (exd_Split m one x x' z).
    tauto.
cut
 ((exists i : nat, 
   Iter (MA0.MfcA.f (Split m one x x')) i z = t) <->
  (exists i : nat, Iter (MA0.MfcA.f m) i z = t)).
  tauto.
split.
 intro.
   elim H1.
   clear H1.
   intros i Hi.
   split with i.
   rewrite <- Iter_cA0_MA0TrSplit0_f in Hi.
   rewrite Iter_cA0_Split1_ter in Hi.
  rewrite <- Iter_cA0_MA0TrSplit0_f in |- *.
     tauto.
  tauto.
intro.
  elim H1.
  clear H1.
  intros i Hi.
  split with i.
  rewrite <- Iter_cA0_MA0TrSplit0_f in |- *.
  rewrite Iter_cA0_Split1_ter in |- *.
 rewrite <- Iter_cA0_MA0TrSplit0_f in Hi.
    tauto.
 tauto.
Qed.

(*===================================================
 INSTANTIATION FOR FACES OF MTr FOR SPLITTING:
    Tr = Split 
      expof_Split0, expof_Split1, 
      degreef_Split0, degreef_Split1 
             (MERGE AND SPLIT)
====================================================*)

(* DIMENSION 0: *)

Lemma cF_Split0: forall(m:fmap)(x x' z:dart),
 inv_hmap m -> cracke m x x' -> exd m z ->
   cF (Split m zero x x') z = 
    if eq_dart_dec (cA m zero x) z then cA_1 m one x'
    else if eq_dart_dec (cA m zero x') z 
         then cA_1 m one x 
         else cF m z.
Proof.
unfold cracke in |- *.
intros.
unfold cF in |- *.
rewrite MA0.cA_1_Split in |- *.
 rewrite MA0.cA_1_Split_opp in |- *.
  assert (Md0.kd = zero).
    tauto.
  rewrite H2 in |- *.
    simpl in |- *.
    elim (eq_dart_dec (cA m zero x) z).
    tauto.
  elim (eq_dart_dec (cA m zero x') z).
    tauto.
   tauto.
  tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma cF_1_Split0:forall(m:fmap)(x x' z:dart),
 inv_hmap m -> cracke m x x' -> exd m z ->
   cF_1 (Split m zero x x') z = 
    if eq_dart_dec (cA_1 m one x') z then (cA m zero x)
    else if eq_dart_dec (cA_1 m one x) z
         then (cA m zero x') 
         else cF_1 m z.
Proof.
intros.
generalize (MA0.crack_exd m x x' H H0).
intro.
unfold cF_1 in |- *.
rewrite MA0.cA_Split in |- *.
 rewrite MA0.cA_Split_opp in |- *.
  assert (Md0.kd = zero).
    tauto.
  rewrite H3 in |- *.
    simpl in |- *.
    elim (eq_dart_dec x (cA m one z)).
   elim (eq_dart_dec (cA_1 m one x') z).
    intros.
      rewrite <- a in a0.
      rewrite cA_cA_1 in a0.
     unfold cracke in H0.
       unfold MA0.crack in H0.
        tauto.
     tauto.
     tauto.
   elim (eq_dart_dec (cA_1 m one x) z).
     tauto.
   intros.
     rewrite a in b.
     rewrite cA_1_cA in b.
     tauto.
    tauto.
    tauto.
  elim (eq_dart_dec (cA_1 m one x) z).
   intros.
     rewrite <- a in b.
     rewrite cA_cA_1 in b.
     tauto.
    tauto.
    tauto.
  elim (eq_dart_dec x' (cA m one z)).
   elim (eq_dart_dec (cA_1 m one x') z).
     tauto.
   intros.
     rewrite a in b.
     rewrite cA_1_cA in b.
     tauto.
    tauto.
    tauto.
  elim (eq_dart_dec (cA_1 m one x') z).
   intros.
     rewrite <- a in b.
     rewrite cA_cA_1 in b.
     tauto.
    tauto.
    tauto.
   tauto.
  tauto.
 tauto.
unfold cracke in H0.
   tauto.
Qed.

(* FROM WHERE: Tr m X Y = 
       Split m zero (cA_1 m zero X) (cA m one Y) *)

(* OK: *)

Lemma cF_Split0_x_0_y1: forall(m:fmap)(x y z:dart),
 cracke m (cA_1 m zero x) (cA m one y) ->
  inv_hmap m -> exd m x -> exd m y -> exd m z ->
    cF (Split m zero (cA_1 m zero x) (cA m one y)) z = 
      (if eq_dart_dec x z then y
       else if eq_dart_dec (cF_1 m y) z
            then cF m x else cF m z).
Proof.
intros.
rewrite cF_Split0 in |- *.
 rewrite cA_cA_1 in |- *.
  rewrite cA_1_cA in |- *.
   fold (cF_1 m y) in |- *.
     fold (cF m x) in |- *.
      tauto.
   tauto.
   tauto.
  tauto.
  tauto.
 tauto.
 tauto.
 tauto.
Qed.

Lemma cF_1_Split0_x_0_y1: forall(m:fmap)(x y z:dart),
 cracke m (cA_1 m zero x) (cA m one y) ->
  inv_hmap m -> exd m x -> exd m y -> exd m z ->
 cF_1 (Split m zero (cA_1 m zero x) (cA m one y)) z = 
      (if eq_dart_dec y z then x
       else if eq_dart_dec (cF m x) z
            then cF_1 m y else cF_1 m z).
Proof.
intros.
rewrite cF_1_Split0 in |- *.
 rewrite cA_1_cA in |- *.
  rewrite cA_cA_1 in |- *.
   fold (cF m x) in |- *.
     fold (cF_1 m y) in |- *.
      tauto.
   tauto.
   tauto.
  tauto.
  tauto.
 tauto.
 tauto.
 tauto.
Qed.

(* INSTANTIATION FOR DIM 0: Split0 AND cF: *)

Module ModSplit0cF<:SigTr
  with Definition Tr:= fun(m:fmap)(x y:dart)=> 
    Split m zero (cA_1 m zero x) (cA m one y)
  with Definition Prec_Tr:= fun(m:fmap)(x y:dart)=> 
    cracke m (cA_1 m zero x) (cA m one y).
Module M:= ModcF0.M.
Definition Tr(m:fmap)(x y:dart):= 
   Split m zero (cA_1 m zero x) (cA m one y).
Definition Prec_Tr(m:fmap)(x y:dart):= 
   cracke m (cA_1 m zero x) (cA m one y).
Definition f_Tr:= cF_Split0_x_0_y1.
Definition f_1_Tr:= cF_1_Split0_x_0_y1.
Definition exd_Tr(m:fmap)(x y z:dart):=
  exd_Split_bis m zero (cA_1 m zero x) (cA m one y) z.
Definition ndN_Tr(m:fmap)(x y:dart):= 
  ndN_Split m zero (cA_1 m zero x) (cA m one y).
End ModSplit0cF.

Module MFTrSplit0:= MTr ModSplit0cF.

(*OK: *)

Lemma MFTrSplit0_expo_expof: 
   MFTrSplit0.MfM.expo = expof.
Proof. tauto. Qed.

(* IT WORKS, BUT IT IS A BIT COMPLEX: *)

Lemma MFTrSplit0_expo_dec_expof_dec: 
 forall(m:fmap)(x y:dart)(H:inv_hmap m)(A B:Prop),
  (if MFTrSplit0.MfM.expo_dec m x y H then A else B)
 <->
  (if expof_dec m x y H then A else B).
Proof. 
intros.
elim (MFTrSplit0.MfM.expo_dec m x y H).
 elim (expof_dec m x y H).
   tauto.
  tauto.
elim (expof_dec m x y H).
  tauto.
 tauto.
Qed.

(* OK: *)

Lemma MFTrSplit0_between_betweenf: 
  MFTrSplit0.MfM.between = betweenf.
Proof. tauto. Qed.

(* OK: *)

Lemma MFTrSplit0_Prec_Tr_cracke: forall(m:fmap)(x y:dart),
  ModSplit0cF.Prec_Tr m x y = 
     cracke m (cA_1 m zero x) (cA m one y).
Proof. tauto. Qed.

(* FROM WHERE: *)

Lemma expof_Split0_x_0_y1_CNS: 
  forall(m : fmap) (x y z t : dart) (H : inv_hmap m),
 ModSplit0cF.Prec_Tr m x y ->
   let x_0:= cA_1 m zero x in
   let y1:= cA m one y in
   let x1:= cF m x in
   let y_1:= cF_1 m y in
   let m1 := Split m zero x_0 y1 in
 exd m z ->
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
assert (cracke m x_0 y1).
 unfold ModSplit0cF.Prec_Tr in H0.
   unfold x_0 in |- *; unfold y1 in |- *.
    tauto.
generalize (MA0.crack_exd m x_0 y1 H H2).
  intros.
  assert (exd m x).
 generalize (exd_cA_1 m zero x).
   fold x_0 in |- *.
    tauto.
assert (exd m y).
 generalize (exd_cA m one y).
   fold y1 in |- *.
    tauto.
set
 (A0 :=
  betweenf m y z x /\ betweenf m y t x \/
  betweenf m x1 z y_1 /\ betweenf m x1 t y_1 \/
  ~ expof m x z /\ expof m z t)
 in |- *.
  set
   (B0 := expof m z t \/ expof m x z /\ expof m y t \/
    expof m x t /\ expof m y z)
   in |- *.
  cut
   (MFTrSplit0.MfM.expo m1 z t <->
    (if MFTrSplit0.MfM.expo_dec m x y H then A0 
     else B0)).
 generalize 
 (MFTrSplit0_expo_dec_expof_dec m x y H A0 B0).
    tauto.
unfold A0 in |- *.
  unfold B0 in |- *.
  rewrite <- MFTrSplit0_between_betweenf in |- *.
  rewrite <- MFTrSplit0_expo_expof in |- *.
  assert (x1 = MFTrSplit0.MfM.f m x).
  tauto.
assert (y_1 = MFTrSplit0.MfM.f_1 m y).
  tauto.
assert (m1 = ModSplit0cF.Tr m x y).
  tauto.
rewrite H6 in |- *; rewrite H8 in |- *; rewrite H7 in |- *.
  apply MFTrSplit0.expo_Tr_CNS.
  tauto.
 tauto.
 tauto.
 tauto.
rewrite <- H8 in |- *.
  unfold m1 in |- *.
  apply inv_hmap_Split.
   tauto.
Qed.

(* USUAL FORM: OK!! *)

Theorem expof_Split0_CNS: 
  forall(m:fmap)(X Y z t:dart)(H:inv_hmap m),
    cracke m X Y -> exd m z ->
      let m1 := Split m zero X Y in
      let X0 := cA m zero X in
      let Y0 := cA m zero Y in
      let Y_1 := cA_1 m one Y in
      let X_1 := cA_1 m one X in 
 (expof m1 z t <->  
     (if expof_dec m X0 Y_1 H
      then
       betweenf m Y_1 z X0 /\ betweenf m Y_1 t X0 \/
       betweenf m X_1 z Y0 /\ betweenf m X_1 t Y0 \/
       ~ expof m X0 z /\ expof m z t
      else 
       expof m z t \/
       expof m X0 z /\ expof m Y_1 t \/
       expof m X0 t /\ expof m Y_1 z)).
Proof.
intros.
assert (exd m X).
 unfold cracke in H0.
   unfold MA0.crack in H0.
   unfold MA0.MfcA.expo in H0.
    tauto.
set (x := X0) in |- *.
  set (y := Y_1) in |- *.
  set (x1 := cF m x) in |- *.
  set (y_1 := cF_1 m y) in |- *.
  assert (X_1 = x1).
 unfold x1 in |- *.
   unfold x in |- *.
   unfold X0 in |- *.
   unfold cF in |- *.
   rewrite cA_1_cA in |- *.
  fold X_1 in |- *.
     tauto.
  tauto.
  tauto.
assert (Y0 = y_1).
 unfold y_1 in |- *.
   unfold y in |- *.
   unfold Y_1 in |- *; unfold cF in |- *.
   unfold cF_1 in |- *.
   rewrite cA_cA_1 in |- *.
  fold Y0 in |- *.
     tauto.
  tauto.
 unfold cracke in H0.
   generalize (MA0.crack_exd m X Y).
    tauto.
rewrite H3 in |- *.
  rewrite H4 in |- *.
  assert 
 (m1 = Split m zero (cA_1 m zero x) (cA m one y)).
 unfold m1 in |- *.
   assert (X = cA_1 m zero x).
  unfold x in |- *.
    unfold X0 in |- *.
    rewrite cA_1_cA in |- *.
    tauto.
   tauto.
   tauto.
 assert (Y = cA m one y).
  unfold y in |- *.
    unfold Y_1 in |- *.
    rewrite cA_cA_1 in |- *.
    tauto.
   tauto.
  generalize (MA0.crack_exd m X Y).
     tauto.
 rewrite H5 in |- *; rewrite H6 in |- *.
    tauto.
rewrite H5 in |- *.
  unfold x1 in |- *.
  unfold y_1 in |- *.
  apply expof_Split0_x_0_y1_CNS.
 unfold ModSplit0cF.Prec_Tr in |- *.
   unfold x in |- *.
   unfold y in |- *.
   unfold X0 in |- *.
   rewrite cA_1_cA in |- *.
  unfold Y_1 in |- *.
    rewrite cA_cA_1 in |- *.
    tauto.
   tauto.
  unfold cracke in H0.
    generalize (MA0.crack_exd m X Y).
     tauto.
  tauto.
  tauto.
 tauto.
Qed.

(* FACE DEGREES, MERGE: *)

Theorem degreef_Split0_merge_summary:
 forall(m : fmap)(X Y Z : dart)(H : inv_hmap m),
     cracke m X Y -> exd m Z ->
       let m1 := Split m zero X Y in
       let X0 := cA m zero X in
       let Y_1 := cA_1 m one Y in 
       let dX0 := degreef m X0 in
       let dY_1 := degreef m Y_1 in
    ~ expof m X0 Y_1 ->
      degreef m1 Z =
        (if expof_dec m X0 Z H
         then dX0 + dY_1
         else
            if expof_dec m Y_1 Z H
            then dX0 + dY_1
            else degreef m Z).
Proof.
intros.
assert (inv_hmap m1).
 unfold m1 in |- *.
   apply inv_hmap_Split.
    tauto.
generalize (MA0.crack_exd m X Y H).
  intro.
  assert (exd m X /\ exd m Y).
 apply H4.
   unfold cracke in H0.
    tauto.
clear H4.
  assert (m1 = ModSplit0cF.Tr m X0 Y_1).
 unfold m1 in |- *.
   unfold ModSplit0cF.Tr in |- *.
   unfold X0 in |- *.
   unfold Y_1 in |- *.
   rewrite cA_1_cA in |- *.
  rewrite cA_cA_1 in |- *.
    tauto.
   tauto.
   tauto.
  tauto.
  tauto.
assert (ModSplit0cF.Prec_Tr m X0 Y_1).
 unfold ModSplit0cF.Prec_Tr in |- *.
   unfold X0 in |- *.
   unfold Y_1 in |- *.
   rewrite cA_1_cA in |- *.
  rewrite cA_cA_1 in |- *.
    tauto.
   tauto.
   tauto.
  tauto.
  tauto.
assert (exd m X0).
 unfold X0 in |- *.
   generalize (exd_cA m zero X).
    tauto.
assert (exd m Y_1).
 unfold Y_1 in |- *.
   generalize (exd_cA_1 m one Y).
    tauto.
assert (~ MFTrSplit0.MfM.expo m X0 Y_1).
 unfold expof in H2.
    tauto.
assert (degreef = MFTrSplit0.MfM.degree).
  tauto.
rewrite H10 in |- *.
  rewrite H4 in H3.
  generalize (MFTrSplit0.degree_Tr_merge_summary
       m X0 Y_1 Z H H6 H7 H8 H1 H3 H9).
  rewrite <- H4 in |- *.
  rewrite <- H10 in |- *.
  fold dX0 in |- *.
  fold dY_1 in |- *.
  elim (MFTrSplit0.MfM.expo_dec m X0 Z H).
 elim (expof_dec m X0 Z H).
   tauto.
 unfold expof in |- *.
    tauto.
elim (expof_dec m X0 Z H).
 unfold expof in |- *.
    tauto.
elim (MFTrSplit0.MfM.expo_dec m Y_1 Z H).
 elim (expof_dec m Y_1 Z H).
   tauto.
  tauto.
elim (expof_dec m Y_1 Z H).
  tauto.
 tauto.
Qed.

(* FACE DEGREES, SPLIT: *)

Theorem degreef_Split0_split_summary:
  forall(m : fmap)(X Y Z : dart)(j : nat) 
        (H : inv_hmap m),
     cracke m X Y -> exd m Z ->
       let m1 := Split m zero X Y in
       let X0 := cA m zero X in
       let X_1 := cA_1 m one X in
       let Y_1 := cA_1 m one Y in 
       let dY_1 := degreef m Y_1 in
       Y_1 = Iter (cF m) j X0 ->
       2 <= j <= dY_1 ->
     degreef m Z =
       (if expof_dec m Y_1 Z H
        then degreef m1 Y_1 + degreef m1 X_1
        else degreef m1 Z).
Proof.
intros.
assert (inv_hmap m1).
 unfold m1 in |- *.
   apply inv_hmap_Split.
    tauto.
generalize (MA0.crack_exd m X Y H).
  intro.
  assert (exd m X /\ exd m Y).
 apply H5.
   unfold cracke in H0.
    tauto.
clear H5.
  assert (m1 = ModSplit0cF.Tr m X0 Y_1).
 unfold m1 in |- *.
   unfold ModSplit0cF.Tr in |- *.
   unfold X0 in |- *.
   unfold Y_1 in |- *.
   rewrite cA_1_cA in |- *.
  rewrite cA_cA_1 in |- *.
    tauto.
   tauto.
   tauto.
  tauto.
  tauto.
assert (ModSplit0cF.Prec_Tr m X0 Y_1).
 unfold ModSplit0cF.Prec_Tr in |- *.
   unfold X0 in |- *.
   unfold Y_1 in |- *.
   rewrite cA_1_cA in |- *.
  rewrite cA_cA_1 in |- *.
    tauto.
   tauto.
   tauto.
  tauto.
  tauto.
assert (exd m X0).
 unfold X0 in |- *.
   generalize (exd_cA m zero X).
    tauto.
assert (exd m Y_1).
 unfold Y_1 in |- *.
   generalize (exd_cA_1 m one Y).
    tauto.
assert (cF = MFTrSplit0.MfM.f).
  tauto.
rewrite H10 in H2.
  assert (degreef = MFTrSplit0.MfM.degree).
  tauto.
rewrite H11 in |- *.
  rewrite H5 in H4.
  generalize
   (MFTrSplit0.degree_Tr_split_summary
      m X0 Y_1 Z j H H7 H8 H9 H1 H2 H3 H4).
  rewrite <- H11 in |- *.
  rewrite <- H5 in |- *.
  rewrite <- H10 in |- *.
  unfold X0 in |- *.
  unfold cF in |- *.
  rewrite cA_1_cA in |- *.
 fold X_1 in |- *.
   elim (MFTrSplit0.MfM.expo_dec m Y_1 Z H).
  elim (expof_dec m Y_1 Z H).
    tauto.
   tauto.
 elim (expof_dec m Y_1 Z H).
   tauto.
  tauto.
 tauto.
 tauto.
Qed.
 
(* FACE DEGREES, SPLIT, BIS: OK: *)

Theorem degreef_Split0_split_summary_bis:
  forall(m : fmap)(X Y Z : dart)(j : nat) 
        (H : inv_hmap m),
    cracke m X Y -> exd m Z ->
       let m1 := Split m zero X Y in
       let X0 := cA m zero X in
       let X_1 := cA_1 m one X in
       let Y_1 := cA_1 m one Y in
       let Y0 := cA m zero Y in 
       let dY_1 := degreef m Y_1 in
       Y_1 = Iter (cF m) j X0 ->
       2 <= j <= dY_1 ->
    (betweenf m Y_1 Z X0 ->  
        degreef m1 Z = dY_1 - j + 1) /\
    (betweenf m X_1 Z Y0 ->
        degreef m1 Z = j - 1) /\
    (~ expof m X0 Z -> 
        degreef m1 Z = degreef m Z).
Proof.
intros.
assert (inv_hmap m1).
 unfold m1 in |- *.
   apply inv_hmap_Split.
    tauto.
generalize (MA0.crack_exd m X Y H).
  intro.
  assert (exd m X /\ exd m Y).
 apply H5.
   unfold cracke in H0.
    tauto.
clear H5.
  assert (m1 = ModSplit0cF.Tr m X0 Y_1).
 unfold m1 in |- *.
   unfold ModSplit0cF.Tr in |- *.
   unfold X0 in |- *.
   unfold Y_1 in |- *.
   rewrite cA_1_cA in |- *.
  rewrite cA_cA_1 in |- *.
    tauto.
   tauto.
   tauto.
  tauto.
  tauto.
assert (ModSplit0cF.Prec_Tr m X0 Y_1).
 unfold ModSplit0cF.Prec_Tr in |- *.
   unfold X0 in |- *.
   unfold Y_1 in |- *.
   rewrite cA_1_cA in |- *.
  rewrite cA_cA_1 in |- *.
    tauto.
   tauto.
   tauto.
  tauto.
  tauto.
assert (exd m X0).
 unfold X0 in |- *.
   generalize (exd_cA m zero X).
    tauto.
assert (exd m Y_1).
 unfold Y_1 in |- *.
   generalize (exd_cA_1 m one Y).
    tauto.
assert (cF = MFTrSplit0.MfM.f).
  tauto.
rewrite H10 in H2.
  assert (degreef = MFTrSplit0.MfM.degree).
  tauto.
rewrite H11 in |- *.
  rewrite H5 in H4.
  assert (betweenf = MFTrSplit0.MfM.between).
  tauto.
assert (expof = MFTrSplit0.MfM.expo).
  tauto.
rewrite H12 in |- *.
  rewrite H13 in |- *.
  rewrite H5 in |- *.
  generalize
   (MFTrSplit0.degree_Tr_split_summary_bis
  m X0 Y_1 Z j H H7 H8 H9 H1 H2 H3 H4).
rewrite <- H5 in |- *.
  rewrite <- H11 in |- *.
  fold dY_1 in |- *.
  rewrite <- H12 in |- *.
  rewrite <- H13 in |- *.
 assert (cF = MFTrSplit0.MfM.f).
  tauto.
rewrite <- H14 in |- *.
  assert (cF_1 = MFTrSplit0.MfM.f_1).
  tauto.
rewrite <- H15 in |- *.
  assert (cF m X0 = X_1).
 unfold X_1 in |- *.
   unfold X0 in |- *.
   unfold cF in |- *.
   rewrite cA_1_cA in |- *.
   tauto.
  tauto.
  tauto.
assert (cF_1 m Y_1 = Y0).
 unfold Y_1 in |- *.
   unfold Y0 in |- *.
   unfold cF_1 in |- *.
   rewrite cA_cA_1 in |- *.
   tauto.
  tauto.
  tauto.
rewrite H16 in |- *.
  rewrite H17 in |- *.
 tauto.
Qed.

(* DIMENSION 1: *)

(* OK: *)

Lemma cF_Split1: forall(m:fmap)(x x' z:dart),
 inv_hmap m -> crackv m x x' -> exd m z ->
   cF (Split m one x x') z = 
    if eq_dart_dec (cF_1 m x) z then x'
    else if eq_dart_dec (cF_1 m x') z 
         then x 
         else cF m z.
Proof.
intros.
unfold crackv in H0.
unfold cF in |- *.
fold (cF m z) in |- *.
rewrite MA1.cA_1_Split in |- *.
 assert (Md1.kd = one).
   tauto.
 rewrite <- H2 in |- *.
   rewrite MA1.cA_1_Split_opp in |- *.
  simpl in |- *.
    rewrite H2 in |- *.
    elim (eq_dart_dec (cA m one x) (cA_1 m zero z)).
   elim (eq_dart_dec (cF_1 m x) z).
     tauto.
   intros.
     elim b.
     unfold cF_1 in |- *.
     rewrite a in |- *.
     rewrite cA_cA_1 in |- *.
     tauto.
    tauto.
    tauto.
  elim (eq_dart_dec (cA m one x') (cA_1 m zero z)).
   elim (eq_dart_dec (cF_1 m x) z).
    intros.
      elim b.
      rewrite <- a in |- *.
      unfold cF_1 in |- *.
      rewrite cA_1_cA in |- *.
      tauto.
     tauto.
    assert (exd m x).
     unfold MA1.crack in H0.
       unfold MA1.MfcA.expo in H0.
        tauto.
    generalize (exd_cA m one x).
       tauto.
   elim (eq_dart_dec (cF_1 m x') z).
     tauto.
   intros.
     elim b.
     unfold cF_1 in |- *.
     rewrite a in |- *.
     rewrite cA_cA_1 in |- *.
     tauto.
    tauto.
    tauto.
  elim (eq_dart_dec (cF_1 m x) z).
   intros.
     elim b0.
     rewrite <- a in |- *.
     unfold cF_1 in |- *.
     rewrite cA_1_cA in |- *.
     tauto.
    tauto.
   assert (exd m x).
    unfold MA1.crack in H0.
      unfold MA1.MfcA.expo in H0.
       tauto.
   generalize (exd_cA m one x).
      tauto.
  elim (eq_dart_dec (cF_1 m x') z).
   intros.
     elim b0.
     rewrite <- a in |- *.
     unfold cF_1 in |- *.
     rewrite cA_1_cA in |- *.
     tauto.
    tauto.
   assert (exd m x').
    unfold MA1.crack in H0.
      generalize (MA1.MfcA.expo_exd m x x').
       tauto.
   generalize (exd_cA m one x').
      tauto.
   tauto.
  tauto.
 tauto.
 tauto.
Qed.

Lemma cF_1_Split1:forall(m:fmap)(x x' z:dart),
 inv_hmap m -> crackv m x x' -> exd m z ->
   cF_1 (Split m one x x') z = 
    if eq_dart_dec x' z then (cF_1 m x)
    else if eq_dart_dec x z then (cF_1 m x') 
         else cF_1 m z.
Proof.
intros.
generalize (MA1.crack_exd m x x' H H0).
intro.
unfold cF_1 in |- *.
rewrite MA1.cA_Split in |- *.
 rewrite MA1.cA_Split_opp in |- *.
  assert (Md1.kd = one).
    tauto.
  rewrite H3 in |- *.
    simpl in |- *.
    elim (eq_dart_dec x z).
   intro.
     rewrite <- a in |- *.
     elim (eq_dart_dec x' x).
    intro.
      symmetry  in |- *.
      rewrite a0 in |- *.
       tauto.
    tauto.
  elim (eq_dart_dec x' z).
    tauto.
   tauto.
  tauto.
 tauto.
unfold crackv in H0.
   tauto.
Qed.

(* FROM WHERE: Tr m X Y = Split m one (cF m X) Y *)

(* OK: *)

Lemma cF_Split1_cF_x_y: forall(m:fmap)(x y z:dart),
 crackv m (cF m x) y ->
  inv_hmap m -> exd m x -> exd m y -> exd m z ->
    cF (Split m one (cF m x) y) z = 
      (if eq_dart_dec x z then y
       else if eq_dart_dec (cF_1 m y) z
            then cF m x else cF m z).
Proof.
intros.
rewrite cF_Split1 in |- *.
 rewrite cF_1_cF in |- *.
   tauto.
  tauto.
  tauto.
 tauto.
 tauto.
 tauto.
Qed.

Lemma cF_1_Split1_cF_x_y: forall(m:fmap)(x y z:dart),
crackv m (cF m x) y ->
 inv_hmap m -> exd m x -> exd m y -> exd m z ->
    cF_1 (Split m one (cF m x) y) z = 
      (if eq_dart_dec y z then x
       else if eq_dart_dec (cF m x) z
            then cF_1 m y else cF_1 m z).
Proof.
intros.
rewrite cF_1_Split1 in |- *.
 rewrite cF_1_cF in |- *.
   tauto.
  tauto.
  tauto.
 tauto.
 tauto.
 tauto.
Qed.

(* INSTANTIATION FOR DIM 1: Split1 AND cF: *)

Module ModSplit1cF<:SigTr
  with Definition Tr:= fun(m:fmap)(x y:dart)=> 
    Split m one (cF m x) y
  with Definition Prec_Tr:= fun(m:fmap)(x y:dart)=> 
    crackv m (cF m x) y.
Module M:= ModcF1.M.
Definition Tr(m:fmap)(x y:dart):= 
   Split m one (cF m x) y.
Definition Prec_Tr(m:fmap)(x y:dart):= 
   crackv m (cF m x) y.
Definition f_Tr:= cF_Split1_cF_x_y.
Definition f_1_Tr:= cF_1_Split1_cF_x_y.
Definition exd_Tr(m:fmap)(x y z:dart):=
  exd_Split_bis m one (cF m x) y z.
Definition ndN_Tr(m:fmap)(x y:dart):= 
  ndN_Split m one (cF m x) y.
End ModSplit1cF.

Module MFTrSplit1:= MTr ModSplit1cF.

(* OK: *)

Lemma MFTrSplit1_expo_expof: 
   MFTrSplit1.MfM.expo = expof.
Proof. tauto. Qed.

(* OK *)

Lemma MFTrSplit1_expo_dec_expof_dec: 
 forall(m:fmap)(x y:dart)(H:inv_hmap m)(A B:Prop),
  (if MFTrSplit1.MfM.expo_dec m x y H then A else B) <->
  (if expof_dec m x y H then A else B).
Proof. 
intros.
elim (MFTrSplit1.MfM.expo_dec m x y H).
 elim (expof_dec m x y H).
   tauto.
  tauto.
elim (expof_dec m x y H).
  tauto.
 tauto.
Qed.

(* OK: *)

Lemma MFTrSplit1_between_betweenf: 
  MFTrSplit1.MfM.between = betweenf.
Proof. tauto. Qed.

(* OK: *)

Lemma MFTrSplit1_Prec_Tr_crackv: forall(m:fmap)(x y:dart),
  ModSplit1cF.Prec_Tr m x y = crackv m (cF m x) y.
Proof. tauto. Qed.

(* OK: *)

Lemma expof_Split1_cF_x_y_CNS: 
  forall(m : fmap)(x y z t : dart)(H : inv_hmap m),
 ModSplit1cF.Prec_Tr m x y ->
   let x1:= cF m x in
   let y_1:= cF_1 m y in
   let m1 := Split m one (cF m x) y in
 exd m z ->
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
assert (crackv m (cF m x) y).
 rewrite <- MFTrSplit1_Prec_Tr_crackv in |- *.
    tauto.
generalize (MA1.crack_exd m (cF m x) y H H2).
  intros.
  assert (exd m x).
 generalize (exd_cF m x).
    tauto.
set
 (A0 :=
  betweenf m y z x /\ betweenf m y t x \/
  betweenf m x1 z y_1 /\ betweenf m x1 t y_1 \/ 
  ~ expof m x z /\ expof m z t)
 in |- *.
  set
   (B0 := expof m z t \/ expof m x z /\ expof m y t \/
       expof m x t /\ expof m y z) in |- *.
  cut
   (MFTrSplit1.MfM.expo m1 z t <->
    (if MFTrSplit1.MfM.expo_dec m x y H then A0 else B0)).
 generalize (MFTrSplit1_expo_dec_expof_dec m x y H A0 B0).
    tauto.
unfold A0 in |- *.
  unfold B0 in |- *.
  rewrite <- MFTrSplit1_between_betweenf in |- *.
  rewrite <- MFTrSplit1_expo_expof in |- *.
  assert (x1 = MFTrSplit1.MfM.f m x).
  tauto.
assert (y_1 = MFTrSplit1.MfM.f_1 m y).
  tauto.
assert (m1 = ModSplit1cF.Tr m x y).
  tauto.
rewrite H6 in |- *; rewrite H5 in |- *; rewrite H7 in |- *.
  apply MFTrSplit1.expo_Tr_CNS.
  tauto.
 tauto.
 tauto.
 tauto.
rewrite <- H7 in |- *.
  unfold m1 in |- *.
  apply inv_hmap_Split.
   tauto.
Qed.

(* USUAL FORM: *)

Lemma expof_Split1_CNS: 
  forall(m : fmap)(X Y z t : dart)(H : inv_hmap m),
 crackv m X Y -> exd m z ->
   let X_1:= cF_1 m X in
   let Y_1:= cF_1 m Y in
   let m1 := Split m one X Y in
  (expof m1 z t <->
        (if expof_dec m X_1 Y H
         then
          betweenf m Y z X_1 /\ betweenf m Y t X_1 \/
          betweenf m X z Y_1 /\ betweenf m X t Y_1 \/
          ~ expof m X_1 z /\ expof m z t
         else
          expof m z t \/
          expof m X_1 z /\ expof m Y t \/
          expof m X_1 t /\ expof m Y z)).
Proof.
intros.
generalize (MA1.crack_exd m X Y H H0).
intro.
decompose [and] H2.
clear H2.
set (x := X_1) in |- *.
set (y := Y) in |- *.
set (x1 := X) in |- *.
set (y_1 := Y_1) in |- *.
assert (x1 = cF m x).
 unfold x in |- *.
   unfold X_1 in |- *.
   rewrite cF_cF_1 in |- *.
  fold x1 in |- *.
     tauto.
  tauto.
  tauto.
assert (y_1 = cF_1 m y).
 unfold y in |- *.
   unfold y_1 in |- *.
   unfold Y_1 in |- *.
    tauto.
assert (m1 = Split m one (cF m x) y).
 unfold m1 in |- *.
   fold y in |- *.
   unfold x in |- *.
   unfold X_1 in |- *.
   rewrite cF_cF_1 in |- *.
   tauto.
  tauto.
  tauto.
rewrite H2 in |- *.
  rewrite H6 in |- *.
  rewrite H5 in |- *.
  apply expof_Split1_cF_x_y_CNS.
 rewrite MFTrSplit1_Prec_Tr_crackv in |- *.
   unfold x in |- *.
   unfold X_1 in |- *.
   rewrite cF_cF_1 in |- *.
  unfold y in |- *.
     tauto.
  tauto.
  tauto.
 tauto.
Qed.

(* FACE DEGREES: MERGE: *)

Theorem degreef_Split1_merge_summary:
 forall(m : fmap)(X Y Z : dart)(H : inv_hmap m),
     crackv m X Y -> exd m Z ->
       let m1 := Split m one X Y in
       let X_1 := cF_1 m X in
       let dX_1 := degreef m X_1 in
       let dY := degreef m Y in
    ~ expof m X_1 Y ->
      degreef m1 Z =
       (if expof_dec m X_1 Z H
        then dX_1 + dY
        else
           if expof_dec m Y Z H
           then dX_1 + dY
           else degreef m Z).
Proof.
intros.
assert (inv_hmap m1).
 unfold m1 in |- *.
   apply inv_hmap_Split.
    tauto.
generalize (MA1.crack_exd m X Y H).
  intro.
  assert (exd m X /\ exd m Y).
 apply H4.
   unfold crackv in H0.
    tauto.
clear H4.
  assert (m1 = ModSplit1cF.Tr m X_1 Y).
 unfold m1 in |- *.
   unfold ModSplit1cF.Tr in |- *.
   unfold X_1 in |- *.
   rewrite cF_cF_1 in |- *.
   tauto.
  tauto.
  tauto.
assert (ModSplit1cF.Prec_Tr m X_1 Y).
 unfold ModSplit1cF.Prec_Tr in |- *.
   unfold X_1 in |- *.
   rewrite cF_cF_1 in |- *.
   tauto.
  tauto.
  tauto.
assert (exd m X_1).
 unfold X_1 in |- *.
   generalize (exd_cF_1 m X).
    tauto.
assert (~ MFTrSplit1.MfM.expo m X_1 Y).
  tauto.
assert (degreef = MFTrSplit1.MfM.degree).
  tauto.
rewrite H9 in |- *.
  rewrite H4 in |- *.
  assert (exd m Y).
  tauto.
rewrite H4 in H3.
  generalize (MFTrSplit1.degree_Tr_merge_summary
         m X_1 Y Z H H6 H7 H10 H1 H3 H8).
  rewrite <- H4 in |- *.
  rewrite <- H9 in |- *.
  fold dY in |- *.
  fold dX_1 in |- *.
  elim (MFTrSplit1.MfM.expo_dec m X_1 Z H).
 elim (expof_dec m X_1 Z H).
   tauto.
  tauto.
elim (MFTrSplit1.MfM.expo_dec m Y Z H).
 elim (expof_dec m X_1 Z H).
   tauto.
 elim (expof_dec m Y Z H).
   tauto.
  tauto.
elim (expof_dec m X_1 Z H).
  tauto.
elim (expof_dec m Y Z H).
  tauto.
 tauto.
Qed.

(* FACE DEGREES, SPLIT: *)

Theorem degreef_Split1_split_summary:
 forall (m : fmap) (X Y Z : dart) (j : nat) 
        (H : inv_hmap m),
      crackv m X Y -> exd m Z ->
       let m1 := Split m one X Y in
       let X_1:= cF_1 m X in
       let dY := degreef m Y in
       Y = Iter (cF m) j X_1 ->
       2 <= j <= dY ->
    degreef m Z =
       (if expof_dec m Y Z H
        then degreef m1 Y + degreef m1 X
        else degreef m1 Z).
Proof.
intros.
assert (inv_hmap m1).
 unfold m1 in |- *.
   apply inv_hmap_Split.
    tauto.
generalize (MA1.crack_exd m X Y H).
  intro.
  assert (exd m X /\ exd m Y).
 apply H5.
   unfold crackv in H0.
    tauto.
clear H5.
  assert (m1 = ModSplit1cF.Tr m X_1 Y).
 unfold ModSplit1cF.Tr in |- *.
   unfold X_1 in |- *.
   rewrite cF_cF_1 in |- *.
  fold m1 in |- *.
     tauto.
  tauto.
  tauto.
assert (ModSplit1cF.Prec_Tr m X_1 Y).
 unfold ModSplit1cF.Prec_Tr in |- *.
   unfold X_1 in |- *.
   rewrite cF_cF_1 in |- *.
   tauto.
  tauto.
  tauto.
assert (exd m X_1).
 unfold X_1 in |- *.
   generalize (exd_cF_1 m X).
    tauto.
assert (exd m Y).
  tauto.
assert (cF = MFTrSplit1.MfM.f).
  tauto.
rewrite H10 in H2.
  assert (degreef = MFTrSplit1.MfM.degree).
  tauto.
rewrite H11 in |- *.
  rewrite H5 in H4.
  generalize
   (MFTrSplit1.degree_Tr_split_summary 
       m X_1 Y Z j H H7 H8 H9 H1 H2 H3 H4).
  rewrite <- H11 in |- *.
  rewrite <- H5 in |- *.
  rewrite <- H10 in |- *.
  unfold X_1 in |- *.
  rewrite cF_cF_1 in |- *.
 elim (MFTrSplit1.MfM.expo_dec m Y Z H).
  elim (expof_dec m Y Z H).
    tauto.
   tauto.
 elim (expof_dec m Y Z H).
   tauto.
  tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Theorem degreef_Split1_split_summary_bis:
 forall (m : fmap) (X Y Z : dart) (j : nat) 
        (H : inv_hmap m),
      crackv m X Y -> exd m Z ->
       let m1  := Split m one X Y in
       let X_1 := cF_1 m X in
       let Y_1 := cF_1 m Y in
       let dY  := degreef m Y in
       Y = Iter (cF m) j X_1 ->
       2 <= j <= dY ->
       (betweenf m Y Z X_1 ->
           degreef m1 Z = dY - j + 1) /\
       (betweenf m X Z Y_1 ->
           degreef m1 Z = j - 1) /\
       (~ expof m X_1 Z ->
           degreef m1 Z = degreef m Z).
Proof.
intros.
assert (inv_hmap m1).
 unfold m1 in |- *.
   apply inv_hmap_Split.
    tauto.
generalize (MA1.crack_exd m X Y H).
  intro.
  assert (exd m X /\ exd m Y).
 apply H5.
   unfold crackv in H0.
    tauto.
clear H5.
  assert (m1 = ModSplit1cF.Tr m X_1 Y).
 unfold ModSplit1cF.Tr in |- *.
   unfold X_1 in |- *.
   rewrite cF_cF_1 in |- *.
  fold m1 in |- *.
     tauto.
  tauto.
  tauto.
assert (ModSplit1cF.Prec_Tr m X_1 Y).
 unfold ModSplit1cF.Prec_Tr in |- *.
   unfold X_1 in |- *.
   rewrite cF_cF_1 in |- *.
   tauto.
  tauto.
  tauto.
assert (exd m X_1).
 unfold X_1 in |- *.
   generalize (exd_cF_1 m X).
    tauto.
assert (exd m Y).
  tauto.
assert (cF = MFTrSplit1.MfM.f).
  tauto.
rewrite H10 in H2.
  assert (degreef = MFTrSplit1.MfM.degree).
  tauto.
rewrite H11 in |- *.
  rewrite H5 in H4.
  assert (betweenf = MFTrSplit1.MfM.between).
  tauto.
rewrite H12 in |- *.
  assert (expof = MFTrSplit1.MfM.expo).
  tauto.
rewrite H13 in |- *.
  rewrite H5 in |- *.
  unfold dY in |- *.
  rewrite H11 in |- *.
  generalize
   (MFTrSplit1.degree_Tr_split_summary_bis 
    m X_1 Y Z j H H7 H8 H9 H1 H2 H3 H4).
  rewrite <- H11 in |- *.
  rewrite <- H5 in |- *.
  rewrite <- H10 in |- *.
  rewrite <- H12 in |- *.
  rewrite <- H13 in |- *.
  assert (cF m X_1 = X).
 unfold X_1 in |- *.
   rewrite cF_cF_1 in |- *.
   tauto.
  tauto.
  tauto.
rewrite H14 in |- *.
  assert (MFTrSplit1.MfM.f_1 m Y = cF_1 m Y).
  tauto.
rewrite H15 in |- *.
  fold Y_1 in |- *.
   tauto.
Qed.

(*=================================================
         CONSEQUENCES IN EDGES AND VERTICES 
               OF BREAKING BY B:
                expe_B0, expv_B1
==================================================*)

(* DIM 0: *)

Lemma expe_B0_CNS: 
  forall (m :fmap)(x z t: dart)(H:inv_hmap m),
       let m1 := B m zero x in
       let x0 := cA m zero x in
       let tx0 := top m zero x in
       let bx0 := bottom m zero x in
     succ m zero x -> exd m z ->
     (expe m1 z t <->
      (if expe_dec m x bx0 H
       then
        betweene m bx0 z x /\ betweene m bx0 t x \/
        betweene m x0 z tx0 /\ betweene m x0 t tx0 \/
        ~ expe m x z /\ expe m z t
       else
        expe m z t \/
        expe m x z /\ expe m bx0 t \/
        expe m x t /\ expe m bx0 z)).
Proof.
intros.
assert (m1 = Split m zero x tx0).
 unfold Split in |- *.
   elim (succ_dec m zero x).
  intro.
    elim (succ_dec m zero tx0).
   unfold tx0 in |- *.
     intro.
      absurd (succ m zero (top m zero x)).
    apply not_succ_top.
       tauto.
    tauto.
  fold m1 in |- *.
     tauto.
  tauto.
assert (expe m x tx0).
 apply expe_symm.
   tauto.
 unfold tx0 in |- *.
   apply MA0.expo_top_z.
   tauto.
 apply succ_exd with zero.
   tauto.
  tauto.
assert (x <> tx0).
 intro.
   rewrite H4 in H0.
   unfold tx0 in H0.
   generalize H0.
   apply not_succ_top.
    tauto.
assert (cA m zero tx0 = bx0).
 unfold tx0 in |- *; unfold bx0 in |- *.
   rewrite cA_top in |- *.
   tauto.
  tauto.
 apply succ_exd with zero.
   tauto.
  tauto.
rewrite <- H5 in |- *.
  unfold x0 in |- *.
  rewrite H2 in |- *.
  apply expe_Split0_CNS_aux.
 unfold cracke in |- *.
   unfold MA0.crack in |- *.
   split.
   tauto.
 fold (expe m x tx0) in |- *.
    tauto.
 tauto.
Qed.

(* DIM 1: OK: *)

Lemma expv_B1_CNS: 
  forall (m :fmap)(x z t: dart)(H:inv_hmap m),
       let m1 := B m one x in
       let x1 := cA m one x in
       let tx1 := top m one x in
       let bx1 := bottom m one x in
     succ m one x -> exd m z ->
     (expv m1 z t <->
      (if expv_dec m x bx1 H
       then
        betweenv m bx1 z x /\ betweenv m bx1 t x \/
        betweenv m x1 z tx1 /\ betweenv m x1 t tx1 \/
        ~ expv m x z /\ expv m z t
       else
        expv m z t \/
        expv m x z /\ expv m bx1 t \/
        expv m x t /\ expv m bx1 z)).
Proof.
intros.
assert (m1 = Split m one x tx1).
 unfold Split in |- *.
   elim (succ_dec m one x).
  intro.
    elim (succ_dec m one tx1).
   unfold tx1 in |- *.
     intro.
      absurd (succ m one (top m one x)).
    apply not_succ_top.
       tauto.
    tauto.
  fold m1 in |- *.
     tauto.
  tauto.
assert (expv m x tx1).
 apply expv_symm.
   tauto.
 unfold tx1 in |- *.
   apply MA1.expo_top_z.
   tauto.
 apply succ_exd with one.
   tauto.
  tauto.
assert (x <> tx1).
 intro.
   rewrite H4 in H0.
   unfold tx1 in H0.
   generalize H0.
   apply not_succ_top.
    tauto.
assert (cA m one tx1 = bx1).
 unfold tx1 in |- *; unfold bx1 in |- *.
   rewrite cA_top in |- *.
   tauto.
  tauto.
 apply succ_exd with one.
   tauto.
  tauto.
rewrite <- H5 in |- *.
  unfold x1 in |- *.
  rewrite H2 in |- *.
  apply expv_Split1_CNS_aux.
 unfold crackv in |- *.
   unfold MA1.crack in |- *.
   split.
   tauto.
 fold (expv m x tx1) in |- *.
    tauto.
 tauto.
Qed.

(*===================================================
      CONSEQUENCES IN FACES OF BREAKING WITH B:
                    expof / B0, B1
===================================================*)

(* 
B m k x IS A PARTICULAR CASE OF Split m k x x' WHERE succ m k x AND x' = top m k x, HENCE ~succ m k x'.
*)

(* OK!!: *)

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
Proof.
intros.
assert (m1 = Split m zero x tx0).
 unfold Split in |- *.
   elim (succ_dec m zero x).
  intro.
    elim (succ_dec m zero tx0).
   unfold tx0 in |- *.
     intro.
      absurd (succ m zero (top m zero x)).
    apply not_succ_top.
       tauto.
    tauto.
  fold m1 in |- *.
     tauto.
  tauto.
assert (expe m x tx0).
 apply expe_symm.
   tauto.
 unfold tx0 in |- *.
   apply MA0.expo_top_z.
   tauto.
 apply succ_exd with zero.
   tauto.
  tauto.
assert (x <> tx0).
 intro.
   rewrite H4 in H0.
   unfold tx0 in H0.
   generalize H0.
   apply not_succ_top.
    tauto.
rewrite H2 in |- *.
  unfold bx0 in |- *.
  unfold tx0_1 in |- *.
  unfold x_1 in |- *.
  unfold x0 in |- *.
  apply expof_Split0_CNS.
 unfold cracke in |- *.
   unfold MA0.crack in |- *.
   split.
   tauto.
 fold (expe m x tx0) in |- *.
    tauto.
 tauto.
Qed.

(* IDEM, DIM 1, OK: *)

Lemma expof_B1_CNS: 
  forall(m:fmap)(x y z t:dart)(H:inv_hmap m),
   let tx1:= top m one x in
   let x_1:= cF_1 m x in   
   let tx1_1:= cF_1 m tx1 in
   let m1 := B m one x in
 succ m one x -> exd m z ->
  (expof m1 z t <->
     (if expof_dec m x_1 tx1 H
      then
       betweenf m tx1 z x_1 /\ betweenf m tx1 t x_1 \/
       betweenf m x z tx1_1 /\ betweenf m x t tx1_1 \/
       ~ expof m x_1 z /\ expof m z t
      else
       expof m z t \/
       expof m x_1 z /\ expof m tx1 t \/
       expof m x_1 t /\ expof m tx1 z)).
Proof.
intros.
assert (m1 = Split m one x tx1).
 unfold Split in |- *.
   elim (succ_dec m one x).
  intro.
    elim (succ_dec m one tx1).
   unfold tx1 in |- *.
     intro.
      absurd (succ m one (top m one x)).
    apply not_succ_top.
       tauto.
    tauto.
  fold m1 in |- *.
     tauto.
  tauto.
assert (expv m x tx1).
 apply expv_symm.
   tauto.
 unfold tx1 in |- *.
   apply MA1.expo_top_z.
   tauto.
 apply succ_exd with one.
   tauto.
  tauto.
assert (x <> tx1).
 intro.
   rewrite H4 in H0.
   unfold tx1 in H0.
   generalize H0.
   apply not_succ_top.
    tauto.
rewrite H2 in |- *.
  unfold tx1_1 in |- *.
  unfold x_1 in |- *.
  apply expof_Split1_CNS.
 unfold crackv in |- *.
   unfold MA1.crack in |- *.
   split.
   tauto.
 fold (expv m x tx1) in |- *.
    tauto.
 tauto.
Qed.


(* TRANSLATE ALSO THE RESULTS FOR DEGREES... *)


(*===================================================
====================================================*)


(*====================================================
=======================================================
                  END of Part 4
=======================================================
=====================================================*)


(* LATER...: *)


(* FAIT DANS Del11 

Lemma cF_1_Br1_bis:forall(m:fmap)(x x' z:dart),
 inv_hmap m -> double_link m x x' -> 
   cF_1 (Br1 m x x') z = 
    if eq_dart_dec (cA_1 m one x) z then  cA m zero x'
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

(* CONTINUATION: USEFUL ?? *)

(*
Theorem orb_x_eqs_orb_y: forall(m:fmap)(x y:dart),
 let m1:= Tr m x y in
 inv_hmap m -> ~expo m x y ->
    eqs (Iter_orb m1 x) (Iter_orb m1 y).
*)

(* ANCIENT: USEFUL ??
PBS... 

Theorem orb_x_eqs_orb_y0: forall(m:fmap)(x y:dart),
 let m1:= L m one x y in
 let y0:= cA m zero y in
 inv_hmap m1 -> ~expof m x y0 ->
    eqs (MF.Iter_orb m1 x) (MF.Iter_orb m1 y0).
Proof.
intros.
apply MF.eqs_orb.
  tauto.
apply MF.expo_symm.
  tauto.
unfold MF.expo in |- *.
  split.
 unfold m1 in |- *.
   simpl in |- *.
   unfold y0 in |- *.
   generalize (exd_cA m zero y).
   unfold m1 in H.
   simpl in H.
   unfold prec_L in H.
    tauto.
split with 1.
  simpl in |- *.
  assert (MF.f = cF).
  tauto.
rewrite H1 in |- *.
  unfold m1 in |- *.
  rewrite cF_L1 in |- *.
 fold y0 in |- *.
   elim (eq_dart_dec y0 y0).
   tauto.
  tauto.
unfold m1 in H; simpl in H.
   tauto.
unfold m1 in H; simpl in H.
   tauto.
Qed.
*)

(* TO ADAPT AND PUT IN J2B: USEFUL?
VERSION orb:

Theorem orb_L1_eqs: forall(m:fmap)(x y z:dart),
 let m1:= L m one x y in
 let y0:= cA m zero y in
 inv_hmap m1 -> exd m z -> ~expof m x y0 
  -> ~expof m x z -> ~expof m y0 z ->  
   eqs (MF.Iter_orb m1 z) (MF.Iter_orb m z).
Proof.
intros.
unfold eqs in |- *.
intro t.
generalize (expof_L1_eq m x y z t H H1 H2 H3).
fold m1 in |- *.
intro.
generalize (MF.expo_eq_exds_orb m z t).
intros.
generalize (MF.expo_eq_exds_orb m1 z t).
intros.
assert (inv_hmap m1).
  tauto.
unfold m1 in H7.
  simpl in H7.
  unfold prec_L in H7.
  decompose [and] H7.
  clear H7.
  assert (exd m z <-> exd m1 z).
 unfold m1 in |- *.
   simpl in |- *.
    tauto.
split.
 intro.
   assert (exd m1 z).
  unfold m1 in |- *.
    simpl in |- *.
     tauto.
 generalize (MF.incls_orbit m1 z H H15).
   intros.
   assert (fmap_to_set m1 = fmap_to_set m).
  unfold m1 in |- *.
    simpl in |- *.
     tauto.
 rewrite H17 in H16.
   inversion H16.
   generalize (H18 t H13).
   intro.
   generalize (exd_exds m t).
   intro.
   clear H18.
   assert (exd m t).
   tauto.
 assert (exd m1 t).
  unfold m1 in |- *.
    simpl in |- *.
     tauto.
 unfold expof in H4.
    tauto.
intro.
  assert (exd m1 z).
 unfold m1 in |- *.
   simpl in |- *.
    tauto.
generalize (MF.incls_orbit m1 z H H15).
  intros.
  assert (fmap_to_set m1 = fmap_to_set m).
 unfold m1 in |- *.
   simpl in |- *.
    tauto.
generalize (MF.incls_orbit m z H8 H0).
  intros.
  inversion H18.
  generalize (H19 t H13).
  intro.
  unfold expof in H4.
  generalize (exd_exds m t).
  intro.
  clear H19.
  assert (exd m1 t).
 unfold m1 in |- *.
   simpl in |- *.
    tauto.
assert (exd m t).
  tauto.
 tauto.
Qed.
*)















