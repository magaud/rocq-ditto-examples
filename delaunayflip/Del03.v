(*=====================================================

        TOPOLOGICAL FMAPS, HMAPS -
              WITH TAGS AND EMBEDDINGS

     PART 3: FUNCTOR MTr FOR TRANSFORMATIONS Tr
                WITH degree_Tr, expo_Tr...

=====================================================*)

Require Export Del02. 

(*====================================================
        SigTr: EXTENSION OF Sigf TO INTRODUCE Tr
====================================================*)

Module Type SigTr.
 Declare Module M:Sigf.
Parameter Tr : fmap -> dart -> dart -> fmap.
Parameter Prec_Tr: fmap -> dart -> dart -> Prop.
Axiom f_Tr : forall(m:fmap)(x y z:dart),
 Prec_Tr m x y -> 
  inv_hmap m -> exd m x -> exd m y -> exd m z ->
   M.f (Tr m x y) z = 
    if eq_dart_dec x z then y
    else if eq_dart_dec (M.f_1 m y) z then (M.f m x)
        else (M.f m z).
Axiom f_1_Tr : forall(m:fmap)(x y z:dart), 
 Prec_Tr m x y ->
  inv_hmap m -> exd m x -> exd m y -> exd m z ->  
   M.f_1 (Tr m x y) z = 
    if eq_dart_dec y z then x
    else if eq_dart_dec (M.f m x) z then (M.f_1 m y)
       else (M.f_1 m z).
Axiom exd_Tr : forall (m:fmap)(x y z:dart),
  inv_hmap m -> (exd m z <-> exd (Tr m x y) z).
Axiom ndN_Tr : forall (m:fmap)(x y:dart),
  ndN (Tr m x y) = ndN m.
End SigTr.

(*====================================================
           FUNCTOR MTr INTRODUCING Tr PROPERTIES
====================================================*)

(* OK: *)

Module MTr(Mod:SigTr).
  Module MfM:= Mf (Mod.M).

(*=====================================================
              degree AND expo AFTER Tr
=====================================================*)

(*=====================================================
           1.  CASE:  ~expo m x y (MERGE)
=====================================================*)

Open Scope nat_scope.

(* i-SUCCS OF y BY Tr, FOR i < DEG OF y, ARE INVARIANT: *)

(* OK: *)

Lemma f_Tr_y_y_1:forall(m:fmap)(x y:dart)(i:nat),
   Mod.Prec_Tr m x y -> 
     inv_hmap m -> exd m x -> exd m y ->
   let dy := MfM.degree m y in  
   let m1:= Mod.Tr m x y in
  ~MfM.expo m x y ->
    i <= dy - 1 ->
      Iter (MfM.f m1) i y = Iter (MfM.f m) i y.
Proof.
intros m x y i Pr.
intros.
generalize (MfM.degree_lub m y H H1).
simpl in |- *.
fold dy in |- *.
intros.
decompose [and] H4.
clear H4.
induction i.
 simpl in |- *.
    tauto.
simpl in |- *.
  rewrite IHi in |- *.
 unfold m1 in |- *.
   rewrite Mod.f_Tr in |- *.
  set (y_1 := MfM.f_1 m y) in |- *.
    set (yi := Iter (MfM.f m) i y) in |- *.
    assert (Mod.M.f = MfM.f).
    tauto.
  assert (Mod.M.f_1 = MfM.f_1).
    tauto.
  rewrite H4 in |- *.
    rewrite H6 in |- *.
    elim (eq_dart_dec x yi).
   intros.
     elim H2.
     apply MfM.expo_symm.
     tauto.
   unfold MfM.expo in |- *.
     split.
     tauto.
   split with i.
     fold yi in |- *.
     symmetry  in |- *.
      tauto.
  fold y_1 in |- *.
    elim (eq_dart_dec y_1 yi).
   intros.
     assert (i = dy - 1).
    apply (MfM.unicity_mod_p m y i (dy - 1) H H1).
     fold dy in |- *.
       rewrite MfM.upb_eq_degree in |- *.
      fold dy in |- *.
         lia.
      tauto.
      tauto.
    rewrite MfM.upb_eq_degree in |- *.
     fold dy in |- *.
        lia.
     tauto.
     tauto.
    rewrite <- MfM.Iter_f_f_1 in |- *.
     simpl in |- *.
       rewrite H7 in |- *.
       fold y_1 in |- *.
       fold yi in |- *.
       symmetry  in |- *.
        tauto.
     tauto.
     tauto.
     lia.
    absurd (i = dy - 1).
     lia.
    tauto.
   tauto.
  tauto.
  tauto.
  tauto.
  tauto.
 generalize (MfM.exd_Iter_f m i y).
    tauto.
 lia.
Qed.

(* i-SUCCS OF y by (f m1), 0 < i < DEG y, <> FROM y: *)

Lemma diff_y1_y_1:forall(m:fmap)(x y:dart)(i:nat),
  Mod.Prec_Tr m x y -> 
    inv_hmap m -> exd m x -> exd m y ->
   let dy := MfM.degree m y in  
   let m1 := Mod.Tr m x y in
  ~MfM.expo m x y -> 
    0 < i <= dy - 1 ->
     Iter (MfM.f m1) i y <> y.
Proof.
intros m x y i Pr.
intros.
generalize (f_Tr_y_y_1 m x y i Pr H H0 H1).
simpl in |- *.
fold dy in |- *.
fold m1 in |- *.
intros.
generalize (H4 H2).
intro.
clear H4.
rewrite H5 in |- *.
 generalize (MfM.degree_lub m y H H1).
   simpl in |- *.
   intros.
   decompose [and] H4.
   clear H4 H5.
   fold dy in H9.
   apply H9.
    lia.
 lia.
Qed.

(* THE dy_SUCC OF y BY (f m1) IS x1: OK: *)

Lemma f_Tr_y:forall(m:fmap)(x y:dart),
 Mod.Prec_Tr m x y -> 
  inv_hmap m -> exd m x -> exd m y ->
   let dy := MfM.degree m y in  
   let m1:= Mod.Tr m x y in
   let x1:= MfM.f m x in
   ~MfM.expo m x y ->
    Iter (MfM.f m1) dy y = x1.
Proof.
intros m x y Pr.
intros.
generalize (MfM.degree_lub m y H H1).
simpl in |- *.
fold dy in |- *.
intros.
decompose [and] H3.
clear H3.
assert (MfM.Iter_upb m y = dy).
 unfold dy in |- *.
   apply MfM.upb_eq_degree.
   tauto.
  tauto.
assert (dy = S (dy - 1)).
  lia.
rewrite H5 in |- *.
  simpl in |- *.
  unfold m1 in |- *.
  rewrite f_Tr_y_y_1 in |- *.
 rewrite Mod.f_Tr in |- *.
  elim (eq_dart_dec x (Iter (MfM.f m) (dy - 1) y)).
   intro.
     elim H2.
     apply MfM.expo_symm.
     tauto.
   unfold MfM.expo in |- *.
     split.
     tauto.
   split with (dy - 1).
     symmetry  in |- *.
      tauto.
  assert (Mod.M.f = MfM.f).
    tauto.
  assert (Mod.M.f_1 = MfM.f_1).
    tauto.
  rewrite H8 in |- *; rewrite H9 in |- *.
    elim (eq_dart_dec (MfM.f_1 m y)
    (Iter (MfM.f m) (dy - 1) y)).
   intros.
     fold x1 in |- *;  tauto.
  intros.
    elim b.
    rewrite <- MfM.Iter_f_f_1 in |- *.
   simpl in |- *.
     rewrite H6 in |- *.
      tauto.
   tauto.
   tauto.
   tauto.
  tauto.
  tauto.
  tauto.
  tauto.
 generalize (MfM.exd_Iter_f m (dy - 1) y).
    tauto.
 tauto.
 tauto.
 tauto.
 tauto.
 tauto.
fold dy in |- *.
   lia.
Qed.

(* IT IS DIFFERENT FROM y: OK *)

Lemma diff_x1_y:forall(m:fmap)(x y:dart),
 Mod.Prec_Tr m x y ->  
  inv_hmap m -> exd m x -> exd m y ->
   let m1 := Mod.Tr m x y in
   let dy := MfM.degree m y in
    ~MfM.expo m x y ->
      Iter (MfM.f m1) dy y <> y.
Proof.
intros m x y Pr.
intros.
unfold m1 in |- *.
unfold dy in |- *.
rewrite f_Tr_y in |- *.
 intro.
   elim H2.
   unfold MfM.expo in |- *.
   split.
   tauto.
 split with 1.
   simpl in |- *.
    tauto.
 tauto.
 tauto.
 tauto.
 tauto.
 tauto.
Qed.

(* j-SUCCS OF x1 BY (f m1), j < DEG x1 (= DEG x), ARE INVARIANT: OK *)

Lemma f_Tr_x1_x_aux:forall(m:fmap)(x y:dart)(j:nat),
 Mod.Prec_Tr m x y -> 
  inv_hmap m -> exd m x -> exd m y ->
   let m1 := Mod.Tr m x y in 
   let x1 := MfM.f m x in
   let dx1 := MfM.degree m x1 in
   let dy  := MfM.degree m y in
   ~MfM.expo m x y ->
    j + 1 <= dx1 ->
     Iter (MfM.f m1) (dy + j) y =
             Iter (MfM.f m) j x1.
Proof.
intros m x y j Pr.
intros.
rewrite Nat.add_comm in |- *.
rewrite MfM.Iter_comp in |- *.
unfold m1 in |- *.
unfold dy in |- *.
rewrite f_Tr_y in |- *.
 fold x1 in |- *.
   fold m1 in |- *.
   induction j.
  simpl in |- *.
     tauto.
 simpl in |- *.
   rewrite IHj in |- *.
  set (x1j := Iter (MfM.f m) j x1) in |- *.
    unfold m1 in |- *.
    rewrite Mod.f_Tr in |- *.
   elim (eq_dart_dec x x1j).
    unfold x1j in |- *.
      unfold x1 in |- *.
      assert (Iter (MfM.f m) 1 x = MfM.f m x).
     simpl in |- *.
        tauto.
    rewrite <- H4 in |- *.
      rewrite <- MfM.Iter_comp in |- *.
      intro.
      symmetry  in a.
       absurd (Iter (MfM.f m) (j + 1) x = x).
     generalize (MfM.degree_lub m x H H0).
       simpl in |- *.
       intro.
       decompose [and] H5.
       clear H5.
       assert (MfM.degree m x = MfM.degree m x1).
      apply MfM.expo_degree.
        tauto.
      unfold MfM.expo in |- *.
        split.
        tauto.
      split with 1.
        simpl in |- *.
        fold x1 in |- *.
         tauto.
     fold dx1 in H5.
       apply H9.
       rewrite H5 in |- *.
        lia.
     tauto.
   elim (eq_dart_dec (Mod.M.f_1 m y) x1j).
    intros.
      unfold x1j in a.
      unfold x1 in a.
      assert (Mod.M.f = MfM.f).
      tauto.
    assert (Mod.M.f_1 = MfM.f_1).
      tauto.
    rewrite H4 in |- *.
      assert (y = MfM.f m (Iter (MfM.f m) j
                    (MfM.f m x))).
     rewrite <- a in |- *.
       rewrite H5 in |- *.
       rewrite MfM.f_f_1 in |- *.
       tauto.
      tauto.
      tauto.
    elim H2.
      unfold MfM.expo in |- *.
      split.
      tauto.
    split with (j + 2).
      rewrite H6 in |- *.
      assert
    (MfM.f m (Iter (MfM.f m) j (MfM.f m x)) =
        Iter (MfM.f m) (S j) (MfM.f m x)).
     simpl in |- *.
        tauto.
    rewrite H7 in |- *.
      assert (MfM.f m x = Iter (MfM.f m) 1 x).
     simpl in |- *.
        tauto.
    rewrite H8 in |- *.
      rewrite <- MfM.Iter_comp in |- *.
      assert (j + 2 = S j + 1).
      lia.
    rewrite H9 in |- *.
       tauto.
    tauto.
   tauto.
   tauto.
   tauto.
   tauto.
  unfold x1j in |- *.
    generalize (MfM.exd_Iter_f m j x1).
    unfold x1 in |- *.
    generalize (MfM.exd_f m x).
     tauto.
  lia.
 tauto.
 tauto.
 tauto.
 tauto.
 tauto.
Qed.

Lemma f_Tr_x1_x:forall(m:fmap)(x y:dart)(j:nat),
 Mod.Prec_Tr m x y -> 
  inv_hmap m -> exd m x -> exd m y ->
   let m1 := Mod.Tr m x y in 
   let x1 := MfM.f m x in
   let dx := MfM.degree m x in
   let dy := MfM.degree m y in
   ~MfM.expo m x y ->
    j + 1 <= dx ->
     Iter (MfM.f m1) (dy + j) y =
         Iter (MfM.f m) j x1.
Proof.
intros m x y j Pr.
intros.
assert (dx = MfM.degree m x1).
 unfold dx in |- *.
   apply MfM.expo_degree.
   tauto.
 unfold MfM.expo in |- *.
   split.
   tauto.
 split with 1.
   simpl in |- *.
   fold x1 in |- *.
    tauto.
unfold m1 in |- *.
  unfold x1 in |- *.
  unfold dy in |- *.
  apply f_Tr_x1_x_aux.
  tauto.
 tauto.
 tauto.
 tauto.
 tauto.
fold x1 in |- *.
  rewrite <- H4 in |- *.
   tauto.
Qed.

(* THE ARE DIFFERENT FROM y: *)

Lemma diff_x1_x:forall(m:fmap)(x y:dart)(j:nat),
 Mod.Prec_Tr m x y -> 
  inv_hmap m -> exd m x -> exd m y ->
   let m1 := Mod.Tr m x y in 
   let x1 := MfM.f m x in
   let dx := MfM.degree m x in
   let dy  := MfM.degree m y in
   ~MfM.expo m x y ->
    j + 1 <= dx ->
     Iter (MfM.f m1) (dy + j) y <> y.
Proof.
intros m x y j Pr.
intros.
unfold m1 in |- *.
unfold dy in |- *.
rewrite f_Tr_x1_x in |- *.
 intro.
   assert (MfM.f m x = Iter (MfM.f m) 1 x).
  simpl in |- *;  tauto.
 rewrite H5 in H4.
   rewrite <- MfM.Iter_comp in H4.
   elim H2.
   unfold MfM.expo in |- *.
   split.
   tauto.
 split with (j + 1).
    tauto.
 tauto.
 tauto.
 tauto.
 tauto.
 tauto.
  fold dx in |- *.
   tauto.
Qed.

(* THE (dy+dx)-TH SUCC OF y IS y: *)

Lemma f_Tr_x:forall(m:fmap)(x y:dart),
 Mod.Prec_Tr m x y -> 
  inv_hmap m -> exd m x -> exd m y ->
   let dy := MfM.degree m y in  
   let m1 := Mod.Tr m x y in
   let dx := MfM.degree m x in
   ~MfM.expo m x y ->
    Iter (MfM.f m1) (dy + dx) y = y.
Proof.
intros m x y Pr.
intros.
assert (0 < dx).
 unfold dx in |- *.
   apply MfM.degree_pos.
   generalize (MfM.exd_f m x).
    tauto.
set (x1 := MfM.f m x) in |- *.
  assert (exd m x1).
 unfold x1 in |- *.
   generalize (MfM.exd_f m x).
    tauto.
assert (dx = MfM.degree m x1).
 unfold dx in |- *.
   apply MfM.expo_degree.
   tauto.
 unfold MfM.expo in |- *.
   split.
   tauto.
 split with 1.
   simpl in |- *.
   fold x1 in |- *.
    tauto.
assert (dy + dx = S (dy + (dx - 1))).
  lia.
rewrite H6 in |- *.
  simpl in |- *.
  unfold m1 in |- *; unfold dy in |- *.
  rewrite f_Tr_x1_x in |- *.
 fold x1 in |- *.
   rewrite <- MfM.Iter_f_f_1 in |- *.
  rewrite H5 in |- *.
    rewrite MfM.degree_per in |- *.
   unfold x1 in |- *.
     simpl in |- *.
     rewrite MfM.f_1_f in |- *.
    rewrite Mod.f_Tr in |- *.
     elim (eq_dart_dec x x).
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
  tauto.
 tauto.
 tauto.
 tauto.
 tauto.
 tauto.
fold dx in |- *.
   lia.
Qed.

(* OK: *)

Lemma degree_Tr_merge_MAX: 
  forall(m:fmap)(x y:dart), 
   let m1:= Mod.Tr m x y in
   let x1 := MfM.f m x in
 Mod.Prec_Tr m x y -> 
  inv_hmap m -> exd m x -> exd m y -> 
 ~ MfM.expo m x y ->
   let MAX := MfM.degree m y + MfM.degree m x in
      MfM.degree_aux m1 y MAX = MAX.
Proof.
intros m x y m1 x1 Pr.
intros.
rewrite MfM.degree_aux_equation in |- *.
unfold m1 in |- *.
rewrite Mod.ndN_Tr in |- *.
set (dy := MfM.degree m y) in |- *.
set (dx := MfM.degree m x) in |- *.
fold dy in MAX.
fold dx in MAX.
elim (Arith.Compare_dec.le_lt_dec MAX (ndN m)).
 intro.
   elim (eq_dart_dec y 
       (Iter (MfM.f (Mod.Tr m x y)) MAX y)).
   tauto.
 intro.
   elim b.
   unfold MAX in |- *; unfold dy in |- *;
  unfold dx in |- *.
   symmetry  in |- *.
   apply f_Tr_x.
   tauto.
  tauto.
  tauto.
  tauto.
  tauto.
generalize (MfM.degree_sum_bound m x y H H0 H1 H2).
  fold dx in |- *.
  fold dy in |- *.
  fold MAX in |- *.
  rewrite Nat.add_comm in |- *.
  fold MAX in |- *.
  intros.
   lia.
Qed.

(* OK: *)

Lemma degree_Tr_merge_aux: 
 forall(m:fmap)(x y:dart)(n:nat),    
  Mod.Prec_Tr m x y ->
   let m1 := Mod.Tr m x y in
   let MAX:= MfM.degree m y + MfM.degree m x in
  inv_hmap m -> exd m x -> exd m y -> 
   ~MfM.expo m x y -> 1 <= MAX - n ->
      MfM.degree_aux m1 y (MAX - n) = MAX.
Proof.
induction n.
 intro Pr.
   intros.
   assert (MAX - 0 = MAX).
   lia.
 rewrite H4 in |- *.
   unfold MAX in |- *.
   unfold m1 in |- *.
   apply degree_Tr_merge_MAX.
   tauto.
  tauto.
  tauto.
  tauto.
  tauto.
intro Pr.
  intros.
  rewrite MfM.degree_aux_equation in |- *.
  unfold m1 in |- *.
  rewrite Mod.ndN_Tr in |- *.
  simpl in |- *.
  elim (Arith.Compare_dec.le_lt_dec (MAX - S n) (ndN m)).
 intro.
   elim (eq_dart_dec y (Iter (MfM.f (Mod.Tr m x y))
   (MAX - S n) y)).
  intros.
    fold m1 in a0.
    set (i := MAX - S n) in |- *.
    fold i in a0.
    fold i in H3.
    simpl in |- *.
    intros.
    generalize (MfM.degree_lub m y H H1).
    simpl in |- *.
    intro.
    set (dx := MfM.degree m x) in |- *.
    fold dx in H4.
    fold dx in MAX.
    set (dy := MfM.degree m y) in |- *.
    fold dy in MAX.
    elim (Arith.Compare_dec.le_lt_dec i (dy - 1)).
   intro.
      absurd (Iter (MfM.f m1) i y = y).
    unfold m1 in |- *.
      apply (diff_y1_y_1 m x y).
      tauto.
     tauto.
     tauto.
     tauto.
     tauto.
    fold dy in |- *.
       lia.
   symmetry  in |- *.
      tauto.
  intro.
    elim (Arith.Compare_dec.le_lt_dec i (dy + (dx - 1))).
   intros.
      absurd (Iter (MfM.f m1) i y = y).
    unfold m1 in |- *.
      set (j := i - dy) in |- *.
      assert (i = dy + j).
     unfold j in |- *.
        lia.
    rewrite H5 in |- *.
      apply (diff_x1_x m x y j Pr H H0 H1 H2).
      fold dx in |- *.
      unfold MAX in a.
      unfold MAX in i.
      unfold i in H5.
       lia.
   symmetry  in |- *.
      tauto.
  intro.
    unfold i in b0.
    unfold i in |- *.
    unfold i in b.
    unfold MAX in |- *.
    unfold MAX in b0.
    unfold MAX in b.
     lia.
 intros.
   elim (Nat.eq_dec (MAX - S n) (ndN m)).
  intro.
    generalize (MfM.degree_sum_bound m x y H H0 H1 H2).
    unfold MAX in |- *.
    unfold MAX in a.
    unfold MAX in a0.
    intro.
    unfold MAX in H3.
     lia.
 intros.
   assert (MAX - S n + 1 = MAX - n).
   lia.
 rewrite H4 in |- *.
   unfold MAX in |- *.
   apply IHn.
   tauto.
  tauto.
  tauto.
  tauto.
 generalize (MfM.degree_sum_bound m x y H H0 H1 H2).
   intro.
   unfold MAX in b0.
   unfold MAX in H4.
   unfold MAX in a.
    tauto.
 unfold MAX in b0.
   unfold MAX in H4.
   unfold MAX in a.
    lia.
intro.
  generalize (MfM.degree_sum_bound m x y H H0 H1 H2).
  intro.
  unfold MAX in b.
  unfold MAX in H3.
  unfold MAX in |- *.
   lia.
Qed.

(* OK: *)

Theorem degree_Tr_merge_y: forall(m:fmap)(x y:dart), 
  Mod.Prec_Tr m x y ->
   let m1 := Mod.Tr m x y in
  inv_hmap m -> exd m x -> exd m y -> 
   ~MfM.expo m x y ->
      MfM.degree m1 y = 
        MfM.degree m y + MfM.degree m x.
Proof.
intros m x y Pr.
intros.
set (dx := MfM.degree m x) in |- *.
set (dy := MfM.degree m y) in |- *.
unfold m1 in |- *.
set (MAX := dy + dx) in |- *.
generalize 
 (degree_Tr_merge_aux m x y (MAX - 1) Pr H H0 H1 H2).
fold dx in |- *; fold dy in |- *; fold MAX in |- *.
intro.
unfold MfM.degree in |- *.
generalize (MfM.degree_lub m y H H1).
simpl in |- *.
fold dy in |- *.
intro.
assert (0 < MAX).
 unfold MAX in |- *.
    lia.
assert (MAX - (MAX - 1) = 1).
  lia.
rewrite H6 in H3.
  apply H3.
   lia.
Qed.

(* OK: *)

Lemma expo_Tr_x_y: forall(m:fmap)(x y:dart), 
 Mod.Prec_Tr m x y ->
   let m1:= Mod.Tr m x y in
 inv_hmap m -> exd m x -> exd m y ->
      MfM.expo m1 x y.
Proof.
intros.
unfold MfM.expo in |- *.
split.
 unfold m1 in |- *.
   generalize (Mod.exd_Tr m x y x).
    tauto.
split with 1.
  simpl in |- *.
  unfold m1 in |- *.
  rewrite Mod.f_Tr in |- *.
 elim (eq_dart_dec x x).
   tauto.
  tauto.
 tauto.
 tauto.
 tauto.
 tauto.
 tauto.
Qed.

(* OK (inv_hmap m1 COULD BE REMOVED) *)

Theorem degree_Tr_merge_x: forall(m:fmap)(x y:dart), 
  Mod.Prec_Tr m x y ->
   let m1 := Mod.Tr m x y in
  inv_hmap m -> exd m x -> exd m y -> 
  inv_hmap m1 ->
   ~MfM.expo m x y ->
      MfM.degree m1 x = 
        MfM.degree m x + MfM.degree m y.
Proof.
intros.
assert (MfM.expo m1 x y).
 apply (expo_Tr_x_y m x y H H0 H1 H2).
assert (MfM.degree m1 x = MfM.degree m1 y).
 generalize (MfM.expo_degree m1 x y).
   intros.
    tauto.
rewrite H6 in |- *.
  rewrite Nat.add_comm in |- *.
  unfold m1 in |- *.
  apply degree_Tr_merge_y.
  tauto.
 tauto.
 tauto.
 tauto.
 tauto.
Qed.

(*====================================================
       expo_Tr_CNS in THE CASE ~expo m x y (merge)
=====================================================*)

(* OK: *)

Lemma expo_Tr_y_z_merge: forall(m:fmap)(x y z:dart),
 Mod.Prec_Tr m x y ->
  let m1:= Mod.Tr m x y in
   inv_hmap m -> exd m x -> exd m y -> exd m z ->
     ~MfM.expo m x y -> 
        MfM.expo m y z -> MfM.expo m1 y z.
Proof.
intros m x y z Pr.
intros.
assert (MfM.expo1 m y z).
 generalize (MfM.expo_expo1 m y z).
    tauto.
unfold MfM.expo1 in H5.
  decompose [and] H5.
  clear H5.
  set (dy := MfM.Iter_upb m y) in |- *.
  fold dy in H7.
  assert (dy = MfM.degree m y).
 unfold dy in |- *.
   apply MfM.upb_eq_degree.
   tauto.
  tauto.
unfold MfM.expo in |- *.
  split.
 unfold m1 in |- *.
   generalize (Mod.exd_Tr m x y y).
    tauto.
elim H7.
  intros j Hj.
  decompose [and] Hj.
  clear Hj H7.
  split with j.
  unfold m1 in |- *.
  rewrite f_Tr_y_y_1 in |- *.
  tauto.
 tauto.
 tauto.
 tauto.
 tauto.
 tauto.
rewrite <- H5 in |- *.
   lia.
Qed.

(* OK: *)

Lemma expo_Tr_x_z_merge: forall(m:fmap)(x y z:dart),
 Mod.Prec_Tr m x y ->
  let m1:= Mod.Tr m x y in
   inv_hmap m -> exd m x -> exd m y -> exd m z ->
     ~MfM.expo m x y -> 
        MfM.expo m x z -> MfM.expo m1 x z.
Proof.
intros m x y z Pr.
intros.
set (dx := MfM.Iter_upb m x) in |- *.
assert (dx = MfM.degree m x).
 unfold dx in |- *.
   apply MfM.upb_eq_degree.
   tauto.
  tauto.
set (dy := MfM.Iter_upb m y) in |- *.
  assert (dy = MfM.degree m y).
 unfold dy in |- *.
   apply MfM.upb_eq_degree.
   tauto.
  tauto.
set (x1 := MfM.f m x) in |- *.
  assert (exd m x1).
 unfold x1 in |- *.
   generalize (MfM.exd_f m x).
    tauto.
set (y_1 := MfM.f_1 m y) in |- *.
  assert (MfM.expo m x1 x).
 apply MfM.expo_symm.
   tauto.
 unfold MfM.expo in |- *.
   unfold x1 in |- *.
   split.
   tauto.
 split with 1.
   simpl in |- *.
    tauto.
assert (MfM.expo m x1 z).
 apply MfM.expo_trans with x.
   tauto.
  tauto.
apply MfM.expo_trans with y.
 unfold m1 in |- *.
   unfold MfM.expo in |- *.
   split.
  generalize (Mod.exd_Tr m x y x).
     tauto.
 split with 1.
   simpl in |- *.
   rewrite Mod.f_Tr in |- *.
  elim (eq_dart_dec x x).
    tauto.
   tauto.
  tauto.
  tauto.
  tauto.
  tauto.
  tauto.
unfold m1 in |- *.
  unfold MfM.expo in |- *.
  split.
 generalize (Mod.exd_Tr m x y y).
    tauto.
assert (MfM.expo1 m x1 z).
 generalize (MfM.expo_expo1 m x1 z).
    tauto.
unfold MfM.expo1 in H10.
  elim H10.
  intros.
  clear H10.
  elim H12.
  intros j Hj.
  clear H12.
  decompose [and] Hj.
  clear Hj.
  assert 
   (MfM.Iter_upb m x1 = MfM.degree m x1).
 apply MfM.upb_eq_degree.
   tauto.
  tauto.
split with (dy + j).
  unfold dy in |- *.
  fold dy in |- *.
  rewrite H6 in |- *.
  rewrite f_Tr_x1_x in |- *.
 fold x1 in |- *.
    tauto.
 tauto.
 tauto.
 tauto.
 tauto.
 tauto.
assert (MfM.degree m x = MfM.degree m x1).
 apply MfM.expo_degree.
   tauto.
 apply MfM.expo_symm.
   tauto.
  tauto.
rewrite H14 in |- *.
  rewrite <- H13 in |- *.
   lia.
Qed.

(* OK: *)

Lemma f_Tr_zi: forall(m:fmap)(x y z:dart)(i:nat),
 Mod.Prec_Tr m x y ->
  let m1 := Mod.Tr m x y in
   inv_hmap m -> exd m x -> exd m y -> exd m z -> 
   ~MfM.expo m x y 
    -> ~MfM.expo m x z -> ~MfM.expo m y z -> 
      Iter (MfM.f m1) i z = Iter (MfM.f m) i z.
Proof.
intros m x y z i Pr.
intros.
induction i.
 simpl in |- *.
    tauto.
simpl in |- *.
  rewrite IHi in |- *.
  set (zi := Iter (MfM.f m) i z) in |- *.
  unfold m1 in |- *.
  rewrite Mod.f_Tr in |- *.
 elim (eq_dart_dec x zi).
  intro.
    elim H4.
    apply MfM.expo_symm.
    tauto.
  unfold MfM.expo in |- *.
    split.
    tauto.
  split with i.
    fold zi in |- *.
    symmetry  in |- *;  tauto.
 assert (Mod.M.f_1 = MfM.f_1).
   tauto.
 rewrite H6 in |- *.
   assert (Mod.M.f = MfM.f).
   tauto.
 rewrite H7 in |- *.
   clear H6 H7.
   elim (eq_dart_dec (MfM.f_1 m y) zi).
  intros.
    elim H5.
    assert (y = Iter (MfM.f m) 1 zi).
   simpl in |- *.
     rewrite <- a in |- *.
     rewrite MfM.f_f_1 in |- *.
     tauto.
    tauto.
    tauto.
  unfold zi in H6.
    rewrite <- MfM.Iter_comp in H6.
    apply MfM.expo_symm.
    tauto.
  rewrite H6 in |- *.
    unfold MfM.expo in |- *.
    split.
    tauto.
  split with (1 + i).
     tauto.
  tauto.
 tauto.
 tauto.
 tauto.
unfold zi in |- *.
  generalize (MfM.exd_Iter_f m i z).
   tauto.
unfold zi in |- *.
  generalize (MfM.exd_Iter_f m i z).
   tauto.
Qed.

Theorem expo_Tr_z_t_merge: 
 forall(m:fmap)(x y z t:dart),
  Mod.Prec_Tr m x y ->
   let m1 := Mod.Tr m x y in
    inv_hmap m -> exd m x -> exd m y -> exd m z ->
     ~MfM.expo m x y -> 
        ~MfM.expo m x z -> ~MfM.expo m y z ->
            MfM.expo m z t -> MfM.expo m1 z t.
Proof.
intros m x y z t Pr.
intros.
unfold MfM.expo in H6.
elim H6.
intros.
clear H6.
elim H8.
intros i Hi.
clear H8.
unfold MfM.expo in |- *.
split.
 unfold m1 in |- *.
   generalize (Mod.exd_Tr m x y z).
    tauto.
split with i.
  rewrite <- Hi in |- *.
  unfold m1 in |- *.
  apply (f_Tr_zi m x y z i Pr H H0 H1 H2 H3 H4 H5).
Qed.

(* RCP, OK: CAUTION! 
inv_hmap m AND inv_hmap m1 AS PREMISE: *)

Theorem expo_x_or_y_merge: forall(m:fmap)(x y z:dart),
 Mod.Prec_Tr m x y ->
 let m1 := Mod.Tr m x y in
   inv_hmap m -> exd m x -> exd m y -> exd m z ->
     ~MfM.expo m x y -> 
   inv_hmap m1 ->
      MfM.expo m1 y z -> 
        (MfM.expo m x z \/ MfM.expo m y z).
Proof.
intros m x y z Pr.
intros.
set (dx := MfM.degree m x) in |- *.
set (dy := MfM.degree m y) in |- *.
set (d1y := MfM.degree m1 y) in |- *.
assert (d1y = dy + dx).
 unfold dx in |- *.
   unfold dy in |- *.
   unfold d1y in |- *.
   unfold m1 in |- *.
   apply (degree_Tr_merge_y m x y Pr H H0 H1 H3).
assert (MfM.expo1 m1 y z).
 generalize (MfM.expo_expo1 m1 y z).
    tauto.
unfold MfM.expo1 in H7.
  intros.
  decompose [and] H7.
  clear H7.
  assert (MfM.Iter_upb m1 y = MfM.degree m1 y).
 apply MfM.upb_eq_degree.
   tauto.
 unfold m1 in |- *.
   generalize (Mod.exd_Tr m x y y).
    tauto.
assert (0 < dx).
 unfold dx in |- *.
   apply MfM.degree_pos.
    tauto.
assert (0 < dy).
 unfold dy in |- *.
   apply MfM.degree_pos.
    tauto.
elim H9.
  clear H9.
  intros i Hi.
  decompose [and] Hi.
  clear Hi.
  rewrite H7 in H9.
  fold d1y in H9.
  elim (Arith.Compare_dec.le_lt_dec i (dy - 1)).
 intros.
   right.
   unfold MfM.expo in |- *.
   split.
   tauto.
 split with i.
   symmetry  in |- *.
   rewrite <- H12 in |- *.
   unfold m1 in |- *.
   apply f_Tr_y_y_1.
   tauto.
  tauto.
  tauto.
  tauto.
  tauto.
 fold dy in |- *.
    tauto.
intro.
  left.
  set (j := i - dy) in |- *.
  set (x1 := MfM.f m x) in |- *.
  apply MfM.expo_trans with x1.
 unfold MfM.expo in |- *.
   split.
   tauto.
 split with 1.
   simpl in |- *.
   fold x1 in |- *;  tauto.
unfold MfM.expo in |- *.
  split.
 unfold x1 in |- *.
   generalize (MfM.exd_f m x).
    tauto.
split with j.
  symmetry  in |- *.
  rewrite <- H12 in |- *.
  unfold m1 in |- *.
  assert (i = dy + j).
 unfold j in |- *.
    lia.
rewrite H13 in |- *.
  unfold dy in |- *.
  unfold x1 in |- *.
  apply f_Tr_x1_x.
  tauto.
 tauto.
 tauto.
 tauto.
 tauto.
fold dx in |- *.
  unfold j in |- *.
  rewrite H6 in H9.
   lia.
Qed.

(* OK: *)

Lemma expo_z_t_merge: forall(m:fmap)(x y z t:dart),
 Mod.Prec_Tr m x y ->
 let m1:= Mod.Tr m x y in
   inv_hmap m -> exd m x -> exd m y -> exd m z ->
     ~MfM.expo m x y -> 
        ~MfM.expo m x z -> ~MfM.expo m y z ->
           MfM.expo m1 z t -> MfM.expo m z t.
Proof.
intros m x y z t Pr.
intros.
unfold MfM.expo in H6.
elim H6.
intros.
clear H6.
unfold MfM.expo in |- *.
split.
  tauto.
elim H8.
  intros i Hi.
  clear H8.
  split with i.
  rewrite <- 
    (f_Tr_zi m x y z i Pr H H0 H1 H2 H3 H4 H5) in |- *.
  fold m1 in |- *.
   tauto.
Qed.

(* OK!: *)

Theorem expo_Tr_merge_CNS: forall(m:fmap)(x y z t:dart),
 Mod.Prec_Tr m x y ->
  let m1:= Mod.Tr m x y in
    inv_hmap m -> exd m x -> exd m y -> exd m z ->
       inv_hmap m1 -> ~MfM.expo m x y -> 
    (MfM.expo m1 z t <->
        (MfM.expo m z t 
      \/ MfM.expo m x z /\ MfM.expo m y t
      \/ MfM.expo m x t /\ MfM.expo m y z)).
Proof.
intros m x y z t Pr.
intros.
split.
 intro.
   elim (MfM.expo_dec m z t).
   tauto.
 intro.
   right.
   elim (MfM.expo_dec m x z).
  elim (MfM.expo_dec m y t).
    tauto.
  intros.
    assert (~ MfM.expo m x t).
   intro.
     elim b.
     apply MfM.expo_trans with x.
    apply MfM.expo_symm.
      tauto.
     tauto.
    tauto.
  elim b.
    apply MfM.expo_symm.
    tauto.
  apply (expo_z_t_merge m x y t z).
    tauto.
   tauto.
   tauto.
   tauto.
  generalize (MfM.expo_exd m1 z t).
    unfold m1 in |- *.
    generalize (Mod.exd_Tr m x y t).
    unfold m1 in H3.
     tauto.
   tauto.
   tauto.
   tauto.
  fold m1 in |- *.
    apply MfM.expo_symm.
    tauto.
   tauto.
   tauto.
 intro.
   elim (MfM.expo_dec m y z).
  intro.
    elim (MfM.expo_dec m x t).
   intro.
      tauto.
  intro.
    assert (~ MfM.expo m y t).
   intro.
     elim b.
     apply MfM.expo_trans with y.
    apply MfM.expo_symm.
      tauto.
     tauto.
    tauto.
  elim b.
    apply MfM.expo_symm.
    tauto.
  apply (expo_z_t_merge m x y t z).
    tauto.
   tauto.
   tauto.
   tauto.
  generalize (MfM.expo_exd m1 z t).
    unfold m1 in |- *.
    generalize (Mod.exd_Tr m x y t).
    unfold m1 in H3.
     tauto.
   tauto.
   tauto.
   tauto.
  fold m1 in |- *.
    apply MfM.expo_symm.
    tauto.
   tauto.
   tauto.
 intro.
   elim b.
   apply (expo_z_t_merge m x y z t).
   tauto.
  tauto.
  tauto.
  tauto.
  tauto.
  tauto.
  tauto.
  tauto.
 fold m1 in |- *.
    tauto.
  tauto.
  tauto.
  tauto.
intros.
  assert (MfM.expo m1 x y).
 unfold m1 in |- *.
   unfold MfM.expo in |- *.
   split.
  generalize (Mod.exd_Tr m x y x).
     tauto.
 split with 1.
   simpl in |- *.
   rewrite Mod.f_Tr in |- *.
  elim (eq_dart_dec x x).
    tauto.
   tauto.
  tauto.
  tauto.
  tauto.
  tauto.
  tauto.
elim (MfM.expo_dec m x z).
 intro.
   assert (MfM.expo m1 x z).
  unfold m1 in |- *.
    apply 
  (expo_Tr_x_z_merge m x y z Pr H H0 H1 H2 H4 a).
 elim (MfM.expo_dec m y t).
  intro.
    assert (exd m t).
   generalize (MfM.expo_exd m y t).
      tauto.
  assert (MfM.expo m1 y t).
   apply 
  (expo_Tr_y_z_merge m x y t Pr H H0 H1 H8 H4 a0).
  apply MfM.expo_trans with y.
   apply MfM.expo_trans with x.
    apply MfM.expo_symm.
      tauto.
     tauto.
    tauto.
   tauto.
 intro.
   elim (MfM.expo_dec m x t).
  intro.
    assert (MfM.expo m1 x t).
   assert (exd m t).
    generalize (MfM.expo_exd m x t).
       tauto.
   apply 
  (expo_Tr_x_z_merge m x y t Pr H H0 H1 H8 H4 a0).
  apply MfM.expo_trans with x.
   apply MfM.expo_symm.
     tauto.
    tauto.
   tauto.
 intro.
   assert (MfM.expo m z t).
   tauto.
 elim b0.
   apply MfM.expo_trans with z.
   tauto.
  tauto.
  tauto.
  tauto.
intro.
  elim (MfM.expo_dec m x t).
 intro.
   assert (exd m t).
  generalize (MfM.expo_exd m x t).
     tauto.
 assert (MfM.expo m1 x t).
  unfold m1 in |- *.
    apply 
  (expo_Tr_x_z_merge m x y t Pr H H0 H1 H7 H4 a).
 elim (MfM.expo_dec m y z).
  intro.
    assert (MfM.expo m1 y z).
   unfold m1 in |- *.
     apply 
  (expo_Tr_y_z_merge m x y z Pr H H0 H1 H2 H4 a0).
  apply MfM.expo_trans with x.
   apply MfM.expo_symm.
     tauto.
   apply MfM.expo_trans with y.
     tauto.
    tauto.
   tauto.
 intro.
   assert (MfM.expo m z t).
   tauto.
 elim b.
   apply MfM.expo_trans with t.
   tauto.
 apply MfM.expo_symm.
   tauto.
  tauto.
  tauto.
intro.
  assert (MfM.expo m z t).
  tauto.
elim (MfM.expo_dec m y z).
 intro.
   assert (MfM.expo m1 y z).
  unfold m1 in |- *.
    apply 
  (expo_Tr_y_z_merge m x y z Pr H H0 H1 H2 H4 a).
 elim (MfM.expo_dec m y t).
  intro.
    assert (exd m t).
   generalize (MfM.expo_exd m y t).
      tauto.
  assert (MfM.expo m1 y t).
   unfold m1 in |- *.
     apply
 (expo_Tr_y_z_merge m x y t Pr H H0 H1 H9 H4 a0).
  apply MfM.expo_trans with y.
   apply MfM.expo_symm.
     tauto.
    tauto.
   tauto.
 intro.
   elim b1.
   apply MfM.expo_trans with z.
   tauto.
  tauto.
  tauto.
intro.
  unfold m1 in |- *.
  apply 
(expo_Tr_z_t_merge m x y z t Pr H H0 H1 H2 H4 b b1).
   tauto.
 tauto.
 tauto.
 tauto.
Qed.

(*=================================================
                  OTHER ORBITS
==================================================*)

(* FINALLY, THE OTHER ORBITS ARE INCHANGED: *)

(* OK: NICE PROOF! *)

Lemma not_expo_Tr_y: forall(m:fmap)(x y z:dart),
 Mod.Prec_Tr m x y ->
    inv_hmap m -> exd m x -> exd m y -> exd m z ->
 let m1:= Mod.Tr m x y in inv_hmap m1 ->
  ~MfM.expo m x y 
    -> ~MfM.expo m x z -> ~MfM.expo m y z -> 
         ~MfM.expo m1 y z.
Proof.
intros.
intro.
assert (MfM.expo1 m1 y z).
 generalize (MfM.expo_expo1 m1 y z).
    tauto.
unfold MfM.expo1 in H9.
  decompose [and] H9.
  clear H9.
  elim H11.
  intros i Hi.
  unfold m1 in Hi.
  clear H11.
  decompose [and] Hi.
  clear Hi.
  rewrite MfM.upb_eq_degree in H9.
 generalize (degree_Tr_merge_y m x y H H0 H1 H2 H5).
   set (dy1 := MfM.degree (Mod.Tr m x y) y) in |- *.
   intros.
   fold dy1 in H9.
   set (dy := MfM.degree m y) in |- *.
   set (dx := MfM.degree m x) in |- *.
   fold dy in H12.
   fold dx in H12.
   elim (Arith.Compare_dec.le_lt_dec i (dy - 1)).
  intro.
    elim H7.
    unfold MfM.expo in |- *.
    split.
    tauto.
  split with i.
    rewrite <- (f_Tr_y_y_1 m x y i) in |- *.
    tauto.
   tauto.
   tauto.
   tauto.
   tauto.
   tauto.
  fold dy in |- *.
     tauto.
 intro.
   set (j := i - dy) in |- *.
   assert (i = dy + j).
  unfold j in |- *.
     lia.
 set (x1 := MfM.f m x) in |- *.
   elim H6.
   apply MfM.expo_trans with x1.
  unfold MfM.expo in |- *.
    split.
    tauto.
  split with 1.
    simpl in |- *.
    fold x1 in |- *.
     tauto.
 unfold MfM.expo in |- *.
   split.
  unfold x1 in |- *.
    generalize (MfM.exd_f m x).
     tauto.
 split with j.
   unfold x1 in |- *.
   rewrite <- (f_Tr_x1_x m x y j) in |- *.
  fold dy in |- *.
    rewrite <- H13 in |- *.
     tauto.
  tauto.
  tauto.
  tauto.
  tauto.
  tauto.
 fold dx in |- *.
    lia.
fold m1 in |- *.
   tauto.
generalize (Mod.exd_Tr m x y y).
   tauto.
Qed.

(* CORROLLARY: OK: *)

Lemma not_expo_Tr_x: forall(m:fmap)(x y z:dart),
 Mod.Prec_Tr m x y ->
    inv_hmap m -> exd m x -> exd m y -> exd m z ->
 let m1:= Mod.Tr m x y in inv_hmap m1 ->
  ~MfM.expo m x y 
    -> ~MfM.expo m x z -> ~MfM.expo m y z -> 
         ~MfM.expo m1 x z.
Proof.
intros.
generalize (not_expo_Tr_y m x y z H H0 H1 H2 H3 H4 H5 H6 H7).
intro.
fold m1 in H8.
generalize (expo_Tr_x_y m x y H H0 H1 H2).
fold m1 in |- *.
intro.
intro.
elim H8.
apply MfM.expo_trans with x.
 apply MfM.expo_symm.
   tauto.
  tauto.
 tauto.
Qed.

(* OK: *)

Lemma Iter_f_Tr_i: forall(m:fmap)(x y z:dart)(i:nat),
 Mod.Prec_Tr m x y ->
    inv_hmap m -> exd m x -> exd m y -> exd m z ->
 let m1:= Mod.Tr m x y in inv_hmap m1 ->
  ~MfM.expo m x y 
    -> ~MfM.expo m x z -> ~MfM.expo m y z -> 
         Iter (MfM.f m1) i z = Iter (MfM.f m) i z.
Proof.
intros.
induction i.
 simpl in |- *.
    tauto.
simpl in |- *.
  rewrite IHi in |- *.
  set (zi := Iter (MfM.f m) i z) in |- *.
  unfold m1 in |- *.
  rewrite Mod.f_Tr in |- *.
 elim (eq_dart_dec x zi).
  intro.
    rewrite a in H6.
    elim H6.
    apply MfM.expo_symm.
    tauto.
  unfold MfM.expo in |- *.
    split.
    tauto.
  split with i.
    fold zi in |- *.
     tauto.
 elim (eq_dart_dec (Mod.M.f_1 m y) zi).
  intros.
    elim H7.
    apply MfM.expo_trans with zi.
   rewrite <- a in |- *.
     apply MfM.expo_symm.
     tauto.
   unfold MfM.expo in |- *.
     split.
    generalize (Mod.M.exd_f_1 m y).
       tauto.
   split with 1.
     simpl in |- *.
     rewrite MfM.f_f_1 in |- *.
     tauto.
    tauto.
    tauto.
  apply MfM.expo_symm.
    tauto.
  unfold MfM.expo in |- *.
    split.
    tauto.
  split with i.
    fold zi in |- *.
     tauto.
  tauto.
 tauto.
 tauto.
 tauto.
 tauto.
unfold zi in |- *.
  generalize (MfM.exd_Iter_f m i z).
   tauto.
Qed.

(* OK: *)

Theorem expo_Tr_eq:forall(m:fmap)(x y z t:dart),
Mod.Prec_Tr m x y ->
    inv_hmap m -> exd m x -> exd m y -> 
 let m1:= Mod.Tr m x y in inv_hmap m1 ->
  ~MfM.expo m x y 
    -> ~MfM.expo m x z -> ~MfM.expo m y z -> 
         (MfM.expo m1 z t <-> MfM.expo m z t).
Proof.
intros.
split.
 unfold m1 in |- *.
   unfold MfM.expo in |- *.
   intros.
   decompose [and] H7.
   split.
  generalize (Mod.exd_Tr m x y z).
     tauto.
 elim H9.
   intros i Hi.
   split with i.
   rewrite <-
 (Iter_f_Tr_i m x y z i H H0 H1 H2) in |- *.
   tauto.
 generalize (Mod.exd_Tr m x y z).
    tauto.
 fold m1 in |- *.
    tauto.
  tauto.
  tauto.
  tauto.
unfold MfM.expo in |- *.
  intros.
  decompose [and] H7.
  split.
 generalize (Mod.exd_Tr m x y z).
    tauto.
elim H9.
  intros i Hi.
  split with i.
  unfold m1 in |- *.
  rewrite (Iter_f_Tr_i m x y z i H H0 H1 H2) in |- *.
  tauto.
generalize (Mod.exd_Tr m x y z).
   tauto.
fold m1 in |- *.
   tauto.
 tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma expo_impl_expo_Tr:forall(m:fmap)(x y z t:dart),
Mod.Prec_Tr m x y ->
    inv_hmap m -> exd m x -> exd m y -> 
 let m1:= Mod.Tr m x y in inv_hmap m1 ->
  ~MfM.expo m x y 
    -> ~MfM.expo m x z -> ~MfM.expo m y t -> 
    MfM.expo m z t -> MfM.expo m1 z t.
Proof.
intros.
assert (~ MfM.expo m y z).
 intro.
   elim H6.
   apply MfM.expo_trans with z.
   tauto.
  tauto.
generalize (expo_Tr_eq m x y z t H H0 H1 H2 H3 H4 H5).
   tauto.
Qed.

(* AUXILIARY TECHNICAL RESULT, OK: *)

Lemma degree_Tr_merge_x_others_aux: 
  forall(m:fmap)(x y z:dart)(n:nat), 
Mod.Prec_Tr m x y ->
    inv_hmap m -> exd m x -> exd m y -> exd m z ->
  let m1:= Mod.Tr m x y in 
  let dz:= MfM.degree m z in 
 inv_hmap m1 ->
  ~MfM.expo m x y -> 
   ~MfM.expo m x z -> ~MfM.expo m y z -> n < dz ->
  MfM.degree_aux m1 z (dz - n) = 
        MfM.degree_aux m z (dz - n).
Proof.
induction n.
 intros.
   rename H8 into dzp.
   assert (dz - 0 = dz).
   lia.
 rewrite H8 in |- *.
   rewrite MfM.degree_aux_equation in |- *.
   unfold m1 in |- *.
   rewrite Mod.ndN_Tr in |- *.
   fold m1 in |- *.
   rewrite (MfM.degree_aux_equation m z dz) in |- *.
   elim (Arith.Compare_dec.le_lt_dec dz (ndN m)).
  elim (eq_dart_dec z (Iter (MfM.f m1) dz z)).
   intros.
     unfold m1 in a.
     elim (eq_dart_dec z (Iter (MfM.f m) dz z)).
     tauto.
   intro.
     rewrite Iter_f_Tr_i in a.
     tauto.
    tauto.
    tauto.
    tauto.
    tauto.
    tauto.
   fold m1 in |- *.
      tauto.
    tauto.
    tauto.
    tauto.
  clear H8.
    elim (eq_dart_dec z (Iter (MfM.f m) dz z)).
   intros.
     unfold m1 in b.
     rewrite Iter_f_Tr_i in b.
     tauto.
    tauto.
    tauto.
    tauto.
    tauto.
    tauto.
   fold m1 in |- *.
      tauto.
    tauto.
    tauto.
    tauto.
  intros.
    elim (Nat.eq_dec dz (ndN m)).
    tauto.
  intro.
    generalize (MfM.degree_lub m z).
    simpl in |- *.
    fold dz in |- *.
    intro.
    elim b.
    symmetry  in |- *.
     tauto.
  tauto.
intros.
  rename H8 into dzp.
  rewrite MfM.degree_aux_equation in |- *.
  unfold m1 in |- *.
  rewrite Mod.ndN_Tr in |- *.
  rewrite
 (MfM.degree_aux_equation m z (dz - S n)) in |- *.
  elim (Arith.Compare_dec.le_lt_dec (dz - S n) (ndN m)).
 rewrite Iter_f_Tr_i in |- *.
  elim (eq_dart_dec z (Iter (MfM.f m) (dz - S n) z)).
    tauto.
  elim (Nat.eq_dec (dz - S n) (ndN m)).
    tauto.
  intros.
    assert (dz - S n + 1 = dz - n).
   assert (dz <> S n).
    intro.
      rewrite H8 in b.
      simpl in b.
       lia.
    lia.
  rewrite H8 in |- *.
    apply IHn.
    tauto.
   tauto.
   tauto.
   tauto.
   tauto.
  fold m1 in |- *.
     tauto.
   tauto.
   tauto.
   tauto.
  fold dz in |- *.
     lia.
  tauto.
  tauto.
  tauto.
  tauto.
  tauto.
 fold m1 in |- *.
    tauto.
  tauto.
  tauto.
  tauto.
 tauto.
Qed.

(* OK! *)

Theorem degree_Tr_merge_others: 
  forall(m:fmap)(x y z:dart), 
Mod.Prec_Tr m x y ->
    inv_hmap m -> exd m x -> exd m y -> exd m z ->
  let m1:= Mod.Tr m x y in 
  let dz:= MfM.degree m z in 
 inv_hmap m1 ->
  ~MfM.expo m x y -> 
   ~MfM.expo m x z -> ~MfM.expo m y z -> 
     MfM.degree m1 z = MfM.degree m z.
Proof.
intros.
unfold MfM.degree in |- *.
unfold m1 in |- *.
generalize (MfM.degree_lub m z).
simpl in |- *.
intro.
assert (0 < dz).
 unfold m1 in H.
   simpl in H.
    tauto.
assert (1 = dz - (dz - 1)).
  lia.
rewrite H10 in |- *.
  unfold dz in |- *.
  apply degree_Tr_merge_x_others_aux.
 fold m1 in |- *.
    tauto.
 tauto.
 tauto.
 tauto.
 tauto.
fold m1 in |- *.
   tauto.
 tauto.
 tauto.
 tauto.
fold dz in |- *.
   lia.
Qed.

(* OK: *)

Lemma expo_Tr_x: forall (m:fmap)(x y z:dart),
Mod.Prec_Tr m x y ->
    inv_hmap m -> exd m x -> exd m y -> exd m z ->
  let m1:= Mod.Tr m x y in 
 inv_hmap m1 ->
   ~MfM.expo m x y -> 
      MfM.expo m x z -> MfM.expo m1 x z. 
Proof.
intros.
set (x1 := MfM.f m x) in |- *.
assert (MfM.expo m x x1).
 unfold MfM.expo in |- *.
   split.
   tauto.
 split with 1.
   simpl in |- *.
   fold x1 in |- *.
    tauto.
rename H7 into Exx1.
  assert (MfM.expo m x1 z).
 apply MfM.expo_trans with x.
  apply MfM.expo_symm.
    tauto.
   tauto.
  tauto.
assert (MfM.expo1 m x1 z).
 generalize (MfM.expo_expo1 m x1 z).
    tauto.
unfold MfM.expo1 in H8.
  set (dx := MfM.Iter_upb m x) in |- *.
  fold dx in H8.
  elim H8.
  clear H8.
  intros.
  elim H9.
  clear H9; intros j Hj.
  elim Hj.
  clear Hj; intros.
  assert (dx = MfM.Iter_upb m x1).
 unfold dx in |- *.
   apply MfM.period_expo.
   tauto.
  tauto.
rewrite <- H11 in H9.
  set (dy := MfM.degree m y) in |- *.
  generalize (expo_Tr_x_y m x y H H0 H1 H2).
  fold m1 in |- *.
  intro.
  apply MfM.expo_trans with y.
  tauto.
unfold MfM.expo in |- *.
  split.
 unfold m1 in |- *.
   generalize (Mod.exd_Tr m x y y).
    tauto.
split with (dy + j).
  unfold m1 in |- *.
  unfold dy in |- *.
  rewrite f_Tr_x1_x in |- *.
 fold x1 in |- *.
    tauto.
 tauto.
 tauto.
 tauto.
 tauto.
 tauto.
fold dx in |- *.
  rewrite <- MfM.upb_eq_degree in |- *.
 fold dx in |- *.
    lia.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma expo_Tr_y: forall (m:fmap)(x y z:dart),
Mod.Prec_Tr m x y ->
    inv_hmap m -> exd m x -> exd m y -> exd m z ->
  let m1:= Mod.Tr m x y in 
 inv_hmap m1 ->
   ~MfM.expo m x y -> 
      MfM.expo m y z -> MfM.expo m1 y z. 
Proof.
intros.
assert (MfM.expo1 m y z).
 generalize (MfM.expo_expo1 m y z).
    tauto.
unfold MfM.expo1 in H7.
  set (dy := MfM.Iter_upb m y) in |- *.
  fold dy in H7.
  elim H7.
  clear H7.
  intros.
  clear H7.
  elim H8.
  clear H8.
  intros i Hi.
  elim Hi.
  clear Hi.
  intros.
  unfold MfM.expo in |- *.
  split.
 unfold m1 in |- *.
   generalize (Mod.exd_Tr m x y y).
    tauto.
split with i.
  unfold m1 in |- *.
  rewrite f_Tr_y_y_1 in |- *.
  tauto;  tauto.
 tauto.
 tauto.
 tauto.
 tauto.
 tauto.
rewrite <- MfM.upb_eq_degree in |- *.
 fold dy in |- *.
    lia.
 tauto.
 tauto.
Qed.

(* OK: *)

Theorem degree_Tr_merge_summary: 
forall (m:fmap)(x y z:dart)(H:inv_hmap m),
  Mod.Prec_Tr m x y ->
  exd m x -> exd m y -> exd m z ->
  let m1:= Mod.Tr m x y in
  let dx:= MfM.degree m x in
  let dy:= MfM.degree m y in
  inv_hmap m1 ->
   ~MfM.expo m x y -> 
     MfM.degree m1 z =
      if MfM.expo_dec m x z H then dx + dy
      else if MfM.expo_dec m y z H then dx + dy
           else MfM.degree m z.
Proof.
intros.
elim (MfM.expo_dec m x z H).
 intro.
   assert (MfM.expo m1 x z).
  unfold m1 in |- *.
    apply expo_Tr_x.
    tauto.
   tauto.
   tauto.
   tauto.
   tauto.
  fold m1 in |- *.
     tauto.
   tauto.
   tauto.
 rewrite (MfM.expo_degree m1 z x) in |- *.
  unfold dx in |- *.
    unfold dy in |- *.
    unfold m1 in |- *.
    apply degree_Tr_merge_x.
    tauto.
   tauto.
   tauto.
   tauto.
  fold m1 in |- *.
     tauto.
   tauto.
  tauto.
 apply MfM.expo_symm.
   tauto.
  tauto.
elim (MfM.expo_dec m y z).
 intros.
   unfold m1 in |- *.
   assert (MfM.expo m1 y z).
  generalize (expo_Tr_y_z_merge m x y z H0 H H1 H2 H3).
     tauto.
 unfold dx in |- *.
   unfold dy in |- *.
   fold m1 in |- *.
   rewrite (MfM.expo_degree m1 z y) in |- *.
  unfold m1 in |- *.
    rewrite Nat.add_comm in |- *.
    apply degree_Tr_merge_y.
    tauto.
   tauto.
   tauto.
   tauto.
   tauto.
  tauto.
 apply MfM.expo_symm.
   tauto.
  tauto.
intros.
  unfold m1 in |- *.
  apply degree_Tr_merge_others.
  tauto.
 tauto.
 tauto.
 tauto.
 tauto.
fold m1 in |- *.
   tauto.
 tauto.
 tauto.
tauto.
Qed.

(*=====================================================
             2. CASE: expo m x y (split)
=====================================================*)

(* CAUTION: *)

Theorem f_Tr_Id: forall(m:fmap)(x y z:dart),
 Mod.Prec_Tr m x y -> 
  inv_hmap m -> exd m x -> exd m y -> exd m z ->
   MfM.f m x = y -> MfM.f (Mod.Tr m x y) z = MfM.f m z.
Proof.
intros m x y z Pr.
intros.
rewrite Mod.f_Tr in |- *.
 elim (eq_dart_dec x z).
  intro.
    rewrite <- a in |- *.
    symmetry  in |- *.
     tauto.
 assert (MfM.f = Mod.M.f).
   tauto.
 assert (MfM.f_1 = Mod.M.f_1).
   tauto.
 rewrite <- H4 in |- *; rewrite <- H5 in |- *.
   elim (eq_dart_dec (MfM.f_1 m y) z).
  intros.
    rewrite <- a in |- *.
    rewrite MfM.f_f_1 in |- *.
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

Theorem Iter_f_Tr_Id: 
 forall(m:fmap)(x y z:dart)(i:nat),
Mod.Prec_Tr m x y ->
 inv_hmap m -> exd m x -> exd m y -> exd m z ->
   MfM.f m x = y -> 
    Iter (MfM.f (Mod.Tr m x y)) i z = 
         Iter (MfM.f m) i z.
Proof.
induction i.
 simpl in |- *.
    tauto.
intro Pr.
intros.
  simpl in |- *.
  rewrite IHi in |- *.
 rewrite f_Tr_Id in |- *.
   tauto.
  tauto.
  tauto.
 tauto.
  tauto.
 generalize (MfM.exd_Iter_f m i z).
    tauto.
  tauto.
 tauto.
 tauto.
 tauto.
 tauto.
 tauto.
tauto.
Qed.

(* OK: CASE (f m x = y) ELIMINATED FIRST: *)

Lemma f_Tr_y_x:forall(m:fmap)(x y:dart)(i j:nat),
 Mod.Prec_Tr m x y ->
  inv_hmap m -> exd m x -> exd m y ->
   let m1 := Mod.Tr m x y in
   let dy := MfM.degree m y in
  y = Iter (MfM.f m) j x ->
    (0 < j /\ j + i <= dy) ->
       Iter (MfM.f m1) i y = Iter (MfM.f m) i y.
Proof.
intros m x y i j Pr.
intros.
unfold m1 in |- *.
elim (Nat.eq_dec j dy).
 intro.
   assert (i = 0).
   lia.
 rewrite H4 in |- *.
   simpl in |- *.
    tauto.
intro.
  induction i.
 simpl in |- *.
    tauto.
simpl in |- *.
  rewrite IHi in |- *.
 unfold m1 in |- *.
   rewrite Mod.f_Tr in |- *.
  set (yi := Iter (MfM.f m) i y) in |- *.
    elim (eq_dart_dec x yi).
   intro.
     clear IHi.
     rewrite a in H2.
     unfold yi in H2.
     rewrite <- MfM.Iter_comp in H2.
     assert (0 = j + i).
    apply (MfM.degree_unicity m y 0 (j + i)).
      tauto.
     tauto.
    fold dy in |- *.
       lia.
    fold dy in |- *.
       lia.
    simpl in |- *.
       tauto.
    absurd (0 = j + i).
     lia.
    tauto.
  elim (eq_dart_dec (Mod.M.f_1 m y) yi).
   intros.
     clear IHi.
     assert (y = Iter (MfM.f m) (S i) y).
    simpl in |- *.
      fold yi in |- *.
      rewrite <- a in |- *.
      rewrite MfM.f_f_1 in |- *.
      tauto.
     tauto.
     tauto.
   assert (0 = S i).
    apply (MfM.degree_unicity m y 0 (S i)).
      tauto.
     tauto.
    fold dy in |- *.
       lia.
    fold dy in |- *.
       lia.
    simpl in |- *.
      simpl in H4.
       tauto.
   inversion H5.
   tauto.
  tauto.
  tauto.
  tauto.
  tauto.
 generalize (MfM.exd_Iter_f m i y).
    tauto.
 lia.
Qed.

Lemma diff_f_Tr_y_x:forall(m:fmap)(x y:dart)(i j:nat),
Mod.Prec_Tr m x y -> inv_hmap m -> exd m x -> exd m y ->
   let m1:= Mod.Tr m x y in
   let dy:= MfM.degree m y in
  y = Iter (MfM.f m) j x ->
    (0 < j /\ j + i <= dy /\ 0 < i) ->
       Iter (MfM.f m1) i y <> y.
Proof.
intros m x y i j Pr.
intros.
unfold m1 in |- *.
rewrite (f_Tr_y_x m x y i j Pr H H0 H1 H2) in |- *.
 generalize (MfM.degree_lub m y H H1).
   simpl in |- *.
   fold dy in |- *.
   intro.
   decompose [and] H4.
   clear H4.
   apply H8.
    lia.
fold dy in |- *.
   tauto.
Qed.

Lemma f_Tr_y_split:forall(m:fmap)(x y:dart)(j:nat),
 Mod.Prec_Tr m x y ->
  inv_hmap m -> exd m x -> exd m y ->
   let m1:= Mod.Tr m x y in
   let dy:= MfM.degree m y in
  y = Iter (MfM.f m) j x -> 
   (0 < j <= dy) ->
     Iter (MfM.f m1) (S (dy - j)) y = y.
Proof.
intros m x y j Pr.
intros.
simpl in |- *.
unfold m1 in |- *.
rewrite (f_Tr_y_x m x y (dy - j) j Pr H H0 H1 H2) in |- *.
 assert (dy = MfM.degree m x).
  unfold dy in |- *.
    apply MfM.expo_degree.
    tauto.
  apply MfM.expo_symm.
    tauto.
  unfold MfM.expo in |- *; split.
    tauto.
  split with j.
    symmetry  in |- *.
     tauto.
 assert (Iter (MfM.f m) (dy - j) y = x).
  rewrite H2 in |- *.
    rewrite <- MfM.Iter_comp in |- *.
    assert (dy - j + j = dy).
    lia.
  rewrite H5 in |- *.
    rewrite H4 in |- *.
    apply MfM.degree_per.
    tauto.
   tauto.
 rewrite H5 in |- *.
   rewrite Mod.f_Tr in |- *.
  elim (eq_dart_dec x x).
    tauto.
   tauto.
  tauto.
  tauto.
  tauto.
  tauto.
 tauto.
fold dy in |- *.
   lia.
Qed.

(* OK: CASE (f m x = y) ELIMINATED FIRST *)

Lemma f_Tr_x1_y_1:forall(m:fmap)(x y:dart)(i j:nat),
 Mod.Prec_Tr m x y ->
  inv_hmap m -> exd m x -> exd m y ->
   let m1:= Mod.Tr m x y in
   let dy:= MfM.degree m y in
   let x1:= MfM.f m x in
  y = Iter (MfM.f m) j x ->
    (i + 2 <= j <= dy) ->
      Iter (MfM.f m1) i x1 = Iter (MfM.f m) i x1.
Proof.
 intros m x y i j Pr.
intros.
assert (MfM.expo m x y).
 unfold MfM.expo in |- *; split.
   tauto.
 split with j.
   symmetry  in |- *.
    tauto.
assert (MfM.degree m x = dy).
 unfold dy in |- *.
   apply (MfM.expo_degree m x y).
   tauto.
  tauto.
assert (MfM.degree m x = MfM.degree m x1).
 apply MfM.expo_degree.
   tauto.
 assert (exd m x1).
  unfold x1 in |- *.
    generalize (MfM.exd_f m x).
     tauto.
 unfold x1 in |- *.
   unfold MfM.expo in |- *.
   split.
   tauto.
 split with 1.
   simpl in |- *.
    tauto.
elim (eq_dart_dec (MfM.f m x) y).
 intro.
   unfold m1 in |- *.
   rewrite Iter_f_Tr_Id in |- *.
   tauto.
  tauto.
  tauto.
  tauto.
  tauto.
 unfold x1 in |- *.
   generalize (MfM.exd_f m x).
    tauto.
  tauto.
intro.
  induction i.
 simpl in |- *.
    tauto.
simpl in |- *.
  rewrite IHi in |- *.
 clear IHi.
   unfold m1 in |- *.
   rewrite Mod.f_Tr in |- *.
  elim (eq_dart_dec x (Iter (MfM.f m) i x1)).
   intro.
     assert (x1 = Iter (MfM.f m) 1 x).
    simpl in |- *.
      fold x1 in |- *.
       tauto.
   rewrite H7 in a.
     rewrite <- MfM.Iter_comp in a.
     assert (0 = i + 1).
    apply (MfM.degree_unicity m x 0 (i + 1)).
      tauto.
     tauto.
    rewrite H5 in |- *.
       lia.
    rewrite H5 in |- *.
       lia.
    simpl in |- *.
       tauto.
    absurd (0 = i + 1).
     lia.
    tauto.
  elim (eq_dart_dec (Mod.M.f_1 m y)
         (Iter (MfM.f m) i x1)).
   intros.
     assert (y = Iter (MfM.f m) (S i) x1).
    simpl in |- *.
      rewrite <- a in |- *.
      rewrite MfM.f_f_1 in |- *.
      tauto.
     tauto.
     tauto.
   rewrite H7 in H2.
     assert (x1 = Iter (MfM.f m) 1 x).
    simpl in |- *.
      fold x1 in |- *.
       tauto.
   rewrite H8 in H2.
     rewrite <- MfM.Iter_comp in H2.
     elim (Nat.eq_dec j dy).
    intro.
      rewrite <- H5 in a0.
      rewrite a0 in H2.
      rewrite MfM.degree_per in H2.
     assert (S i + 1 = 0).
      apply (MfM.degree_unicity m x (S i + 1) 0).
        tauto.
       tauto.
      rewrite H5 in |- *.
         lia.
      rewrite H5 in |- *.
         lia.
      rewrite H2 in |- *.
        simpl in |- *.
         tauto.
      absurd (S i + 1 = 0).
       lia.
      tauto.
     tauto.
     tauto.
   intro.
     assert (S i + 1 = j).
    apply (MfM.degree_unicity m x (S i + 1) j).
      tauto.
     tauto.
    rewrite H5 in |- *.
       lia.
    rewrite H5 in |- *.
       lia.
     tauto.
    absurd (S i + 1 = j).
     lia.
    tauto.
   tauto.
  tauto.
  tauto.
  tauto.
  tauto.
 generalize (MfM.exd_Iter_f m i x1).
   unfold x1 in |- *.
   generalize (MfM.exd_f m x).
    tauto.
 lia.
Qed.

(* OK: *)

Lemma diff_x1_y_1:forall(m:fmap)(x y:dart)(i j:nat),
 Mod.Prec_Tr m x y ->
  inv_hmap m -> exd m x -> exd m y ->
   let m1:= Mod.Tr m x y in
   let dy:= MfM.degree m y in
   let x1:= MfM.f m x in
  y = Iter (MfM.f m) j x ->
    (i + 2 <= j <= dy /\ 0 < i) ->
      Iter (MfM.f m1) i x1 <> x1.
Proof.
intros m x y i j Pr.
intros.
unfold m1 in |- *.
unfold x1 in |- *.
rewrite (f_Tr_x1_y_1 m x y i j Pr H H0 H1 H2) in |- *.
 assert (MfM.expo m y x1).
  apply MfM.expo_trans with x.
   apply MfM.expo_symm.
     tauto.
   unfold MfM.expo in |- *.
     split.
     tauto.
   split with j.
     symmetry  in |- *.
      tauto.
  unfold MfM.expo in |- *.
    unfold x1 in |- *.
    split.
    tauto.
  split with 1.
    simpl in |- *.
     tauto.
 assert (dy = MfM.degree m x1).
  unfold dy in |- *.
    apply MfM.expo_degree.
    tauto.
   tauto.
 assert (exd m x1).
  unfold x1 in |- *.
    generalize (MfM.exd_f m x).
     tauto.
 generalize (MfM.degree_lub m x1 H H6).
   simpl in |- *.
   intro.
   decompose [and] H7.
   clear H7.
   apply H11.
   rewrite <- H5 in |- *.
    lia.
fold dy in |- *.
   lia.
Qed.

Lemma f_Tr_x1_split:forall(m:fmap)(x y:dart)(j:nat),
 Mod.Prec_Tr m x y ->
  inv_hmap m -> exd m x -> exd m y ->
   let m1:= Mod.Tr m x y in
   let dy:= MfM.degree m y in
   let x1:= MfM.f m x in
  y = Iter (MfM.f m) j x ->
    (2 <= j <= dy) ->
      Iter (MfM.f m1) (j - 1) x1 = x1.
Proof.
intros m x y j Pr.
intros.
assert (j - 1 = S (j - 2)).
  lia.
rewrite H4 in |- *.
  simpl in |- *.
  unfold m1 in |- *.
  unfold x1 in |- *.
  rewrite (f_Tr_x1_y_1 m x y (j - 2) j Pr) in |- *.
 assert (Iter (MfM.f m) (j - 2)
    (MfM.f m x) = MfM.f_1 m y).
  clear H4.
    rewrite H2 in |- *.
    assert (MfM.f m x = Iter (MfM.f m) 1 x).
   simpl in |- *.
      tauto.
  rewrite H4 in |- *.
    rewrite <- MfM.Iter_comp in |- *.
    assert (j - 2 + 1 = j - 1).
    lia.
  rewrite H5 in |- *.
    clear H5.
    rewrite <- MfM.Iter_f_f_1 in |- *.
   simpl in |- *.
      tauto.
   tauto.
   tauto.
   lia.
 rewrite H5 in |- *.
   rewrite Mod.f_Tr in |- *.
  elim (eq_dart_dec x (MfM.f_1 m y)).
   intro.
     rewrite a in |- *.
     rewrite MfM.f_f_1 in |- *.
     tauto.
    tauto.
    tauto.
  elim (eq_dart_dec (Mod.M.f_1 m y) (MfM.f_1 m y)).
    tauto.
   tauto.
  tauto.
  tauto.
  tauto.
 tauto.
 generalize (MfM.exd_f_1 m y).
    tauto.
 tauto.
 tauto.
 tauto.
 tauto.
fold dy in |- *.
   lia.
Qed.

(* OK: *)

Lemma f_Tr_x1_y_1_bis:forall(m:fmap)(x y:dart)(i j:nat),
 Mod.Prec_Tr m x y ->
  inv_hmap m -> exd m x -> exd m y ->
   let m1:= Mod.Tr m x y in
   let dy:= MfM.degree m y in
   let x1:= MfM.f m x in
  y = Iter (MfM.f m) j x ->
    (i + 2 <= j <= dy) ->
      Iter (MfM.f m1) i x1 =
         Iter (MfM.f m) (dy - j + 1 + i) y.
Proof.
intros m x y i j Pr.
intros.
assert (MfM.expo m x y).
 unfold MfM.expo in |- *; split.
   tauto.
 split with j.
   symmetry  in |- *.
    tauto.
assert (MfM.degree m x = dy).
 unfold dy in |- *.
   apply (MfM.expo_degree m x y).
   tauto.
  tauto.
assert (MfM.degree m x = MfM.degree m x1).
 apply MfM.expo_degree.
   tauto.
 assert (exd m x1).
  unfold x1 in |- *.
    generalize (MfM.exd_f m x).
     tauto.
 unfold x1 in |- *.
   unfold MfM.expo in |- *.
   split.
   tauto.
 split with 1.
   simpl in |- *.
    tauto.
cut (Iter (MfM.f m1) i x1 = Iter (MfM.f m) i x1).
 intro.
   rewrite H7 in |- *.
   assert (x1 = Iter (MfM.f m) (dy - j + 1) y).
  rewrite H2 in |- *.
    rewrite <- MfM.Iter_comp in |- *.
    assert (dy - j + 1 + j = S dy).
    lia.
  rewrite H8 in |- *.
    simpl in |- *.
    rewrite <- H5 in |- *.
    rewrite MfM.degree_per in |- *.
   fold x1 in |- *.
      tauto.
   tauto.
   tauto.
 rewrite H8 in |- *.
   rewrite <- MfM.Iter_comp in |- *.
   assert (i + (dy - j + 1) = dy - j + 1 + i).
   lia.
 rewrite H9 in |- *.
    tauto.
unfold m1 in |- *.
  unfold x1 in |- *.
  apply (f_Tr_x1_y_1 m x y i j Pr H H0 H1 H2 H3).
Qed.

(* OK!: *)

Lemma degree_Tr_split_y_aux:
 forall(m:fmap)(x y:dart)(j i:nat), 
 Mod.Prec_Tr m x y ->
  inv_hmap m -> exd m x -> exd m y -> 
   let m1:= Mod.Tr m x y in
   let dy:= MfM.degree m y in
  y = Iter (MfM.f m) j x -> 
   (0 < j /\ j + i < dy) ->
      MfM.degree_aux m1 y ((dy - j) - i) = dy - j + 1.
Proof.
intros m x y j i Pr.
intros.
assert (exd m x).
  tauto.
rename H4 into H5.
  assert (MfM.expo m x y).
 unfold MfM.expo in |- *.
   split.
   tauto.
 split with j.
   symmetry  in |- *.
    tauto.
generalize (MfM.degree_bound m y H H1).
  intro.
  fold dy in H6.
  induction i.
 unfold m1 in |- *.
   assert (dy - j - 0 = dy - j).
   lia.
 rewrite H7 in |- *.
   clear H7.
   rewrite MfM.degree_aux_equation in |- *.
   rewrite Mod.ndN_Tr in |- *.
   elim (Arith.Compare_dec.le_lt_dec (dy - j) (ndN m)).
  intro.
    elim (eq_dart_dec y 
       (Iter (MfM.f (Mod.Tr m x y)) (dy - j) y)).
   intro.
     symmetry  in a0.
  absurd (Iter (MfM.f (Mod.Tr m x y)) (dy - j) y = y).
    apply (diff_f_Tr_y_x m x y (dy - j) j Pr).
      tauto.
     tauto.
     tauto.
     tauto.
    fold dy in |- *.
      split.
     clear a H6.
        lia.
    clear a H6.
       lia.
    tauto.
  elim (Nat.eq_dec (dy - j) (ndN m)).
   intros.
     rewrite a0 in |- *.
      tauto.
  intros.
    rewrite MfM.degree_aux_equation in |- *.
    rewrite Mod.ndN_Tr in |- *.
    elim (Arith.Compare_dec.le_lt_dec (dy - j + 1) (ndN m)).
   intro.
     elim (eq_dart_dec y 
      (Iter (MfM.f (Mod.Tr m x y)) (dy - j + 1) y)).
     tauto.
   intro.
     elim b1.
     symmetry  in |- *.
     assert (dy - j + 1 = S (dy - j)).
    clear a b H6 a0.
       lia.
   rewrite H7 in |- *.
     clear H7.
     unfold dy in |- *.
     rewrite f_Tr_y_split in |- *.
     tauto.
    tauto.
    tauto.
    tauto.
    tauto.
   tauto.
   fold dy in |- *.
     clear a b a0.
      lia.
  intros.
    clear H3 H6.
     lia.
 intro.
    lia.
unfold m1 in |- *.
  rewrite MfM.degree_aux_equation in |- *.
  rewrite Mod.ndN_Tr in |- *.
  elim (Arith.Compare_dec.le_lt_dec (dy - j - S i) (ndN m)).
 intro.
   elim (eq_dart_dec y 
       (Iter (MfM.f (Mod.Tr m x y)) (dy - j - S i) y)).
  intros.
    symmetry  in a0.
absurd 
  (Iter (MfM.f (Mod.Tr m x y)) (dy - j - S i) y = y).
   apply (diff_f_Tr_y_x m x y (dy - j - S i) j Pr).
     tauto.
    tauto.
    tauto.
    tauto.
   fold dy in |- *.
     split.
     tauto.
   split.
     lia.
   clear H6 a a0.
      lia.
   tauto.
 elim (Nat.eq_dec (dy - j - S i) (ndN m)).
  intros.
     absurd (dy - j - S i = ndN m).
    lia.
   tauto.
 intros.
   assert (dy - j - S i + 1 = dy - j - i).
  clear a b H6.
     lia.
 rewrite H7 in |- *.
   apply IHi.
   clear H7.
   clear a b H6.
   split.
   tauto.
  lia.
intro.
   absurd (ndN m < dy - j - S i).
  lia.
 tauto.
Qed.

(* OK: *)

Lemma degree_Tr_split_y:
 forall(m:fmap)(x y:dart)(j:nat), 
 Mod.Prec_Tr m x y ->
  inv_hmap m -> exd m x -> exd m y -> 
   let m1:= Mod.Tr m x y in
   let dy:= MfM.degree m y in
  y = Iter (MfM.f m) j x -> 
   (0 < j <= dy) ->
      MfM.degree m1 y = dy - j + 1.
Proof.
intros m x y j Pr.
intros.
assert (exd m x).
  tauto.
rename H4 into H5.
assert (MfM.expo m x y).
 unfold MfM.expo in |- *.
   split.
   tauto.
 split with j.
   symmetry  in |- *.
    tauto.
elim (Nat.eq_dec j dy).
 intro.
   unfold m1 in |- *.
   assert (MfM.expo m x y).
  unfold MfM.expo in |- *.
    split.
    tauto.
  split with j.
    symmetry  in |- *.
     tauto.
 assert (MfM.degree m x = dy).
  unfold dy in |- *.
    apply MfM.expo_degree.
    tauto.
   tauto.
 assert (y = x).
  rewrite H2 in |- *.
    rewrite a in |- *.
    rewrite <- H7 in |- *.
    rewrite MfM.degree_per in |- *.
    tauto.
   tauto.
   tauto.
 unfold MfM.degree in |- *.
   rewrite MfM.degree_aux_equation in |- *.
   rewrite Mod.ndN_Tr in |- *.
   elim (Arith.Compare_dec.le_lt_dec 1 (ndN m)).
  intro.
    elim (eq_dart_dec y 
    (Iter (MfM.f (Mod.Tr m x y)) 1 y)).
   simpl in |- *.
     intro.
     rewrite a in |- *.
      lia.
  intro.
    elim b.
    simpl in |- *.
    rewrite Mod.f_Tr in |- *.
   elim (eq_dart_dec x y).
     tauto.
   rewrite H8 in |- *.
      tauto.
   tauto.
   tauto.
   tauto.
   tauto.
   tauto.
 intro.
   rewrite a in |- *.
    lia.
intro.
  unfold m1 in |- *.
  unfold MfM.degree in |- *.
  unfold dy in |- *.
  assert (1 = dy - j - (dy - j - 1)).
  lia.
assert
 (MfM.degree_aux (Mod.Tr m x y) y 1 =
   MfM.degree_aux (Mod.Tr m x y) y 
      (dy - j - (dy - j - 1))).
 rewrite <- H6 in |- *.
    tauto.
rewrite H7 in |- *.
  unfold dy in |- *.
  apply (degree_Tr_split_y_aux m x y j
      (MfM.degree m y - j - 1) Pr).
  tauto.
 tauto.
 tauto.
 tauto.
fold dy in |- *.
  clear H6.
  split.
  tauto.
 lia.
Qed.

(* OK, CASE j = 2 DIRECTLY CONSIDERED AFTERWARDS: *)

Lemma degree_Tr_split_x1_aux:
 forall(m:fmap)(x y:dart)(j i:nat), 
 Mod.Prec_Tr m x y ->
  inv_hmap m -> exd m x -> exd m y -> 
   let m1:= Mod.Tr m x y in
   let dy:= MfM.degree m y in
   let x1:= MfM.f m x in
  y = Iter (MfM.f m) j x -> 
    (i + 2 < j <= dy) ->
      MfM.degree_aux m1 x1 ((j - 2) - i) = j - 1.
Proof.
intros m x y j i Pr.
intros.
assert (exd m x).
tauto.
rename H4 into H5.
assert (MfM.expo m x y).
 unfold MfM.expo in |- *.
   split.
   tauto.
 split with j.
   symmetry  in |- *.
    tauto.
generalize (MfM.degree_bound m y H H1).
  intro.
  fold dy in H6.
  induction i.
 unfold m1 in |- *.
   assert (j - 2 - 0 = j - 2).
   lia.
 rewrite H7 in |- *.
   clear H7.
   simpl in H3.
   assert (MfM.expo m x x1).
  unfold x1 in |- *.
    unfold MfM.expo in |- *.
    split.
   auto.
  split with 1.
    simpl in |- *.
     tauto.
 assert (MfM.expo m x y).
  unfold MfM.expo in |- *.
    split.
    tauto.
  split with j.
    symmetry  in |- *.
     tauto.
 assert (MfM.expo m x1 y).
  apply MfM.expo_trans with x.
   apply MfM.expo_symm.
     tauto.
    tauto.
   tauto.
 assert (MfM.degree m x1 = dy).
  unfold dy in |- *.
    apply (MfM.expo_degree m x1 y H H9).
 rewrite MfM.degree_aux_equation in |- *.
   rewrite Mod.ndN_Tr in |- *.
   elim (Arith.Compare_dec.le_lt_dec (j - 2) (ndN m)).
  intro.
    elim (eq_dart_dec x1 
         (Iter (MfM.f (Mod.Tr m x y)) (j - 2) x1)).
   intro.
     symmetry  in a0.
 absurd (Iter (MfM.f (Mod.Tr m x y)) (j - 2) x1 = x1).
    unfold x1 in |- *.
      apply (diff_x1_y_1 m x y (j - 2) j Pr).
      tauto.
     tauto.
     tauto.
     tauto.
    fold dy in |- *.
      split.
      lia.
     lia.
    tauto.
  elim (Nat.eq_dec (j - 2) (ndN m)).
   intros.
      lia.
  intros.
    rewrite MfM.degree_aux_equation in |- *.
    rewrite Mod.ndN_Tr in |- *.
    elim (Arith.Compare_dec.le_lt_dec (j - 2 + 1) (ndN m)).
   intro.
     elim (eq_dart_dec x1 
      (Iter (MfM.f (Mod.Tr m x y)) (j - 2 + 1) x1)).
    intros.
       lia.
   intros.
     elim b1.
     symmetry  in |- *.
     assert (j - 2 + 1 = j - 1).
     lia.
   rewrite H11 in |- *.
     clear H11.
     unfold x1 in |- *.
     apply f_Tr_x1_split.
     tauto.
    tauto.
    tauto.
    tauto.
    tauto.
   fold dy in |- *.
      lia.
  intros.
     absurd (ndN m < j - 2 + 1).
    lia.
   tauto.
 intros.
    absurd (ndN m < j - 2).
   lia.
  tauto.
unfold m1 in |- *.
  rewrite MfM.degree_aux_equation in |- *.
  rewrite Mod.ndN_Tr in |- *.
  elim (Arith.Compare_dec.le_lt_dec (j - 2 - S i) (ndN m)).
 intro.
   elim (eq_dart_dec x1
      (Iter (MfM.f (Mod.Tr m x y)) (j - 2 - S i) x1)).
  intros.
    symmetry  in a0.
  absurd (Iter (MfM.f (Mod.Tr m x y)) 
        (j - 2 - S i) x1 = x1).
   apply (diff_x1_y_1 m x y (j - 2 - S i) j Pr).
     tauto.
    tauto.
    tauto.
    tauto.
   fold dy in |- *.
     split.
    split.
     clear a H6.
        lia.
     tauto.
   clear a a0 H6.
      lia.
   tauto.
 elim (Nat.eq_dec (j - 2 - S i) (ndN m)).
  intros.
     absurd (j - 2 - S i = ndN m).
   clear b a0 a.
      lia.
   tauto.
 intros.
   assert (j - 2 - S i + 1 = j - 2 - i).
  clear b0 b a H6.
     lia.
 rewrite H7 in |- *.
   apply IHi.
   clear a b H7.
   split.
   lia.
  tauto.
intro.
   absurd (ndN m < j - 2 - S i).
 clear b.
    lia.
 tauto.
Qed.

(* OK, CASE j = 2 ALSO CONSIDERED: *)

Lemma degree_Tr_split_x1:
 forall(m:fmap)(x y:dart)(j:nat), 
 Mod.Prec_Tr m x y ->
  inv_hmap m -> exd m x -> exd m y -> 
   let m1:= Mod.Tr m x y in
   let dy:= MfM.degree m y in
   let x1:= MfM.f m x in
  y = Iter (MfM.f m) j x -> 
    (2 <= j <= dy) -> 
      MfM.degree m1 x1 = j - 1.
Proof.
intros m x y j Pr.
intros.
assert (exd m x).
tauto.
rename H4 into H5.
assert (MfM.expo m x y).
 unfold MfM.expo in |- *.
   split.
   tauto.
 split with j.
   symmetry  in |- *.
    tauto.
elim (Nat.eq_dec j 2).
 intros.
   rename a into j2.
   rewrite j2 in |- *.
   assert (2 - 1 = 1).
   lia.
 rewrite H6 in |- *.
   clear H6.
   rewrite j2 in H2.
   unfold m1 in |- *.
   unfold MfM.degree in |- *.
   rewrite MfM.degree_aux_equation in |- *.
   rewrite Mod.ndN_Tr in |- *.
   elim (Arith.Compare_dec.le_lt_dec 1 (ndN m)).
  intro.
    elim
 (eq_dart_dec x1 (Iter (MfM.f (Mod.Tr m x y)) 1 x1)).
    tauto.
  intro.
    simpl in b.
    rewrite Mod.f_Tr in b.
   generalize b.
     clear b.
     elim (eq_dart_dec x x1).
    intros.
      simpl in H2.
      fold x1 in H2.
      rewrite <- a0 in H2.
      fold x1 in H2.
      symmetry  in H2.
       tauto.
   elim (eq_dart_dec (Mod.M.f_1 m y) x1).
    intros.
      unfold x1 in b0.
       tauto.
   intros.
     rewrite H2 in b.
     simpl in b.
     rewrite MfM.f_1_f in b.
    fold x1 in b.
       tauto.
    tauto.
   generalize (MfM.exd_f m x).
      tauto.
   tauto.
   tauto.
   tauto.
  tauto.
  unfold x1 in |- *.
    generalize (MfM.exd_f m x).
     tauto.
 intros.
    lia.
intro j2.
  unfold MfM.degree in |- *.
  unfold x1 in |- *.
  assert (1 = j - 2 - (j - 3)).
  lia.
assert (MfM.degree_aux m1 (MfM.f m x) 1 =
     MfM.degree_aux m1 (MfM.f m x) (j - 2 - (j - 3))).
 rewrite <- H6 in |- *.
    tauto.
rewrite H7 in |- *.
  unfold m1 in |- *.
  apply degree_Tr_split_x1_aux.
  tauto.
 tauto.
 tauto.
 tauto.
 tauto.
fold dy in |- *.
   lia.
Qed.

(* OK: CASE J = 1: *)

Theorem degree_Tr_split_1_aux:
 forall(m:fmap)(x:dart)(k:nat), 
  inv_hmap m -> exd m x -> 
   let y:= MfM.f m x in 
  Mod.Prec_Tr m x y ->
   let m1:= Mod.Tr m x y in
   let dy:= MfM.degree m y in
    k < dy ->
     MfM.degree_aux m1 y (dy - k) = dy. 
Proof.
intros m x k H H0 y Pr.
intros.
rename H1 into kdy.
assert (exd m y).
 unfold y in |- *.
   generalize (MfM.exd_f m x).
    tauto.
assert (0 < dy).
 unfold dy in |- *.
   apply MfM.degree_pos.
    tauto.
generalize (MfM.degree_bound m y H H1).
  intro.
  induction k.
 assert (dy - 0 = dy).
   lia.
 rewrite H4 in |- *.
   clear H4.
   rewrite MfM.degree_aux_equation in |- *.
   unfold m1 in |- *.
   rewrite Mod.ndN_Tr in |- *.
   elim (Arith.Compare_dec.le_lt_dec dy (ndN m)).
  elim 
 (eq_dart_dec y (Iter (MfM.f (Mod.Tr m x y)) dy y)).
    tauto.
  elim (Nat.eq_dec dy (ndN m)).
   rewrite Iter_f_Tr_Id in |- *.
    unfold dy in |- *.
      rewrite MfM.degree_per in |- *.
      tauto.
     tauto.
     tauto.
    tauto.
    tauto.
    tauto.
    tauto.
   tauto.
   fold y in |- *.
      tauto.
  rewrite Iter_f_Tr_Id in |- *.
   unfold dy in |- *.
     rewrite MfM.degree_per in |- *.
     tauto.
    tauto.
    tauto.
   tauto.
   tauto.
   tauto.
   tauto.
   tauto.
  fold y in |- *.
     tauto.
 intro.
   fold dy in H3.
    lia.
rewrite MfM.degree_aux_equation in |- *.
  unfold m1 in |- *.
  rewrite Mod.ndN_Tr in |- *.
  elim (Arith.Compare_dec.le_lt_dec (dy - S k) (ndN m)).
 elim (eq_dart_dec y (Iter (MfM.f (Mod.Tr m x y))
     (dy - S k) y)).
  intros.
    fold dy in H3.
    rewrite Iter_f_Tr_Id in a.
   assert (dy - S k = 0).
    rewrite (MfM.degree_unicity m y (dy - S k) 0)
      in |- *.
      tauto.
     tauto.
     tauto.
    fold dy in |- *.
       lia.
    fold dy in |- *.
       tauto.
    simpl in |- *.
      symmetry  in |- *.
       tauto.
    absurd (dy - S k = 0).
     lia.
    tauto.
   tauto.
   tauto.
   tauto.
   tauto.
  tauto.
  fold y in |- *.
     tauto.
 elim (Nat.eq_dec (dy - S k) (ndN m)).
  intros.
     absurd (dy - S k = ndN m).
   fold dy in H3.
      lia.
   tauto.
 intros.
   fold m1 in |- *.
   assert (dy - S k + 1 = dy - k).
   lia.
 rewrite H4 in |- *.
   clear H4.
   apply IHk.
    lia.
intro.
  fold dy in H3.
   lia.
Qed.

(* CASE j = 1: Tr m x y WITHOUT EFFECT: *)

Theorem degree_Tr_split_1:
 forall(m:fmap)(x:dart), 
  inv_hmap m -> exd m x -> 
   let y:= MfM.f m x in 
  Mod.Prec_Tr m x y ->
   let m1:= Mod.Tr m x y in
     MfM.degree m1 y = MfM.degree m y. 
Proof.
intros m x H H0 y Pr.
assert (exd m y).
 unfold y in |- *.
   generalize (MfM.exd_f m x).
    tauto.
set (dy := MfM.degree m y) in |- *.
  assert (exd m y).
 unfold y in |- *.
   generalize (MfM.exd_f m x).
    tauto.
assert (0 < dy).
 unfold dy in |- *.
   apply MfM.degree_pos.
    tauto.
   simpl.
  unfold MfM.degree in |- *.
  assert (dy - (dy - 1) = 1).
  lia.
rewrite <- H4 in |- *.
  unfold dy in |- *.
  unfold y in |- *.
  apply degree_Tr_split_1_aux.
  tauto.
 tauto.
fold y in |- *.
  tauto.
  fold y.
  fold dy in |- *.
   lia.
Qed.

(* THE GREAT RESULT: *)

Theorem degree_Tr_split:
 forall(m:fmap)(x y:dart)(j:nat), 
  inv_hmap m -> exd m x -> exd m y -> 
   let m1:= Mod.Tr m x y in
   let x1:= MfM.f m x in
   let dy := MfM.degree m y in
  y = Iter (MfM.f m) j x -> 
  Mod.Prec_Tr m x y -> 2 <= j <= dy ->
   MfM.degree m1 y + MfM.degree m1 x1 = 
    MfM.degree m y. 
Proof.
intros.
unfold m1 in |- *.
unfold x1 in |- *.
fold dy in |- *.
rewrite (degree_Tr_split_x1 m x y j H3) in |- *.
 rewrite (degree_Tr_split_y m x y j H3) in |- *.
  fold dy in |- *.
     lia.
  tauto.
  tauto.
  tauto.
  tauto.
 fold dy in |- *.
    lia.
 tauto.
 tauto.
 tauto.
 tauto.
fold dy in |- *.
   tauto.
Qed.

(*=====================================================
           expo / Tr (CASE expo m x y) (SPLIT)
          OUTSIDE ORBIT OF x (= ORBIT Of y) 
=====================================================*)

(* OUTSIDE ORBIT OF x OR ORBIT OF y: *)

Lemma expo_not_orbit_y_aux: 
 forall (m:fmap)(x y z:dart)(i:nat),
  Mod.Prec_Tr m x y ->
  inv_hmap m -> exd m x -> exd m y -> exd m z ->
    let t:= Iter (MfM.f m) i z in
  MfM.expo m x y -> 
    ~ MfM.expo m y z -> 
         MfM.expo (Mod.Tr m x y) z t.
Proof.
intros m x y z i Pr.
intros.
induction i.
 simpl in |- *.
   intros.
   simpl in t.
   unfold t in |- *.
   apply MfM.expo_refl.
   generalize (Mod.exd_Tr m x y z).
    tauto.
unfold t in |- *.
  simpl in |- *.
  apply MfM.expo_trans with (Iter (MfM.f m) i z).
 apply IHi.
unfold MfM.expo in |- *.
  split.
 generalize (Mod.exd_Tr m x y (Iter (MfM.f m) i z)).
   generalize (MfM.exd_Iter_f m i z).
    tauto.
split with 1.
  simpl in |- *.
  rewrite Mod.f_Tr in |- *.
 elim (eq_dart_dec x (Iter (MfM.f m) i z)).
  intro.
    elim H4.
    apply MfM.expo_trans with x.
   apply MfM.expo_symm.
     tauto.
    tauto.
  apply MfM.expo_symm.
    tauto.
  rewrite a in |- *.
    unfold MfM.expo in |- *.
    split.
    tauto.
  split with i.
     tauto.
 elim (eq_dart_dec (Mod.M.f_1 m y)
   (Iter (MfM.f m) i z)).
  intros.
    elim H4.
    assert (y = Iter (MfM.f m) (S i) z).
   simpl in |- *.
     rewrite <- a in |- *.
     rewrite MfM.f_f_1 in |- *.
     tauto.
    tauto.
    tauto.
  apply MfM.expo_symm.
    tauto.
  rewrite H5 in |- *.
    unfold MfM.expo in |- *.
    split.
    tauto.
  split with (S i).
     tauto.
  tauto.
 tauto.
 tauto.
 tauto.
  tauto.
generalize (MfM.exd_Iter_f m i z).
   tauto.
Qed.

Lemma expo_not_orbit_y: 
 forall (m:fmap)(x y z t:dart),
 Mod.Prec_Tr m x y ->
  inv_hmap m -> exd m x -> exd m y -> exd m z ->
  MfM.expo m x y -> 
    ~ MfM.expo m y z -> 
        MfM.expo m z t ->
          MfM.expo (Mod.Tr m x y) z t.
Proof.
intros m x y z t Pr.
intros.
unfold MfM.expo in H5.
elim H5.
clear H5.
intros.
elim H6.
clear H6.
intros i Hi.
rewrite <- Hi in |- *.
apply (expo_not_orbit_y_aux m x y z i Pr).
  tauto.
 tauto.
 tauto.
 tauto.
 tauto.
 tauto.
Qed.

Lemma expo_not_orbit_x: 
 forall (m:fmap)(x y z t:dart),
 Mod.Prec_Tr m x y ->
  inv_hmap m -> exd m x -> exd m y -> exd m z ->
  MfM.expo m x y -> 
    ~ MfM.expo m x z -> 
        MfM.expo m z t ->
          MfM.expo (Mod.Tr m x y) z t.
Proof.
intros m x y z t Pr.
intros.
assert (~ MfM.expo m y z).
 intro.
   elim H4.
   apply MfM.expo_trans with y.
   tauto.
  tauto.
apply expo_not_orbit_y.
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

Lemma Iter_f_Tr_split_i: 
 forall(m:fmap)(x y z:dart)(i:nat),
  Mod.Prec_Tr m x y ->
    inv_hmap m -> exd m x -> exd m y -> exd m z ->
 let m1:= Mod.Tr m x y in inv_hmap m1 ->
   MfM.expo m x y 
    -> ~MfM.expo m x z -> 
        Iter (MfM.f m1) i z = Iter (MfM.f m) i z.
Proof.
intros.
induction i.
 simpl in |- *.
    tauto.
simpl in |- *.
  rewrite IHi in |- *.
  set (zi := Iter (MfM.f m) i z) in |- *.
  unfold m1 in |- *.
  rewrite Mod.f_Tr in |- *.
 elim (eq_dart_dec x zi).
  intro.
    rewrite a in H6.
    elim H6.
    apply MfM.expo_symm.
    tauto.
  unfold MfM.expo in |- *.
    split.
    tauto.
  split with i.
    fold zi in |- *.
     tauto.
 intro.
   assert (~ MfM.expo m y z).
  intro.
    elim H6.
    apply MfM.expo_trans with y.
    tauto.
   tauto.
 elim (eq_dart_dec (Mod.M.f_1 m y) zi).
  intros.
    assert (y = Mod.M.f m zi).
   rewrite <- a in |- *.
     rewrite Mod.M.f_f_1 in |- *.
     tauto.
    tauto.
    tauto.
  elim H7.
    apply MfM.expo_symm.
    tauto.
  rewrite H8 in |- *.
    unfold zi in |- *.
    unfold MfM.expo in |- *.
    split.
    tauto.
  split with (S i).
    simpl in |- *.
     tauto.
  tauto.
 tauto.
 tauto.
 tauto.
 tauto.
unfold zi in |- *.
  generalize (MfM.exd_Iter_f m i z).
   tauto.
Qed.

(* OK: *)

Lemma degree_Tr_split_x_others_aux: 
  forall(m:fmap)(x y z:dart)(n:nat), 
Mod.Prec_Tr m x y ->
    inv_hmap m -> exd m x -> exd m y -> exd m z ->
  let m1:= Mod.Tr m x y in 
  let dz:= MfM.degree m z in 
 inv_hmap m1 ->
  MfM.expo m x y -> 
   ~MfM.expo m x z -> n < dz ->
  MfM.degree_aux m1 z (dz - n) = 
          MfM.degree_aux m z (dz - n).
Proof.
induction n.
 intros.
   assert (dz - 0 = dz).
   lia.
 rewrite H8 in |- *.
   rewrite MfM.degree_aux_equation in |- *.
   unfold m1 in |- *.
   rewrite Mod.ndN_Tr in |- *.
   fold m1 in |- *.
   rewrite (MfM.degree_aux_equation m z dz) in |- *.
   elim (Arith.Compare_dec.le_lt_dec dz (ndN m)).
  elim (eq_dart_dec z (Iter (MfM.f m1) dz z)).
   intros.
     unfold m1 in a.
     elim (eq_dart_dec z (Iter (MfM.f m) dz z)).
     tauto.
   intro.
     rewrite Iter_f_Tr_split_i in a.
     tauto.
    tauto.
    tauto.
    tauto.
    tauto.
    tauto.
   fold m1 in |- *.
      tauto.
    tauto.
    tauto.
  clear H8.
    elim (eq_dart_dec z (Iter (MfM.f m) dz z)).
   intros.
     unfold m1 in b.
     rewrite Iter_f_Tr_split_i in b.
     tauto.
    tauto.
    tauto.
    tauto.
    tauto.
    tauto.
   fold m1 in |- *.
      tauto.
    tauto.
    tauto.
  intros.
    elim (Nat.eq_dec dz (ndN m)).
    tauto.
  intro.
    generalize (MfM.degree_lub m z).
    simpl in |- *.
    fold dz in |- *.
    intro.
    elim b.
    symmetry  in |- *.
     tauto.
  tauto.
intros.
  rewrite MfM.degree_aux_equation in |- *.
  unfold m1 in |- *.
  rewrite Mod.ndN_Tr in |- *.
  rewrite
 (MfM.degree_aux_equation m z (dz - S n)) in |- *.
  elim (Arith.Compare_dec.le_lt_dec (dz - S n) (ndN m)).
 rewrite Iter_f_Tr_split_i in |- *.
  elim (eq_dart_dec z (Iter (MfM.f m) (dz - S n) z)).
    tauto.
  elim (Nat.eq_dec (dz - S n) (ndN m)).
    tauto.
  intros.
    assert (dz - S n + 1 = dz - n).
   assert (dz <> S n).
    intro.
      rewrite H8 in b.
      simpl in b.
       lia.
    lia.
  rewrite H8 in |- *.
    apply IHn.
    tauto.
   tauto.
   tauto.
   tauto.
   tauto.
  fold m1 in |- *.
     tauto.
   tauto.
   tauto.
  fold dz in |- *.
     lia.
  tauto.
  tauto.
  tauto.
  tauto.
  tauto.
 fold m1 in |- *.
    tauto.
  tauto.
  tauto.
 tauto.
Qed.

(* OK: *)

Theorem degree_Tr_split_others: 
  forall(m:fmap)(x y z:dart), 
Mod.Prec_Tr m x y ->
    inv_hmap m -> exd m x -> exd m y -> exd m z ->
  let m1:= Mod.Tr m x y in 
 inv_hmap m1 ->
  MfM.expo m x y -> 
   ~MfM.expo m x z -> 
     MfM.degree m1 z = MfM.degree m z.
Proof.
intros.
set (dz := MfM.degree m z) in |- *.
unfold MfM.degree in |- *.
unfold m1 in |- *.
generalize (MfM.degree_lub m z H0 H3).
simpl in |- *.
intro.
fold dz in H7.
assert (1 = dz - (dz - 1)).
  lia.
rewrite H8 in |- *.
  unfold dz in |- *.
  rewrite degree_Tr_split_x_others_aux in |- *.
 fold dz in |- *.
   rewrite <- H8 in |- *.
   unfold dz in |- *.
   unfold MfM.degree in |- *.
    tauto.
 tauto.
 tauto.
 tauto.
 tauto.
 tauto; fold m1 in |- *;  tauto.
fold m1 in |- *.
   tauto.
 tauto.
 tauto.
fold dz in |- *.
   lia.
Qed.

(* FINALLY: *)

Theorem degree_Tr_split_summary: 
forall (m:fmap)(x y z:dart)(j:nat)(H:inv_hmap m),
  Mod.Prec_Tr m x y ->
  exd m x -> exd m y -> exd m z ->
  let dy := MfM.degree m y in
  y = Iter (MfM.f m) j x -> 
  2 <= j <= dy ->
  let m1:= Mod.Tr m x y in
  let x1:= MfM.f m x in 
  inv_hmap m1 ->
    MfM.degree m z =
       if MfM.expo_dec m y z H 
       then MfM.degree m1 y + MfM.degree m1 x1
       else MfM.degree m1 z.
Proof.
intros.
assert (MfM.expo m x y).
 unfold MfM.expo in |- *.
   split.
   tauto.
 split with j.
   symmetry  in |- *.
    tauto.
elim (MfM.expo_dec m y z H).
 intros.
   assert (dy = MfM.degree m z).
  unfold dy in |- *.
    apply MfM.expo_degree.
    tauto.
   tauto.
 rewrite <- H8 in |- *.
   unfold dy in |- *.
   unfold m1 in |- *.
   unfold x1 in |- *.
   rewrite (degree_Tr_split m x y j) in |- *.
   tauto.
  tauto.
  tauto.
  tauto.
  tauto.
  tauto.
 fold dy in |- *.
    tauto.
intros.
  unfold m1 in |- *.
  rewrite degree_Tr_split_others in |- *.
  tauto.
 tauto.
 tauto.
 tauto.
 tauto.
 tauto.
fold m1 in |- *.
   tauto.
 tauto.
intro.
  elim b.
  apply MfM.expo_trans with x.
 apply MfM.expo_symm.
   tauto.
  tauto.
 tauto.
Qed.

(*=====================================================
             expo_Tr : PART 2 (Case expo x y) split
=====================================================*)

Definition dec (A:Prop):Set:= {A}+{~A}.

Lemma and_not : forall (A B : Prop),
  dec A -> dec B ->
   {A /\ ~ B } + {~ A \/ B}.
Proof.
unfold dec in |- *.
intros.
 tauto.
Qed.

(* SUFFICIENT CONDITION: OK! *)

Lemma expo_Tr_split_CS:forall (m:fmap)(x y z t:dart),
 Mod.Prec_Tr m x y ->
  inv_hmap m -> exd m x -> exd m y -> exd m z ->
  let x1 := MfM.f m x in
  let y_1 := MfM.f_1 m y in
  let m1:= Mod.Tr m x y in
  inv_hmap m1 -> MfM.expo m x y -> 
  ( MfM.between m y z x /\ MfM.between m y t x 
 \/ MfM.between m x1 z y_1 /\ MfM.between m x1 t y_1
 \/ ~ MfM.expo m x z /\ MfM.expo m z t ) ->
        MfM.expo m1 z t.
Proof.
intros m x y z t Pr.
intros.
rename H3 into Im1.
rename H4 into H3.
rename H5 into H4.
unfold m1 in |- *.
generalize (MfM.expo_dec m x z H).
generalize (MfM.expo_dec m z t H).
intros AA BB.
fold (dec (MfM.expo m z t)) in AA.
fold (dec (MfM.expo m x z)) in BB.
elim (and_not (MfM.expo m z t) (MfM.expo m x z) AA BB).
 intro.
   apply expo_not_orbit_x.
   tauto.
  tauto.
  tauto.
  tauto.
  tauto.
  tauto.
  tauto.
 tauto.
assert (MfM.expo1 m x y).
 generalize (MfM.expo_expo1 m x y).
    tauto.
rename H5 into Exy.
  unfold MfM.expo1 in Exy.
  elim Exy.
  clear Exy.
  intros Exy1.
  clear Exy1; intro Exy.
  elim Exy.
  clear Exy.
  intros j Exy.
  elim Exy.
  clear Exy.
  intros Ejx Exy.
  symmetry  in Exy.
  assert (MfM.Iter_upb m x = MfM.Iter_upb m y).
 rewrite Exy in |- *.
   apply MfM.period_uniform.
   tauto.
  tauto.
rename H5 into Equpb.
  intro.
  elim H4.
 clear H4.
   intro.
   unfold MfM.between in H4.
   decompose [and] H4.
   clear H4.
   generalize (H5 H H1).
   clear H5.
   intro.
   generalize (H6 H H1).
   clear H6.
   intro.
   elim H4.
   clear H4.
   intros iz Hz.
   elim Hz.
   clear Hz.
   intros jx Hx.
   decompose [and] Hx.
   clear Hx.
   elim H5.
   clear H5.
   intros it Ht.
   elim Ht.
   clear Ht.
   intros kx Hx.
   decompose [and] Hx.
   clear Hx.
   assert (jx = kx).
  apply (MfM.unicity_mod_p m y jx kx).
    tauto.
   tauto.
   tauto.
   tauto.
  rewrite H10 in |- *.
     tauto.
 elim (Nat.eq_dec j 0).
  intro.
    rewrite a in Exy.
    simpl in Exy.
    assert (jx = 0).
   rewrite (MfM.unicity_mod_p m y jx 0) in |- *.
     tauto.
    tauto.
    tauto.
    tauto.
    lia.
   simpl in |- *.
     rewrite H7 in |- *.
     symmetry  in |- *.
      tauto.
  assert (iz = 0).
    lia.
  assert (it = 0).
    lia.
  assert (z = t).
   rewrite H14 in H4.
     simpl in H4.
     rewrite H15 in H5.
     simpl in H5.
     rewrite <- H5 in |- *.
     symmetry  in |- *.
      tauto.
  rewrite <- H16 in |- *.
    apply MfM.expo_refl.
    generalize (Mod.exd_Tr m x y z).
     tauto.
 intro j0.
   apply MfM.expo_trans with y.
  apply MfM.expo_symm.
   fold m1 in |- *.
      tauto.
  unfold MfM.expo in |- *.
    split.
   generalize (Mod.exd_Tr m x y y).
      tauto.
  split with iz.
    rewrite (f_Tr_y_x m x y iz j Pr) in |- *.
    tauto.
   tauto.
   tauto.
   tauto.
   tauto.
  split.
    lia.
  assert (MfM.Iter_upb m y = MfM.degree m y).
   apply (MfM.upb_eq_degree m y H H1).
  assert (jx = MfM.degree m y - j).
   rewrite
 (MfM.degree_unicity m y jx (MfM.degree m y - j)) 
    in |- *.
     tauto.
    tauto.
    tauto.
    lia.
    lia.
   set (yj := Iter (MfM.f m) jx y) in |- *.
     set (dy := MfM.degree m y) in |- *.
     rewrite Exy in |- *.
     rewrite <- MfM.Iter_comp in |- *.
     assert (dy - j + j = dy).
    unfold dy in |- *.
       lia.
   rewrite H14 in |- *.
     clear H14.
     unfold dy in |- *.
     rewrite <- H13 in |- *.
     rewrite <- Equpb in |- *.
     rewrite MfM.Iter_upb_period in |- *.
    unfold yj in |- *.
       tauto.
    tauto.
    tauto.
   lia.
 unfold MfM.expo in |- *.
   split.
  generalize (Mod.exd_Tr m x y y).
     tauto.
 split with it.
   rewrite (f_Tr_y_x m x y it j Pr) in |- *.
   tauto.
  tauto.
  tauto.
  tauto.
  tauto.
 split.
   lia.
 assert (MfM.Iter_upb m y = MfM.degree m y).
  apply (MfM.upb_eq_degree m y H H1).
 assert (jx = MfM.degree m y - j).
  rewrite (MfM.degree_unicity m y jx 
      (MfM.degree m y - j)) in |- *.
    tauto.
   tauto.
   tauto.
   lia.
   lia.
  rewrite H7 in |- *.
    set (dy := MfM.degree m y) in |- *.
    rewrite Exy in |- *.
    rewrite <- MfM.Iter_comp in |- *.
    assert (dy - j + j = dy).
   unfold dy in |- *.
      lia.
  rewrite H14 in |- *.
    clear H14.
    unfold dy in |- *.
    rewrite <- H13 in |- *.
    rewrite <- Equpb in |- *.
    rewrite MfM.Iter_upb_period in |- *.
    tauto.
   tauto.
   tauto.
  lia.
clear H4.
  intro.
  assert (exd m x1).
 unfold x1 in |- *.
   generalize (MfM.exd_f m x).
    tauto.
rename H5 into Ex1.
  assert (MfM.expo m x1 y).
 apply MfM.expo_trans with x.
  apply MfM.expo_symm.
    tauto.
  unfold x1 in |- *.
    unfold MfM.expo in |- *.
    split.
    tauto.
  split with 1.
    simpl in |- *.
     tauto.
  tauto.
assert (MfM.Iter_upb m x1 = MfM.Iter_upb m y).
 apply MfM.period_expo.
   tauto.
  tauto.
assert (MfM.Iter_upb m y = MfM.degree m y).
 apply (MfM.upb_eq_degree m y H H1).
assert (MfM.Iter_upb m x1 = MfM.degree m x1).
 apply (MfM.upb_eq_degree m x1 H Ex1).
elim H4.
 clear H4.
   intro.
   unfold MfM.between in H4.
   decompose [and] H4.
   clear H4.
   generalize (H9 H Ex1).
   clear H9.
   intro.
   elim H4.
   intros iz Hz.
   clear H4.
   elim Hz.
   clear Hz.
   intros j1 Hj.
   decompose [and] Hj.
   clear Hj.
   generalize (H10 H Ex1).
   intro.
   clear H10.
   elim H12.
   clear H12.
   intros it Ht.
   elim Ht.
   clear Ht.
   intros j2 Hj.
   decompose [and] Hj.
   clear Hj.
   assert (j1 = j2).
  apply (MfM.unicity_mod_p m x1 j1 j2).
    tauto.
   tauto.
   tauto.
   tauto.
  rewrite H14 in |- *.
     tauto.
 elim (Nat.eq_dec j 1).
  intro.
    assert (y = MfM.f m x).
   rewrite Exy in |- *.
     simpl in |- *.
     rewrite a in |- *.
     simpl in |- *.
      tauto.
  apply MfM.expo_trans with x1.
   apply MfM.expo_symm.
    fold m1 in |- *.
       tauto.
   unfold MfM.expo in |- *.
     split.
    generalize (Mod.exd_Tr m x y x1).
       tauto.
   split with iz.
     rewrite Iter_f_Tr_Id in |- *.
     tauto.
    tauto.
    tauto.
    tauto.
    tauto.
    tauto.
   symmetry  in |- *.
      tauto.
  unfold MfM.expo in |- *.
    split.
   generalize (Mod.exd_Tr m x y x1).
      tauto.
  split with it.
    rewrite Iter_f_Tr_Id in |- *.
    tauto.
   tauto.
   tauto.
   tauto.
   tauto.
 tauto.
  symmetry  in |- *;  tauto.
 intro.
   elim (Nat.eq_dec j 0).
  intro.
    assert (y = x).
   rewrite Exy in |- *.
     rewrite a in |- *.
     simpl in |- *.
      tauto.
  elim (eq_dart_dec x1 y_1).
   intro.
     assert (j1 = 0).
    rewrite <- a0 in H11.
      apply (MfM.unicity_mod_p m x1 j1 0).
      tauto.
     tauto.
     tauto.
     lia.
    simpl in |- *.
       tauto.
   assert (iz = 0).
     lia.
   assert (it = 0).
     lia.
   rewrite H20 in H10.
     simpl in H10.
     rewrite H19 in H4.
     simpl in H4.
     rewrite <- H4 in |- *.
     rewrite <- H10 in |- *.
     apply MfM.expo_refl.
     generalize (Mod.exd_Tr m x y x1).
      tauto.
  intro.
    assert (1 <> MfM.Iter_upb m x1).
   intro.
     assert (j1 = 0).
     lia.
   rewrite H19 in H11.
     simpl in H11.
      tauto.
  assert (j1 = MfM.Iter_upb m x1 - 2).
   apply (MfM.unicity_mod_p m x1 j1 
     (MfM.Iter_upb m x1 - 2)).
     tauto.
    tauto.
    tauto.
    lia.
   rewrite <- MfM.Iter_f_f_1 in |- *.
    rewrite MfM.Iter_upb_period in |- *.
     simpl in |- *.
       unfold x1 in |- *.
       rewrite MfM.f_1_f in |- *.
      fold x1 in |- *.
        rewrite <- H17 in |- *.
        fold y_1 in |- *.
         tauto.
      tauto.
      tauto.
     tauto.
     tauto.
    tauto.
    tauto.
    lia.
  apply MfM.expo_trans with x1.
   apply MfM.expo_symm.
    fold m1 in |- *.
       tauto.
   unfold MfM.expo in |- *.
     split.
    generalize (Mod.exd_Tr m x y x1).
       tauto.
   split with iz.
     unfold x1 in |- *.
     rewrite
  (f_Tr_x1_y_1 m x y iz (MfM.degree m y) Pr) in |- *.
    fold x1 in |- *.
       tauto.
    tauto.
    tauto.
    tauto.
   rewrite <- H17 in |- *.
     rewrite MfM.degree_per in |- *.
     tauto.
    tauto.
    tauto.
    lia.
  unfold MfM.expo in |- *.
    split.
   generalize (Mod.exd_Tr m x y x1).
      tauto.
  split with it.
    unfold x1 in |- *.
    rewrite (f_Tr_x1_y_1 m x y it 
       (MfM.degree m y) Pr) in |- *.
   fold x1 in |- *.
      tauto.
   tauto.
   tauto.
   tauto.
  rewrite <- H17 in |- *.
    rewrite MfM.degree_per in |- *.
    tauto.
   tauto.
   tauto.
   lia.
 intro.
   assert (j1 = j - 2).
  apply (MfM.unicity_mod_p m x1 j1 (j - 2)).
    tauto.
   tauto.
   tauto.
   lia.
  rewrite H11 in |- *.
    assert (x1 = Iter (MfM.f m) 1 x).
   simpl in |- *.
      tauto.
  rewrite H17 in |- *.
    rewrite <- MfM.Iter_comp in |- *.
    assert (j - 2 + 1 = j - 1).
    lia.
  rewrite H18 in |- *.
    rewrite <- MfM.Iter_f_f_1 in |- *.
   rewrite <- Exy in |- *.
     simpl in |- *.
     fold y_1 in |- *.
      tauto.
   tauto.
   tauto.
   lia.
 apply MfM.expo_trans with x1.
  apply MfM.expo_symm.
   fold m1 in |- *.
      tauto.
  unfold MfM.expo in |- *.
    split.
   generalize (Mod.exd_Tr m x y x1).
      tauto.
  split with iz.
    unfold x1 in |- *.
    rewrite (f_Tr_x1_y_1 m x y iz j Pr) in |- *.
   fold x1 in |- *.
      tauto.
   tauto.
   tauto.
   tauto.
   tauto.
   lia.

 unfold MfM.expo in |- *.
   split.
  generalize (Mod.exd_Tr m x y x1).
     tauto.
 split with it.
   unfold x1 in |- *.
   rewrite (f_Tr_x1_y_1 m x y it j Pr) in |- *.
  fold x1 in |- *.
     tauto.
  tauto.
  tauto.
  tauto.
  tauto.
  lia.
intro.
   tauto.
Qed.

(* NECESSARY CONDITION: *)

(* FIRST: OK *)

Lemma expo_Tr_split_CNA_aux:
  forall (m:fmap)(x y z:dart)(i:nat),
 Mod.Prec_Tr m x y ->
  inv_hmap m -> exd m x -> exd m y -> exd m z ->
    let m1 := Mod.Tr m x y in
    let t := Iter (MfM.f m1) i z in
  inv_hmap m1 -> exd m z ->
    MfM.expo m x y -> ~ MfM.expo m x z -> 
       MfM.expo m z t.
Proof.
intros m x y z i Pr.
intros.
elim (eq_dart_dec (MfM.f m x) y).
 intro.
   unfold MfM.expo in |- *.
   split.
   tauto.
 split with i.
   unfold t in |- *.
   unfold m1 in |- *.
   rewrite Iter_f_Tr_Id in |- *.
   tauto.
  tauto.
  tauto.
  tauto.
  tauto.
  tauto.
  tauto.
intro.
  intros.
  induction i.
 unfold t in |- *.
   simpl in |- *.
   apply MfM.expo_refl.
    tauto.
simpl in t.
  set (zi := Iter (MfM.f m1) i z) in |- *.
  fold zi in t.
  unfold t in |- *.
  unfold m1 in |- *.
  rewrite Mod.f_Tr in |- *.
 elim (eq_dart_dec x zi).
  intro.
    simpl in IHi.
    fold zi in IHi.
    rewrite <- a in IHi.
    elim H6.
    apply MfM.expo_symm.
    tauto.
   tauto.
 elim (eq_dart_dec (Mod.M.f_1 m y) zi).
  intros.
    simpl in IHi.
    fold zi in IHi.
    assert (y = MfM.f m zi).
   rewrite <- a in |- *.
     rewrite MfM.f_f_1 in |- *.
     tauto.
    tauto.
    tauto.
  apply MfM.expo_trans with zi.
    tauto.
  apply MfM.expo_trans with y.
   rewrite H7 in |- *.
     unfold MfM.expo in |- *.
     split.
    unfold zi in |- *.
      unfold m1 in |- *.
      generalize (MfM.exd_Iter_f (Mod.Tr m x y) i z).
      generalize (Mod.exd_Tr m x y 
        (Iter (MfM.f (Mod.Tr m x y)) i z)).
      unfold m1 in H3.
      generalize (Mod.exd_Tr m x y z).
       tauto.
   split with 1.
     simpl in |- *.
      tauto.
  apply MfM.expo_trans with x.
   apply MfM.expo_symm.
     tauto.
    tauto.
  unfold MfM.expo in |- *.
    split.
    tauto.
  split with 1.
    simpl in |- *.
     tauto.
 intros.
   simpl in IHi.
   fold zi in IHi.
   apply MfM.expo_trans with zi.
   tauto.
 unfold MfM.expo in |- *.
   split.
  unfold zi in |- *.
    unfold m1 in |- *.
    generalize (MfM.exd_Iter_f (Mod.Tr m x y) i z).
    generalize (Mod.exd_Tr m x y 
       (Iter (MfM.f (Mod.Tr m x y)) i z)).
    unfold m1 in H3.
    generalize (Mod.exd_Tr m x y z).
     tauto.
 split with 1.
   simpl in |- *.
    tauto.
 tauto.
 tauto.
 tauto.
 tauto.
unfold zi in |- *.
  unfold m1 in |- *.
  generalize (MfM.exd_Iter_f (Mod.Tr m x y) i z).
  generalize (Mod.exd_Tr m x y
  (Iter (MfM.f (Mod.Tr m x y)) i z)).
  unfold m1 in H3.
  generalize (Mod.exd_Tr m x y z).
   tauto.
Qed.

(* OK: *)

Lemma expo_Tr_split_CNA:forall (m:fmap)(x y z t:dart),
 Mod.Prec_Tr m x y ->
  inv_hmap m -> exd m x -> exd m y -> exd m z ->
    let m1 := Mod.Tr m x y in
  inv_hmap m1 -> 
    MfM.expo m x y -> 
     MfM.expo m1 z t -> ~ MfM.expo m x z -> 
       MfM.expo m z t.
Proof.
intros m x y z t Pr.
intros.
unfold  MfM.expo in H5.
elim H5.
clear H5.
intros.
elim H7.
clear H7.
intros i Hi.
rewrite <- Hi in |- *.
unfold m1 in |- *.
apply (expo_Tr_split_CNA_aux m x y z i Pr).
  tauto.
 tauto.
 tauto.
 tauto.
 tauto.
 tauto.
 tauto.
 tauto.
Qed.

(* OK!: *)

Lemma not_expo_Tr_y_x1:forall (m:fmap)(x y:dart),
 Mod.Prec_Tr m x y ->
  inv_hmap m -> exd m x -> exd m y -> 
   x <> y -> MfM.f m x <> y ->
    let m1 := Mod.Tr m x y in
    let x1 := MfM.f m x in
  inv_hmap m1 -> 
    MfM.expo m x y -> ~MfM.expo m1 y x1.
Proof.
intros m x y Pr.
intros.
assert (MfM.expo1 m x y).
 generalize (MfM.expo_expo1 m x y H).
    tauto.
intros.
  assert (MfM.expo1 m x y).
 generalize (MfM.expo_expo1 m x y H).
    tauto.
unfold MfM.expo1 in H6.
  elim H6.
  clear H6.
  intros.
  clear H6.
  elim H8.
  clear H8.
  intros j Hj.
  elim Hj.
  clear Hj.
  intros.
  assert (j <> 0).
 intro.
   rewrite H9 in H8.
   simpl in H8.
    tauto.
assert (j <> 1).
 intro.
   rewrite H10 in H8.
   simpl in H8.
    tauto.
intro.
  assert (MfM.expo1 m1 y x1).
 generalize (MfM.expo_expo1 m1 y x1).
    tauto.
unfold MfM.expo1 in H12.
  elim H12.
  clear H12.
  intros.
  elim H13.
  clear H13.
  intros k Hk.
  elim Hk.
  clear Hk.
  intros.
  elim (Nat.eq_dec k 0).
 intro.
   rewrite a in H14.
   simpl in H14.
   unfold x1 in H14.
   symmetry  in H14.
    tauto.
intro.
  assert (MfM.Iter_upb m1 y = MfM.degree m1 y).
 apply MfM.upb_eq_degree.
   tauto.
  tauto.
assert (MfM.Iter_upb m x = MfM.Iter_upb m y).
 apply MfM.period_expo.
   tauto.
  tauto.
assert (MfM.Iter_upb m y = MfM.degree m y).
 apply (MfM.upb_eq_degree m y H H1).
assert (MfM.degree m1 y = MfM.degree m y - j + 1).
 unfold m1 in |- *.
   apply (degree_Tr_split_y m x y j Pr H H0 H1).
  symmetry  in |- *.
     tauto.
  lia.
assert (Iter (MfM.f m1) k y = Iter (MfM.f m) k y).
 unfold m1 in |- *.
   rewrite (f_Tr_y_x m x y k j Pr) in |- *.
   tauto.
  tauto.
  tauto.
  tauto.
 symmetry  in |- *.
    tauto.
 split.
   lia.
  lia.
assert (Iter (MfM.f m) (k - 1) y = x).
 rewrite <- MfM.Iter_f_f_1 in |- *.
  simpl in |- *.
    rewrite <- H19 in |- *.
    rewrite H14 in |- *.
    unfold x1 in |- *.
    rewrite MfM.f_1_f in |- *.
    tauto.
   tauto.
   tauto.
  tauto.
  tauto.
  lia.
assert (Iter (MfM.f m1) (k - 1) y = x).
 unfold m1 in |- *.
   rewrite (f_Tr_y_x m x y (k - 1) j Pr) in |- *.
   tauto.
  tauto.
  tauto.
  tauto.
 symmetry  in |- *.
    tauto.
 split.
   lia.
  lia.
assert (Iter (MfM.f m1) k y = y).
 assert (k = S (k - 1)).
   lia.
 rewrite H22 in |- *.
   simpl in |- *.
   rewrite H21 in |- *.
   unfold m1 in |- *.
   rewrite Mod.f_Tr in |- *.
  elim (eq_dart_dec x x).
    tauto.
   tauto.
  tauto.
  tauto.
  tauto.
  tauto.
 tauto.
rewrite H14 in H22.
  unfold x1 in H22.
   tauto.
Qed.

(* OK: *)

Lemma Iter_Tr_x_x : forall (m:fmap)(x:dart)(i:nat),
 Mod.Prec_Tr m x x ->
  inv_hmap m -> exd m x ->  
   let m1:= Mod.Tr m x x in
    Iter (MfM.f m1) i x = x.
   intros.
induction i.
 simpl in |- *.
    tauto.
simpl in |- *.
  rewrite IHi in |- *.
  unfold m1 in |- *.
  rewrite Mod.f_Tr in |- *.
 elim (eq_dart_dec x x).
   tauto.
  tauto.
 tauto.
 tauto.
 tauto.
tauto.
tauto.
Qed.

(* OK: *)

Lemma degree_Tr_x_x : forall (m:fmap)(x:dart),
 Mod.Prec_Tr m x x ->
  inv_hmap m -> exd m x ->  
   let m1:= Mod.Tr m x x in
    MfM.degree m1 x = 1.
Proof.
intros.
unfold MfM.degree in |- *.
unfold m1 in |- *.
rewrite MfM.degree_aux_equation in |- *.
rewrite Mod.ndN_Tr in |- *.
elim (Arith.Compare_dec.le_lt_dec 1 (ndN m)).
 elim
 (eq_dart_dec x (Iter (MfM.f (Mod.Tr m x x)) 1 x)).
   tauto.
 intros.
   rewrite Iter_Tr_x_x in b.
   tauto.
  tauto.
  tauto.
 tauto.
intro.
   lia.
Qed.

(* OK: j = 1: *)

Lemma expo_Tr_split_CN_1:forall (m:fmap)(x y z t:dart),
 Mod.Prec_Tr m x y ->
  inv_hmap m -> exd m x -> exd m y -> exd m z ->
  let x1 := MfM.f m x in
  let y_1 := MfM.f_1 m y in
  let m1:= Mod.Tr m x y in
  inv_hmap m1 -> 
   MfM.f m x = y ->  
    MfM.expo m1 z t ->
     MfM.expo m x z ->
   ( MfM.between m y z x /\ MfM.between m y t x 
   \/ MfM.between m x1 z y_1 /\ MfM.between m x1 t y_1
   \/ ~ MfM.expo m x z /\ MfM.expo m z t ).
Proof.
intros m x y z t Pr.
intros.
assert (MfM.expo m z t).
 unfold MfM.expo in H5.
   elim H5.
   clear H5.
   intros.
   elim H7.
   clear H7.
   intros i Hi.
   unfold MfM.expo in |- *.
   split.
   tauto.
 split with i.
   rewrite <- Hi in |- *.
   symmetry  in |- *.
   unfold m1 in |- *.
   rewrite Iter_f_Tr_Id in |- *.
   tauto.
  tauto.
  tauto.
  tauto.
  tauto.
  tauto.
 tauto.
assert (MfM.expo m x y).
 unfold MfM.expo in |- *.
   split.
   tauto.
 split with 1.
   simpl in |- *.
    tauto.
assert (MfM.expo m y t).
 apply MfM.expo_trans with x.
  apply MfM.expo_symm.
    tauto.
   tauto.
 apply MfM.expo_trans with z.
   tauto.
  tauto.
assert (MfM.expo m y z).
 apply MfM.expo_trans with x.
  apply MfM.expo_symm.
    tauto.
   tauto.
  tauto.
assert (y_1 = x).
 unfold y_1 in |- *.
   rewrite <- H4 in |- *.
   rewrite MfM.f_1_f in |- *.
   tauto.
  tauto.
  tauto.
assert (MfM.expo m y x).
 apply MfM.expo_symm.
   tauto.
  tauto.
assert (MfM.expo1 m y x).
 generalize (MfM.expo_expo1 m y x).
    tauto.
assert (MfM.expo1 m y t).
 generalize (MfM.expo_expo1 m y t).
    tauto.
assert (MfM.expo1 m y z).
 generalize (MfM.expo_expo1 m y z).
    tauto.
generalize (MfM.expo_between_3 m y x z H H13 H15).
  generalize (MfM.expo_between_3 m y x t H H13 H14).
  unfold x1 in |- *.
  fold y_1 in |- *.
  rewrite H4 in |- *.
  rewrite H11 in |- *.
   tauto.
Qed.

(* OK: j = 0 (et j <> 1) *)

Lemma expo_Tr_split_CN_0:forall (m:fmap)(x y z t:dart),
 Mod.Prec_Tr m x y ->
  inv_hmap m -> exd m x -> exd m y -> exd m z ->
  let x1 := MfM.f m x in
  let y_1 := MfM.f_1 m y in
  let m1:= Mod.Tr m x y in
  inv_hmap m1 -> 
   x = y ->  
    MfM.expo m1 z t ->
     MfM.expo m x z -> MfM.f m x <> y ->
    ( MfM.between m y z x /\ MfM.between m y t x 
    \/ MfM.between m x1 z y_1 /\ MfM.between m x1 t y_1
    \/ ~ MfM.expo m x z /\ MfM.expo m z t ).
Proof.
intros m x y z t Pr.
intros.
rename H7 into Dx1.
elim (eq_dart_dec z x).
 intro.
   rewrite a in H5.
   assert (t = x).
  unfold MfM.expo in H5.
    elim H5.
    clear H5.
    intros.
    elim H7.
    clear H7.
    intros i Hi.
    unfold m1 in Hi.
    rewrite <- H4 in Hi.
    rewrite Iter_Tr_x_x in Hi.
   symmetry  in |- *.
      tauto.
  rewrite <- H4 in Pr.
     tauto.
   tauto.
   tauto.
 left.
   rewrite a in |- *.
   rewrite H7 in |- *.
   rewrite <- H4 in |- *.
   assert (MfM.expo1 m x x).
  assert (MfM.expo m x x).
   apply MfM.expo_refl.
      tauto.
  generalize (MfM.expo_expo1 m x x).
     tauto.
 generalize (MfM.between_expo_refl_1 m x x).
    tauto.
intro.
  elim (Nat.eq_dec x t).
 intro.
   rewrite <- a in H5.
   assert (MfM.expo m1 x z).
  apply MfM.expo_symm.
    tauto.
   tauto.
 unfold MfM.expo in H7.
   elim H7.
   clear H7.
   intros.
   elim H8.
   intros i Hi.
   clear H8.
   unfold m1 in Hi.
   rewrite <- H4 in Hi.
   rewrite Iter_Tr_x_x in Hi.
  symmetry  in Hi.
     tauto.
 rewrite <- H4 in Pr.
    tauto.
  tauto.
  tauto.
intro.
  assert (MfM.expo1 m x z).
 generalize (MfM.expo_expo1 m x z).
    tauto.
unfold MfM.expo1 in H7.
  elim H7.
  clear H7.
  intros.
  clear H7.
  elim H8.
  clear H8.
  intros iz Hiz.
  decompose [and] Hiz.
  clear Hiz.
  assert (MfM.Iter_upb m x = MfM.degree m x).
 apply MfM.upb_eq_degree.
   tauto.
  tauto.
assert (iz <> 0).
 intro.
   rewrite H10 in H8.
   simpl in H8.
   symmetry  in H8.
    tauto.
assert (Iter (MfM.f m) (iz - 1) x1 = z).
 unfold x1 in |- *.
   assert (Iter (MfM.f m) 1 x = MfM.f m x).
  simpl in |- *.
     tauto.
 rewrite <- H11 in |- *.
   rewrite <- MfM.Iter_comp in |- *.
   assert (iz - 1 + 1 = iz).
   lia.
 rewrite H12 in |- *.
   clear H12.
    tauto.
assert (MfM.degree m1 x = 1).
 unfold m1 in |- *.
   rewrite <- H4 in |- *.
   apply degree_Tr_x_x.
  rewrite <- H4 in Pr.
     tauto.
  tauto.
  tauto.
assert (y = Iter (MfM.f m) (MfM.degree m y) x).
 rewrite <- H4 in |- *.
   rewrite MfM.degree_per in |- *.
   tauto.
  tauto.
  tauto.
rewrite H9 in H7.
  rewrite H4 in H7.
  assert (2 <= MfM.degree m y).
  lia.
assert (MfM.degree m1 y + MfM.degree m1 x1 =
    MfM.degree m y).
 unfold m1 in |- *.
   unfold x1 in |- *.
   apply (degree_Tr_split m x y (MfM.degree m y)).
   tauto.
  tauto.
  tauto.
 rewrite H4 in |- *.
   rewrite MfM.degree_per in |- *.
   tauto.
  tauto.
  tauto.
  tauto.
  lia.
rewrite H4 in H12.
  assert (Iter (MfM.f m1) (iz - 1) x1 = z).
 unfold m1 in |- *.
   unfold x1 in |- *.
   rewrite (f_Tr_x1_y_1 m x y (iz - 1) 
     (MfM.degree m y) Pr) in |- *.
  fold x1 in |- *.
     tauto.
  tauto.
  tauto.
  tauto.
 rewrite H4 in |- *.
   rewrite MfM.degree_per in |- *.
   tauto.
  tauto.
  tauto.
 split.
   lia.
  lia.
assert (MfM.expo m1 x1 z).
 unfold MfM.expo in |- *.
   split.
  assert (exd m x1).
   unfold x1 in |- *.
     generalize (MfM.exd_f m x).
      tauto.
  unfold m1 in |- *.
    generalize (Mod.exd_Tr m x y x1).
     tauto.
 split with (iz - 1).
    tauto.
assert (MfM.expo m1 x1 t).
 apply MfM.expo_trans with z.
   tauto.
  tauto.
assert (MfM.expo1 m1 x1 t).
 generalize (MfM.expo_expo1 m1 x1 t).
    tauto.
unfold MfM.expo1 in H19.
  elim H19.
  clear H19.
  intros.
  elim H20.
  clear H20.
  intros it Hit.
  elim Hit.
  clear Hit.
  intros.
  assert (Iter (MfM.f m1) (MfM.degree m1 x1 - 1) x1
       = y_1).
 rewrite <- MfM.Iter_f_f_1 in |- *.
  simpl in |- *.
    rewrite MfM.degree_per in |- *.
   unfold m1 in |- *.
     rewrite Mod.f_1_Tr in |- *.
    elim (eq_dart_dec y x1).
     unfold x1 in |- *.
       intros.
       symmetry  in a.
        tauto.
    elim (eq_dart_dec (Mod.M.f m x) x1).
     unfold y_1 in |- *.
        tauto.
    intros.
      elim b1.
      unfold x1 in |- *.
       tauto.
    tauto.
    tauto.
    tauto.
    tauto.
   unfold x1 in |- *.
     generalize (MfM.exd_f m x).
      tauto.
   tauto.
   tauto.
  tauto.
  tauto.
  lia.
right.
  left.
  assert (Iter (MfM.f m) it x1 = t).
 rewrite <- H21 in |- *.
   unfold x1 in |- *.
   unfold m1 in |- *.
   rewrite (f_Tr_x1_y_1 m x y it (MfM.degree m y) Pr)
       in |- *.
   tauto.
  tauto.
  tauto.
  tauto.
  tauto.
 split.
  assert (MfM.Iter_upb m1 x1 = MfM.degree m1 x1).
   apply MfM.upb_eq_degree.
     tauto.
    tauto.
  rewrite H23 in H20.
     lia.
  lia.
assert (Iter (MfM.f m) (MfM.degree m1 x1 - 1) x1 = y_1).
 rewrite <- H22 in |- *.
   unfold m1 in |- *.
   unfold x1 in |- *.
   rewrite
    (f_Tr_x1_y_1 m x y (MfM.degree (Mod.Tr m x y) 
      (MfM.f m x) - 1)
       (MfM.degree m y) Pr) in |- *.
   tauto.
  tauto.
  tauto.
  tauto.
  tauto.
 fold m1 in |- *.
   fold x1 in |- *.
   split.
   lia.
  lia.
assert (MfM.expo m x x1).
 unfold MfM.expo in |- *.
   split.
   tauto.
 split with 1.
   simpl in |- *.
   fold x1 in |- *.
    tauto.
assert (MfM.degree m x = MfM.degree m x1).
 apply MfM.expo_degree.
   tauto.
  tauto.
assert (MfM.Iter_upb m x1 = MfM.degree m x1).
 apply MfM.upb_eq_degree.
   tauto.
 unfold x1 in |- *.
   generalize (MfM.exd_f m x).
    tauto.
split.
 unfold MfM.between in |- *.
   intros.
   split with (iz - 1).
   split with (MfM.degree m1 x1 - 1).
   rewrite H27 in |- *.
   rewrite <- H26 in |- *.
   rewrite H4 in |- *.
   split.
   tauto.
 split.
   tauto.
 split.
   lia.
  lia.
unfold MfM.between in |- *.
  intros.
  split with it.
  split with (MfM.degree m1 x1 - 1).
  rewrite H27 in |- *.
  rewrite <- H26 in |- *.
  rewrite H4 in |- *.
  split.
  tauto.
split.
  tauto.
split.
 assert (MfM.Iter_upb m1 x1 = MfM.degree m1 x1).
  apply MfM.upb_eq_degree.
    tauto.
   tauto.
 rewrite H30 in H20.
    lia.
 lia.
Qed.

(* OK: 2 <= j *)

Lemma expo_Tr_split_CN_j:
 forall (m:fmap)(x y z t:dart)(j:nat),
  Mod.Prec_Tr m x y ->
  inv_hmap m -> exd m x -> exd m y -> exd m z ->
  let x1 := MfM.f m x in
  let y_1 := MfM.f_1 m y in
  let m1:= Mod.Tr m x y in
  let dy:= MfM.degree m y in
  inv_hmap m1 -> 
   y = Iter (MfM.f m) j x -> 
    2 <= j <= dy -> MfM.f m x <> y -> x <> y ->
     MfM.expo m1 z t ->
      MfM.expo m x z -> 
   ( MfM.between m y z x /\ MfM.between m y t x 
  \/ MfM.between m x1 z y_1 /\ MfM.between m x1 t y_1
  \/ ~ MfM.expo m x z /\ MfM.expo m z t ).
Proof.
intros m x y z t j Pr.
intros.
assert (MfM.expo m x1 z).
 apply MfM.expo_trans with x.
  apply MfM.expo_symm.
    tauto.
  unfold MfM.expo in |- *.
    split.
    tauto.
  split with 1.
    simpl in |- *.
    fold x1 in |- *.
     tauto.
  tauto.
assert (MfM.expo1 m x1 z).
 generalize (MfM.expo_expo1 m x1 z).
    tauto.
unfold MfM.expo1 in H11.
  elim H11.
  clear H11.
  intros.
  elim H12.
  clear H12.
  intros iz Hi.
  elim Hi.
  intros.
  clear Hi.
  assert (MfM.degree m1 y = MfM.degree m y - j + 1).
 unfold m1 in |- *.
   apply (degree_Tr_split_y m x y j Pr H H0 H1).
   tauto.
 fold dy in |- *.
    lia.
assert (MfM.degree m1 x1 = j - 1).
 unfold m1 in |- *.
   apply (degree_Tr_split_x1 m x y j Pr H H0 H1).
   tauto.
 fold dy in |- *.
    tauto.
assert (MfM.degree m1 y +MfM.degree m1 x1 = 
   MfM.degree m y).
 unfold m1 in |- *.
   unfold x1 in |- *.
   apply (degree_Tr_split m x y j).
   tauto.
  tauto.
  tauto.
  tauto.
  tauto.
 fold dy in |- *.
    lia.
assert (MfM.expo m x1 y).
 apply MfM.expo_trans with x.
  apply MfM.expo_symm.
    tauto.
  unfold MfM.expo in |- *.
    split.
    tauto.
  split with 1.
    simpl in |- *.
    fold x1 in |- *.
     tauto.
 unfold MfM.expo in |- *.
   split.
   tauto.
 split with j.
   symmetry  in |- *.
    tauto.
assert (MfM.Iter_upb m x1 = MfM.degree m x1).
 apply MfM.upb_eq_degree.
   tauto.
  tauto.
assert (MfM.degree m x1 = MfM.degree m y).
 apply MfM.expo_degree.
   tauto.
  tauto.
rewrite H18 in H12.
  rewrite H19 in H12.
  assert (MfM.expo1 m1 z t).
 generalize (MfM.expo_expo1 m1 z t).
    tauto.
elim (Arith.Compare_dec.le_lt_dec iz (j - 2)).
 intro.
   assert (Iter (MfM.f m1) iz x1 = z).
  unfold m1 in |- *.
    unfold x1 in |- *.
    rewrite (f_Tr_x1_y_1 m x y iz j Pr) in |- *.
   fold x1 in |- *.
      tauto.
   tauto.
   tauto.
   tauto.
   tauto.
  fold dy in |- *.
     lia.
 assert (MfM.expo m1 x1 z).
  unfold MfM.expo in |- *.
    split.
   unfold m1 in |- *.
     generalize (Mod.exd_Tr m x y x1).
      tauto.
  split with iz.
     tauto.
 assert (MfM.expo m1 x1 t).
  apply MfM.expo_trans with z.
    tauto.
   tauto.
 assert (MfM.expo1 m1 x1 t).
  generalize (MfM.expo_expo1 m1 x1 t).
     tauto.
 unfold MfM.expo1 in H24.
   elim H24.
   clear H24.
   intros.
   elim H25.
   clear H25.
   intros it Hi.
   elim Hi.
   clear Hi.
   intros.
   assert (MfM.Iter_upb m1 x1 = MfM.degree m1 x1).
  apply MfM.upb_eq_degree.
    tauto.
   tauto.
 assert (Iter (MfM.f m) (j - 2) x1 = y_1).
  unfold x1 in |- *.
    assert (Iter (MfM.f m) 1 x = MfM.f m x).
   simpl in |- *.
      tauto.
  rewrite <- H28 in |- *.
    rewrite <- MfM.Iter_comp in |- *.
    assert (j - 2 + 1 = j - 1).
    lia.
  rewrite H29 in |- *.
    rewrite <- MfM.Iter_f_f_1 in |- *.
   simpl in |- *.
     rewrite <- H4 in |- *.
     fold y_1 in |- *.
      tauto.
   tauto.
   tauto.
   lia.
 right.
   left.
   split.
  unfold MfM.between in |- *.
    intros.
    rewrite H18 in |- *.
    split with iz.
    split with (j - 2).
    split.
    tauto.
  split.
    tauto.
   lia.
 unfold MfM.between in |- *.
   intros.
   split with it.
   split with (j - 2).
   split.
  unfold x1 in |- *.
    rewrite <- (f_Tr_x1_y_1 m x y it j Pr) in |- *.
   fold m1 in |- *.
      tauto.
   tauto.
   tauto.
   tauto.
   tauto.
  fold dy in |- *.
    rewrite H27 in H25.
    fold dy in H16.
     lia.
 split.
   tauto.
 rewrite H18 in |- *.
   rewrite H19 in |- *.
   fold dy in |- *.
    lia.
intros.
  assert (Iter (MfM.f m) (iz - (j - 1)) y = z).
 rewrite <- H13 in |- *.
   rewrite H4 in |- *.
   rewrite <- MfM.Iter_comp in |- *.
   assert (iz - (j - 1) + j = iz + 1).
   lia.
 rewrite H21 in |- *.
   clear H21.
   rewrite MfM.Iter_comp in |- *.
   simpl in |- *.
   fold x1 in |- *.
    tauto.
assert (Iter (MfM.f m1) (iz - (j - 1)) y = z).
 unfold m1 in |- *.
   rewrite (f_Tr_y_x m x y (iz - (j - 1)) j Pr) 
    in |- *.
   tauto.
  tauto.
  tauto.
  tauto.
  tauto.
 split.
   lia.
 fold dy in |- *.
   fold dy in H12.
    lia.
assert (MfM.expo m1 y z).
 unfold MfM.expo in |- *.
   split.
  unfold m1 in |- *.
    generalize (Mod.exd_Tr m x y y).
     tauto.
 split with (iz - (j - 1)).
    tauto.
assert (MfM.expo m1 y t).
 apply MfM.expo_trans with z.
   tauto.
  tauto.
assert (MfM.expo1 m1 y t).
 generalize (MfM.expo_expo1 m1 y t).
    tauto.
unfold MfM.expo1 in H25.
  elim H25.
  clear H25.
  intros.
  elim H26.
  clear H26.
  intros it Ht.
  elim Ht.
  clear Ht.
  intros.
  assert (MfM.Iter_upb m1 y = MfM.degree m1 y).
 apply MfM.upb_eq_degree.
   tauto.
  tauto.
rewrite H28 in H26.
  fold dy in H14.
  fold dy in H16.
  fold dy in H12.
  assert (Iter (MfM.f m) it y = t).
 rewrite <- (f_Tr_y_x m x y it j Pr) in |- *.
  fold m1 in |- *.
     tauto.
  tauto.
  tauto.
  tauto.
  tauto.
 split.
   lia.
 fold dy in |- *.
    lia.
left.
  assert (Iter (MfM.f m) (dy - j) y = x).
 rewrite H4 in |- *.
   rewrite <- MfM.Iter_comp in |- *.
   assert (dy - j + j = dy).
   lia.
 rewrite H30 in |- *.
   assert (MfM.expo m x y).
  unfold MfM.expo in |- *.
    split.
    tauto.
  split with j.
    symmetry  in |- *.
     tauto.
 assert (MfM.degree m x = dy).
  unfold dy in |- *.
    rewrite (MfM.expo_degree m x y) in |- *.
    tauto.
   tauto.
   tauto.
 rewrite <- H32 in |- *.
   rewrite MfM.degree_per in |- *.
   tauto.
  tauto.
  tauto.
split.
 unfold MfM.between in |- *.
   intros.
   split with (iz - (j - 1)).
   split with (dy - j).
   split.
   tauto.
 split.
   tauto.
 rewrite MfM.upb_eq_degree in |- *.
  fold dy in |- *.
    split.
    lia.
   lia.
  tauto.
  tauto.
unfold MfM.between in |- *.
  intros.
  split with it.
  split with (dy - j).
  split.
  tauto.
split.
  tauto.
rewrite MfM.upb_eq_degree in |- *.
 fold dy in |- *.
   split.
   lia.
  lia.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma expo_Tr_split_CN:forall (m:fmap)(x y z t:dart),
  Mod.Prec_Tr m x y ->
  inv_hmap m -> exd m x -> exd m y -> exd m z ->
  let x1 := MfM.f m x in
  let y_1 := MfM.f_1 m y in
  let m1:= Mod.Tr m x y in
  inv_hmap m1 -> MfM.expo m x y ->  
   MfM.expo m1 z t ->
    (  MfM.between m y z x /\ MfM.between m y t x 
    \/ MfM.between m x1 z y_1 /\ MfM.between m x1 t y_1
    \/ ~ MfM.expo m x z /\ MfM.expo m z t ).
Proof.
intros m x y z t Pr.
intros.
assert (MfM.expo1 m x y).
 generalize (MfM.expo_expo1 m x y).
    tauto.
unfold MfM.expo1 in H6.
  elim H6.
  clear H6.
  intros.
  elim H7.
  clear H7.
  intros j Hj.
  elim Hj.
  clear Hj.
  intros.
  symmetry  in H8.
  assert (MfM.Iter_upb m x = MfM.degree m x).
 apply MfM.upb_eq_degree.
   tauto.
  tauto.
assert (MfM.degree m x = MfM.degree m y).
 apply MfM.expo_degree.
   tauto.
  tauto.
rewrite H9 in H7.
  rewrite H10 in H7.
  elim (MfM.expo_dec m x z).
 intro.
   elim (eq_dart_dec (MfM.f m x) y).
  intro.
    unfold x1 in |- *; unfold y_1 in |- *; 
     unfold m1 in |- *.
    apply (expo_Tr_split_CN_1 m x y z t
    Pr H H0 H1 H2 H3 a0 H5 a).
 intro.
   assert (j <> 1).
  intro.
    rewrite H11 in H8.
    simpl in H8.
    symmetry  in H8.
     tauto.
 elim (eq_dart_dec x y).
  intro.
    apply (expo_Tr_split_CN_0 m x y z t 
    Pr H H0 H1 H2 H3 a0 H5 a b).
 intro.
   assert (j <> 0).
  intro.
    rewrite H12 in H8.
    simpl in H8.
    symmetry  in H8.
     tauto.
 unfold y_1 in |- *.
   unfold x1 in |- *.
   unfold m1 in |- *.
   apply (expo_Tr_split_CN_j m x y z t
        j Pr H H0 H1 H2 H3 H8).
   lia.
  tauto.
  tauto.
 fold m1 in |- *.
    tauto.
  tauto.
intro.
  elim (MfM.expo_dec m z t).
  tauto.
intro.
   absurd (MfM.expo m z t).
  tauto.
apply (expo_Tr_split_CNA m x y z t Pr H H0 H1 H2 H3 H4 H5 b).
 tauto.
 tauto.
Qed.

Lemma expo_Tr_split_CNS:forall (m:fmap)(x y z t:dart),
 Mod.Prec_Tr m x y ->
  inv_hmap m -> exd m x -> exd m y -> exd m z ->
  let x1 := MfM.f m x in
  let y_1 := MfM.f_1 m y in
  let m1:= Mod.Tr m x y in
  inv_hmap m1 -> MfM.expo m x y ->  
   (MfM.expo m1 z t <->
   ( MfM.between m y z x /\ MfM.between m y t x 
   \/ MfM.between m x1 z y_1 /\ MfM.between m x1 t y_1
   \/ ~ MfM.expo m x z /\ MfM.expo m z t)).
Proof.
intros m x y z t Pr.
intros.
split.
 apply 
 (expo_Tr_split_CN m x y z t Pr H H0 H1 H2 H3 H4).
apply (expo_Tr_split_CS m x y z t Pr H H0 H1 H2 H3 H4).
Qed.

(* THEN, THE SUMMARY: *)

Theorem expo_Tr_CNS:
  forall(m:fmap)(x y z t:dart)(H:inv_hmap m),
  Mod.Prec_Tr m x y ->
  exd m x -> exd m y -> exd m z ->
  let x1 := MfM.f m x in
  let y_1 := MfM.f_1 m y in
  let m1:= Mod.Tr m x y in
  inv_hmap m1 -> 
 (MfM.expo m1 z t <->
   if MfM.expo_dec m x y H then  
    ( MfM.between m y z x /\ MfM.between m y t x 
   \/ MfM.between m x1 z y_1 /\ MfM.between m x1 t y_1
   \/ ~ MfM.expo m x z /\ MfM.expo m z t)
   else 
    ( MfM.expo m z t 
   \/ MfM.expo m x z /\ MfM.expo m y t
   \/ MfM.expo m x t /\ MfM.expo m y z)). 
Proof.
intros m x y z t H Pr.
intros.
elim (MfM.expo_dec m x y H).
 intro.
   apply 
 (expo_Tr_split_CNS m x y z t Pr H H0 H1 H2 H3 a).
intro.
  apply
 (expo_Tr_merge_CNS m x y z t Pr H H0 H1 H2 H3 b).
Qed.

(*
Theorem expo_Tr_CNS:
  forall(m:fmap)(x y z t:dart)(H:inv_hmap m),
  Mod.Prec_Tr m x y ->
  exd m x -> exd m y -> exd m z ->
  let x1 := MfM.f m x in
  let y_1 := MfM.f_1 m y in
  let m1:= Mod.Tr m x y in
  inv_hmap m1 -> 
 (MfM.expo m1 z t <->
   if MfM.expo_dec m x y H then  
    ( MfM.between m y z x /\ MfM.between m y t x 
   \/ MfM.between m x1 z y_1 /\ MfM.between m x1 t y_1
   \/ ~ MfM.expo m x z /\ MfM.expo m z t)
   else 
    ( MfM.expo m z t 
   \/ MfM.expo m x z /\ MfM.expo m y t
   \/ MfM.expo m x t /\ MfM.expo m y z)). 


MfM.expo_between_3
     : forall (m : fmap) (x y z : dart),
       inv_hmap m ->
       MfM.expo1 m x y ->
       MfM.expo1 m x z ->
       MfM.between m x z y \/ 
        MfM.between m (MfM.f m y) z (MfM.f_1 m x)




Lemma degree_Tr_split_x1:
 forall(m:fmap)(x y:dart)(j:nat), 
 Mod.Prec_Tr m x y ->
  inv_hmap m -> exd m x -> exd m y -> 
   let m1:= Mod.Tr m x y in
   let dy:= MfM.degree m y in
   let x1:= MfM.f m x in
   y = Iter (MfM.f m) j x -> 
    (2 <= j <= dy) -> 
      MfM.degree m1 x1 = j - 1.



degree_Tr_split_y
     : forall (m : fmap) (x y : dart) (j : nat),
       Mod.Prec_Tr m x y ->
       inv_hmap m ->
       exd m x ->
       exd m y ->
       let m1 := Mod.Tr m x y in
       let dy := MfM.degree m y in
       y = Iter (MfM.f m) j x -> 
       0 < j <= dy -> 
       MfM.degree m1 y = dy - j + 1


degree_Tr_x_x
     : forall (m : fmap) (x : dart),
       Mod.Prec_Tr m x x ->
       inv_hmap m -> exd m x -> 
       let m1 := Mod.Tr m x x in
            MfM.degree m1 x = 1


Theorem degree_Tr_split_others: 
  forall(m:fmap)(x y z:dart), 
Mod.Prec_Tr m x y ->
    inv_hmap m -> exd m x -> exd m y -> exd m z ->
  let m1:= Mod.Tr m x y in 
 inv_hmap m1 ->
  MfM.expo m x y -> 
   ~MfM.expo m x z -> 
     MfM.degree m1 z = MfM.degree m z.

MfM.between_dec
     : forall (m : fmap) (z v t : dart),
       inv_hmap m -> exd m z ->
     MfM.between m z v t \/ ~ MfM.between m z v t
*)

(* FINALLY, OTHER BETTER FORM FOR degree: *) 

Theorem degree_Tr_split_summary_bis: 
forall (m:fmap)(x y z:dart)(j:nat)(H:inv_hmap m),
  Mod.Prec_Tr m x y ->
  exd m x -> exd m y -> exd m z ->
  let dy := MfM.degree m y in
  y = Iter (MfM.f m) j x -> 
  2 <= j <= dy ->
  let x1:= MfM.f m x in 
  let y_1:= MfM.f_1 m y in
  let m1:= Mod.Tr m x y in
  inv_hmap m1 ->
    (MfM.between m y z x ->  
        MfM.degree m1 z = dy - j + 1) /\
    (MfM.between m x1 z y_1 ->
        MfM.degree m1 z = j - 1) /\
    (~ MfM.expo m x z -> 
        MfM.degree m1 z = MfM.degree m z).
Proof.
intros.
assert (MfM.expo m x y).
 rewrite H4 in |- *.
   unfold MfM.expo in |- *.
   split.
   tauto.
 split with j.
    tauto.
assert (MfM.expo m y x).
 apply MfM.expo_symm.
   tauto.
  tauto.
assert (MfM.expo1 m y x).
 generalize (MfM.expo_expo1 m y x).
    tauto.
elim (MfM.expo_dec m x z).
 intro.
   assert (MfM.expo m y z).
  apply MfM.expo_trans with x.
    tauto.
   tauto.
 assert (MfM.expo1 m y z).
  generalize (MfM.expo_expo1 m y z).
     tauto.
 generalize (MfM.expo_between_3 m y x z H H9 H11).
   fold x1 in |- *.
   fold y_1 in |- *.
   intro.
   generalize (MfM.between_dec m y z x H H2).
   intro.
   assert (exd m x1).
  unfold x1 in |- *.
    generalize (MfM.exd_f m x).
     tauto.
 generalize (MfM.between_dec m x1 z y_1 H H14).
   intro.
 split.
  intro.
    assert (MfM.expo m1 y z).
   generalize 
(expo_Tr_split_CNS m x y y z H0 H H1 H2 H2 H6 H7).
     fold m1 in |- *.
     assert (MfM.between m y y x).
    generalize (MfM.between_expo_refl_1 m y x H H2).
       tauto.
    tauto.
  assert (MfM.degree m1 y = MfM.degree m1 z).
   apply MfM.expo_degree.
     tauto.
    tauto.
  rewrite <- H18 in |- *.
    apply (degree_Tr_split_y m x y j H0 H H1 H2 H4).
    fold dy in |- *.
     lia.
 split.
  intro.
    assert (MfM.expo m x1 z).
   apply MfM.expo_symm.
     tauto.
   apply MfM.expo_trans with x.
    apply MfM.expo_symm.
      tauto.
     tauto.
   unfold MfM.expo in |- *.
     split.
     tauto.
   split with 1.
     simpl in |- *.
     unfold x1 in |- *.
      tauto.
  assert (MfM.expo m1 x1 z).
   generalize 
 (expo_Tr_split_CNS m x y x1 z H0 H H1 H2 H14 H6 H7).
     fold m1 in |- *.
     fold x1 in |- *.
     fold y_1 in |- *.
     assert (MfM.expo m x1 y_1).
    apply MfM.expo_trans with x.
     apply MfM.expo_symm.
       tauto.
     unfold MfM.expo in |- *.
       split.
       tauto.
     split with 1.
       simpl in |- *.
       unfold x1 in |- *.
        tauto.
    apply MfM.expo_trans with y.
      tauto.
    apply MfM.expo_symm.
      tauto.
    unfold MfM.expo in |- *.
      split.
     unfold y_1 in |- *.
       generalize (MfM.exd_f_1 m y).
        tauto.
    split with 1.
      simpl in |- *.
      unfold y_1 in |- *.
      rewrite MfM.f_f_1 in |- *.
      tauto.
     tauto.
     tauto.
   assert (MfM.between m x1 x1 y_1).
    assert (MfM.expo1 m x1 y_1).
     generalize (MfM.expo_expo1 m x1 y_1).
        tauto.
    generalize 
  (MfM.between_expo_refl_1 m x1 y_1 H H14).
       tauto.
    tauto.
  assert (MfM.degree m1 x1 = MfM.degree m1 z).
   apply MfM.expo_degree.
     tauto.
    tauto.
  rewrite <- H19 in |- *.
    apply (degree_Tr_split_x1 m x y j H0 H H1 H2 H4).
    fold dy in |- *.
     tauto.
 intro.
   unfold m1 in |- *.
   apply 
(degree_Tr_split_others m x y z H0 H H1 H2 H3 H6 H7).
    tauto.
intro.
  split.
 intro.
   generalize (MfM.between_expo m y z x H H2 H10).
   intros.
   elim b.
   apply MfM.expo_trans with y.
   tauto.
  tauto.
split.
 intro.
   assert (exd m x1).
  unfold x1 in |- *.
    generalize (MfM.exd_f m x).
     tauto.
 generalize (MfM.between_expo m x1 z y_1 H H11 H10).
   intros.
   elim b.
   apply MfM.expo_trans with x1.
  unfold MfM.expo in |- *.
    split.
    tauto.
  split with 1.
    simpl in |- *.
    unfold x1 in |- *.
     tauto.
  tauto.
intro.
  apply 
(degree_Tr_split_others m x y z H0 H H1 H2 H3 H6 H7).
   tauto.
 tauto.
Qed.

End MTr.

(*=====================================================
                    THE END
=====================================================*)





(*====================================================
            COMPLEMENTS: USEFUL ?
=====================================================*)

(* TO ADAPT ?? *)


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

(* ADAPT AND PUT IN J2B: USEFUL?
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

