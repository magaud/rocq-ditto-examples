(*=====================================================

  TOPOLOGICAL FMAPS, HMAPS -
              WITH TAGS AND EMBEDDINGS

     PART 2 : SETS OF DARTS, PATHS, ORBITS 
                 FUNCTOR Mf FOR f-ORBITS

              (LATER : FUNCTOR MTr WITH Tr)

       NOETHERIAN INDUCTION ON A BIJECTION f
       WITH SIGNATURES FUNCTORS AND MODULES

=====================================================*)

Require Export Del01.

(*===================================================
                     SETS OF DARTS 

           FOR NOETHERIAN INDUCTIVE REASONINGS
===================================================*)

Open Scope nat_scope.

Inductive set:Set:=
    Vs : set | Is : set -> dart -> set.

Fixpoint exds(s:set)(z:dart){struct s}:Prop:=
  match s with
     Vs => False
   | Is s0 x => x=z \/ exds s0 z
  end.

Lemma exds_dec: forall(s:set)(z:dart),
  {exds s z}+{~exds s z}.
Proof.
induction s.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intro.
   generalize (eq_dart_dec d z).
   generalize (IHs z).
   tauto.
Qed.

(* IF NO DART IS IN s, s IS Vs: *)

Lemma not_exds_Vs: forall s:set,
  (forall z:dart, ~exds s z) -> s = Vs.
Proof.
intros.
induction s.
 tauto.
 generalize (H d).
   simpl in |- *.
   tauto.
Qed.

Lemma not_exds_diff: forall(s:set)(z:dart),
  ~exds s z -> 
    forall(t:dart), exds s t -> z <> t.
Proof.
intros.
induction s.
 simpl in H0.
   tauto.
 simpl in H0.
   simpl in H.
   elim H0.
  intros.
    rewrite <- H1.
    intro.
    symmetry  in H2.
    tauto.
  apply IHs.
    tauto.
Qed.

(* SUPPRESSION OF ALL OCCURRENCES of z: *)

Fixpoint Ds(s:set)(z:dart){struct s}:set:=
  match s with
     Vs => Vs
   | Is s0 x =>
       if eq_dart_dec x z then (Ds s0 z)
       else Is (Ds s0 z) x
  end.

Lemma not_exds_Ds:forall(s:set)(z:dart),
   ~exds (Ds s z) z.
Proof.
induction s.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   elim (eq_dart_dec d z).
  intro.
    apply (IHs z).
  simpl in |- *.
    generalize (IHs z).
    tauto.
Qed.

Lemma exds_Ds:forall(s:set)(x z:dart),
   x <> z ->
     (exds s z <-> exds (Ds s x) z).
Proof.
induction s.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   elim (eq_dart_dec d x).
  intro.
    rewrite a.
    generalize (IHs x z).
    tauto.
  intro.
    simpl in |- *.
    generalize (IHs x z).
    tauto.
Qed.

Lemma exds_Ds_diff:forall(s:set)(x z:dart),
   exds (Ds s x) z -> x <> z.
induction s.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros x z.
   elim (eq_dart_dec d x).
  intro.
    apply IHs.
  simpl in |- *.
    intros.
    elim H.
   intro.
     rewrite <- H0.
     intro.
     rewrite H1 in b.
     tauto.
   apply IHs.
Qed.

Lemma Ds_s:forall(s:set)(z:dart),
  ~exds s z <-> Ds s z = s.
Proof.
induction s.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   elim (eq_dart_dec d z).
  intro.
    rewrite a.
    generalize (IHs z).
    intros.
    split.
   tauto.
   intro.
     assert (exds (Is s z) z).
    simpl in |- *.
      tauto.
    rewrite <- H0 in H1.
      absurd (exds (Ds s z) z).
     apply not_exds_Ds.
     tauto.
  intro.
    split.
   intros.
     generalize (IHs z).
     intros.
     assert (Ds s z = s).
    tauto.
    rewrite H1.
      tauto.
   intros.
     injection H.
     generalize (IHs z).
     tauto.
Qed.

Lemma not_exds_Ds_bis:forall(s:set)(x z:dart),
   ~exds s z -> ~exds (Ds s x) z.
Proof.
induction s.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   elim (eq_dart_dec d x).
  intro.
    apply IHs.
    tauto.
  simpl in |- *.
    intro.
    generalize (IHs x z).
    tauto.
Qed.

Lemma exds_Ds_exds:forall(s:set)(x z:dart),
   exds (Ds s x) z -> exds s z.
Proof.
intros.
generalize (exds_dec s z).
intro.
generalize (exds_dec (Ds s x) z).
intro.
generalize (not_exds_Ds_bis s x z).
tauto.
Qed.

(* "cardinal" of a (multi-)set: *)

Fixpoint card(s:set):nat:=
  match s with
     Vs => 0
   | Is s0 x => 
       if exds_dec s0 x then card s0
       else 1 + card s0
  end.

Lemma card_Ds:forall (s:set)(z:dart),
  card (Ds s z) <= card s.
Proof.
induction s.
 simpl in |- *.
   intro.
   lia.
 simpl in |- *.
   intro.
   elim (eq_dart_dec d z).
  intro.
    elim (exds_dec s d).
   intro.
     apply IHs.
   intro.
     generalize (IHs z).
     intro.
     lia.
  simpl in |- *.
    elim (exds_dec s d).
   elim (exds_dec (Ds s z) d).
    intros.
      apply IHs.
    intros.
      generalize (exds_Ds s z d).
      assert (z <> d).
     intro.
       rewrite H in b0.
       tauto.
     tauto.
   elim (exds_dec (Ds s z) d).
    intros.
      generalize (IHs z).
      intro.
      lia.
    intros.
      generalize (IHs z).
      intro.
      lia.
Qed.

Lemma not_exds_card_Ds:forall (s:set)(z:dart),
  ~exds s z -> card (Ds s z) = card s.
Proof.
intros.
generalize (Ds_s s z).
intros.
assert (Ds s z = s).
 tauto.
 rewrite H1.
   tauto.
Qed.

Lemma exds_card_pos:forall (s:set)(z:dart),
  exds s z -> 0 < card s.
Proof.
induction s.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   elim (exds_dec s d).
  intro.
    apply (IHs d a); tauto.
  intro.
    lia.
Qed.

Lemma exds_card_Ds:forall (s:set)(z:dart),
  exds s z -> card (Ds s z) = card s - 1.
Proof.
induction s.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   elim (eq_dart_dec d z).
  intro.
    elim (exds_dec s d).
   intro.
     rewrite a in a0.
     apply IHs.
     tauto.
   intro.
     rewrite a in b.
     rewrite not_exds_card_Ds.
    lia.
    tauto.
  simpl in |- *.
    elim (exds_dec (Ds s z) d).
   elim (exds_dec s d).
    intros.
      rewrite IHs.
     tauto.
     tauto.
    intros.
      generalize (exds_Ds s z d).
      assert (z <> d).
     intro.
       rewrite H0 in b0.
       tauto.
     tauto.
   elim (exds_dec s d).
    intros.
      generalize (exds_Ds s z d).
      assert (z <> d).
     intro.
       rewrite H0 in b0.
       tauto.
     tauto.
    intros.
      rewrite IHs.
 assert (0 < card s)%nat.
      apply exds_card_pos with z.
        tauto.
      lia.
     tauto.
Qed.

Lemma exds_card_Ds_inf:forall (s:set)(z:dart),
  exds s z -> card (Ds s z) < card s.
Proof.
intros.
generalize (exds_card_pos s z H).
generalize (exds_card_Ds s z H).
intros.
lia.
Qed.

(* ==========================================================
          RELATIONSHIPS BETWEEN sets AND fmaps
===========================================================*)

(* fmap to set *)

Fixpoint fmap_to_set(m:fmap):set:=
 match m with
     V => Vs
   | I m0 x _ _ => Is (fmap_to_set m0) x
   | L m0 _ _ _ => (fmap_to_set m0)
 end.

Lemma exd_exds:forall(m:fmap)(z:dart),
  exd m z <-> exds (fmap_to_set m) z.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   generalize (IHm z); tauto.
 simpl in |- *.
   tauto.
Qed.

Fixpoint ndN (m:fmap):nat:=
 match m with
    V => 0
  | I m0 x _ _ => 
       if exd_dec m0 x then ndN m0
       else 1 + ndN m0
  | L m0 _ _ _ => ndN m0
 end.

Lemma nd_card:forall(m:fmap),
  ndN m = card (fmap_to_set m).
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   elim (exd_dec m d).
  elim (exds_dec (fmap_to_set m) d).
   tauto.
   intros.
     generalize (exd_exds m d).
     tauto.
  elim (exds_dec (fmap_to_set m) d).
   intros.
     generalize (exd_exds m d).
     tauto.
   rewrite IHm.
     tauto.
 simpl in |- *.
   tauto.
Qed.

(* ===================================================
          ALWAYS (multi-)sets
===================================================*)

(* s1 - s2: *)

Fixpoint set_minus(s1 s2:set){struct s1}:set:=
 match s1 with
     Vs => Vs
   | Is s0 x =>
       if exds_dec s2 x then set_minus s0 s2
       else Is (set_minus s0 s2) x
 end.

Lemma not_exds_minus: forall(s1 s2:set)(z:dart),
  ~ exds s1 z ->
     ~ exds (set_minus s1 s2) z.
Proof.
induction s1.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   elim (exds_dec s2 d).
  intro.
    apply IHs1.
    tauto.
  simpl in |- *.
    intro.
    generalize (IHs1 s2 z).
    tauto.
Qed.

Lemma exds_set_minus: forall(s1 s2:set)(z:dart),
  exds s1 z -> ~exds s2 z ->
     exds (set_minus s1 s2) z.
Proof.
induction s1.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   elim (exds_dec s2 d).
  intro.
    elim H.
   intro.
     rewrite H1 in a.
     tauto.
   intro.
     apply IHs1.
    tauto.
    tauto.
  simpl in |- *.
    intro.
    elim H.
   tauto.
   generalize (IHs1 s2 z).
tauto.
Qed.

Lemma not_exds_set_minus: forall(s1 s2:set)(z:dart),
  exds s2 z -> ~exds (set_minus s1 s2) z.
Proof.
induction s1.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   elim (exds_dec s2 d).
  intro.
    apply IHs1.
    tauto.
  simpl in |- *.
    intro.
    generalize (IHs1 s2 z).
    intro.
    assert (d <> z).
   intro.
     rewrite H1 in b.
     tauto.
  tauto.
Qed.

Lemma exds_set_minus_eq:forall(s1 s2:set)(z:dart),
  (exds s1 z /\ ~exds s2 z) <-> 
      exds (set_minus s1 s2) z.
Proof.
intros.
generalize (not_exds_set_minus s1 s2 z).
generalize (exds_set_minus s1 s2 z).
generalize (exds_dec s2 z).
generalize (exds_dec (set_minus s1 s2) z).
generalize (exds_dec s1 z).
generalize (not_exds_minus s1 s2 z).
tauto.
Qed.

(* s1 INCLUDED IN (OR OBS. EQUAL TO) s2 *)

Inductive incls(s1 s2:set):Prop:=
  exds2 : (forall z:dart, exds s1 z -> exds s2 z) 
          -> incls s1 s2.

(* USEFUL: *)

Lemma set_minus_s_Ds :forall(s1 s2:set)(x:dart), 
  ~ exds s1 x -> exds s2 x -> 
     set_minus s1 (Ds s2 x) = set_minus s1 s2. 
Proof.
induction s1.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   elim (exds_dec (Ds s2 x) d).
  elim (exds_dec s2 d).
   intros.
     apply IHs1.
    tauto.
    tauto.
   intros.
     generalize (exds_Ds s2 x d).
     intros.
     assert (x <> d).
    intro.
      rewrite H2 in H.
      tauto.
    tauto.
  elim (exds_dec s2 d).
   intros.
     generalize (exds_Ds s2 x d).
     intros.
     assert (x <> d).
    intro.
      rewrite H2 in H.
      tauto.
    tauto.
   intros.
     rewrite IHs1.
    tauto.
    tauto.
    tauto.
Qed.

(* OK: *)

Lemma card_minus_set:forall(s1 s2:set),
  incls s2 s1 -> 
    (card (set_minus s1 s2) + card s2 = card s1)%nat.
Proof.
induction s1.
 simpl in |- *.
   intros.
   inversion H.
   simpl in H0.
   generalize (not_exds_Vs s2 H0).
   intro.
   rewrite H1.
   simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   inversion H.
   simpl in H0.
   elim (exds_dec s2 d).
  elim (exds_dec s1).
   intros.
     apply IHs1.
     constructor.
     intros.
     elim (H0 z H1).
    intro.
      rewrite <- H2.
      tauto.
    tauto.
   intros.
     generalize (IHs1 (Ds s2 d)).
     intros.
     inversion H.
     assert (incls (Ds s2 d) s1).
    constructor.
      intros.
      assert (d <> z).
     intro.
       rewrite H4 in H3.
       apply (not_exds_Ds s2 z H3).
     generalize (exds_Ds s2 d z H4).
       intro.
       assert (exds s2 z).
      tauto.
      assert (exds (Is s1 d) z).
       apply H2.
         tauto.
       simpl in H7.
         tauto.
    generalize (set_minus_s_Ds s1 s2 d b a).
      intro.
      rewrite H4 in H1.
      generalize (exds_card_Ds s2 d a).
      intro.
      rewrite H5 in H1.
      rewrite <- H1.
     generalize (exds_card_pos s2 d a).
       intro.
       lia.
     tauto.
  intro.
    simpl in |- *.
    elim (exds_dec (set_minus s1 s2) d).
   elim (exds_dec s1 d).
    intros.
      apply IHs1.
      constructor.
      intros.
      elim (H0 z H1).
     intro.
       rewrite H2 in b.
       tauto.
     tauto.
    intros.
      generalize (exds_set_minus_eq s1 s2 d).
      tauto.
   elim (exds_dec s1 d).
    intros.
      elim b0.
      apply (exds_set_minus s1 s2 d a b).
    intros.
      rewrite <- IHs1 with s2.
     lia.
     constructor.
       intros.
       elim (H0 z).
      intro.
        rewrite H2 in b.
        tauto.
      tauto.
      tauto.
Qed.

(* EQUALITY/DISJONCTION OF SETS *)

Definition impls(s1 s2:set):Prop:=
  forall z:dart, exds s1 z -> exds s2 z.

Definition eqs(s1 s2:set):Prop:=
  forall z:dart, exds s1 z <-> exds s2 z.

Definition disjs(s1 s2:set):Prop:=
  forall z:dart, exds s1 z -> exds s2 z -> False.

(*==================================================
             NOETHERIAN RELATION ON (MULTI-)SETS 
===================================================*)

Definition Rs(sy sx:set):=
  card sy < card sx.

Lemma Acc_set:forall s:set, Acc Rs s.
Proof.
induction s.
 apply Acc_intro.
   unfold Rs at 1 in |- *.
   simpl in |- *.
   intros.
   inversion H.
 apply Acc_intro.
   intro y.
   unfold Rs at 1 in |- *.
   simpl in |- *.
   inversion IHs.
   intro.
   elim (Nat.eq_dec (card y) (card s)).
  intro.
    apply Acc_intro.
    intro y0.
    unfold Rs at 1 in |- *.
    rewrite a.
    intro.
    apply H.
    unfold Rs in |- *.
    tauto.
  intro.
    apply Acc_intro.
    unfold Rs at 1 in |- *.
    intros.
    generalize H0.
    clear H0.
    elim (exds_dec s d).
   intros.
     apply H.
     unfold Rs in |- *.
     lia.
   intros.
      apply H.
     unfold Rs in |- *.
     lia.
Qed.

Lemma Rs_wf : well_founded Rs.
Proof.
unfold well_founded in |- *.
apply Acc_set.
Qed.

Lemma exds_Rs_Ds:
 forall(s:set)(z:dart),
   exds s z -> Rs (Ds s z) s.
Proof.
unfold Rs in |- *.
simpl in |- *.
intros.
apply exds_card_Ds_inf.
tauto.
Qed.

(*===================================================
                   ITERATOR Iter
===================================================*)

(* ITERATOR FOR ANY FUNCTION g: *)

Fixpoint Iter(g:dart->dart)(n:nat)(z:dart){struct n}:dart:=
  match n with
    0 => z
  | S n0 => g (Iter g n0 z)
 end.

(*===================================================
                  MODULE Type Sigf 
===================================================*)

(* SIGNATURE FOR BIJECTIONS f, f_1 : *)

Module Type Sigf.
(* f : bijection on a hmap m, with
definition domain (exd m) : dart -> Prop *)
Parameter f : fmap -> dart -> dart.
Parameter f_1 : fmap -> dart -> dart.
Axiom exd_f:forall (m:fmap)(z:dart),
  inv_hmap m -> (exd m z <-> exd m (f m z)).
Axiom exd_f_1:forall (m:fmap)(z:dart),
  inv_hmap m -> (exd m z <-> exd m (f_1 m z)).
Axiom f_1_f : forall (m:fmap)(z:dart), 
  inv_hmap m -> exd m z -> f_1 m (f m z) = z.
Axiom f_f_1 : forall (m:fmap )(z:dart), 
  inv_hmap m -> exd m z -> f m (f_1 m z) = z.
End Sigf.

(*===================================================
                     FUNCTOR Mf
===================================================*)

(* FUNCTOR Mf: *)

Module Mf(M:Sigf)<:Sigf
   with Definition f:=M.f
   with Definition f_1:=M.f_1.
Definition f:=M.f.
Definition f_1:=M.f_1.
Definition exd_f:=M.exd_f.
Definition exd_f_1:=M.exd_f_1.
Definition f_1_f:=M.f_1_f.
Definition f_f_1:=M.f_f_1.

Lemma exd_Iter_f:forall(m:fmap)(n:nat)(z:dart),
  inv_hmap m -> (exd m z <-> exd m (Iter (f m) n z)).
Proof.
induction n.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   generalize (exd_f m (Iter (f m) n z)).
   generalize (IHn z).
   generalize (IHn (Iter (f m) n z)).
tauto.
Qed.

Lemma exd_Iter_f_1:forall(m:fmap)(n:nat)(z:dart),
  inv_hmap m -> (exd m z <-> exd m (Iter (f_1 m) n z)).
Proof.
induction n.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   generalize (exd_f_1 m (Iter (f_1 m) n z)).
   generalize (IHn z).
   generalize (IHn (Iter (f_1 m) n z)).
tauto.
Qed.

(*===================================================
                 ITERATIONS IN ORBITS:
	       WITH NOETHERIAN INDUCTION
===================================================*)

(* REMAINING DARTS DURING f ITERATION 
ON z STARTING FROM A set sx: *)

Theorem Iter_rem_F :
 forall (m:fmap)(z:dart),
  forall sx: set, (forall sy: set, Rs sy sx -> set)
    -> set.
Proof.
 intros m z.
 refine
    (fun sx F =>
     let n:= ndN m - card sx in
     let zn := Iter (f m) n z in
     match exds_dec sx zn with
       left _ => F (Ds sx zn) _
     | right _ => sx
     end).
 apply exds_Rs_Ds.
 tauto.
Defined.

Definition Iter_rem_aux(m:fmap)(z:dart): set -> set
 := Fix Rs_wf (fun _:set => set) (Iter_rem_F m z).

(* UPPER_BOUND OF THE f ITERATION NUMBER 
STARTING FROM A SET: *)

Definition Iter_upb_aux(m:fmap)(z:dart)(s:set):nat:=
  ndN m - card (Iter_rem_aux m z s).

(* REMAINING DARTS IN THE f ITERATION 
STARTING FROM THE FMAP DART SET: *)

Definition Iter_rem(m:fmap)(z:dart):set:=
  Iter_rem_aux m z (fmap_to_set m).

(* UPPER_BOUND OF THE f ITERATION NUMBER 
STARTING FROM THE FMAP DART SET: *)

Definition Iter_upb(m:fmap)(z:dart):nat:=
  ndN m - card (Iter_rem m z).

(* DART SETS CONTAINING THE f-ORBIT: *)

Definition Iter_orb_aux(m:fmap)(z:dart)(s:set):set:=
  set_minus (fmap_to_set m) (Iter_rem_aux m z s).

Definition Iter_orb(m:fmap)(z:dart):set:=
  set_minus (fmap_to_set m) (Iter_rem m z).

(* FIXPOINT EQUATION TO CHARACTERIZE THE REMAINING
   DART SET, STARTING FROM A SET: *)

Theorem Iter_rem_aux_equation :
  forall(m:fmap)(z:dart)(sx:set),
  Iter_rem_aux m z sx =
    let n := ((ndN m) - (card sx))%nat in
    let zn := Iter (f m) n z in
    if exds_dec sx zn
    then Iter_rem_aux m z (Ds sx zn)
    else sx.
Proof.
intros m z sx.
unfold Iter_rem_aux in |- *.
rewrite Fix_eq.
 auto.
 intros x0 f0 g0 Heqfg.
   unfold Iter_rem_F in |- *.
   destruct (exds_dec x0 (Iter (f m) 
     ((ndN m - card x0))%nat z)).
  rewrite Heqfg.
    trivial.
  trivial.
Qed.

(*===================================================
 EXISTENCE PROPERTIES OF ITERATED DARTS, upb 
 IN ORBITS...:
	       WITH NOETHERIAN INDUCTION 
===================================================*)

(* FOR THE FOLLOWING LEMMA: *)

Definition P1
 (m:fmap)(z:dart)(s:set):Prop:=
    let sr := Iter_rem_aux m z s in
    let n := Iter_upb_aux m z s in
    ~ exds sr (Iter (f m) n z).

(* THE upb_ITERATED DART BY f DOES NOT REMAIN: *)

Lemma not_exds_rem_upb :
  forall(m:fmap)(z:dart)(s:set),
   let sr := Iter_rem_aux m z s in
    let n := Iter_upb_aux m z s in
    ~ exds sr (Iter (f m) n z).
Proof.
intros m z.
refine (well_founded_ind Rs_wf (P1 m z) _).
unfold P1 in |- *.
unfold Iter_upb_aux in |- *.
simpl in |- *.
intros.
rewrite Iter_rem_aux_equation.
simpl in |- *.
elim (exds_dec x (Iter (f m) (ndN m - card x) z)).
 intro.
   apply H.
   unfold Rs in |- *.
   simpl in |- *.
   apply exds_card_Ds_inf.
   tauto.
 tauto.
Qed.

(* THE upb_ITERATED DART BY f DOES NOT REMAIN: *)

Lemma not_exds_Iter_rem_upb :
 forall(m:fmap)(z:dart),
  let n:= Iter_upb m z in
   ~ exds (Iter_rem m z) (Iter (f m) n z).
Proof.
unfold Iter_rem in |- *.
unfold Iter_upb in |- *.
intros m z.
unfold Iter_rem in |- *.
generalize (not_exds_rem_upb m z (fmap_to_set m)).
simpl in |- *.
unfold Iter_upb_aux in |- *.
tauto.
Qed.

(* THE upb_ITERATED DART BY f IS IN m: *)

Lemma  exd_Iter_upb:
  forall(m:fmap)(z:dart), inv_hmap m ->
   exd m z -> exd m (Iter (f m) (Iter_upb m z) z).
Proof.
intros.
generalize (exd_Iter_f m (Iter_upb m z) z).
tauto.
Qed.

(* THE upb_ITERATED DART BY f IS IN THE COMPLEMENTARY: *)

Lemma exd_Iter_orb_upb :
 forall(m:fmap)(z:dart),
  inv_hmap m -> exd m z ->
   let n:= Iter_upb m z in
     exds (Iter_orb m z) (Iter (f m) n z).
Proof.
unfold Iter_orb in |- *.
intros.
apply exds_set_minus.
 generalize (exd_exds m (Iter (f m) (Iter_upb m z) z)).
   intro.
   generalize (exd_Iter_upb m z H H0).
   tauto.
 apply not_exds_Iter_rem_upb.
Qed.

(* NOT REMAINING EQUIVALENT TO BEING IN THE COMPLEMENTARY: *)

Lemma exds_rem_orb:forall(m:fmap)(z t:dart),
 inv_hmap m -> exd m t ->
  (~exds (Iter_rem m z) t <-> exds (Iter_orb m z) t).
Proof.
intros.
unfold Iter_orb in |- *.
generalize (exds_set_minus_eq (fmap_to_set m) (Iter_rem m z) t).
generalize (exd_exds m t).
tauto.
Qed.

Definition R3
 (m:fmap)(z t:dart)(s:set):Prop:=
  ~ exds s t ->
   let sr := Iter_rem_aux m z s in
    ~ exds sr t.

Lemma LR3:forall(m:fmap)(z t:dart)(s:set),
  ~ exds s t ->
   let sr := Iter_rem_aux m z s in
    ~ exds sr t.
Proof.
intros m z t.
refine (well_founded_ind Rs_wf (R3 m z t) _).
unfold R3 in |- *.
intros.
rewrite Iter_rem_aux_equation.
simpl in |- *.
elim (exds_dec x (Iter (f m) (ndN m - card x) z)).
 intro.
   apply H.
  unfold Rs in |- *.
    apply exds_card_Ds_inf.
    tauto.
  apply not_exds_Ds_bis.
    tauto.
 tauto.
Qed.

Definition R2
 (m:fmap)(z:dart)(s:set):Prop:=
   let sr := Iter_rem_aux m z s in
    ~ exds sr (Iter (f m) (ndN m - card s)%nat z).

Lemma LR2 :
  forall(m:fmap)(z:dart)(s:set),
   let sr := Iter_rem_aux m z s in
    ~ exds sr (Iter (f m) (ndN m - card s)%nat z).
Proof.
intros m z.
simpl in |- *.
refine (well_founded_ind Rs_wf (R2 m z) _).
unfold R2 in |- *.
intros.
rewrite Iter_rem_aux_equation.
simpl in |- *.
elim (exds_dec x (Iter (f m) (ndN m - card x) z)).
 intro.
   apply LR3.
   apply not_exds_Ds.
 tauto.
Qed.

(* OK!! BUT lia IS LONG... *)

Definition R1
 (m:fmap)(z:dart)(i:nat)(s:set):Prop:=
   let sr := Iter_rem_aux m z s in
   let n := Iter_upb_aux m z s in
      (ndN m - card s <= i <= n)%nat -> 
       ~ exds sr (Iter (f m) i z).
Lemma LR1 :
  forall(m:fmap)(z:dart)(i:nat)(s:set),
   let sr := Iter_rem_aux m z s in
   let n := Iter_upb_aux m z s in
     (ndN m - card s <= i <= n)%nat -> 
      ~ exds sr (Iter (f m) i z).
Proof.
intros m z i.
refine (well_founded_ind Rs_wf (R1 m z i) _).
unfold R1 in |- *.
unfold Iter_upb_aux in |- *.
intros.
elim (Nat.eq_dec i (ndN m - card x)%nat).
 intro.
   rewrite a.
   apply LR2.
 intro.
   generalize H0.
   rewrite Iter_rem_aux_equation.
   simpl in |- *.
   elim (exds_dec x (Iter (f m) (ndN m - card x) z)).
  intros.
    apply H.
   unfold Rs in |- *.
     apply exds_card_Ds_inf.
     tauto.
   split.
    generalize (exds_card_Ds x 
        (Iter (f m) (ndN m - card x)%nat z) a).
      intro.
      rewrite H2.
      elim H0.
      intros.
      clear H a H1 H2 H0 H4.
      lia.
    tauto.
  intros.
    clear H H0 b0.
    lia.
Qed.

(* VERY IMPORTANT: COROLLARIES: *)

Lemma not_exds_Iter_f_i :
  forall(m:fmap)(z:dart)(i:nat),
   let sr := Iter_rem m z in
   let n := Iter_upb m z in
     (i <= n)%nat -> ~ exds sr (Iter (f m) i z).
Proof.
simpl in |- *.
unfold Iter_upb in |- *.
unfold Iter_rem in |- *.
intros.
apply LR1.
generalize (nd_card m).
intro.
rewrite H0.
simpl in |- *.
unfold Iter_upb in |- *.
unfold Iter_upb_aux in |- *.
lia.
Qed.

Lemma exds_Iter_f_i :
  forall(m:fmap)(z:dart)(i:nat),
  inv_hmap m -> exd m z ->
   let s := Iter_orb m z in
   let n := Iter_upb m z in
     (i <= n)%nat -> exds s (Iter (f m) i z).
Proof.
intros.
assert (exd m (Iter (f m) i z)).
 generalize (exd_Iter_f m i z H).
   intro.
   tauto.
 generalize (exds_rem_orb m z (Iter (f m) i z) H H2).
   unfold s in |- *.
   intros.
   generalize (not_exds_Iter_f_i m z i).
   simpl in |- *.
   tauto.
Qed.

(*===================================================
          card PROPERTIES OF ORBITS:
	    WITH NOETHERIAN INDUCTION
===================================================*)

(* card OF THE REMAINING / ndN IN THE fmap: *)

Definition P2
 (m:fmap)(z:dart)(s:set):Prop:=
  (card s < ndN m ->
    card (Iter_rem_aux m z s) < ndN m)%nat.

Lemma card_rem_aux:forall(m:fmap)(z:dart)(s:set),
  (card s < ndN m ->
    card (Iter_rem_aux m z s) < ndN m)%nat.
Proof.
intros m z.
refine (well_founded_ind Rs_wf (P2 m z) _).
unfold P2 in |- *.
intros.
rewrite Iter_rem_aux_equation.
simpl in |- *.
elim (exds_dec x (Iter (f m) (ndN m - card x) z)).
 intro.
   apply H.
  unfold Rs in |- *.
    apply exds_card_Ds_inf.
    tauto.
  assert (card (Ds x (Iter (f m) (ndN m - card x) z)) 
     < card x)%nat.
   apply exds_card_Ds_inf.
     tauto.
   lia.
  tauto.
Qed.

Definition P2_bis
 (m:fmap)(z:dart)(s:set):Prop:=
  (card s <= ndN m ->
    card (Iter_rem_aux m z s) <= ndN m)%nat.

Lemma card_rem_aux_bis:forall(m:fmap)(z:dart)(s:set),
   (card s <= ndN m ->
    card (Iter_rem_aux m z s) <= ndN m)%nat.
Proof.
intros m z.
refine (well_founded_ind Rs_wf (P2_bis m z) _).
unfold P2_bis in |- *.
intros.
rewrite Iter_rem_aux_equation.
simpl in |- *.
elim (exds_dec x (Iter (f m) (ndN m - card x) z)).
 intro.
   apply H.
  unfold Rs in |- *.
    apply exds_card_Ds_inf.
    tauto.
  assert (card (Ds x (Iter (f m) (ndN m - card x) z)) 
          < card x)%nat.
   apply exds_card_Ds_inf.
     tauto.
   lia.
  tauto.
Qed.

(* THEN: *)

Lemma upb_pos_aux:forall(m:fmap)(z:dart),
  exd m z ->
      (card (Iter_rem m z) < ndN m)%nat.
Proof.
intros.
unfold Iter_rem in |- *.
rewrite Iter_rem_aux_equation.
simpl in |- *.
elim (exds_dec (fmap_to_set m) (Iter (f m) (ndN m - card (fmap_to_set m)) z)).
 intro.
   apply card_rem_aux.
   assert
    (card (Ds (fmap_to_set m) 
      (Iter (f m) (ndN m - card (fmap_to_set m)) z))
        < card (fmap_to_set m))%nat.
  apply exds_card_Ds_inf.
    tauto.
  generalize (nd_card m).
    intro.
    lia.
 intro.
   generalize (nd_card m).
   intro.
   assert (ndN m - card (fmap_to_set m) = 0)%nat.
  lia.
  rewrite H1 in b.
    simpl in b.
    generalize (exd_exds m z).
    intro.
    generalize (exds_dec (fmap_to_set m) z).
    tauto.
Qed.

(* OK, IMPORTANT: COROLLARY*)

Theorem upb_pos:forall(m:fmap)(z:dart),
  exd m z -> (0 < Iter_upb m z)%nat.
Proof.
unfold Iter_upb in |- *.
intros.
generalize (upb_pos_aux m z).
intros.
generalize (H0 H).
intro.
lia.
Qed.

Definition Q1(m:fmap)(z:dart)(s:set):Prop:=
   (card (Iter_rem_aux m z s) <= card s)%nat.

Lemma LQ1:forall(m:fmap)(z:dart)(s:set),
   (card (Iter_rem_aux m z s) <= card s)%nat.
Proof.
intros m z.
refine (well_founded_ind Rs_wf (Q1 m z) _).
unfold Q1 in |- *.
intros.
rewrite Iter_rem_aux_equation.
simpl in |- *.
elim (exds_dec x (Iter (f m) (ndN m - card x) z)).
 intro.
   assert (card (Ds x (Iter (f m) 
     (ndN m - card x) z)) < card x)%nat.
  apply exds_card_Ds_inf.
    tauto.
  assert
   (card (Iter_rem_aux m z 
      (Ds x (Iter (f m) (ndN m - card x) z))) <=
    card (Ds x (Iter (f m) (ndN m - card x) z)))%nat.
   apply H.
     unfold Rs in |- *.
     tauto.
   lia.
 intro.
   lia.
Qed.

Definition Q2(m:fmap)(z:dart)(s:set):Prop:=
  exds s (Iter (f m) (ndN m - card s)%nat z) ->
      (card (Iter_rem_aux m z s) < card s)%nat.

Lemma LQ2:forall(m:fmap)(z:dart)(s:set),
  exds s (Iter (f m) (ndN m - card s) z) ->
      (card (Iter_rem_aux m z s) < card s)%nat.
Proof.
intros m z.
refine (well_founded_ind Rs_wf (Q2 m z) _).
unfold Q2 in |- *.
intros.
rewrite Iter_rem_aux_equation.
simpl in |- *.
elim (exds_dec x (Iter (f m) (ndN m - card x) z)).
 intro.
   assert (card (Ds x (Iter (f m) (ndN m - card x) z)) 
         < card x)%nat.
  apply exds_card_Ds_inf.
    tauto.
  assert
   (card (Iter_rem_aux m z (Ds x (Iter (f m) 
      (ndN m - card x) z))) <=
    card (Ds x (Iter (f m) (ndN m - card x) z)))%nat.
   apply LQ1.
   lia.
 tauto.
Qed.

(*===================================================
     SOME LEMMAS, THEN RESULTS ABOUT PERIODICITY
===================================================*)

(* L2 : *)

Definition PL2(m:fmap)(z t:dart)(x:set):Prop:=
  inv_hmap m -> exd m z -> exds x t ->
    let sr:= Iter_rem_aux m z x in
    let zn0 := (Iter (f m) (ndN m - card x)%nat z) in
    ~exds sr t -> 
       exds x zn0 -> 
        ~ exds (Iter_rem_aux m z (Ds x zn0)) t.

Lemma L2:forall(m:fmap)(z t:dart)(x:set),
  inv_hmap m -> exd m z -> exds x t ->
    let sr:= Iter_rem_aux m z x in
    let zn0 := (Iter (f m) (ndN m - card x)%nat z) in
    ~exds sr t -> 
       exds x zn0 -> 
        ~ exds (Iter_rem_aux m z (Ds x zn0)) t.
Proof.
intros m z t.
refine (well_founded_ind Rs_wf (PL2 m z t) _).
unfold PL2 in |- *.
intros.
generalize H3.
clear H3.
rewrite (Iter_rem_aux_equation m z x).
simpl in |- *.
elim (exds_dec x (Iter (f m) (ndN m - card x) z)).
 tauto.
 tauto.
Qed.

(* L3: *)

Definition PL3(m:fmap)(z t:dart)(x:set):Prop:=
  inv_hmap m -> exd m z -> exds x t ->
    let sr:= Iter_rem_aux m z x in
    let zn0 := (Iter (f m) (ndN m - card x)%nat z) in
    ~exds sr t -> 
       exds x zn0.

Lemma L3:forall(m:fmap)(z t:dart)(x:set),
  inv_hmap m -> exd m z -> exds x t ->
    let sr:= Iter_rem_aux m z x in
    let zn0 := (Iter (f m) (ndN m - card x)%nat z) in
    ~exds sr t -> 
       exds x zn0. 
Proof.
intros m z t.
refine (well_founded_ind Rs_wf (PL3 m z t) _).
unfold PL3 in |- *.
intros.
generalize H3.
clear H3.
rewrite (Iter_rem_aux_equation m z x).
simpl in |- *.
elim (exds_dec x (Iter (f m) (ndN m - card x) z)).
 tauto.
 tauto.
Qed.

(* EXTRACTION, OK: *)

Definition P4(m:fmap)(z t:dart)(s:set):Set:=
 inv_hmap m -> exd m z -> exds s t ->
   (card s <= ndN m)%nat ->
   let sr:= Iter_rem_aux m z s in
   let nr:= Iter_upb_aux m z s in
   ~ exds sr t ->
      {i:nat | (i < nr)%nat /\ Iter (f m) i z = t}.

Lemma ex_i_aux :forall(m:fmap)(z t:dart)(s:set),
 inv_hmap m -> exd m z -> exds s t ->
   (card s <= ndN m)%nat ->
   let sr:= Iter_rem_aux m z s in
   let nr:= Iter_upb_aux m z s in
   ~ exds sr t ->
      {i:nat | (i < nr)%nat /\ Iter (f m) i z = t}.
Proof.
intros m z t.
refine (well_founded_induction Rs_wf (P4 m z t) _).
unfold P4 in |- *.
unfold Iter_upb_aux in |- *.
intros.
rewrite Iter_rem_aux_equation.
simpl in |- *.
elim (exds_dec x (Iter (f m) (ndN m - card x)%nat z)).
 intro.
   elim
 (eq_dart_dec (Iter (f m) (ndN m - card x)%nat z) t).
  intro.
    split with (ndN m - card x)%nat.
    split.
   assert
    (card (Iter_rem_aux m z (Ds x (Iter (f m) 
        (ndN m - card x) z))) <=
    card (Ds x (Iter (f m) (ndN m - card x) z)))%nat.
  assert 
   (card (Ds x (Iter (f m) (ndN m - card x) z)) 
               < card x)%nat.
     apply exds_card_Ds_inf.
       tauto.
     apply LQ1.
    generalize (exds_card_Ds_inf x 
         (Iter (f m) (ndN m - card x)%nat z)).
      intros.
      generalize (H6 a).
      intro.
      lia.
   tauto.
  intro.
    apply H.
   unfold Rs in |- *.
     apply exds_card_Ds_inf.
     tauto.
   tauto.
   tauto.
   generalize 
 (exds_Ds x (Iter (f m) (ndN m - card x)%nat z) t).
     tauto.
   assert (card (Ds x (Iter (f m) (ndN m - card x) z))
     < card x)%nat.
    apply exds_card_Ds_inf.
      tauto.
    lia.
   apply L2.
    tauto.
    tauto.
    tauto.
    tauto.
    tauto.
 intro.
   absurd 
 (exds x (Iter (f m) (ndN m - card x)%nat z)).
  tauto.
  eapply L3.
   tauto.
   tauto.
   apply H2.
     tauto.
Qed.

(* IF t IS REMOVED, THERE EXISTS i < nr, S.T. t IS THE ith ITERATED: OK *)

Lemma ex_i :forall(m:fmap)(z t:dart),
 inv_hmap m -> exd m z -> exd m t ->
   let sr:= Iter_rem m z in
   let nr:= Iter_upb m z in
   ~ exds sr t ->
      {i : nat | (i < nr)%nat /\ Iter (f m) i z = t}.
Proof.
unfold Iter_rem in |- *.
unfold Iter_upb in |- *.
intros.
generalize ex_i_aux.
simpl in |- *.
unfold Iter_rem in |- *.
unfold Iter_upb_aux in |- *.
intros.
apply H3.
 tauto.
 tauto.
 generalize (exd_exds m t).
   tauto.
 rewrite nd_card.
   lia.
 tauto.
Qed.

(* THIS APPLIES TO THE nr-th ITERATED *)

Lemma ex_i_upb :forall(m:fmap)(z:dart),
 inv_hmap m -> exd m z -> 
   let nr:= Iter_upb m z in
 {i : nat | (i < nr)%nat /\ 
     Iter (f m) i z = Iter (f m) nr z}.
Proof.
intros.
unfold nr in |- *.
apply ex_i.
 tauto.
 tauto.
 generalize (exd_Iter_f m (Iter_upb m z) z).
   tauto.
 generalize not_exds_rem_upb.
   simpl in |- *.
   intros.
   unfold Iter_rem in |- *; unfold Iter_upb in |- *.
   unfold Iter_rem in |- *.
   unfold Iter_upb_aux in H1.
   apply H1.
Qed.

(* A RESULT OF PERIODICITY: *)

Lemma Iter_plus:forall(m:fmap)(z:dart)(p i:nat),
 inv_hmap m -> exd m z -> 
   Iter (f m) (p + i)%nat z = Iter (f m) i z -> 
      Iter (f m) p z = z.
Proof.
induction i.
 simpl in |- *.
   assert (p + 0 = p)%nat.
  lia.
  rewrite H.
    tauto.
 simpl in |- *.
   assert (p + S i = S (p + i))%nat.
  lia.
  rewrite H.
    simpl in |- *.
    clear H.
    intros.
    assert
     (f_1 m (f m (Iter (f m) (p + i)%nat z)) = 
         f_1 m (f m (Iter (f m) i z))).
   rewrite H1.
     tauto.
   rewrite f_1_f in H2.
    rewrite f_1_f in H2.
     apply IHi.
      tauto.
      tauto.
      tauto.
     tauto.
     generalize (exd_Iter_f m i z).
       tauto.
    tauto.
    generalize (exd_Iter_f m (p + i) z).
      tauto.
Qed.

(* ITS INVERSE: *)

Lemma Iter_plus_inv:forall(m:fmap)(z:dart)(p i:nat),
 inv_hmap m -> exd m z -> 
   Iter (f m) p z = z -> 
     Iter (f m) (p + i)%nat z = Iter (f m) i z.
Proof.
induction i.
 simpl in |- *.
   assert (p + 0 = p)%nat.
  lia.
  rewrite H.
    tauto.
 simpl in |- *.
   assert (p + S i = S (p + i))%nat.
  lia.
  rewrite H.
    simpl in |- *.
    clear H.
    intros.
    rewrite IHi.
   tauto.
   tauto.
   tauto.
   tauto.
Qed.

(* AND n TIMES: *)

Lemma Iter_mult:forall(m:fmap)(z:dart)(n p:nat),
 inv_hmap m -> exd m z -> 
     Iter (f m) p z = z ->  
       Iter (f m) (n*p)%nat z = z.
Proof.
induction n.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   rewrite Iter_plus_inv.
    apply (IHn p H H0 H1).
  tauto.
  tauto.
  tauto.
Qed.

(* PERIODICITY + n TIMES: *)

Lemma Iter_plus_mult:forall(m:fmap)(z:dart)(n p i:nat),
 inv_hmap m -> exd m z -> 
    Iter (f m) p z = z -> 
      Iter (f m) (i + n*p)%nat z = Iter (f m) i z.
Proof.
intros.
induction n.
 simpl in |- *.
   assert (i + 0 = i)%nat.
  lia.
  rewrite H2.
    tauto.
 simpl in |- *.
   assert (i + (p + n * p) = p + (i + n * p))%nat.
  lia.
  rewrite H2.
    rewrite Iter_plus_inv.
   tauto.
   tauto.
   tauto.
   tauto.
Qed.

Lemma Iter_comp:forall(m:fmap)(i j:nat)(z:dart),
  Iter (f m) (i+j)%nat z =
      Iter (f m) i (Iter (f m) j z).
Proof.
induction i.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   rewrite IHi.
   tauto.
Qed.

Lemma f_1_Iter_f:forall(m:fmap)(i:nat)(z:dart),
  inv_hmap m -> exd m z ->
    (f_1 m) (Iter (f m) (S i) z) = Iter (f m) i z.
Proof.
induction i.
 simpl in |- *.
   intros.
   apply f_1_f.
  trivial.
  trivial.
 simpl in |- *.
   intros.
   rewrite f_1_f.
  tauto.
  tauto.
  assert (f m (Iter (f m) i z) = Iter (f m) (S i) z).
   simpl in |- *.
     tauto.
   rewrite H1.
     generalize (exd_Iter_f m (S i) z).
     tauto.
Qed. 

Lemma Iter_f_f_1  :forall(m:fmap)(i j:nat)(z:dart),
  inv_hmap m -> exd m z -> (j <= i)%nat ->
    Iter (f_1 m) j (Iter (f m) i z) = 
        Iter (f m) (i - j)%nat z.
Proof.
 induction i.
 intros.
   assert (j = 0)%nat.
  lia.
  rewrite H2.
    simpl in |- *.
    trivial.
 induction j.
  simpl in |- *.
    tauto.
  intros.
    simpl in |- *.
    assert (f m (Iter (f m) i z) = Iter (f m) (S i) z).
   simpl in |- *.
     tauto.
   rewrite H2.
     rewrite IHj.
    assert (S i - j = S (i - j))%nat.
     lia.
     rewrite H3.
       apply f_1_Iter_f.
      trivial.
      trivial.
    trivial.
    trivial.
    lia.
Qed.

Lemma Iter_f_f_1_i:forall(m:fmap)(i:nat)(z:dart),
  inv_hmap m -> exd m z -> 
    Iter (f_1 m) i (Iter (f m) i z) = z. 
Proof.
intros.
rewrite Iter_f_f_1.
 assert (i - i = 0)%nat.
  lia.
  rewrite H1.
    simpl in |- *.
    trivial.
 trivial.
 trivial.
 lia.
Qed.

(* IMMEDIATE: USEFUL *)

Lemma Iter_f_Si:forall(m:fmap)(i:nat)(z:dart),
  inv_hmap m -> exd m z -> 
    Iter (f m) (S i) z = Iter (f m) i (f m z).
Proof.
simpl in |- *.
intros.
induction i.
 simpl in |- *.
    tauto.
simpl in |- *.
  rewrite IHi in |- *.
   tauto.
Qed.

(* IMMEDIATE: USEFUL *)

Lemma Iter_f_1_Si:forall(m:fmap)(i:nat)(z:dart),
  inv_hmap m -> exd m z -> 
    Iter (f_1 m) (S i) z = Iter (f_1 m) i (f_1 m z).
Proof.
simpl in |- *.
intros.
induction i.
 simpl in |- *.
    tauto.
simpl in |- *.
  rewrite IHi in |- *.
   tauto.
Qed.
   
(*===================================================
                nr IS THE LOWEST PERIOD... 
===================================================*)

Definition diff_int_aux
  (m:fmap)(z:dart)(a b:nat)(t:dart): Prop:=
   forall i : nat, (a <= i <= b)%nat -> 
     Iter (f m) i z <> t.

Lemma diff_int_aux_dec:forall(m:fmap)(z:dart)(a b:nat)(t:dart),
  {diff_int_aux m z a b t} + {~diff_int_aux m z a b t}.
Proof.
intros.
elim (Arith.Compare_dec.le_gt_dec b a).
 intro.
   elim (Nat.eq_dec a b).
  intro.
    rewrite <- a1.
    elim (eq_dart_dec (Iter (f m) a z) t).
   intro.
     right.
     unfold diff_int_aux in |- *.
     intro.
     generalize a2.
     apply H.
     lia.
   intro.
     left.
     unfold diff_int_aux in |- *.
     intros.
     assert (i = a).
    lia.
    rewrite H0.
      tauto.
  intro.
    left.
    unfold diff_int_aux in |- *.
    intros.
    lia.
 induction b.
  intro.
    absurd (0 > a)%nat.
   lia.
   tauto.
  intro.
    elim (Nat.eq_dec a b).
   intro.
     rewrite a0.
     elim (eq_dart_dec (Iter (f m) b z) t).
    intro.
      right.
      unfold diff_int_aux in |- *.
      intro.
      generalize a1.
      apply H.
      lia.
    intro.
      elim (eq_dart_dec (Iter (f m) (S b) z) t).
     intro.
       right.
       unfold diff_int_aux in |- *.
       intro.
       generalize a1.
       apply H.
       lia.
     intro.
       left.
       unfold diff_int_aux in |- *.
       intros.
       assert (i = b \/ i = S b).
      lia.
      elim H0.
       intro.
         rewrite H1.
         tauto.
       intro.
         rewrite H1.
         tauto.
   intro.
     assert (b > a)%nat.
    lia.
    elim (IHb H).
     intro.
       elim (eq_dart_dec (Iter (f m) (S b) z) t).
      intro.
        right.
        unfold diff_int_aux in |- *.
        intro.
        generalize a1.
        apply H0.
        lia.
      intro.
        left.
        unfold diff_int_aux in |- *.
        intros.
        unfold diff_int_aux in a0.
        elim (Nat.eq_dec i (S b)).
       intro.
         rewrite a1.
         tauto.
       intro.
         assert (a <= i <= b)%nat.
        lia.
        apply (a0 i H1).
     intro.
       right.
       unfold diff_int_aux in |- *.
       unfold diff_int_aux in b2.
       intro.
       apply b2.
       intros.
       apply H0.
       lia.
Qed.

(* DIFFERENCE IN AN INTERVAL *)

Definition diff_int
  (m:fmap)(z:dart)(a b:nat): Prop:=
   forall i j : nat, 
    (a <= i /\ i < j /\ j <= b)%nat -> 
      Iter (f m) i z <> Iter (f m) j z.

Lemma diff_int_le:forall(m:fmap)(z:dart)(a b:nat),
  (b <= a)%nat -> diff_int m z a b.
Proof.
intros.
unfold diff_int in |- *.
intros.
lia.
Qed.

Lemma diff_int_dec:forall(m:fmap)(z:dart)(a b:nat),
  {diff_int m z a b} + {~diff_int m z a b}.
Proof.
intros.
induction b.
 left.
   unfold diff_int in |- *.
   intros.
   lia.
 elim IHb.
  intro.
    generalize (diff_int_aux_dec m z a b 
       (Iter (f m) (S b) z)).
    intros.
    elim H.
   intro.
     clear IHb H.
     left.
     unfold diff_int in |- *.
     intros.
     unfold diff_int in a0.
     unfold diff_int_aux in a1.
     elim (Nat.eq_dec j (S b)).
    intro.
      rewrite a2.
      apply a1.
      lia.
    intro.
      apply a0.
      lia.
   intro.
     clear IHb H.
     unfold diff_int_aux in b0.
     right.
     unfold diff_int in |- *.
     intro.
     apply b0.
     intros.
     apply H.
     lia.
  intro.
    unfold diff_int in b0.
    right.
    unfold diff_int in |- *.
    intro.
    apply b0.
    intros.
    apply H.
    lia.
Qed.

(* EXISTENCY Of THE z^i IN AN INTERVAL *)

Definition exds_int(m:fmap)(z:dart)(a b:nat)(s:set):Prop:=
  forall i:nat, (a <= i <= b)%nat ->  
    exds s (Iter (f m) i z).

Lemma exds_int_gt:forall(m:fmap)(z:dart)(a b:nat)(s:set),
  (b < a)%nat -> exds_int m z a b s.
Proof.
intros.
unfold exds_int in |- *.
intros.
absurd (b < a)%nat.
 lia.
 tauto.
Qed.

Lemma exds_int_dec : forall(m:fmap)(z:dart)(a b:nat)(s:set),
  {exds_int m z a b s} + {~exds_int m z a b s}.
Proof.
intros.
elim (Arith.Compare_dec.le_gt_dec a b).
 intro.
   induction b.
  elim (exds_dec s z).
   intro.
     left.
     unfold exds_int in |- *.
     intros.
     assert (i = 0)%nat.
    lia.
    rewrite H0.
      simpl in |- *.
      tauto.
   intro.
     right.
     unfold exds_int in |- *.
     intro.
     apply b.
     assert (exds s (Iter (f m) 0%nat z)).
    apply H.
      lia.
    simpl in H0.
      tauto.
  elim (Nat.eq_dec a (S b)).
   intro.
     rewrite <- a1.
     elim (exds_dec s (Iter (f m) a z)).
    intro.
      left.
      unfold exds_int in |- *.
      intros.
      assert (i = a).
     lia.
     rewrite H0.
       tauto.
    intro.
      right.
      unfold exds_int in |- *.
      intro.
      apply b0.
      apply H.
      lia.
   intro.
     assert (a <= b)%nat.
    lia.
    elim (IHb H).
     intro.
       elim (exds_dec s (Iter (f m) (S b) z)).
      intro.
        left.
        unfold exds_int in |- *.
        intros.
        elim (Nat.eq_dec i (S b)).
       intro.
         rewrite a3.
         tauto.
       intro.
         unfold exds_int in a1.
         apply a1.
         lia.
      intro.
        right.
        unfold exds_int in |- *.
        intro.
        apply b1.
        apply H0.
        lia.
     intro.
       right.
       unfold exds_int in |- *.
       intro.
       apply b1.
       unfold exds_int in |- *.
       intros.
       apply H0.
       lia.
 intro.
   left.
   apply exds_int_gt.
   lia.
Qed. 

(* OK: *)

Lemma rem_1_step :forall(m:fmap)(z:dart)(s:set),
 inv_hmap m ->  
   let sr:= Iter_rem_aux m z s in
   let nr:= Iter_upb_aux m z s in
     (card sr + 1 <= card s <-> 
       exds s (Iter (f m) (ndN m - card s) z))%nat. 
Proof.
simpl in |- *.
intros.
generalize (Iter_rem_aux_equation m z s).
simpl in |- *.
intro.
split.
 intro.
   generalize H0.
   elim (exds_dec s (Iter (f m) (ndN m - card s) z)).
  tauto.
  intros.
    rewrite H2 in H1.
    absurd (card s + 1 <= card s)%nat.
   lia.
   tauto.
 intro.
   generalize (LQ2 m z s H1).
   intro.
 lia.
Qed.

(* OK: *)

Lemma rem_2_steps :forall(m:fmap)(z:dart)(s:set),
 inv_hmap m -> 
   let sr:= Iter_rem_aux m z s in
   let nr:= Iter_upb_aux m z s in
     (card sr + 2 <= card s -> 
       exds (Ds s (Iter (f m) (ndN m - card s) z)) 
         (Iter (f m) (ndN m + 1 - card s) z))%nat. 
Proof.
intros.
generalize (rem_1_step m z 
   (Ds s (Iter (f m) (ndN m - card s)%nat z)) H).
simpl in |- *.
generalize (rem_1_step m z s H).
simpl in |- *.
intros.
assert (card (Iter_rem_aux m z s) + 1 <= card s)%nat.
 unfold sr in H0. clear H1 H2.
   lia.
 assert (exds s (Iter (f m) (ndN m - card s)%nat z)).
  tauto.
  generalize (Iter_rem_aux_equation m z s).
    simpl in |- *.
    elim 
  (exds_dec s (Iter (f m) (ndN m - card s) z)).
   intros.
     assert 
 (card (Ds s (Iter (f m) (ndN m - card s) z)) + 1 
        = card s)%nat.
    rewrite exds_card_Ds.
     clear H1 H2 H3 H4 a H5.
       lia.
     tauto.
    assert 
 (card (Ds s (Iter (f m) (ndN m - card s) z)) 
        = card s - 1)%nat.
     clear H1 H2 H3 H4 a H5.
       lia.
     unfold sr in H0.
       rewrite H7 in H2.
       rewrite <- H5 in H2.
       assert (card (Iter_rem_aux m z s) + 1 
         <= card s - 1)%nat.
      clear H1 H2 H3 H4 a H5 H6 H7.
        lia.
      assert (ndN m + 1 - card s = 
         ndN m - (card s - 1))%nat.
       clear H1 H2 H3 H4 a H5 H6 H7 H8.
         lia.
       rewrite <- H9 in H2.
         tauto.
   tauto.
Qed.

(* OK: ALL z^i FOR n0 <=i <= nr-1 EXIST IN s: *)

Definition P6(m:fmap)(z:dart)(s:set):Prop:= 
 inv_hmap m ->
  (card s <= ndN m ->
   let n0:= ndN m - card s in
   let nr:= Iter_upb_aux m z s in
    exds s (Iter (f m) n0 z) -> 
      exds_int m z n0 (nr - 1) s)%nat.

(* OK: LONG... *)

Lemma LP6:forall(m:fmap)(z:dart)(s:set),
 inv_hmap m ->
  (card s <= ndN m ->
   let n0:= ndN m - card s in
   let nr:= Iter_upb_aux m z s in
    exds s (Iter (f m) n0 z) -> 
      exds_int m z n0 (nr - 1) s)%nat.
Proof.
intros m z.
refine (well_founded_ind Rs_wf (P6 m z) _).
unfold P6 in |- *.
unfold Iter_upb_aux in |- *.
intros.
generalize (LQ1 m z x).
intro.
generalize (Iter_rem_aux_equation m z x).
simpl in |- *.
intro.
rewrite H4.
generalize H4.
simpl in |- *.
elim (exds_dec x (Iter (f m) (ndN m - card x) z)).
 intros.
   clear H4.
   generalize 
  (exds_card_Ds x (Iter (f m) 
      (ndN m - card x)%nat z) a).
   intro.
   generalize 
 (H (Ds x (Iter (f m) (ndN m - card x)%nat z))).
   intros.
   generalize (rem_1_step m z x H0).
   simpl in |- *.
   intros.
   assert (card (Iter_rem_aux m z x) + 1
      <= card x)%nat.
  tauto.
  clear H7.
    elim (Nat.eq_dec (card (Iter_rem_aux m z x) + 1) 
      (card x))%nat.
   intro.
     rewrite <- H5.
     assert (ndN m - card (Iter_rem_aux m z x) - 1 
      = ndN m - card x)%nat.
    clear H3 H4 H8.
      lia.
    rewrite H7.
      unfold exds_int in |- *.
      intros.
      assert (i = ndN m - card x)%nat.
     clear H1 H3 H4 H8 a0 H7.
       lia.
     rewrite H10.
       tauto.
   intro.
     assert 
  (card (Iter_rem_aux m z x) + 2 <= card x)%nat.
    clear H1 H3 H4.
      lia.
    generalize (rem_2_steps m z x H0 H7).
      intro.
      rewrite H4 in H6.
      assert 
    (ndN m - (card x - 1) = ndN m + 1 - card x)%nat.
     clear H3 H4 H5 H8 b.
       lia.
     rewrite H10 in H6.
       rewrite <- H5.
       rewrite <- H5 in H6.
       unfold exds_int in |- *.
       intros.
       elim (Nat.eq_dec (ndN m - card x) i)%nat.
      intro.
        rewrite <- a0.
        tauto.
      intro.
        assert
         (exds_int m z (ndN m + 1 - card x)
          (ndN m - card (Iter_rem_aux m z x) - 1)
        (Ds x (Iter (f m) (ndN m - card x) z)))%nat.
       apply H6.
        unfold Rs in |- *.
          clear H1 H3 H5 H8 b H10 H11 b0.
          lia.
        tauto.
        clear H3 H5 H4 H8 H7 H10 H11 b0.
          lia.
        tauto.
       unfold exds_int in H12.
         assert (exds (Ds x (Iter (f m) 
       (ndN m - card x) z)) (Iter (f m) i z))%nat.
        apply H12.
          clear H10.
          clear H1 H3 H5 H4 H8 H7 H8 b.
          lia.
        eapply exds_Ds_exds.
          apply H13.
 tauto.
Qed.

(* OK: FOR ALL n0 < j <= nr-1, z^n0 <> z^j: 
LENGHT: SYMPLIFY: TOO MUCH lias... *)

Definition P7(m:fmap)(z:dart)(s:set):Prop:= 
 inv_hmap m ->
  (card s <= ndN m ->
   let n0:= ndN m - card s in
   let nr:= Iter_upb_aux m z s in
   exds s (Iter (f m) n0 z) -> 
     forall j:nat, n0 < j <= nr - 1 ->
       Iter (f m) n0 z <> Iter (f m) j z)%nat.

Lemma LP7:forall(m:fmap)(z:dart)(s:set),
inv_hmap m ->
  (card s <= ndN m ->
   let n0:= ndN m - card s in
   let nr:= Iter_upb_aux m z s in
   exds s (Iter (f m) n0 z) -> 
     forall j:nat, n0 < j <= nr - 1 ->
       Iter (f m) n0 z <> Iter (f m) j z)%nat.
Proof.
intros m z.
refine (well_founded_ind Rs_wf (P7 m z) _).
unfold P7 in |- *.
unfold Iter_upb_aux in |- *.
intros.
generalize (LQ1 m z x).
generalize (rem_1_step m z x H0).
simpl in |- *.
intro.
assert (card (Iter_rem_aux m z x) + 1 <= card x)%nat.
 tauto.
 clear H4.
   intro.
   clear H4.

   elim (Nat.eq_dec (card (Iter_rem_aux m z x) + 1) 
        (card x))%nat.
  intro.
    clear H5.
    lia.
  intro.
    assert (card (Iter_rem_aux m z x) + 2 
         <= card x)%nat.
   lia.
   generalize (rem_2_steps m z x H0 H4).
     intro.
     clear b H5.
     elim
      (eq_dart_dec (Iter (f m) (ndN m - card x) z)
         (Iter (f m) 
    (ndN m - card (Iter_rem_aux m z x) - 1) z))%nat.
    intros.
      assert
 (card (Ds x (Iter (f m) (ndN m - card x) z)) 
        = card x - 1)%nat.
     rewrite exds_card_Ds.
      tauto.
      tauto.
     assert
 (card (Ds x (Iter (f m) (ndN m - card x) z)) 
           <= ndN m)%nat.
      lia.
      generalize (LP6 m z 
  (Ds x (Iter (f m) (ndN m - card x) z)) H0 H7)%nat.
        simpl in |- *.
        intros.
        rewrite H5 in H8.
        unfold Iter_upb_aux in H8.
        generalize (Iter_rem_aux_equation m z x).
        simpl in |- *.
        elim 
    (exds_dec x (Iter (f m) (ndN m - card x) z)).
       intros.
         clear a0.
         rewrite <- H9 in H8.
         assert (ndN m - (card x - 1) = 
             ndN m + 1 - card x)%nat.
        clear H3 a H5 H7 H9.
          lia.
        rewrite H10 in H8.
          generalize (H8 H6).
          intro.
          clear H8.
          unfold exds_int in H11.
          assert
        (exds (Ds x (Iter (f m) (ndN m - card x) z))
              (Iter (f m) 
    (ndN m - card (Iter_rem_aux m z x) - 1) z))%nat.
         apply H11.
           split.
          clear H3 a H H7 H9 H10.
            lia. 
          apply le_n.
         rewrite <- a in H8.
           absurd
         (exds (Ds x (Iter (f m) (ndN m - card x) z))
               (Iter (f m) (ndN m - card x) z))%nat.
          apply not_exds_Ds.
          tauto.
       tauto.
    intros.
      elim (Nat.eq_dec 
      (ndN m - card (Iter_rem_aux m z x) - 1) j)%nat.
     intro.
       rewrite <- a.
       tauto.
     intro.
       generalize (H (Ds x (Iter (f m)
          (ndN m - card x) z)))%nat.
       intro.
       assert
        (forall j : nat,
  ndN m - 
  card (Ds x (Iter (f m) (ndN m - card x) z)) 
   < j <= ndN m - card (Iter_rem_aux m z 
  (Ds x (Iter (f m) (ndN m - card x) z))) - 1 ->
         Iter (f m) 
  (ndN m - card (Ds x (Iter (f m) 
 (ndN m - card x) z))) z <> Iter (f m) j z)%nat.
      apply H5.
       unfold Rs in |- *.
         rewrite exds_card_Ds.
        clear H1 H3 b b0.
          lia.
        tauto.
       tauto.
       generalize (exds_card_Ds x 
         (Iter (f m) (ndN m - card x) z) H2)%nat.
         intro.
         rewrite H7.
         clear H3 H4 b b0 H7.
         lia.
       generalize (exds_card_Ds x 
          (Iter (f m) (ndN m - card x) z) H2)%nat.
         intro.
         rewrite H7.
         assert (ndN m - (card x - 1) = 
           ndN m + 1 - card x)%nat.
        clear H3 b b0 H7.
          lia.
        rewrite H8.
          tauto.
      clear H5.
        generalize (exds_card_Ds x 
           (Iter (f m) (ndN m - card x) z) H2)%nat.
        intro.
        rewrite H5 in H7.
        generalize (Iter_rem_aux_equation m z x).
        simpl in |- *.
      elim 
   (exds_dec x (Iter (f m) (ndN m - card x) z))%nat.
       intros.
         clear a.
         rewrite <- H8 in H7.
         assert (ndN m - (card x - 1) = 
    ndN m + 1 - card x)%nat.
        clear H3 b b0 H5 H8.
          lia.
        rewrite H9 in H7.
          intro.
          assert (Iter (f m) (S (ndN m - card x)) z 
             = Iter (f m) (S j) z)%nat.
         simpl in |- *.
           rewrite H10.
           tauto.
         generalize H11.
           assert (S (ndN m - card x) = 
    ndN m + 1 - card x)%nat.
          clear H9.
            clear H5.
            clear H3 b b0 H8 H10 H11.
            lia.
          rewrite H12.
            apply H7.
            split.
           rewrite <- H12.
             apply -> Nat.succ_lt_mono.
             tauto.
           clear H12.
             clear H9.
             clear H5.
             clear H4.
             clear H1 b H8 H10 H11.
             elim H3.
             intros.
             clear H1.
             clear H3.
             lia.
       tauto.
Qed.

(* OK: FOR ALL n0 <= i < j <= nr-1, z^i <> z^j: 
LENGHT: SYMPLIFY: TOO MUCH lias... *)

Definition P8(m:fmap)(z:dart)(s:set):Prop:= 
 inv_hmap m ->
  (card s <= ndN m ->
   let n0:= ndN m - card s in
   let nr:= Iter_upb_aux m z s in
    exds s (Iter (f m) n0 z) -> 
     diff_int m z n0 (nr - 1))%nat.

Lemma LP8:forall(m:fmap)(z:dart)(s:set),
 inv_hmap m ->
  (card s <= ndN m ->
   let n0:= ndN m - card s in
   let nr:= Iter_upb_aux m z s in
    exds s (Iter (f m) n0 z) -> 
     diff_int m z n0 (nr - 1))%nat.
Proof.
intros m z.
refine (well_founded_ind Rs_wf (P8 m z) _).
unfold P8 in |- *.
unfold Iter_upb_aux in |- *.
intros.
generalize (rem_1_step m z x H0).
simpl in |- *.
intro.
assert (card (Iter_rem_aux m z x) + 1 <= card x)%nat.
 tauto.
 clear H3.
   elim (Nat.eq_dec (card (Iter_rem_aux m z x) + 1) 
       (card x))%nat.
  intro.
    clear H4.
    assert (ndN m - card (Iter_rem_aux m z x) - 1 
         = ndN m - card x)%nat.
   lia.
   rewrite H3.
     apply diff_int_le.
     apply le_n.
  intro.
    assert 
 (card (Iter_rem_aux m z x) + 2 <= card x)%nat.
   lia.
   clear b H4.
     generalize (rem_2_steps m z x H0 H3).
     intro.
     generalize (LP7 m z x H0 H1 H2).
     intro.
     unfold diff_int in |- *.
     intros.
     elim (Nat.eq_dec (ndN m - card x) i)%nat.
    intro.
      rewrite <- a.
      unfold Iter_upb_aux in H5.
      apply H5.
      split.
     rewrite a.
       tauto.
     tauto.
    intro.
      assert
  (card (Ds x (Iter (f m) (ndN m - card x) z))
          = card x - 1)%nat.
     rewrite exds_card_Ds.
      tauto.
      tauto.
     generalize (Iter_rem_aux_equation m z x).
       simpl in |- *.
       elim 
   (exds_dec x (Iter (f m) (ndN m - card x) z))%nat.
      intros.
        clear a.
        clear H5.
     generalize
 (H (Ds x (Iter (f m) (ndN m - card x) z)))%nat.
        intros.
        assert
 (diff_int m z 
 (ndN m - 
     card (Ds x (Iter (f m) (ndN m - card x) z)))
      (ndN m -
        card (Iter_rem_aux m z 
  (Ds x (Iter (f m) (ndN m - card x) z))) - 1))%nat.
       apply H5.
        unfold Rs in |- *.
          apply exds_card_Ds_inf.
          tauto.
        tauto.
        rewrite H7.
          lia.
        rewrite H7.
          assert (ndN m - (card x - 1) = 
             ndN m + 1 - card x)%nat.
         clear H5.
           clear H.
           clear H8.
           lia.
         rewrite H9.
           tauto.
       clear H5 H.
         rewrite <- H8 in H9.
         unfold diff_int in H9.
         rewrite H7 in H9.
         apply H9.
         split.
        clear H8 H9.
          clear H1 H3 H4.
          clear H0.
          lia.
        tauto.
      tauto.
Qed.

(* ALL DARTS IN AN f-ORBIT ARE DISTINCT: *)  

Definition diff_orb(m:fmap)(z:dart):Prop:=
 let nr:= Iter_upb_aux m z (fmap_to_set m) in
  (diff_int m z 0 (nr - 1))%nat.

Theorem exd_diff_orb:forall(m:fmap)(z:dart),
   inv_hmap m -> exd m z ->
      diff_orb m z.
intros.
unfold diff_orb in |- *.
generalize (nd_card m).
intro.
assert (ndN m - card (fmap_to_set m) = 0)%nat.
 rewrite H1.
   lia.
 cut
  (diff_int m z (ndN m - card (fmap_to_set m))
     (Iter_upb_aux m z (fmap_to_set m) - 1))%nat.
  rewrite H2.
    tauto.
  apply LP8.
   tauto.
   rewrite H1.
     apply le_n.
   rewrite H2.
     simpl in |- *.
     generalize (exd_exds m z).
     tauto.
Qed.

(* OK: nr IS A PERIOD OF THE f-ORBIT 
(IN FACT, IT IS THE LOWEST ONE, SINCE n0 = 0 
AND ALL z^i DIFFER FROM z = z^n0 = z^0, FOR n0 < i <= nr-1) *)

Theorem Iter_upb_period:forall(m:fmap)(z:dart),
 inv_hmap m -> exd m z ->
  let nr:= Iter_upb m z in
    Iter (f m) nr z = z.
Proof.
simpl in |- *.
intros.
generalize (ex_i_upb m z H H0).
simpl in |- *.
intros.
elim H1.
intros i Hi.
clear H1.
elim (Nat.eq_dec i 0%nat).
 intro.
   rewrite a in Hi.
   simpl in Hi.
   symmetry  in |- *.
   tauto.
 intro.
   decompose [and] Hi.
   clear Hi.
   assert (f_1 m (Iter (f m) i z) =
         f_1 m (Iter (f m) (Iter_upb m z) z)).
  rewrite H2.
    tauto.
  set (i1 := (i - 1)%nat) in |- *.
    set (nr1 := (Iter_upb m z - 1)%nat) in |- *.
    assert (i = S i1).
   unfold i1 in |- *.
     lia.
   assert (Iter_upb m z = S nr1).
    unfold nr1 in |- *.
      lia.
    rewrite H5 in H3.
      rewrite H4 in H3.
      simpl in H3.
      rewrite f_1_f in H3.
     rewrite f_1_f in H3.
      unfold i1 in H3.
        unfold nr1 in H3.
        absurd (Iter (f m) (i - 1)%nat z = 
     Iter (f m) (Iter_upb m z - 1)%nat z).
       generalize (LP8 m z (fmap_to_set m) H).
         simpl in |- *.
         intros.
         unfold diff_int in H6.
         assert
          (forall i j : nat,
           ndN m - card (fmap_to_set m) <= i /\
        i < j <= 
         Iter_upb_aux m z (fmap_to_set m) - 1 ->
           Iter (f m) i z <> Iter (f m) j z)%nat.
        apply H6.
         rewrite nd_card.
           apply le_n.
   assert (ndN m - card (fmap_to_set m) = 0)%nat.
          rewrite nd_card.
            simpl in |- *.
            lia.
          rewrite H7.
            simpl in |- *.
            generalize (exd_exds m z).
            tauto.
        apply H7.
          split.
         clear H6.
           clear H7.
           clear H2.
           rewrite nd_card.
           lia.
         clear H7 H6.
           clear H2.
           split.
          lia.
          unfold Iter_upb in |- *.
            unfold Iter_upb_aux in |- *.
            unfold Iter_rem in |- *.
            apply le_n.
       tauto.
      tauto.
      generalize (exd_Iter_f m nr1 z).
        tauto.
     tauto.
     generalize (exd_Iter_f m i1 z).
       tauto.
Qed.

(* WE HAVE: z^(i + n*p) = z^i FOR ALL i *)

Lemma Iter_period:forall(m:fmap)(z:dart)(i n:nat),
 inv_hmap m -> exd m z ->
  let p:= Iter_upb m z in
    Iter (f m) (i + n*p)%nat z = Iter (f m) i z.
Proof.
intros.
intros.
assert (Iter (f m) p z = z).
 unfold p in |- *.
   apply Iter_upb_period.
  tauto.
  tauto.
 rewrite Iter_plus_mult.
  trivial.
  assumption.
  assumption.
  assumption.
Qed.

(* WE HAVE: z^i = z^(i mod p) FOR ALL i *)

From Stdlib Require Import Euclid.

(* RECALL:
modulo
     : forall n : nat,
       n > 0 ->
       forall m : nat, 
    {r : nat | exists q : nat, 
                m = q * n + r /\ n > r}
*)

Lemma mod_p:forall(m:fmap)(z:dart)(i:nat),
 inv_hmap m -> exd m z ->
  let p := Iter_upb m z in
   {j :nat | Iter (f m) i z  = 
       Iter (f m) j z /\ (j < p)%nat}.
Proof.
intros.
assert (p > 0)%nat.
 unfold p in |- *.
   generalize (upb_pos m z H0).
   intro.
   lia.
 generalize (modulo p H1 i).
   intro.
   elim H2.
   intros r Hr.
   split with r.
   elim Hr.
   intros q Hq.
   elim Hq.
   clear Hq.
   intros.
   split.
  rewrite H3.
    rewrite Nat.add_comm.
    unfold p in |- *.
    rewrite Iter_period.
   trivial.
   tauto.
   tauto.
  lia.
Qed.

From Stdlib Require Export Compare.

(* ALL DARTS IN AN f-ORBIT HAVE THE SAME PERIOD: *) 

Lemma period_uniform : forall(m:fmap)(z:dart)(i:nat),
 inv_hmap m -> exd m z ->
    Iter_upb m z = Iter_upb m (Iter (f m) i z).
Proof.
intros.
set (zi := Iter (f m) i z) in |- *.
set (p := Iter_upb m z) in |- *.
set (q := Iter_upb m zi) in |- *.
generalize (Iter_upb_period m z H H0).
simpl in |- *.
fold p in |- *.
intro.
assert (exd m zi).
 unfold zi in |- *.
   generalize (exd_Iter_f m i z H).
   tauto.
 generalize (Iter_upb_period m zi H H2).
   simpl in |- *.
   fold q in |- *.
   intro.
   assert 
   (Iter (f m) (i + q)%nat z = Iter (f m) q zi).
  unfold zi in |- *.
    rewrite Nat.add_comm.
    apply Iter_comp.
  assert (Iter (f m) q z = z).
   apply (Iter_plus m z q i H H0).
     fold zi in |- *.
     rewrite Nat.add_comm.
     rewrite <- H3.
     tauto.
   assert (Iter (f m) p zi = zi).
    unfold zi in |- *.
      rewrite <- Iter_comp.
      rewrite Nat.add_comm.
      assert (i + p = i + 1 * p)%nat.
     lia.
     rewrite H6.
       unfold p in |- *.
       rewrite Iter_period.
      trivial.
      trivial.
      trivial.
    clear H4.
      elim (Arith.Compare_dec.lt_eq_lt_dec p q).
     intro.
       elim a.
      clear a.
        intro.
        generalize (exd_diff_orb m zi H H2).
        unfold diff_orb in |- *.
        unfold Iter_upb in q.
        unfold Iter_rem in q.
        unfold Iter_upb_aux in |- *.
        fold q in |- *.
        unfold diff_int in |- *.
        intros.
        absurd (Iter (f m) p zi = zi).
       intro.
         symmetry  in H7.
         replace zi with (Iter (f m) 0%nat zi) in H7.
        generalize H7.
          clear H7.
          apply H4.
          split.
         lia.
         split.
          unfold p in |- *.
            apply upb_pos.
            tauto.
          lia.
        simpl in |- *.
          trivial.
       tauto.
      tauto.
     intro.
       generalize (exd_diff_orb m z H H0).
       unfold diff_orb in |- *.
       unfold Iter_upb in p.
       unfold Iter_rem in p.
       unfold Iter_upb_aux in |- *.
       fold p in |- *.
       unfold diff_int in |- *.
       intros.
       symmetry  in H5.
       absurd (z = Iter (f m) q z).
      replace z with (Iter (f m) 0%nat z).
       apply H4.
         split.
        lia.
        split.
         unfold q in |- *.
           apply upb_pos.
           tauto.
         lia.
       simpl in |- *.
         trivial.
      tauto.
Qed.

(* UNICITY OF THE INDICE mod p: *)

Lemma unicity_mod_p:forall(m:fmap)(z:dart)(j k:nat),
 inv_hmap m -> exd m z ->
  let p := Iter_upb m z in
   (j < p)%nat -> (k < p)%nat -> 
    Iter (f m) j z = Iter (f m) k z -> j = k.
Proof.
intros.
generalize (exd_diff_orb m z H H0).
unfold diff_orb in |- *.
unfold Iter_upb in p.
unfold Iter_upb_aux in |- *.
unfold Iter_rem in p.
fold p in |- *.
unfold diff_int in |- *.
intros.
elim (Arith.Compare_dec.le_gt_dec j k).
 elim (Nat.eq_dec j k).
  intros.
    tauto.
  intros.
    absurd (Iter (f m) j z = Iter (f m) k z).
   apply (H4 j k).
     lia.
   tauto.
 intro.
   symmetry in H3.
   absurd (Iter (f m) k z = Iter (f m) j z).
  apply (H4 k j).
    lia.
  tauto. 
Qed.

(*===================================================
                 PATHS in f-ORBITS:
===================================================*)

(* REFLEXIVE EXISTENCE OF A PATH: *)

Definition expo(m:fmap)(z t:dart):Prop:=
   exd m z /\ exists i:nat, Iter (f m) i z = t.

(* FOR THE DECIDABILITY: *)

Definition expo1
 (m:fmap)(z t:dart):Prop:=
  exd m z /\
   let p:= Iter_upb m z in 
    exists j:nat, (j < p)%nat /\ Iter (f m) j z = t.

Lemma expo_expo1: 
  forall(m:fmap)(z t:dart), inv_hmap m ->
    (expo m z t <-> expo1 m z t). 
Proof.
unfold expo in |- *.
unfold expo1 in |- *.
intros.
unfold expo in |- *.
unfold expo1 in |- *.
intros.
split.
 intros.
   elim H0.
   clear H0.
   intros.
   split.
  tauto.
  elim H1.
    intros i Hi.
    clear H1.
    generalize (mod_p m z i H H0).
    simpl in |- *.
    intros.
    elim H1.
    intros j Hj.
    split with j.
    split.
   tauto.
   rewrite Hi in Hj.
     symmetry  in |- *.
     tauto.
 intros.
   elim H0.
   clear H0.
   intros.
   split.
  tauto.
  elim H1.
    intros.
    split with x.
    tauto.
Qed.

(* OK, GIVES THE "SMALLEST" INDICE j ST zj = zi: *)

Definition modulo(m:fmap)(z:dart)(i:dart)
    (hi:inv_hmap m)(he:exd m z):nat.
Proof.
intros.
assert
 (let p := Iter_upb m z in
  {j : nat | 
   Iter (f m) i z = Iter (f m) j z /\ (j < p)%nat}).
 apply mod_p.
  tauto.
  tauto.
 simpl in H.
   elim H.
   intros.
   apply x.
Defined.

(* EXISTENCE OF THE EXTREMITY DARTS: *)

Lemma expo_exd:
  forall(m:fmap)(z t:dart),
   inv_hmap m -> expo m z t -> exd m t.
Proof.
unfold expo in |- *.
intros.
decompose [and] H0.
elim H2.
intros i Hi.
rewrite <- Hi.
generalize (exd_Iter_f m i z).
tauto.
Qed.

(* REFLEXIVITY: *)

Lemma expo_refl:
  forall(m:fmap)(z:dart), exd m z -> expo m z z.
Proof.
intros.
unfold expo in |- *.
split.
 tauto.
 split with 0%nat.
   simpl in |- *.
   tauto.
Qed.

(* TRANSITIVITY: *)

Lemma expo_trans:
  forall(m:fmap)(z t u:dart),
  expo m z t -> expo m t u -> expo m z u.
Proof.
unfold expo in |- *.
intros.
intuition.
elim H2.
intros j Hj.
elim H3.
intros i Hi.
split with (i + j)%nat.
rewrite Iter_comp.
rewrite Hj.
tauto.
Qed.

(* SYMMETRY: OK!! *)

Lemma expo_symm:forall(m:fmap)(z t:dart),
  inv_hmap m -> 
     expo m z t -> expo m t z.
Proof.
intros m z t Hm He.
assert (exd m t).
 apply expo_exd with z.
  tauto.
  tauto.
 unfold expo in |- *.
   unfold expo in He.
   intuition.
   elim H1.
   intros i Hi.
   rewrite <- Hi.
   clear H1.
   generalize (mod_p m z i Hm H0).
   intro.
   simpl in H1.
   elim H1.
   intros r Hr.
   elim Hr.
   clear Hr H1.
   intros.
   split with (Iter_upb m z - r)%nat.
   rewrite H1.
   rewrite <- Iter_comp.
   assert (Iter_upb m z - r + r = Iter_upb m z)%nat.
  lia.
  rewrite H3.
    apply Iter_upb_period.
   tauto.
   tauto.
Qed.

Lemma expo_f:forall(m:fmap)(z:dart),
  exd m z -> expo m z (f m z).
Proof.
  unfold expo. intros. 
   split. tauto. split with 1. simpl. tauto. 
Qed.
  
Lemma expo_f_1:forall(m:fmap)(z:dart),
  inv_hmap m -> exd m z -> expo m z (f_1 m z).
Proof.
  intros. unfold expo. intros. 
   split. tauto. 
     set(p:=Iter_upb m z). 
      split with (p-1). rewrite <- Iter_f_f_1. simpl. 
     unfold p. rewrite Iter_upb_period. tauto.
tauto. tauto. tauto. tauto. 
   generalize (upb_pos m z H0). fold p. intro. lia. 
Qed.

(* THERE EXISTS j <= n S.T. zj = t: INDUCTIVE DEF. *)

Fixpoint ex_j
 (m:fmap)(z t:dart)(n:nat){struct n}:Prop:=
match n with
   0%nat => z = t
 | S n0 => Iter (f m) n z = t \/ ex_j m z t n0
end. 

Lemma ex_j_dec:
 forall(m:fmap)(z t:dart)(n:nat),
  {ex_j m z t n} + {~ex_j m z t n}.
Proof.
induction n.
 simpl in |- *.
   apply eq_dart_dec.
 simpl in |- *.
   generalize (eq_dart_dec (f m (Iter (f m) n z)) t).
   tauto.
Qed.

(* THERE EXISTS j <= n S.T. zj = t: COMMON DEF. EQUIVALENT TO INDUCTIVE DEF.: *)

Lemma ex_j_exist_j:forall(m:fmap)(z t:dart)(n:nat),
  ex_j m z t n <-> 
   exists j :nat, (j <= n)%nat /\ Iter (f m) j z = t.
Proof.
induction n.
 simpl in |- *.
   split.
  intro.
    split with 0%nat.
    split.
   lia.
   simpl in |- *.
     tauto.
  intro.
    elim H.
    intros j Hj.
    intuition.
    inversion H0.
    rewrite H2 in H1.
    simpl in |- *.
    simpl in H1.
    tauto.
 simpl in |- *.
   split.
  intro.
    elim H.
   intro.
     split with (S n).
     split. clear IHn.
    lia.
    simpl in |- *.
      tauto.
   intro.
     assert (exists j : nat, (j <= n)%nat 
            /\ Iter (f m) j z = t).
    tauto.
    elim H1.
      intros j Hj.
      split with j.
      split. clear H0 IHn.
     lia.
     tauto.
  intros.
    elim H.
    intros j Hj.
    elim (Nat.eq_dec j (S n)).
   intro.
     rewrite a in Hj.
     simpl in Hj.
     tauto.
   intro.
     assert (exists j : nat, (j <= n)%nat 
        /\ Iter (f m) j z = t).
    split with j.
      split. clear IHn.
     lia.
     tauto.
    tauto.
Qed.

(* t IS A ITERATED SUCC OF z IN AN ORBIT IS EQUIVALENT TO:
there exists j <= p-1 s.t. zj = t: *)

Lemma expo1_ex_j: 
  forall(m:fmap)(z t:dart), inv_hmap m -> exd m z ->
  let p:= Iter_upb m z in
    (ex_j m z t (p - 1)%nat <-> expo1 m z t).
Proof.
intros.
generalize (Iter_upb_period m z H H0).
generalize (upb_pos m z H0).
rename H into hm.
rename H0 into hz.
fold p in |- *.
intros Hp1 Hp2.
generalize (ex_j_exist_j m z t (p - 1)%nat).
unfold expo1 in |- *.
fold p in |- *.
intros.
split.
 intro.
   assert (exists j : nat, (j <= p - 1)%nat 
       /\ Iter (f m) j z = t).
  tauto.
  elim H1.
    intros j Hj.
    split.
   tauto.
   split with j.
     split. clear H H0.
    lia.
    tauto.
 intro.
   elim H0.
   intros.
   elim H2.
   clear H0 H2.
   intros i Hj.
   assert (exists j : nat, (j <= p - 1)%nat 
        /\ Iter (f m) j z = t).
  split with i.
    split. clear H. 
   lia.
   tauto.
  tauto.
Qed.

(* DECIDABILITY OF expo1: *)

Lemma expo1_dec : 
  forall (m:fmap)(z t:dart), 
   inv_hmap m -> exd m z ->
     {expo1 m z t} + {~expo1 m z t}.
Proof.
intros.
set (p := Iter_upb m z) in |- *.
generalize (ex_j_dec m z t (p - 1)).
intro.
elim H1.
 intro.
   left.
   generalize (expo1_ex_j m z t H H0).
   simpl in |- *.
   fold p in |- *.
   tauto.
 intro.
   right.
   intro.
   generalize (expo1_ex_j m z t H H0).
   simpl in |- *.
   fold p in |- *.
   tauto.
Qed.

(* DECIDABILITY: OK!! *)

Lemma expo_dec: forall(m:fmap)(z t:dart),
  inv_hmap m ->  
    {expo m z t} + {~expo m z t}.
Proof.
intros m z t hm.
generalize (expo_expo1 m z t hm).
generalize (expo1_dec m z t hm).
intros.
elim (exd_dec m z).
 tauto.
 unfold expo in |- *.
   tauto.
Qed.

(* ALL DARTS OF AN ORBIT HAVE THE SAME period: *)

Theorem period_expo : forall(m:fmap)(z t:dart),
 inv_hmap m -> expo m z t ->
    Iter_upb m z = Iter_upb m t.
Proof.
unfold expo in |- *.
intros.
elim H0.
clear H0.
intros.
elim H1.
intros i Hi.
rewrite <- Hi.
apply period_uniform.
 tauto.
 tauto.
Qed.

Open Scope nat_scope. 

(* SUMMARY: nr IS THE LOWEST nat > 0 S.T.
z^nr = z AND 0 < i < nr -> z^i <> z: OK *)

Theorem period_lub : forall(m:fmap)(z:dart),
 inv_hmap m -> exd m z ->
  let nr:= Iter_upb m z in
   0 < nr /\ Iter (f m) nr z = z /\
    forall i:nat, 0 < i < nr -> Iter (f m) i z <> z.
Proof.
intros.
split.
 unfold nr in |- *.
   apply upb_pos.
    tauto.
split.
 unfold nr in |- *.
   apply Iter_upb_period.
   tauto.
  tauto.
intros.
  generalize (exd_diff_orb m z).
  unfold diff_orb in |- *.
  unfold Iter_upb in nr.
  unfold Iter_rem in nr.
  unfold Iter_upb_aux in |- *.
  fold nr in |- *.
  unfold diff_int in |- *.
  intros.
  assert
   (forall i j : nat,
    0 <= i /\ i < j <= nr - 1 -> 
       Iter (f m) i z <> Iter (f m) j z).
  tauto.
clear H2.
  generalize (H3 0 i).
  intros.
  simpl in H2.
  intro.
  symmetry  in H4.
  apply H2.
 split.
   lia.
  lia.
assumption.
Qed.

(*===================================================
          COMPLEMENTS FOR cell degrees (July 08)
===================================================*)

From Stdlib Require Import Recdef.

Open Scope nat_scope. 

(* FOLLOWING: *)

Lemma ndN_pos:forall(m:fmap)(z:dart),
  exd m z -> 0 < ndN m.
Proof.
induction m.
 simpl in |- *.
    tauto.
simpl in |- *.
  intros.
  elim (exd_dec m d).
 intro.
   apply IHm with d.
    tauto.
intro.
   lia.
simpl in |- *.
   tauto.
Qed.

(* degree OF A CELL: OK! *)

Function degree_aux(m:fmap)(z:dart)(n:nat)
   {measure (fun i:nat => ndN m - i) n}:nat:=
  if Compare_dec.le_lt_dec n (ndN m) 
  then if eq_dart_dec z (Iter (f m) n z) then n
       else if Nat.eq_dec n (ndN m) then (ndN m) + 1 
            else degree_aux m z (n+1)
  else (ndN m) + 1.
Proof.
intros.
lia.
Defined.

Definition degree(m:fmap)(z:dart):= 
  degree_aux m z 1.

Definition P_degree_pos(m:fmap)(z:dart)(n1 n2:nat):
  Prop:= exd m z -> 0 < n1 -> 0 < n2.

Lemma degree_pos_aux:forall(m:fmap)(z:dart),
  P_degree_pos m z 1 (degree m z).
Proof.
unfold degree in |- *.
intros.
apply degree_aux_ind.
 intros.
   unfold P_degree_pos in |- *.
    tauto.
intros.
  unfold P_degree_pos in |- *.
  intros.
   lia.
intros.
  unfold P_degree_pos in |- *.
  unfold P_degree_pos in H.
  assert (0 < n + 1).
  lia.
 tauto.
intros.
  unfold P_degree_pos in |- *.
  intros.
   lia.
Qed.

Theorem degree_pos:forall(m:fmap)(z:dart),
   exd m z -> 0 < degree m z.
Proof.
unfold degree in |- *.
intros.
generalize (degree_pos_aux m z).
unfold P_degree_pos in |- *.
unfold degree in |- *.
intros.
assert (0 < 1).
  lia.
 tauto.
Qed.

Definition P_degree_diff(m:fmap)(z:dart)(n1 n2:nat):
  Prop:= inv_hmap m -> exd m z -> 0 < n1 ->  
   forall i:nat, n1 <= i < n2 -> Iter (f m) i z <> z.

Lemma degree_diff_aux:forall(m:fmap)(z:dart),
  P_degree_diff m z 1 (degree m z).
Proof.
unfold degree in |- *.
intros.
apply degree_aux_ind.
 intros.
   unfold P_degree_diff in |- *.
   intros.
    lia.
intros.
  unfold P_degree_diff in |- *.
  intros.
  rewrite _x1 in H2.
  assert (i = n).
 rewrite _x1 in |- *.
    lia.
rewrite H3 in |- *.
  intro.
  symmetry  in H4.
  assert (z <> Iter (f m) n z).
 apply _x0.
 tauto.
intros.
  unfold P_degree_diff in |- *.
  unfold P_degree_diff in H.
  intros.
  elim (Nat.eq_dec n i).
 intro.
   rewrite <- a in |- *.
   intro.
   assert (z <> Iter (f m) n z).
  apply _x0.
 symmetry  in H4.
    tauto.
intro.
  apply H.
  tauto.
 tauto.
 lia.
split.
  lia.
 tauto.
intros.
  unfold P_degree_diff in |- *.
  intros.
   lia.
Qed.

Theorem degree_diff: forall (m:fmap)(z:dart),
  inv_hmap m -> exd m z -> 
    forall i:nat, 0 < i < (degree m z) -> 
       Iter (f m) i z <> z.
Proof.
intros.
generalize (degree_diff_aux m z).
unfold P_degree_diff in |- *.
intros.
assert (forall i : nat, 1 <= i < degree m z -> Iter (f m) i z <> z).
 apply H2.
   tauto.
  tauto.
  lia.
apply H3.
   lia.
Qed.

Lemma degree_bound: forall (m:fmap)(z:dart),
  inv_hmap m -> exd m z -> degree m z <= ndN m.
Proof.
intros.
elim (Arith.Compare_dec.le_lt_dec (degree m z) (ndN m)).
  tauto.
intro.
  generalize (degree_diff m z H H0).
  intro.
  set (nr := Iter_upb m z) in |- *.
  assert (Iter (f m) nr z = z).
 unfold nr in |- *.
   apply Iter_upb_period.
   tauto.
  tauto.
assert (nr <= ndN m).
 unfold nr in |- *.
   unfold Iter_upb in |- *.
    lia.
 absurd (Iter (f m) nr z = z).
 apply H1.
   split.
  unfold nr in |- *.
    apply upb_pos.
     tauto.
  lia.
 tauto.
Qed.

(* OK: *)

Definition P_degree_per(m:fmap)(z:dart)(n1 n2:nat):
  Prop:= inv_hmap m -> exd m z -> 
   0 < n1 -> n2 <= ndN m ->  
       Iter (f m) n2 z = z.

Lemma degree_per_aux: forall(m:fmap)(z:dart),
    P_degree_per m z 1 (degree m z).
Proof.
unfold degree in |- *.
intros.
apply degree_aux_ind.
 intros.
   unfold P_degree_per in |- *.
   symmetry  in |- *.
    tauto.
intros.
  unfold P_degree_per in |- *.
  intros.
   absurd (ndN m + 1 <= ndN m).
  lia.
 tauto.
intros.
  unfold P_degree_per in |- *.
  unfold P_degree_per in H.
  intros.
  apply H.
  tauto.
 tauto.
 lia.
 tauto.
intros.
  unfold P_degree_per in |- *.
  intros.
   absurd (ndN m + 1 <= ndN m).
  lia.
 tauto.
Qed.

Theorem degree_per: forall (m:fmap)(z:dart),
  inv_hmap m -> exd m z -> 
    Iter (f m) (degree m z) z = z.
Proof.
intros.
apply degree_per_aux.
  tauto.
 tauto.
 lia.
apply degree_bound.
  tauto.
 tauto.
Qed.

(* SUMMARY: OK *)

Theorem degree_lub: forall(m:fmap)(z:dart),
 inv_hmap m -> exd m z ->
 let p:= degree m z in
   0 < p /\ Iter (f m) p z = z /\
    forall i:nat, 0 < i < p -> Iter (f m) i z <> z.
Proof.
intros.
unfold p in |- *.
split.
 apply degree_pos.
    tauto.
split.
 apply degree_per.
   tauto.
  tauto.
apply degree_diff.
  tauto.
 tauto.
Qed.

Require Import Arith.

(* OK!! *)

Theorem upb_eq_degree:forall(m:fmap)(z:dart),
 inv_hmap m -> exd m z ->
   Iter_upb m z = degree m z. 
Proof.
intros.
set (p := degree m z) in |- *.
set (nr := Iter_upb m z) in |- *.
generalize (period_lub m z H H0).
generalize (degree_lub m z H H0).
simpl in |- *.
fold p in |- *.
fold nr in |- *.
intros.
decompose [and] H1.
clear H1.
decompose [and] H2.
clear H2.
elim (lt_eq_lt_dec nr p).
 intro.
   elim a.
  intro.
     absurd (Iter (f m) nr z = z).
   apply H6.
      lia.
   tauto.
  tauto.
intro.
   absurd (Iter (f m) p z = z).
 apply H8.
    lia.
 tauto.
Qed.

(* IMMEDIATELY, REPLACING Iter_upb by degree: *)

Theorem expo_degree : forall(m:fmap)(z t:dart),
 inv_hmap m -> expo m z t ->
    degree m z = degree m t.
Proof.
intros.
generalize (period_expo m z t H H0).
rewrite upb_eq_degree in |- *.
 rewrite upb_eq_degree in |- *.
   tauto.
  tauto.
 apply (expo_exd m z t H H0).
 tauto.
unfold expo in H0.
   tauto.
Qed.

Theorem degree_uniform : forall(m:fmap)(z:dart)(i:nat),
 inv_hmap m -> exd m z ->
    degree m z = degree m (Iter (f m) i z).
Proof.
intros.
generalize (period_uniform m z i H H0).
rewrite upb_eq_degree in |- *.
 rewrite upb_eq_degree in |- *.
   tauto.
  tauto.
 generalize (exd_Iter_f m i z).
    tauto.
 tauto.
 tauto.
Qed.

Theorem degree_unicity:forall(m:fmap)(z:dart)(j k:nat),
 inv_hmap m -> exd m z ->
  let p := degree m z in
   j < p -> k < p -> 
    Iter (f m) j z = Iter (f m) k z -> j = k.
Proof.
intros.
generalize (unicity_mod_p m z j k H H0).
simpl in |- *.
rewrite upb_eq_degree in |- *.
 fold p in |- *.
    tauto.
 tauto.
 tauto.
Qed.

(* TO EXPRESS ALL WITH degree *)

Definition expo2
 (m:fmap)(z t:dart):Prop:=
  exd m z /\
   let p:= degree m z in 
    exists j:nat, (j < p)%nat /\ Iter (f m) j z = t.

Lemma expo1_expo2: 
  forall(m:fmap)(z t:dart), inv_hmap m ->
    (expo1 m z t <-> expo2 m z t). 
Proof.
intros.
unfold expo1 in |- *; unfold expo2 in |- *.
split.
 intro.
   rewrite <- upb_eq_degree in |- *.
   tauto.
  tauto.
  tauto.
intro.
  rewrite upb_eq_degree in |- *.
  tauto.
 tauto.
 tauto.
Qed.

Lemma expo_expo2: 
  forall(m:fmap)(z t:dart), inv_hmap m ->
    (expo m z t <-> expo2 m z t). 
Proof.
intros.
generalize (expo_expo1 m z t H).
generalize (expo1_expo2 m z t H).
 tauto.
Qed.

Open Scope R_scope. 

(*===================================================
  COMPLEMENTS FOR orbits AND rem , BOUNDS 
              (AUGUST 08)
===================================================*)

(* ANY orbit IS INCLUDED IN THE hmap SUPPORT: OK: *)

Lemma incls_orbit:forall(m:fmap)(x:dart),
 inv_hmap m -> exd m x ->
  incls (Iter_orb m x) (fmap_to_set m).
Proof.
intros.
apply exds2.
intro.
unfold Iter_orb in |- *.
generalize (exds_set_minus_eq (fmap_to_set m) 
   (Iter_rem m x) z).
 tauto.
Qed.

Lemma exds_orb_exd:forall(m:fmap)(x z:dart),
 inv_hmap m -> exd m x ->
  exds (Iter_orb m x) z -> exd m z.
Proof.
intros.
generalize (incls_orbit m x H H0).
intro.
inversion H2.
generalize (H3 z H1).
intro.
generalize (exd_exds m z).
 tauto.
Qed.

(* ANY REMAINING set IS INCLUDED IN THE hmap SUPPORT: OK: *)

Lemma incls_rem:forall(m:fmap)(x:dart),
 inv_hmap m -> exd m x ->
  incls (Iter_rem m x) (fmap_to_set m).
Proof.
unfold Iter_rem in |- *.
intros.
apply exds2.
intro.
intro.
generalize (LR3 m x z (fmap_to_set m)).
simpl in |- *.
generalize (exds_dec (fmap_to_set m) z).
generalize (exds_dec (Iter_rem_aux m x (fmap_to_set m)) z).
 tauto.
Qed.

(* card OF orbit: OK *)

Lemma card_orbit:forall(m:fmap)(x:dart),
  inv_hmap m -> exd m x ->
      card (Iter_orb m x) = Iter_upb m x.
Proof.
unfold Iter_orb in |- *.
unfold Iter_upb in |- *.
intros.
generalize (incls_rem m x H H0).
intros.
rewrite nd_card in |- *.
generalize (card_minus_set (fmap_to_set m) 
  (Iter_rem m x) H1).
intro.
 lia.
Qed.

(* EACH dart OF AN orbit IS ITERATED: *)

Lemma exds_orb_ex :forall(m:fmap)(z t:dart),
 inv_hmap m -> exd m z -> 
   let s:= Iter_orb m z in
   let p:= Iter_upb m z in
    exds s t ->
      {i : nat | (i < p)%nat /\ Iter (f m) i z = t}.
Proof.
intros.
intros.
assert (exd m t).
 generalize (incls_orbit m z H H0).
   intro.
   inversion H2.
   generalize (H3 t H1).
   intro.
   generalize (exd_exds m t).
    tauto.
assert (~ exds (Iter_rem m z) t).
 generalize (exds_rem_orb m z t H H2).
    tauto.
apply (ex_i m z t H H0 H2 H3).
Qed.

(* CHARACTERIZATION OF orbit: *)

Theorem exds_orb_eq_ex :forall(m:fmap)(z t:dart),
 inv_hmap m -> exd m z -> 
   let s:= Iter_orb m z in
   let p:= Iter_upb m z in
 (exds s t <-> 
   exists i:nat,(i < p)%nat /\ Iter (f m) i z = t).
Proof.
split.
 intro.
   generalize (exds_orb_exd m z t H H0 H1).
   intro.
   generalize (exds_orb_ex m z t H H0 H1).
   intro.
   elim H3.
   intros.
   split with x.
    tauto.
intros.
  elim H1.
  intros i Hi.
  clear H1.
  decompose [and] Hi.
  clear Hi.
  rewrite <- H2 in |- *.
  apply exds_Iter_f_i.
  tauto.
 tauto.
 lia.
Qed.

Open Scope nat_scope.

(* IDEM, LARGE *)

Theorem exds_orb_eq_ex_large :forall(m:fmap)(z t:dart),
 inv_hmap m -> exd m z -> 
   let s:= Iter_orb m z in
   let p:= Iter_upb m z in
 (exds s t <-> exists i:nat, Iter (f m) i z = t).
Proof.
split.
 intro.
   generalize (exds_orb_exd m z t H H0 H1).
   intro.
   generalize (exds_orb_eq_ex m z t H H0).
   simpl in |- *.
   intro.
   assert (exists i : nat, 
  i < Iter_upb m z /\ Iter (f m) i z = t).
   tauto.
 clear H3.
   elim H4.
   intros.
   split with x.
    tauto.
intro.
  assert (expo m z t).
 unfold expo in |- *.
   split.
   tauto.
  tauto.
generalize (expo_expo1 m z t H).
  unfold expo1 in |- *.
  intro.
  assert (exists j : nat, 
     j < Iter_upb m z /\ Iter (f m) j z = t).
  tauto.
generalize (exds_orb_eq_ex m z t H H0).
  simpl in |- *.
   tauto.
Qed.

(* COROLLARIES: OK *)

Theorem expo_eq_exds_orb :forall(m:fmap)(z t:dart),
 inv_hmap m -> exd m z -> 
 (expo m z t <-> exds (Iter_orb m z) t).
Proof.
intros.
generalize (exds_orb_eq_ex_large m z t H H0).
simpl in |- *.
intro.
unfold expo in |- *.
 tauto.
Qed.

Theorem expo1_eq_exds_orb :forall(m:fmap)(z t:dart),
 inv_hmap m -> exd m z -> 
 (expo1 m z t <-> exds (Iter_orb m z) t).
Proof.
intros.
generalize (exds_orb_eq_ex m z t H H0).
simpl in |- *.
intro.
unfold expo1 in |- *.
 tauto.
Qed.

(* EQUIVALENCE OF ORBITS: *)

(* EASY, OK: *)

Lemma impls_orb:forall(m:fmap)(x y:dart),
  inv_hmap m -> exd m x -> 
    expo m x y -> 
     impls (Iter_orb m x) (Iter_orb m y).
Proof.
unfold impls in |- *.
intros.
assert (exd m y).
 generalize (expo_exd m x y).
    tauto.
generalize (exds_orb_eq_ex_large m x z H H0).
  intros.
  generalize (exds_orb_eq_ex_large m y z H H3).
  intro.
  assert (exd m z).
 generalize (exd_exds m z).
   intro.
   generalize (incls_orbit m x H H0).
   intro.
   inversion H7.
   generalize (H8 z H2).
    tauto.
simpl in H4.
  assert (exists i : nat, Iter (f m) i x = z).
  tauto.
elim H7.
  clear H7.
  intros i Hi.
  assert (expo m x z).
 unfold expo in |- *.
   split.
   tauto.
 split with i.
    tauto.
assert (expo m y z).
 apply expo_trans with x.
  apply expo_symm.
    tauto.
   tauto.
  tauto.
assert (exists i : nat, Iter (f m) i y = z).
 unfold expo in H8.
    tauto.
simpl in H5.
   tauto.
Qed.

Lemma eqs_orb:forall(m:fmap)(x y:dart),
  inv_hmap m ->  
    expo m x y -> 
     eqs (Iter_orb m x) (Iter_orb m y).
Proof.
unfold eqs in |- *.
intros.
assert (exd m x).
 unfold expo in H0.
    tauto.
assert (exd m y).
 apply expo_exd with x.
   tauto.
  tauto.
split.
 generalize (impls_orb m x y H H1 H0).
   unfold impls in |- *.
   intro.
   apply H3.
assert (expo m y x).
 apply expo_symm.
   tauto.
  tauto.
generalize (impls_orb m y x H H2 H3).
  unfold impls in |- *.
  intro.
  apply H4.
Qed.

(* RCP: *)

Lemma orb_impls_expo:forall(m:fmap)(x y:dart),
  inv_hmap m -> exd m x -> exd m y ->
     impls (Iter_orb m x) (Iter_orb m y) -> expo m x y.
Proof.
intros.
unfold impls in H2.
generalize (H2 x).
intro.
assert (exds (Iter_orb m x) x).
 generalize (expo_eq_exds_orb m x x H H0).
   intro.
   assert (expo m x x).
  apply expo_refl.
     tauto.
  tauto.
apply expo_symm.
  tauto.
generalize (expo_eq_exds_orb m y x H H1).
   tauto.
Qed.

(* THEN, THE RESULT: *)

Theorem expo_eq_eqs_orb:forall(m:fmap)(x y:dart),
  inv_hmap m -> exd m x -> exd m y ->
(expo m x y <-> eqs (Iter_orb m x) (Iter_orb m y)).
Proof.
split.
 apply (eqs_orb m x y H).
unfold eqs in |- *.
  intro.
  generalize (orb_impls_expo m x y H H0 H1).
  unfold impls in |- *.
  intro.
  assert (forall z : dart, 
     exds (Iter_orb m x) z -> exds (Iter_orb m y) z).
 intro.
   intro.
   generalize (H2 z).
    tauto.
 tauto.
Qed.

(* ORBITS ARE DISJOINED, OK: *)

Lemma disjs_orb:forall(m:fmap)(x y:dart),
  inv_hmap m -> exd m x -> exd m y -> 
   ~expo m x y -> 
     disjs (Iter_orb m x) (Iter_orb m y).
Proof.
unfold disjs.
intros.
assert (exd m z).
 generalize (incls_orbit m x H H0).
   intro.
   inversion H5.
   clear H5.
   generalize (H6 z).
   intro.
   assert (exds (fmap_to_set m) z).
   tauto.
 clear H6 H5.
   generalize (exd_exds m z).
    tauto.
generalize (exds_orb_eq_ex m x z H H0).
  generalize (exds_orb_eq_ex m y z H H1).
  simpl in |- *.
  set (px := Iter_upb m x) in |- *.
  set (py := Iter_upb m y) in |- *.
  intros.
  assert (exists i : nat, i < py /\ 
      Iter (f m) i y = z).
  tauto.
clear H6.
  assert (exists i : nat, i < px /\ 
      Iter (f m) i x = z).
  tauto.
clear H7.
  elim H8.
  intros i Hi.
  clear H8.
  elim H6.
  intros j Hj.
  clear H6.
  decompose [and] Hi.
  clear Hi.
  intros.
  decompose [and] Hj.
  clear Hj.
  intros.
  assert (expo m y z).
 unfold expo in |- *.
   split.
   tauto.
 split with i.
    tauto.
assert (expo m x z).
 unfold expo in |- *.
   split.
   tauto.
 split with j.
    tauto.
elim H2.
  apply expo_trans with z.
  tauto.
apply expo_symm.
  tauto.
 tauto.
Qed.

(* RCP: *)

Lemma disjs_orb_not_expo:forall(m:fmap)(x y:dart),
  inv_hmap m -> exd m x -> exd m y -> 
 disjs (Iter_orb m x) (Iter_orb m y) -> ~expo m x y.
Proof.
unfold disjs in |- *.
intros.
generalize (H2 x).
intros.
assert (exds (Iter_orb m x) x).
 generalize (expo_eq_exds_orb m x x H H0).
   intro.
   assert (expo m x x).
  apply expo_refl.
     tauto.
  tauto.
intro.
  assert (expo m y x).
 apply expo_symm.
   tauto.
  tauto.
generalize (expo_eq_exds_orb m y x H H1).
   tauto.
Qed.

(* THEN, THE RESULT: *)

Theorem not_expo_disjs_orb:forall(m:fmap)(x y:dart),
  inv_hmap m -> exd m x -> exd m y -> 
   (~expo m x y <-> 
     disjs (Iter_orb m x) (Iter_orb m y)).
Proof.
split.
 apply (disjs_orb m x y H H0 H1).
apply (disjs_orb_not_expo m x y H H0 H1).
Qed.

Lemma incls_minus: forall(m:fmap)(x y:dart),
  inv_hmap m -> exd m x -> exd m y -> 
   ~expo m x y ->
     let s:= fmap_to_set m in
     let sx:= Iter_orb m x in
     let sy:= Iter_orb m y in
      incls sy (set_minus s sx).
Proof.
intros.
apply exds2.
intros.
apply exds_set_minus.
 generalize (incls_orbit m y H H1).
   intro.
   inversion H4.
   fold s in H5.
   apply H5.
   fold sy in |- *.
    tauto.
intro.
  generalize (disjs_orb m x y H H0 H1 H2).
  unfold disjs in |- *.
  intro.
  apply (H5 z H4 H3).
Qed.

Open Scope nat_scope.

(* THE SUM OF TWO degrees IS BOUNDED : OK *)

Theorem upb_sum_bound: forall(m:fmap)(x y:dart),
   inv_hmap m -> exd m x -> exd m y -> ~expo m x y ->
     Iter_upb m x + Iter_upb m y <= ndN m.
Proof.
intros.
rewrite <- card_orbit in |- *.
 rewrite <- card_orbit in |- *.
  set (s := fmap_to_set m) in |- *.
    set (sx := Iter_orb m x) in |- *.
    set (sy := Iter_orb m y) in |- *.
    generalize (incls_minus m x y H H0 H1 H2).
    simpl in |- *.
    fold s in |- *.
    fold sx in |- *.
    fold sy in |- *.
    intro.
    generalize (incls_orbit m x H H0).
    fold s in |- *.
    fold sx in |- *.
    intro.
    generalize (card_minus_set s sx H4).
    intro.
    generalize (card_minus_set (set_minus s sx) sy H3).
    intro.
    generalize (nd_card m).
    intro.
    fold s in H7.
    rewrite H7 in |- *.
    clear H7.
     lia.
  tauto.
  tauto.
 tauto.
 tauto.
Qed.

(* THEN, COROLLARY: *)

Theorem degree_sum_bound: forall(m:fmap)(x y:dart),
   inv_hmap m -> exd m x -> exd m y -> ~expo m x y ->
     degree m x + degree m y <= ndN m.
Proof.
intros.
rewrite <- upb_eq_degree in |- *.
 rewrite <- upb_eq_degree in |- *.
  apply (upb_sum_bound m x y H H0 H1 H2).
  tauto.
  tauto.
 tauto.
 tauto.
Qed.

Open Scope R_scope.

(*===================================================
                between in f-ORBITS:
===================================================*)

(* v IS between z AND t IN AN f-ORBIT: *)

Definition between(m:fmap)(z v t:dart):Prop:=
 inv_hmap m -> exd m z ->  
  exists i:nat, exists j:nat, 
   Iter (f m) i z = v /\
     Iter (f m) j z = t /\
       (i <= j < Iter_upb m z)%nat.

(* OK: *)

Lemma between_expo1:forall(m:fmap)(z v t:dart),
  inv_hmap m -> exd m z -> 
    between m z v t ->
      expo1 m z v /\ expo1 m z t. 
Proof.
unfold between in |- *.
intros.
generalize (H1 H H0).
clear H1.
intro.
elim H1.
intros i Hi.
clear H1.
elim Hi.
clear Hi.
intros j Hj.
decompose [and] Hj.
clear Hj.
unfold expo1 in |- *.
split.
 split.
  tauto.
  split with i.
    split.
   lia.
   tauto.
 split.
  tauto.
  split with j.
    split.
   tauto.
   tauto.
Qed.

Lemma between_expo:forall(m:fmap)(z v t:dart),
  inv_hmap m -> exd m z -> 
    between m z v t ->
      expo m z v /\ expo m z t. 
Proof.
intros.
generalize (between_expo1 m z v t H H0 H1).
intros.
generalize (expo_expo1 m z v H).
generalize (expo_expo1 m z t H).
tauto.
Qed.

(* OK: *)

Lemma between_expo_refl_1:forall(m:fmap)(z t:dart),
  inv_hmap m -> exd m z -> 
    (between m z z t <-> expo1 m z t). 
Proof.
intros.
unfold between in |- *.
unfold expo1 in |- *.
split.
 intros.
   generalize (H1 H H0).
   clear H1.
   intro.
   elim H1.
   clear H1.
   intros i Hi.
   elim Hi.
   intros j Hj.
   split.
  tauto.
  split with j.
    tauto.
 intros.
   intuition.
   elim H5.
   intros i Hi.
   clear H5.
   split with 0%nat.
   split with i.
   simpl in |- *.
   split.
  tauto.
  split.
   tauto.
lia.
Qed.

(* IDEM: *)

Lemma between_expo_refl_2:forall(m:fmap)(z t:dart),
  inv_hmap m -> exd m z -> 
    (between m z t t <-> expo1 m z t). 
Proof.
intros.
unfold between in |- *.
unfold expo1 in |- *.
split.
 intros.
   generalize (H1 H H0).
   clear H1.
   intro.
    intuition.
   elim H1.
   clear H1.
   intros i Hi.
   elim Hi.
   intros j Hj.
   split with j.
    tauto.
intros.
  decompose [and] H1.
  clear H1.
  elim H5.
  clear H5.
  intros j Hj.
  split with j.
  split with j.
  split.
  tauto.
split.
  tauto.
split.
  lia.
 tauto.
Qed.

Lemma expo_between_1:forall(m:fmap)(z t:dart),
  inv_hmap m -> exd m z -> 
    (expo1 m z t <-> between m z t (f_1 m z)).  
Proof.
intros.
rename H0 into Ez.
unfold between in |- *.
unfold expo1 in |- *.
split.
 intros.
   intuition.
   elim H4.
   intros j Hj.
   clear H4.
   split with j.
   split with (Iter_upb m z - 1)%nat.
   split.
  tauto.
  split.
   set (nr := Iter_upb m z) in |- *.
     assert (Iter (f m) nr z = z).
    unfold nr in |- *.
      apply Iter_upb_period.
     tauto.
     tauto.
    assert (0 < nr)%nat.
     unfold nr in |- *.
       apply upb_pos.
       tauto.
     assert (f_1 m (Iter (f m) nr z) = f_1 m z).
      rewrite H0.
        tauto.
      rewrite <- Iter_f_f_1.
       simpl in |- *.
         tauto.
       tauto.
       tauto.
       lia.
   lia.
 intros.
   split.
  tauto.
  intuition.
    elim H0.
    clear H0.
    intros i Hi.
    elim Hi.
    intros j Hj.
    split with i.
    split.
   lia.
   tauto.
Qed.

Lemma expo_between_3:forall(m:fmap)(x y z:dart),
  inv_hmap m -> expo1 m x y -> expo1 m x z -> 
 between m x z y \/ between m (f m y) z (f_1 m x). 
Proof.
unfold expo1 in |- *.
unfold between in |- *.
intros.
intuition.
elim H3.
clear H3.
intros i Hi.
elim H4.
intros j Hj.
clear H4.
elim (le_lt_dec j i).
 intro.
   left.
   intros.
   split with j.
   split with i.
   split.
  tauto.
  split.
   tauto.
   lia.
 intro.
   right.
   intros.
   intuition.
   split with (j - i - 1)%nat.
   split with (Iter_upb m x - (2 + i))%nat.
   assert (Iter_upb m (f m y) = Iter_upb m x).
  rewrite <- H5.
    assert (Iter (f m) (S i) x = 
        f m (Iter (f m) i x)).
   simpl in |- *.
     tauto.
   rewrite <- H8.
     rewrite <- period_uniform.
    tauto.
    tauto.
    tauto.
  split.
   rewrite <- H5.
  assert (f m (Iter (f m) i x) = Iter (f m) (S i) x).
    simpl in |- *.
      tauto.
    rewrite H9.
      rewrite <- Iter_comp.
      assert (j - i - 1 + S i = j)%nat.
     lia.
     rewrite H10.
       tauto.
   split.
    rewrite <- H5.
   assert (f m (Iter (f m) i x) = 
        Iter (f m) (S i) x).
     simpl in |- *.
       tauto.
     rewrite H9.
       rewrite <- Iter_comp.
       assert (Iter_upb m x - (2 + i) + S i = 
                Iter_upb m x - 1)%nat.
      lia.
      rewrite H10.
        rewrite <- f_1_Iter_f.
   assert (S (Iter_upb m x - 1) = Iter_upb m x)%nat.
        lia.
        rewrite H11.
          rewrite Iter_upb_period.
         tauto.
         tauto.
         tauto.
       tauto.
       tauto.
    rewrite H8.
      lia.
Qed.

(* DECIDABILITY OF between *)

Lemma existi_dec:forall(m:fmap)(z v:dart)(k:nat),
(exists i:nat, (i < k)%nat /\ Iter (f m) i z = v) \/
(~exists i:nat, (i < k)%nat /\ Iter (f m) i z = v).
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
  elim (eq_dart_dec (Iter (f m) k z) v).
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
  elim (Nat.eq_dec i k).
 intro.
   rewrite a in Hi.
    tauto.
intro.
  split.
  lia.
 tauto.
Qed.

(* THEN, between_dec IN Prop *)

Lemma between_dec:
 forall(m:fmap)(z v t:dart), inv_hmap m -> exd m z ->
    (between m z v t \/ ~between m z v t).
Proof.
intros.
set (p := Iter_upb m z) in |- *.
generalize (existi_dec m z v p).
generalize (existi_dec m z t p).
intros.
elim H1.
 elim H2.
  clear H1 H2.
    intros.
    elim H1.
    intros i Hi.
    clear H1.
    elim H2.
    intros j Hj.
    clear H2.
    decompose [and] Hi.
    clear Hi.
    intros.
    decompose [and] Hj.
    clear Hj.
    intros.
    elim (le_lt_dec i j).
   intro.
     left.
     unfold between in |- *.
     split with i.
     split with j.
      tauto.
  intro.
    right.
    unfold between in |- *.
    intro.
    elim H5.
   intros i0 Hi.
     clear H5.
     elim Hi.
     clear Hi.
     intros j0 Hj0.
     decompose [and] Hj0.
     clear Hj0.
     fold p in H9.
     assert (i = i0).
    apply (unicity_mod_p m z i i0).
      tauto.
     tauto.
    fold p in |- *.
       tauto.
    fold p in |- *.
       lia.
    rewrite H5 in |- *.
       tauto.
   assert (j = j0).
    apply (unicity_mod_p m z j j0).
      tauto.
     tauto.
    fold p in |- *.
       tauto.
    fold p in |- *.
       lia.
    rewrite H7 in |- *.
       tauto.
   rewrite H8 in b.
     rewrite H10 in b.
      lia.
   tauto.
   tauto.
 clear H2.
   clear H1.
   intros.
   right.
   unfold between in |- *.
   intro.
   elim H3.
  intros i Hi.
    clear H3.
    elim Hi.
    clear Hi.
    intros j Hj.
    fold p in Hj.
    apply H1.
    split with i.
    split.
    lia.
   tauto.
  tauto.
  tauto.
clear H1.
  clear H2.
  right.
  unfold between in |- *.
  intro.
  elim H2.
 intros i Hi.
   clear H2.
   elim Hi.
   clear Hi.
   intros j Hj.
   fold p in Hj.
   apply H1.
   split with j.
    tauto.
 tauto.
 tauto.
Qed.

End Mf.

(*===================================================
              SIGNATURE Sigd FOR DIMENSIONS
===================================================*)

Module Type Sigd.
Parameter kd:dim.
End Sigd.

(*===================================================
               FUNCTOR McA FOR cAk
===================================================*)

Module McA(Md:Sigd)<:Sigf.
Definition f := fun(m:fmap)(z:dart) => 
   cA m Md.kd z.
Definition f_1 := fun(m:fmap)(z:dart) => 
   cA_1 m Md.kd z.
Definition exd_f := 
   fun(m:fmap)(z:dart) => exd_cA m Md.kd z. 
Definition exd_f_1 := 
   fun(m:fmap)(z:dart) => exd_cA_1 m Md.kd z. 
Definition f_1_f := fun(m:fmap)(z:dart) => 
   cA_1_cA m Md.kd z.
Definition f_f_1 := fun(m:fmap)(z:dart) => 
   cA_cA_1 m Md.kd z.
End McA.

(*==================================================
        SPECIALIZATION: FUNCTOR MA FOR cA0, cA1
              WITH COMMON PROPERTIES
===================================================*)

(* COMMON INSTANTIATION TO cA0 AND cA1: *)

Module MA (Md:Sigd).
  Module McAMd:=  McA Md.
  Module MfcA := Mf McAMd.

(* DIM 0 AND 1 COMMON PROPERTIES: *)

Definition expo_exd_r:= MfcA.expo_exd.

Lemma expo_exd_l:forall(m:fmap)(z t:dart),
  inv_hmap m -> MfcA.expo m z t -> exd m z. 
Proof. unfold MfcA.expo in |- *. tauto. Qed.

Lemma expo_exd_exd:forall(m:fmap)(z t:dart),
  inv_hmap m -> MfcA.expo m z t ->
    (exd m z /\ exd m t). 
Proof.
intros.
split.
 apply (expo_exd_l m z t H H0).
apply (expo_exd_r m z t H H0).
Qed.

Lemma f_cA:forall(m:fmap)(z:dart),
    MfcA.f m z = cA m Md.kd z.
Proof. tauto. Qed.

Lemma Iter_f_cA:forall(m:fmap)(i:nat)(z:dart),
   Iter (MfcA.f m) i z = Iter (cA m Md.kd) i z.
Proof.
induction i.
 simpl in |- *;  tauto.
intro.
  simpl in |- *.
  rewrite IHi in |- *.
   tauto.
Qed.

Lemma Iter_cA_Shift: 
 forall(m:fmap)(x z:dart)(i:nat),
  inv_hmap m -> succ m Md.kd x -> 
   let m0:= Shift m Md.kd x in
    Iter (cA m0 Md.kd) i z = Iter (cA m Md.kd) i z.
Proof.
induction i.
intros; simpl; tauto.
intros; unfold m0.
unfold Iter; fold Iter.
rewrite cA_Shift.
rewrite IHi.
tauto.
    tauto.
 tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma expo_equiv:forall(m:fmap)(z t:dart),
  MfcA.expo m z t <-> 
(exd m z /\ exists i:nat, Iter (cA m Md.kd) i z = t). 
Proof.
unfold MfcA.expo in |- *.
intros.
split.
 intro.
   elim H.
   intros.
   elim H1.
   intros i Hi.
   split.
   tauto.
 split with i.
   rewrite <- Iter_f_cA in |- *.
    tauto.
intros.
  elim H.
  intros.
  elim H1.
  intros i Hi.
  split.
  tauto.
split with i.
  rewrite Iter_f_cA in |- *.
   tauto.
Qed.

(* OK: *)

Lemma expo_Shift:forall (m:fmap)(x z t:dart),
  inv_hmap m -> succ m Md.kd x ->
    let m0:= Shift m Md.kd x
      in MfcA.expo m0 z t <-> MfcA.expo m z t.
Proof.
intros.
generalize (expo_equiv m z t).
generalize (expo_equiv m0 z t).
intros.
assert (exd m z <-> exd m0 z).
 unfold m0 in |- *.
   apply (exd_Shift m Md.kd x z).
assert
 ((exists i : nat, Iter (cA m Md.kd) i z = t) <->
  (exists i : nat, Iter (cA m0 Md.kd) i z = t)).
 split.
  intro.
    elim H4.
    intros i Hi.
    split with i.
    unfold m0 in |- *.
    rewrite Iter_cA_Shift in |- *.
    tauto.
   tauto.
   tauto.
 intros.
   elim H4.
   intros i Hi.
   split with i.
   unfold m0 in Hi.
   rewrite Iter_cA_Shift in Hi.
   tauto.
  tauto.
  tauto.
 tauto.
Qed.

(* OK: *)

Lemma bottom_cA: forall(m:fmap)(z:dart),
 inv_hmap m -> exd m z -> 
   bottom m Md.kd (cA m Md.kd z) = bottom m Md.kd z. 
Proof.
induction m.
 simpl in |- *.
    tauto.
simpl in |- *.
  unfold prec_I in |- *.
  intros.
  elim (eq_dart_dec d z).
 elim (eq_dart_dec d z).
   tauto.
  tauto.
elim (eq_dart_dec d (cA m Md.kd z)).
 intros.
   rewrite a in H.
    absurd (exd m (cA m Md.kd z)).
   tauto.
 generalize (exd_cA m Md.kd z).
    tauto.
intros.
  apply IHm.
  tauto.
 tauto.
simpl in |- *.
  unfold prec_L in |- *.
  unfold succ in |- *.
  unfold pred in |- *.
  intros.
  decompose [and] H.
  clear H.
  elim (eq_dim_dec d Md.kd).
 intro.
   rewrite <- a in |- *.
   elim (eq_dart_dec d0 z).
  intro.
    elim (eq_dart_dec d1 (bottom m d d1)).
   intro.
     elim (eq_dart_dec d1 (bottom m d z)).
     tauto.
   rewrite a0 in |- *.
      tauto.
  intro.
    elim b.
    symmetry  in |- *.
    apply nopred_bottom.
    tauto.
   tauto.
  unfold pred in |- *.
     tauto.
 elim (eq_dart_dec (cA_1 m d d1) z).
  elim (eq_dart_dec d1 (bottom m d (cA m d d0))).
   intros.
     rewrite a in a0.
     rewrite IHm in a0.
    generalize H7.
      rewrite cA_eq in |- *.
     elim (succ_dec m d d0).
      unfold succ in |- *.
         tauto.
     symmetry  in a0.
       rewrite a in |- *.
        tauto.
     tauto.
    tauto.
    tauto.
  intros.
    elim (eq_dart_dec d1 (bottom m d z)).
   intros.
     rewrite a in |- *.
     apply IHm.
     tauto.
    tauto.
  intro.
    rewrite cA_1_eq in a0.
   generalize a0.
     elim (pred_dec m d d1).
    unfold pred in |- *.
       tauto.
   intros.
     rewrite <- a1 in b1.
     rewrite bottom_top in b1.
     tauto.
    tauto.
    tauto.
   unfold pred in |- *.
      tauto.
   tauto.
 elim (eq_dart_dec d1 (bottom m d (cA m d z))).
  intros.
    rewrite a in a0.
    rewrite IHm in a0.
   elim (eq_dart_dec d1 (bottom m d z)).
     tauto.
   intros.
     rewrite a in b1.
      tauto.
   tauto.
   tauto.
 rewrite <- a in IHm.
   rewrite IHm in |- *.
  intros.
    elim (eq_dart_dec d1 (bottom m d z)).
    tauto.
   tauto.
  tauto.
  tauto.
rewrite IHm in |- *.
  tauto.
 tauto.
 tauto.
Qed.

Lemma expo_bottom_ind: forall(m:fmap)(z:dart)(i:nat),
  inv_hmap m -> exd m z -> 
  let t:= Iter (cA m Md.kd) i z in
    bottom m Md.kd z = bottom m Md.kd t. 
Proof.
induction i.
 simpl in |- *.
    tauto.
simpl in IHi.
  simpl in |- *.
  intros.
  rewrite bottom_cA in |- *.
 apply IHi.
   tauto.
  tauto.
 tauto.
generalize (MfcA.exd_Iter_f m i z).
  rewrite Iter_f_cA in |- *.
   tauto.
Qed.

Lemma expo_bottom: forall(m:fmap)(z t:dart),
  inv_hmap m -> MfcA.expo m z t ->
    bottom m Md.kd z = bottom m Md.kd t. 
Proof.
intros.
unfold MfcA.expo in H0.
elim H0.
intros.
elim H2.
intros i Hi.
rewrite <- Hi in |- *.
rewrite Iter_f_cA in |- *.
apply expo_bottom_ind.
  tauto.
 tauto.
Qed.

(* SYMMETRICALLY: *)

Lemma top_cA_1: forall(m:fmap)(z:dart),
 inv_hmap m -> exd m z -> 
   top m Md.kd (cA_1 m Md.kd z) = top m Md.kd z. 
Proof.
induction m.
 simpl in |- *.
    tauto.
simpl in |- *.
  unfold prec_I in |- *.
  intros.
  elim (eq_dart_dec d z).
 elim (eq_dart_dec d z).
   tauto.
  tauto.
elim (eq_dart_dec d (cA_1 m Md.kd z)).
 intros.
   rewrite a in H.
    absurd (exd m (cA_1 m Md.kd z)).
   tauto.
 generalize (exd_cA_1 m Md.kd z).
    tauto.
intros.
  apply IHm.
  tauto.
 tauto.
simpl in |- *.
  unfold prec_L in |- *.
  unfold succ in |- *.
  unfold pred in |- *.
  intros.
  decompose [and] H.
  clear H.
  elim (eq_dim_dec d Md.kd).
 intro.
   rewrite <- a in |- *.
   rewrite <- a in IHm.
   elim (eq_dart_dec d1 z).
  intro.
    elim (eq_dart_dec d0 (top m d d0)).
   intro.
     elim (eq_dart_dec d0 (top m d z)).
     tauto.
   rewrite a0 in |- *.
      tauto.
  intro.
    elim b.
    symmetry  in |- *.
    apply nosucc_top.
    tauto.
   tauto.
  unfold succ in |- *.
     tauto.
 elim (eq_dart_dec (cA m d d0) z).
  elim (eq_dart_dec d0 (top m d (cA_1 m d d1))).
   intros.
     rewrite IHm in a0.
    generalize H7.
      intro.
      assert (d0 <> cA_1 m d d1).
     intro.
       rewrite H in H6.
       rewrite cA_cA_1 in H6.
       tauto.
      tauto.
      tauto.
    generalize H.
      rewrite cA_1_eq in |- *.
     elim (pred_dec m d d1).
      unfold pred in |- *.
         tauto.
      tauto.
     tauto.
    tauto.
    tauto.
  intros.
    elim (eq_dart_dec d0 (top m d z)).
   intros.
     apply IHm.
     tauto.
    tauto.
  intro.
    rewrite cA_eq in a0.
   generalize a0.
     elim (succ_dec m d d0).
    unfold succ in |- *.
       tauto.
   intros.
     rewrite <- a1 in b1.
     rewrite top_bottom in b1.
     tauto.
    tauto.
    tauto.
   unfold succ in |- *.
      tauto.
   tauto.
 elim (eq_dart_dec d0 (top m d (cA_1 m d z))).
  intros.
    rewrite IHm in a0.
   elim (eq_dart_dec d0 (top m d z)).
     tauto.
   intros.
      tauto.
   tauto.
   tauto.
 rewrite IHm in |- *.
  intros.
    elim (eq_dart_dec d0 (top m d z)).
    tauto.
   tauto.
  tauto.
  tauto.
rewrite IHm in |- *.
  tauto.
 tauto.
 tauto.
Qed.

(* THEN, THE SAME FOR cA_1: *)

Lemma f_cA_1:forall(m:fmap)(z:dart),
    MfcA.f_1 m z = cA_1 m Md.kd z.
Proof. tauto. Qed.

Lemma Iter_f_1_cA_1:forall(m:fmap)(i:nat)(z:dart),
   Iter (MfcA.f_1 m) i z = Iter (cA_1 m Md.kd) i z.
Proof.
induction i.
 simpl in |- *;  tauto.
intro.
  simpl in |- *.
  rewrite IHi in |- *.
   tauto.
Qed.

Lemma expo_top_ind: forall(m:fmap)(z:dart)(i:nat),
  inv_hmap m -> exd m z -> 
  let t:= Iter (cA m Md.kd) i z in
    top m Md.kd z = top m Md.kd t. 
Proof.
intros.
assert (z = Iter (cA_1 m Md.kd) i t).
 unfold t in |- *.
   rewrite <- Iter_f_cA in |- *.
   rewrite <- Iter_f_1_cA_1 in |- *.
   rewrite MfcA.Iter_f_f_1_i in |- *.
   tauto.
  tauto.
  tauto.
induction i.
 simpl in |- *.
    tauto.
simpl in IHi.
  generalize IHi.
  clear IHi.
  rewrite <- Iter_f_cA in |- *.
  rewrite <- Iter_f_1_cA_1 in |- *.
  rewrite MfcA.Iter_f_f_1_i in |- *.
 rewrite Iter_f_cA in |- *.
   intros.
   assert (top m Md.kd z =
   top m Md.kd (Iter (cA m Md.kd) i z)).
   tauto.
 clear IHi.
   simpl in t.
   assert (cA_1 m Md.kd t = Iter (cA m Md.kd) i z).
  unfold t in |- *.
    rewrite cA_1_cA in |- *.
    tauto.
   tauto.
  generalize (MfcA.exd_Iter_f m i z).
    rewrite Iter_f_cA in |- *.
     tauto.
 rewrite H2 in |- *.
   rewrite <- H3 in |- *.
   apply top_cA_1.
   tauto.
 unfold t in |- *.
   generalize (exd_cA m Md.kd (Iter (cA m Md.kd) i z)).
   generalize (MfcA.exd_Iter_f m i z).
   rewrite Iter_f_cA in |- *.
    tauto.
 tauto.
 tauto.
Qed.

(* FINALLY: *)

Lemma expo_top: forall(m:fmap)(z t:dart),
  inv_hmap m -> MfcA.expo m z t ->
    top m Md.kd z = top m Md.kd t. 
Proof.
intros.
unfold MfcA.expo in H0.
elim H0.
intros.
elim H2.
intros i Hi.
rewrite <- Hi in |- *.
rewrite Iter_f_cA in |- *.
apply expo_top_ind.
  tauto.
 tauto.
Qed.

(* OK: *)

Lemma succ_zi: forall(m:fmap)(z:dart)(i:nat),
  inv_hmap m -> exd m z -> ~pred m Md.kd z -> 
   (i + 1 < MfcA.Iter_upb m z)%nat ->
     let zi:= Iter (MfcA.f m) i z in
       succ m Md.kd zi.
Proof.
intros.
assert (exd m zi).
 unfold zi in |- *.
   generalize (MfcA.exd_Iter_f m i z).
    tauto.
assert (bottom m Md.kd z = bottom m Md.kd zi).
 apply expo_bottom.
   tauto.
 unfold MfcA.expo in |- *.
   split.
   tauto.
 split with i.
   fold zi in |- *.
    tauto.
assert (top m Md.kd z = top m Md.kd zi).
 apply expo_top.
   tauto.
 unfold MfcA.expo in |- *.
   split.
   tauto.
 split with i.
   fold zi in |- *.
    tauto.
assert (bottom m Md.kd z = z).
 apply nopred_bottom.
   tauto.
  tauto.
  tauto.
generalize (succ_dec m Md.kd zi).
  intro.
  elim H7.
  tauto.
intro.
  assert (top m Md.kd zi = zi).
 apply nosucc_top.
   tauto.
  tauto.
  tauto.
generalize (cA_eq m Md.kd zi H).
  elim (succ_dec m Md.kd zi).
  tauto.
intros.
  rewrite <- H4 in H9.
  rewrite H6 in H9.
  assert (cA m Md.kd zi = MfcA.f m zi).
  tauto.
rewrite H10 in H9.
  unfold zi in H9.
  assert (Iter (MfcA.f m) (S i) z = z).
 simpl in |- *.
    tauto.
assert (S i = 0).
 apply (MfcA.unicity_mod_p m z (S i) 0).
   tauto.
  tauto.
  lia.
  lia.
 simpl in |- *.
    tauto.
inversion H12.
Qed.

(* OK: *)

Lemma bottom_B_bis: forall(m:fmap)(z:dart)(i j:nat),
  inv_hmap m -> exd m z -> ~pred m Md.kd z ->
    let zi := Iter (MfcA.f m) i z in
    let zj := Iter (MfcA.f m) j z in
    let m0 := B m Md.kd zi in
      (i < j < MfcA.Iter_upb m z)%nat ->
         bottom m0 Md.kd zj = A m Md.kd zi.
Proof.
simpl in |- *.
intros.
set (p := MfcA.Iter_upb m z) in |- *.
fold p in H2.
set (zi := Iter (MfcA.f m) i z) in |- *.
set (zj := Iter (MfcA.f m) j z) in |- *.
set (m0 := B m Md.kd zi) in |- *.
unfold zj in |- *.
unfold p in H2.
induction j.
  absurd (i < 0 < MfcA.Iter_upb m z).
   lia.
  tauto.
fold p in IHj.
  fold p in H2.
  assert (exd m zi).
 unfold zi in |- *.
   generalize (MfcA.exd_Iter_f m i z).
    tauto.
assert (exd m zj).
 unfold zj in |- *.
   generalize (MfcA.exd_Iter_f m (S j) z).
    tauto.
assert (bottom m Md.kd z = bottom m Md.kd zi).
 apply expo_bottom.
   tauto.
 unfold MfcA.expo in |- *.
   split.
   tauto.
 split with i.
   fold zi in |- *.
    tauto.
assert (bottom m Md.kd z = bottom m Md.kd zj).
 apply expo_bottom.
   tauto.
 unfold MfcA.expo in |- *.
   split.
   tauto.
 split with (S j).
   fold zj in |- *.
    tauto.
assert (top m Md.kd z = top m Md.kd zi).
 apply expo_top.
   tauto.
 unfold MfcA.expo in |- *.
   split.
   tauto.
 split with i.
   fold zi in |- *.
    tauto.
assert (top m Md.kd z = top m Md.kd zj).
 apply expo_top.
   tauto.
 unfold MfcA.expo in |- *.
   split.
   tauto.
 split with (S j).
   fold zj in |- *.
    tauto.
assert (bottom m Md.kd z = z).
 apply nopred_bottom.
   tauto.
  tauto.
  tauto.
assert (succ m Md.kd zi).
 unfold zi in |- *.
   apply succ_zi.
   tauto.
  tauto.
  tauto.
 fold p in |- *.
    lia.
generalize (MfcA.exd_diff_orb m z H H0).
  unfold MfcA.diff_orb in |- *.
  unfold MfcA.Iter_upb in p.
  unfold MfcA.Iter_upb_aux in |- *.
  unfold MfcA.Iter_rem in p.
  fold p in |- *.
  fold (MfcA.Iter_rem m z) in p.
  fold (MfcA.Iter_upb m z) in p.
  unfold MfcA.diff_int in |- *.
  intros.
  assert (zi <> zj).
 unfold zi in |- *.
   unfold zj in |- *.
   apply H11.
    lia.
assert (z <> zj).
 unfold zj in |- *.
   generalize (H11 0 (S j)).
   simpl in |- *.
   intro.
   apply H13.
    lia.
elim (Nat.eq_dec (S (S j)) p).
 intro.
   assert (cA m Md.kd zj = z).
  unfold zj in |- *.
    assert
     (MfcA.f m (Iter (MfcA.f m) (S j) z) =
      Iter (MfcA.f m) 1 (Iter (MfcA.f m) (S j) z)).
   simpl in |- *.
      tauto.
  assert (S (S j) = 1 + S j).
    lia.
  assert
   (cA m Md.kd (Iter (MfcA.f m) (S j) z)
       = MfcA.f m (Iter (MfcA.f m) (S j) z)).
    tauto.
  rewrite H16 in |- *.
    rewrite H14 in |- *.
    rewrite <- MfcA.Iter_comp in |- *.
    rewrite <- H15 in |- *.
    rewrite a in |- *.
    unfold p in |- *.
    generalize (MfcA.Iter_upb_period m z H H0).
    simpl in |- *.
     tauto.
 simpl in |- *.
   assert (inv_hmap (B m Md.kd zi)).
  apply inv_hmap_B.
     tauto.
 assert (~ succ m Md.kd zj).
  intro.
    generalize (cA_eq m Md.kd zj H).
    elim (succ_dec m Md.kd zj).
   intros.
     rewrite H14 in H17.
     assert (zj = A_1 m Md.kd z).
    rewrite H17 in |- *.
      rewrite A_1_A in |- *.
      tauto.
     tauto.
     tauto.
   unfold pred in H1.
     rewrite <- H18 in H1.
     elim H1.
     apply exd_not_nil with m.
     tauto.
    tauto.
   tauto.
 assert (~ succ (B m Md.kd zi) Md.kd zj).
  unfold succ in |- *.
    unfold succ in H16.
    rewrite A_B_bis in |- *.
    tauto.
  intro.
    symmetry  in H17.
     tauto.
 assert (top m Md.kd zi = zj).
  rewrite <- H7 in |- *.
    rewrite H8 in |- *.
    apply nosucc_top.
    tauto.
   tauto.
   tauto.
 generalize (cA_eq m Md.kd zj H).
   elim (succ_dec m Md.kd zj).
   tauto.
 intros.
   generalize (cA_B m Md.kd zi zj H H10).
   elim (eq_dart_dec zi zj).
   tauto.
 elim (eq_dart_dec (top m Md.kd zi) zj).
  intros.
    clear b a0.
    generalize (cA_eq (B m Md.kd zi) Md.kd zj H15).
    elim (succ_dec (B m Md.kd zi) Md.kd zj).
    tauto.
  intros.
    clear b.
    clear b0.
    simpl in zj.
    fold zj in |- *.
    unfold m0 in |- *.
    rewrite <- H20 in |- *.
    rewrite <- H21 in |- *.
     tauto.
 intro.
   simpl in |- *.
   set (zj' := Iter (MfcA.f m) j z) in |- *.
   intros.
   assert (succ m Md.kd zj).
  unfold zj in |- *.
    apply succ_zi.
    tauto.
   tauto.
   tauto.
  fold p in |- *.
     lia.
 assert (succ m Md.kd zj').
  unfold zj' in |- *.
    apply succ_zi.
    tauto.
   tauto.
   tauto.
  fold p in |- *.
     lia.
 assert (cA m Md.kd zj' = A m Md.kd zj').
  rewrite cA_eq in |- *.
   elim (succ_dec m Md.kd zj').
     tauto.
    tauto.
   tauto.
 assert (exd m zj').
  unfold zj' in |- *.
    generalize (MfcA.exd_Iter_f m j z).
     tauto.
 assert (exd m0 zj').
  unfold m0 in |- *.
    generalize (exd_B m Md.kd zi zj').
     tauto.
 elim (Nat.eq_dec i j).
  intro.
    assert (zi = zj').
   unfold zj' in |- *.
     rewrite <- a0 in |- *.
     fold zi in |- *.
      tauto.
  rewrite <- H26 in |- *.
    assert (MfcA.f m zi = cA m Md.kd zi).
    tauto.
  rewrite H27 in |- *.
    unfold m0 in |- *.
    assert
 (~ pred (B m Md.kd zi) Md.kd (A m Md.kd zi)).
   unfold pred in |- *.
     rewrite A_1_B in |- *.
     tauto.
    tauto.
  rewrite <- H26 in H23.
    rewrite H23 in |- *.
    apply nopred_bottom.
   apply inv_hmap_B.
      tauto.
  generalize (succ_exd_A m Md.kd zi).
     tauto.
   tauto.
 intro.
   assert (zi <> zj').
  unfold zi in |- *.
    unfold zj' in |- *.
    apply H11.
     lia.
 assert (succ m0 Md.kd zj').
  unfold m0 in |- *.
    unfold succ in |- *.
    rewrite A_B_bis in |- *.
   unfold succ in H22.
      tauto.
  intro.
    symmetry  in H27.
     tauto.
 assert (A m0 Md.kd zj' = A m Md.kd zj').
  unfold m0 in |- *.
    rewrite A_B_bis in |- *.
    tauto.
  intro.
    symmetry  in H28.
     tauto.
 assert (bottom m0 Md.kd (A m0 Md.kd zj')
  = bottom m0 Md.kd zj').
  apply bottom_A.
   unfold m0 in |- *.
     apply inv_hmap_B.
      tauto.
   tauto.
 assert (cA m Md.kd zj' = MfcA.f m zj').
   tauto.
 rewrite <- H30 in |- *.
   rewrite H23 in |- *.
   rewrite <- H28 in |- *.
   rewrite bottom_A in |- *.
  unfold zj' in |- *.
    apply IHj.
     lia.
 unfold m0 in |- *.
   apply inv_hmap_B.
    tauto.
  tauto.
intro.
  simpl in |- *.
  set (zj' := Iter (MfcA.f m) j z) in |- *.
  intros.
  assert (succ m Md.kd zj).
 unfold zj in |- *.
   apply succ_zi.
   tauto.
  tauto.
  tauto.
 fold p in |- *.
    lia.
assert (succ m Md.kd zj').
 unfold zj' in |- *.
   apply succ_zi.
   tauto.
  tauto.
  tauto.
 fold p in |- *.
    lia.
assert (cA m Md.kd zj' = A m Md.kd zj').
 rewrite cA_eq in |- *.
  elim (succ_dec m Md.kd zj').
    tauto.
   tauto.
  tauto.
assert (exd m zj').
 unfold zj' in |- *.
   generalize (MfcA.exd_Iter_f m j z).
    tauto.
assert (exd m0 zj').
 unfold m0 in |- *.
   generalize (exd_B m Md.kd zi zj').
    tauto.
elim (Nat.eq_dec i j).
 intro.
   assert (zi = zj').
  unfold zj' in |- *.
    rewrite <- a in |- *.
    fold zi in |- *.
     tauto.
 rewrite <- H19 in |- *.
   rewrite <- H19 in H16.
   assert (MfcA.f m zi = cA m Md.kd zi).
   tauto.
 rewrite H20 in |- *.
   unfold m0 in |- *.
   assert (~ pred (B m Md.kd zi) Md.kd (A m Md.kd zi)).
  unfold pred in |- *.
    rewrite A_1_B in |- *.
    tauto.
   tauto.
 rewrite H16 in |- *.
   apply nopred_bottom.
  apply inv_hmap_B.
     tauto.
 generalize (exd_B m Md.kd zi (A m Md.kd zi)).
   generalize (succ_exd_A m Md.kd zi).
    tauto.
  tauto.
intro.
  assert (zi <> zj').
 unfold zi in |- *.
   unfold zj' in |- *.
   apply H11.
    lia.
assert (succ m0 Md.kd zj').
 unfold m0 in |- *.
   unfold succ in |- *.
   rewrite A_B_bis in |- *.
  unfold succ in H15.
     tauto.
 intro.
   symmetry  in H20.
    tauto.
assert (A m0 Md.kd zj' = A m Md.kd zj').
 unfold m0 in |- *.
   rewrite A_B_bis in |- *.
   tauto.
 intro.
   symmetry  in H21.
    tauto.
assert (MfcA.f m zj' = cA m Md.kd zj').
  tauto.
rewrite H22 in |- *.
  rewrite H16 in |- *.
  rewrite <- H21 in |- *.
  unfold m0 in |- *.
  rewrite bottom_A in |- *.
 unfold zj' in |- *.
   apply IHj.
    lia.
apply inv_hmap_B.
   tauto.
fold m0 in |- *.
   tauto.
Qed.

Lemma bottom_B_ter: forall(m:fmap)(z:dart)(i j:nat),
  inv_hmap m -> exd m z -> ~pred m Md.kd z ->
    let zi := Iter (MfcA.f m) i z in
    let zj := Iter (MfcA.f m) j z in
    let m0 := B m Md.kd zi in
      (j <= i < MfcA.Iter_upb m z)%nat ->
         bottom m0 Md.kd zj = bottom m Md.kd zj.
Proof.
intros.
elim (succ_dec m Md.kd zi).
 intro Szi.
   set (p := MfcA.Iter_upb m z) in |- *.
   fold p in H2.
   unfold zj in |- *.
   unfold p in H2.
   induction j.
  simpl in |- *.
    simpl in zj.
    assert (~ pred m0 Md.kd z).
   unfold pred in |- *.
     unfold m0 in |- *.
     rewrite A_1_B_bis in |- *.
    unfold pred in H1.
       tauto.
    tauto.
   intro.
     unfold pred in H1.
     rewrite H3 in H1.
     rewrite A_1_A in H1.
    generalize (MfcA.exd_Iter_f m i z).
      fold zi in |- *.
      intros.
      apply H1.
      apply exd_not_nil with m.
      tauto.
     tauto.
    tauto.
   unfold succ in |- *.
     rewrite <- H3 in |- *.
     apply exd_not_nil with m.
     tauto.
    tauto.
  rewrite nopred_bottom in |- *.
   rewrite nopred_bottom in |- *.
     tauto.
    tauto.
    tauto.
    tauto.
  unfold m0 in |- *.
    apply inv_hmap_B.
     tauto.
  unfold m0 in |- *.
    generalize (exd_B m Md.kd zi z).
     tauto.
   tauto.
 assert (j < i).
   lia.
 simpl in |- *.
   rename zj into zj1.
   set (zj := Iter (MfcA.f m) j z) in |- *.
   assert (exd m zj).
  unfold zj in |- *.
    generalize (MfcA.exd_Iter_f m j z).
     tauto.
 assert (MfcA.f m zj = cA m Md.kd zj).
   tauto.
 rewrite H5 in |- *.
   clear H5.
   rewrite bottom_cA in |- *.
  assert (cA m0 Md.kd zj = cA m Md.kd zj).
   unfold m0 in |- *.
     rewrite cA_B in |- *.
    elim (eq_dart_dec zi zj).
     intro.
       assert (i = j).
      apply (MfcA.unicity_mod_p m z i j H H0).
        tauto.
       lia.
      fold zi in |- *.
        fold zj in |- *.
         tauto.
      absurd (i = j).
       lia.
      tauto.
    intro.
      elim (eq_dart_dec (top m Md.kd zi) zj).
     intro.
       assert (bottom m Md.kd z = z).
      apply nopred_bottom.
        tauto.
       tauto.
       tauto.
     assert (bottom m Md.kd z = bottom m Md.kd zi).
      apply expo_bottom.
        tauto.
      unfold MfcA.expo in |- *.
        split.
        tauto.
      split with i.
        fold zi in |- *.
         tauto.
     assert (bottom m Md.kd z = bottom m Md.kd zj).
      assert (bottom m Md.kd z = bottom m Md.kd zj1).
       apply expo_bottom.
         tauto.
       unfold MfcA.expo in |- *.
         split.
         tauto.
       split with (S j).
         fold zj1 in |- *.
          tauto.
      assert (bottom m Md.kd z = bottom m Md.kd zj).
       apply expo_bottom.
         tauto.
       unfold MfcA.expo in |- *.
         split.
         tauto.
       split with j.
         fold zj in |- *.
          tauto.
      assert (top m Md.kd z = top m Md.kd zi).
       apply expo_top.
         tauto.
       unfold MfcA.expo in |- *.
         split.
         tauto.
       split with i.
         fold zi in |- *.
          tauto.
       tauto.
     assert (top m Md.kd z = top m Md.kd zj1).
      apply expo_top.
        tauto.
      unfold MfcA.expo in |- *.
        split.
        tauto.
      split with (S j).
        fold zj1 in |- *.
         tauto.
     assert (z = zj1).
      rewrite <- H5 in |- *.
        rewrite H6 in |- *.
        rewrite <- cA_top in |- *.
       rewrite a in |- *.
         unfold zj1 in |- *.
         simpl in |- *.
         fold zj in |- *.
          tauto.
       tauto.
      unfold zi in |- *.
        generalize (MfcA.exd_Iter_f m i z).
         tauto.
     assert (0 = S j).
      apply (MfcA.unicity_mod_p m z 0 (S j) H H0).
        lia.
       lia.
      simpl in |- *.
        unfold zj1 in H9.
        simpl in H9.
         tauto.
     inversion H10.
     tauto.
    tauto.
    tauto.
  rewrite <- H5 in |- *.
    rewrite bottom_cA in |- *.
   unfold zj in |- *.
     apply IHj.
      lia.
  unfold m0 in |- *.
    apply inv_hmap_B.
     tauto.
  unfold m0 in |- *.
    generalize (exd_B m Md.kd zi zj).
     tauto.
  tauto.
  tauto.
intro.
  unfold m0 in |- *.
  rewrite not_succ_B in |- *.
  tauto.
 tauto.
 tauto.
Qed.

Lemma bottom_B_quad: forall(m:fmap)(z v:dart)(j:nat),
  inv_hmap m -> exd m z -> ~pred m Md.kd z ->
  let m0 := B m Md.kd v in
  let t := Iter (MfcA.f m) j z in
   (j < MfcA.Iter_upb m z)%nat ->
     ~MfcA.expo m z v ->
        bottom m0 Md.kd t = bottom m Md.kd t.
Proof.
Proof.
intros.
elim (succ_dec m Md.kd v).
 intro.
   assert (inv_hmap m0).
  unfold m0 in |- *.
    apply inv_hmap_B.
    tauto.
  assert (~ pred m0 Md.kd z).
   unfold m0 in |- *.
     elim (Nat.eq_dec z (A m Md.kd v)).
    intro.
      unfold pred in |- *.
      rewrite a0.
      rewrite A_1_B.
     tauto.
     tauto.
    intro.
      unfold pred in |- *.
      rewrite A_1_B_bis.
     unfold pred in H1.
       tauto.
     tauto.
     tauto.
   induction j.
    simpl in t.
      unfold t in |- *.
      rewrite nopred_bottom.
     rewrite nopred_bottom.
      tauto.
      tauto.
      tauto.
      tauto.
     tauto.
     unfold m0 in |- *.
       generalize (exd_B m Md.kd v z).
       tauto.
     tauto.
    set (t' := Iter (MfcA.f m) j z) in |- *.
      assert (t' <> v).
     unfold MfcA.expo in H3.
  assert (~ (exists i : nat, 
     Iter (MfcA.f m) i z = v)).
      tauto.
      clear H3.
        unfold t' in |- *.
        intro.
        elim H6.
        split with j.
        tauto.
     assert (succ m Md.kd t').
      unfold t' in |- *.
        apply succ_zi.
       tauto.
       tauto.
       tauto.
       lia.
      assert (A m0 Md.kd t' = A m Md.kd t').
       unfold m0 in |- *.
         rewrite A_B_bis.
        tauto.
        tauto.
       assert (cA m Md.kd t' = A m Md.kd t').
        rewrite cA_eq.
         elim (succ_dec m Md.kd t').
          tauto.
          tauto.
         tauto.
        assert (succ m0 Md.kd t').
         unfold succ in |- *.
           unfold m0 in |- *.
           rewrite A_B_bis.
          unfold succ in H7.
            tauto.
          tauto.
         assert (cA m0 Md.kd t' = A m0 Md.kd t').
          rewrite cA_eq.
           elim (succ_dec m0 Md.kd t').
            tauto.
            tauto.
           tauto.
          assert (t = cA m Md.kd t').
           unfold t' in |- *.
  assert (cA m Md.kd (Iter (MfcA.f m) j z) = 
       MfcA.f m (Iter (MfcA.f m) j z)).
    tauto.
  rewrite H12 in |- *.
    clear H12.
             unfold t in |- *.
             simpl in |- *.
             tauto.
           rewrite H12.
             rewrite H9.
             rewrite bottom_A.
            rewrite <- H8.
              rewrite bottom_A.
             unfold t' in |- *.
               apply IHj.
               lia.
             tauto.
             tauto.
            tauto.
            tauto.
 unfold m0 in |- *.
   intro.
   rewrite not_succ_B.
  tauto.
  tauto.
  tauto.
Qed.

Lemma not_between_B:forall(m:fmap)(x z:dart),
  inv_hmap m -> exd m x -> exd m z -> x <> z -> 
  let z0:= bottom m Md.kd z in 
   ~MfcA.between m z0 x z ->
       (~MfcA.expo m z0 x
    \/  forall(i j:nat),
         x = Iter (MfcA.f m) i z0 ->
         z = Iter (MfcA.f m) j z0 ->
         (i < MfcA.Iter_upb m z0)%nat ->
         (j < MfcA.Iter_upb m z0)%nat ->
              (j <= i)%nat).
Proof.
intros.
unfold MfcA.between in |- *.
elim (MfcA.expo_dec m z0 x).
 intro.
   right.
   unfold MfcA.between in H3.
   intros.
   elim (Arith.Compare_dec.le_gt_dec j i).
   tauto.
 intro.
   elim H3.
   intros.
   clear H3.
   split with i.
   split with j.
   split.
  symmetry  in |- *.
     tauto.
 split.
  symmetry  in |- *.
     tauto.
 elim (Nat.eq_dec i j).
  intro.
    rewrite a0 in H4.
    rewrite <- H5 in H4.
     tauto.
 intro.
    lia.
 tauto.
 tauto.
Qed.

(* USEFUL LEMMAS: *)

(* OK: *)

Lemma Iter_cA_I:
 forall(m:fmap)(d z:dart)(t:tag)(p:point)(i:nat),
  inv_hmap (I m d t p) -> exd m z ->
    Iter (cA (I m d t p) Md.kd) i z = 
       Iter (cA m Md.kd) i z.
Proof.
induction i.
 simpl in |- *.
    tauto.
intros.
  set (x := cA (I m d t p) Md.kd) in |- *.
  simpl in |- *.
  unfold x in |- *.
  clear x.
  rewrite IHi in |- *.
 simpl in |- *.
   elim (eq_dart_dec d (Iter (cA m Md.kd) i z)).
  intro.
    simpl in H.
    unfold prec_I in H.
    generalize (MfcA.exd_Iter_f m i z).
    rewrite <- Iter_f_cA in a.
    rewrite <- a in |- *.
     tauto.
  tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma nopred_expo_L_i:
 forall(m:fmap)(i:nat)(k:dim)(x y z:dart),
   inv_hmap (L m k x y) -> 
    exd m z -> ~pred m Md.kd z ->
     let t:= Iter (cA m Md.kd) i z in  
       (i < MfcA.Iter_upb m z)%nat ->
         MfcA.expo (L m k x y) z t.
Proof.
induction i.
 simpl in |- *.
   intros.
   unfold MfcA.expo in |- *.
   apply MfcA.expo_refl.
   simpl in |- *.
    tauto.
intros.
  simpl in t.
  set (zi := Iter (cA m Md.kd) i z) in |- *.
  fold zi in t.
  apply MfcA.expo_trans with zi.
 unfold zi in |- *.
   apply IHi.
   tauto.
  tauto.
  tauto.
  lia.
unfold t in |- *.
  assert (t = cA (L m k x y) Md.kd zi).
 simpl in |- *.
   elim (eq_dim_dec k Md.kd).
  intro.
    elim (eq_dart_dec x zi).
   intro.
     assert (bottom m Md.kd z = z).
    apply nopred_bottom.
     simpl in H.
        tauto.
     tauto.
     tauto.
   assert (bottom m Md.kd zi = z).
    rewrite <- H3 in |- *.
      symmetry  in |- *.
      unfold zi in |- *.
      apply expo_bottom_ind.
     simpl in H.
        tauto.
     tauto.
   assert (t = cA m Md.kd zi).
    unfold t in |- *.
       tauto.
   generalize H5.
     rewrite cA_eq in |- *.
    elim (succ_dec m Md.kd zi).
     rewrite <- a0 in |- *.
       simpl in H.
       unfold prec_L in H.
       rewrite a in H.
        tauto.
    rewrite H4 in |- *.
      unfold t in |- *.
      unfold zi in |- *.
      assert (Iter (cA m Md.kd) (S i) z =
    cA m Md.kd (Iter (cA m Md.kd) i z)).
     simpl in |- *.
        tauto.
    rewrite <- H6 in |- *.
      intros.
      rewrite <- Iter_f_cA in H7.
      assert (S i = 0).
     apply (MfcA.unicity_mod_p m z (S i) 0).
      simpl in H.
         tauto.
      tauto.
      tauto.
      lia.
     rewrite H7 in |- *.
       simpl in |- *.
        tauto.
    inversion H8.
   simpl in H.
      tauto.
  intros.
    elim (eq_dart_dec (cA_1 m Md.kd y) zi).
   intro.
     generalize a0.
     rewrite cA_1_eq in |- *.
    elim (pred_dec m Md.kd y).
     simpl in H.
       unfold prec_L in H.
       rewrite a in H.
        tauto.
    intros.
      assert (bottom m Md.kd zi = y).
     rewrite <- a1 in |- *.
       apply bottom_top.
      simpl in H.
         tauto.
     simpl in H.
       unfold prec_L in H.
        tauto.
      tauto.
    assert (bottom m Md.kd y = y).
     apply nopred_bottom.
      simpl in H.
         tauto.
     simpl in H.
       unfold prec_L in H.
        tauto.
      tauto.
    assert (bottom m Md.kd z = z).
     apply nopred_bottom.
      simpl in H.
         tauto.
      tauto.
      tauto.
    assert (bottom m Md.kd z = bottom m Md.kd zi).
     unfold zi in |- *.
       apply expo_bottom_ind.
      simpl in H.
         tauto.
      tauto.
    rewrite H3 in H6.
      rewrite H5 in H6.
      assert (t = cA m Md.kd zi).
     fold t in |- *.
        tauto.
    generalize H7.
      rewrite cA_eq in |- *.
     elim (succ_dec m Md.kd zi).
      rewrite <- a1 in |- *.
        intro.
         absurd (succ m Md.kd (top m Md.kd y)).
       apply not_succ_top.
         simpl in H.
          tauto.
       tauto.
     intros.
       rewrite H3 in H8.
       unfold t in H8.
       unfold zi in H8.
       rewrite H6 in H8.
       assert
        (cA m Md.kd (Iter (cA m Md.kd) i y) =
        Iter (cA m Md.kd) (S i) y).
      simpl in |- *.
         tauto.
     rewrite H9 in H8.
       rewrite <- Iter_f_cA in H8.
       assert (S i = 0).
      apply (MfcA.unicity_mod_p m y (S i) 0).
       simpl in H.
          tauto.
      simpl in H.
        unfold prec_L in H.
         tauto.
      rewrite <- H6 in |- *.
         lia.
      rewrite <- H6 in |- *.
         lia.
      simpl in |- *.
         tauto.
     inversion H10.
    simpl in H.
       tauto.
   simpl in H.
      tauto.
  intros.
    fold t in |- *.
     tauto.
 fold t in |- *.
    tauto.
fold t in |- *.
  rewrite H3 in |- *.
  unfold MfcA.expo in |- *.
  split.
 simpl in |- *.
   unfold zi in |- *.
   generalize (MfcA.exd_Iter_f m i z).
   simpl in H.
   rewrite Iter_f_cA in |- *.
    tauto.
split with 1.
  rewrite Iter_f_cA in |- *.
  simpl in |- *.
   tauto.
Qed.

(* OK: *)

Lemma expo_bottom_z: forall(m:fmap)(z:dart),
  inv_hmap m -> exd m z -> 
     MfcA.expo m (bottom m Md.kd z) z.
Proof.
induction m.
 simpl in |- *.
    tauto.
simpl in |- *.
  intros.
  elim (eq_dart_dec d z).
 intros.
   apply MfcA.expo_refl.
   rewrite <- a in |- *.
   simpl in |- *.
    tauto.
intros.
  assert (MfcA.expo m (bottom m Md.kd z) z).
 apply IHm.
   tauto.
  tauto.
unfold MfcA.expo in H1.
  elim H1.
  clear H1.
  intros.
  unfold MfcA.expo in |- *.
  simpl in |- *.
  split.
  tauto.
elim H2.
  clear H2.
  intros i Hi.
  split with i.
  rewrite Iter_f_cA in |- *.
  rewrite Iter_cA_I in |- *.
 rewrite <- Iter_f_cA in |- *.
    tauto.
simpl in |- *.
   tauto.
 tauto.
rename d into k.
  rename d0 into x.
  rename d1 into y.
  simpl in |- *.
  intros.
  unfold prec_L in H.
  elim (eq_dim_dec k Md.kd).
 intro.
   rewrite a in |- *.
   elim (eq_dart_dec y (bottom m Md.kd z)).
  intros.
    set (z0 := bottom m Md.kd z) in |- *.
    fold z0 in a0.
    set (x0 := bottom m Md.kd x) in |- *.
    assert (inv_hmap m).
    tauto.
  generalize (IHm z H1 H0).
    fold z0 in |- *.
    intro.
    assert (exd m x).
    tauto.
  generalize (IHm x H1 H3).
    fold x0 in |- *.
    intro.
    assert (MfcA.expo1 m z0 z).
   generalize (MfcA.expo_expo1 m z0 z).
      tauto.
  assert (MfcA.expo1 m x0 x).
   generalize (MfcA.expo_expo1 m x0 x).
      tauto.
  rewrite <- a0 in H5.
    assert (MfcA.expo (L m Md.kd x y) x0 x).
   unfold MfcA.expo1 in H6.
     elim H6.
     clear H6.
     intros.
     elim H7.
     intros i Hi.
     generalize (nopred_expo_L_i m i Md.kd x y x0).
     intros.
     unfold MfcA.expo in H8.
     decompose [and] Hi.
     clear Hi.
     set (m1 := L m Md.kd x y) in |- *.
     rewrite <- H10 in |- *.
     rewrite <- Iter_f_cA in H8.
     unfold m1 in |- *.
     apply H8.
    simpl in |- *.
      unfold prec_L in |- *.
      rewrite a in H.
       tauto.
    tauto.
   unfold x0 in |- *.
     apply not_pred_bottom.
      tauto.
    tauto.
  assert (MfcA.expo (L m Md.kd x y) y z).
   unfold MfcA.expo1 in H5.
     elim H5.
     clear H5.
     intros.
     elim H8.
     clear H8.
     intros j Hj.
     generalize (nopred_expo_L_i m j Md.kd x y y).
     intros.
     unfold MfcA.expo in H8.
     decompose [and] Hj.
     clear Hj.
     set (m1 := L m Md.kd x y) in |- *.
     rewrite <- H10 in |- *.
     rewrite <- Iter_f_cA in H8.
     unfold m1 in |- *.
     apply H8.
    simpl in |- *.
      unfold prec_L in |- *.
      rewrite a in H.
       tauto.
    tauto.
   rewrite a in H.
      tauto.
    tauto.
  assert (MfcA.expo (L m Md.kd x y) x y).
   unfold MfcA.expo in |- *.
     split.
    simpl in |- *.
       tauto.
   split with 1.
     rewrite Iter_f_cA in |- *.
     simpl in |- *.
     elim (eq_dart_dec x x).
    elim (eq_dim_dec Md.kd Md.kd).
      tauto.
     tauto.
    tauto.
  apply MfcA.expo_trans with x.
    tauto.
  apply MfcA.expo_trans with y.
    tauto.
   tauto.
 intro.
   assert (MfcA.expo m (bottom m Md.kd z) z).
  apply IHm.
    tauto.
   tauto.
 set (zO := bottom m Md.kd z) in |- *.
   fold zO in H1.
   assert (MfcA.expo1 m zO z).
  generalize (MfcA.expo_expo1 m zO z).
     tauto.
 unfold MfcA.expo1 in H2.
   elim H2.
   clear H2.
   intros.
   elim H3.
   clear H3.
   intros i Hi.
   decompose [and] Hi.
   clear Hi.
   rewrite <- H4 in |- *.
   generalize (nopred_expo_L_i m i Md.kd x y zO).
   intros.
   rewrite <- Iter_f_cA in H5.
   apply H5.
  simpl in |- *.
    unfold prec_L in |- *.
    rewrite a in H.
     tauto.
  tauto.
 unfold zO in |- *.
   apply not_pred_bottom.
    tauto.
  tauto.
intro.
  assert (MfcA.expo m (bottom m Md.kd z) z).
 apply IHm.
   tauto.
  tauto.
set (zO := bottom m Md.kd z) in |- *.
  fold zO in H1.
  assert (MfcA.expo1 m zO z).
 generalize (MfcA.expo_expo1 m zO z).
    tauto.
unfold MfcA.expo1 in H2.
  elim H2.
  clear H2.
  intros.
  elim H3.
  clear H3.
  intros i Hi.
  decompose [and] Hi.
  clear Hi.
  rewrite <- H4 in |- *.
  generalize (nopred_expo_L_i m i k x y zO).
  intros.
  rewrite <- Iter_f_cA in H5.
  apply H5.
 simpl in |- *.
   unfold prec_L in |- *.
    tauto.
 tauto.
unfold zO in |- *.
  apply not_pred_bottom.
   tauto.
 tauto.
Qed.

(* IDEM: *)

Lemma expo_top_z: forall(m:fmap)(z:dart),
  inv_hmap m -> exd m z -> 
     MfcA.expo m (top m Md.kd z) z.
Proof.
intros.
assert (MfcA.expo m (bottom m Md.kd z) z).
 apply (expo_bottom_z m z H H0).
assert (cA m Md.kd (top m Md.kd z) = bottom m Md.kd z).
 apply cA_top.
   tauto.
  tauto.
assert (MfcA.expo m (top m Md.kd z) (bottom m Md.kd z)).
 unfold MfcA.expo in |- *.
   split.
  generalize (exd_top m Md.kd z).
     tauto.
 split with 1.
   simpl in |- *.
    tauto.
apply MfcA.expo_trans with (bottom m Md.kd z).
  tauto.
tauto.
Qed.

(* OK: *)

Lemma bottom_bottom_expo: forall(m:fmap)(z t:dart),
  inv_hmap m -> exd m z -> exd m t -> 
    bottom m Md.kd z = bottom m Md.kd t ->
        MfcA.expo m z t.
Proof.
intros.
 apply MfcA.expo_trans with (bottom m Md.kd z).
   apply MfcA.expo_symm.
     tauto.
   apply expo_bottom_z.
     tauto.
    tauto.
  rewrite H2 in |- *.
    apply expo_bottom_z.
    tauto.
   tauto.
Qed.

(* OK: *)

Lemma top_top_expo: forall(m:fmap)(z t:dart),
  inv_hmap m -> exd m z -> exd m t -> 
    top m Md.kd z = top m Md.kd t ->
        MfcA.expo m z t.
Proof.
intros.
generalize (cA_top m Md.kd z H H0).
intro.
generalize (cA_top m Md.kd t H H1).
intro.
rewrite H2 in H3.
rewrite H3 in H4.
apply bottom_bottom_expo.
  tauto.
 tauto.
 tauto.
 tauto.
Qed.

(* FINALLY, THE EXPECTED RESULT (OK): *)

Lemma between_bottom_B_bis: forall(m:fmap)(x' x:dart),
  inv_hmap m -> exd m x -> exd m x' -> x' <> x -> 
  let x0 := bottom m Md.kd x in
  let m0 := B m Md.kd x' in
      ((MfcA.between m x0 x' x ->
          bottom m0 Md.kd x = A m Md.kd x')
   /\ (~MfcA.between m x0 x' x ->
          bottom m0 Md.kd x = bottom m Md.kd x)).
Proof.
intros.
unfold MfcA.between in |- *.
split.
 intros.
   assert (exd m x0).
  unfold x0 in |- *.
    apply exd_bottom.
    tauto.
   tauto.
 generalize (H3 H H4).
   clear H3.
   intro.
   elim H3.
   intros i Hi.
   clear H3.
   elim Hi.
   clear Hi.
   intros j Hj.
   decompose [and] Hj.
   clear Hj.
   assert (~ pred m Md.kd x0).
  unfold x0 in |- *.
    apply not_pred_bottom.
     tauto.
 elim (Nat.eq_dec i j).
  intro.
    rewrite a in H3.
    rewrite H3 in H6.
     tauto.
 intro.
   unfold m0 in |- *.
   rewrite <- H3 in |- *.
   rewrite <- H6 in |- *.
   apply bottom_B_bis.
   tauto.
  tauto.
  tauto.
  lia.
intros.
  assert (exd m x0).
 unfold x0 in |- *.
   apply exd_bottom.
   tauto.
  tauto.
unfold m0 in |- *.
  generalize (not_between_B m x' x H H1 H0 H2).
  simpl in |- *.
  fold x0 in |- *.
  intros.
  assert
   (~ MfcA.expo m x0 x' \/
    (forall i j : nat,
     x' = Iter (MfcA.f m) i x0 ->
     x = Iter (MfcA.f m) j x0 ->
     i < MfcA.Iter_upb m x0 ->
       j < MfcA.Iter_upb m x0 -> j <= i)).
 apply H5.
    tauto.
clear H5.
  elim H6.
 clear H6.
   intro.
   assert (MfcA.expo m x0 x).
  unfold x0 in |- *.
    apply expo_bottom_z.
    tauto.
   tauto.
 assert (MfcA.expo1 m x0 x).
  generalize (MfcA.expo_expo1 m x0 x).
     tauto.
 unfold MfcA.expo1 in H7.
   elim H7.
   clear H7.
   intros.
   elim H8.
   intros j Hj.
   clear H8.
   decompose [and] Hj.
   clear Hj.
   unfold x0 in |- *.
   rewrite <- H9 in |- *.
   apply bottom_B_quad.
   tauto.
  tauto.
 unfold x0 in |- *.
   apply not_pred_bottom.
    tauto.
  tauto.
  tauto.
clear H6.
  intros.
  clear H3.
  assert (MfcA.expo m x0 x).
 unfold x0 in |- *.
   apply expo_bottom_z.
   tauto.
  tauto.
assert (MfcA.expo1 m x0 x).
 generalize (MfcA.expo_expo1 m x0 x).
    tauto.
unfold MfcA.expo1 in H6.
  decompose [and] H6.
  clear H6.
  elim H8.
  clear H8.
  intros j Hj.
  elim (MfcA.expo_dec m x0 x').
 intro.
   assert (MfcA.expo1 m x0 x').
  generalize (MfcA.expo_expo1 m x0 x').
     tauto.
 unfold MfcA.expo1 in H6.
   decompose [and] H6.
   clear H6.
   elim H9.
   clear H9.
   intros i Hi.
   unfold x0 in |- *.
   decompose [and] Hj.
   clear Hj.
   decompose [and] Hi.
   clear Hi.
   rewrite <- H9 in |- *.
   rewrite <- H11 in |- *.
   apply bottom_B_ter.
   tauto.
  tauto.
 unfold x0 in |- *.
   apply not_pred_bottom.
    tauto.
 assert (j <= i).
  apply H5.
   symmetry  in |- *.
      tauto.
  symmetry  in |- *.
     tauto.
   tauto.
   tauto.
  lia.
intro.
  decompose [and] Hj.
  clear Hj.
  rewrite <- H8 in |- *.
  assert (x0 = bottom m Md.kd x0).
 unfold x0 in |- *.
   rewrite bottom_bottom in |- *.
   tauto.
  tauto.
rewrite H8 in |- *.
  unfold x0 in |- *.
  rewrite <- H8 in |- *.
  apply bottom_B_quad.
  tauto.
 tauto.
unfold x0 in |- *.
  apply not_pred_bottom.
   tauto.
 tauto.
 tauto.
 tauto.
Qed.

(* COROLLARY: OK *)

Lemma not_expo_bottom_B: forall(m:fmap)(x' x:dart),
  inv_hmap m -> exd m x -> exd m x' ->
  let m0 := B m Md.kd x' in
    ~ MfcA.expo m x' x ->
        bottom m0 Md.kd x = bottom m Md.kd x.
Proof.
intros.
set (x0 := bottom m Md.kd x) in |- *.
assert (~ MfcA.between m x0 x' x).
 intro.
   assert (exd m x0).
  unfold x0 in |- *.
    apply exd_bottom.
    tauto.
   tauto.
 generalize (MfcA.between_expo m x0 x' x H H4 H3).
   intros.
    absurd (MfcA.expo m x' x).
   tauto.
 apply MfcA.expo_trans with x0.
  apply MfcA.expo_symm.
    tauto.
   tauto.
  tauto.
fold x0 in |- *.
  assert (x' <> x).
 intro.
   rewrite H4 in H2.
   elim H2.
   apply MfcA.expo_refl.
    tauto.
 generalize (between_bottom_B_bis m x' x H H0 H1 H4).
  simpl in |- *.
  fold x0 in |- *.
   tauto.
Qed.

(*===================================================
              bottom_Shift, top_Shift 
===================================================*)

(* OK: *)

Lemma between_bottom_x_top: forall(m:fmap)(x:dart),
 inv_hmap m -> succ m Md.kd x -> 
  MfcA.between m (bottom m Md.kd x) x (top m Md.kd x).
Proof.
intros.
assert (exd m x).
 apply succ_exd with Md.kd.
   tauto.
  tauto.
generalize (expo_bottom_z m x H H1).
  intro.
  assert (MfcA.expo1 m (bottom m Md.kd x) x).
 generalize (MfcA.expo_expo1 m (bottom m Md.kd x) x).
    tauto.
unfold MfcA.expo1 in H3.
  elim H3.
  clear H3.
  intros.
  elim H4.
  clear H4.
  intros i Hi.
  split with i.
  generalize (MfcA.upb_pos m (bottom m Md.kd x) H5).
  intro.
  set (p := 
    MfcA.Iter_upb m (bottom m Md.kd x)) in |- *.
  fold p in H4.
  fold p in Hi.
  split with (p - 1)%nat.
  split.
  tauto.
split.
 rewrite <- cA_1_bottom in |- *.
  assert (cA_1 m Md.kd (bottom m Md.kd x) = 
     MfcA.f_1 m (bottom m Md.kd x)).
    tauto.
  rewrite H7 in |- *.
    rewrite <- MfcA.Iter_f_f_1 in |- *.
   simpl in |- *.
     unfold p in |- *.
     rewrite MfcA.Iter_upb_period in |- *.
     tauto.
    tauto.
    tauto.
   tauto.
   tauto.
   lia.
  tauto.
  tauto.
 lia.
Qed.

(* OK: *)

Lemma bottom_Shift:
 forall(m:fmap)(x z:dart)(H:inv_hmap m), 
  succ m Md.kd x -> exd m z -> x <> z ->
  let m0 := Shift m Md.kd x in
   bottom m0 Md.kd z = 
    if MfcA.expo_dec m x z H then A m Md.kd x
    else bottom m Md.kd z.
Proof.
intros.
unfold m0 in |- *.
unfold Shift in |- *.
simpl in |- *.
assert (exd m x).
 apply succ_exd with Md.kd.
   tauto.
  tauto.
assert (exd m (top m Md.kd x)).
 apply exd_top.
   tauto.
  tauto.
assert (x <> top m Md.kd x).
 intro.
   rewrite H5 in H0.
    absurd (succ m Md.kd (top m Md.kd x)).
  apply not_succ_top.
     tauto.
  tauto.
generalize (between_bottom_B_bis m x (top m Md.kd x) H H4 H3 H5).
  simpl in |- *.
  rewrite bottom_top_bis in |- *.
 intros.
   generalize
  (between_bottom_B_bis m x z H H1 H3 H2).
   simpl in |- *.
   intros.
   assert (exd m (bottom m Md.kd x)).
  apply exd_bottom.
    tauto.
   tauto.
 generalize (MfcA.between_dec m 
    (bottom m Md.kd x) x (top m Md.kd x) H).
   assert (exd m (bottom m Md.kd z)).
  apply exd_bottom.
    tauto.
   tauto.
 generalize (MfcA.between_dec m 
    (bottom m Md.kd z) x z H H9).
   intro.
   intro.
   decompose [and] H6.
   decompose [and] H7.
   clear H6 H7.
   generalize (not_expo_bottom_B m x z H H1 H3).
   simpl in |- *.
   intro.
   elim H10.
  clear H10.
    intro.
    generalize (H14 H7).
    intro.
    clear H14.
    rewrite H10 in |- *.
    elim (eq_dart_dec (bottom m Md.kd x) 
 (A m Md.kd x)).
   intro.
      absurd (bottom m Md.kd x = A m Md.kd x).
    apply succ_bottom.
      tauto.
     tauto.
    tauto.
  intro.
    elim (MfcA.expo_dec m x z H).
   elim (eq_dim_dec Md.kd Md.kd).
     tauto.
    tauto.
  intro.
    generalize (MfcA.between_expo m 
     (bottom m Md.kd z) x z).
    intros.
    elim b0.
    apply MfcA.expo_trans with (bottom m Md.kd z).
   apply MfcA.expo_symm.
     tauto.
    tauto.
   tauto.
 intro.
   generalize (H15 H7).
   clear H15.
   intro.
   rewrite H15 in |- *.
   elim (MfcA.expo_dec m x z H).
  intro.
    elim (eq_dart_dec (bottom m Md.kd x) 
       (bottom m Md.kd z)).
   intros.
     elim (eq_dim_dec Md.kd Md.kd).
    intro.
      apply H12.
      apply between_bottom_x_top.
      tauto.
     tauto.
    tauto.
  intro.
    elim b.
    apply expo_bottom.
    tauto.
   tauto.
 elim (eq_dim_dec Md.kd Md.kd).
  elim (eq_dart_dec (bottom m Md.kd x)
  (bottom m Md.kd z)).
   intros.
     elim b.
     clear b.
     apply MfcA.expo_trans with (bottom m Md.kd x).
    apply MfcA.expo_symm.
      tauto.
    apply expo_bottom_z.
      tauto.
     tauto.
   rewrite a in |- *.
     apply expo_bottom_z.
     tauto.
    tauto.
   tauto.
  tauto.
 tauto.
tauto.
Qed.

(* IDEM: *)

Lemma top_Shift:
 forall(m:fmap)(x z:dart)(H:inv_hmap m),
 succ m Md.kd x -> exd m z -> x <> z ->
  let m0:= Shift m Md.kd x in
   top m0 Md.kd z =
     if MfcA.expo_dec m x z H then x 
     else top m Md.kd z.
Proof.
intros.
generalize (bottom_Shift m x z H H0 H1 H2).
intros.
rewrite <- (cA_1_bottom m0 Md.kd z) in |- *.
 unfold m0 in H3.
   fold m0 in H3.
   rewrite H3 in |- *.
   elim (MfcA.expo_dec m x z H).
  assert (cA m Md.kd x = A m Md.kd x).
   rewrite cA_eq in |- *.
    elim (succ_dec m Md.kd x).
      tauto.
     tauto.
    tauto.
  rewrite <- H4 in |- *.
    assert (cA m0 Md.kd x = cA m Md.kd x).
   unfold m0 in |- *.
     rewrite cA_Shift in |- *.
     tauto.
    tauto.
    tauto.
  rewrite <- H5 in |- *.
    rewrite cA_1_cA in |- *.
    tauto.
  unfold m0 in |- *.
    apply inv_hmap_Shift.
    tauto.
   tauto.
  unfold m0 in |- *.
    generalize (exd_Shift m Md.kd x x).
    assert (exd m x).
   apply succ_exd with Md.kd.
     tauto.
    tauto.
   tauto.
 generalize H3.
   elim (MfcA.expo_dec m x z H).
   tauto.
 intros.
   unfold m0 in |- *.
   rewrite cA_1_Shift in |- *.
  apply cA_1_bottom.
    tauto.
   tauto.
  tauto.
  tauto.
unfold m0 in |- *; apply inv_hmap_Shift.
  tauto.
 tauto.
unfold m0 in |- *.
  generalize (exd_Shift m Md.kd x z).
   tauto.
Qed.

(*=================================================
              CRACK IN A k-CELL:
=================================================*)

Definition crack(m:fmap)(x x':dart):Prop:=
  x <> x' /\ MfcA.expo m x x'.

Lemma crack_comm: forall (m:fmap)(x x':dart),
  inv_hmap m -> crack m x x' -> crack m x' x.
Proof.
unfold crack in |- *.
intros.
split.
 intro.
   symmetry  in H1.
    tauto.
apply MfcA.expo_symm.
  tauto.
 tauto.
Qed.

(* OK: *)

Lemma crack_succ :forall (m:fmap)(x x':dart), 
  inv_hmap m -> crack m x x' -> 
     (succ m Md.kd x \/ succ m Md.kd x').
Proof.
intros.
unfold crack in H0.
elim (succ_dec m Md.kd x).
  tauto.
elim (succ_dec m Md.kd x').
  tauto.
intros.
  assert (exd m x).
 apply (expo_exd_l m x x').
   tauto.
  tauto.
assert (exd m x').
 apply (expo_exd_r m x x').
   tauto.
  tauto.
assert (top m Md.kd x = x).
 apply nosucc_top.
   tauto.
  tauto.
  tauto.
assert (top m Md.kd x' = x').
 apply nosucc_top.
   tauto.
  tauto.
  tauto.
elim H0.
  intros.
  elim H5.
  rewrite <- H3 in |- *.
  rewrite <- H4 in |- *.
  apply expo_top.
  tauto.
 tauto.
Qed.

Lemma crack_exd :forall (m:fmap)(x x':dart), 
  inv_hmap m -> crack m x x' -> 
     (exd m x /\ exd m x').
Proof.
unfold crack in |- *.
intros.
split.
 unfold MfcA.expo in H0.
    tauto.
apply MfcA.expo_exd with x.
  tauto.
 tauto.
Qed.

(*===================================================
               PROPERTIES OF Split
                 WITH crack 
===================================================*)

Lemma cA_Split:forall(m:fmap)(x x' z:dart),
 inv_hmap m -> crack m x x' -> 
   cA (Split m Md.kd x x') Md.kd z = 
    if eq_dart_dec x z then cA m Md.kd x'
    else if eq_dart_dec x' z then cA m Md.kd x 
         else cA m Md.kd z.
Proof.
intros.
elim H0.
clear H0.
intros Dxx'.
intro.
unfold Split in |- *.
set (m0 := L (B m Md.kd x) Md.kd (top m Md.kd x) (bottom m Md.kd x)) in |- *.
elim (succ_dec m Md.kd x).
 elim (succ_dec m Md.kd x').
  intros.
    unfold m0 in |- *.
    rewrite cA_B in |- *.
   elim (eq_dart_dec x' z).
    intro.
      fold (Shift m Md.kd x) in |- *.
      rewrite (bottom_Shift m x x' H a0) in |- *.
     elim (eq_dart_dec x z).
      intro.
        rewrite <- a1 in a2.
         tauto.
     elim (MfcA.expo_dec m x x').
      intros.
        rewrite cA_eq in |- *.
       elim (succ_dec m Md.kd x).
         tauto.
        tauto.
       tauto.
     intros.
        tauto.
    apply succ_exd with Md.kd.
      tauto.
     tauto.
     tauto.
   elim
    (eq_dart_dec
   (top (L (B m Md.kd x) Md.kd (top m Md.kd x) 
   (bottom m Md.kd x)) Md.kd x') z).
    fold m0 in |- *.
      elim (eq_dart_dec x z).
     intros.
       rewrite <- a1 in a2.
       unfold m0 in |- *.
       fold (Shift m Md.kd x) in |- *.
       rewrite A_Shift in |- *.
      elim (eq_dart_dec x x').
        tauto.
      elim (eq_dart_dec (top m Md.kd x) x').
       intros.
         rewrite <- a3 in a.
          absurd (succ m Md.kd (top m Md.kd x)).
        apply not_succ_top.
           tauto.
        tauto.
      intros.
        rewrite cA_eq in |- *.
       elim (succ_dec m Md.kd x').
         tauto.
        tauto.
       tauto.
      tauto.
      tauto.
    intros.
      unfold m0 in a1.
      fold (Shift m Md.kd x) in a1.
      rewrite (top_Shift m x x' H) in a1.
     generalize a1.
       elim (MfcA.expo_dec m x x' H).
       tauto.
      tauto.
     tauto.
    apply succ_exd with Md.kd.
      tauto.
     tauto.
     tauto.
   fold m0 in |- *.
     unfold m0 in |- *.
     fold (Shift m Md.kd x) in |- *.
     rewrite (top_Shift m x x' H) in |- *.
    intros.
      rewrite cA_Shift in |- *.
     elim (eq_dart_dec x z).
      intro.
        generalize b.
        elim (MfcA.expo_dec m x x' H).
        tauto.
       tauto.
      tauto.
     tauto.
     tauto.
    tauto.
   apply succ_exd with Md.kd;  tauto;  tauto.
    tauto.
  fold (Shift m Md.kd x) in |- *.
    apply inv_hmap_Shift.
    tauto.
   tauto.
  unfold succ in |- *.
    simpl in |- *.
    elim (eq_dim_dec Md.kd Md.kd).
   intro E.
     elim (eq_dart_dec (top m Md.kd x) x').
    intro.
       absurd (succ m Md.kd (top m Md.kd x)).
     rewrite <- a1 in a.
        absurd (succ m Md.kd (top m Md.kd x)).
      apply not_succ_top.
         tauto.
      tauto.
    rewrite a1 in |- *.
       tauto.
   rewrite A_B_bis in |- *.
    unfold succ in a.
       tauto.
   intro.
     symmetry  in H1.
      tauto.
   tauto.
 intros.
   rewrite cA_B in |- *.
  elim (eq_dart_dec x z).
   intros.
     rewrite cA_eq in |- *.
    elim (succ_dec m Md.kd x').
      tauto.
    intro.
      apply expo_bottom.
      tauto.
     tauto.
    tauto.
  elim (eq_dart_dec (top m Md.kd x) z).
   elim (eq_dart_dec x' z).
    rewrite cA_eq in |- *.
     elim (succ_dec m Md.kd x).
       tauto.
      tauto.
     tauto.
   intros.
     rewrite cA_eq in |- *.
    elim (succ_dec m Md.kd z).
     intro.
       rewrite <- a0 in a1.
        absurd (succ m Md.kd (top m Md.kd x)).
      apply not_succ_top.
         tauto.
      tauto.
    intros.
      assert (top m Md.kd x = top m Md.kd x').
     apply expo_top.
       tauto.
      tauto.
    rewrite a0 in H1.
      generalize (nosucc_top m Md.kd x' H).
      intro.
      rewrite H2 in H1.
     symmetry  in H1.
        tauto.
    generalize (MfcA.expo_exd m x x').
       tauto.
     tauto.
    tauto.
  elim (eq_dart_dec x' z).
   intros.
     generalize (expo_top m x x').
     intros.
     rewrite H1 in b0.
    elim b0.
      rewrite <- a0 in |- *.
      apply nosucc_top.
      tauto.
    generalize (MfcA.expo_exd m x x').
       tauto.
     tauto.
    tauto.
    tauto.
   tauto.
  tauto.
  tauto.
intro.
  elim (eq_dart_dec x z).
 intro.
   rewrite <- a in |- *.
   generalize (crack_succ m x x' H).
   unfold crack in |- *.
   intros.
   rewrite cA_B in |- *.
  elim (eq_dart_dec x' x).
   intro.
     symmetry  in a0.
      tauto.
  elim (eq_dart_dec (top m Md.kd x') x).
   intros.
     rewrite cA_eq in |- *.
    elim (succ_dec m Md.kd x').
      tauto.
     tauto.
    tauto.
  intros.
    assert (top m Md.kd x = x).
   apply nosucc_top.
     tauto.
   unfold MfcA.expo in H0.
      tauto.
    tauto.
  assert (top m Md.kd x = top m Md.kd x').
   apply expo_top.
     tauto.
    tauto.
  rewrite H3 in H2.
     tauto.
  tauto.
  tauto.
intro.
  rewrite cA_B in |- *.
 elim (eq_dart_dec x' z).
  intros.
    rewrite cA_eq in |- *.
   elim (succ_dec m Md.kd x).
     tauto.
   intro.
     apply expo_bottom.
     tauto.
   apply MfcA.expo_symm.
     tauto.
    tauto.
   tauto.
 elim (eq_dart_dec (top m Md.kd x') z).
  intros.
    assert (top m Md.kd x = x).
   apply nosucc_top.
     tauto.
   unfold MfcA.expo in H0.
      tauto.
    tauto.
  assert (top m Md.kd x = top m Md.kd x').
   apply expo_top.
     tauto.
    tauto.
  rewrite H2 in H1.
    rewrite H1 in a.
     tauto.
  tauto.
 tauto.
generalize (crack_succ m x x').
  unfold crack in |- *.
   tauto.
Qed.

(* OK: *)

Lemma cA_1_Split:forall(m:fmap)(x x' z:dart),
 inv_hmap m -> crack m x x' -> 
   cA_1 (Split m Md.kd x x') Md.kd z = 
    if eq_dart_dec (cA m Md.kd x) z then x'
    else if eq_dart_dec (cA m Md.kd x') z then x 
         else cA_1 m Md.kd z.
Proof.
intros.
generalize (crack_exd m x x' H H0).
intro Exx'.
elim (exd_dec m z).
 intro.
   set (t := cA_1 (Split m Md.kd x x') Md.kd z) 
   in |- *.
   assert (z = cA (Split m Md.kd x x') Md.kd t).
  unfold t in |- *.
    rewrite cA_cA_1 in |- *.
    tauto.
  apply inv_hmap_Split.
     tauto.
  generalize (exd_Split m Md.kd x x' z).
     tauto.
 generalize H1.
   rewrite cA_Split in |- *.
  elim (eq_dart_dec x t).
   intros.
     elim (eq_dart_dec (cA m Md.kd x) z).
    intro.
      assert (x = cA_1 m Md.kd z).
     rewrite <- a1 in |- *.
       rewrite cA_1_cA in |- *.
       tauto.
      tauto.
      tauto.
    rewrite H2 in H3.
      rewrite cA_1_cA in H3.
     rewrite a0 in H3.
        tauto.
     tauto.
     tauto.
   elim (eq_dart_dec (cA m Md.kd x') z).
    intros.
      symmetry  in |- *.
       tauto.
   symmetry  in H2.
      tauto.
  elim (eq_dart_dec x' t).
   intros.
     elim (eq_dart_dec (cA m Md.kd x) z).
    symmetry  in a0.
       tauto.
   symmetry  in H2.
      tauto.
  elim (eq_dart_dec (cA m Md.kd x) z).
   intros.
     assert (x = cA_1 m Md.kd z).
    rewrite <- a0 in |- *.
      rewrite cA_1_cA in |- *.
      tauto.
     tauto.
     tauto.
   rewrite H2 in H3.
     rewrite cA_1_cA in H3.
     tauto.
    tauto.
   rewrite H2 in a.
     generalize (exd_cA m Md.kd t).
      tauto.
  elim (eq_dart_dec (cA m Md.kd x') z).
   intros.
     assert (x' = cA_1 m Md.kd z).
    rewrite <- a0 in |- *.
      rewrite cA_1_cA in |- *.
      tauto.
     tauto.
     tauto.
   rewrite H2 in H3.
     rewrite cA_1_cA in H3.
     tauto.
    tauto.
   rewrite H2 in a.
     generalize (exd_cA m Md.kd t).
      tauto.
  intros.
    rewrite H2 in |- *.
    rewrite cA_1_cA in |- *.
    tauto.
   tauto.
  rewrite H2 in a.
    generalize (exd_cA m Md.kd t).
     tauto.
  tauto.
  tauto.
intro.
  assert (cA_1 (Split m Md.kd x x') Md.kd z = nil).
 apply not_exd_cA_1.
  apply inv_hmap_Split.
     tauto.
 generalize (exd_Split m Md.kd x x' z).
   generalize (exd_dec m z).
   generalize (exd_dec (Split m Md.kd x x') z).
    tauto.
elim (eq_dart_dec (cA m Md.kd x) z).
 intro.
   rewrite <- a in b.
   generalize (exd_cA_cA_1 m Md.kd x).
    tauto.
elim (eq_dart_dec (cA m Md.kd x') z).
 intros.
   rewrite <- a in b.
   generalize (exd_cA_cA_1 m Md.kd x').
    tauto.
intros.
  rewrite H1 in |- *.
  rewrite not_exd_cA_1 in |- *.
  tauto.
 tauto.
 tauto.
Qed.

(* OK: *)

Lemma cA_Split_opp:forall(m:fmap)(x x' z:dart),
 inv_hmap m ->  
   cA (Split m Md.kd x x') (dim_opp Md.kd) z = 
      cA m (dim_opp Md.kd) z.
Proof.
unfold Split in |- *.
intros.
elim (succ_dec m Md.kd x).
 elim (succ_dec m Md.kd x').
  intros.
    induction Md.kd.
   rewrite cA_B_ter in |- *.
    simpl in |- *.
      rewrite cA_B_ter in |- *.
      tauto.
     tauto.
    intro.
      inversion H0.
   fold (Shift m zero x) in |- *.
     apply inv_hmap_Shift.
     tauto.
    tauto.
   simpl in |- *.
     intro.
     inversion H0.
  rewrite cA_B_ter in |- *.
   simpl in |- *.
     rewrite cA_B_ter in |- *.
     tauto.
    tauto.
   intro.
     inversion H0.
  fold (Shift m one x) in |- *.
    apply inv_hmap_Shift.
    tauto.
   tauto.
  simpl in |- *.
    intro.
    inversion H0.
 intros.
   rewrite cA_B_ter in |- *.
   tauto.
  tauto.
 intro.
   induction Md.kd.
  simpl in H0.
    inversion H0.
 simpl in H0.
   inversion H0.
rewrite cA_B_ter in |- *.
  tauto.
 tauto.
intro.
  induction Md.kd.
 inversion H0.
simpl in H0.
  inversion H0.
Qed.

(* IDEM, OK: *)

Lemma cA_1_Split_opp:forall(m:fmap)(x x' z:dart),
 inv_hmap m ->  
   cA_1 (Split m Md.kd x x') (dim_opp Md.kd) z = 
      cA_1 m (dim_opp Md.kd) z.
Proof.
unfold Split in |- *.
intros.
elim (succ_dec m Md.kd x).
 elim (succ_dec m Md.kd x').
  intros.
    induction Md.kd.
   rewrite cA_1_B_ter in |- *.
    simpl in |- *.
      rewrite cA_1_B_ter in |- *.
      tauto.
     tauto.
    intro.
      inversion H0.
   fold (Shift m zero x) in |- *.
     apply inv_hmap_Shift.
     tauto.
    tauto.
   simpl in |- *.
     intro.
     inversion H0.
  rewrite cA_1_B_ter in |- *.
   simpl in |- *.
     rewrite cA_1_B_ter in |- *.
     tauto.
    tauto.
   intro.
     inversion H0.
  fold (Shift m one x) in |- *.
    apply inv_hmap_Shift.
    tauto.
   tauto.
  simpl in |- *.
    intro.
    inversion H0.
 intros.
   rewrite cA_1_B_ter in |- *.
   tauto.
  tauto.
 intro.
   induction Md.kd.
  simpl in H0.
    inversion H0.
 simpl in H0.
   inversion H0.
rewrite cA_1_B_ter in |- *.
  tauto.
 tauto.
intro.
  induction Md.kd.
 inversion H0.
simpl in H0.
  inversion H0.
Qed.

(*===================================================
                END OF FUNCTOR MA /
===================================================*)

End MA.

(*=================================================
          END OF FUNCTOR MA /
  INSTANTIATION OF MA FOR DIMENSIONS 0 AND 1
==================================================*)

(* INSTANTIATIONS OF Sigd: *)

Module Md0<:Sigd.
Definition kd:=zero.
End Md0.

Module Md1<:Sigd.
Definition kd:=one.
End Md1.

Module MA0 := MA Md0.
Module MA1 := MA Md1.

(* TEST:
Check MA0.MfcA.expo.
MA0.MfcA.expo
     : fmap -> dart -> dart -> Prop
*)

(* ALIASES: *)

Definition expe:= MA0.MfcA.expo.
Definition expe_dec:= MA0.MfcA.expo_dec.
Definition expe_refl:= MA0.MfcA.expo_refl.
Definition expe_symm:= MA0.MfcA.expo_symm.
Definition expe_trans:=MA0.MfcA.expo_trans.
Definition betweene:= MA0.MfcA.between.
Definition betweene_dec:= MA0.MfcA.between_dec.

Definition expv:= MA1.MfcA.expo.
Definition expv_dec:= MA1.MfcA.expo_dec.
Definition expv_refl:= MA1.MfcA.expo_refl.
Definition expv_symm:= MA1.MfcA.expo_symm.
Definition expv_trans:=MA1.MfcA.expo_trans.
Definition betweenv:= MA1.MfcA.between.
Definition betweenv_dec:= MA1.MfcA.between_dec.

(*====================================================
           INSTANCIATION OF Mf FOR cF, cF_1:
=====================================================*)

Module McF<:Sigf.
Definition f := cF.
Definition f_1 := cF_1.
Definition exd_f := exd_cF.
Definition exd_f_1 := exd_cF_1.
Definition f_1_f := cF_1_cF.
Definition f_f_1 := cF_cF_1.
End McF.

Module MF:= Mf McF.

(* ALIASES: *)

(* VOIR:

Definition expof(m:fmap)(x y:dart):Prop:=
  inv_hmap m /\ MF.expo m x y.

Lemma expof_dec : forall(m:fmap)(x y:dart),
  {expof m x y} + {~expof m x y}.
Proof.
unfold expof in |- *.
intros.
generalize (MF.expo_dec m x y).
generalize (inv_hmap_dec m).
tauto.
Qed.

*)

Definition expof:= MF.expo.
Definition betweenf:= MF.between.

(* OK: Iter_cF_Shift: *)

Lemma Iter_cF_Shift: 
forall(m:fmap)(k:dim)(x z:dart)(i:nat),
 inv_hmap m -> succ m k x -> 
  let m0:= Shift m k x in
  Iter (cF m0) i z =  Iter (cF m) i z.
Proof.
induction i.
intros; simpl; tauto.
intros; unfold m0.
unfold Iter; fold Iter.
rewrite cF_Shift.
rewrite IHi.
tauto.
    tauto.
 tauto.
 tauto.
 tauto.
Qed.

(* expof_Shift: OK *)

Lemma expof_Shift: forall(m:fmap)(k:dim)(x z t:dart),
 inv_hmap m -> succ m k x -> 
   (expof (Shift m k x) z t <-> expof m z t).
Proof.
intros.
unfold expof in |- *.
generalize (inv_hmap_Shift m k x).
intro.
generalize (H1 H H0).
clear H1.
intro.
unfold MF.expo in |- *.
assert (exd m x).
 apply succ_exd with k.
   tauto.
  tauto.
generalize (exd_Shift m k x z).
  intro.
  split.
 intros.
   decompose [and] H4.
   clear H4.
   elim H6.
   clear H6.
   intros i Hi.
   split.
   tauto.
 split with i.
   rewrite <- Hi in |- *.
   symmetry  in |- *.
   apply Iter_cF_Shift.
   tauto.
  tauto.
intro.
  decompose [and] H4.
  clear H4.
  elim H6.
  clear H6.
  intros i Hi.
  split.
  tauto.
split with i.
  rewrite <- Hi in |- *.
  apply Iter_cF_Shift.
  tauto.
 tauto.
Qed.

Lemma expof_refl: forall (m : fmap) (z : dart), 
  exd m z -> expof m z z.
Proof. unfold expof in |- *; apply MF.expo_refl. Qed.

Lemma expof_symm: forall (m : fmap) (z t : dart), 
  inv_hmap m -> expof m z t -> expof m t z. 
Proof. unfold expof in |- *; apply MF.expo_symm. Qed.

Lemma expof_trans: forall (m : fmap) (z t u : dart),
  expof m z t -> expof m t u -> expof m z u.
Proof. unfold expof in |- *; apply MF.expo_trans. Qed.

Lemma expof_dec: forall (m : fmap) (z t : dart),
  inv_hmap m -> {expof m z t} + {~expof m z t}.
Proof. unfold expof ; apply MF.expo_dec. Qed.

Lemma betweenf_dec: forall(m:fmap)(z v t:dart), 
 inv_hmap m -> exd m z ->
    (betweenf m z v t \/ ~betweenf m z v t).
Proof. unfold betweenf ; apply MF.between_dec. Qed.

(*===================================================
                     THE END
===================================================*)

