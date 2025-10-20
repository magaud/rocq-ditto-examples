
(*=================================================================

                 Delaunay triangulation algorithm
                   
                        (Final version for papers)

(16 Janvier 2010)
===================================================================*)

Require Import TRIANG04 Lra.

Open Scope R_scope.

Set Asymmetric Patterns.

(*=========================================================
                  PRELIMINARIES : DETERMINANTS AND inCircle
===========================================================*)

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

Lemma neq_det4_first_last : 
  forall (a11 a12 a13 a14 
          a21 a22 a23 a24
          a31 a32 a33 a34
          a41 a42 a43 a44 : R),
  det4 a11 a12 a13 a14 
          a21 a22 a23 a24
          a31 a32 a33 a34
          a41 a42 a43 a44 =
- det4 a41 a42 a43 a44
          a21 a22 a23 a24
          a31 a32 a33 a34
          a11 a12 a13 a14.
Proof.
  intros; unfold det4, det3, det2; ring.
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

Lemma eq_det4_tr : 
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

Lemma inCircle_dec: forall (p q r s:point),
    {inCircle p q r s} + {~inCircle p q r s}.
Proof.
   intros. unfold inCircle.
   apply Rgt_dec.
Qed.

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

Lemma inCircle_tr :  forall (p q r s:point),
    inCircle p q r s -> inCircle q r p s. 
Proof.
 unfold inCircle. intros. 
 rewrite eq_det4_tr in H. tauto. 
Qed. 

(*===================================
                  PROOF OF YB for ccw_exchange
===================================*)

From Stdlib Require Import Psatz.

Definition ccwd (xp yp xq yq xr yr : R) :=
  xp * yq - xq * yp - xp * yr + xr * yp + xq * yr - xr * yq.

Definition ccwr (xp yp xq yq xr yr : R) := ccwd xp yp xq yq xr yr > 0.

Lemma axiom1' : forall xp yp xq yq xr yr,
  ccwd xp yp xq yq xr yr = ccwd xq yq xr yr xp yp.
intros; unfold ccwd; ring.
Qed.

Lemma axiom1 : forall xp yp xq yq xr yr,
  ccwr xp yp xq yq xr yr -> ccwr xq yq xr yr xp yp.
unfold ccwr; intros; rewrite axiom1' in H; assumption.
Qed.

Lemma axiom5 :
  forall xp yp xq yq xr yr xs ys xt yt,
  ccwr xq yq xp yp xr yr -> ccwr xq yq xp yp xs ys -> 
  ccwr xq yq xp yp xt yt -> ccwr xq yq xr yr xs ys ->
  ccwr xq yq xs ys xt yt -> ccwr xq yq xr yr xt yt.
unfold ccwr; intros xp yp xq yq xr yr xs ys xt yt pqr pqs pqt prs pst.
(* This is taken from Bertot & Pichardie 2001. *)

assert (Cramer : ccwd xq yq xp yp xs ys * ccwd xq yq xr yr xt yt = 
        ccwd xq yq xs ys xt yt * ccwd xq yq xp yp xr yr + 
        ccwd xq yq xr yr xs ys * ccwd xq yq xp yp xt yt).
  unfold ccwd; ring.
nra.
Qed.

Lemma eq_not_ccwr :
  forall xp yp xq yq xr yr, xp = xq -> yp = yq -> ~ccwr xp yp xq yq xr yr.
intros xp yp xq yq xr yr q1 q2; subst; unfold ccwr, ccwd.
  match goal with |- ~?a > 0 => assert (a = 0) by ring end.
psatz R.
Qed.

Definition in_circled (xp yp xq yq xr yr xs ys : R) :=
  xp *
       (yq * ((xr * xr + yr * yr) * 1 - 1 * (xs * xs + ys * ys)) -
        yr * ((xq * xq + yq * yq) * 1 - 1 * (xs * xs + ys * ys)) +
        ys * ((xq * xq + yq * yq) * 1 - 1 * (xr * xr + yr * yr))) -
       xq *
       (yp * ((xr * xr + yr * yr) * 1 - 1 * (xs * xs + ys * ys)) -
        yr * ((xp * xp + yp * yp) * 1 - 1 * (xs * xs + ys * ys)) +
        ys * ((xp * xp + yp * yp) * 1 - 1 * (xr * xr + yr * yr))) +
       xr *
       (yp * ((xq * xq + yq * yq) * 1 - 1 * (xs * xs + ys * ys)) -
        yq * ((xp * xp + yp * yp) * 1 - 1 * (xs * xs + ys * ys)) +
        ys * ((xp * xp + yp * yp) * 1 - 1 * (xq * xq + yq * yq))) -
       xs *
       (yp * ((xq * xq + yq * yq) * 1 - 1 * (xr * xr + yr * yr)) -
        yq * ((xp * xp + yp * yp) * 1 - 1 * (xr * xr + yr * yr)) +
        yr * ((xp * xp + yp * yp) * 1 - 1 * (xq * xq + yq * yq))).

Lemma ccwd_translation :
  forall a b xp yp xq yq xr yr,
  ccwd (xp + a) (yp + b) (xq + a) (yq + b) (xr + a) (yr + b) =
  ccwd xp yp xq yq xr yr.
intros; unfold ccwd; ring.
Qed.

Definition distance_sq (xp yp xq yq:R) :=
  (xp - xq)*(xp - xq) + (yp - yq)*(yp - yq).

Definition implicit_to_center_and_radius :
  forall a b c x y,  x*x + y*y + a*x +b*y + c =
  distance_sq x y ((-1/2)*a) ((-1/2) * b) +(c - (1/4) * (a*a + b * b)).
intros a b c x y; unfold distance_sq; field.
Qed.

Lemma translation_distance :
  forall a b xp yp xq yq,
    distance_sq (xp - a) (yp - b) (xq - a) (yq - b) =
    distance_sq xp yp xq yq.
intros; unfold distance_sq; ring.
Qed.

Definition in_circle (xp yp xq yq xr yr xs ys : R) :=
  in_circled xp yp xq yq xr yr xs ys > 0.

Lemma in_circled_polynomial :
  forall xp yp xq yq xr yr x y,
    in_circled xp yp xq yq xr yr x y =
    (- ccwd xp yp xq yq xr yr * (x * x + y * y) -
       ccwd yp (xp^2 + yp^2) yq (xq^2 + yq^2) yr (xr^2 + yr^2) * x +
       ccwd xp (xp^2 + yp^2) xq (xq^2 + yq^2) xr (xr^2 + yr^2) * y +
       ((xr^2 + yr^2) * yq * xp + xq * yr * (xp^2 + yp^2) +
        xr * yp * (xq^2 + yq^2) - xp * yr * (xq^2 + yq^2) -
        xq * yp * (xr^2 + yr^2) - xr * yq * (xp^2 + yp^2))).
intros; unfold in_circled, ccwd; ring.
Qed.

Lemma in_circled_distance :
  forall xp yp xq yq xr yr,
    ccwd xp yp xq yq xr yr > 0 ->
    exists a, exists b, exists r,
    forall x y,
    in_circled xp yp xq yq xr yr x y =
    - ccwd xp yp xq yq xr yr * ((distance_sq x y a b) - r).
intros xp yp xq yq xr yr cc.
assert (ccn : ccwd xp yp xq yq xr yr <> 0).
intros H; rewrite H in cc; case (Rgt_irrefl _ cc).
(* The formulas here are proposed by Coq in dummy proofs, where
  one first proposes 0 as value and use field_simplify
  to see what comes up.*)
exists (-(ccwd yp (xp^2 + yp^2) yq (xq^2 + yq^2) yr (xr^2 + yr^2)
         / (2 * ccwd xp yp xq yq xr yr))).
exists (ccwd xp (xp^2 + yp^2) xq (xq^2 + yq^2) xr (xr^2 + yr^2)
         / (2 * ccwd xp yp xq yq xr yr)).
exists((4 * ccwd xp yp xq yq xr yr ^ 2 * xr ^ 2 * yq * xp -
    4 * ccwd xp yp xq yq xr yr ^ 2 * xr ^ 2 * xq * yp +
    4 * ccwd xp yp xq yq xr yr ^ 2 * xr * yq ^ 2 * yp -
    4 * ccwd xp yp xq yq xr yr ^ 2 * xr * yq * xp ^ 2 -
    4 * ccwd xp yp xq yq xr yr ^ 2 * xr * yq * yp ^ 2 +
    4 * ccwd xp yp xq yq xr yr ^ 2 * xr * xq ^ 2 * yp +
    4 * ccwd xp yp xq yq xr yr ^ 2 * yr ^ 2 * yq * xp -
    4 * ccwd xp yp xq yq xr yr ^ 2 * yr ^ 2 * xq * yp -
    4 * ccwd xp yp xq yq xr yr ^ 2 * yr * yq ^ 2 * xp +
    4 * ccwd xp yp xq yq xr yr ^ 2 * yr * xp ^ 2 * xq -
    4 * ccwd xp yp xq yq xr yr ^ 2 * yr * xp * xq ^ 2 +
    4 * ccwd xp yp xq yq xr yr ^ 2 * yr * xq * yp ^ 2 +
    ccwd xp yp xq yq xr yr *
    ccwd yp (xp ^ 2 + yp ^ 2) yq (xq ^ 2 + yq ^ 2) yr (xr ^ 2 + yr ^ 2) ^ 2 +
    ccwd xp yp xq yq xr yr *
    ccwd xp (xp ^ 2 + yp ^ 2) xq (xq ^ 2 + yq ^ 2) xr (xr ^ 2 + yr ^ 2) ^ 2) /
   (4 * ccwd xp yp xq yq xr yr ^ 3)).
intros x y; rewrite in_circled_polynomial.
unfold distance_sq; field; assumption.
Qed.

Lemma sq_diff_eq_0_eq x x' : (x - x') * (x - x') = 0 ->
  x = x'.
Proof.
intros.
nra.
Qed.

Lemma distance_0_eq :
  forall x y x' y', distance_sq x y x' y' = 0 -> x = x' /\ y = y'.
Proof.
intros x y x' y'.
assert (0 <= (y - y') * (y - y')).
  now change (0 <= Rsqr (y - y')); apply Rle_0_sqr.
assert (0 <= (x - x') * (x - x')).
  now change (0 <= Rsqr (x - x')); apply Rle_0_sqr.
unfold distance_sq; split.
  apply sq_diff_eq_0_eq.
  apply Rle_antisym; lra.
apply sq_diff_eq_0_eq.
apply Rle_antisym; lra.
Qed.

Lemma distance_sq_pos :
  forall x y x' y', distance_sq x y x' y' >= 0.
intros; unfold distance_sq.
assert (0 <= (y - y') * (y - y')).
  now change (0 <= Rsqr (y - y')); apply Rle_0_sqr.
assert (0 <= (x - x') * (x - x')).
  now change (0 <= Rsqr (x - x')); apply Rle_0_sqr.
lra.
Qed.

Lemma in_circled1 :
  forall xp yp xq yq xr yr, in_circled xp yp xq yq xr yr xp yp = 0.
intros; unfold in_circled; ring.
Qed.

Lemma in_circled2 :
  forall xp yp xq yq xr yr, in_circled xp yp xq yq xr yr xq yq = 0.
intros; unfold in_circled; ring.
Qed.

Lemma in_circled3 :
  forall xp yp xq yq xr yr, in_circled xp yp xq yq xr yr xr yr = 0.
intros; unfold in_circled; ring.
Qed.

Lemma ccw_circle_positive_radius :
  forall xp yp xq yq xr yr a b r,
    ccwd xp yp xq yq xr yr > 0 ->
    (forall x y, in_circled xp yp xq yq xr yr x y =
    - ccwd xp yp xq yq xr yr * ((distance_sq x y a b) - r)) ->
    r > 0.
intros xp yp xq yq xr yr a b r q d.
assert (vp := in_circled1 xp yp xq yq xr yr).
rewrite d in vp.
assert (vdp := distance_sq_pos xp yp a b).
assert (r >= 0) by nra.
case (Req_dec r 0); [ | nra].
intros r0; assert (pa : distance_sq xp yp a b = 0) by nra.
assert (vq := in_circled2 xp yp xq yq xr yr).
rewrite d in vq.
assert (qa : distance_sq xq yq a b = 0) by nra.
destruct (distance_0_eq _ _ _ _ pa).
destruct (distance_0_eq _ _ _ _ qa).
assert (xpq:xp = xq) by (subst; auto).
assert (ypq:yp = yq) by (subst; auto).
assert (tmp:= eq_not_ccwr _ _ _ _ xr yr xpq ypq).
case tmp; unfold ccwr; assumption.
Qed.

Lemma in_circle_ccwr :
  forall x y a b, 0 < a^2 + b^2 ->
    distance_sq x y a b <= (a^2 + b^2) -> (x = 0 -> y <> 0) ->
    ccwr 0 0 b (-a) x y.
unfold ccwr, ccwd, distance_sq; intros x y a b rp inc diff; ring_simplify.
ring_simplify in inc. case (Req_dec x 0).
intros x0; rewrite x0 in inc |- *. 
assert (diff' := diff x0); nra.
intros; nra.
Qed.

Lemma exists_tangent :
  forall xp yp xq yq xr yr, ccwr xp yp xq yq xr yr ->
   exists xt, exists yt,  ccwr xp yp xt yt xq yq /\ ccwr xp yp xt yt xr yr /\
      forall xs ys, in_circle xp yp xq yq xr yr xs ys -> ccwr xp yp xt yt xs ys.
intros xp yp xq yq xr yr cc.
destruct (in_circled_distance xp yp xq yq xr yr cc) as [a [b [r H]]].
exists (xp + b - yp); exists (yp + xp - a).
assert (qa : distance_sq xq yq a b = r).
assert (ciq := in_circled2 xp yp xq yq xr yr).
rewrite H in ciq; unfold ccwr in cc; nra.
assert (ra : distance_sq xr yr a b = r).
assert (cir := in_circled3 xp yp xq yq xr yr).
rewrite H in cir; unfold ccwr in cc; nra.
assert (xq - xp = 0 -> yq - yp <> 0).
  intros H1 H2; assert (H1' : xp = xq) by nra.
  assert (H2' : yp = yq) by nra.
case (eq_not_ccwr _ _ _ _ xr yr H1' H2'); assumption.
assert (xr - xp = 0 -> yr - yp <> 0).
  intros H1 H2; assert (H1' : xr = xp) by nra.
  assert (H2' : yr = yp) by nra.
case (eq_not_ccwr _ _ _ _ xq yq H1' H2').
apply axiom1; apply axiom1; assumption.
assert (pa : distance_sq xp yp a b = r).
assert (cip := in_circled1 xp yp xq yq xr yr).
rewrite H in cip; unfold ccwr in cc; nra.
unfold ccwr; rewrite <- (ccwd_translation (-xp) (-yp) _ _ _ _ xq yq).
rewrite <- (ccwd_translation (-xp) (-yp) _ _ _ _ xr yr).
replace (xp + - xp) with 0 by ring.
replace (yp + - yp) with 0 by ring.
replace (xp + b - yp + - xp) with (b - yp) by ring.
replace (yp + xp - a + - yp) with (-(a - xp)) by ring.
assert (rp := ccw_circle_positive_radius xp yp xq yq xr yr a b r cc H).
assert (d' : 0 < (a-xp)^2 + (b-yp)^2).
match goal with |- 0 < ?A => replace A with (distance_sq xp yp a b) end.
rewrite pa; solve[auto with real].
unfold distance_sq; ring.
split.
apply in_circle_ccwr.
assumption.
fold (xq - xp); fold (yq - yp); rewrite translation_distance.
match goal with |- ?a <= ?b => assert (dq : a = b) end.
rewrite qa, <- pa; unfold distance_sq; ring.
rewrite dq; solve [auto with real].
assumption.
split.
apply in_circle_ccwr.
assumption.
fold (xr - xp); fold (yr - yp); rewrite translation_distance.
match goal with |- ?a <= ?b => assert (dq : a = b) end.
rewrite ra, <- pa; unfold distance_sq; ring.
rewrite dq; solve [auto with real].
assumption.
intros xs ys inc.
rewrite <- (ccwd_translation (-xp) (-yp) _ _ _ _ xs ys).
replace (xp + - xp) with 0 by ring.
replace (yp + - yp) with 0 by ring.
replace (xp + b - yp + - xp) with (b - yp) by ring.
replace (yp + xp - a + - yp) with (-(a - xp)) by ring.
apply in_circle_ccwr.
assumption.
unfold in_circle in inc; rewrite H in inc.
assert (sa : distance_sq xs ys a b < r).
unfold ccwr in cc; nra.
fold (xs - xp); fold (ys - yp); rewrite translation_distance.
match goal with |- _ <= ?A => assert (dd : distance_sq xp yp a b = A) end.
unfold distance_sq; ring.
rewrite <- dd, pa; solve[auto with real].
intros Hx Hy; assert (Hx' : xs = xp) by (clear - Hx; nra).
assert (Hy' : ys = yp) by (clear - Hy; nra).
rewrite Hx', Hy' in inc; unfold in_circle in inc; rewrite in_circled1 in inc.
clear -inc; nra.
Qed.

Lemma exchange :
forall xp yp xq yq xr yr xs ys,  ccwr xp yp xq yq xr yr ->
  ccwr xp yp xr yr xs ys ->
  in_circle xp yp xq yq xr yr xs ys ->
  ccwr xp yp xq yq xs ys /\ ccwr xq yq xr yr xs ys.
Proof.
intros xp yp xq yq xr yr xs ys cc1 cc2 ic.
split.
destruct (exists_tangent _ _ _ _ _ _ cc1) as
  [xt [yt [ptq [ptr pta]]]].
apply axiom5 with xt yt xr yr; try assumption.
apply pta; assumption.
apply axiom1 in cc2.
destruct (exists_tangent _ _ _ _ _ _ cc2) as
  [xt [yt [rts [rtp rta]]]].
apply axiom1; apply axiom1.
apply axiom5 with xt yt xp yp; try assumption.
apply rta.
unfold in_circle; replace
  (in_circled xr yr xs ys xp yp xq yq) with
  (in_circled xp yp xq yq xr yr xs ys).
exact ic.
unfold in_circled; ring.
apply axiom1; apply axiom1; assumption.
Qed.

(*========END OF YB'PROOF========*)

(*===========BRIDGE============ *)

Lemma ccw_exchange_bis: forall (p q r s: point),
  ccw p q r -> ccw p r s -> inCircle p q r s ->
      (ccw p q s /\ ccw q r s).
Proof.
  induction p. rename a into xp. rename b into yp. 
  induction q. rename a into xq. rename b into yq. 
  induction r. rename a into xr. rename b into yr. 
  induction s. rename a into xs. rename b into ys. 
  unfold ModelOfKnuth.ccw. unfold ModelOfKnuth.det.
  unfold inCircle. simpl. 
  generalize (exchange xp yp xq yq xr yr xs ys). 
  unfold ccwr. unfold ccwd. unfold in_circle. 
  unfold in_circled. unfold det4. unfold det3. unfold det2. 
  intros. 
  set(D:=
    xp *
    (yq * ((xr * xr + yr * yr) * 1 - 1 * (xs * xs + ys * ys)) -
     yr * ((xq * xq + yq * yq) * 1 - 1 * (xs * xs + ys * ys)) +
     ys * ((xq * xq + yq * yq) * 1 - 1 * (xr * xr + yr * yr))) -
    xq *
    (yp * ((xr * xr + yr * yr) * 1 - 1 * (xs * xs + ys * ys)) -
     yr * ((xp * xp + yp * yp) * 1 - 1 * (xs * xs + ys * ys)) +
     ys * ((xp * xp + yp * yp) * 1 - 1 * (xr * xr + yr * yr))) +
    xr *
    (yp * ((xq * xq + yq * yq) * 1 - 1 * (xs * xs + ys * ys)) -
     yq * ((xp * xp + yp * yp) * 1 - 1 * (xs * xs + ys * ys)) +
     ys * ((xp * xp + yp * yp) * 1 - 1 * (xq * xq + yq * yq))) -
    xs *
    (yp * ((xq * xq + yq * yq) * 1 - 1 * (xr * xr + yr * yr)) -
     yq * ((xp * xp + yp * yp) * 1 - 1 * (xr * xr + yr * yr)) +
     yr * ((xp * xp + yp * yp) * 1 - 1 * (xq * xq + yq * yq)))). 
  fold D in H2. fold D in H. 
  apply H. tauto. tauto. tauto. 
Qed. 

(* IMPORTANT: *)

Theorem ccw_exchange: forall (p q r s: point),
  ccw p q r -> ccw q p s -> inCircle p q r s ->
      (ccw r s q /\ ccw s r p).
Proof. 
  intros. 
  generalize (ccw_exchange_bis q r p s). 
  intros. 
  generalize (ccw_axiom_1 p q r H). intro. 
  generalize (inCircle_tr p q r s H1). intro. 
  assert (ccw q r s /\ ccw r p s). tauto. 
  split. apply ccw_axiom_1. tauto. 
  apply ccw_axiom_1. apply ccw_axiom_1. tauto. 
Qed.

(*===========END BRIDGE=====================*)

(*=========================================
                      Illegal and its Properties -
                           Implies prec_Flip:
==========================================*)

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

(* ==========================================
                                 
                        A REPRENDRE (ANCIENNE VERSION)

============================================ *)

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

Definition some_illegal:= illegal_first.


Lemma exd_some_illegal: forall m mr, 
    let x := some_illegal m mr in
    x <> Del01.nil -> exd m x.
Proof exd_illegal_first.

Lemma illegal_some_illegal:
 forall m,
   let x := some_illegal m m in
      x <> Del01.nil -> illegal m x.
Proof illegal_first_illegal.


(*=====================================
                          
                               FIN REPRISE 

 =====================================*)

(* Require Import List. *)

(*=====================================
                  
                               A SUPPRIMER : 

 =====================================

(* rand n : returns a natural <= n *) 

(*
Parameter rand: nat -> nat.

Axiom rand_le_n : forall n, (rand n <= n)%nat.
*)


Definition empty_list (X:Type)(l: list X):Prop:=
  match l with
    nil => True
  | _ => False
 end.

Lemma empty_list_dec : forall (X:Type)(l: list X),
  {empty_list X l} + {~empty_list X l}.
Proof. induction l. simpl. tauto. simpl. tauto. Qed.

Fixpoint illegal_list (m mr:fmap){struct m}: list dart:=
  match m with
      V => nil
   |  I m0 x t p => 
        let l:= illegal_list m0 mr in
        if illegal_dec mr x then x :: l  else illegal_list m0 mr 
   |  L m0 k x y => illegal_list m0 mr
 end.

Lemma In_illegal_list: forall (m mr:fmap)(x:dart),
   In x (illegal_list m mr) -> exd m x. 
Proof.
  intros. induction m. 
  simpl in H. tauto.
  simpl in H. simpl. generalize H. clear H.
    elim (illegal_dec mr d). simpl. tauto. tauto.
  simpl. simpl in H. tauto.
Qed.

Definition some_illegal(m mr: fmap): dart := 
  let l:= illegal_list m mr in 
  if empty_list_dec dart l then  Del01.nil
  else nth (rand (length l - 1)%nat) l Del01.nil.

Lemma exd_some_illegal: forall m mr, 
    let x := some_illegal m mr in
    x <> Del01.nil -> exd m x. 
Proof.
 unfold some_illegal. intros m mr. 
set (l:=illegal_list m mr). 
elim empty_list_dec. tauto. 
   set (x:= nth (rand (length l - 1)) l Del01.nil). 
   intros. assert (In x l). 
   eapply nth_In.  
   assert (rand (length l - 1) <= (length l - 1))%nat. 
   apply rand_le_n. 
   assert (0 < length l)%nat.
   induction l. simpl in b. tauto. simpl. lia. 
   lia. eapply In_illegal_list. 
   unfold l in H0. apply H0.
Qed.

Definition no_dart_illegal(m:fmap):Prop:= 
    empty_list dart (illegal_list m m).

Lemma nth_illegal_illegal: forall m mr x, 
    In x (illegal_list m mr) -> illegal mr x.
Proof.
  intros. induction m. 
  simpl in H. tauto.
  simpl in H. generalize H. clear H.
    elim (illegal_dec mr d). simpl. intros.
      elim H. intro. rewrite <-H0. tauto.  tauto. 
    tauto. simpl in H. tauto.
Qed.
 
Lemma some_illegal_illegal_aux:
 forall m mr, 
   let x :=some_illegal m mr in
    x <> Del01.nil -> illegal mr x.
Proof.
  intros m mr. 
  unfold some_illegal. 
  set (l:=illegal_list m mr). 
  elim (empty_list_dec dart l). tauto. 
  set(p:=rand (length l - 1)). set (x:=nth p l Del01.nil). 
  intros. eapply nth_illegal_illegal.
  eapply nth_In. fold l. 
  assert (rand (length l - 1) <= (length l - 1))%nat. 
  apply rand_le_n. 
  assert (0 < length l)%nat.
  induction l. simpl in b. tauto. simpl. lia. 
  unfold p. lia. 
Qed.

Lemma illegal_some_illegal: forall m,
   let x := some_illegal m m in
      x <> Del01.nil -> illegal m x.
Proof.
    intros. apply some_illegal_illegal_aux. fold x. tauto.
Qed.

(* Stopping test: *)

Lemma no_dart_illegal_dec: 
   forall m, {no_dart_illegal m} + {~no_dart_illegal m}.
Proof.
   unfold no_dart_illegal. intro.
   apply empty_list_dec.
Qed.

===========================================
                                  
                              FIN SUPPRESSION 

============================================*)

(* Next map: *)

Definition next (m:fmap): fmap := 
   let z:= some_illegal m m in 
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

Lemma illegal_prec_Flip_emb: forall (m:fmap)(x:dart),
    illegal m x ->prec_Flip_emb m x.
Proof.
   unfold illegal. unfold prec_Flip_emb.
    intros. 
   generalize (ccw_exchange 
     (fpoint m x) (fpoint m (cA m zero x))
        (fpoint m (cF m (cF m x)))
         (fpoint m (cF m (cF m (cA m zero x))))).
   intros. 
     assert (ccw (fpoint m (cF m (cF m x))) (fpoint m (cF m (cF m (cA m zero x))))
       (fpoint m (cA m zero x)) /\
     ccw (fpoint m (cF m (cF m (cA m zero x)))) (fpoint m (cF m (cF m x)))
       (fpoint m x)). tauto. split. tauto. split. tauto. clear H0 H. split. 
    apply ccw_axiom_1. apply ccw_axiom_1. tauto. 
    apply ccw_axiom_1. apply ccw_axiom_1. tauto. 
Qed.

Theorem illegal_prec_Flip:  forall (m:fmap)(x:dart),
  inv_Triangulation m -> isWellembede m -> isWellembedv m -> 
    exd m x -> illegal m x -> prec_Flip m x. 
Proof.
  intros. apply prec_Flip_emb_prec_Flip.
   tauto. tauto. tauto. tauto. 
     apply illegal_prec_Flip_emb. tauto.
Qed.

(*==================================================================
                                 TOWARD DELAUNAY
==================================================================*)

From Stdlib Require Import Recdef Arith Compare_dec Bool.

Open Scope nat_scope.

(*==================================================================
                      General properties of lists
==================================================================*)

(* RECALL: forallb is builtin: forall with a boolean function:

forallb = 
fun (A : Type) (f : A -> bool) =>
fix forallb (l : list A) : bool :=
  match l with
  | nil => true
  | a :: l0 => f a && forallb l0
  end
     : forall A : Type, (A -> bool) -> list A -> bool
*)

(* This lemma should be given in the standard library. *)

(*
Lemma forallb_app : forall A p (l1 l2:list A),
  forallb p (l1++l2) = forallb p l1 && forallb p l2.
intros; induction l1; simpl; [solve [auto] | ].
case (p a); simpl; solve[auto].
Qed.
*)
(* Every element of l satisfies pr: *)

From Stdlib Require Import List.

Fixpoint foralll (A:Type)(pr:A->Prop)(l:list A) : Prop :=
  match l with
    nil => True
  | a::tl => pr a /\ foralll A pr tl
  end.

Arguments foralll : default implicits.

(* Every element of l1 ++ l2 satisfies pr
 iff every element of l1 and every element of l2 satisfies pr: *)

Lemma foralll_app : forall A p (l1 l2 : list A),
  foralll p (l1++l2) <-> foralll p l1 /\ foralll p l2.
intros A p l1 l2; induction l1; simpl; intuition auto.
Qed.

(* Flip preserves the ordered lists of darts and tags, it also
  preserved the set of points, but not the order nor the multiplicity,
  so we need to sort the set of points to show preservation. *)

Fixpoint darts_of_fmap (m:fmap) : list dart :=
  match m with
    I m' d _ _ => d::darts_of_fmap m'
  | L m' _ _ _ => darts_of_fmap m'
  | V => nil
  end.

Fixpoint points_of_fmap (m:fmap) : list point :=
  match m with
    I m'  _ _ p => p::points_of_fmap m'
  | L m' _ _ _ => points_of_fmap m'
  | V => nil
  end.

Fixpoint tags_of_fmap(m:fmap) : list tag:=
  match m with
      V => nil
     |  I m x t p => t :: (tags_of_fmap m)
     |  L m k x y => tags_of_fmap m
   end.

Lemma B_preserves_darts :
forall m k x, darts_of_fmap (B m k x) = darts_of_fmap m.
intros m k x; induction m; simpl.
  reflexivity.
 rewrite IHm; reflexivity.
case (eq_dim_dec d k); simpl; [ | intros; exact IHm].
case (eq_dart_dec d0 x);simpl; [reflexivity | intros; assumption].
Qed.

Lemma B_preserves_tags :
forall m k x, tags_of_fmap (B m k x) = tags_of_fmap m.
intros m k x; induction m; simpl;[reflexivity |rewrite IHm; reflexivity | ].
case (eq_dim_dec d k); simpl; [ | intros; exact IHm].
case (eq_dart_dec d0 x);simpl; [reflexivity | intros; assumption].
Qed.

Lemma B_preserves_fpoint :
  forall m k x y, fpoint (B m k x) y = fpoint m y.
induction m as [ | m IHm d t p | m IHm kl d d']; intros k x y.
  reflexivity.
 simpl; destruct (eq_dart_dec d y);[reflexivity | apply IHm].
simpl; destruct (eq_dim_dec kl k);
  [destruct (eq_dart_dec d x);[reflexivity | simpl] | simpl]; apply IHm.
Qed.

Lemma Split_preserves_darts :
  forall m k x1 x2, darts_of_fmap (Split m k x1 x2) = darts_of_fmap m.
intros m k x1 x2; unfold Split.
case (succ_dec m k x1); [ | intros; solve[apply B_preserves_darts]].
case (succ_dec m k x2); [ | intros; solve[apply B_preserves_darts]].
intros _ _; repeat (rewrite B_preserves_darts; simpl); reflexivity.
Qed.

Lemma Split_preserves_tags :
  forall m k x1 x2, tags_of_fmap (Split m k x1 x2) = tags_of_fmap m.
intros m k x1 x2; unfold Split.
case (succ_dec m k x1); [ | intros; solve[apply B_preserves_tags]].
case (succ_dec m k x2); [ | intros; solve[apply B_preserves_tags]].
intros _ _; repeat (rewrite B_preserves_tags; simpl); reflexivity.
Qed.

Lemma Split_preserves_fpoint :
  forall m k x1 x2 y, fpoint (Split m k x1 x2) y = fpoint m y.
intros m k x1 x2 y; unfold Split.
case (succ_dec m k x1); [ | intros; solve[apply B_preserves_fpoint]].
case (succ_dec m k x2); [ | intros; solve[apply B_preserves_fpoint]].
intros _ _; repeat (rewrite B_preserves_fpoint; simpl); reflexivity.
Qed.

Lemma Shift_preserves_darts :
  forall m k x, darts_of_fmap (Shift m k x) = darts_of_fmap m.
intros m k x; unfold Shift; simpl; apply B_preserves_darts.
Qed.

Lemma Shift_preserves_tags :
  forall m k x, tags_of_fmap (Shift m k x) = tags_of_fmap m.
intros m k x; unfold Shift; simpl; apply B_preserves_tags.
Qed.

Lemma Shift_preserves_fpoint :
  forall m k x y, fpoint (Shift m k x) y = fpoint m y.
intros m k x; unfold Shift; simpl; apply B_preserves_fpoint.
Qed.

Lemma G_preserves_darts :
  forall m k x1 x2, darts_of_fmap (G m k x1 x2) = darts_of_fmap m.
intros m k x1 x2; unfold G; case (succ_dec m k x1); simpl;[ | reflexivity].
intros _; apply B_preserves_darts.
Qed.

Lemma G_preserves_tags :
  forall m k x1 x2, tags_of_fmap (G m k x1 x2) = tags_of_fmap m.
intros m k x1 x2; unfold G; case (succ_dec m k x1); simpl;[ | reflexivity].
intros _; apply B_preserves_tags.
Qed.

Lemma G_preserves_fpoint :
  forall m k x1 x2 y, fpoint (G m k x1 x2) y = fpoint m y.
intros m k x1 x2; unfold G; case (succ_dec m k x1); simpl;[ | reflexivity].
intros _; apply B_preserves_fpoint.
Qed.

Lemma Merge_preserves_darts : forall m k x1 x2,
  darts_of_fmap (Merge m k x1 x2) = darts_of_fmap m.
intros m k x1 x2; unfold Merge; rewrite G_preserves_darts.
case (pred_dec m k x2); intros _; [apply Shift_preserves_darts |reflexivity].
Qed.

Lemma Merge_preserves_tags : forall m k x1 x2,
  tags_of_fmap (Merge m k x1 x2) = tags_of_fmap m.
intros m k x1 x2; unfold Merge; rewrite G_preserves_tags.
case (pred_dec m k x2); intros _; [apply Shift_preserves_tags |reflexivity].
Qed.

Lemma Merge_preserves_fpoint : forall m k x1 x2 y,
  fpoint (Merge m k x1 x2) y = fpoint m y.
intros m k x1 x2 y; unfold Merge; rewrite G_preserves_fpoint.
case (pred_dec m k x2); intros _; [apply Shift_preserves_fpoint |reflexivity].
Qed.

Lemma Flip_topo_preserves_darts :
  forall m x, darts_of_fmap (Flip_topo m x) = darts_of_fmap m.
intros m x; unfold Flip_topo.
 rewrite !Merge_preserves_darts, !Split_preserves_darts; reflexivity.
Qed.

Lemma Flip_topo_preserves_tags :
  forall m x, tags_of_fmap (Flip_topo m x) = tags_of_fmap m.
intros m x; unfold Flip_topo.
 rewrite !Merge_preserves_tags, !Split_preserves_tags; reflexivity.
Qed.

Lemma Flip_topo_preserves_fpoint :
  forall m x y, fpoint (Flip_topo m x) y = fpoint m y.
intros m x y; unfold Flip_topo.
 rewrite !Merge_preserves_fpoint, !Split_preserves_fpoint; reflexivity.
Qed.

Lemma Chp_preserves_darts :
  forall m x p, darts_of_fmap (Chp m x p) = darts_of_fmap m.
intros m x p; induction m; simpl; [reflexivity | | assumption ].
case (eq_dart_dec d x); simpl; [ | intros; rewrite IHm]; reflexivity.
Qed.

Lemma Chp_preserves_tags :
  forall m x p, tags_of_fmap (Chp m x p) = tags_of_fmap m.
intros m x p; induction m; simpl; [reflexivity | | assumption ].
case (eq_dart_dec d x); simpl; [ | intros; rewrite IHm]; reflexivity.
Qed.

Lemma Flip_emb_preserves_darts :
  forall m x y x' y', darts_of_fmap (Flip_emb m x y x' y') = darts_of_fmap m.
intros m x y x' y'; unfold Flip_emb; rewrite !Chp_preserves_darts; reflexivity.
Qed.

Lemma Flip_emb_preserves_tags :
  forall m x y x' y', tags_of_fmap (Flip_emb m x y x' y') = tags_of_fmap m.
intros m x y x' y'; unfold Flip_emb; rewrite !Chp_preserves_tags; reflexivity.
Qed.

Lemma Flip_preserves_darts :
  forall m x, darts_of_fmap (Flip m x) = darts_of_fmap m.
intros m x; unfold Flip;
  rewrite Flip_emb_preserves_darts, Flip_topo_preserves_darts; reflexivity.
Qed.

Lemma Flip_preserves_tags :
  forall m x, tags_of_fmap (Flip m x) = tags_of_fmap m.
intros m x; unfold Flip;
  rewrite Flip_emb_preserves_tags, Flip_topo_preserves_tags; reflexivity.
Qed.

Lemma B_preserves_points :
forall m k x, points_of_fmap (B m k x) = points_of_fmap m.
intros m k x; induction m; simpl.
  reflexivity.
 rewrite IHm; reflexivity.
case (eq_dim_dec d k); simpl; [ | intros; exact IHm].
case (eq_dart_dec d0 x);simpl; [reflexivity | intros; assumption].
Qed.

Lemma Split_preserves_points :
  forall m k x1 x2, points_of_fmap (Split m k x1 x2) = points_of_fmap m.
intros m k x1 x2; unfold Split.
case (succ_dec m k x1); [ | intros; solve[apply B_preserves_points]].
case (succ_dec m k x2); [ | intros; solve[apply B_preserves_points]].
intros _ _; repeat (rewrite B_preserves_points; simpl); reflexivity.
Qed.

Lemma Shift_preserves_points :
  forall m k x, points_of_fmap (Shift m k x) = points_of_fmap m.
intros m k x; unfold Shift; simpl; apply B_preserves_points.
Qed.

Lemma G_preserves_points :
  forall m k x1 x2, points_of_fmap (G m k x1 x2) = points_of_fmap m.
intros m k x1 x2; unfold G; case (succ_dec m k x1); simpl;[ | reflexivity].
intros _; apply B_preserves_points.
Qed.

Lemma Merge_preserves_points : forall m k x1 x2,
  points_of_fmap (Merge m k x1 x2) = points_of_fmap m.
intros m k x1 x2; unfold Merge; rewrite G_preserves_points.
case (pred_dec m k x2); intros _; [apply Shift_preserves_points |reflexivity].
Qed.

Lemma Flip_topo_preserves_points :
  forall m x, points_of_fmap (Flip_topo m x) = points_of_fmap m.
intros m x; unfold Flip_topo.
 rewrite !Merge_preserves_points, !Split_preserves_points; reflexivity.
Qed.

Definition lex (p1 p2 : point) :=
  match p1, p2 with
     (x1,x2),(y1,y2) => (x1 < y1 \/ (x1=y1 /\ x2 <= y2))%R
  end.

Lemma lex_antisym : forall p1 p2, lex p1 p2 -> lex p2 p1 -> p1 = p2.
intros [x1 y1] [x2 y2] [x1x2 | [x1x2 y1y2]] [x2x1 | [x2x1 y2y1]].
   lra.
  lra.
 lra.
assert (y1 = y2) by (apply Rle_antisym; assumption).
clear x2x1; subst; reflexivity.
Qed.

Lemma lex_trans : forall p1 p2 p3, lex p1 p2 -> lex p2 p3 -> lex p1 p3.
intros [x1 y1] [x2 y2] [x3 y3]; unfold lex.
intros [x1x2 | [x1x2 y1y2]] [x2x3 | [x2x3 y1y3]].
   left; lra.
  left; lra.
 left; lra.
right; split;[subst; reflexivity | lra].
Qed.

Lemma lex_total : forall p1 p2, ~lex p1 p2 -> lex p2 p1.
intros [x1 y1][x2 y2]; unfold lex.
intros n; case (Rlt_dec x2 x1); [tauto | ].
intros n'; case (Req_dec_1 x2 x1);[right; split;[tauto | ] | ].
 case (Rle_dec y2 y1); [tauto | ].
 intros n''; case n; right; subst; split; [reflexivity | ].
apply Rlt_le; apply Rnot_le_lt; assumption.
intros n''; case n; left; apply Rnot_le_lt.
intros n3; case n3.
 intros n4; apply n'; assumption.
intros; contradiction.
Qed.

Definition lex_dec (p1 p2:point) : {lex p1 p2}+{~lex p1 p2}.
destruct p1 as [x1 x2]; destruct p2 as [y1 y2].
case (Rlt_dec x1 y1); intros x1y1.
 left; left; assumption.
case (Req_dec_1 x1 y1); intros q1.
 case (Rle_dec x2 y2); intros x2y2.
  intros; left; right; split; assumption.
 right; intros H; case H.
  exact x1y1.
 intros [_ abs]; apply x2y2; assumption.
right; intros H; case H.
 exact x1y1.
intros [q2 _]; apply q1; assumption.
Qed.

Definition p_dec (p1 p2 : point) : {p1 = p2} + {p1 <> p2}.
destruct p1 as [x1 y1]; destruct p2 as [x2 y2].
case (Req_dec_1 x1 x2); intros x1x2.
 case (Req_dec_1 y1 y2); intros y1y2.
  subst; left; reflexivity.
 right; intros q; injection q; intros; subst; case y1y2; reflexivity.
right; intros q; injection q; intros; subst; case x1x2; reflexivity.
Qed.

(* sorting and removing duplications. *)

Fixpoint insert (p:point) (l:list point) : list point :=
  match l with
    p1::l => if p_dec p p1 then p1::l else
             if lex_dec p p1 then p::p1::l else p1::insert p l
  | nil => p::nil
  end. 

Fixpoint sort (l:list point) : list point :=
  match l with
    p::l => insert p (sort l)
  | nil => nil
  end.

Lemma isWellembedv_deg_dup :
  forall m d p, inv_hmap m -> isWellembedv m -> isPoly m ->
    exd m d -> fpoint m d = p -> exists d', d <> d' /\ exd m d' /\
               fpoint m d' = p.
intros m d p h w pl x fp; unfold isPoly, degreev in pl.
set (dd := MA1Tr.MfM.degree m d).
assert (tmp := MA1Tr.MfM.degree_lub m d h x); fold dd in tmp.
destruct tmp as [H1 [H2 H3]].
exists (Iter (MA1Tr.MfM.f m) 1 d).
split.
 assert (tmp := pl d x); fold dd in tmp; apply sym_not_equal; apply H3; lia.
assert (pp: MA1Tr.MfM.expo m d (MA1Tr.MfM.f m d)).
 simpl; split; [assumption | exists 1; reflexivity].
split.
 apply MA1Tr.MfM.expo_exd with d; assumption.
unfold isWellembedv, expv in w; apply sym_equal; rewrite <- fp.
apply (w d _ x pp).
Qed.

Lemma insert_in_d :
  forall l p1 p2, In p1  (p2::l) -> In p1 (insert p2 l).
intros l p1 p2; induction l.
 simpl; intro H; exact H.
simpl; intros [H1 | [H2 | H3]].
  case (p_dec p2 a).
   intros; subst; subst; left; reflexivity.
  intros _; case (lex_dec p2 a); intros _.
   subst; simpl; left; reflexivity.
  simpl; right; apply IHl; simpl; left; assumption.
 subst; case (p_dec p2 p1).
  left; reflexivity.
 case (lex_dec p2 p1); intros _ _.
  right; left; reflexivity.
 left; reflexivity.
case (p_dec p2 a).
 intros _; right; assumption.
case (lex_dec p2 a); intros _ _.
 right; right; assumption.
simpl; right; apply IHl; right; assumption.
Qed.

Lemma insert_in_it :
  forall l p, In p (insert p l).
intros l p; induction l.
 simpl; solve[auto].
simpl; case (p_dec p a).
 intros q; subst; left; reflexivity.
case (lex_dec p a); intros _ _.
 simpl; left; reflexivity.
simpl; right; assumption.
Qed.

Lemma in_insert :
  forall p1 p2 l, In p1 (insert p2 l) -> p2 = p1 \/ In p1 l.
intros p1 p2 l; induction l.
 intros H; exact H.
simpl; case (p_dec p2 a).
 intros p2a [ ap1 | il]; subst; tauto.
intros p2na; case (lex_dec p2 a); simpl; tauto.
Qed.

Lemma sort_in :
  forall l p, In p l -> In p (sort l).
intros l p; induction l.
 intros H; exact H.
simpl; intros [q | i].
 subst; apply insert_in_it.
apply insert_in_d; simpl; right; solve[auto].
Qed.

Lemma in_sort :
  forall l p, In p (sort l) -> In p l.
intros l p; induction l.
 intros H; exact H.
simpl; intros H; apply in_insert in H; destruct H as [H | H]; tauto.
Qed.

(* A very long combinatorial proof.  could be automated? *)
Lemma insert_commute :
  forall p1 p2 l, insert p1 (insert p2 l) = insert p2 (insert p1 l).
intros p1 p2 l; induction l.
simpl; case (p_dec p1 p2); case (p_dec p2 p1); intros.
    subst p2; tauto.
   case n; subst; reflexivity.
  case n; subst; reflexivity.
 case (lex_dec p1 p2); intros p1p2; case (lex_dec p2 p1); intros p2p1.
    case n; apply lex_antisym; assumption.
   reflexivity.
  reflexivity.
 case n; apply lex_antisym; apply lex_total; assumption.
simpl; case (p_dec p2 a); intros p2a.
 simpl; case (p_dec p1 a); intros p1a.
  simpl; case (p_dec p2 a); [reflexivity | intros n; case n; assumption].
 case (lex_dec p1 a); intros lp1a.
  simpl; case (p_dec p2 p1); intros p2p1.
   reflexivity.
  case (lex_dec p2 p1); intros lp2p1.
   subst; case p2p1; apply lex_antisym; assumption.
  case (p_dec p2 a); [ intros _ | intros n; case n; assumption]; reflexivity.
 simpl; case (p_dec p2 a); [ intros _ | intros n; case n; assumption].
 reflexivity.
case (p_dec p1 a); intros p1a.  
 simpl; case (lex_dec p2 a); intros lp2a.
  simpl; case (p_dec p2 a); [intros abs; case p2a; assumption |intros _].
  case (p_dec p1 p2);[intros _; reflexivity | intros p1p2 ].
  case (lex_dec p1 p2); intros lp1p2.
   subst; case p1p2; apply lex_antisym; assumption.
  case (p_dec p1 a); [intros _ | intros n; case n; assumption]; reflexivity.
 case (p_dec p2 a);[ intros; case p2a; assumption | intros _; simpl].
 case (p_dec p1 a);[ intros _| intros n; case n; assumption]; reflexivity.
case (lex_dec p2 a); intros lp2a; simpl.
 case (p_dec p1 p2); intros p1p2; simpl.
  subst; case (lex_dec p2 a);[intros _ | intros n; case n; assumption].
  simpl; case (p_dec p2 p2);[ reflexivity | intros n; case n; reflexivity].
 case (lex_dec p1 p2); intros lp1p2; simpl.
  case (lex_dec p1 a); intros lp1a; simpl.
   case (p_dec p2 p1);
    [intros ab; case p1p2; apply sym_equal; assumption | intros _].
   case (lex_dec p2 p1);
    [intros lp2p1; case p1p2; apply lex_antisym; assumption | intros _].
   case (p_dec p2 a);[intros ab; case p2a; assumption | intros _].
   case (lex_dec p2 a);[ intros _; reflexivity | intros n; case n; assumption].
  case (p_dec p2 a);[intros ab; case p2a; assumption | intros _; simpl].
  case p2a; apply lex_antisym;[ assumption| ].
  apply lex_trans with p1;[apply lex_total | ]; assumption.
 case (p_dec p1 a);[intros ab;case p1a; assumption | intros _].
 case (lex_dec p1 a); intros lp1a; simpl.
 case (p_dec p2 p1);
   [intros ab; case p1p2; apply sym_equal; assumption | intros _].
  case (lex_dec p2 p1);[reflexivity | ].
  intros lp2p1; case p1p2; apply lex_antisym; apply lex_total; assumption.
 case (p_dec p2 a);[intros ab; case p2a; assumption | intros _].
 case (lex_dec p2 a);[reflexivity | intros ab; case ab; assumption].
case (p_dec p1 a);[intros ab; case p1a; assumption | intros _].
case (lex_dec p1 a);intros lp1a; simpl.
 case (p_dec p2 p1); intros p2p1;[subst; case lp2a; assumption| ].
 case (lex_dec p2 p1); intros lp2p1; simpl.
  case p2p1;apply lex_antisym;[assumption | apply (lex_trans _ _ _ lp1a)].
  apply lex_total; assumption.
 case (p_dec p2 a);[intros ab; case p2a; assumption | intros _].
 case (lex_dec p2 a); [intros ab; case lp2a; assumption | reflexivity].
case (p_dec p2 a);[intros ab; case p2a; assumption | intros _].
case (lex_dec p2 a);[intros ab; case lp2a; assumption | intros _].
rewrite IHl; reflexivity.
Qed.

Lemma insert_twice : forall l p, insert p (insert p l) = insert p l.
induction l; intros p; simpl.
 case (p_dec p p);[reflexivity | intros n; case n; reflexivity].
case (p_dec p a); simpl;[intros; subst | ].
 case (p_dec a a);[reflexivity | intros n; case n; reflexivity].
case (lex_dec p a); simpl.
 case (p_dec p p);[reflexivity | intros n; case n; reflexivity].
intros lpa pa; case (p_dec p a);[intros ab; case pa; assumption | intros _].
case (lex_dec p a);[intros ab; case lpa; assumption | intros _].
rewrite IHl; reflexivity.
Qed.

Lemma Chp_step : forall d p m, 
  insert (fpoint m d) (insert p (sort (points_of_fmap (Chp m d p)))) =
  insert (fpoint m d) (insert p (sort (points_of_fmap m))).
intros d p; induction m;[reflexivity | | exact IHm].
simpl sort; simpl fpoint; simpl Chp.
case (eq_dart_dec d0 d); intros d0d.
 simpl sort; rewrite (insert_commute p p0), !insert_twice; reflexivity.
simpl sort; rewrite !(insert_commute p p0), !(insert_commute (fpoint m d) p0).
rewrite IHm; reflexivity.
Qed.

Lemma insert_already :
  forall d p m, exd m d -> fpoint m d = p ->
    insert p (sort (points_of_fmap m)) = sort (points_of_fmap m).
intros d p m; revert d p.
induction m as [ | m IHm d0 t p0 | m IHm k da da']; intros d p.
  intros H; solve[case H].
 simpl; intros [d0d | inm].
 case (eq_dart_dec d0 d);[ intros _ | intros ab; case ab; assumption].
 intros p0p; subst p0; rewrite insert_twice; reflexivity.
 case (eq_dart_dec d0 d); intros d0d.
 intros p0p; subst p0; rewrite insert_twice; reflexivity.
 intros pmdp; rewrite insert_commute. 
 rewrite IHm with d p; try assumption; reflexivity.
simpl; apply IHm.
Qed.

Lemma Chp_diff : forall m p d1 d2, exd m d1 -> d1 <> d2 ->
              sort (points_of_fmap (Chp m d2 p)) =
              insert (fpoint m d1) (sort (points_of_fmap (Chp m d2 p))).
induction m as [ | m IHm d t p0 | m IHm k da da' ]; intros p d1 d2 exd1 d1nd2.
  case exd1.
 simpl; destruct (eq_dart_dec d d2) as [dd2 | dnd2].
 simpl in exd1 |- *; destruct exd1 as [dd1 | exd1]; 
  [case d1nd2; rewrite <- dd2; apply sym_equal; assumption | ].
 destruct (eq_dart_dec d d1) as [dd1 | dnd1].
  case d1nd2; rewrite <- dd2; apply sym_equal; assumption.
  rewrite <- (insert_already d1 (fpoint m d1) m), insert_commute, insert_twice.
    reflexivity.
   assumption.
  reflexivity.
 simpl in exd1 |- *; destruct exd1 as [dd1 | exd1].
  destruct (eq_dart_dec d d1) as [_ | dnd1]; [ | case dnd1; assumption].
  rewrite insert_twice; reflexivity.
 destruct (eq_dart_dec d d1) as [dd1 | dnd1].
  rewrite insert_twice; reflexivity.
 rewrite insert_commute, <- IHm; solve[auto].
simpl in exd1 |- *; apply IHm; assumption.
Qed.

Lemma Chp_preserves_points :
  forall m d d' d1 p, exd m d -> exd m d' -> exd m d1 -> fpoint m d' = p ->
    fpoint m d1 = fpoint m d -> d1 <> d -> fpoint m d <> p ->
    sort (points_of_fmap (Chp m d p)) = insert p (sort (points_of_fmap m)).
induction m as [ | m IHm d0 t p0 | m IHm k da da'];
 intros d d' d1 p ind ind' ind1 dp dd1 dnd1 pdnp.
  solve [case ind].
 assert (dnd' : d <> d').
  intros dd'; rewrite <- dd' in dp; rewrite dp in pdnp; case pdnp; reflexivity.
 revert pdnp dd1; simpl Chp; simpl fpoint;
  case (eq_dart_dec d0 d); intros d0d pdnp dd1;
  [destruct (eq_dart_dec d0 d1) as [d0d1 | _];
    [case dnd1; rewrite <- d0d1;assumption|] | ].
  simpl.
  rewrite (insert_already d1 p0); try reflexivity.
   simpl in ind1; destruct ind1 as [ab | ind1].
    rewrite <- ab in dnd1; case dnd1; assumption.
   assumption.
  simpl in dd1.
  destruct (eq_dart_dec d0 d1) as [dd1' | _].
  rewrite <- dd1' in dnd1; case dnd1; assumption.
  destruct (eq_dart_dec d0 d) as [_ | d0nd]; [ | case d0nd]; assumption.
 simpl.
 simpl in dp; destruct (eq_dart_dec d0 d') as [d0d' | d0nd'].
  destruct (eq_dart_dec d0 d1) as [d0d1 | d0nd1];
   [case pdnp; rewrite <- dp; apply sym_equal; assumption | ].
  simpl in ind, ind1; destruct ind as [ab | ind];[case d0d; exact ab | ].
  destruct ind1 as [ab | ind1];[case d0nd1; exact ab | ].
  rewrite (Chp_diff m p d1 d ind1 dnd1), dd1.
  rewrite dp, insert_twice, insert_commute, Chp_step, insert_commute.
  rewrite <- dd1, (insert_already d1 (fpoint m d1) m);solve[auto].
 assert (exd m d) by (destruct ind;[case d0d | ]; assumption).
 destruct (eq_dart_dec d0 d1) as [d0d1| d0nd1].
  rewrite dd1, <- (insert_already d p (Chp m d p)), Chp_step, insert_commute.
    reflexivity.
   rewrite exd_Chp; assumption.
  rewrite fpoint_Chp.
   destruct (eq_dart_dec d d) as [ _ | ab];[ | case ab]; reflexivity.
  assumption.
 assert (exd m d') by (destruct ind';[case d0nd' | ]; assumption).
 assert (exd m d1) by (destruct ind1;[case d0nd1 | ]; assumption).
 rewrite (insert_commute p), IHm with (d1 := d1) (d' := d');
   assumption || reflexivity.
simpl in ind, ind', ind1 |- *; apply IHm with (d1 := d1) (d' := d'); assumption.
Qed.

Lemma cA_1_is_cA :
  forall m d, inv_hmap m -> isMap m -> exd m d -> cA_1 m zero d = cA m zero d.
intros m d h M ind; assert (t := M _ ind).
rewrite (degreee_invol_nofixpt _ _ h ind) in t; destruct t as [t1 t2].
pattern d at 1; rewrite <- t2; rewrite cA_1_cA; trivial.
rewrite <- exd_cA; trivial.
Qed.

Lemma tri_face_2_diff :
  forall m d, inv_Triangulation m -> isWellembed m -> exd m d ->
  fpoint m d <> fpoint m (cF m (cF m d)).
intros m d [h [M [p T]]] [_ [we [wv wf]]] ind; assert (T' := T _ ind).
assert (tmp := MF0Tr.MfM.degree_lub m d h ind).
revert tmp; fold degreef; unfold isTri in T'; rewrite T'; intros [_ [tmp _]].
unfold MF0Tr.MfM.f, McF.f in tmp; simpl in tmp.
pattern d at 1; rewrite <- tmp.
assert (ind2 : exd m (cF m (cF m d))) by (rewrite<- !exd_cF; assumption).
assert (ind3 : exd m (cA_1 m zero (cF m (cF m d))))
  by (rewrite <- exd_cA_1; assumption).
unfold cF at 1; 
 rewrite <- (wv (cA_1 m zero (cF m (cF m d)))
                (cA_1 m one (cA_1 m zero (cF m (cF m d))))); try assumption.
 pattern (cF m (cF m d)) at 2; rewrite <- (cA_cA_1 m zero); try assumption.
 apply we; rewrite <-exd_cA_1, <- !exd_cF; assumption.
apply expv_symm; try assumption; fold expv.
pattern (cA_1 m zero (cF m (cF m d))) at 2; rewrite <- (cA_cA_1 m one); trivial.
apply cA_expv; rewrite <- exd_cA_1; try assumption.
Qed.

Lemma Flip_preserves_points :
  forall m, inv_Triangulation m -> isWellembed m ->
    forall d, prec_Flip m d -> sort (points_of_fmap (Flip m d)) =
     sort (points_of_fmap m).
intros m iT w d [ind [_ [_ [H1 H2]]]]; unfold Flip, Flip_emb.
assert (iT' := iT); destruct iT' as [h [M [p tr]]].
assert (iW := w); destruct w as [_ [we [w' wf]]].
assert (exd1 : exists d1, d <> d1 /\ exd m d1 /\ fpoint m d1 = fpoint m d)
  by (apply isWellembedv_deg_dup; assumption || reflexivity).
destruct exd1 as [d1 [dd1 [ind1 pp]]].
pose (de := cA m zero d); fold de.
assert (exde: exd m de) by (unfold de; rewrite <- exd_cA; assumption).
assert (exd2 : exists d2, cA m zero d <> d2 /\ exd m d2 /\
               fpoint m d2 = fpoint m de)
  by (apply isWellembedv_deg_dup; assumption || reflexivity).
destruct exd2 as [d2 [ed2 [ind2 pp2]]].
assert (dnd2 : d <> d2)
  by (intros dd2; apply (we d);[|fold de; rewrite <- pp2, dd2]; trivial).
pose (dp := cA_1 m one d); fold dp.
assert (indp : exd m dp) by (unfold dp; rewrite <- exd_cA_1; trivial).
assert (dncf : d <> cF m dp).
 unfold cF; intros dcf.
 apply (we dp);[unfold dp; rewrite <- exd_cA_1; assumption | red in w'].
 assert (t:= cA_1_is_cA _ dp h M indp).
 rewrite <- (cA_cA_1 m one (cA m zero dp)), <- t, <- dcf; try assumption.
  apply w';[assumption | ].
  apply expv_trans with d; fold expv;[unfold dp | apply cA_expv; assumption].
  pattern d at 2; rewrite <- (cA_cA_1 m one d); try assumption.
  apply cA_expv; assumption.
 rewrite <- exd_cA; assumption.
assert (fde : cA_1 m one de = cF m d)
  by (unfold de; rewrite <- cA_1_is_cA; trivial).
rewrite fde.
assert (inde : exd m de) by (unfold de; rewrite <- exd_cA; trivial).
assert (infd : exd (Flip_topo m d) d) by (rewrite <- exd_Flip_topo; trivial).
rewrite Chp_preserves_points with (d' := (cF m dp)) (d1 := d2).
       rewrite <- Chp_diff.
         rewrite Chp_preserves_points with (d' := cF m (cF m d)) (d1 := d1).
                rewrite insert_already with (d:= cF m (cF m d)).
                  rewrite Flip_topo_preserves_points; reflexivity.
                 rewrite <- exd_Flip_topo, <- !exd_cF; assumption.
                reflexivity.
               assumption.
              rewrite <- exd_Flip_topo, <- !exd_cF; assumption.
             rewrite <- exd_Flip_topo; assumption.
            reflexivity.
           rewrite !Flip_topo_preserves_fpoint; assumption.
          solve[auto].
         rewrite !Flip_topo_preserves_fpoint; apply tri_face_2_diff;
          reflexivity || assumption.
        rewrite <- exd_Flip_topo, <- exd_cF; assumption.
       solve[auto].
      rewrite exd_Chp, <- exd_Flip_topo; assumption.
     rewrite exd_Chp, <- exd_Flip_topo, <- exd_cF; assumption.
    rewrite exd_Chp, <- exd_Flip_topo; assumption.
   rewrite fpoint_Chp.
    case (eq_dart_dec d (cF m dp)); intros dcf; 
     [case dncf; exact dcf | reflexivity].
   assumption.
  rewrite fpoint_Chp.
   case (eq_dart_dec d d2); intros dd2;[case dnd2; exact dd2 | ].
   rewrite fpoint_Chp.
    case (eq_dart_dec d de); intros dca.
     assert (t'' := M _ ind).
     rewrite (degreee_invol_nofixpt _ _ h ind) in t''; destruct t'' as [t'' _].
     case t''; solve[auto].
    rewrite !Flip_topo_preserves_fpoint; assumption.
   assumption.
  assumption.
 solve[auto].
rewrite fpoint_Chp.
 assert (t'' := M _ ind).
 rewrite (degreee_invol_nofixpt _ _ h ind) in t''; destruct t'' as [t'' _].
 case (eq_dart_dec d de);[intros test;case t'';solve[auto] | intros _].
 rewrite !Flip_topo_preserves_fpoint.
 unfold dp; rewrite <- (cA_1_cA m zero d); fold de; try assumption.
 fold (cF m de); apply tri_face_2_diff; assumption.
assumption.
Qed.

(*================================================================
                           Finite sets
=================================================================*)

(* Inductive definition of finite set:
L'ORDRE DANS fs_enum EST-IL IMPORTANT ?? *)

Record fset (A:Type) := mkfs {prd :> A -> Prop; fs_enum : list A;
   _ : forall x, prd x -> In x fs_enum}.

Arguments prd : default implicits.
Arguments fs_enum : default implicits.

(* Each element of a finite set is in the correspondent list: *)

Lemma enum_p : forall A (fs : fset A) x, fs x -> In x (fs_enum fs).
intros A [p e i] q; apply i; assumption.
Qed.

(*==================================================================
               Operations on lists and finite sets
                     cartesien product, disjoint sum
====================================================================*)

Section cartesian_product.

(* A and B are 2 finite sets: *)
Variables (T1 T2 : Type) (A : fset T1) (B : fset T2).

(* Predicate on T1*T2: *)
Definition prod_prd (p: T1*T2) : Prop :=
  let (x,y) := p in prd A x /\ prd B y.

(* Product of 2 lists: *)
Fixpoint prod_list (l1 : list T1) (l2:list T2) : list (T1*T2) :=
  match l1 with
   nil => nil
  | a::l1 => map (fun b => (a,b)) l2++prod_list l1 l2
  end.

(* OK: *)
Lemma prod_list_enum :
  forall x, prod_prd x -> In x (prod_list (fs_enum A) (fs_enum B)).
assert (rec : 
  forall l1 l2 a b, In a l1 -> In b l2 -> In (a,b) (prod_list l1 l2)).
 induction l1 as [ | a' l1 Hl1].
  intros l2 a b abs; case abs.
  simpl; intros l2 a b [aa' | ia].
  intros ib; subst a'; unfold prod_list; apply in_or_app; fold prod_list.
  left; generalize b ib; clear b ib; induction l2 as [ | b' l2 Hl2].
   intros b abs; case abs.
  simpl; intros b [bb' | ib].
   subst b'; solve[auto].
  solve[auto].
 intros ib; apply in_or_app; right; solve[auto].
intros [a b]; simpl; intros pab; apply rec.
 apply enum_p; intuition.
apply enum_p; intuition.
Qed.

(* Constructor of a produit of finite sets: *)
Definition prod_fs := 
 mkfs (T1*T2) prod_prd (prod_list (fs_enum A) (fs_enum B)) prod_list_enum.

End cartesian_product.

Section sum.

(* Disjoint sum of 2 finite sets: *)

Variables (T1 T2 :Type)(A : fset T1)(B:fset T2).

Definition sum_prd (x:T1+T2) :=
  match x with inl x' => A x' | inr y' => B y' end.

Lemma sum_enum :
  forall x, sum_prd x -> In x (map (@inl T1 T2) (fs_enum A)++
                                  map (@inr T1 T2) (fs_enum B)).
intros [x' | y']; simpl; intros p.
 apply in_or_app; left; apply in_map; apply enum_p; assumption.
apply in_or_app; right; apply in_map; apply enum_p; assumption.
Qed.

(* Constructor of sum: *)
Definition sum_fs :=
  mkfs (T1+T2) sum_prd
    (map (@inl T1 T2) (fs_enum A)++map (@inr T1 T2) (fs_enum B))
    sum_enum.

End sum.

(*======================================================================
                Generation of the finite sets of lists
            of length n the elements of which satisfy a predicate
                      (for sets of lists representing hypermaps)
======================================================================*)

Section fixed_length. 
 (* Lists of fixed length n and the elements of which 
satisfy a predicate prd (they have duplicata) *) 

Variable (T : Type) (A : fset T).

(* Duplications of l' by adding to each
one element of l only at each step
(each list of l' has only a element of l more) *)

Fixpoint add_elems (l : list T) (l':list (list T)) : list (list T) :=
  match l with
    a::tl => map (cons a) l'++add_elems tl l'
   | nil => nil
  end.

(* Consequence: *)

Lemma in_add_elems :
  forall l l' x y, In x l -> In y l' -> In (x::y) (add_elems l l').
Proof.
induction l as [|a l Hl].
 intros l' x y abs; case abs.
simpl; intros l' x y [xa | xl].
 subst x.
 intros iy; apply in_or_app; left.
 generalize y iy; clear y iy; induction l' as [ | b l' Hl'].
  intros y abs; case abs.
 simpl; intros y [yb | yl'].
  subst y; left; solve[auto].
 right; solve[auto].
intros iy; apply in_or_app; right; solve[auto].
Qed.

(* n = length l and each element of l satisfies (prd A): *)

Definition fl_prd (n:nat) (l: list T) :=
  length l = n /\  foralll (prd A) l.

(* List of all the lists satisfying fl_prd: *)

Fixpoint fl_list (n:nat) : list (list T) :=
  match n with
    0 => nil::nil
  | S p => add_elems (fs_enum A) (fl_list p)
  end.

(* Property of finite sets: *)

Lemma fl_enum : forall n l, fl_prd n l -> In l (fl_list n).
Proof.
induction n as [ | n Hn].
 intros [ | a l]; simpl; [solve[auto] | ].
 unfold fl_prd; simpl; intros H; decompose [and] H; discriminate.
simpl.
intros [ | a l]; simpl.
 unfold fl_prd; simpl; intuition discriminate.
unfold fl_prd.
intros [ll all].
simpl in all; destruct all as [ aa all].
apply in_add_elems; [apply enum_p; assumption | apply Hn; split; auto].
Qed.

(* Finite set of all the lists satisfying fl_prd
( length n and all elements satisfy prd A, 
for the finite set A): *)

Definition fl_fs (n:nat) := mkfs _ (fl_prd n) (fl_list n) (fl_enum n).

(*
fl_fs : nat -> fset (list T)
*)

End fixed_length.

(* In  fact, (lists-)hypermaps have not the same length... *)

(*================================================================
                 Finite sets by injection
=================================================================*)

Section injection.

Variables (T1 T2 : Type) (f : T1 -> T2) (g : T2 -> T1).

Variable (B : fset T2) (pA : T1 -> Prop).

Hypothesis right_inverse : forall x, pA x -> g (f x) = x.

Hypothesis pA_B : forall x, pA x -> B (f x).

(* If x satisfies pA, it is in the list which corresponds to (g B): *)

Lemma inverse_enum : 
  forall x, pA x -> In x (map g (fs_enum B)).
Proof.
intros x Bx; assert (H' : In (f x) (fs_enum B)).
 apply enum_p; solve[auto].
generalize H'; clear H'; induction (fs_enum B) as [ | b l Hl].
 simpl; solve[auto].
simpl; intros [xb | xl].
 left; rewrite xb; rewrite right_inverse; solve[auto].
solve[auto].
Qed.

(* Finite set in T1 built from finite set B in T2
thanks to an injection from T1 to T2: *)

Definition inj_fs :=
   mkfs T1 pA (map g (fs_enum B)) inverse_enum.

(*
inj_fs
     : fset T1
*)

End injection.

(*================================================================
              Type unit viewed as a finite set
=================================================================*)

(* Type unit is seen as a finite set with only one element, tt: *)
Section unit_finite_set.

(*
Print unit.
Inductive unit : Set :=  tt : unit
*)

Lemma unit_enum : forall x:unit, True -> In x (tt::nil).
intros []; simpl; solve[auto].
Qed.

(* Construction of the finite set for unit: *)
Definition u_fs := mkfs unit (fun x:unit => True) (tt::nil) unit_enum.

End unit_finite_set.

(*================================================================
                            Bounded lists
=================================================================*)

Section bounded_length_list.

Variables (T : Type) (A : fset T).

(* n <= length l and each element of l satisfies (prd A): *)

Definition bl_prd (n:nat)(l:list T) :=
  length l <= n /\ foralll A l.

(* List of length n of elements of T+unit filled with tt only: *)

Fixpoint pad (n:nat) : list(sum T unit) :=
 match n with 0 => nil | S p => inr T tt::pad p end.

(* List l completed by tt until length n: *)

Definition bl_f n l :=
 map (@inl T unit) l++pad (n - length l).

(* Inverse: *)

Fixpoint bl_inv (l:list(T+unit)) : list T :=
 match l with
 | nil => nil 
 | inl x::tl => x::bl_inv tl
 | inr _::tl => nil
 end.

(* Proof of inversion: *)

Lemma bl_inv_p : forall n l, bl_inv (bl_f n l) = l.
Proof.
unfold bl_f; intros n l; generalize n; induction l; clear n.
 intros n; case n; simpl; solve[auto].
simpl.
intros n; apply f_equal.
case n.
 replace (0 - S(length l)) with (length l - length l).
  solve[auto].
 rewrite Nat.sub_diag; solve[auto].
auto.
Qed.

(* Idem: *)

Lemma bl_inv_p' : forall n l, bl_prd n l -> bl_inv (bl_f n l) = l.
intros n l _; apply bl_inv_p.
Qed.
 
(* OK: *)

Lemma length_pad : forall n, length (pad n) = n.
induction n; simpl; auto.
Qed.

(* OK: *)

Lemma bl_length : forall n l, length l <= n  -> length (bl_f n l) = n.
Proof.
intros n l le; unfold bl_f.
rewrite length_app, length_map, length_pad.
rewrite Nat.add_sub_assoc.
rewrite Nat.add_sub_swap.
lia.
solve[auto].
solve[auto].
Qed.

(* Construction of the finite set of all the lists satisfying bl_prd
(length bounded by n and all elements satisfy prd A): *)

Lemma bl_length' :
  forall n x, bl_prd n x ->
  fl_fs _ (sum_fs T unit A u_fs) n (bl_f n x).
Proof.
simpl; unfold bl_prd, fl_prd.
intros n l [le all].
assert (le' := le).
apply bl_length in le; rewrite le.
split; [ solve[auto] | ].
unfold bl_f; rewrite foralll_app.
generalize n le' all; elim l;[ | intros a l' Hl']; simpl; clear le n le' all.
 intros n _ _;  split; [ solve[auto] | ]; induction (n-0); simpl; solve[auto].
intros [ | n']; [ intro H'; inversion H' | ].
change (S n' - S (length l')) with (n' -length l'). 
intros le; apply le_S_n in le; simpl. 
intros [ha all]; split;[ split;[assumption | ] | ]; firstorder.
Qed.

(* Construction of the inverse finite set of all the lists satisfying bl_prd
(bounded by n and all the elements satisfy prd A, for the finite set A): *)

Definition bl_fs n : fset _ :=
  inj_fs (list T) (list (sum T unit)) (bl_f n) bl_inv
    (fl_fs (T+unit) (sum_fs T unit A u_fs) n)
      (bl_prd n) (bl_inv_p' n)(bl_length' n).

(*
 bl_fs
     : nat -> fset (list T)
*)

End bounded_length_list.

(*================================================================
                  Lists without duplication
=================================================================*)

(* QUESTION: IS THERE A RISK OF DUPLICATION ? *)

Section list_without_duplication.

Variables (T : Type) (teq : forall x y:T, {x=y}+{x<>y}).
 
(* x is not in l *)

Fixpoint notin x l :=
  match l with
    a::tl => if teq x a then false else notin x tl
  | nil => true
  end.

(* l contains no duplicata *)

Fixpoint no_dup l :=
  match l with x::tl => notin x tl && no_dup tl | nil => true end.

Variable A : fset T.

(* This lemma should be given in the library. *)

Lemma remove_length_le :
  forall x l, length (remove teq x l) <= length l.
Proof.
intros x l; induction l; simpl; auto.
case (teq x a); [solve[auto] | ].
intros _; simpl; apply le_n_S; auto.
Qed.

(* OK: *)

Lemma remove_length_lt :
  forall x l, In x l -> length (remove teq x l) < length l.
Proof.
intros x l; induction l; simpl.
 contradiction.
 intros [ax | intl].
 case (teq x a).
  intros _; apply le_n_S; apply remove_length_le.
 intros abs; case abs; solve[auto].
case (teq x a).
 intros _; apply le_n_S; apply remove_length_le.
intros _; simpl; apply -> PeanoNat.Nat.succ_lt_mono; auto.
Qed.

(* Equality in bool: *)

Definition teqb x y := if teq x y then true else false.

(* RECALL:
teqb
     : T -> T -> bool
*)

(* OK: *)

Lemma remove_preserved :
  forall x y l, x <> y -> In y l -> In y (remove teq x l).
Proof.
intros x y l diff; induction l.
 intros abs; case abs.
simpl; intros [ay | yl].
 case (teq x a).
  intros xa; case diff; subst; solve[auto].
 simpl; intros _; left; solve[auto].
case (teq x a); simpl;solve[auto].
Qed.

(* OK: *)

Lemma notin_all_remove : forall p x l l', 
  notin x l = true -> foralll p l ->
  (forall y, p y -> In y l') ->
    foralll (fun y => p y /\ In y (remove teq x l')) l.
Proof.
intros p x l; induction l; intros l'.
 simpl; solve[auto].
simpl; intros nt all.
destruct (teq x a);[discriminate |].
destruct all as [pa all'].
intros en_p.
split.
split; [ | apply remove_preserved]; solve[auto].
apply IHl; solve[auto].
Qed.

(* OK: *)

Lemma length_no_dup :
  forall l, no_dup l = true ->
   foralll A l -> length l <= length (fs_enum A).
Proof.
pose (n := length (fs_enum A)).
assert (n' : length (fs_enum A) <= n) by auto; generalize n A n'; clear n n' A.
induction n.
 intros A l0.
 assert (q : length (fs_enum A) = 0) by auto with arith.
 rewrite q; intros [ | x l]; [solve[auto] | ].
 simpl; intros _ [q' _]; apply enum_p in q'.
 destruct (fs_enum A); [case q' | discriminate q].
intros A le [ | x l] nd all; simpl; [simpl; solve [apply le_0_n] | ].
simpl in nd.
assert (nd' : notin x l = true /\ no_dup l = true).
 case_eq (notin x l); case_eq (no_dup l); auto;
 intros q q'; rewrite q, q' in nd; discriminate nd.
destruct nd' as [nd1 nd2]; clear nd.
assert (le' : length (remove teq x (fs_enum A)) < length (fs_enum A)).
 apply remove_length_lt; apply enum_p.
 destruct all; solve[auto].

apply Nat.le_trans with (2:= le').
apply le_n_S.
assert (len : length (remove teq x (fs_enum A)) <= n).
 apply le_S_n; apply Nat.le_trans with (2:= le); exact le'.
assert (en_p :
  forall y, A y /\ In y (remove teq x (fs_enum A)) ->
    In y (remove teq x (fs_enum A))).
 firstorder.
apply IHn with 
 (A := mkfs _ (fun y => A y /\ In y (remove teq x (fs_enum A))) (remove teq x (fs_enum A))
              en_p);[exact len | exact nd2 | ].
simpl; clear le' len en_p.
simpl in all; destruct all as [ax all'].
apply notin_all_remove;[assumption| assumption | apply enum_p].
Qed.

(* No duplicata in l and each element of l satisfies prd: *)

Definition no_dup_prd l :=
  no_dup l = true /\ foralll (prd A) l.

Lemma no_dup_to_bl_prd :
  forall x, no_dup_prd x ->
  bl_fs _ A (length (fs_enum A)) x.
Proof.
intros l; unfold no_dup_prd, bl_fs, inj_fs, bl_prd; simpl.
repeat rewrite <-(andb_comm (forallb A l)).
intros [nd all]; split;[ | solve[auto]].
apply length_no_dup; auto.
Qed.

(* Finite set of the lists which are inverse by bl_inv
of the finite set of lists satisfying bl_f: 
lists without duplicata ??: *)

Definition no_dup_fs : fset (list T) :=
  inj_fs _ _ (fun x => x) (fun x => x)
    (bl_fs _ A (length (fs_enum A)))
    no_dup_prd (fun x _  => refl_equal x)
     no_dup_to_bl_prd.

(* 
no_dup_fs
     : fset (list T)
*)

End list_without_duplication.

(*================================================================
                Representation of a map by a list and inverse
=================================================================*)

Section fmap_list. 

Fixpoint fmap_to_list (f:fmap): list (dart*tag*point + dim*dart*dart) :=
  match f with
      V => nil
   |  I  f' d t p => inl _ (d,t,p) :: fmap_to_list f' 
   |  L f' dm d1 d2 => inr _ (dm,d1,d2)::fmap_to_list f'
  end.

Fixpoint list_to_fmap (l:list(dart*tag*point+dim*dart*dart)) : fmap :=
  match l with
    nil => V
  | inl (d,t,p)::l' => I (list_to_fmap l') d t p
  | inr (dm, d1, d2)::l' => L (list_to_fmap l') dm d1 d2
  end.

End fmap_list.

(*================================================================
                        Dimensions as finite sets
================================================================*)

Section dim.

(* dim viewed as a finite set: *)

Lemma dim_enum : forall x, True -> In x (zero::one::nil).
intros [ | ]; simpl; auto.
Qed.

Definition dims := mkfs _ (fun x => True) (zero::one::nil) dim_enum.

End dim.

(*================================================================
                          Generation of a finite set of lists
                              representing hypermaps
  ================================================================*)

Section fmaps_are_finite.

Variables (dartsl : list dart)(tagsl : list tag)(pointsl : list point).

Let darts :fset dart := 
  mkfs dart (fun x => In x dartsl) dartsl (fun x h => h).

Let tags : fset tag :=
  mkfs tag (fun x => In x tagsl) tagsl (fun x h => h).

Let points : fset point :=
  mkfs point (fun x => In x pointsl) pointsl (fun x h => h).

Hypotheses nil_not_darts : ~darts (Del01.nil).
  
(* OK:  *)

Lemma fmap_to_list_inj :
  forall f, list_to_fmap (fmap_to_list f) = f.
induction f as [ | f IHf d | f IHf d1 d2 d3]; simpl; try (rewrite IHf); auto.
Qed.

(* The darts, darts, points of f are in the finite set A : *)  (* USEFUL *)

Fixpoint darts_in_fs (f:fmap)(A:fset dart) : Prop :=
  match f with
    V => True
  |  I f' d t p => A d /\ darts_in_fs f' A
  |  L f' dm d1 d2 => darts_in_fs f' A
  end.

Fixpoint tags_in_fs (f:fmap)(A:fset tag) : Prop :=
  match f with
    V => True
  |  I f' d t p => A t /\ tags_in_fs f' A
  |  L f' dm d1 d2 => tags_in_fs f' A
  end.

Fixpoint points_in_fs (f:fmap)(A:fset point) : Prop :=
  match f with
    V => True
  |  I f' d t p => A p /\ points_in_fs f' A
  |  L f' dm d1 d2 => points_in_fs f' A
  end.

(* OK: *)

Lemma darts_in_fs_exd :
  forall A f, darts_in_fs f A -> forall x, exd f x -> A x.
Proof.
intros A f; induction f.
  simpl; intros _ x abs; case abs.
 simpl; intros [id b].
 intros x [xd | exx]; [subst x; solve[auto] | firstorder ].
simpl; solve[auto].
Qed.

Lemma tags_in_fs_exd :
  forall A f, tags_in_fs f A -> forall x, exd f x -> A (ftag f x).
Proof.
intros A f; induction f.
  simpl; intros _ x abs; case abs.
 simpl; intros [id b].
 intros x [xd | exx].
 elim (eq_dart_dec d x). tauto. tauto. 
  elim (eq_dart_dec d x). tauto. 
   solve[auto].
simpl; solve[auto].
Qed.

Lemma points_in_fs_exd :
  forall A f, points_in_fs f A -> forall x, exd f x -> A (fpoint f x).
Proof.
intros A f; induction f.
  simpl; intros _ x abs; case abs.
 simpl; intros [id b].
 intros x [xd | exx].
 elim (eq_dart_dec d x). tauto. tauto. 
  elim (eq_dart_dec d x). tauto. 
   solve[auto].
simpl; solve[auto].
Qed.

(* e_fs := darts * tags * points + dims * darts * darts :  *)

Definition e_fs := sum_fs _ _  (prod_fs _ _ (prod_fs _ _ darts tags) points)
   (prod_fs _ _ (prod_fs _ _ dims darts) darts).

(*OK: *)

Definition eeq : forall x y:dart*tag*point+dim*dart*dart, {x=y}+{x<>y}.
Proof.
intros [[[d1 t1] (x1,y1)] | [[k d1] d2]] [[[d'1 t'1] (x'1,y'1)] | [[k' d'1] d'2]].
  case (eq_dart_dec d1 d'1); 
     case (eq_tag_dec t1 t'1);  
        case (Req_dec_1 x1 x'1); 
           case (Req_dec_1 y1 y'1).
     left. rewrite e; rewrite e0; rewrite e1; rewrite e2. tauto. 
        intros. right. rewrite e; rewrite e0; rewrite e1. 
             injection. tauto. 
        intros. right. rewrite e; rewrite e0; rewrite e1. 
             injection. tauto.          
        intros. right. rewrite e; rewrite e0; 
             injection. tauto.   
        intros. right. rewrite e; rewrite e0; rewrite e1. 
             injection. tauto.   
        intros. right. rewrite e; rewrite e0; 
             injection. tauto.   
        intros. right. rewrite e; rewrite e0; 
             injection. tauto.   
        intros. right. rewrite e. 
             injection. tauto.   
        intros. right. rewrite e; rewrite e0; rewrite e1. 
             injection. tauto. 
        intros. right. rewrite e; rewrite e0; 
             injection. tauto.   
        intros. right. rewrite e; rewrite e0; 
             injection. tauto.   
        intros. right. rewrite e. 
             injection. tauto.   
        intros. right. rewrite e; rewrite e0; 
             injection. tauto.   
        intros. right. rewrite e. 
             injection. tauto.   
        intros. right. rewrite e. 
             injection. tauto.   
        intros.  right. 
             injection. tauto.   
 right; discriminate.
 right; discriminate.
case (eq_dim_dec k k'); intros kq;
  [ | right; intros q; injection q; intros; case kq; assumption].
case (eq_dart_dec d1 d'1); intros d1q;
  [ | right; intros q; injection q; intros; case d1q; assumption].
case (eq_dart_dec d2 d'2); intros d2q;
  [ | right; intros q; injection q; intros; case d2q; assumption].
subst; left; auto.
Qed.

(* RECALL: forallb is forall in bool : 

forallb = 
fun (A : Type) (f : A -> bool) =>
fix forallb (l : list A) : bool :=
  match l with
  | nil => true
  | a :: l0 => f a && forallb l0
  end
     : forall A : Type, (A -> bool) -> list A -> bool
*)

(* forallb_step : property of  forallb : *)

Lemma forallb_step :
 forall A p (l : list A) a, forallb p (a::l) = p a && forallb p l.
Proof.
 simpl; auto.
Qed.

(* RECALL: notin expresses that an object does not 
belong to a list :

notin = 
fun (T : Type) (teq : forall x y : T, {x = y} + {x <> y}) =>
fix notin (x : T) (l : list T) {struct l} : bool :=
  match l with
  | nil => true
  | a :: tl => if teq x a then false else notin x tl
  end
     : forall T : Type,
       (forall x y : T, {x = y} + {x <> y}) -> T -> list T -> bool
*)

(* If dart x belongs to the list corresponding to a map,
it belongs to the map: *)

Lemma notin_false_exd :
  forall x t p f, notin _ eeq (inl _ (x,t,p)) (fmap_to_list f) = false -> exd f x.
Proof.
intros x t p f; induction f as [ | f IHf d | f IHf k d1 d2].
  simpl; intros; discriminate.
 simpl. case (eeq (inl _ (x,t,p)) (inl _ (d,t0,p0))).
  intros q. injection q. solve[auto].
 solve[auto].
simpl. case (eeq (inl _ (x,t,p)) (inr _ (k, d1, d2))).
 intros; discriminate.
solve[auto].
Qed.

(* If dart x is the origin of a k-sewing of the list 
corresponding to a map, it has a successor in the k-permutation: *)

Lemma notin_false_succ :
  forall k x y f,
   inv_hmap f ->
     notin _ eeq (inr _ (k, x, y)) (fmap_to_list f) = false ->
       succ f k x.
Proof.
intros k x y f; induction f as [ | f IHf d | f IHf k' d1 d2]; intros i_f.
  simpl; intros; discriminate.
 simpl. case (eeq (inr _ (k, x, y)) (inl _ (d,t,p))).
  intros; discriminate.
 solve[simpl in i_f; intuition].
simpl. case (eeq (inr _ (k, x, y)) (inr _ (k', d1, d2))).
  intros q; injection q; intros q1 q2 q3 _; unfold succ.
 simpl.
 case (eq_dim_dec k' k). 
  case (eq_dart_dec d1 x). 
   simpl in i_f. unfold prec_L in i_f. 
    intros. apply (exd_not_nil f). tauto. tauto. 
  solve[intuition].
 solve[intuition].
intros diff ni; apply IHf in ni; unfold succ; simpl.
 case (eq_dim_dec k' k); intros kk'.
  case (eq_dart_dec d1 x); intros xd1.
        simpl in i_f. unfold prec_L in i_f. 
          apply (exd_not_nil f). tauto. tauto. 
   simpl in i_f. unfold prec_L in i_f. 
       unfold succ in ni. tauto.
         unfold succ in ni. tauto. 
 simpl in i_f. tauto.
Qed.
  
(* When the darts of a (true...) hypermap are in darts,
there is no dart duplicata in the correspondent list: *)

Lemma fmap_to_list_e :
  forall f, darts_in_fs f darts -> tags_in_fs f tags -> points_in_fs f points ->
   inv_hmap f -> 
    no_dup_fs _ eeq e_fs (fmap_to_list f) .
Proof.
induction f as [ | f IHf d t p | f IHf k d1 d2].
  simpl; unfold no_dup_prd; solve[auto].
 simpl; unfold prec_I; intros [dd fd] [tt ft][pp fp] [i_f [dnn dnex]].
   unfold no_dup_prd; simpl no_dup. 
   assert (IHf' : no_dup_fs (dart * tag * point + dim * dart * dart) eeq e_fs
        (fmap_to_list f)) by tauto; clear IHf. 
simpl in IHf'; unfold no_dup_prd in IHf'; destruct IHf' as [IHf' IHf''].
rewrite IHf'.
  case_eq (notin _ eeq (inl _  (d, t, p)) (fmap_to_list f)); intros ni.
   split; [solve[auto] | simpl; auto ].
assert (tmp := notin_false_exd _ _ _ _ ni); case dnex; solve[auto].
simpl; intros df tf pf[invf [exd1 [exd2 [sd1 _]]]].
assert (IHf' := df); apply IHf in IHf';
  [simpl in IHf' | assumption | assumption | assumption].
destruct IHf' as [IHf'1 IHf'2].
unfold no_dup_prd; clear IHf.
simpl no_dup.
rewrite IHf'1.
simpl in IHf'2 |- *.
case_eq (notin _ eeq (inr _ (k, d1, d2)) (fmap_to_list f)).
 repeat split; [ | | solve[auto] ].
  apply (darts_in_fs_exd darts) with (2:= exd1); assumption.
 apply (darts_in_fs_exd darts) with (2:= exd2); assumption.
intros nif; case sd1; apply notin_false_succ with (y:=d2); auto.
Qed.

(* Predicate for a hypermap: darts are in darts,
  tags in tags, and points in points: *)

Definition fmap_prd (f:fmap) :=
  darts_in_fs f darts /\ tags_in_fs f tags /\ points_in_fs f points
   /\ inv_Triangulation f /\ isWellembed f.

(* When the darts of a hypermap are in darts,
there is no duplicata in the correspondent list: *) 

Lemma fmap_prd_e :
  forall f, fmap_prd f ->
    no_dup_fs _ eeq e_fs (fmap_to_list f).
Proof.
unfold fmap_prd; intros f [di [ti [pi iv]]].
unfold inv_Triangulation in iv. 
decompose [and] iv. 
unfold inv_hmap in H.
exact (fmap_to_list_e f di ti pi H1) .
Qed.

(* Injection to built the finite set of fmaps: *) 

Definition fmap_fs :=
 inj_fs _ _ fmap_to_list list_to_fmap 
   (no_dup_fs _ eeq e_fs) fmap_prd
     (fun x _ => fmap_to_list_inj x) fmap_prd_e.

End fmaps_are_finite.

(*================================================================  
              Direct concrete Delaunay algorithm
                (inspired by YB generic solution)
=================================================================*)

Section Delaunay_solution.

(*===========FINITE SETS of darts, tags, points===========*)

Lemma dart_proof: forall m x, exd m x -> In x (darts_of_fmap m).
Proof.
  induction m. simpl. tauto.
  simpl. intros. firstorder. 
  simpl. tauto.
Qed.

Definition fs_dart(m: fmap):=
     mkfs dart (exd m) (darts_of_fmap m)(dart_proof m). 

Lemma tag_proof: 
   forall m t, (exists x, exd m x /\ t = ftag m x) -> In t (tags_of_fmap m).
Proof.
  intros. 
  induction m. simpl. intros. elim H. tauto.
  simpl. simpl in H. elim H. intros. clear H. 
      generalize H0. elim (eq_dart_dec d x). intros. 
       left. symmetry. tauto. intros.
        right. apply IHm. split with x. tauto. 
       simpl. simpl in H. firstorder.
Qed.

Definition fs_tag(m: fmap):=
   mkfs tag (fun t:tag => exists x, exd m x /\ t = ftag m x) 
             (tags_of_fmap m)(tag_proof m). 

Lemma point_proof: 
   forall m p, (exists x, exd m x /\ p = fpoint m x) ->
     In p (sort (points_of_fmap m)).
Proof.
induction m; intros p' [x [inx q]]; apply sort_in.
  solve[case inx].
 simpl in inx, q |- *; destruct (eq_dart_dec d x).
  solve[auto].
 destruct inx; [case n;assumption | right; apply in_sort; apply IHm].
 exists x; solve[auto].
simpl; apply in_sort; firstorder.
Qed.

Definition fs_point(m: fmap):=
   mkfs point (fun p:point => exists x, exd m x /\ p = fpoint m x) 
             (sort (points_of_fmap m)) (point_proof m). 

(* ========================================

                 DEBUT INSERTION DE  TRIANG04.ComplYB.v 

=========================================*)

(*======================================
            Lemmas on expf and Flip
=======================================*)

Lemma expf_Flip_Flip_topo : forall m x z t,
   expf (Flip m x) z t <-> expf (Flip_topo m x) z t.
Proof. 
  unfold Flip. unfold Flip_emb. 
  intros. set (m':= Flip_topo m x). 
    set(p1:=(fpoint m'
       (cF m (cA_1 m one (cA m zero x))))). 
   set (p2:=  (fpoint m' (cF m (cA_1 m one x)))). 
   generalize (expf_Chp (Chp m' x p1) (cA m zero x) p2 z t). 
    generalize (expf_Chp m' x p1 z t). 
     tauto. 
Qed.
    
Lemma expf_Flip_xy: forall m x z,
  inv_Triangulation m -> prec_Flip m x -> exd m z ->
    let y := cA m zero x in let m' := Flip m x in
       expf m x z \/ expf m y z <-> expf m' x z \/ expf m' y z.
Proof.
  intros. 
  generalize (eqf_Flip_topo m x z H H0 H1). 
  simpl. fold y. 
  generalize (expf_Flip_Flip_topo m x x z). 
  generalize (expf_Flip_Flip_topo m x y z).  fold m'. 
  tauto. 
Qed.

(*==================================
                    Lemma YB on lists
==================================*)
      
Fixpoint no_dupl(l:list dart) :=
  match l with
    nil => True
  | x0 :: l0 => ~ In x0 l0 /\ no_dupl l0
  end.

Open Scope nat_scope.
Lemma remove_le :
 forall A (d:forall x y:A, {x=y}+{x<>y}) a l,
  length (remove d a l) <= length l.
intros A d a; induction l as [ | b l IH].
 simpl; solve[apply le_n].
simpl; case (d a b); simpl; intros _; auto with arith.
Qed.

Lemma remove_decrease :
 forall A (d:forall x y:A, {x=y}+{x<>y}) a l,
   In a l -> length (remove d a l) < length l.
intros A d a; induction l as [ | b l IH].
 intros; contradiction.
simpl; intros [ba | inal]; case (d a b); simpl.
   solve[assert (tmp:= remove_le A d a l); auto with arith].
  solve[intros abs; case abs; auto].
 solve[intros _; auto with arith].
solve[intros _; auto with arith].
Qed.

Lemma remove_In2 :
  forall A (d :forall x y:A, {x=y}+{x<>y}) a l x, In x (remove d a l) -> In x l.
intros A d a l x; induction l as [ | b l IH].
 simpl; contradiction.
simpl; destruct (d a b).
 solve[auto].
simpl; intros [bx | inx]; solve[auto].
Qed.

Lemma remove_In3 :
  forall A (d :forall x y:A, {x=y}+{x<>y}) a l x, 
  x <> a -> In x l -> In x (remove d a l).
intros A d a l x xna; induction l as [ | b l IH].
 simpl; contradiction.
simpl; destruct (d a b).
 intros [bx | inxl];[ | solve[auto]].
 case xna; transitivity b;solve[auto].
intros [bx | inx]; simpl; solve[auto].
Qed.

Lemma no_dupl_inj_length1 :
  forall (f :dart -> dart) l' l,
    (forall x y, In x l -> In y l -> f x = f y -> x = y) ->
    (forall x, In x l' -> exists y, In y l /\ x = f y) ->
    no_dupl l' ->
    length l' <= length l.
intros f l'; induction l' as [ | a l' IH]; intros l j s d.
 solve[apply le_0_n].
simpl; destruct (s a) as [y [iny fya]].
 simpl; tauto.
apply Nat.le_trans with (m := S (length (remove eq_dart_dec y l))).
 apply le_n_S; apply IH.
   intros x z inx inz; apply j; eapply remove_In2; solve[eauto].
 intros x inx; destruct (s x) as [y' [iny' fy'x]].
   simpl; solve[auto].
  exists y';split;[ | assumption].
  apply remove_In3.
   intros yy'; rewrite yy', <- fya in fy'x; rewrite fy'x in inx; simpl in d.
   tauto.
  assumption.
simpl in d; tauto.
apply remove_decrease; assumption.
Qed.

Lemma no_dupl_inj_length2 :
  forall (f :dart -> dart) l l',
    (forall x y, In x l -> In y l -> f x = f y -> x = y) ->
    (forall x, In x l -> In (f x) l') ->
    no_dupl l ->
    length l <= length l'.
intros f; induction l as [ | a l IH]; intros l' j c d.
 simpl; solve[apply le_0_n].
simpl; apply Nat.le_trans with (S (length (remove eq_dart_dec (f a) l'))).
 apply le_n_S; apply IH.
   solve[intros x y inx iny; apply j; simpl; auto].
  intros x inx; case (eq_dart_dec (f x) (f a)).
   intros abs; assert (xa:x = a) by (apply j; simpl; auto).
   rewrite <- xa in d; simpl in d; tauto.
  solve[intros dif; simpl in c; apply remove_In3; auto].
 simpl in d; tauto.
apply remove_decrease; simpl in c; auto.
Qed.

Lemma toto : forall (l:list dart) x1 x2 x3, 
  (x1 <> x2 /\ x2 <> x3 /\ x3 <> x1) ->
  (forall x, In x l <-> (x = x1 \/ x = x2 \/ x = x3)) ->
  no_dupl l ->
  length l = 3.
intros l x1 x2 x3 dif c nd; change 3 with (length (1::2::3::nil));
  apply Nat.le_antisymm.
 apply no_dupl_inj_length1 with
  (f := fun x => if eq_nat_dec x 1 then x1 else if eq_nat_dec x 2 then x2
                 else x3).
   intros x y; simpl; intros [x1' | [x2'| [x3' | []]]][y1 |[y2 |[y3 | []]]];
    subst x y; simpl eq_nat_dec; simpl; intros abs;
    assert (abs' := sym_equal abs); tauto.
  intros x inx; destruct (c x) as [xn _]; case (xn inx); clear xn.
   intros xx1; subst x; exists 1; simpl; tauto.
  intros [xx | xx]; subst x;
    (exists 2; simpl; tauto) || (exists 3; simpl; tauto).
 assumption.
apply no_dupl_inj_length2 with
  (f := fun x => if eq_nat_dec x 1 then x1 else if eq_nat_dec x 2 then x2
                 else x3).
   intros x y; simpl; intros [x1' | [x2'| [x3' | []]]][y1 |[y2 |[y3 | []]]];
    subst x y; simpl eq_nat_dec; simpl; intros abs;
    assert (abs' := sym_equal abs); tauto.
 intros x inx; assert (xx : x = 1 \/ x = 2 \/ x = 3).
  simpl in inx;
    solve[intuition
      (match goal with |- ?x = S ?y => apply sym_equal end; auto || auto)].
 simpl in inx;
   repeat (destruct inx as [ xx' | inx];
            [subst x; simpl;
             match goal with
               |- In ?a _ => destruct (c a) as [_ inx']; auto end  | ]).
 contradiction.
simpl; solve[intuition (discriminate || auto)].
Qed.
 
(* =============================
                            fmap_2_list
==============================*)

Fixpoint fmap_2_list(m:fmap) : list dart:=
   match m with
      V => nil
   |  I m0 x0 _ _ => x0 :: fmap_2_list m0
   |  L m0 _ _ _ => fmap_2_list m0
  end.

Lemma In_exd: forall m z,
   exd m z <-> In z (fmap_2_list m).
Proof.
  induction m. 
  simpl. tauto.
  simpl. intros. generalize (IHm z). tauto. 
  simpl. intros. generalize (IHm z). tauto. 
Qed.

Lemma fmap_2_list_B: forall m k x,
   fmap_2_list (B m k x) =  fmap_2_list m.
Proof.
  induction m. simpl. tauto. 
  simpl. intros. rewrite IHm. tauto. 
  intros. simpl. 
   elim (eq_dim_dec d k). simpl. 
     elim (eq_dart_dec d0 x). tauto. 
   simpl. intros. apply IHm. 
   simpl. intros. apply IHm. 
Qed.

Lemma fmap_2_list_Shift: forall m k x,
   fmap_2_list (Shift m k x) =  fmap_2_list m.
Proof.
  unfold Shift. intros. simpl. 
  apply fmap_2_list_B.
Qed.

Lemma fmap_2_list_Split: forall m k x y,
   fmap_2_list (Split m k x y) =  fmap_2_list m.
Proof.
  unfold Split. intros. 
   elim ( succ_dec m k x). 
    elim (succ_dec m k y). 
      rewrite fmap_2_list_B. simpl. 
        rewrite fmap_2_list_B. tauto.    
      rewrite fmap_2_list_B. tauto.    
     rewrite fmap_2_list_B. tauto.    
Qed.
  
Lemma fmap_2_list_G: forall m k x y,
   fmap_2_list (G m k x y) =  fmap_2_list m.
Proof.
   unfold G. intros. simpl. 
        elim ( succ_dec m k x). 
      rewrite fmap_2_list_Shift. tauto. 
   tauto.
Qed.   

Lemma fmap_2_list_Merge: forall m k x y,
   fmap_2_list (Merge m k x y) =  fmap_2_list m.
Proof.
  unfold Merge. 
  intros. 
   rewrite  fmap_2_list_G. 
    elim (pred_dec m k y). 
   rewrite  fmap_2_list_Shift. tauto. 
  tauto.
Qed.

Lemma fmap_2_list_Flip_topo: forall m x,
   fmap_2_list (Flip_topo m x) =  fmap_2_list m.
Proof.
  intros. unfold Flip_topo. 
    rewrite  fmap_2_list_Merge. 
    rewrite  fmap_2_list_Merge. 
    rewrite  fmap_2_list_Split. 
    rewrite  fmap_2_list_Split. tauto.
Qed.

Lemma fmap_2_list_Chp: forall m x p,
   fmap_2_list (Chp m x p) =  fmap_2_list m.
Proof.
  induction m. 
  simpl. tauto.
  intros. simpl. 
   elim (eq_dart_dec d x). simpl. tauto. 
   simpl. rewrite IHm. tauto. 
  intros. simpl. apply IHm.
Qed.

Lemma fmap_2_list_Flip_emb: forall m x y x' y',
   fmap_2_list (Flip_emb m x y x' y') =  fmap_2_list m.
Proof.
  intros. unfold Flip_emb. 
  rewrite fmap_2_list_Chp. 
  rewrite fmap_2_list_Chp. tauto.
Qed.

Lemma fmap_2_list_Flip: forall m x,
   fmap_2_list (Flip m x) =  fmap_2_list m.
Proof.
  unfold Flip. intros.
  rewrite fmap_2_list_Flip_emb.
  apply fmap_2_list_Flip_topo.
Qed.

(*================================
         Sumg : summation of a real function g
            on all the triangles of triangulation 
================================*)

Open Scope R_scope.

(* Sum of all the cylinder volumes (counted 3 times), 
apart from the external face: *)

Fixpoint Sumg_aux
  (l:list dart)(mr:fmap)(g:fmap->dart->R):R:=
  match l with
     nil => 0
  | x0::l0 =>  Sumg_aux l0 mr g +
        if expf_dec mr 1%nat x0 then 0 else g mr x0 
 end.

Definition Sumg m g := Sumg_aux (fmap_2_list m) m g.

(* Sum of all the prism volumes (counted 3 times) for the 
triangle of x before the Flip: *)

Fixpoint Sumg_in_aux
  (l:list dart)(mr:fmap)(x:dart)(g:fmap->dart->R):R:=
  match l with
     nil => 0
  |  x0::l0 =>  Sumg_in_aux l0 mr x g +
        if expf_dec mr 1%nat x0 then 0 
        else if expf_dec mr x x0 then g mr x0 
               else 0
  end.

Definition Sumg_in m x g := Sumg_in_aux (fmap_2_list m) m x g.

(* Sum of all the prism volumes (counted 3 times) for the 
other ccw triangles before the Flip: *)

Fixpoint Sumg_out_aux
  (l:list dart)(mr:fmap)(x:dart)(g:fmap->dart->R):R:=
  match l with
     nil => 0
  |  x0::l0 =>  Sumg_out_aux l0 mr x g +
        if expf_dec mr 1%nat x0 then 0 
        else if expf_dec mr x x0 then 0
               else if expf_dec mr (cA mr zero x) x0 then 0
                      else g mr x0
  end.

Definition Sumg_out m x g := Sumg_out_aux (fmap_2_list m) m x g.

(* OK: *)

Lemma Sumg_in_plus_out_aux: forall l m x g,
 ~ expf m x (cA m zero x) ->
   Sumg_in_aux l m x g +  
      Sumg_in_aux l m (cA m zero x) g + 
         Sumg_out_aux l m x g = Sumg_aux l m g.
Proof.
 induction l. 
 simpl. intros. ring. 
 intros. simpl. 
  elim ( expf_dec m 1%nat a). 
   intro. rewrite <-(IHl m x g). ring. tauto. 
 elim (expf_dec m x a). 
 elim (expf_dec m (cA m zero x) a). intros. 
   elim H. apply expf_trans with a. tauto. 
    apply expf_symm. tauto. intros. 
   rewrite <-(IHl m x g). ring. tauto. 
 elim (expf_dec m (cA m zero x) a). 
   intros. rewrite <-(IHl m x g). ring. tauto. 
    intros. rewrite <-(IHl m x g). ring. tauto. 
Qed.

Lemma Sumg_in_plus_out: forall m x g,
 ~ expf m x (cA m zero x) ->
   Sumg_in m x g + Sumg_in m  (cA m zero x) g + Sumg_out m x g 
     = Sumg m g.
Proof.
  unfold Sumg, Sumg_in, Sumg_out. 
  intros. apply Sumg_in_plus_out_aux. tauto. 
Qed.

(*==================================
                  Volume of a prism with triangular basis
==================================*)

(* Volume: *)
Open Scope R_scope.

Definition volume (a b c:point) : R :=
  let (xa, ya) := a in let (xb, yb) := b in let (xc, yc) := c in
  det4 xa ya 0 1
       xb yb 0 1
       xc yc 0 1
       xa ya (xa^2 + ya^2) 1 +
  det4 xb yb 0 1
       xa ya (xa^2 + ya^2) 1
       xb yb (xb^2 + yb^2) 1
       xc yc (xc^2 + yc^2) 1 +
  det4 xa ya (xa^2 + ya^2) 1
       xc yc 0 1
       xc yc (xc^2 + yc^2) 1
       xb yb 0 1. 

Lemma volume_relation :
  forall a b c d, 
    volume a b d + volume b c d = 
    volume a b c + volume a c d +
        det4 (fst a) (snd a) (mod2 a) 1 
            (fst b) (snd b) (mod2 b) 1 
            (fst c) (snd c) (mod2 c) 1
            (fst d) (snd d) (mod2 d) 1.
intros [xa ya] [xb yb] [xc yc] [xd yd].
unfold volume, snd, fst, det4, det3, det2, mod2. ring.
Qed.

Lemma volume_perm : forall x y z, volume x y z = volume y z x.
intros [xa ya] [xb yb] [xc yc].
unfold volume, snd, fst, det4, det3, det2; ring.
Qed.

(* INSTANTIATED BY DETERMINANTS: *)

Definition g (m : fmap) (d : dart) : R :=
  -volume (fpoint m d) (fpoint m (cF m d)) (fpoint m (cF m (cF m d))).

(* 3 PROPERTIES FOR g : "axioms" AT THE BEGINNING *)

Lemma axiom_g_1:  forall m z, 
  inv_Triangulation m -> isWellembed m -> 
      exd m z -> 
          g m (cF m z) = g m z.
intros m z iT iW inz.
unfold g at 2; rewrite volume_perm; unfold g.
assert (tmp := iT); destruct tmp as [h [_ [_ iT']]]; red in iT'.
assert (tr := iT' z inz); red in tr.
assert (tmp := MF0Tr.MfM.degree_lub m z h inz); fold degreef in tmp;
rewrite tr in tmp; destruct tmp as [_ [h2 _]].
change MF0Tr.MfM.f with cF in h2; fold cF in h2; simpl in h2.
rewrite h2; reflexivity.
Qed.

Lemma axiom_g_2:  forall m x, 
  inv_Triangulation m -> isWellembed m -> 
   prec_Flip_emb m x -> exd m x -> illegal m x ->
    let y := cA m zero x in
     g (Flip m x) x +  g (Flip m x) y < g m x + g m y.
intros m x iT iW pfe inx ill; lazy zeta; unfold g.
rewrite <- !Ropp_plus_distr.
assert (tmp := cF_Flip m x iT iW pfe inx); 
 unfold yff, xff, x_1, y_1, y in tmp;
 destruct tmp as [fy [ffx [nbx [fx [h1 h2]]]]].
assert (iT' := iT); destruct iT' as [h [ism [isp iT']]].
assert (ca1ca := cA_1_is_cA m x h ism inx).
rewrite (fpoint_Flip m x x h ism inx (x_neq_y m x iT inx)).
case (eq_dart_dec x x);[intros _ | intros abs;case abs; reflexivity].
rewrite <- fx, <- fy, <- ffx, <- h1.
destruct (Poly_diff_vertex m x h inx (isp _ inx)) as [xdx1 xdx_1].
rewrite (fpoint_Flip _ _ (cF m (cA_1 m one x)) h ism inx (x_neq_y m x iT inx)).
assert (expf1 : expf m (cA m zero x) (cF m (cA m zero x))).
 split;[assumption | apply MF.expo_f; rewrite <- exd_cA; assumption].
assert (expf2 : expf m x (cF m x)).
 split;[assumption | apply MF.expo_f; assumption].
case (eq_dart_dec x (cF m (cA_1 m one x))).
 intros xabs; case (not_expf_x_y m x iT iW pfe inx); unfold y.
 pattern x at 1; rewrite xabs.
 pattern x at 1; rewrite <- (cA_1_cA m zero); fold (cF m (cA m zero x)).
   apply expf_symm.
   apply expf_trans with (1:= expf1); split;[assumption |].
   apply MF.expo_f; rewrite <-exd_cF, <-exd_cA;solve[auto].
  exact h.
 assumption.
intro xnfa_1.
case (eq_dart_dec (cA m zero x)(cF m (cA_1 m one x))).
 intros caqfa_1; destruct (diff_y m x iT inx) as [_ [tmp _]]; case tmp.
 exact caqfa_1.
intros ynfa_1.
rewrite (fpoint_Flip _ _ (cA_1 m one (cA m zero x)) h
            ism inx (x_neq_y m x iT inx)).
case (eq_dart_dec x (cA_1 m one (cA m zero x))).
 intros xabs; destruct (diff_x m x iT inx) as [tmp _]; case tmp; exact xabs.
intros xna_1y.
assert (iny : exd m (cA m zero x)) by (rewrite <- exd_cA; assumption).
destruct (Poly_diff_vertex m (cA m zero x) h iny (isp _ iny)) as [ydy1 ydy_1].
case (eq_dart_dec (cA m zero x) (cA_1 m one (cA m zero x))).
 intros yabs; case ydy_1; exact yabs.
intros _.
rewrite (fpoint_Flip _ _ (cA m zero x) h ism inx (x_neq_y m x iT inx)).
case (eq_dart_dec x (cA m zero x)).
 intros xabs; case (x_neq_y m x iT inx); exact xabs.
intros _; case (eq_dart_dec (cA m zero x) (cA m zero x));
 [ | intros u;case u; reflexivity].
intros _.
rewrite (fpoint_Flip _ _ (cF m (cA_1 m one (cA m zero x)))
           h ism inx (x_neq_y m x iT inx)).
case (eq_dart_dec x (cF m (cA_1 m one (cA m zero x)))).
 intros xabs; destruct (diff_x m x iT inx) as [_ [t _]]; case t; exact xabs.
intros xnxff.
case (eq_dart_dec (cA m zero x) (cF m (cA_1 m one (cA m zero x)))).
 intros xabs; case (not_expf_x_y m x iT iW pfe inx); unfold y.
 rewrite xabs; rewrite <- ca1ca; fold (cF m x).
   apply expf_trans with (1:= expf2); split;[assumption |].
   apply MF.expo_f; rewrite <-exd_cF;solve[auto].
intros ynffx.
rewrite (fpoint_Flip _ _ (cA_1 m one x) h ism inx (x_neq_y m x iT inx)).
case (eq_dart_dec x (cA_1 m one x)).
 intros xabs; case (not_expf_x_y m x iT iW pfe inx); unfold y.
 pattern x at 1; rewrite xabs; pattern x at 1; rewrite <- (cA_1_cA m zero);
  try assumption.
 apply expf_symm; fold (cF m (cA m zero x)).
 split;[assumption | apply MF.expo_f; solve[auto]].
intros xnx_1.
case (eq_dart_dec (cA m zero x) (cA_1 m one x)).
 intros yabs.
 destruct (Tri_diff_face m (cA m zero x) h iny (iT' _ iny)) as [t [_ _]]. 
 case t; unfold cF; rewrite cA_1_cA; solve[auto].
intros ynx_1.
pattern x at 2; rewrite <- (cA_1_cA m zero); fold (cF m (cA m zero x));
 try auto.
pattern (cA m zero x) at 2 4; rewrite <- ca1ca; fold (cF m x).
assert (iW' := iW); destruct iW' as [_ [_ [iwv _]]]; red in iwv.
assert (yloc : fpoint m (cA m zero x) = fpoint m (cF m x)).
 unfold cF; rewrite ca1ca; apply iwv; auto.
 apply expv_symm; auto.
 pattern (cA m zero x) at 2; rewrite <- (cA_cA_1 m one); auto.
 apply cA_expv; rewrite <- exd_cA_1; auto.

set(u:= -
(volume (fpoint m (cF m (cF m x))) (fpoint m (cF m (cF m (cA m zero x))))
   (fpoint m (cF m x)) +
 volume (fpoint m (cF m (cF m (cA m zero x)))) (fpoint m (cF m (cF m x)))
   (fpoint m (cA_1 m one x)))). 
set(v:= volume (fpoint m x) (fpoint m (cF m x)) (fpoint m (cF m (cF m x)))). 

(* match goal with |- ?a < -(?b + _) => set u := a; set v := b end. *)
rewrite volume_perm.
unfold cF at 1; rewrite cA_1_cA; try auto.
assert (expv1: expv m (cA_1 m one x) x). 
 pattern x at 2; rewrite <- (cA_cA_1 m one); auto; apply cA_expv;
  rewrite <- exd_cA_1; auto.
rewrite (iwv (cA_1 m one x) x); [ | rewrite <- exd_cA_1 | ]; auto.
unfold v; rewrite <- volume_perm, <- yloc, volume_relation.
unfold u; rewrite <- yloc.
rewrite Rplus_comm, volume_perm.
rewrite (iwv (cA_1 m one x) x); [ | rewrite <- exd_cA_1 | ]; auto.
assert (tmp : forall x y, 0 < -y -> -x < -(x + y)) by (clear; intros; lra).
apply tmp; clear tmp.
assert (ill' := ill); destruct ill' as [_ [_ inc]]; red in inc.
rewrite <- eq_det4_perm, neq_det4_first_last, <- eq_det4_perm, Ropp_involutive.
exact inc.
Qed.

Lemma axiom_g_3:  forall m x,
  inv_Triangulation m -> isWellembed m -> 
   prec_Flip_emb m x -> exd m x ->
    let y := cA m zero x in
  (forall z, exd m z -> ~ expf m 1%nat z -> ~expf m x z -> ~expf m y z -> 
     g (Flip m x) z = g m z).
intros m x iT iW pfe inx y z inz n1 nx ny; unfold g.
assert (t := iT); destruct t as [h [ism _]].
rewrite (fpoint_Flip _ _ z h ism inx (x_neq_y m x iT inx)).
assert (exd m (cA m zero x)) by (rewrite <- exd_cA; auto).
case (eq_dart_dec x z).
 intros xabs; case nx; rewrite xabs; apply expf_refl; solve[auto].
case (eq_dart_dec (cA m zero x) z).
 intros xabs; case ny; rewrite <- xabs; apply expf_refl; solve[auto].
assert (infz : exd m (cF m z)) by (rewrite <- exd_cF; auto).
assert (zfz: expf m z (cF m z)).
 split;[assumption | apply MF.expo_f; solve[auto]].
assert (fzffz : expf m (cF m z) (cF m (cF m z))).
 split;[assumption | apply MF.expo_f; auto; rewrite <- exd_cF;solve[auto]].
assert (zffz : expf m (cF m (cF m z)) z)
  by (apply expf_symm; apply expf_trans with (1:= zfz) (2:=fzffz)).
assert (difs :cA m zero x <> cF m (cF m z) /\
   x <> cF m (cF m z) /\
   cA m zero x <> cF m z /\
   x <> cF m z /\
   cA m zero x <> z /\
   x <> z).
 split;[intros u;case ny;unfold y; rewrite u; assumption | ].
 split;[intros u;case nx; rewrite u; assumption | ].
 split;[intros u;case ny;unfold y; rewrite u; apply expf_symm; assumption | ].
 split;[intros u;case nx; rewrite u; apply expf_symm; assumption | ].
 split;[intros u;case ny; unfold y; rewrite u; apply expf_refl;assumption | ].
 intros u;case nx; rewrite u; apply expf_refl; assumption.
destruct difs as [ynff [xnff [ynf [xnf [ynz xnz]]]]].
assert (xy_1 : expf m x (y_1 m x)).
 unfold y_1, TRIANG04.y; rewrite <- cA_1_is_cA; auto; fold (cF m x).
 split; [assumption | apply MF.expo_f; auto].
assert (yx_1 : expf m (cA m zero x) (x_1 m x)).
 unfold x_1; pattern x at 2; rewrite <- (cA_1_cA m zero); auto;
   fold (cF m (cA m zero x)).
 split; [assumption | apply MF.expo_f; auto].
assert (xfx : expf m x (cF m x)) by (split;[ | apply MF.expo_f]; auto).
assert (yfy : expf m (cA m zero x) (cF m (cA m zero x)))
  by (split;[ | apply MF.expo_f]; auto).
assert (fzz : expf m (cF m z) z) by (apply expf_symm; auto).
assert (xff m x <> cF m z).
 unfold xff; intros u; case nx; apply expf_trans with (cF m z); auto.
 rewrite <-u; apply expf_trans with (1:=xy_1).
 split;[assumption|apply MF.expo_f; auto].
 apply exd_y_1; solve[auto].
assert (yff m x <> cF m z).
 unfold yff; intros u; case ny; apply expf_trans with (cF m z); auto.
 rewrite <- u; apply expf_trans with (1:=yx_1).
 split;[assumption|apply MF.expo_f; auto].
 apply exd_x_1; solve[auto].
assert (y_1 m x <> cF m z).
 intros u; case nx; apply expf_trans with (1:=xy_1); rewrite u; solve[auto].
assert (x_1 m x <> cF m z).
 intros u; case ny; apply expf_trans with (1:=yx_1); rewrite u; solve[auto].
assert (xff m x <> z).
 unfold xff; intros u; case nx; rewrite <- u;
  apply expf_trans with (y_1 m x); auto.
 split;[assumption|apply MF.expo_f; auto].
 apply exd_y_1; solve[auto].
assert (yff m x <> z).
 unfold yff; intros u; case ny; rewrite <- u.
 apply expf_trans with (1:=yx_1).
 split;[assumption|apply MF.expo_f; auto].
 apply exd_x_1; solve[auto].
assert (y_1 m x <> z).
 intros u; case nx; rewrite <- u; solve[auto].
assert (x_1 m x <> z).
 intros u; case ny; rewrite <- u; solve[auto].
repeat rewrite cF_Flip_z; auto.
rewrite (fpoint_Flip _ _ (cF m z) h ism inx (x_neq_y m x iT inx)).
case (eq_dart_dec x (cF m z));[ tauto | ].
case (eq_dart_dec (cA m zero x) (cF m z));[ tauto | ].
rewrite (fpoint_Flip _ _ (cF m (cF m z)) h ism inx (x_neq_y m x iT inx)).
case (eq_dart_dec x (cF m (cF m z))); [tauto | ].
case (eq_dart_dec (cA m zero x) (cF m (cF m z)));[tauto | ].
reflexivity.
Qed.

(* For the 2 triangles involved in the Flip: *)

Lemma expf_x_g: forall m x z,
  inv_Triangulation m ->  isWellembed m -> exd m x ->
     expf m x z -> g m z = g m x.
Proof.
  intros m x z inv_Triangulation_m  isWellembed_m exd_x. 
  generalize   inv_Triangulation_m. 
  intro IT. intro. unfold inv_Triangulation in inv_Triangulation_m. 
  decompose [and] inv_Triangulation_m. 
  clear  inv_Triangulation_m. 
  unfold isTriangulation in H4. 
  generalize (H4 x exd_x). intro. 
  generalize (isTri_expf_eq m x z H0 exd_x H3). 
  intros. 
  assert (x = z \/ cF m x = z \/ cF m (cF m x) = z). tauto. 
  assert (g m (cF m x) = g m x). 
  apply axiom_g_1. tauto. tauto. tauto. 
  assert (g m (cF m (cF m x)) = g m x). 
  rewrite <-H7. apply axiom_g_1.
  tauto. tauto. generalize (exd_cF m x). tauto. 
  elim H6. clear H6. intro. rewrite <-H6. tauto. 
  clear H6. intro. elim H6. clear H6. intro. rewrite <-H6. tauto. 
  clear H6. intro. rewrite <-H6. tauto. 
Qed.

Lemma expf_y_g: forall m x z,
 inv_Triangulation m ->  isWellembed m -> exd m x ->
  let y:= cA m zero x in
   expf m y z -> g m z = g m y.
Proof.
  intros m x z inv_Triangulation_m  isWellembed_m exd_x. 
  generalize inv_Triangulation_m. 
  intro IT. intros. 
  unfold inv_Triangulation in inv_Triangulation_m. 
  decompose [and] inv_Triangulation_m. 
  clear  inv_Triangulation_m. 
  unfold isTriangulation in H4. 
  assert (exd m y). unfold y. generalize (exd_cA m zero x). tauto. 
  generalize (H4 y H3). intro. 
  generalize (isTri_expf_eq m y z H0 H3 H5). 
  intros. 
  assert (y = z \/ cF m y = z \/ cF m (cF m y) = z). tauto. 
  assert (g m (cF m y) = g m y). 
  apply axiom_g_1. tauto. tauto. tauto. 
  assert (g m (cF m (cF m y)) = g m y). 
  rewrite <-H8. apply axiom_g_1.
  tauto. tauto. generalize (exd_cF m y). tauto. 
  elim H7. clear H7. intro. rewrite <-H7. tauto. 
  clear H7. intro. elim H7. clear H7. intro. rewrite <-H7. tauto. 
  clear H7. intro. rewrite <-H7. tauto. 
Qed.

(*===================================
              Sumg / Flip
===================================*)

Section embed_faces_Compl.

Open Scope R_scope.

Variables (m:fmap)(x:dart).

Hypothesis inv_Triangulation_m: inv_Triangulation m.
Hypothesis isWellembed_m: isWellembed m.
Hypothesis prec_Flip_emb_x: prec_Flip_emb m x.
Hypothesis exd_x: exd m x.
Hypothesis ill_x: illegal m x.

Definition x_1:= cA_1 m one x.
Definition y:= cA m zero x.
Definition y_1:= cA_1 m one y.
Definition xff:= cF m y_1.
Definition yff:= cF m x_1.

(*
Definition m1 := Split m one x x_1.
Definition m2 := Split m1 one y y_1.
Definition m3 := Merge m2 one xff x.
Definition m4 := Merge m3 one yff y.
*)

(* Preservation of the volumes of the other triangles: *)

Lemma Sumg_out_Flip_aux : forall l,
  (forall z:dart, In z l -> exd m z) ->
   Sumg_out_aux l (Flip m x) x g = Sumg_out_aux l m x g.
Proof.
  induction l. 
  simpl. intros. tauto. 
  assert (prec_Flip m x). 
  unfold isWellembed in isWellembed_m. 
  apply prec_Flip_emb_prec_Flip. 
  tauto. tauto. tauto. tauto. tauto. intros.
  simpl in H0. 
  unfold Sumg_out_aux. fold Sumg_out_aux. 
  generalize 
 (expf_Flip_1 m x inv_Triangulation_m isWellembed_m 
     prec_Flip_emb_x exd_x a). intro. 
   elim (expf_dec (Flip m x) 1%nat a). 
     elim (expf_dec m 1%nat a). 
       rewrite IHl. tauto. intro. 
    generalize (H0 z). tauto. tauto. 
       elim (expf_dec m 1%nat a).  tauto. 
     elim (expf_dec (Flip m x) x a).  
      elim (expf_dec m x a). 
        rewrite IHl. tauto. 
      intro. generalize (H0 z). tauto. 
     elim ( expf_dec m (cA m zero x) a). 
       rewrite IHl. tauto. 
     intros.  generalize (H0 z). tauto. 
    assert (exd m a). generalize (H0 a). tauto. 
     generalize (expf_Flip_xy m x a inv_Triangulation_m H H2). 
     simpl. intros. tauto. 
   assert (cA (Flip m x) zero x = cA m zero x). 
    rewrite cA0_Flip. tauto. tauto. tauto. tauto. 
   rewrite H2. 
    fold y. 
  elim (expf_dec (Flip m x) y). 
    elim (expf_dec m x a). rewrite IHl. tauto. 
      intros.  generalize (H0 z). tauto. 
    elim (expf_dec m y a). 
      rewrite IHl. tauto. 
      intros.  generalize (H0 z). tauto. 
    intros. 
   assert (exd m a). generalize (H0 a). tauto. 
   generalize (expf_Flip_xy m x a inv_Triangulation_m H H3). 
      simpl. intros. tauto. 
     elim (expf_dec m x a). intros. 
 assert (exd m a). generalize (H0 a). tauto. 
   generalize (expf_Flip_xy m x a inv_Triangulation_m H H3). 
      simpl. intros. tauto. 
      elim (expf_dec m y a). 
 assert (exd m a). generalize (H0 a). tauto. 
   generalize (expf_Flip_xy m x a inv_Triangulation_m H H3). 
      simpl. intros. tauto. 
      rewrite IHl. intros.
    rewrite axiom_g_3. tauto. 
  tauto. tauto.  tauto. tauto. clear -H0; firstorder. 
  tauto. tauto. tauto. 
      intros.  generalize (H0 z). tauto. 
Qed.

Lemma Sumg_out_Flip :
   Sumg_out (Flip m x) x g = Sumg_out m x g.
Proof.
  unfold  Sumg_out. 
  rewrite fmap_2_list_Flip. 
  apply Sumg_out_Flip_aux.  intros. 
  generalize (In_exd m z). tauto. 
Qed.

(* =====================================
      sublist of the (3) darts in u'face, x'face, y'face: 
======================================*)

Fixpoint fmap_2_list3(m':fmap)(u:dart){struct m'} : list dart:=
   match m' with
      V => nil
   |  I m0 x0 _ _ =>  
         let l0 := fmap_2_list3 m0 u in
         if expf_dec m u x0 then x0 :: l0
         else l0
   |  L m0 _ _ _ => fmap_2_list3 m0 u
  end.

Lemma In3_exd_x :  forall m' z,
   In z (fmap_2_list3 m' x) -> exd m' z.
Proof.
  induction m'. simpl. tauto.
  simpl. elim (expf_dec m x d). simpl. intros. 
    generalize (IHm' z). tauto. 
   intros.  generalize (IHm' z). tauto. 
  simpl. tauto.
Qed.

Lemma In3_exd_y :  forall m' z,
   In z (fmap_2_list3 m' y) -> exd m' z.
Proof.
  induction m'. simpl. tauto. 
  unfold  inv_Triangulation in inv_Triangulation_m.
  assert (exd m y). unfold y. 
  generalize (exd_cA m zero x). tauto. 
  simpl. elim (expf_dec m y d). simpl. intros. 
    generalize (IHm' z). tauto. 
   intros.  generalize (IHm' z). tauto. 
  simpl. tauto.
Qed.

Lemma In_fmap_2_list3_x : forall m' z,
   In z (fmap_2_list3 m' x) -> 
      (x = z \/ cF m x = z \/ cF m (cF m x) = z).
Proof.
  induction m'. 
  simpl. tauto.
  simpl. intro z. 
    generalize inv_Triangulation_m. intro IT. 
    unfold inv_Triangulation in IT.
    decompose [and] IT. clear IT.
   unfold isTriangulation in H3. 
    elim (expf_dec m x d). 
      simpl. intros. 
      elim H2. clear H2. intro. rewrite H2 in a. 
      generalize (isTri_expf_eq m x z H exd_x (H3 x exd_x)). 
      tauto. clear H2. intro. 
      apply IHm'. tauto. 
   intro. 
      apply IHm'. tauto. 
Qed.

Lemma In_fmap_2_list3_y : forall m' z,
   In z (fmap_2_list3 m' y) -> 
      (y = z \/ cF m y = z \/ cF m (cF m y) = z).
Proof.
  induction m'. 
  simpl. tauto.
  simpl. intro z. 
    generalize inv_Triangulation_m. intro IT. 
    unfold inv_Triangulation in IT.
    decompose [and] IT. clear IT.
assert (exd m y). unfold y. generalize (exd_cA m zero x). tauto. 
   unfold isTriangulation in H3. 
    elim (expf_dec m y d). 
      simpl. intros. 
      elim H4. clear H4. intro. rewrite H4 in a. 
  generalize (isTri_expf_eq m y z H H2 (H3 y H2)). 
      tauto. clear H4. intro. 
      apply IHm'. tauto. 
   intro. 
      apply IHm'. 
  simpl. tauto. 
Qed.

Lemma fmap_2_list3_In_x : forall m' z,
    exd m' z ->
      (x = z \/ cF m x = z \/ cF m (cF m x) = z) ->
    In z (fmap_2_list3 m' x).
Proof.
  induction m'. 
  simpl. tauto. 
  simpl. intros. 
    generalize inv_Triangulation_m. intro IT. 
    unfold inv_Triangulation in IT.
    decompose [and] IT. clear IT.
   unfold isTriangulation in H5. 
    elim (expf_dec m x d). 
      simpl. intros. 
    elim (eq_dart_dec d z). tauto.
    intro. right. 
    apply IHm'. tauto. tauto. 
    intro.  
      elim (eq_dart_dec d z). clear H. intro. 
        rewrite a in b. 
      elim b. 
      generalize (isTri_expf_eq m x z H1 exd_x (H5 x exd_x)). 
     tauto. intro. 
     apply IHm'. tauto. tauto. 
   simpl. 
 tauto.
Qed.

Lemma fmap_2_list3_In_y : forall m' z,
    exd m' z ->
      (y = z \/ cF m y = z \/ cF m (cF m y) = z) ->
    In z (fmap_2_list3 m' y).
Proof.
  induction m'. 
  simpl. tauto. 
  simpl. intros. 
    generalize inv_Triangulation_m. intro IT. 
    unfold inv_Triangulation in IT.
    decompose [and] IT. clear IT.
   unfold isTriangulation in H5. 
 assert (exd m y). unfold y. generalize (exd_cA m zero x). tauto. 
    elim (expf_dec m y d). 
      simpl. intros. 
    elim (eq_dart_dec d z). tauto.
    intro. right. 
    apply IHm'. tauto. tauto. 
    intro.  
      elim (eq_dart_dec d z). clear H. intro. 
        rewrite a in b. 
      elim b. 
      generalize (isTri_expf_eq m y z H1 H4 (H5 y H4)). 
     tauto. intro. 
     apply IHm'. tauto. tauto. 
   simpl. 
 tauto.
Qed.

Lemma In_fmap_2_list3_m_x : forall z,
  In z (fmap_2_list3 m x) <->
     (x = z \/ cF m x = z \/ cF m (cF m x) = z).
Proof.
 split. intro. apply In_fmap_2_list3_x with m. tauto. 
 intro.
  generalize inv_Triangulation_m. intro IT. 
    unfold inv_Triangulation in IT.
    decompose [and] IT. clear IT.
   unfold isTriangulation in H4. 
   apply fmap_2_list3_In_x. 
   elim H. clear H. intro. rewrite <-H. tauto. 
   clear H. intro H. elim H. clear H. intro. rewrite <-H. 
    generalize (exd_cF m x). tauto. 
  clear H. intro H. elim H. clear H. 
    generalize (exd_cF m x).  generalize (exd_cF m (cF m x)). tauto. 
  tauto.
Qed.

Lemma In_fmap_2_list3_m_y : forall z,
  In z (fmap_2_list3 m y) <->
     (y = z \/ cF m y = z \/ cF m (cF m y) = z).
Proof.
 split. intro. apply In_fmap_2_list3_y with m. tauto. 
 intro.
  generalize inv_Triangulation_m. intro IT. 
    unfold inv_Triangulation in IT.
    decompose [and] IT. clear IT.
   unfold isTriangulation in H4. 
 assert (exd m y). unfold y. generalize (exd_cA m zero x). tauto. 
   apply fmap_2_list3_In_y. 
   elim H. clear H. intro. rewrite <-H. tauto. 
   clear H. intro H. elim H. clear H. intro. rewrite <-H. 
    generalize (exd_cF m y). tauto. 
  clear H. intro H. elim H. clear H. 
    generalize (exd_cF m y).  generalize (exd_cF m (cF m y)). tauto. 
  tauto.
Qed.

Lemma In_fmap_2_list3_m_expf_x: forall z,
  In z (fmap_2_list3 m x) <-> expf m x z.
Proof.
  intros. 
   generalize inv_Triangulation_m. intro IT. 
    unfold inv_Triangulation in IT.
    decompose [and] IT. clear IT.
   unfold isTriangulation in H3.
   generalize (isTri_expf_eq m x z H exd_x (H3 x exd_x)).
   generalize (In_fmap_2_list3_m_x z). tauto.
Qed.

Lemma In_fmap_2_list3_m_expf_y: forall z,
  In z (fmap_2_list3 m y) <-> expf m y z.
Proof.
  intros. 
   generalize inv_Triangulation_m. intro IT. 
    unfold inv_Triangulation in IT.
    decompose [and] IT. clear IT.
   unfold isTriangulation in H3.
assert (exd m y). unfold y. generalize (exd_cA m zero x). tauto. 
    generalize (isTri_expf_eq m y z H H2 (H3 y H2)).
   generalize (In_fmap_2_list3_m_y z). tauto.
Qed.

(*===============================
            Sum on x'face, then y'face:
===============================*)

Definition Sumg_in3_x m g := 
     Sumg_in_aux (fmap_2_list3 m x) m x g. 

Definition Sumg_in3_y m g := 
     Sumg_in_aux (fmap_2_list3 m y) m y g. 

Lemma Sumg_in_aux_eq_x: forall m', 
    Sumg_in_aux  (fmap_2_list m') m x g =
         Sumg_in_aux (fmap_2_list3 m' x) m x g. 
Proof. 
 induction m'. simpl. tauto. 
 simpl. intros. 
 elim (expf_dec m 1%nat d). 
    elim (expf_dec m x d). simpl. 
 elim (expf_dec m 1%nat d). intros. 
  rewrite IHm'. tauto. 
  tauto. 
   intros.   rewrite IHm'. ring. 
 intros. 
  elim (expf_dec m x d). intros. 
  simpl. elim (expf_dec m 1%nat d). tauto. 
      elim (expf_dec m x d). intros. 
  rewrite IHm'. tauto.
       tauto. 
  rewrite IHm'. intro. ring. 
  simpl. tauto.
Qed.
      
Lemma Sumg_in_aux_eq_y: forall m', 
    Sumg_in_aux  (fmap_2_list m') m y g =
         Sumg_in_aux (fmap_2_list3 m' y) m y g. 
Proof. 
 induction m'. simpl. tauto. 
 simpl. intros. 
 elim (expf_dec m 1%nat d). 
    elim (expf_dec m y d). simpl. 
 elim (expf_dec m 1%nat d). intros. 
  rewrite IHm'. tauto. 
  tauto. 
   intros. rewrite IHm'. ring. 
 intros. 
  elim (expf_dec m y d). intros. 
  simpl. elim (expf_dec m 1%nat d). tauto. 
      elim (expf_dec m y d). intros. 
  rewrite IHm'. tauto.
       tauto. 
  rewrite IHm'. intro. ring. 
  simpl. tauto.
Qed.

Lemma no_dupl_fmap_2_list3_x: forall m', 
   inv_hmap m' ->  no_dupl (fmap_2_list3 m' x). 
Proof.
  induction m'. simpl. tauto.
  simpl. unfold prec_I. intros. 
   elim (expf_dec m x d). simpl. intros. 
    split. intro. 
    generalize (In3_exd_x m' d). tauto. tauto. 
   tauto. 
  simpl. tauto.
Qed.

Lemma no_dupl_fmap_2_list3_y: forall m', 
   inv_hmap m' ->  no_dupl (fmap_2_list3 m' y). 
Proof.
  induction m'. simpl. tauto.
  simpl. unfold prec_I. intros. 
   elim (expf_dec m y d). simpl. intros. 
    split. intro. 
    generalize (In3_exd_y m' d). tauto. tauto. 
   tauto. 
  simpl. tauto.
Qed.

Lemma no_dupl_fmap_2_list3_m_x: no_dupl (fmap_2_list3 m x). 
Proof.
 unfold inv_Triangulation in inv_Triangulation_m.
 apply no_dupl_fmap_2_list3_x. tauto.
Qed.

Lemma no_dupl_fmap_2_list3_m_y: no_dupl (fmap_2_list3 m y). 
Proof.
 unfold inv_Triangulation in inv_Triangulation_m.
 apply no_dupl_fmap_2_list3_y. tauto.
Qed.

Fixpoint nbexpf(l: list dart)(z:dart){struct l} : nat := 
   match l with
     nil => 0%nat
   | x0 :: l0 =>
        if expf_dec m z x0 then (nbexpf l0 z + 1)%nat
        else  nbexpf l0 z
  end.

(* OK: *)

Lemma expv_y_xf: expv m y  (cF m x).
Proof.
  rewrite <-y_1_cF_x.
  assert (TRIANG04.y_1 m x = y_1). tauto. rewrite H. 
  apply expv_symm. 
     unfold inv_Triangulation in inv_Triangulation_m. tauto. 
  unfold MA1.MfcA.expo. 
  split. apply exd_y_1. tauto. tauto. 
  split with 1%nat. simpl. unfold y_1. 
  assert (MA1.MfcA.f m (cA_1 m one y) = cA m one  (cA_1 m one y)). 
  tauto. rewrite H0. rewrite cA_cA_1. tauto. 
   unfold inv_Triangulation in inv_Triangulation_m. tauto. 
  apply exd_y. tauto. tauto. tauto. tauto.
Qed.
 
Lemma not_expf_1_x: ~ expf m 1%nat x.
Proof.
  unfold inv_Triangulation in inv_Triangulation_m. 
  decompose [and] inv_Triangulation_m. 
  unfold isTriangulation in H3.  
  unfold prec_Flip_emb in prec_Flip_emb_x.
  assert (ccw (fpoint m x) (fpoint m (cA m zero x))
                    (fpoint m (cF m (cF m x)))). tauto. 
  unfold isWellembed in isWellembed_m. 
  decompose [and] isWellembed_m.
  unfold isWellembedf in H8. 
  unfold isWellembedv in H5. 
  assert (fpoint m y = fpoint m (cF m x)). 
  apply H5. apply exd_y. unfold inv_Triangulation. tauto. 
  tauto. apply expv_y_xf. fold y in H2. rewrite H7 in H2. 
  clear prec_Flip_emb_x. 
  decompose [and] H8. clear H8.
  intro. 
  assert (isTri m 1%nat). 
  apply (H3 1%nat H4). 
  generalize (expf_1 m x H H4 H11). 
  intro. 
  assert (1%nat = x \/ cF m 1%nat = x \/ cF m (cF m 1%nat) = x). tauto. 
  clear H12. 
  assert (ccw_triangle m x). 
  unfold ccw_triangle. tauto. 
  assert (cw_triangle m (cF m 1%nat)).
  apply cw_dart_cF. tauto. tauto. tauto. tauto.
  assert (~cw_triangle m x). 
  generalize (ccw_cw_triangle m x). tauto. 
  elim H13. clear H13. intro. rewrite H13 in H9. tauto. 
  clear H13. intro.  elim H13. clear H13. intro. 
     rewrite H13 in H14. tauto.
  clear H13. intro.  rewrite <-H13 in H15. elim H15. 
  assert (exd m (cF m 1%nat)). generalize (exd_cF m 1%nat). tauto. 
   apply cw_dart_cF. tauto. tauto. 
  apply H3. tauto. tauto.
Qed.

Lemma expv_x_yf: expv m x  (cF m y).
Proof.
  assert (TRIANG04.y m x = y). tauto. rewrite<-H. 
  rewrite <-x_1_cF_y.  
   assert (TRIANG04.x_1 m x = x_1). tauto. rewrite H0. 
  apply expv_symm. 
     unfold inv_Triangulation in inv_Triangulation_m. tauto. 
  unfold MA1.MfcA.expo. 
  split. apply exd_x_1. tauto. tauto. 
  split with 1%nat. simpl. unfold y_1. 
  assert (MA1.MfcA.f m x_1 = cA m one  x_1). 
  tauto. rewrite H1. unfold x_1. rewrite cA_cA_1. tauto. 
   unfold inv_Triangulation in inv_Triangulation_m. tauto. 
  tauto. tauto. tauto.
Qed.

Lemma not_expf_1_y: ~ expf m 1%nat y.
Proof.
  unfold inv_Triangulation in inv_Triangulation_m. 
  decompose [and] inv_Triangulation_m. 
  unfold isTriangulation in H3.  
  unfold prec_Flip_emb in prec_Flip_emb_x.
  assert (ccw (fpoint m (cA m zero x)) (fpoint m x)
                    (fpoint m (cF m (cF m (cA m zero x))))).
  tauto. fold y in H2. 
  unfold isWellembed in isWellembed_m. 
  decompose [and] isWellembed_m.
  unfold isWellembedf in H8. 
  unfold isWellembedv in H5. 
  assert (fpoint m x = fpoint m (cF m y)). 
  apply H5. apply exd_x. 
  apply expv_x_yf. rewrite H7 in H2. 
  clear prec_Flip_emb_x. 
  decompose [and] H8. clear H8.
  intro. 
  assert (isTri m 1%nat). 
  apply (H3 1%nat H4). 
  generalize (expf_1 m y H H4 H11). 
  intro. 
  assert (1%nat = y \/ cF m 1%nat = y \/ cF m (cF m 1%nat) = y). tauto. 
  clear H12. 
  assert (ccw_triangle m y). 
  unfold ccw_triangle. tauto. 
  assert (cw_triangle m (cF m 1%nat)).
  apply cw_dart_cF. tauto. tauto. tauto. tauto.
  assert (~cw_triangle m y). 
  generalize (ccw_cw_triangle m y). tauto. 
  elim H13. clear H13. intro. rewrite H13 in H9. tauto. 
  clear H13. intro.  elim H13. clear H13. intro. 
     rewrite H13 in H14. tauto.
  clear H13. intro.  rewrite <-H13 in H15. elim H15. 
  assert (exd m (cF m 1%nat)). generalize (exd_cF m 1%nat). tauto. 
   apply cw_dart_cF. tauto. tauto. 
  apply H3. tauto. tauto.
Qed.

Lemma Sum_in_aux_x: forall l,
  Sumg_in_aux l m x g = (INR (nbexpf l x)) *  (g m x). 
Proof.
  induction l. simpl. intros. ring. 
  simpl. intros. 
  elim (expf_dec m 1%nat a). 
  elim (expf_dec m x a).  intros. 
     generalize not_expf_1_x. intro. 
    elim H. apply expf_trans with a. tauto. 
      apply expf_symm. tauto. 
    intros. rewrite IHl. ring. 
     elim (expf_dec m x a).  intros.   
   rewrite (expf_x_g m x a). 
      rewrite plus_INR. 
   rewrite Rmult_plus_distr_r. 
   rewrite IHl. simpl.  
   ring. tauto. intros. tauto. tauto. tauto. 
  rewrite IHl. intros. ring.
Qed.

Lemma Sum_in_aux_y: forall l,
  Sumg_in_aux l m y g = (INR (nbexpf l y)) *  (g m y). 
Proof.
  induction l. simpl. intros. ring. 
  simpl. intros. 
  elim (expf_dec m 1%nat a). 
  elim (expf_dec m y a).  intros. 
     generalize not_expf_1_y. intro. 
    elim H. apply expf_trans with a. tauto. 
      apply expf_symm. tauto. 
    intros. rewrite IHl. ring. 
     elim (expf_dec m y a).  intros.   
   rewrite (expf_y_g m x a). 
      rewrite plus_INR. 
   rewrite Rmult_plus_distr_r. 
   rewrite IHl. simpl.  fold y. 
   ring. tauto. tauto. tauto. tauto. intros. 
  rewrite IHl. ring.
Qed.

Lemma Sum_in3_x: let l3:= fmap_2_list3 m x in
  Sumg_in3_x m g = (INR (nbexpf l3 x)) *  (g m x).
Proof.
  simpl. apply  Sum_in_aux_x. 
Qed.

Lemma Sum_in3_y: let l3:= fmap_2_list3 m y in
  Sumg_in3_y m g = (INR (nbexpf l3 y)) *  (g m y).
Proof.
  simpl. apply  Sum_in_aux_y. 
Qed.

Lemma Sum_in3_x_aux: forall l, 
  (forall z, In z l -> expf m x z) ->
     nbexpf l x = length l.
Proof.
 induction l. simpl. tauto. 
 simpl. intros. 
 elim (expf_dec m x a). intro. 
 rewrite IHl. lia.
  intros. apply H. tauto. 
  generalize (H a). tauto. 
Qed.

Lemma Sum_in3_y_aux: forall l, 
  (forall z, In z l -> expf m y z) ->
     nbexpf l y = length l.
Proof.
 induction l. simpl. tauto. 
 simpl. intros. 
 elim (expf_dec m y a). intro. 
 rewrite IHl. lia.
  intros. apply H. tauto. 
  generalize (H a). tauto. 
Qed.

Lemma length_l3_x: 
 let l3 := fmap_2_list3 m x in
     length l3 = 3%nat.
Proof.
  intros. 
   generalize inv_Triangulation_m. intro IT. 
    unfold inv_Triangulation in IT.
    decompose [and] IT. clear IT.
   unfold isTriangulation in H3. 
   generalize (Tri_diff_face m x H exd_x (H3 x exd_x)).
   simpl. intro. 
  apply (toto l3 x (cF m x) (cF m (cF m x))). 
  split. tauto. split. tauto.  intro. symmetry in H4. tauto. 
  intro z. 
  generalize (In_fmap_2_list3_m_x z). fold l3. 
 intro. 
 assert (x = z \/ cF m x = z \/ cF m (cF m x) = z <->
             z = x \/ z = cF m x \/ z = cF m (cF m x)). 
  split. intros.
     elim H5. clear H5. intro. symmetry in H5. tauto. 
     clear H5. intro.  elim H5. clear H5. intro. symmetry in H5. tauto. 
     clear H5. intro. symmetry in H5. tauto. 
  intros. 
     elim H5. clear H5. intro. symmetry in H5. tauto. 
     clear H5. intro.  elim H5. clear H5. intro. symmetry in H5. tauto. 
     clear H5. intro. symmetry in H5. tauto. 
  clear H2. tauto. 
  apply no_dupl_fmap_2_list3_m_x.
Qed.
  
Lemma nbexpf_l3_x: 
 let l3 := fmap_2_list3 m x in nbexpf l3 x = 3%nat.
Proof.
  intro. rewrite Sum_in3_x_aux. 
  apply length_l3_x.  intro z. 
  generalize (In_fmap_2_list3_m_expf_x z). 
  tauto. 
Qed.
 
Lemma Sumg3_in_x: let l3:= fmap_2_list3 m x in
  Sumg_in3_x m g = (INR 3%nat) *  (g m x).
Proof.
  intro. rewrite Sum_in3_x. 
  rewrite nbexpf_l3_x. tauto. 
Qed.

Lemma length_l3_y: 
 let l3 := fmap_2_list3 m y in
     length l3 = 3%nat.
Proof.
  intros. 
   generalize inv_Triangulation_m. intro IT. 
    unfold inv_Triangulation in IT.
    decompose [and] IT. clear IT.
   unfold isTriangulation in H3. 
 assert (exd m y). unfold y. generalize (exd_cA m zero x). tauto. 
   rename H2 into exd_y. 
   generalize (Tri_diff_face m y H exd_y (H3 y exd_y)).
   simpl. intro. 
  apply (toto l3 y (cF m y) (cF m (cF m y))). 
  split. tauto. split. tauto.  intro. symmetry in H4. tauto. 
  intro z. 
  generalize (In_fmap_2_list3_m_y z). fold l3. 
 intro. 
 assert (y = z \/ cF m y = z \/ cF m (cF m y) = z <->
             z = y \/ z = cF m y \/ z = cF m (cF m y)). 
  split. intros.
     elim H5. clear H5. intro. symmetry in H5. tauto. 
     clear H5. intro.  elim H5. clear H5. intro. symmetry in H5. tauto. 
     clear H5. intro. symmetry in H5. tauto. 
  intros. 
     elim H5. clear H5. intro. symmetry in H5. tauto. 
     clear H5. intro.  elim H5. clear H5. intro. symmetry in H5. tauto. 
     clear H5. intro. symmetry in H5. tauto. 
  clear H2. tauto. 
  apply no_dupl_fmap_2_list3_m_y.
Qed.
  
Lemma nbexpf_l3_y: 
 let l3 := fmap_2_list3 m y in nbexpf l3 y = 3%nat.
Proof.
  intro. rewrite Sum_in3_y_aux. 
  apply length_l3_y.  intro z. 
  generalize (In_fmap_2_list3_m_expf_y z). 
  tauto. 
Qed.
 
Lemma Sumg3_in_y: let l3:= fmap_2_list3 m y in
  Sumg_in3_y m g = (INR 3%nat) *  (g m y).
Proof.
  intro. rewrite Sum_in3_y. 
  rewrite nbexpf_l3_y. tauto. 
Qed.

Lemma Sumg_in_x_3:
  Sumg_in m x g = (INR 3%nat) *  (g m x).
Proof.
  rewrite <-Sumg3_in_x. 
  unfold Sumg_in, Sumg_in3_x. 
  apply Sumg_in_aux_eq_x.
Qed.
  
Lemma Sumg_in_y_3:
  Sumg_in m y g = (INR 3%nat) *  (g m y).
Proof.
  rewrite <-Sumg3_in_y. 
  unfold Sumg_in, Sumg_in3_y. 
  apply Sumg_in_aux_eq_y.
Qed.

(*================================
                             Sumg_in / Flip
================================*)

(* =====================================
               sublist of the darts in u'face of Flip m x: 
          Same develoment with Flip m x as previously wiyh m
======================================*)

Fixpoint fmap_2_list3_Flip(m':fmap)(u:dart){struct m'} : list dart:=
   match m' with
      V => nil
   |  I m0 x0 _ _ =>  
         let l0 := fmap_2_list3_Flip m0 u in
         if expf_dec (Flip m x) u x0 then x0 :: l0
         else l0
   |  L m0 _ _ _ => fmap_2_list3_Flip m0 u
  end.

Lemma In3_exd_x_Flip :  forall m' z,
   In z (fmap_2_list3_Flip m' x) -> exd m' z.
Proof.
  induction m'. simpl. tauto.
  simpl. elim (expf_dec (Flip m x) x d). simpl. intros. 
    generalize (IHm' z). tauto. 
   intros.  generalize (IHm' z). tauto. 
  simpl. tauto.
Qed.

Lemma In3_exd_y_Flip :  forall m' z,
   In z (fmap_2_list3_Flip m' y) -> exd m' z.
Proof.
  induction m'. simpl. tauto. 
  unfold  inv_Triangulation in inv_Triangulation_m.
  assert (exd m y). unfold y. 
  generalize (exd_cA m zero x). tauto. 
  simpl. elim (expf_dec (Flip m x) y d). simpl. intros. 
    generalize (IHm' z). tauto. 
   intros.  generalize (IHm' z). tauto. 
  simpl. tauto.
Qed.

Lemma In_fmap_2_list3_x_Flip : forall m' z,
   In z (fmap_2_list3_Flip m' x) -> 
      (x = z \/ cF (Flip m x) x = z \/ 
           cF (Flip m x) (cF (Flip m x) x) = z).
Proof.
  induction m'. 
   unfold fmap_2_list3_Flip; fold fmap_2_list3_Flip. intros; tauto.
  unfold fmap_2_list3_Flip; fold fmap_2_list3_Flip. intro z. 
  assert (prec_Flip m x). 
  unfold isWellembed in isWellembed_m. 
  apply prec_Flip_emb_prec_Flip. tauto. tauto. tauto. tauto. tauto. 
  generalize 
  (inv_Triangulation_Flip m x inv_Triangulation_m H). intro ITF. 
    unfold inv_Triangulation in ITF.
    decompose [and] ITF. clear ITF.
   unfold isTriangulation in H4. 
    elim (expf_dec (Flip m x) x d). 
     unfold fmap_2_list3_Flip; fold fmap_2_list3_Flip.  intros. 
      elim H3. clear H3. intro. rewrite H3 in a. 
     assert (exd (Flip m x) x). 
    generalize (exd_Flip m x x). tauto. 
      generalize (isTri_expf_eq (Flip m x) x z H0 H5 (H4 x H5)). 
      tauto. clear H3. intro. 
      apply IHm'. tauto. 
   intro. 
      apply IHm'. tauto. 
Qed.

Lemma In_fmap_2_list3_y_Flip : forall m' z,
   In z (fmap_2_list3_Flip m' y) -> 
      (y = z \/ cF (Flip m x) y = z \/ 
           cF (Flip m x) (cF (Flip m x) y) = z).
Proof.
  induction m'. 
  unfold fmap_2_list3_Flip; fold fmap_2_list3_Flip. intros; tauto.
  unfold fmap_2_list3_Flip; fold fmap_2_list3_Flip. intro z. 
  assert (prec_Flip m x). 
  unfold isWellembed in isWellembed_m. 
  apply prec_Flip_emb_prec_Flip. tauto. tauto. tauto. tauto. tauto. 
  generalize 
  (inv_Triangulation_Flip m x inv_Triangulation_m H). intro ITF. 
    unfold inv_Triangulation in ITF.
    decompose [and] ITF. clear ITF.
   unfold isTriangulation in H4. 
  assert (exd m y). unfold y. generalize (exd_cA m zero x).
  unfold  inv_Triangulation in inv_Triangulation_m. tauto. 
 assert (exd (Flip m x) y). 
    generalize (exd_Flip m x y). tauto. 
    elim (expf_dec (Flip m x) y d). 
      unfold fmap_2_list3_Flip; fold fmap_2_list3_Flip. intros. 
      elim H6. clear H6. intro. rewrite H6 in a. 
      generalize (isTri_expf_eq (Flip m x) y z H0 H5 (H4 y H5)). 
      tauto. clear H6. intro. 
      apply IHm'. tauto. 
   intro. 
      apply IHm'. tauto. 
Qed.

Lemma fmap_2_list3_In_x_Flip : forall m' z,
    exd m' z ->
      (x = z \/ cF (Flip m x) x = z \/ cF (Flip m x) (cF (Flip m x) x) = z) ->
    In z (fmap_2_list3_Flip m' x).
Proof.
 induction m'. 
  unfold fmap_2_list3_Flip; fold fmap_2_list3_Flip. tauto.
  unfold fmap_2_list3_Flip; fold fmap_2_list3_Flip. intro z. 
  assert (prec_Flip m x). 
  unfold isWellembed in isWellembed_m. 
  apply prec_Flip_emb_prec_Flip. tauto. tauto. tauto. tauto. tauto. 
  generalize 
  (inv_Triangulation_Flip m x inv_Triangulation_m H). intro ITF. 
    unfold inv_Triangulation in ITF.
    decompose [and] ITF. clear ITF.
   unfold isTriangulation in H4. 
 elim (expf_dec (Flip m x) x d). 
      unfold fmap_2_list3_Flip, In; fold fmap_2_list3_Flip; fold In. intros. 
   elim (eq_dart_dec d z). unfold In; fold In. tauto. 
    intro. right. 
    apply IHm'. unfold exd in H3; fold exd in H3; tauto. tauto. 
    intros.  
      elim (eq_dart_dec d z). intro. 
        rewrite a in b. 
      elim b. 
  assert (exd (Flip m x) x). 
    generalize (exd_Flip m x x). tauto. 
      generalize (isTri_expf_eq (Flip m x) x z H0 H6 (H4 x H6)). 
     tauto. intro. 
     apply IHm'. unfold exd in H3; fold exd in H3;tauto. tauto. 
   unfold fmap_2_list3_Flip; fold fmap_2_list3_Flip. 
 tauto.
Qed.

Lemma fmap_2_list3_In_y_Flip : forall m' z,
    exd m' z ->
      (y = z \/ cF (Flip m x) y = z \/ cF (Flip m x) (cF (Flip m x) y) = z) ->
    In z (fmap_2_list3_Flip m' y).
Proof.
 induction m'. 
  unfold fmap_2_list3_Flip; fold fmap_2_list3_Flip. tauto.
  unfold fmap_2_list3_Flip; fold fmap_2_list3_Flip. intro z. 
  assert (prec_Flip m x). 
  unfold isWellembed in isWellembed_m. 
  apply prec_Flip_emb_prec_Flip. tauto. tauto. tauto. tauto. tauto. 
  generalize 
  (inv_Triangulation_Flip m x inv_Triangulation_m H). intro ITF. 
    unfold inv_Triangulation in ITF.
    decompose [and] ITF. clear ITF.
   unfold isTriangulation in H4. 
 elim (expf_dec (Flip m x) y d). 
       intros. 
   elim (eq_dart_dec d z). unfold In; fold In. tauto.
    intro. right. 
    apply IHm'. unfold exd in H3; fold exd in H3; tauto. tauto. 
    intros.  
      elim (eq_dart_dec d z). intro. 
        rewrite a in b. 
      elim b. 
  assert (exd (Flip m x) y). 
    generalize (exd_Flip m x y). 
unfold y. generalize (exd_cA m zero x). 
 unfold inv_Triangulation in inv_Triangulation_m. 
   clear H H0 H1 H2 H3 H5. tauto. 
      generalize (isTri_expf_eq (Flip m x) y z H0 H6 (H4 y H6)). 
     tauto. intro. 
     apply IHm'. unfold exd in H3; fold exd in H3;tauto. tauto. 
   unfold fmap_2_list3_Flip; fold fmap_2_list3_Flip. 
 tauto.
Qed.

Lemma In_fmap_2_list3_m_x_Flip : forall z,
  In z (fmap_2_list3_Flip m x) <->
     (x = z \/ cF (Flip m x) x = z \/ cF (Flip m x) (cF (Flip m x) x) = z).
Proof.
 split. intro. apply In_fmap_2_list3_x_Flip with m. tauto. 
 intro.
  generalize inv_Triangulation_m. intro IT. 
    unfold inv_Triangulation in IT.
    decompose [and] IT. clear IT.
   unfold isTriangulation in H4. 
  generalize (cF_Flip m x inv_Triangulation_m isWellembed_m 
         prec_Flip_emb_x exd_x). cbv zeta.
  unfold TRIANG04.xff, TRIANG04.yff. 
  rewrite y_1_cF_x. rewrite x_1_cF_y.  unfold TRIANG04.y. 
   fold y. 
 intros. decompose [and] H3. clear H3. 
 apply fmap_2_list3_In_x_Flip. 
  assert (exd m y). generalize (exd_cA m zero x). unfold y. tauto. 
   elim H. clear H. intro. rewrite <-H. tauto. 
   clear H. intro H. elim H. clear H. intro. rewrite <-H. 
    rewrite <-H8. 
    generalize (exd_cF m y). generalize (exd_cF m (cF m y)). tauto. 
  clear H. intro H. rewrite <-H.  rewrite <-H8. rewrite <-H9. 
    generalize (exd_cF m x).  tauto. 
  tauto. tauto. tauto. tauto. tauto. 
Qed.

Lemma In_fmap_2_list3_m_y_Flip : forall z,
  In z (fmap_2_list3_Flip m y) <->
     (y = z \/ cF (Flip m x) y = z \/ cF (Flip m x) (cF (Flip m x) y) = z).
Proof.
 split. intro. apply In_fmap_2_list3_y_Flip with m. tauto. 
 intro.
  generalize inv_Triangulation_m. intro IT. 
    unfold inv_Triangulation in IT.
    decompose [and] IT. clear IT.
   unfold isTriangulation in H4. 
  assert (exd m y). 
  unfold y. generalize (exd_cA m zero x). tauto. 
rename H3 into exd_y.
  generalize (cF_Flip m x inv_Triangulation_m isWellembed_m 
         prec_Flip_emb_x exd_x). cbv zeta.
  unfold TRIANG04.xff, TRIANG04.yff. 
  rewrite y_1_cF_x. rewrite x_1_cF_y.  unfold TRIANG04.y. 
   fold y. 
 intros. decompose [and] H3. clear H3. 
 apply fmap_2_list3_In_y_Flip. 
   elim H. clear H. intro. rewrite <-H. tauto. 
   clear H. intro H. elim H. clear H. intro. rewrite <-H. 
    rewrite <-H5. 
    generalize (exd_cF m x). generalize (exd_cF m (cF m x)). tauto. 
  clear H. intro H. rewrite <-H.  rewrite <-H5. rewrite <-H7. 
    generalize (exd_cF m y).  tauto. 
  tauto. tauto. tauto. tauto. tauto. 
Qed.

Lemma In_fmap_2_list3_m_expf_x_Flip: forall z,
  In z (fmap_2_list3_Flip m x) <-> expf (Flip m x) x z.
Proof.
  intros. 
 assert (prec_Flip m x). 
  unfold isWellembed in isWellembed_m. 
  apply prec_Flip_emb_prec_Flip. tauto. tauto. tauto. tauto. tauto. 
  generalize 
  (inv_Triangulation_Flip m x inv_Triangulation_m H). intro ITF. 
    unfold inv_Triangulation in ITF.
    decompose [and] ITF. clear ITF.
   unfold isTriangulation in H4. 
 assert (exd (Flip m x) x). generalize (exd_Flip m x x). tauto. 
  generalize (isTri_expf_eq (Flip m x) x z H0 H3 (H4 x H3)).
   generalize (In_fmap_2_list3_m_x_Flip z). tauto.
Qed.

Lemma In_fmap_2_list3_m_expf_y_Flip: forall z,
  In z (fmap_2_list3_Flip m y) <-> expf (Flip m x) y z.
Proof.
  intros. 
 assert (prec_Flip m x). 
  unfold isWellembed in isWellembed_m. 
  apply prec_Flip_emb_prec_Flip. tauto. tauto. tauto. tauto. tauto. 
  generalize 
  (inv_Triangulation_Flip m x inv_Triangulation_m H). intro ITF. 
    unfold inv_Triangulation in ITF.
    decompose [and] ITF. clear ITF.
   unfold isTriangulation in H4. 
assert (exd m y). unfold y. generalize (exd_cA m zero x). 
  unfold inv_Triangulation in inv_Triangulation_m. tauto. 
 assert (exd (Flip m x) y). generalize (exd_Flip m x y). tauto. 
  generalize (isTri_expf_eq (Flip m x) y z H0 H5 (H4 y H5)).
   generalize (In_fmap_2_list3_m_y_Flip z). tauto.
Qed.

Definition Sumg_in3_x_Flip m g := 
     Sumg_in_aux (fmap_2_list3_Flip m x) (Flip m x) x g. 

Definition Sumg_in3_y_Flip m g := 
     Sumg_in_aux (fmap_2_list3_Flip m y) (Flip m x) y g. 

Lemma Sumg_in_aux_eq_x_Flip: forall m', 
    Sumg_in_aux  (fmap_2_list m') (Flip m x) x g =
         Sumg_in_aux (fmap_2_list3_Flip m' x)  (Flip m x) x g. 
Proof. 
 induction m'. simpl. tauto. 
 simpl. intros. 
 elim (expf_dec (Flip m x) 1%nat d). 
    elim (expf_dec (Flip m x) x d). simpl. 
 elim (expf_dec (Flip m x) 1%nat d). intros. 
  rewrite IHm'. tauto. 
  tauto. 
   intros.   rewrite IHm'. ring. 
 intros. 
  elim (expf_dec (Flip m x) x d). intros. 
  simpl. elim (expf_dec (Flip m x) 1%nat d). tauto. 
      elim (expf_dec  (Flip m x) x d). intros. 
  rewrite IHm'. tauto.
       tauto. 
  rewrite IHm'. intro. ring. 
  simpl. tauto.
Qed.
      
Lemma Sumg_in_aux_eq_y_Flip: forall m', 
    Sumg_in_aux  (fmap_2_list m')  (Flip m x) y g =
         Sumg_in_aux (fmap_2_list3_Flip m' y) (Flip m x) y g. 
Proof. 
 induction m'. simpl. tauto. 
 simpl. intros. 
 elim (expf_dec (Flip m x) 1%nat d). 
    elim (expf_dec (Flip m x) y d). simpl. 
 elim (expf_dec (Flip m x) 1%nat d). intros. 
  rewrite IHm'. tauto. 
  tauto. 
   intros. rewrite IHm'. ring. 
intros. 
  elim (expf_dec (Flip m x) y d). intros. 
  simpl. elim (expf_dec (Flip m x) 1%nat d). tauto. 
      elim (expf_dec  (Flip m x) y d). intros. 
  rewrite IHm'. tauto.
       tauto. 
  rewrite IHm'. intro. ring. 
  simpl. tauto.
Qed.

Lemma no_dupl_fmap_2_list3_x_Flip: forall m', 
   inv_hmap m' ->  no_dupl (fmap_2_list3_Flip m' x). 
Proof.
  induction m'. simpl. tauto.
  simpl. unfold prec_I. intros. 
   elim (expf_dec (Flip m x) x d). simpl. intros. 
    split. intro. 
    generalize (In3_exd_x_Flip m' d). tauto. tauto. 
   tauto. 
  simpl. tauto.
Qed.

Lemma no_dupl_fmap_2_list3_y_Flip: forall m', 
   inv_hmap m' ->  no_dupl (fmap_2_list3_Flip m' y). 
Proof.
  induction m'. simpl. tauto.
  simpl. unfold prec_I. intros. 
   elim (expf_dec (Flip m x) y d). simpl. intros. 
    split. intro. 
    generalize (In3_exd_y_Flip m' d). tauto. tauto. 
   tauto. 
  simpl. tauto.
Qed.

Lemma no_dupl_fmap_2_list3_m_x_Flip: 
   no_dupl (fmap_2_list3_Flip m x). 
Proof.
 unfold inv_Triangulation in inv_Triangulation_m.
 apply no_dupl_fmap_2_list3_x_Flip. tauto.
Qed.

Lemma no_dupl_fmap_2_list3_m_y_Flip: 
   no_dupl (fmap_2_list3_Flip m y). 
Proof.
 unfold inv_Triangulation in inv_Triangulation_m.
 apply no_dupl_fmap_2_list3_y_Flip. tauto.
Qed.

Fixpoint nbexpf_Flip(l: list dart)(z:dart){struct l} : nat := 
   match l with
     nil => 0%nat
   | x0 :: l0 =>
        if expf_dec (Flip m x) z x0 then (nbexpf_Flip l0 z + 1)%nat
        else  nbexpf_Flip l0 z
  end.

(* OK: *)

Lemma not_expf_1_x_Flip: ~ expf (Flip m x) 1%nat x.
Proof.
  generalize (expf_Flip_1 m x inv_Triangulation_m
     isWellembed_m prec_Flip_emb_x exd_x x). 
  generalize not_expf_1_x. tauto.
Qed.

Lemma not_expf_1_y_Flip: ~ expf (Flip m x) 1%nat y.
Proof.
  generalize (expf_Flip_1 m x inv_Triangulation_m
     isWellembed_m prec_Flip_emb_x exd_x y). 
  generalize not_expf_1_y. tauto.
Qed.

Lemma Sum_in_aux_x_Flip: forall l,
  Sumg_in_aux l (Flip m x) x g = 
        (INR (nbexpf_Flip l x)) *  (g (Flip m x) x). 
Proof.
  induction l. simpl. intros. ring. 
  simpl. intros. 
  elim (expf_dec (Flip m x) 1%nat a). 
  elim (expf_dec (Flip m x) x a).  intros. 
     generalize not_expf_1_x_Flip. intro. 
    elim H. apply expf_trans with a. tauto. 
      apply expf_symm. tauto. 
    intros. rewrite IHl. ring. 
     elim (expf_dec (Flip m x) x a).  intros.   
   assert (prec_Flip m x). 
     unfold isWellembed in isWellembed_m. 
       apply prec_Flip_emb_prec_Flip.  
        tauto. tauto. tauto. tauto. tauto. 
   rewrite (expf_x_g (Flip m x) x a). 
      rewrite plus_INR. 
   rewrite Rmult_plus_distr_r. 
   rewrite IHl. simpl.  
   ring. apply inv_Triangulation_Flip. tauto.
    tauto. apply isWellembed_Flip. tauto. tauto. 
      tauto. tauto. generalize (exd_Flip m x x). tauto. 
    tauto. intros.
  rewrite IHl. ring.
Qed.

Lemma Sum_in_aux_y_Flip: forall l,
  Sumg_in_aux l (Flip m x) y g = 
        (INR (nbexpf_Flip l y)) *  (g (Flip m x) y). 
Proof.
  induction l. simpl. intros. ring. 
  simpl. intros. 
  elim (expf_dec (Flip m x) 1%nat a). 
  elim (expf_dec (Flip m x) y a).  intros. 
     generalize not_expf_1_y_Flip. intro. 
    elim H. apply expf_trans with a. tauto. 
      apply expf_symm. tauto. 
    intros. rewrite IHl. ring. 
     elim (expf_dec (Flip m x) y a).  intros.   
   assert (prec_Flip m x). 
     unfold isWellembed in isWellembed_m. 
       apply prec_Flip_emb_prec_Flip.  
        tauto. tauto. tauto. tauto. tauto. 
   rewrite (expf_y_g (Flip m x) x a). 
   rewrite cA0_Flip. fold y. 
     assert (INR (nbexpf_Flip l y + 1) = INR (nbexpf_Flip l y) +
          INR (1%nat)).  rewrite plus_INR. tauto. 
   assert (INR 1%nat = 1). simpl. tauto. 
   rewrite H0. rewrite H1. rewrite IHl. ring. 
  tauto. tauto. tauto. 
   apply inv_Triangulation_Flip. tauto.
    tauto. apply isWellembed_Flip. tauto. tauto. 
      tauto. tauto. generalize (exd_Flip m x x). tauto. 
    rewrite cA0_Flip. fold y. tauto. tauto. tauto. tauto. 
    intros.
  rewrite IHl. ring.
Qed.

Lemma Sum_in3_x_Flip: 
 let l3:= fmap_2_list3_Flip m x in
  Sumg_in3_x_Flip m g = (INR (nbexpf_Flip l3 x)) *  (g (Flip m x) x).
Proof.
  simpl. apply  Sum_in_aux_x_Flip. 
Qed.

Lemma Sum_in3_y_Flip: let l3:= 
 fmap_2_list3_Flip m y in
  Sumg_in3_y_Flip m g = (INR (nbexpf_Flip l3 y)) *  (g (Flip m x) y).
Proof.
  simpl. apply  Sum_in_aux_y_Flip. 
Qed.

Lemma Sum_in3_x_aux_Flip: forall l, 
  (forall z, In z l -> expf (Flip m x) x z) ->
     nbexpf_Flip l x = length l.
Proof.
 induction l. simpl. tauto. 
 simpl. intros. 
 elim (expf_dec (Flip m x) x a). intro. 
 rewrite IHl. lia.
  intros. apply H. tauto. 
  generalize (H a). tauto. 
Qed.

Lemma Sum_in3_y_aux_Flip: forall l, 
  (forall z, In z l -> expf (Flip m x) y z) ->
     nbexpf_Flip l y = length l.
Proof.
 induction l. simpl. tauto. 
 simpl. intros. 
 elim (expf_dec (Flip m x) y a). intro. 
 rewrite IHl. lia.
  intros. apply H. tauto. 
  generalize (H a). tauto. 
Qed.

Lemma length_l3_x_Flip: 
 let l3 := fmap_2_list3_Flip m x in
     length l3 = 3%nat.
Proof.
  intros. 
 assert (prec_Flip m x). 
  unfold isWellembed in isWellembed_m. 
  apply prec_Flip_emb_prec_Flip. tauto. tauto. tauto. tauto. tauto. 
  generalize 
  (inv_Triangulation_Flip m x inv_Triangulation_m H). intro ITF. 
    unfold inv_Triangulation in ITF.
    decompose [and] ITF. clear ITF.
   unfold isTriangulation in H4. 
  assert (exd (Flip m x) x). generalize (exd_Flip m x x). tauto. 
  rename H3 into exd_Flip_x.
 generalize (Tri_diff_face (Flip m x) x H0 exd_Flip_x 
     (H4 x exd_Flip_x)).
   cbv zeta. intro. 
  apply (toto l3 x (cF (Flip m x) x) (cF (Flip m x) (cF  (Flip m x) x))). 
  split. tauto. split. tauto.  intro. symmetry in H5. tauto. 
  intro z. 
  generalize (In_fmap_2_list3_m_x_Flip z). fold l3. 
 intro. 
 assert (x = z \/ cF (Flip m x) x = z \/ cF (Flip m x) (cF (Flip m x) x) = z <->
             z = x \/ z = cF  (Flip m x) x \/ z = cF (Flip m x) (cF  (Flip m x) x)). 
  split. intros. rename H5 into I5. rename H6 into H5.
     elim H5. clear H5. intro. symmetry in H5. tauto. 
     clear H5. intro.  elim H5. clear H5. intro. symmetry in H5. tauto. 
     clear H5. intro. symmetry in H5. tauto. 
  intros.  rename H5 into I5. rename H6 into H5.
     elim H5. clear H5. intro. symmetry in H5. tauto. 
     clear H5. intro.  elim H5. clear H5. intro. symmetry in H5. tauto. 
     clear H5. intro. symmetry in H5. tauto. 
  clear H2.
   set(P:= z = x \/ z = cF (Flip m x) x \/ z = cF (Flip m x) (cF (Flip m x) x)). 
   set (Q:= x = z \/ cF (Flip m x) x = z \/ cF (Flip m x) (cF (Flip m x) x) = z). 
   fold P Q in H5, H6. clear H3. tauto. 
  apply no_dupl_fmap_2_list3_m_x_Flip.
Qed.
  
Lemma nbexpf_l3_x_Flip: 
 let l3 := fmap_2_list3_Flip m x in nbexpf_Flip l3 x = 3%nat.
Proof.
  intro. rewrite Sum_in3_x_aux_Flip. 
  apply length_l3_x_Flip.  intro z. 
  generalize (In_fmap_2_list3_m_expf_x_Flip z). 
  tauto. 
Qed.
 
Lemma Sumg3_in_x_Flip: 
 let l3:= fmap_2_list3_Flip m x in
  Sumg_in3_x_Flip m g = (INR 3%nat) *  (g (Flip m x) x).
Proof.
  intro. rewrite Sum_in3_x_Flip. 
  rewrite nbexpf_l3_x_Flip. tauto. 
Qed.

Lemma length_l3_y_Flip: 
 let l3 := fmap_2_list3_Flip m y in
     length l3 = 3%nat.
Proof.
intros. 
 assert (prec_Flip m x). 
  unfold isWellembed in isWellembed_m. 
  apply prec_Flip_emb_prec_Flip. tauto. tauto. tauto. tauto. tauto. 
  generalize 
  (inv_Triangulation_Flip m x inv_Triangulation_m H). intro ITF. 
    unfold inv_Triangulation in ITF.
    decompose [and] ITF. clear ITF.
   unfold isTriangulation in H4. 
  assert (exd (Flip m x) x). generalize (exd_Flip m x x). tauto. 
  rename H3 into exd_Flip_x.
  assert (exd m y). unfold y. generalize (exd_cA m zero x). 
    unfold inv_Triangulation in inv_Triangulation_m.  tauto. 
  rename H3 into exd_y. 
    assert (exd (Flip m x) y). generalize (exd_Flip m x y). tauto. 
  rename H3 into exd_Flip_y.
 generalize (Tri_diff_face (Flip m x) y H0 exd_Flip_y 
     (H4 y exd_Flip_y)).
   cbv zeta. intro. 
  apply (toto l3 y (cF (Flip m x) y) (cF (Flip m x) (cF  (Flip m x) y))). 
  split. tauto. split. tauto.  intro. symmetry in H5. tauto. 
  intro z. 
  generalize (In_fmap_2_list3_m_y_Flip z). fold l3. 
 intro. 
 assert (y = z \/ cF (Flip m x) y = z \/ cF (Flip m x) (cF (Flip m x) y) = z <->
             z = y \/ z = cF  (Flip m x) y \/ z = cF (Flip m x) (cF  (Flip m x) y)). 
  split. intros. rename H5 into I5. rename H6 into H5.
     elim H5. clear H5. intro. symmetry in H5. tauto. 
     clear H5. intro.  elim H5. clear H5. intro. symmetry in H5. tauto. 
     clear H5. intro. symmetry in H5. tauto. 
  intros.  rename H5 into I5. rename H6 into H5.
     elim H5. clear H5. intro. symmetry in H5. tauto. 
     clear H5. intro.  elim H5. clear H5. intro. symmetry in H5. tauto. 
     clear H5. intro. symmetry in H5. tauto. 
  clear H2.
   set(P:= z = y \/ z = cF (Flip m x) y \/ z = cF (Flip m x) (cF (Flip m x) y)). 
   set (Q:= y = z \/ cF (Flip m x) y = z \/ cF (Flip m x) (cF (Flip m x) y) = z). 
   fold P Q in H5, H6. clear H3. tauto. 
  apply no_dupl_fmap_2_list3_m_y_Flip.
Qed.
  
Lemma nbexpf_l3_y_Flip: 
 let l3 := fmap_2_list3_Flip m y in nbexpf_Flip l3 y = 3%nat.
Proof.
  intro. rewrite Sum_in3_y_aux_Flip. 
  apply length_l3_y_Flip.  intro z. 
  generalize (In_fmap_2_list3_m_expf_y_Flip z). 
  tauto. 
Qed.
 
Lemma Sumg3_in_y_Flip: let l3:= fmap_2_list3_Flip m y in
  Sumg_in3_y_Flip m g = (INR 3%nat) *  (g (Flip m x) y).
Proof.
  intro. rewrite Sum_in3_y_Flip. 
  rewrite nbexpf_l3_y_Flip. tauto. 
Qed.

Lemma Sumg_in_x_3_Flip:
  Sumg_in (Flip m x) x g = (INR 3%nat) *  (g (Flip m x) x).
Proof.
  rewrite <-Sumg3_in_x_Flip. 
  unfold Sumg_in, Sumg_in3_x_Flip. 
  assert (fmap_2_list (Flip m x) = fmap_2_list m). 
  apply fmap_2_list_Flip. rewrite H. 
  apply Sumg_in_aux_eq_x_Flip.
Qed.
  
Lemma Sumg_in_y_3_Flip:
  Sumg_in (Flip m x) y g = (INR 3%nat) *  (g (Flip m x) y).
Proof. 
  rewrite <-Sumg3_in_y_Flip. 
  unfold Sumg_in, Sumg_in3_y_Flip. 
  assert (fmap_2_list (Flip m x) = fmap_2_list m). 
  apply fmap_2_list_Flip. rewrite H. 
  apply Sumg_in_aux_eq_y_Flip.
Qed.

(*================================
                          Final result
================================*)

(* OK: *)

Definition not_expf_x_y := TRIANG04.not_expf_x_y.  

Lemma not_expf_Flip_x_y : ~ expf (Flip m x) x y.
Proof.
 generalize isWellembed_m. intro IW. 
 generalize inv_Triangulation_m. intro IT.
 unfold inv_Triangulation in IT. 
 decompose [and] IT. rename H into Im. rename H1 into IM. 
 rename H0 into IP. 
 unfold isTriangulation in H3. rename H3 into IsT. 
 unfold isWellembed in isWellembed_m. 
 assert (prec_Flip m x). 
  apply prec_Flip_emb_prec_Flip. tauto. tauto. tauto. tauto. tauto. 
 assert (inv_Triangulation (Flip m x)). 
 apply inv_Triangulation_Flip. tauto. tauto. 
 unfold  inv_Triangulation in H0. 
 decompose [and] H0. clear H0. 
 unfold isTriangulation in H5. 
 assert (exd (Flip m x) x). generalize (exd_Flip m x x). tauto. 
 generalize (H5 x H0). intro. 
 generalize ( isTri_expf_eq (Flip m x) x y H1 H0 H4). 
 intros. 
 generalize (cF_Flip m x inv_Triangulation_m IW prec_Flip_emb_x exd_x).
 assert (TRIANG04.yff m x = yff). tauto. 
 assert (TRIANG04.y_1 m x = y_1). tauto. 
 assert (TRIANG04.y m x = y). tauto. 
 generalize (diff_2faces_x_y m x 
         inv_Triangulation_m IW prec_Flip_emb_x exd_x).
 assert (exd m y). apply exd_y. tauto. tauto. 
generalize (Tri_diff_face m y Im H10 (IsT y H10)). 
 cbv zeta. rewrite H7, H8, H9.
 intros. 
 assert (yff = cF (Flip m x) x). tauto. 
  assert (y_1 = cF (Flip m x) yff). tauto. 
  rewrite <-H14 in H6. rewrite <-H15 in H6. 
  assert (yff = cF m (cF m y)). 
 unfold yff. unfold x_1. rewrite (x_cA0_1_y m x).
 rewrite H9. fold (cF m y). tauto. tauto. tauto. 
 rewrite <-H16 in H11. 
 intro. 
 assert (x = y \/ yff = y \/ y_1 = y). tauto. 
 clear H6 H7 H8 H9 H10 H13 H14 H15 H16 H17. 
 assert (yff <> y). intro. symmetry in H6. tauto. 
 tauto. 
Qed. 

Lemma Sumg_decr: Sumg (Flip m x) g < Sumg m g.
Proof.
   assert (prec_Flip m x). 
   unfold isWellembed in isWellembed_m. 
   apply prec_Flip_emb_prec_Flip. tauto. tauto. tauto. tauto. tauto. 
   rewrite <- (Sumg_in_plus_out m x g). 
   rewrite <- (Sumg_in_plus_out (Flip m x) x g). 
   rewrite cA0_Flip. fold y. 
   rewrite Sumg_in_x_3. 
   rewrite Sumg_in_y_3. 
   rewrite Sumg_in_x_3_Flip. 
   rewrite Sumg_in_y_3_Flip. 
   rewrite Sumg_out_Flip. 
   generalize (axiom_g_2 m x inv_Triangulation_m
          isWellembed_m prec_Flip_emb_x exd_x ill_x). 
   cbv zeta. fold y. intros. 
apply Rplus_lt_le_compat.
do 2 rewrite <- Rmult_plus_distr_l.
apply Rmult_lt_compat_l.
(*Search INR.*)
replace 0 with (INR 0) by reflexivity.
apply lt_INR.
lia.
assumption.
apply Rle_refl.

   tauto. tauto. tauto. 
   rewrite cA0_Flip. fold y. 
   apply not_expf_Flip_x_y. 
   tauto. tauto. tauto. 
   fold y. apply not_expf_x_y. 
   tauto. tauto. tauto. tauto.
Qed.

End embed_faces_Compl.

(*========= END VOLUMES ===================*)

(*=======================================
                         DELAUNAY Cont'd
========================================*)

Definition mes(m : fmap): R:= Sumg m g.

Definition step := next.

(* Stopping condition: *)

Definition final:= no_dart_illegal.

(*===== ==========REPRISE =======================

remplacer mes par Sumg
remplacer leA par <= 

============================================*)

Definition leA(r1 r2:R) := r1 >= r2.

Definition leA_dec:= Rge_dec.
Definition leA_refl:= Rge_refl.
Definition leA_trans:= Rge_trans.
Definition leA_antisym:= Rge_antisym.

Lemma leA_total:forall r1 r2,
    ~ leA r1 r2 -> leA r2 r1.
Proof.
  unfold leA. intros.
  apply Rgt_ge. 
  apply Rlt_gt. 
  apply Rnot_ge_lt. 
  tauto. 
Qed.

Lemma Flip_decrease :
  forall m x,  inv_Triangulation m -> isWellembed m -> 
     exd m x -> illegal m x -> 
       leA (mes m) (mes (Flip m x)).
Proof.
  intros. unfold leA. unfold mes. 
  apply Rgt_ge. 
  apply Rlt_gt. 
  apply Sumg_decr. 
  tauto. tauto. 
  apply illegal_prec_Flip_emb. tauto. tauto. tauto.
Qed.

Lemma Flip_diff :
  forall m x,  inv_Triangulation m -> isWellembed m -> 
     exd m x -> illegal m x -> 
       mes m <> mes (Flip m x).
Proof.
  intros. unfold leA. unfold mes. 
  apply Rgt_not_eq.  apply Rlt_gt. 
  apply Sumg_decr. 
  tauto. tauto. 
  apply illegal_prec_Flip_emb. tauto. tauto. tauto.
Qed.

Definition tri_map_tr := {x : fmap | inv_Triangulation x /\ isWellembed x}.

Fixpoint larger (x : fmap) (l:list fmap) : list fmap :=
 match l with
   nil => nil
 | y::tl =>
    match leA_dec (mes x) (mes y) with
     left _ => y::larger x tl
   | _ => larger x tl
   end
 end.

Definition nat_measure (m : tri_map_tr) : nat :=
  let (m, _) := m in
  let s := fmap_fs (darts_of_fmap m)
             (tags_of_fmap m)
             (sort (points_of_fmap m)) in
  length (larger m (fs_enum s)).

(* Successors are in A: *)

(* First: points *)

Lemma leA_to_le :
  forall l m1 m2, leA (mes m1) (mes m2) ->
   (length (larger m2 l) <= length (larger m1 l))%nat.
Proof.
intros l m1 m2 cmp; induction l.
 solve[auto].
 simpl. case (leA_dec (mes m2) (mes a)); 
     case (leA_dec (mes m1) (mes a)).
 intros _ _; simpl; apply le_n_S; auto.
 intros c1 c2; assert (c3 : leA (mes m2) ( mes m1)). 
  apply leA_trans with (mes a); [assumption | apply leA_total; assumption].
  assert (m12 : mes m2 = mes m1) by (apply leA_antisym; assumption).
  case c1; rewrite <- m12; assumption.
 intros; apply le_S; assumption.
 intros; assumption.
Qed.

Definition p_tri : 
  {x : fmap | inv_Triangulation x /\ isWellembed x} -> fmap :=
 fun s => let (x, _) := s in x.

Definition step_tri : {x | inv_Triangulation x /\ isWellembed x} ->
   {x | inv_Triangulation x /\ isWellembed x}.
intros [m [iT iW]].
pose (z := some_illegal m m).
case (eq_dart_dec z Del01.nil).
 intros _; exact (exist (fun x => inv_Triangulation x /\ isWellembed x)
                     m (conj iT iW)).
intros cond.
 exists (Flip m z).
assert (exd m z) by (apply exd_some_illegal; assumption).
assert (illegal m z) by (apply illegal_some_illegal; assumption).
split.
 apply inv_Triangulation_Flip.
  assumption.
 apply illegal_prec_Flip; assumption || (destruct iW; tauto).
apply isWellembed_Flip; try assumption.
apply illegal_prec_Flip_emb; assumption.
Defined.

Lemma Alt_to_lt : 
  forall l m1 m2, leA (mes m1) (mes m2) -> 
    mes m1 <> mes m2 -> In m1 l ->
    (length (larger m2 l) < length (larger m1 l))%nat.
Proof.
intros l m1 m2 cmp dif; induction l.
 intros abs; case abs.
simpl; intros [ m1a | m1l].
 subst a; case (leA_dec (mes m2) (mes m1)).
 intros m21; case dif; apply leA_antisym; assumption.
 case (leA_dec (mes m1) (mes m1)).
  intros _ _; simpl; apply le_n_S; apply leA_to_le; assumption.
 intros n; case n; apply leA_refl.
case (leA_dec (mes m2) (mes a)); intros m2a.
 case (leA_dec (mes m1) (mes a)); intros m1a.
  simpl; apply -> PeanoNat.Nat.succ_lt_mono; solve[auto].
 case dif;apply leA_antisym;[assumption | ].
 apply leA_trans with (mes a);[assumption | apply leA_total; assumption].
case (leA_dec (mes m1) (mes a)); intros m1a.
 simpl; apply Nat.lt_lt_succ_r; solve[auto].
solve[auto].
Qed.

Lemma darts_in_list_add :
   forall d l m, 
     darts_in_fs m
       (mkfs dart (fun x => In x l) l (fun x h => h)) ->
     darts_in_fs m
       (mkfs dart (fun x => In x (d::l)) (d::l) (fun x h => h)).
intros d' l m; induction m as [ | m IH d t p | m IH k d1 d2].
  solve[trivial].
 simpl; intros [il dl]; split; solve[auto].
simpl; solve[auto].
Qed.

Lemma darts_in_fs_list: forall m : fmap, 
    inv_hmap m -> 
      darts_in_fs m
       (mkfs dart (fun x => In x (darts_of_fmap m)) (darts_of_fmap m) 
          (fun x h => h)).
Proof.
induction m as [ | m IH d t p | m IH k d1 d2].
  solve[trivial].
 solve[simpl; intros [h pr]; split;[ | apply darts_in_list_add]; auto].
solve[simpl; intros [h _]; auto].
Qed.

Lemma tags_in_list_add :
   forall d l m, 
     tags_in_fs m
       (mkfs tag (fun x => In x l) l (fun x h => h)) ->
     tags_in_fs m
       (mkfs tag (fun x => In x (d::l)) (d::l) (fun x h => h)).
intros d' l m; induction m as [ | m IH d t p | m IH k d1 d2].
  solve[trivial].
 simpl; intros [il dl]; split; solve[auto].
simpl; solve[auto].
Qed.

Lemma tags_in_fs_list: forall m : fmap, 
    inv_hmap m -> 
      tags_in_fs m
       (mkfs tag (fun x => In x (tags_of_fmap m)) (tags_of_fmap m) 
          (fun x h => h)).
Proof.
induction m as [ | m IH d t p | m IH k d1 d2].
  solve[trivial].
 solve[simpl; intros [h pr]; split;[ | apply tags_in_list_add]; auto].
solve[simpl; intros [h _]; auto].
Qed.

Lemma points_in_list_add :
   forall d l m, 
     points_in_fs m
       (mkfs point (fun x => In x l) l (fun x h => h)) ->
     points_in_fs m
       (mkfs point (fun x => In x (insert d l)) (insert d l) (fun x h => h)).
intros d' l m; induction m as [ | m IH d t p | m IH k d1 d2].
  solve[trivial].
 solve [simpl; intros [il dl]; split;[apply insert_in_d; right |]; auto].
simpl; solve[auto].
Qed.

Lemma points_in_fs_list: forall m : fmap, 
    inv_hmap m -> 
      points_in_fs m
       (mkfs point (fun x => In x (sort (points_of_fmap m)))
          (sort (points_of_fmap m))
          (fun x h => h)).
Proof.
induction m as [ | m IH d t p | m IH k d1 d2].
  solve[trivial].
 simpl; intros [h pr].
 solve[split;[apply insert_in_it | apply points_in_list_add]; auto].
solve[simpl; intros [h _]; auto].
Qed.

Lemma fmap_in_fs :
 forall m : fmap, inv_Triangulation m -> isWellembed m -> 
        fmap_fs (darts_of_fmap m) (tags_of_fmap m) (sort (points_of_fmap m)) m.
unfold inv_Triangulation; intros m iT iW.
split.
 simpl; apply darts_in_fs_list; tauto.
split.
 simpl; apply tags_in_fs_list; tauto.
split.
 simpl; apply points_in_fs_list; tauto.
unfold inv_Triangulation; tauto.
Qed.

(* The measure is strictly decreasing: 
AFTER EXPRESSING mes:  OK! *)
Lemma non_final_step_decrease :
  forall m, ~final (p_tri m) ->
   (nat_measure (step_tri m) < nat_measure m)%nat.
Proof.
unfold nat_measure, step_tri; intros [m [iT iW]].
case (eq_dart_dec (some_illegal m m) Del01.nil).
 intros sill; unfold final, p_tri; intros n; case n; exact sill.
intros ill nf.
assert (illegal m (some_illegal m m))
  by (apply illegal_some_illegal; assumption).
assert (exd m (some_illegal m m)) by (apply exd_some_illegal; assumption).
rewrite Flip_preserves_darts, Flip_preserves_tags, Flip_preserves_points;
 try assumption.
 apply Alt_to_lt.
   apply Flip_decrease; assumption.
  apply Flip_diff; assumption.
 apply enum_p; apply fmap_in_fs; assumption.
apply illegal_prec_Flip; try assumption; clear nf; destruct iW; tauto.
Qed.

(* The stopping condition final is decidable:*)

Definition final_bool x :=
  if no_dart_illegal_dec x then true else false.

Definition tri_map := {x | inv_Triangulation x /\ isWellembed x}.

Function delaunay' (t : tri_map) 
  {measure nat_measure} : fmap :=
  if final_bool (p_tri t) then p_tri t else delaunay' (step_tri t).
intros t; unfold final_bool; case (no_dart_illegal_dec (p_tri t));
 [intros _ ab; discriminate | intros f _].
  apply non_final_step_decrease; exact f.
Defined.

End Delaunay_solution.

(*================================================================
                                 Delaunay function:
================================================================*)

Definition Delaunay(m:fmap)(IT: inv_Triangulation m)(WE:isWellembed m) :=
  delaunay' (exist (fun x => inv_Triangulation x /\ isWellembed x) m (conj IT WE)).

(*================================================================
                          PARTIAL CORRECTNESS
=================================================================*)

Theorem inv_Triangulation_Delaunay : 
  forall (m : fmap)(IT: inv_Triangulation m)(WE: isWellembed m),  
    inv_Triangulation (Delaunay m IT WE).  
Proof.
  intros m IT WE; unfold Delaunay.
  generalize (exist (fun x => inv_Triangulation x /\ isWellembed x) m
                  (conj IT WE)).
  intros s; functional induction delaunay' s. 
  destruct t as [t [IT' IW']]; simpl; assumption.
  assumption.
Qed.

Theorem isWellembed_Delaunay : 
  forall (m : fmap)(IT: inv_Triangulation m)(WE: isWellembed m),  
      isWellembed (Delaunay m IT WE). 
Proof.
  intros m IT WE; unfold Delaunay.
  generalize (exist (fun x => inv_Triangulation x /\ isWellembed x) m
               (conj IT WE)).
  intros s; functional induction delaunay' s.
  destruct t as [t [IT' IW']]; simpl; assumption.
  assumption.
Qed.

(* OK!: *)

Theorem no_dart_illegal_Delaunay : 
  forall (m : fmap)(IT: inv_Triangulation m)(WE: isWellembed m),  
      no_dart_illegal (Delaunay m IT WE). 
Proof.
intros m IT WE; unfold Delaunay.
generalize (exist (fun x : fmap => inv_Triangulation x /\ isWellembed x) m
           (conj IT WE)); intros s.
functional induction delaunay' s;
 [ unfold final_bool in e; 
   destruct (no_dart_illegal_dec (p_tri t)); discriminate || assumption
 | assumption].
Qed.

Definition planar_tri_map(t:tri_map):=
   match t with (exist m _) => planar m end.
 
Lemma planar_planar_tri_map: 
 forall (m : fmap)(IT: inv_Triangulation m)(WE: isWellembed m),  
     planar m -> 
       planar_tri_map (exist 
          (fun x : fmap => inv_Triangulation x /\ isWellembed x) m
           (conj IT WE)). 
Proof. 
  simpl. tauto.
Qed.

Lemma planar_tri_map_planar: forall t,
  planar_tri_map t -> planar (p_tri t). 
Proof. 
  induction t. tauto. 
Qed.

Lemma planar_step_tri: forall t,
  planar_tri_map t -> planar_tri_map (step_tri t). 
Proof. 
  intros. destruct t as [m [IT' IW']]. 
  unfold step_tri. fold step_tri. 
  elim (eq_dart_dec (some_illegal m m) Del01.nil). tauto. 
  intro. apply planar_planar_tri_map.  
  apply planar_Flip. tauto.  unfold isWellembed in IW'. 
  decompose [and] IW'. 
  apply illegal_prec_Flip. 
  tauto. tauto. tauto. 
  apply exd_some_illegal. tauto.
   apply illegal_some_illegal. tauto.
  apply (planar_tri_map_planar (exist (fun x : fmap => inv_Triangulation x /\ isWellembed x) m
         (conj IT' IW')) H).  
Qed.

Theorem planar_Delaunay : 
  forall (m : fmap)(IT: inv_Triangulation m)(WE: isWellembed m),  
     planar m -> planar (Delaunay m IT WE). 
Proof.
intros m IT WE PL; unfold Delaunay. 
generalize (planar_planar_tri_map m IT WE PL). 
generalize (exist (fun x : fmap => inv_Triangulation x /\ isWellembed x) m
           (conj IT WE)).  
set(P := fun(s:tri_map)(r:fmap)=> planar_tri_map s -> planar r). 
apply (delaunay'_ind  P). unfold P. 
intros. apply planar_tri_map_planar. tauto. 
unfold P. intros. apply H.
apply planar_step_tri. tauto. 
Qed.

(*================================================================
                          EXTRACTION IN Ocaml
=================================================================*)

Extract Inductive sumbool =>  "bool" [ "true" "false" ].

Extraction "Delaunay.ml"  Delaunay.

(* SEEMS OK *)

(*================================================================
                         END TRIANG05
=================================================================*)
