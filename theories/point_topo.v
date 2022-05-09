From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.analysis Require Import reals classical_sets boolp.
From mathcomp Require Import zify algebra_tactics.ring.
Require Import tactics mathcomp_extras.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.
Open Scope classical_set_scope.
Open Scope real_scope.

(* Topological facts about sets of points in R^d, 
 * in a more elementary way than mathcomp.analysis.topology. *)

Section PointTopo.

Variables (R : realType) (d : nat).
Notation point := 'M[R]_(1, d).

Section EuclidNorm.
Implicit Types (x y : point) (s t : R).
Open Scope ring_scope.

Definition norm (x : point) : R := Num.sqrt ((x *m x^T) ord0 ord0). 

Lemma norm_scalel x (s : R) : norm (s *: x) = `|s| * norm x.
Proof. 
  rewrite /norm trmx_scale scale_mulmx mxE -expr2 sqrtrM.
  by rewrite sqrtr_sqr.
  by rewrite sqr_ge0.
Qed.

Lemma norm_scaler x (s : R) : norm (s *: x) = norm x * `|s|.
Proof. by rewrite norm_scalel mulrC. Qed.

Lemma norm_ge0if x : (0 <= norm x ?= iff (x == 0))%R.
Proof. 
  split ; first by rewrite sqrtr_ge0.
  apply /idP ; case: ifP => [/eqP ->|].
    by rewrite /norm mul0mx mxE sqrtr0.
  move /negbT => H ; apply /idP ; move: H ; apply contra.
  rewrite eq_sym /norm sqrtr_eq0 => xxT_le0.
  apply /eqP ; apply matrixP => i j ; rewrite mxE.
  have: i = 0 by case: i => [i Hi] ; apply val_inj => /= ; lia. move->.
  have xxT_ge0 : (x *m x^T) ord0 ord0 >= 0.
    by rewrite mxE ; apply sumr_ge0if => k _ ; rewrite mxE -expr2 sqr_ge0.
  have xxT_eq0 : (x *m x^T) ord0 ord0 == 0.
    by rewrite Order.POrderTheory.eq_le xxT_le0 xxT_ge0.
  clear xxT_ge0 xxT_le0 ; move: xxT_eq0.
  rewrite mxE eq_sym sumr_ge0if /= ; last first => [k _ | /forallP /(_ j)].
    by rewrite mxE -expr2 sqr_ge0.
  by rewrite mxE -expr2 sqrf_eq0 => /eqP ->. 
Qed.

Lemma norm0 : norm 0 = 0.
Proof. 
  move: (eqxx (GRing.zero (matrix_zmodType R 1 d))). 
  by rewrite -norm_ge0if eq_sym => /eqP.
Qed. 

Lemma normN x : norm (-x) = norm x.
Proof. by rewrite -scaleN1r norm_scalel normrN1 mul1r. Qed.

End EuclidNorm.

Section OpenSets.
Implicit Types (S : set point) (x : point).

(* A simple (i.e. without filters) definition of an open set of points *)
Definition openS_near S x :=
  exists2 eps : R, (eps > 0)%R & forall y, (norm (x - y) <= eps)%R -> S y.
Definition openS S := {in S, forall x, openS_near S x }.

Lemma openS_near_scale S x u : 
  openS_near S x -> exists2 l, (l > 0)%R & S (x + l%:M *m u)%R.
Proof. 
  rewrite /openS_near /= => [[eps eps_gt0 Heps]].
  case: (u =P 0)%R => [->|neq_u0].
    exists (GRing.one (Num.NumDomain.ringType R)) => //.
    rewrite mulmx0 addr0 ; apply Heps.
    by rewrite subrr norm0 ; apply Order.POrderTheory.ltW.
  have l_gt0 : (0 < eps / norm u)%R.
    apply mulr_gt0 ; rewrite ?invr_gt0 //.
    move: neq_u0=> /eqP ; apply contraR ; rewrite -Order.TotalTheory.leNgt => H.
    by rewrite -norm_ge0if Order.POrderTheory.eq_le H norm_ge0if.
  exists (eps / norm u)%R => //.
  apply Heps ; rewrite opprD addrA subrr sub0r normN mul_scalar_mx norm_scalel.
  rewrite gtr0_norm // -mulrA mulVr ?mulr1 //.
  by rewrite unitfE eq_sym norm_ge0if ; apply /eqP.
Qed.

Lemma openS_setT : openS (@setT point).
Proof. 
  rewrite /openS /openS_near /= => x _.
  by exists (GRing.one (Num.NumDomain.ringType R)).
Qed.

Lemma le_min (x y z : R) : (x <= Num.min y z)%R <-> (x <= y)%R && (x <= z)%R.
Proof. Admitted.
  (*case: (Num.Theory.ltrP y z) => [/Order.POrderTheory.ltW|] Oyz ;
  apply is_true_inj ; apply propext ; split.
  - move=> le_xy. apply /andP ; split => //. Search transitive. apply Order.MeetJoinMixin.le_trans.*)

Lemma openS_near_cap m (P : set 'I_m) F x :
  (forall i, P i -> openS_near (F i) x) -> 
  openS_near (\bigcap_(i in P) F i) x.
Proof.
  elim: m F P => [|m IH] F1 P1 Oi.
    exists (GRing.one (Num.NumDomain.ringType R)) => // y _ i.
    by rewrite (set_ord0 P1) /=.
  pose F0 := (fun i : 'I_m => F1 (widen_ord (leqnSn m) i)).
  pose P0 := [set i | P1 (widen_ord (leqnSn m) i)].
  have Oi' : forall i : 'I_m, P0 i -> openS_near (F0 i) x => [i|].
    by rewrite /P0 /F0 /= ; apply Oi.
  move: (Oi ord_max) (IH F0 P0 Oi') ; rewrite /openS_near /= => Om {}IH.
  case: (asboolP (P1 ord_max)) IH => P1om [e1 lt_0e1 IH] ;
  [move: P1om=> /Om [e2 lt_0e2 {}Om]|pose e2 := e1] ;
  exists (Num.min e1 e2) ; (try by case: (Num.Theory.ltrP e1 e2)) ;
  rewrite /bigcap /= => y /le_min/andP[le_De1 le_De2] i P1i ;
  move: (IH y le_De1) ; rewrite /bigcap /= => {}IH ;
  case: (widen_ordP i) P1i => [ |j] P1i.
  - by apply Om.
  - by apply IH ; rewrite /P0 //=.
  - by intuition.
  - by apply IH ; rewrite /P0 //=. 
Qed.

Lemma openS_cap m (P : set 'I_m) F :
  (forall i, P i -> openS (F i)) -> openS (\bigcap_(i in P) F i).
Proof. 
  rewrite /bigcap /openS /= => Oi x ; rewrite in_setE /= => Fx.
  apply openS_near_cap => /= i Pi ; apply Oi => //. 
  by rewrite in_setE ; apply Fx.
Qed.


End OpenSets.

End PointTopo.