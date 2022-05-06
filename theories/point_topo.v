From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.analysis Require Import reals classical_sets boolp.
From mathcomp Require Import zify.
Require Import tactics csets_extras.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Open Scope classical_set_scope.
Open Scope real_scope.

(* Topological facts about sets of points in R^d, 
 * in a more elementary way than mathcomp.analysis.topology. *)

Section PointTopo.

Variables (R : realType) (d : nat).
Notation point := 'M[R]_(1, d).

Section EuclidNorm.

Definition norm (x : point) : R := Num.sqrt ((x *m x^T)%R ord0 ord0). 
Lemma norm_scalarMl x (s : R) : (s >= 0)%R -> norm (s%:M *m x) = (s * norm x)%R.
Proof. Admitted.
Lemma norm_scalarMr x (s : R) : (s >= 0)%R -> norm (x *m s%:M) = (s * norm x)%R.
Proof. Admitted.

End EuclidNorm.

Section OpenSets.
Implicit Types (S : set point) (x : point).

(* A simple (i.e. without filters) definition of an open set of points *)
Definition openS_near S x :=
  exists2 eps : R, (eps > 0)%R & forall y, (norm (x - y) <= eps)%R -> S y.
Definition openS S := {in S, forall x, openS_near S x }.

Lemma openS_near_scale S x u : 
  openS_near S x -> exists2 l, (l > 0)%R & S (x + l%:M *m u)%R.
Proof. Admitted.

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

Lemma widen_ord_ante m (i : 'I_m.+1) :
i != ord_max -> exists j : 'I_m, i = widen_ord (leqnSn m) j.
Proof. 
case: i => [i lt_im1] => ne_oiom.
case: (i =P m) => C_im.
- have: Ordinal lt_im1 = ord_max by apply val_inj.
  by move: ne_oiom => /[swap] -> ; rewrite eqxx.
- have lt_im : i < m by lia. exists (Ordinal lt_im).
  by apply val_inj.
Qed.


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
  case: (i =P ord_max) ; [by move-> ; apply Om| |by move: P1i=> /[swap] -> /P1om|] 
    => /eqP /widen_ord_ante[j Hij] ;
  by rewrite Hij ; apply IH ; rewrite /P0 /= -Hij.
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