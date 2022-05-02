From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.analysis Require Import reals classical_sets topology boolp.
From mathcomp Require Import zify.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope classical_set_scope.
Open Scope real_scope.

Section Arrangement.

Variables R : realType.
(* d : dimension of the space.
 * n : number of hyperplanes in the arrangement. *)
Variables (d n : nat).
Hypothesis gt_d1 : d > 1.
Notation point := 'M[R]_(1, d).
(* We create the hyperplane subtype of square matrices *)
Record hplane := Hplane { M :> 'M[R]_(d, d) ; _ : \rank M == d.-1 }.
Canonical hplane_subType := [subType for M].
Lemma hplane_rank (h: hplane) : \rank h = d.-1.
Proof. by apply /eqP ; case: h. Qed.

Variables (H : n.-tuple hplane).

(* A sign represents which side of a hyperplane a point is *)
Inductive sign := Left | On | Right.

Definition I3_of_sign (s : sign) : 'I_3 := 
  match s with Left => inord 0 | On => inord 1 | Right => inord 2 end.
Definition sign_of_I3 (i : 'I_3) : sign :=
  match val i with 0 => Left | 1 => On | _ => Right end.
Lemma I3_of_signK : cancel I3_of_sign sign_of_I3.
Proof. by case ; rewrite /I3_of_sign /sign_of_I3 /= inordK. Qed.

Definition sign_eqMixin := CanEqMixin I3_of_signK.
Canonical sign_eqType := EqType sign sign_eqMixin.
Definition sign_choiceMixin := CanChoiceMixin I3_of_signK.
Canonical sign_choiceType := ChoiceType sign sign_choiceMixin.
Definition sign_countMixin := CanCountMixin I3_of_signK.
Canonical sign_countType := CountType sign sign_countMixin.
Definition sign_finMixin := CanFinMixin I3_of_signK.
Canonical sign_finType := FinType sign sign_finMixin.

Lemma rank_hplaneC (h : hplane) : \rank h^C%MS = 1.
Proof. by rewrite mxrank_compl hplane_rank ; lia. Qed.

Definition hside (x : point) (h : hplane) : sign := 
  let v := row_base h^C%MS in 
  let t : R := (mulmx x v^T) ord0 ltac:(rewrite rank_hplaneC ; exact: ord0) in 
  if (t == 0)%R then On 
  else if (t > 0)%R then Right
  else Left.
  
(* The set of points in the row-space of M *)
Definition Mpoints k (M : 'M[R]_(k, d)) : set point := [set x | (x <= M)%MS ].
(* The set of points Left/On/Right of a hyperplane *) 
Definition hpoints s h : set point := [set x | hside x h == s ].

Lemma Mpoints_id : Mpoints 1%:M = setT.
Proof. by rewrite -subTset /subset /Mpoints => x _ /= ; apply submx1. Qed.

Definition face := n.-tuple sign.
Definition fpoints (f : face) : set point := 
  \bigcap_i hpoints (tnth f i) (tnth H i).
Definition clfpoints (f : face) : set point := 
  \bigcap_i (hpoints (tnth f i) (tnth H i) `|` hpoints On (tnth H i)).
Definition nempty (f : face) : Prop := fpoints f !=set0.

Definition dim f : nat := infimum 0 (mxrank @` [set M : 'M[R]_d | fpoints f `<=` Mpoints M]).

Lemma inf_le (A : set nat) x0 t :
  (exists2 x, A x & x <= t) -> infimum x0 A <= t.
Proof. Admitted.

Lemma inf_ge (A : set nat) x0 t :
  (forall x, A x -> x >= t) -> A !=set0 -> infimum x0 A >= t.
Proof. Admitted. 


Lemma card_set_count m (T : eqType) (t : m.-tuple T) x : 
  #|[set i | tnth t i == x]| = count (xpred1 x) t.
Proof. 
  rewrite cardE /in_set /enum_mem size_filter /= /mem /=.
  rewrite -(@count_map _ _ _ (fun s : T => boolp.asbool (s == x))).
  f_equal.
  - by apply funext => s ; rewrite asboolb.
  - apply (@eq_from_nth _ x) ; rewrite size_map -enumT size_enum_ord.
    + by case: t => /= ; lia.
    + move=> i lt_in. rewrite (nth_map (Ordinal lt_in)) ?size_enum_ord //.
      by rewrite (tnth_nth x) ; f_equal ; rewrite nth_enum_ord //.
Qed.


Lemma fpoints_onNon f :
  let P := [set i | tnth f i == On] in
  fpoints f =
    Mpoints (\bigcap_(i | i \in P) tnth H i)%MS `&`  
    \bigcap_(i in ~`P) hpoints (tnth f i) (tnth H i).
Proof. Admitted.
    
(* This would be the most natural definition of a subface :
Definition subfaceT f g := 
  (dim g = (dim f).+1) /\ (fpoints f `<=` closure (fpoints g)).
 * And we would prove something like the following lemma to obtain a simpler definition :
Lemma clfpointsE g : nempty g -> closure (fpoints g) `<=>` clfpoints g.
 * However this definition would require us to provide a topologicalType 
 * on matrices of reals, and then manipulate the closure operation, 
 * which is defined with filters. *)

(* This is a more convenient definition of subface : we will only work with this one. *)
Definition subface f g : Prop := 
  (dim g = (dim f).+1) /\ (fpoints f `<=` clfpoints g).

Lemma image_nonempty aT rT (f : aT -> rT) (A : set aT) :
  A !=set0 -> [set f x | x in A] !=set0.
Proof. by case => [x Ax] ; exists (f x) ; exists x. Qed.

Lemma hplane_cap_rank_lb (P : set 'I_n) : \rank (\bigcap_(i in P) tnth H i) >= d - #|P|.
Proof. Admitted.


Definition norm (x : point) : R := Num.sqrt ((x *m x^T)%R ord0 ord0). 
Lemma norm_scalarMl x (s : R) : (s >= 0)%R -> norm (s%:M *m x) = (s * norm x)%R.
Proof. Admitted.
Lemma norm_scalarMr x (s : R) : (s >= 0)%R -> norm (x *m s%:M) = (s * norm x)%R.
Proof. Admitted.

(* A simple (i.e. without filters) definition of an open set of points *)
Definition openS_near (S : set point) x :=
  exists2 eps : R, (eps > 0)%R & forall y, (norm (x - y) <= eps)%R -> S y.
Definition openS (S : set point) := forall x, S x -> openS_near S x.

Lemma openS_near_scale S (x u : point) : 
  openS_near S x -> exists2 l, (l > 0)%R & S (x + l%:M *m u)%R.
Proof. Admitted.

Lemma open_Non f : 
  let P := [set i | tnth f i == On] in
  openS (\bigcap_(i in ~`P) hpoints (tnth f i) (tnth H i)).
Proof. Admitted.

Lemma Csubset1 T (A : set T) (x : T) : ([set x] `<=` A) = (x \in A).
Proof. Admitted.

Lemma submx_lin (x y : point) (l : R) (M : 'M[R]_d) : 
  ((x + l%:M *m y)%R <= M)%MS -> (l > 0)%R -> (x <= M)%MS -> (y <= M)%MS.
Proof. Admitted.

Lemma dim_lb (f : face) : nempty f -> dim f >= d - count (xpred1 On) f.
Proof.
  move=> NEf. apply inf_ge ; last first.
    by apply image_nonempty ; exists 1%:M%R => /= ; rewrite Mpoints_id ; apply subsetT.
  move=> r /= [M points_fM <-] ; move: NEf (@open_Non f) points_fM. 
  rewrite /nempty /openS -card_set_count fpoints_onNon ; 
  remember ([set i | tnth f i == On]) as P ; rewrite -HeqP ;
  remember (\bigcap_(i in P) tnth H i)%MS as K ;
  remember (\bigcap_(i in ~`P) hpoints (tnth f i) (tnth H i)) as S ; rewrite -HeqS.
  move=> [x /= [Kx Sx]] /(_ x Sx) O_Sx KSM ; rewrite /Mpoints /= in Kx.
  have KiM : forall i, row i K \in Mpoints M => [i|].
    move: (openS_near_scale (row i K) O_Sx) => [l lt_0l S_x_lKi].
    have K_x_lKi : (x + l%:M *m row i K)%R \in Mpoints K.
      by rewrite inE /Mpoints /= ; apply addmx_sub => // ;
      apply mulmx_sub ; apply row_sub.
    have M_x_lKi : (x + l%:M *m row i K)%R \in Mpoints M ; [|clear K_x_lKi S_x_lKi].
      rewrite -Csubset1 ; apply (@subset_trans _ (Mpoints K `&` S)) => // ; rewrite Csubset1.
      rewrite in_setI ; apply /andP ; split ; [apply K_x_lKi|rewrite inE ; apply S_x_lKi].
    have Mx : x \in Mpoints M.
      rewrite -Csubset1 ; apply (@subset_trans _ (Mpoints K `&` S)) => // ; rewrite Csubset1.
      rewrite in_setI ; apply /andP ; split ; rewrite inE ?/Mpoints //=.
    rewrite !inE /Mpoints /= in M_x_lKi Mx * ; apply (@submx_lin x _ l) => //.
  have KM : (K <= M)%MS.
    by apply /row_subP => i ; move: (KiM i) ; rewrite inE /Mpoints /=.
  apply (@leq_trans (\rank K)) ; last by apply mxrankS.
  by rewrite HeqK hplane_cap_rank_lb.
Qed.


Section SimpleArrangement.

(* Since I only study arrangements in which all hyperplanes 
 * contain the origin, a simple arrangement can only have 
 * at most d hyperplanes. To simplify I also suppose that n = d. *)
Hypothesis eq_nd : n = d.
Hypothesis simple : \rank (\bigcap_(i : 'I_n) tnth H i) == 0.

Lemma simple_ext (P : set 'I_n) : 
  \rank (\bigcap_(i in P) tnth H i) <= d - #|P|.
Proof. Admitted.

Lemma simple_dim_ub f : dim f <= d - count (xpred1 On) f.
Proof.
  rewrite /dim ; apply inf_le.
  rewrite fpoints_onNon ; 
  remember [set i | tnth f i == On] as P ; rewrite -HeqP ;
  remember (\bigcap_(i in P) tnth H i)%MS as M.
  exists (\rank M).
    by apply imageP ; rewrite mksetE ; apply subIsetl.
  rewrite HeqM ; apply (leq_trans (simple_ext _)).
  by apply eq_leq ; congr (_ - _) ; rewrite HeqP card_set_count.
Qed.


Lemma simple_dim_eq f : nempty f -> dim f = d - count (xpred1 On) f.
Proof. by move=> NEf ; apply /eqP ; rewrite eqn_leq simple_dim_ub dim_lb. Qed.

End SimpleArrangement.

