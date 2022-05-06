From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.analysis Require Import reals classical_sets boolp.
From mathcomp Require Import zify algebra_tactics.ring.
Require Import tactics csets_extras point_topo.

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

Lemma is_true_inj : injective is_true.
Proof. 
  move=> a b ; case: a ; case: b => //= ;  
  move: (@iffP (is_true true) (is_true false) true (@idP true)) => H0 H1.
  - by feed_n 2 H0 ; [by rewrite H1 .. |] ; case: H0.
  - by feed_n 2 H0 ; [by rewrite H1 .. |] ; case: H0.
Qed.

Lemma nat_of_bool_inj : injective nat_of_bool.
Proof. by move=> a b ; case: a ; case: b. Qed. 


Lemma Mhcap_rank_lb (M : 'M[R]_d) (h : hplane) : 
  \rank (M :&: h) >= \rank M - 1.
Proof. by move: (mxrank_sum_cap M h) (rank_leq_col (M + h)%MS) ; rewrite hplane_rank ; lia. Qed.

Lemma hplane_cap_lb (P : set 'I_n) : \rank (\bigcap_(i in P) tnth H i) >= d - #|P|.
Proof. 
  elim: n P H => [|n0 IH] P0 H0.
    by rewrite big_ord0 mxrank1 ; lia.
  unlock index_enum ; rewrite /= -enumT mathcomp_extra.enum_ordS.
  rewrite -cats1 big_cat /= big_map [in X in _ <= \rank (_ :&: X)]big_mkcond big_seq1 /=.
  pose H1 := [tuple tnth H0 (widen_ord (leqnSn n0) i) | i < n0].
  have H1i i : tnth H1 i = tnth H0 (widen_ord (leqnSn n0) i).
    by rewrite /H1 tnth_mktuple.
  pose P1 := [set i | widen_ord (leqnSn n0) i \in P0].
  have P1i i : i \in P1 = (widen_ord (leqnSn n0) i \in P0).
    by apply is_true_inj ; rewrite /P1 !in_setE /= !in_setE.
  case: ifP ; [rewrite -(leqRW (Mhcap_rank_lb _ _)) | rewrite capmx1] ;
  under eq_big => [i|i Pi] do [rewrite -P1i|rewrite -H1i] ;
  move: (IH P1 H1) ; unlock index_enum ; rewrite /= -enumT => IH1 OmP0 ; rewrite -(leqRW IH1) ;
  apply eq_leq ; [rewrite -subnDA|] ; congr (_ - _) ;
  rewrite /P1 !card_set_sum big_ord_recr OmP0 /= ; [congr (_ + _) | rewrite addn0] ;
  by apply eq_big => [//|i _] ; f_equal ; apply is_true_inj ; rewrite !in_setE /= in_setE.
Qed.



Lemma openS_Non_hplane (h : hplane) s : s != On -> openS (hpoints s h).
Proof. 
  rewrite /openS /openS_near => Non x shx.
  pose V := h^C%MS. Search proj_mx.
  move: (@add_proj_mx _ _ _ h V x) => decomp ; feed_n 2 decomp.
    by rewrite /V capmx_compl.
    by apply submx_full, addsmx_compl_full.
Admitted.
  
Lemma openS_Non (f : face) : 
  let P := [set i | tnth f i == On] in
  openS (\bigcap_(i in ~`P) hpoints (tnth f i) (tnth H i)).
Proof. by apply openS_cap => i /= /negP ; apply openS_Non_hplane. Qed.


Lemma submx_lin (x y : point) (l : R) (M : 'M[R]_d) : 
  ((x + l%:M *m y)%R <= M)%MS -> (l > 0)%R -> (x <= M)%MS -> (y <= M)%MS.
Proof. Admitted.

Lemma fdim_lb (f : face) : nempty f -> dim f >= d - count (xpred1 On) f.
Proof.
  move=> NEf. apply inf_ge ; last first.
    by apply image_nonempty ; exists 1%:M%R => /= ; rewrite Mpoints_id ; apply subsetT.
  move=> r /= [M points_fM <-] ; move: NEf (@openS_Non f) points_fM. 
  rewrite /nempty /openS -card_set_count fpoints_onNon ; 
  remember ([set i | tnth f i == On]) as P ; rewrite -HeqP ;
  remember (\bigcap_(i in P) tnth H i)%MS as K ;
  remember (\bigcap_(i in ~`P) hpoints (tnth f i) (tnth H i)) as S ; rewrite -HeqS.
  move=> [x /= [Kx Sx]] /in_setP/(_ x Sx) O_Sx KSM ; rewrite /Mpoints /= in Kx.
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
  by rewrite HeqK hplane_cap_lb.
Qed.


Section SimpleArrangement.

(* Since I only study arrangements in which all hyperplanes 
 * contain the origin, a simple arrangement can only have 
 * at most d hyperplanes. To simplify I also suppose that n = d. *)
Hypothesis eq_nd : n = d.
Definition simple := \rank (\bigcap_(i : 'I_n) tnth H i) = 0.
Hypothesis sH : simple.

Lemma bigcap1U m a i0 (P : set 'I_m) (F : 'I_m -> 'M[R]_a) :
  (\bigcap_(i in (i0 |` P)) F i = F i0 :&: \bigcap_(i in P) F i)%MS.
Proof. Admitted.

Lemma lia_test (M : 'M[R]_d) (P : set 'I_n) (k : nat) : 0 < d - #|P| -> \rank M <= (d - #|P|.+1) + 1 -> \rank M <= d - #|P|.
Proof. lia. Qed.

Lemma hplane_cap_eq (P : set 'I_n) : 
  \rank (\bigcap_(i in P) tnth H i) = d - #|P|.
Proof. 
  elim /finset_ind_rev : P => /= [|i0 P N_Px].
    by under eq_big do [rewrite in_setT|] ; rewrite sH card_setT /= card_ord ; lia.
  rewrite set1U_disj_card // bigcap1U.
  remember (\bigcap_(i in P) tnth H i)%MS as M ; rewrite -HeqM => IH.
  suff: \rank M <= d - #|P|.
    move: (hplane_cap_lb P) ; rewrite -HeqM => LB UB. 
    by apply /eqP ; rewrite eqn_leq UB LB.
  have MHi0C : (M :&: tnth H i0 == tnth H i0 :&: M)%MS by rewrite capmxC submx_refl.
  move: (Mhcap_rank_lb M (tnth H i0)).
  move: (Nin_card_ltT N_Px) ; rewrite card_ord [n in _ < n]eq_nd => lt_Pd.
  rewrite (eqmx_rank MHi0C) IH -(leq_add2r 1) subnK.
  rewrite -addn1 subnDA subnK //. 
  rewrite -(leq_add2r #|P|) subnK // ; first by apply ltnW. 
  rewrite HeqM -(leqRW (hplane_cap_lb P)). 
  by rewrite -(leq_add2r #|P|) subnK // ; apply ltnW.
Qed. 
  
Lemma fdim_ub f : dim f <= d - count (xpred1 On) f.
Proof.
  rewrite /dim ; apply inf_le.
  rewrite fpoints_onNon ; 
  remember [set i | tnth f i == On] as P ; rewrite -HeqP ;
  remember (\bigcap_(i in P) tnth H i)%MS as M.
  exists (\rank M).
    by apply imageP ; rewrite mksetE ; apply subIsetl.
  rewrite HeqM hplane_cap_eq ; apply eq_leq. 
  by congr (_ - _) ; rewrite HeqP card_set_count.
Qed.


Lemma dim_eq f : nempty f -> dim f = d - count (xpred1 On) f.
Proof. by move=> NEf ; apply /eqP ; rewrite eqn_leq fdim_ub fdim_lb. Qed.

End SimpleArrangement.

End Arrangement.
