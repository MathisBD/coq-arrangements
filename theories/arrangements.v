From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.analysis Require Import reals classical_sets boolp.
From mathcomp Require Import zify algebra_tactics.ring.
Require Import tactics mathcomp_extras point_topo.

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

Lemma hsideE x h : hside x h == On <-> (x <= h)%MS.
Proof. 
  split => sub_xh ; last first.
  - remember (row_base h^C%MS) as V.
    remember ((x *m V^T) ord0 (eq_rect_r [eta ordinal] ord0 (rank_hplaneC h)))%R as t.
    suff: t = 0%R => [eq_t0|].
      by rewrite /hside ; case: ifP => // /negbT ; case: ifP => [|/negbT] ; rewrite -HeqV -Heqt eq_t0 eqxx.
Admitted.  
  
Lemma hpoints_On h : hpoints On h = Mpoints h.
Proof. by rewrite /hpoints /Mpoints eqEsubset ; split => x /= ; rewrite hsideE. Qed.


Lemma Mpoints_id : Mpoints 1%:M = setT.
Proof. by rewrite -subTset /subset /Mpoints => x _ /= ; apply submx1. Qed.

Lemma Mpoints_cap2 (A B : 'M[R]_d) : Mpoints (A :&: B)%MS = Mpoints A `&` Mpoints B.
Proof. by rewrite /Mpoints eqEsubset ; split => x /= ; rewrite sub_capmx ; move=> /andP. Qed.

Lemma Mpoints_cap m (P : set 'I_m) (F : 'I_m -> 'M[R]_d) :
  Mpoints (\bigcap_(i in P) F i)%MS = \bigcap_(i in P) Mpoints (F i).
Proof.
  elim /finset_ind : P => [|i0 P NPi0 IH].
    under eq_bigl => i do rewrite in_set0. 
    by rewrite big_pred0 // Mpoints_id ; symmetry ; rewrite -subTset /bigcap => x /=.
  rewrite bigcap_setU1 -IH -Mpoints_cap2 ; f_equal.
  rewrite (bigID (xpred1 i0)) /= ; congr (_ :&: _)%MS. 
  - under eq_bigl => i. rewrite andb_idl => [|/eqP->]. over. 
      by rewrite in_setE /= ; intuition.
    by rewrite big_pred1_eq.
  - have cond i : (i \in i0 |` P) && (i != i0) = (i \in P). 
      apply /eqP ; rewrite eqE /= /eqb /addb ; case: ifP => [|/negbT].
      + rewrite negb_and => /orP[] ; last by rewrite negbK => /eqP->.
        by apply contra ; rewrite !in_setE /= ; intuition.
      + rewrite negbK => /andP[] ; rewrite !in_setE /= => [[->|//]].
        by rewrite eqxx.
    by under eq_bigl do rewrite cond.
Qed.

Definition face := n.-tuple sign.
Definition fpoints (f : face) : set point := 
  \bigcap_i hpoints (tnth f i) (tnth H i).
Definition clfpoints (f : face) : set point := 
  \bigcap_i (hpoints (tnth f i) (tnth H i) `|` hpoints On (tnth H i)).
Definition nempty (f : face) : Prop := fpoints f !=set0.

Lemma fpointsP f x : 
  reflect (forall i, hside x (tnth H i) = tnth f i) (x \in fpoints f).
Proof.
  apply (iffP idP) ; rewrite /fpoints /bigcap in_setE /= => P i.
  - by move: (P i I) ; rewrite /hpoints /= => /eqP.
  - by rewrite /hpoints /= P.
Qed.

Lemma clfpointsP f x :
  reflect (forall i, hside x (tnth H i) = tnth f i \/ hside x (tnth H i) = On)
    (x \in clfpoints f).
Proof.
  apply (iffP idP) ; rewrite /clfpoints /bigcap in_setE /= => P i.
  - by move: (P i I) ; rewrite /hpoints /= ; move=> [/eqP->|/eqP->] ; auto.
  - by rewrite /hpoints /= ; case: (P i) => -> ; auto.
Qed.

Lemma eqEfpoints f f' : nempty f -> (f == f') = (fpoints f == fpoints f'). 
Proof.
  move=> [x fx]. 
  apply is_true_inj, propext ; split => [/eqP-> //|/eqP points_ff'].
  Search eq tnth in tuple. 
  apply /eqP ; apply eq_from_tnth => i.
  move: (fx) ; rewrite -in_setE => /fpointsP /(_ i) <-.
  by apply /fpointsP ; rewrite in_setE -points_ff'.
Qed. 


Definition dim f : nat := infimum 0 (mxrank @` [set M : 'M[R]_d | fpoints f `<=` Mpoints M]).

Lemma dim_led f : dim f <= d.
Proof. 
  apply inf_le ; exists d => //= ; exists 1%:M%R ; last by rewrite mxrank1.
  by rewrite /Mpoints ; under eq_set do rewrite submx1 /=.
Qed.

(* This would be the most natural definition of a subface :
Definition subfaceT f g := 
  (dim g = (dim f).+1) /\ (fpoints f `<=` closure (fpoints g)).
 * And we would prove something like the following lemma to obtain a simpler definition :
Lemma clfpointsE g : nempty g -> closure (fpoints g) `<=>` clfpoints g.
 * However this definition would require us to provide a topologicalType 
 * on matrices of reals, and then manipulate the closure operation, 
 * which is defined with filters. *)

(* This is a more convenient definition of subface : we will only work with this one. *)
Inductive subface f g : Prop := 
  Subface of nempty f & nempty g & fpoints f `<=` clfpoints g & dim g = (dim f).+1.

Lemma face_inclP f g : nempty f -> 
  reflect (fpoints f `<=` clfpoints g) [forall i, (tnth f i == On) || (tnth f i == tnth g i)].
Proof.
  move=> NE_f ; apply (iffP idP) => [/forallP P x|].
  - rewrite -in_setE => /fpointsP Hf.
    rewrite -in_setE ; apply /clfpointsP => i.
    by rewrite Hf ; case: (orP (P i)) => /eqP ; intuition.
  - move: NE_f => [x fx] /(_ x fx) Hg ; apply /forallP => i.
    move: fx ; rewrite -in_setE => /fpointsP /(_ i) Hf.
    move: Hg ; rewrite -in_setE => /clfpointsP /(_ i).
    by rewrite Hf ; move=> [->|->] ; rewrite eqxx ?orbT ?orTb. 
Qed.

Lemma fpoints_onNon f :
  let P := [set i | tnth f i == On] in
  fpoints f =
    Mpoints (\bigcap_(i in P) tnth H i)%MS `&`  
    \bigcap_(i in ~`P) hpoints (tnth f i) (tnth H i).
Proof. 
  remember [set i | tnth f i == On] as P => /=.
  rewrite /fpoints [in LHS](bigcapID P) !setTI ; congr (_ `&` _).
  under eq_bigcapr => i do [rewrite [in P i]HeqP /= => /eqP-> ; rewrite hpoints_On].
  by rewrite Mpoints_cap.
Qed.

(* calculates the orthogonal space of M *)
(*Definition orthoM (M : 'M[R]_d) : 'M[R]_d := *)


Lemma openS_Non_hplane (h : hplane) s : s != On -> openS (hpoints s h).
Proof. 
  rewrite /openS /openS_near => Non x shx.
  pose V := h^C%MS.
  move: (@add_proj_mx _ _ _ h V x) => decomp ; feed_n 2 decomp.
    by rewrite /V capmx_compl.
    by apply submx_full, addsmx_compl_full.
  
Admitted.
  
Lemma openS_Non (f : face) : 
  let P := [set i | tnth f i == On] in
  openS (\bigcap_(i in ~`P) hpoints (tnth f i) (tnth H i)).
Proof. by apply openS_cap => i /= /negP ; apply openS_Non_hplane. Qed.


Lemma Mhcap_rank_lb (h : hplane) (M : 'M[R]_d) : 
  \rank (M :&: h) >= \rank M - 1.
Proof. by move: (mxrank_sum_cap M h) (rank_leq_col (M + h)%MS) ; rewrite hplane_rank ; lia. Qed.

Lemma Mhcap_rank_eq (h : hplane) (M : 'M[R]_d) : 
  \rank M = \rank (M :&: h) + ~~(M <= h)%MS.
Proof. 
  (case E: (M <= h)%MS ; move: E) => [/idP /capmx_idPl /eqmxP /eqmx_rank->|/negbT NS_Mh] /= ; try lia.
  apply /eqP ; move: NS_Mh ; apply contraR.
  have /orP : (\rank (M :&: h) == \rank M) || (\rank (M :&: h) + 1 == \rank M).
    suff: \rank M - 1 <= \rank (M :&: h) <= \rank M ; [lia|].
    by rewrite Mhcap_rank_lb /= ; apply mxrankS, capmxSl.
  case => [rMhM _ | /eqP] ; last by lia.
  apply /capmx_idPl /eqmxP /andP ; split ; first by apply capmxSl.
  by rewrite -mxrank_leqif_sup // capmxSl.
Qed.

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

Lemma submx_lin (x y : point) (l : R) (M : 'M[R]_d) : 
  ((x + l%:M *m y)%R <= M)%MS -> (l > 0)%R -> (x <= M)%MS -> (y <= M)%MS.
Proof. 
  move=> xlyM lt_0l xM.
  have lyM : ((l%:M *m y)%R <= M)%MS.
    rewrite -[(l%:M *m y)%R]GRing.add0r -(GRing.subrr x).
    rewrite -GRing.addrAC. 
    by apply addmx_sub ; rewrite // -GRing.scaleN1r ; apply scalemx_sub.
  rewrite -[y](@GRing.scalerK _ _ l). 
  - by rewrite -!mul_scalar_mx ; apply mulmx_sub.
  - by apply Num.Theory.lt0r_neq0.
Qed. 


Lemma dimE f : 
  nempty f -> dim f = \rank \bigcap_(i | tnth f i == On) tnth H i.
Proof.
  have cond i : (tnth f i == On) = (i \in [set i | tnth f i == On]).
    by apply is_true_inj ; rewrite in_setE /=.
  under eq_bigl do rewrite cond.
  move=> NEf. 
  apply /eqP ; rewrite eqn_leq ; apply /andP ; split ; last first.
  - apply inf_ge ; last first.
      by apply image_nonempty ; exists 1%:M%R => /= ; rewrite Mpoints_id ; apply subsetT.
    move=> r /= [M points_fM <-] ; move: NEf (@openS_Non f) points_fM. 
    rewrite /nempty /openS fpoints_onNon.
    remember ([set i | tnth f i == On]) as P ; rewrite -?HeqP.
    remember (\bigcap_(i in P) tnth H i)%MS as K ; rewrite -?HeqK.
    remember (\bigcap_(i in ~`P) hpoints (tnth f i) (tnth H i)) as S ; rewrite -?HeqS.
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
    by apply mxrankS.
  - apply inf_le ; rewrite fpoints_onNon.
    remember ([set i | tnth f i == On]) as P ; rewrite -?HeqP.
    remember (\bigcap_(i in P) tnth H i)%MS as K ; rewrite -?HeqK.
    by exists (\rank K) => //= ; exists K.
Qed.

Lemma fdim_lb (f : face) : nempty f -> dim f >= d - count (xpred1 On) f.
Proof.
  move=> NEf ; rewrite dimE //.
  have cond i : (tnth f i == On) = (i \in [set i | tnth f i == On]).
    by apply is_true_inj ; rewrite in_setE /=.
  under eq_bigl do rewrite cond.
  by rewrite -card_set_count hplane_cap_lb.
Qed.
  
Lemma subface_exist g : nempty g -> dim g > 0 -> exists f, subface f g.
Proof. Admitted.


Lemma face_Ofg_reduce f g i0 :
  let Of := [set j | (tnth f j == On) && (tnth g j != On)] in
  let Og := [set j | tnth g j == On] in
  subface f g -> i0 \in Of ->
  (\bigcap_(i in Of `|` Og) tnth H i == \bigcap_(i in i0 |` Og) tnth H i)%MS.
Proof. 
  pose Of := [set j | (tnth f j == On) && (tnth g j != On)].
  pose Og := [set j | tnth g j == On].
  rewrite /= -/Og -/Of => sub_fg Of_i0.
  rewrite -(mxrank_leqif_eq _) ; last first.
    by apply mxbigcap_sub => i ; move: Of_i0 ; rewrite !in_setE /= => [+ [->|]] ; intuition.
  have -> : \rank (\bigcap_(i in Of `|` Og) tnth H i) = dim f.
    rewrite dimE ; [f_equal ; apply eq_bigl => i | by case: sub_fg].
    apply is_true_inj ; rewrite in_setE /Og /Of /= ; apply propext ; split ; last first.
      move=> -> /= ; case: (tnth g i =P On) ; intuition.
    case => [/andP[->] //|].
    case: sub_fg => NE_f _ /face_inclP /forallP Hfg _.
    by case: (orP (Hfg NE_f i)) => [|/eqP->].
  rewrite (eqmxP (mxbigcap1U _ _)) ; last first.
    by move: Of_i0 ; rewrite /Of /Og in_setE /= notin_set /= => /andP[_ /negP].
  have Rg : \rank (\bigcap_(i in Og) tnth H i)%MS = dim g.
    rewrite dimE ; [f_equal ; apply eq_bigl => i | by case: sub_fg].
    by apply is_true_inj ; rewrite in_setE /Og /=.
  suff Nsub : ~~ (\bigcap_(i in Og) tnth H i <= tnth H i0)%MS.
    move: (Mhcap_rank_eq (tnth H i0) (\bigcap_(i in Og) tnth H i)%MS).
    by rewrite Rg Nsub /= capmxC ; case: sub_fg => _ _ _ ; lia.
  move: Of_i0 ; rewrite in_setE /Of /= ; apply contraL ; rewrite negb_and negbK.
  have [x /[dup] gx] : nempty g by case: sub_fg.
  rewrite fpoints_onNon /Mpoints /= -/Og => [[sub1 _]] sub2.
  have {sub1} {sub2} /hsideE : (x <= tnth H i0)%MS by eapply submx_trans ; eauto.
  by move: gx ; rewrite -in_setE => /fpointsP /(_ i0) -> ; intuition.
Qed.

Lemma face_Ofg_sub f g : 
  let Of := [set j | (tnth f j == On) && (tnth g j != On)] in
  let Og := [set j | tnth g j == On] in
  subface f g -> 
  (fpoints f `<=` Mpoints (\bigcap_(i in Of `|` Og) tnth H i)%MS).
Proof.
  pose Of := [set j | (tnth f j == On) && (tnth g j != On)].
  pose Og := [set j | tnth g j == On].
  rewrite /= fpoints_onNon -/Og -/Of => sub_fg.
  have cond i : i \in Of `|` Og = (i \in [set j | tnth f j == On]).
    apply is_true_inj ; rewrite !in_setE /Of /Og /= ; apply propext ; split ; last first.
      by move=> -> /= ; case: (tnth g i =P On) ; intuition.
    case => [/andP[->] //|].
    case: sub_fg => NE_f _ /face_inclP /forallP Hfg _.
    by case: (orP (Hfg NE_f i)) => [|/eqP->].
  by under eq_bigl do rewrite cond ; apply subIsetl.
Qed.

(* With On(f) = [set i | f i = On], this lemma says that
 * the sets (On(f) \ On(g)) when f ranges over the subfaces of g are disjoint *)
Lemma subfaces_disjoint f f' g i : 
  subface f g -> subface f' g ->
  tnth f i == On -> tnth f' i == On -> tnth g i != On -> f = f'.
Proof. 
  move=> sub_fg sub_f'g fi f'i gi.
  pose Of := [set j | (tnth f j == On) && (tnth g j != On)].
  pose Of' := [set j | (tnth f' j == On) && (tnth g j != On)].
  pose Og := [set j | tnth g j == On].
  apply eq_from_tnth => j.
  suff: j \in Of \/ j \in Of' -> tnth f j = tnth f' j.
    (case E: ((j \in Of) || (j \in Of')) ; move: E) => [/idP /orP|/negbT] ; first by intuition.
    rewrite negb_or -!in_setC /Of /Of' => /andP [+ +] _.
    rewrite !in_setE /= => /idP + /idP ; rewrite !negb_and !negbK => /orP H1 /orP H2.
    have Hfg : (tnth f j = On) \/ (tnth f j = tnth g j).
      case: sub_fg => NE_f _ /face_inclP fiP _ ; feed fiP ; first by [].
      by move: fiP => /forallP /(_ j) /orP[|] /eqP-> ; intuition.
    have Hf'g : (tnth f' j = On) \/ (tnth f' j = tnth g j).
      case: sub_f'g => NE_f' _ /face_inclP f'iP _ ; feed f'iP ; first by [].
      by move: f'iP => /forallP /(_ j) /orP[|] /eqP-> ; intuition.
    have HhOn : tnth g j == On -> tnth f j = tnth f' j.
      move=> /eqP H3 ; rewrite H3 in Hfg Hf'g.
      by case: Hfg ; case: Hf'g => -> ->.
    case: H1 ; case: H2 ; try auto.
    move=> /eqP + /eqP ; intuition ; last by eapply eq_trans ; eauto.
  wlog : f f' sub_fg sub_f'g fi f'i @Of @Of' / (j \in Of) => [|Ofj _].
    by move=> HW [|] Hj ; [|symmetry] ; eapply HW => // ; rewrite -/Of -/Of' ; intuition.
  have [x f'x] : nempty f' by case: sub_f'g.
  suff : hside x (tnth H j) == On.
    move: Ofj ; rewrite /Of in_setE /= => /andP[/eqP-> _] /eqP.
    by move: f'x ; rewrite -in_setE => /fpointsP /(_ j) -> ->.
  have Ofi : i \in Of by rewrite /Of in_setE /= ; apply /andP.
  have Of'i : i \in Of' by rewrite /Of' in_setE /= ; apply /andP.
  move: (face_Ofg_reduce sub_fg Ofi) (face_Ofg_reduce sub_f'g Of'i) ; 
    rewrite -/Of -/Of' -/Og => /andP[_ Ofg_red] /andP[Of'g_red _].
  move: (face_Ofg_sub sub_f'g) ; rewrite -/Of' -/Og /Mpoints => /(_ x f'x) /= => x_Of'g.
  have: (x <= \bigcap_(i in (Of `|` Og)) tnth H i)%MS.
    eapply submx_trans ; first apply x_Of'g.
    eapply submx_trans ; first apply Of'g_red.
    by apply Ofg_red.
  move: (Ofj) => Ofj2 ; rewrite in_setE in Ofj2 ; apply setD1K in Ofj2 ; rewrite -Ofj2 -setUA.
  rewrite (eqmxP (mxbigcap1U _ _)) ; last first. 
    rewrite notin_set /= => [[[]|]] //.
    move: Ofj ; rewrite in_setE /Og /Of /= => /andP[_] /[swap] /eqP->.
    by rewrite eqxx.
  by rewrite sub_capmx => /andP[/hsideE + _].
Qed.


Definition simple := \rank (\bigcap_(i : 'I_n) tnth H i) = 0.

(* I will likely not show this theorem, see "Algorithms in Combinatorial Geometry"
 * by Edelsbrunner, Theorem 1.3. *)
Theorem nempty_face_count (k : 'I_d.+1) : 
  #|[set f | (dim f == k) && `[< nempty f >]]| 
    <= \sum_(i < k.+1) 'C(d-i, k-i) * 'C(n, d-i)
    ?= iff `[< simple >].
Proof. Admitted.

Section SimpleArrangement.
(* Since I only study arrangements in which all hyperplanes 
 * contain the origin, a simple arrangement can only have 
 * at most d hyperplanes. To simplify I also suppose that n = d. *)
Hypothesis eq_nd : n = d.
Hypothesis sH : simple.


Lemma hplane_cap_eq (P : set 'I_n) : 
  \rank (\bigcap_(i in P) tnth H i) = d - #|P|.
Proof. 
  elim /finset_ind_rev : P => /= [|i0 P N_Px].
    by under eq_big do [rewrite in_setT|] ; rewrite sH card_setT /= card_ord ; lia.
  rewrite set1U_disj_card // (eqmx_rank (mxbigcap1U _ _)) //.
  remember (\bigcap_(i in P) tnth H i)%MS as M ; rewrite -HeqM => IH.
  suff: \rank M <= d - #|P|.
    move: (hplane_cap_lb P) ; rewrite -HeqM => LB UB. 
    by apply /eqP ; rewrite eqn_leq UB LB.
  have MHi0C : (M :&: tnth H i0 == tnth H i0 :&: M)%MS by rewrite capmxC submx_refl.
  move: (Mhcap_rank_lb (tnth H i0) M).
  move: (Nin_card_ltT N_Px) ; rewrite card_ord [n in _ < n]eq_nd => lt_Pd.
  rewrite (eqmx_rank MHi0C) IH -(leq_add2r 1) subnK.
  rewrite -addn1 subnDA subnK //. 
  rewrite -(leq_add2r #|P|) subnK // ; first by apply ltnW. 
  rewrite HeqM -(leqRW (hplane_cap_lb P)). 
  by rewrite -(leq_add2r #|P|) subnK // ; apply ltnW.
Qed. 
  
Theorem fdim_ub f : dim f <= d - count (xpred1 On) f.
Proof.
  rewrite /dim ; apply inf_le ; rewrite fpoints_onNon ; 
  remember [set i | tnth f i == On] as P ; rewrite -HeqP ;
  remember (\bigcap_(i in P) tnth H i)%MS as M.
  exists (\rank M).
    by apply imageP ; rewrite mksetE ; apply subIsetl.
  rewrite HeqM hplane_cap_eq ; apply eq_leq. 
  by congr (_ - _) ; rewrite HeqP card_set_count.
Qed.


Theorem dim_simpleE f : nempty f -> dim f = d - count (xpred1 On) f.
Proof. by move=> NEf ; apply /eqP ; rewrite eqn_leq fdim_ub fdim_lb. Qed.

Lemma size_enum_sign : size (enum sign_finType) = 3.
Proof. Admitted.

Lemma face_count : #|[set: face]| = 3 ^ d.
Proof. by rewrite card_setT /= card_tuple eq_nd cardE size_enum_sign. Qed.

Lemma factM_dvdn_fact i k : i <= k -> i`! * (k - i)`! %| k`!.
Proof. by move=> le_ik ; apply /dvdnP ; exists 'C(k, i) ; rewrite bin_fact. Qed.

Lemma binomM_eq (k : 'I_d.+1) (i : 'I_k.+1) :  
  'C(d-i, k-i) * 'C(d, d-i) = 'C(d, k) * 'C(k, i).
Proof.
  case: i => /= ; case: k => /= k le_kd i le_ik.
  move: le_ik le_kd ; rewrite !ltnS.
  case: (ltnP 0 k) ; last first.
    rewrite leqn0 => /eqP->. rewrite leqn0 => /eqP-> _.
    by rewrite !subn0 !bin0 binn.
  case: (ltnP i d) ; last first => [leq_di _ le_ik le_kd|lt_id lt_0k le_ik le_kd].
    have : i = d /\ k = d by lia. move=> [-> ->].
    by rewrite !subnn !bin0 !binn.
  rewrite !bin_factd ; [| try lia ..].
  have: d - (d - i) = i by lia. move->.
  have: d - i - (k - i) = d - k by lia. move->.
  rewrite !divn_mulAC. rewrite !muln_divA. rewrite -!divnMA.
  rewrite -mulnA divnMl ?fact_gt0 //. 
  rewrite [k`! * (d - k)`!]mulnC [in RHS]mulnA divnMr ?fact_gt0 //.
  congr (_ %/ _) ; lia.
  - by rewrite factM_dvdn_fact ; try lia.
  - by rewrite mulnC factM_dvdn_fact ; try lia.
  - by rewrite factM_dvdn_fact ; try lia.
  - have: d - i - (k - i) = d - k by lia. move<-.
    by rewrite factM_dvdn_fact ; try lia.
Qed.

Lemma dimk_nemptyf_count (k : 'I_d.+1) :
  #|[set f | (dim f == k) && `[< nempty f >]]| = 'C(d, k) * 2 ^ k.
Proof. 
  move: sH => /asboolP ; rewrite -(nempty_face_count k) => /eqP->.
  rewrite eq_nd ; under eq_big do [|rewrite binomM_eq].
  rewrite -big_distrr /= ; congr (_ * _).
  rewrite -[2]/(1 + 1) Pascal ; apply eq_bigr => i _.
  by rewrite !exp1n !muln1.
Qed.

Lemma total_nemptyf_count : #|[set f | `[< nempty f >]]| = 3 ^ d.
Proof. 
  pose F (k : 'I_d.+1) := [set f | dim f == k].
  rewrite [[set f | `[< nempty f >]]](@bigcup_decomp _ _ F).
  suff : disjointS F => [/(@disjointS_capl _ _ [set f | `[< nempty f >]]) /asboolP |].
    rewrite -card_bigcup_leif /F => /eqP ->.
    under eq_big do [|rewrite setIC -set_andb dimk_nemptyf_count]. 
    under eq_big => [i|i _] do [|rewrite -[2 ^ i]mul1n -{1}(exp1n (d - i))].
    by rewrite -Pascal.
  rewrite /disjointS => i j neq_ij ; apply /eqP.
  apply contraT => /set0P[f] /= []. 
  by rewrite /F /= => /eqP -> /eqP /ord_inj eq_ij ; rewrite eq_ij eqxx in neq_ij.
  move=> f _ ; rewrite /bigcup /= ; exists (inord (dim f)) => //.
  by rewrite /F inordK //= ltnS dim_led.
Qed.

Lemma g_equal aT rT (f g : aT -> rT) : f = g -> forall x, f x = g x.
Proof. by move->. Qed.

Theorem all_nempty f : nempty f.
Proof.
  move: total_nemptyf_count => /eqP. 
  rewrite -face_count card_setT card_leTif /= => /eqP /g_equal /= P.
  by apply /asboolP ; rewrite P.
Qed.

Lemma tuple2_count_ge m (T : eqType) (f g : m.-tuple T) a :
  (forall i, (tnth f i != tnth g i) ==> (tnth f i == a)) -> 
  count (xpred1 a) f >= count (xpred1 a) g.
Proof. 
  elim: m f g => [|m IH] f g Hfg.
    move: f g Hfg => [f /eqP /size0nil Sf] [g /eqP /size0nil Sg] _ /=.
    by rewrite Sf Sg /=.
  have Heqf := (tuple_eta f) ; have Heqg := (tuple_eta g).
  rewrite Heqf Heqg /= /thead.
  case: (tnth f ord0 =P tnth g ord0) => [->|/eqP].
  - by rewrite leq_add2l ; apply IH => i ; rewrite !tnth_behead Hfg.
  - move=> /(implyP (Hfg ord0)) -> /= ; apply leq_add ; first by rewrite leq_b1.
    by apply IH => i ; rewrite !tnth_behead Hfg.
Qed.

Lemma tuple_eq_intro1 m (T : eqType) (f g : m.-tuple T) a :
  (forall i, (tnth f i != tnth g i) ==> (tnth f i == a)) -> 
  count (xpred1 a) f = count (xpred1 a) g -> f = g.
Proof. 
  elim: m f g => [|m IH] f g /= Hfg Hcount.
    clear Hfg Hcount ; move: f g => [f Sf] [g Sg] /=.
    apply /eqP ; rewrite -val_eqE /=.
    by move: Sf Sg => /eqP/size0nil-> /eqP/size0nil->.
  move: (tuple_eta f) (tuple_eta g) => Heqf Heqg.
  rewrite Heqf Heqg ; apply /eqP ; rewrite -val_eqE /= eqseq_cons.
  case: (thead f =P thead g) ; last first => [/eqP fg0 | /= fg0].
  - have f0 : thead f == a by apply (implyP (Hfg ord0)), fg0.
    have g0 : thead g != a by rewrite -(eqP f0) eq_sym fg0.
    apply False_ind.
    move: Hcount ; rewrite Heqf Heqg /= -[thead g == a]negbK f0 g0 /= add0n.
    move: (@tuple2_count_ge _ _ (behead_tuple f) (behead_tuple g) a) => bfg_count.
    feed bfg_count => [i|]. by rewrite !tnth_behead Hfg.
    move: bfg_count => /[swap] <- /= ; lia.
  - suff: behead_tuple f = behead_tuple g by move /eqP ; rewrite -val_eqE /=.
    apply IH => [i|] ; first by rewrite !tnth_behead Hfg.
    move: Hcount ; rewrite Heqf Heqg /= -fg0.
    by case: (thead f =P a) => /= _ ; [rewrite !add1n => /succn_inj | rewrite !add0n].
Qed.

Lemma tuple_count_eq1 m (T : eqType) (f g : m.-tuple T) a : 
  (exists i, [/\ tnth f i == a, tnth g i != a & forall j, j != i -> tnth f j = tnth g j]) <->
    (count (xpred1 a) f = (count (xpred1 a) g).+1 /\ 
    forall i, (tnth f i != tnth g i) ==> (tnth f i == a)).
Proof. 
  split => [[i [fi gi fgj]] | []].
  - split ; last first => [j|].
    + apply /implyP ; case: (i =P j) => [<- //|/eqP neq_ij].
      by rewrite fgj ; [rewrite eqxx|rewrite eq_sym].
    + elim: m i f g fi gi fgj => /= [[]|m IH i] f g fi gi fgj ; first by lia.
      move: (tuple_eta f) (tuple_eta g) => Heqf Heqg.
      rewrite Heqf Heqg /= /thead ; case: (i =P ord0) => [eq_i0|/eqP neq_i0].
      * rewrite -eq_i0 fi -[tnth g i == a]negbK gi /= add0n add1n ; congr (_.+1).
        suff: [tuple of behead f] = [tuple of behead g].
          by move=> /(f_equal (@tval m T)) /= ->.
        apply /eqP ; rewrite eqEtuple ; apply /forallP => /= j.
        rewrite !tnth_behead fgj // eq_i0.
        apply contraT ; rewrite negbK => /eqP /(f_equal val) /=.
        rewrite inordK // ; case: j => /= ; lia.
      * rewrite -[in RHS]addn1 -[in RHS]addnA.
        congr (_ + _) ; first by rewrite fgj // eq_sym. 
        rewrite addn1.
        have lt_i1m: i.-1 < m. 
          case: i neq_i0 fi gi fgj => /= [i Hi] + _ _ _.
          rewrite -val_eqE /= ; lia.
        have i11_i: i.-1.+1 = i.
          case: i neq_i0 lt_i1m fi gi fgj => /= [i Hi] + _ _ _ _.
          rewrite -val_eqE /= ; lia.
        apply (IH (Ordinal lt_i1m)) =>[| |j neq_ji1] ; rewrite !tnth_behead ?i11_i ?inord_val //=.
        apply fgj ; clear fi gi fgj i11_i neq_i0.
        move: neq_ji1 ; rewrite -!val_eqE /=.
        case: j => /= [j Hj] ; case: i lt_i1m => /= [i Hi] _.
        by rewrite inordK ; lia.
  - elim: m f g => /= [f g Hcount|m IH f g Hcount Hfg].
      apply False_ind ; move: f g Hcount => [f /eqP /size0nil Hf] [g /eqP /size0nil Hg] /=.
      by rewrite Hf Hg /=.
      have Heqf := (tuple_eta f) ; have Heqg := (tuple_eta g).
      case: (tnth f ord0 =P tnth g ord0) ; last first => [/eqP | fg0].
    + move=> /[dup] /(implyP (Hfg ord0)) => f0 g0 ; rewrite (eqP f0) eq_sym in g0.
      exists ord0 ; split => // j neq_j0 ; move: Hcount.
      rewrite Heqf Heqg /= /thead -[tnth g ord0 == a]negbK f0 g0 /= add0n add1n => /succn_inj Hcount.
      have lt_j1m : j.-1 < m.
        by case: j neq_j0 => /= [j Hj] ; rewrite -val_eqE /= ; lia.
      remember (Ordinal lt_j1m) as j'.
      have Hjj' : j = lift ord0 j'.
        case: j neq_j0 lt_j1m j' Heqj' => [j Hj] /= neq_j0 lt_j1m [j' Hj'] /= Heqj'.
        apply /eqP ; rewrite -!val_eqE /= /bump leq0n /= in neq_j0 *.
        by move: Heqj' => /eqP ; rewrite -val_eqE /= ; lia.
      rewrite Hjj' !tnthS ; f_equal.
      by apply (@tuple_eq_intro1 _ _ _ _ a) => [i|] ; [rewrite !tnth_behead|].
    + specialize (IH (behead_tuple f) (behead_tuple g)) ; feed_n 2 IH.
      * by move: Hcount ; rewrite Heqf Heqg /thead fg0 /= ; lia.
      * by setoid_rewrite tnth_behead.
      case: IH => [i [bfi bgi bfgj]].
      exists (lift ord0 i) ; split => [| |[j Hj] /=].
      * by rewrite Heqf tnthS bfi.
      * by rewrite Heqg tnthS bgi.
      * rewrite Heqf Heqg -val_eqE /= /bump /=.
        case: j Hj => [|j] Hj.
          have /eqP j0 : Ordinal Hj == ord0 by rewrite -val_eqE /=.
          by rewrite !j0 !tnth0 /thead fg0.
        have Hj' : j < m by lia.
        have: Ordinal Hj = lift ord0 (Ordinal Hj') => [|-> neq_ji].
          by apply /eqP ; rewrite -val_eqE /= /bump /= add1n.
        rewrite !tnthS ; apply bfgj ; rewrite -val_eqE /= ; lia.
Qed.
     
Lemma dim_eqk f g k : dim g = dim f + k <-> 
  count (xpred1 On) f = count (xpred1 On) g + k.
Proof.    
  rewrite !dim_simpleE ; [|by apply all_nempty ..] ; split ; last first.
  - move=> P ; rewrite P subnDA subnK //.
    have: count (xpred1 On) f <= d by rewrite -eq_nd ; apply tuple_count_size.
    by lia. 
  - have: count (xpred1 On) f <= d by rewrite -eq_nd ; apply tuple_count_size.
    have: count (xpred1 On) g <= d by rewrite -eq_nd ; apply tuple_count_size.
    by lia.
Qed.

Theorem subfaceE f g : subface f g <-> 
  exists i, [/\ tnth f i == On, tnth g i != On & forall j, j != i -> tnth f j = tnth g j].
Proof. 
  split ; last first => [Hfg | [_ _]].
  - constructor ; [by apply all_nempty .. |move=> x|]. 
    + case: Hfg => [i [fi gi fgj]]. 
      rewrite -in_setE => /fpointsP Hf.
      rewrite -in_setE ; apply /clfpointsP => j.
      case: (i =P j) => [<-|/eqP neq_ij] ; first by right ; rewrite Hf (eqP fi).
      by rewrite Hf -fgj ; [|rewrite eq_sym //] ; left.
    + rewrite -addn1 ; apply dim_eqk.
      by move: Hfg ; rewrite tuple_count_eq1 addn1 => [[-> _]].
  - rewrite -[(dim f).+1]addn1 dim_eqk => /face_inclP Hincl Hcount .
    feed Hincl ; [by apply all_nempty | do [move=> /forallP /=] in Hincl].
    apply tuple_count_eq1 ; split => [|i] ; first by rewrite -addn1.
    by rewrite implyNb orbC Hincl.
Qed. 

End SimpleArrangement.

End Arrangement.

