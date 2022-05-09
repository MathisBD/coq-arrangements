From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.analysis Require Import reals classical_sets boolp.
From mathcomp Require Import zify.
Require Import tactics.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section TupleExtras.
Variables (T : eqType) (n : nat).
Implicit Types (x y : T) (t : n.-tuple T).

Lemma tuple_cons_in x y t (l : list (n.-tuple T)) :
  [tuple of x :: t] \in map (cons_tuple y) l <-> x = y /\ t \in l.
Proof. Admitted.

Lemma tuple_behead_cons x t :
  [tuple of behead [tuple of x :: t]] = t. 
Proof. Admitted.

Lemma cons_tupleE x t : cons_tuple x t = [tuple of x :: t].
Proof. by []. Qed. 

Lemma cons_tuple_inj : injective2 (@cons_tuple n T).
Proof. Admitted.

Lemma tuple_count_size x t :
  count (xpred1 x) t <= n.
Proof.
  rewrite (leqRW (@count_size _ _ t)).
  by case: t => t /eqP st /= ; rewrite st leqnn.
Qed.

End TupleExtras.

Section BoolExtras.

Lemma is_true_inj : injective is_true.
Proof. 
  move=> a b ; case: a ; case: b => //= ;  
  move: (@iffP (is_true true) (is_true false) true (@idP true)) => H0 H1.
  - by feed_n 2 H0 ; [by rewrite H1 .. |] ; case: H0.
  - by feed_n 2 H0 ; [by rewrite H1 .. |] ; case: H0.
Qed.

Lemma nat_of_bool_inj : injective nat_of_bool.
Proof. by move=> a b ; case: a ; case: b. Qed. 

End BoolExtras.

Section OrdExtras.
Variables n : nat.

Inductive lift_ord_spec : 'I_n.+1 -> Type :=
  | Lift_ord_0 : lift_ord_spec (@ord0 n)
  | Lift_ord_lift : forall (i : 'I_n), lift_ord_spec (lift ord0 i).

(* Use this with 'case: (lift_ordP i)'. *)
Lemma lift_ordP i : lift_ord_spec i.
Proof. 
  case: (i =P ord0) => [->|/eqP] ; first by constructor.
  case: i => [i lt_in1] /= ; rewrite -val_eqE /= => ne_i0.
  have lt_i1n : i.-1 < n by lia.
  have : Ordinal lt_in1 = lift ord0 (Ordinal lt_i1n) => [|->].
    by apply /eqP ; rewrite -val_eqE /= /bump /= ; lia.
  by constructor.
Qed.

Inductive widen_ord_spec : 'I_n.+1 -> Type :=
  | Widen_ord_max : widen_ord_spec (@ord_max n)
  | Widen_ord_widen : forall (i : 'I_n), widen_ord_spec (widen_ord (leqnSn n) i).

(* Use this with 'case: (widen_ordP i)'. *)
Lemma widen_ordP i : widen_ord_spec i.
Proof. 
  case: (i =P ord_max) => [->|/eqP] ; first by constructor.
  case: i => [i lt_in1] ; rewrite -val_eqE /= => ne_im.
  have lt_in : i < n by lia. 
  have : Ordinal lt_in1 = widen_ord (leqnSn n) (Ordinal lt_in) => [|->].
    by apply /eqP ; rewrite -val_eqE /=.
  by constructor.
Qed.

End OrdExtras. 

Section MatrixExtras.
Open Scope real_scope.
Open Scope classical_set_scope.
Open Scope ring_scope.
Variables R : realType.
Implicit Types (s t : R).

Lemma trmx_scale n m (A : 'M_(n, m)) s  : (s *: A)^T = s *: A^T.
Proof. by rewrite -mul_mx_scalar trmx_mul tr_scalar_mx mul_scalar_mx. Qed.

Lemma scale_mulmx m1 m2 m3 (A : 'M_(m1, m2)) (B : 'M_(m2, m3)) s t : 
  s *: A *m (t *: B) = (s * t) *: (A *m B).
Proof. 
  rewrite -!mul_scalar_mx scalar_mxM.
  rewrite mulmxA [in RHS]mulmxA ; congr (_ *m _).
  by rewrite -mulmxA scalar_mxC mulmxA.
Qed.

Lemma bigcap1U n a i0 (P : set 'I_n) (F : 'I_n -> 'M[R]_a) : i0 \notin P ->
  (\bigcap_(i in (i0 |` P)) F i == F i0 :&: \bigcap_(i in P) F i)%MS.
Proof. 
  rewrite (bigID [pred i | i == i0]) /= => N_Pi0.
  apply /eqmxP ; apply cap_eqmx.
  - under eq_bigl do (rewrite andb_idl => [|/eqP->] ; [|by rewrite in_setE ; left]).
    rewrite big_pred1_eq ; apply eqmx_refl.
  - have cond i : ((i \in i0 |` P) && (i != i0)) = (i \in P).
      apply /eqP ; rewrite -eqbE /eqb /addb ; case: ifP => [|/negbT].
      + rewrite negb_and negbK => /orP[|/eqP-> //].
        move /negP ; rewrite in_setE /= -[P i]in_setE.
        by case E: (i \in P) ; intuition.
      + by rewrite negbK => /andP[+ /eqP] ; rewrite !in_setE /= ; intuition.
    under eq_bigl do rewrite cond ; apply eqmx_refl.
Qed.

Lemma sumr_ge0if (I : finType) (P : pred I) (E : I -> R) :
  (forall i, P i -> 0 <= E i)%R -> 
  (0 <= \sum_(i | P i) E i ?= iff [forall i, P i ==> (E i == 0)])%R.
Proof. 
  move=> Hle0 ; split ; first by apply big_ind => // x y ; apply Num.Theory.addr_ge0.
  apply /eqP ; case: ifP => [/forallP Heq0|]. 
  - apply big_ind => //.
    by move=> x y <- <- ; rewrite GRing.Theory.addr0.
    by move=> i Pi ; symmetry ; apply /eqP ; apply (implyP (Heq0 i)).
  - move /negbT ; rewrite negb_forall => /existsP[i0].
    rewrite negb_imply => /andP[Pi0 Ei0_neq0].
    suff: \sum_(i | P i) E i > 0 by move /Num.Theory.lt0r_neq0 /eqP ; intuition.
    have Ei0_gt0 : E i0 > 0 by rewrite Order.POrderTheory.lt_def Ei0_neq0 Hle0. clear Ei0_neq0.
    rewrite (bigID (xpred1 i0)) /= ; apply Num.Theory.ltr_paddr.
    + by apply big_ind => // [x y | i /andP[Pi _]] ; [apply Num.Theory.addr_ge0 | auto].
    + by under eq_bigl do rewrite andb_idl => [|/eqP-> //] ; rewrite big_pred1_eq.
Qed.

End MatrixExtras.

Section NatSetBounds.
Open Scope classical_set_scope.
Variables (A : set nat) (x0 t : nat).

Lemma inf_le :
  (exists2 x, A x & x <= t) -> infimum x0 A <= t.
Proof. Admitted.

Lemma inf_ge :
  (forall x, A x -> x >= t) -> A !=set0 -> infimum x0 A >= t.
Proof. Admitted.

End NatSetBounds.

Section ClassicalSetsExtras.
Open Scope classical_set_scope.

Lemma image_nonempty aT rT (f : aT -> rT) (A : set aT) :
  A !=set0 -> [set f x | x in A] !=set0.
Proof. by case => [x Ax] ; exists (f x) ; exists x. Qed.

Lemma set_ord0 (P : set 'I_0) : P = set0.
Proof. Admitted.

Lemma Csubset1 T (A : set T) x : ([set x] `<=` A) = (x \in A).
Proof. by apply propext ; rewrite /subset /= in_setE ; split => [/(_ x (Logic.eq_refl _)) | Ax t ->]. Qed.

Lemma finset_ind_rev (T : finType) (P : (set T) -> Prop) :
  P setT -> 
  (forall x S, x \notin S -> P (x |` S) -> P S) ->
  (forall S, P S).
Proof. Admitted.


Definition disjointS n T (F : 'I_n -> set T) := forall i j, i != j -> F i `&` F j =set0.

Lemma disjointS_capl n T S (F : 'I_n -> set T) :
  disjointS F -> disjointS (fun i => S `&` F i).
Proof. Admitted.

Lemma disjointS_capr n T S (F : 'I_n -> set T) :
  disjointS F -> disjointS (fun i => F i `&` S).
Proof. Admitted.

Lemma bigcap_decomp n T (F : 'I_n -> set T) S :
  S `<=` \bigcup_i F i -> S = \bigcup_i (S `&` F i).
Proof. Admitted.

Section CardSet.
Variables (T : finType).
Implicit Types (S : set T).

Lemma card_set_sum S : 
  #|S| = \sum_i (i \in S).
Proof. Admitted.

Lemma card0_set0 S : (#|S| == 0) = (S == set0).
Proof. 
  apply /eqP ; case: ifP => [/eqP ->|/negbT /set0P[x Sx]].
  - rewrite card_set_sum. apply big_ind => // [x y -> -> //| i _].
    by rewrite in_set0 /=.
  - suff: #|S| > 0 by move=> /lt0n_neq0 /eqP.
    rewrite card_set_sum (bigID [pred i | i == x]) /=.
    rewrite addn_gt0 ; apply /orP ; left ; rewrite big_pred1_eq.
    by rewrite lt0b in_setE.
Qed.

Lemma card_set0 : #|@set0 T| = 0.
Proof. by apply /eqP ; rewrite (card0_set0 set0) eqxx. Qed.

Lemma card_setT : #|@setT T| = #|T|.
Proof. by rewrite card_set_sum ; under eq_big do [|rewrite in_setT /=] ; rewrite sum1_card. Qed.

Lemma card_leTif S : #|S| <= #|T| ?= iff (S == setT).
Proof.
  rewrite -card_setT !card_set_sum ; split.
  - by apply leq_sum => i _ ; rewrite in_setT /= leq_b1.
  - rewrite (@leqif_sum _ _ [pred i | i \in S]) /= ; last first => [i _|].
    + by rewrite in_setT /= ; split ; [rewrite leq_b1 | case: (i \in S)].
    + symmetry ; apply /eqP ; case: ifP => [/forallP H | /negbT].
      * apply funext => x /= ; move: (implyP (H x) (eq_refl true)).
        rewrite in_setE => Sx ; apply propext ; intuition.
      * rewrite negb_forall => /existsP[x] ; rewrite negb_imply /= => N_Sx ST.
        have Sx : x \in S by rewrite in_setE ST /=.
        by move: Sx N_Sx => ->.
Qed.

Lemma Nin_card_ltT x S : x \notin S -> #|S| < #|T|.
Proof. 
  move=> N_Px.
  apply contraT ; rewrite -ltnNge ltnS => le_TP.
  have /eqP eq_TP : #|S| == #|T| by rewrite eqn_leq (card_leTif S) /=.
  by move: eq_TP N_Px => /eqP ; rewrite card_leTif => /eqP -> ; rewrite in_setT.
Qed.

Lemma set1U_disj_card x S :
  x \notin S -> #|x |` S| = #|S|.+1.
Proof. Admitted.

Lemma card_set_count m (t : m.-tuple T) x : 
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

Lemma card_bigcup_leif n (F : 'I_n -> set T) :
  #|\bigcup_i F i| <= \sum_i #|F i| ?= iff `[< disjointS F >].
Proof. Admitted.

End CardSet.

End ClassicalSetsExtras.
