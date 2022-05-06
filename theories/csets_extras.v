From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.analysis Require Import classical_sets boolp.
From mathcomp Require Import zify.
Require Import tactics.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Open Scope classical_set_scope.

(* Simple lemmas about classical sets,
 * defined in mathcomp.analysis.classical_sets. *)


Section NatSetBounds.

Variables (A : set nat) (x0 t : nat).

Lemma inf_le :
  (exists2 x, A x & x <= t) -> infimum x0 A <= t.
Proof. Admitted.

Lemma inf_ge :
  (forall x, A x -> x >= t) -> A !=set0 -> infimum x0 A >= t.
Proof. Admitted.

End NatSetBounds.


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
