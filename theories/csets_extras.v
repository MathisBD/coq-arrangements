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


Section CardSet.

Variables (T : finType).
Implicit Types (S : set T).

Lemma card_set_sum S : 
  #|S| = \sum_i (i \in S).
Proof. Admitted.

Lemma card_eq0_set0 S : #|S| = 0 -> S =set0.
Proof. Admitted.

Lemma card_set0 : #|@set0 T| = 0.
Proof. Admitted.

Lemma card_eqT_setT S : #|S| = #|T| -> S = setT.
Proof. Admitted.

Lemma card_setT : #|@setT T| = #|T|.
Proof. Admitted.

Lemma card_leT S : #|S| <= #|T|.
Proof. Admitted.

Lemma Nin_card_ltT x S : x \notin S -> #|S| < #|T|.
Proof. 
  move=> N_Px.
  apply contraT ; rewrite -ltnNge ltnS => le_TP.
  have /eqP eq_TP : #|S| == #|T| by rewrite eqn_leq (card_leT S) /=.
  by move: eq_TP N_Px => /card_eqT_setT /= -> ; rewrite in_setT.
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

End CardSet.
