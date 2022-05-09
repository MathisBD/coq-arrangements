From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.analysis Require Import reals classical_sets.
From mathcomp Require Import zify.
Require Import tactics.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section TupleExtras.
Variables (n : nat) (T : eqType).
Implicit Types (x y : T) (t : n.-tuple T).

Lemma tuple_cons_in x y t (l : list (n.-tuple T)) :
  [tuple of x :: t] \in map (cons_tuple y) l <-> x = y /\ t \in l.
Proof. Admitted.

Lemma tuple_behead_cons x t :
  [tuple of behead [tuple of x :: t]] = t. 
Proof. Admitted.

Inductive ord_0lift_spec m : 'I_m.+1 -> Type :=
  | Ord_0lift_0 : @ord_0lift_spec m (@ord0 m)
  | Ord_0lift_lift : forall (i : 'I_m), @ord_0lift_spec m (lift ord0 i).

Lemma ord_0liftP m (i : 'I_m.+1) : ord_0lift_spec i.
Proof. Admitted.

Lemma cons_tupleE x t : cons_tuple x t = [tuple of x :: t].
Proof. by []. Qed. 

Lemma cons_tuple_inj : injective2 (@cons_tuple n T).
Proof. Admitted.

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

Section MatrixExtras.
Open Scope real_scope.
Open Scope classical_set_scope.
Variables R : realType.

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

End MatrixExtras.
