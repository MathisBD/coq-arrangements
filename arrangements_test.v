From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.analysis Require Import reals classical_sets topology.
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

Variables (P : n.-tuple hplane).

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
(* The position of a point relative to the hyperplanes of P *)
Definition feature (x : point) : n.-tuple sign := map_tuple (hside x) P.

Definition face := n.-tuple sign.
Definition in_face (x : point) (f : face) : bool := (feature x) == f.
Definition fpoints (f : face) : set point := [set x | in_face x f].
Definition in_clface (x : point) (f : face) : bool :=
  all2 (fun sx sf => (sx == On) || (sx == sf)) (feature x) f.
Definition clfpoints (f : face) : set point := [set x | in_clface x f].

Definition nempty (f : face) : Prop := fpoints f !=set0.

Definition dim f : nat := infimum 0 (mxrank @` [set M : 'M[R]_d | fpoints f `<=` Mpoints M]).


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

Lemma dim_lb (f : face) : nempty f -> dim f >= d - count (xpred1 On) f.
Proof. Admitted.

Section SimpleArrangement.
Definition simple := True.
Hypothesis sP : simple.


Lemma simple_dim_ub f : dim f <= d - count (xpred1 On) f.
Proof. Admitted.

Lemma simple_dim_eq f : nempty f -> dim f = d - count (xpred1 On) f.
Proof. by apply /eqP ; rewrite eqn_leq simple_dim_ub dim_lb. Qed.

End SimpleArrangement.

