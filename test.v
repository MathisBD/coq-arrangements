From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Fixpoint neg_tup2 n (t : n.-tuple bool) : n.-tuple bool :=
  match n, t with 
  | 0, _ => [tuple]
  | n'.+1, t => [tuple of ~~(thead t) :: neg_tup2 [tuple of behead t]]
  end.

Fixpoint neg_tup n (t : n.-tuple bool) : n.-tuple bool :=
  match n with 
  | 0 => [tuple]
  | n'.+1 => [tuple of ~~(thead t) :: behead t]
  end.


