From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.analysis Require Import reals classical_sets boolp.
From mathcomp Require Import zify algebra_tactics.ring.
Require Import tactics csets_extras point_topo arrangements.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Open Scope classical_set_scope.
Open Scope real_scope.

Section IncidenceGraph.
Variables R : realType.
(* d : dimension of the space.
 * n : number of hyperplanes in the arrangement. *)
Variables (d n : nat).
Hypothesis gt_d1 : d > 1.

Notation point := 'M[R]_(1, d).
Notation hplane := (arrangements.hplane R d).
Notation face := (arrangements.face n).
Notation subface := (arrangements.subface gt_d1).
Notation nempty := (arrangements.nempty gt_d1).
Notation fpoints := (arrangements.fpoints gt_d1).
Notation clfpoints := (arrangements.clfpoints gt_d1).

Record igraph := Igraph { incident: rel face ; ipoint : face -> point }.

Definition forigin : face := [tuple of nseq n On].
Definition reachable ig f :=  
  f \in dfs (rgraph (incident ig)) #|[set: face]| [::] forigin.

(* An incidence graph represents an arrangement with subface relation 'incident'
 * and with faces that are reachable in ig. *)
(* A side effect of this definition is that an incidence graph can only describe 
 * arrangements that contain the origin vertex *)
Inductive ig_rep (ig : igraph) (H : n.-tuple hplane) : Prop :=
  IGrep of (forall f g, reflect (subface H f g) (incident ig f g)) &
    (forall f, reflect (nempty H f) (reachable ig f)).

(* This is an invariant maintained by the algorithm that constructs an igraph. *)
Inductive ig_ipoint (ig : igraph) (H : n.-tuple hplane) : Prop :=
  IGipoint of (forall f, nempty H f -> ipoint ig f \in fpoints H f).


Section IGManipulation.

(* The empty incidence graph. *)
Definition igempty := Igraph [rel f g | false] (fun f => 0%R).

(* extend an igraph by setting ipoint f = x *)
Definition igext_ipoint ig (f : face) (x : point) :=
  Igraph (incident ig) (fun g => if g == f then x else ipoint ig g).

Definition igext_incidence ig (f g : face) :=
  Igraph [rel f' g' | ((f' == f) && (g' == g)) || (incident ig f' g')] (ipoint ig).

(* An example using the notations to extend igraphs : *)

End IGManipulation.

End IncidenceGraph.

Notation "f '-incidence->' g ';' ig" := (igext_incidence ig f g)
  (at level 0, right associativity) : form_scope.
Notation "f '-ipoint->' x ; ig" := (igext_ipoint ig f x)
  (at level 0, right associativity) : form_scope.
