From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.analysis Require Import reals classical_sets boolp.
From mathcomp Require Import zify algebra_tactics.ring.
Require Import tactics csets_extras point_topo arrangements igraph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Open Scope classical_set_scope.
Open Scope real_scope.

Section SimpleIGBuilding.
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
Notation igraph := (@igraph.igraph R d n).
Notation igempty := (igraph.igempty R d n).
Notation igext_incidence := (@igraph.igext_incidence R d n).
Notation igext_ipoint := (@igraph.igext_ipoint R d n).


Section SimpleIGBuilding.
Variables (H : n.-tuple hplane).
Hypothesis eq_nd : n = d.
Hypothesis sH : simple H.

Section Algorithm.

(* This returns the list of all faces of size k (empty or not). *)
Fixpoint all_faces k : seq (k.-tuple sign) :=
  match k with 
  | k'.+1 => 
      let fs := all_faces k' in 
        (map (cons_tuple Left ) fs) ++
        (map (cons_tuple On   ) fs) ++
        (map (cons_tuple Right) fs)
  | 0 => [tuple] :: [::]
  end.

Fixpoint build_subs_rec k (g : k.-tuple sign) : list (k.-tuple sign) :=
  match k, g with 
  | 0, _ => [::]
  | k'.+1, g =>
    let g' := [tuple of behead g] in
    let fs := map (cons_tuple (thead g)) (build_subs_rec g') in
      if thead g == On then fs else cons_tuple On g' :: fs
  end.

Definition build_subs (g : face) : list face := build_subs_rec g.

Definition add_subfaces (g : face) (ig : igraph) := 
  foldr (fun f ig => (f -incidence-> g ; ig)) ig (build_subs g).
  
(* Yes, build doesn't depend on H : all simple arrangements in dimension d 
 * have the same incidence graph. *)
Definition build : igraph :=
  foldr add_subfaces igempty (all_faces n).

End Algorithm.

Section Correctness.

Lemma all_faces_correct k f : f \in all_faces k.
Proof. 
  elim: k f => [|k IH] f ; rewrite /all_faces.
    by rewrite tuple0 inE.
  case: (tupleP f) => s f' ; rewrite !mem_cat ; apply /or3P.
  by case: s ; [apply Or31 | apply Or32 | apply Or33] ; 
    rewrite tuple_cons_in ; intuition.
Qed.

Lemma build_subs_rec_inv k (g : k.-tuple sign) : 
  forall f, f \in build_subs_rec g -> 
    exists i, [/\ tnth f i == On, tnth g i != On & forall j, j != i -> tnth f j = tnth g j].
Proof. 
  elim: k g => [|k IH] g f ; first by rewrite /build_subs_rec inE.
  case: (tupleP f) => /= sf f'. 
  case: (tupleP g) => /= sg g' ; rewrite /thead tnth0 tuple_behead_cons.
  case: ifP => [/eqP->|/negbT neq_sgOn].
  - rewrite tuple_cons_in tupleE => [[-> /IH[i [/= fi gi fgj]]]].
    exists (lift ord0 i) ; split => [| |j] ; rewrite ?tnthS //.
    by case: (ord_0liftP j) => // j' ; rewrite (inj_eq lift_inj) !tnthS ; apply fgj.
  - rewrite in_cons => /orP[] ; [|rewrite tuple_cons_in].
    + rewrite {1}tupleE => /eqP P ; apply cons_tuple_inj in P ; move: P => [-> ->].
      exists ord0 ; split => [| |j] ; [rewrite tnth0 // .. |].
      by case: (ord_0liftP j) => // j' _ ; rewrite !tnthS.
    + move=> [-> /IH[i [fi gi fgj]]].
      exists (lift ord0 i) ; split => [| |j] ; rewrite ?tnthS //.
      by case: (ord_0liftP j) => // j' ; rewrite (inj_eq lift_inj) !tnthS ; apply fgj.
Qed.
  
Corollary build_subs_subface g : 
  forall f, f \in build_subs g -> subface H f g.
Proof. by move=> f Hfg ; apply subfaceE ; last apply build_subs_rec_inv. Qed.



Lemma all_reachable f : reachable build f.
Proof. Admitted.

Theorem build_correct : ig_rep gt_d1 build H.
Proof. Admitted.


End Correctness.

End SimpleIGBuilding.