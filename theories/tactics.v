(* Setoid Rewriting with Ssreflec's boolean inequalities. 
 * Solution created by Georges Gonthier *)
From Coq Require Import Basics Setoid Morphisms.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Preorder and Instances for bool *)
Inductive leb a b := Leb of (a ==> b).

Lemma leb_eq a b : leb a b <-> (a -> b).
Proof. move: a b => [|] [|]; firstorder. Qed.

#[export] Instance: PreOrder leb.
Proof. split => [[|]|[|][|][|][?][?]]; try exact: Leb. Qed.

#[export] Instance: Proper (leb ==> leb ==> leb) andb.
Proof. move => [|] [|] [A] c d [B]; exact: Leb. Qed.

#[export] Instance: Proper (leb ==> leb ==> leb) orb.
Proof. move => [|] [|] [A] [|] d [B]; exact: Leb. Qed.

#[export] Instance: Proper (leb ==> impl) is_true.
Proof. move => a b []. exact: implyP. Qed.

(* Instances for le *)
#[export] Instance: Proper (le --> le ++> leb) leq.
Proof. move => n m /leP ? n' m' /leP ?. apply/leb_eq => ?. eauto using leq_trans. Qed.

#[export] Instance: Proper (le ==> le ==> le) addn.
Proof. move => n m /leP ? n' m' /leP ?. apply/leP. exact: leq_add. Qed.

#[export] Instance: Proper (le ==> le ==> le) muln.
Proof. move => n m /leP ? n' m' /leP ?. apply/leP. exact: leq_mul. Qed.

#[export] Instance: Proper (le ++> le --> le) subn.
Proof. move => n m /leP ? n' m' /leP ?. apply/leP. exact: leq_sub. Qed.

#[export] Instance: Proper (le ==> le) S.
Proof. move => n m /leP ?. apply/leP. by rewrite ltnS. Qed.

#[export] Instance: RewriteRelation le. Qed.

(* Wrapper Lemma to trigger setoid rewrite *)
Definition leqRW m n : m <= n -> le m n := leP.

(* Testing
Lemma T1 : forall x y, x <= y -> x + 1 <= y + 1.
Proof. move => x y h. by rewrite (leqRW h). Qed.

Lemma T2 : forall x y, x <= y -> (x + 1 <= y + 1) && true.
Proof. move => x y h. by rewrite (leqRW h) andbT. Qed.*)


(* This tactic feeds the precondition of an implication in order to derive the conclusion
  (taken from http://comments.gmane.org/gmane.science.mathematics.logic.coq.club/7013).

  Usage: feed H.

  H: P -> Q  ==becomes==>  H: P
                          ____
                          Q

  After completing this proof, Q becomes a hypothesis in the context. *)
  Ltac feed H :=
  match type of H with
  | ?foo -> _ =>
    let FOO := fresh in
    assert foo as FOO; [|specialize (H FOO); clear FOO]
  end.

(* Generalization of feed for multiple hypotheses.
    feed_n is useful for accessing conclusions of long implications.

    Usage: feed_n 3 H.
      H: P1 -> P2 -> P3 -> Q.

    We'll be asked to prove P1, P2 and P3, so that Q can be inferred. *)
Ltac feed_n n H := match constr:(n) with
  | O => idtac
  | (S ?m) => feed H ; [| feed_n m H]
  end.



