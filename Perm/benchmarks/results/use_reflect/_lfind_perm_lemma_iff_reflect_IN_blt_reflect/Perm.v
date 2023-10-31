(* Perm: Basic Techniques for Permutations and Ordering *)
(* From: https://github.com/kolya-vasiliev/verified-functional-algorithms-2019/blob/master/Perm.v *)

Load LFindLoad.
From lfind Require Import LFind.
Unset Printing Notations.
Set Printing Implicit.

Require Import Coq.Strings.String.
Require Export Coq.Bool.Bool.
Require Export Coq.Arith.Arith.
Require Export Coq.Arith.EqNat.
Require Export Coq.omega.Omega.
Require Export Coq.Lists.List.
Export ListNotations.
Require Export Permutation.

(* ################################################################# *)
(* The Less-Than Order on the Natural Numbers *)

(* For some reason, the Coq library has [ <? ] and [ <=? ] notations, but is missing these three: *)

Notation  "a >=? b" := (Nat.leb b a) (at level 70, only parsing) : nat_scope.
Notation  "a >? b"  := (Nat.ltb b a) (at level 70, only parsing) : nat_scope.
Notation " a =? b"  := (beq_nat a b) (at level 70) : nat_scope.

(* Inductive reflect (P : Prop) : bool -> Set :=
	  | ReflectT : P -> reflect P true 
    | ReflectF : ~ P -> reflect P false *)            

(* ================================================================= *)

(* Helper Lemma = iff_reflect : ∀ (P : Prop) (b : bool), P ↔ b = true → reflect P b *)
(* Helper Lemma = Nat.eqb_eq : ∀ n m : nat, (n =? m) = true ↔ n = m *)
Lemma beq_reflect : forall x y, reflect (x = y) (x =? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry.  apply Nat.eqb_eq.
Qed.

(* Helper Lemma = iff_reflect : ∀ (P : Prop) (b : bool), P ↔ b = true → reflect P b *)
(* Helper Lemma = Nat.ltb_lt : ∀ n m : nat, (n <? m) = true ↔ n < m *)
Lemma blt_reflect : forall x y, reflect (x < y) (x <? y).
Proof.
  intros x y.
  lfind_debug.
  Admitted.

  (* apply iff_reflect. symmetry. apply Nat.ltb_lt.
Qed. *)
