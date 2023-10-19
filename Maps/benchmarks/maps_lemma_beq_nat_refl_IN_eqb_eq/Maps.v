(** * Maps: Total and Partial Maps *)
Load LFindLoad.
From lfind Require Import LFind.
Unset Printing Notations.
Set Printing Implicit.

From Coq Require Import Bool.Bool.
From Coq Require Import Logic.FunctionalExtensionality.
From VFA Require Import Perm.

(* ################################################################# *)
(** * Total Maps *)

Definition total_map (A : Type) : Type := nat -> A.

Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

Definition t_update {A : Type} (m : total_map A) (x : nat) (v : A) : total_map A :=
  fun x' => if x =? x' then v else m x'.

Definition examplemap :=
  t_update (t_update (t_empty false) 1 false) 3 true.

Lemma t_apply_empty:  forall A x v, @t_empty A v x = v.
Proof. intros. unfold t_empty. reflexivity. Qed.

Lemma t_update_eq : forall A (m: total_map A) x v,
  (t_update m x v) x = v.
Proof. intros. unfold t_update. replace (x =? x) with true. auto. apply beq_nat_refl. Qed. 

Theorem eqb_eq : forall n m, n =? m = true <-> n = m.
Proof.
  split. 
  - generalize dependent m. induction n. destruct m. reflexivity. discriminate. 
  destruct m. discriminate. simpl. intros. rewrite (IHn m H). reflexivity.
  - intros. rewrite H. symmetry. 
  lfind_debug.
  Admitted.

  (* apply beq_nat_refl.
Qed. *)
