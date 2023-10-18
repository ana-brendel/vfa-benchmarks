(** * Maps: Total and Partial Maps *)

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
  - intros. rewrite H. symmetry. apply beq_nat_refl.
Qed.

Theorem t_update_neq : forall (X:Type) v x1 x2
  (m : total_map X), x1 <> x2 -> (t_update m x1 v) x2 = m x2.
Proof.
  intros. unfold t_update. 
  assert (G: x1 <> x2 -> x1 =? x2 = false). intros. unfold not in H0. rewrite <- eqb_eq in H0.
  destruct (x1 =? x2). contradiction. reflexivity. apply G in H. rewrite H. reflexivity.
Qed.

Lemma t_update_shadow : forall A (m: total_map A) v1 v2 x, 
  t_update (t_update m x v1) x v2 = t_update m x v2.
Proof.
  intros. unfold t_update. apply functional_extensionality_dep. intros.
  destruct (x =? x0). auto. auto. 
Qed.

Theorem t_update_same : forall X x (m : total_map X), t_update m x (m x) = m.
Proof.
  intros. unfold t_update. apply functional_extensionality_dep. intros. 
  assert (G : x =? x0 = true <-> x = x0). apply eqb_eq.
  assert (G1: true = true). auto.
  destruct (x =? x0). apply G in G1. rewrite G1. auto. auto.
Qed. 

Lemma beq_idP : forall x y, reflect (x = y) (Nat.eqb x y).
Proof. intros. apply iff_reflect. rewrite eqb_eq. split. auto. auto. Qed.  

Theorem t_update_permute : forall (X:Type) v1 v2 x1 x2 (m : total_map X),
  x2 <> x1 -> (t_update (t_update m x2 v2) x1 v1) = (t_update (t_update m x1 v1) x2 v2).
Proof.
  intros. unfold t_update. apply functional_extensionality_dep. intros.
  destruct (beq_idP x1 x).
  - destruct (beq_idP x2 x). rewrite e in H; rewrite e0 in H. contradiction. auto.
  - destruct (beq_idP x2 x). auto. auto.
Qed.

Definition partial_map (A : Type) := total_map (option A).

Definition empty {A : Type} : partial_map A :=
  t_empty None.

Definition update {A : Type} (m : partial_map A) (x : nat) (v : A) : partial_map A := t_update m x (Some v).


Lemma apply_empty : forall A x, @empty A x = None.
Proof.
  intros. unfold empty. rewrite t_apply_empty.
  reflexivity.
Qed.

Lemma update_eq : forall A (m: partial_map A) x v,
  (update m x v) x = Some v.
Proof.
  intros. unfold update. rewrite t_update_eq.
  reflexivity.
Qed.

Theorem update_neq : forall (X:Type) v x1 x2
                       (m : partial_map X),
  x2 <> x1 ->
  (update m x2 v) x1 = m x1.
Proof.
  intros X v x1 x2 m H.
  unfold update. rewrite t_update_neq; auto.
Qed.

Lemma update_shadow : forall A (m: partial_map A) v1 v2 x,
  update (update m x v1) x v2 = update m x v2.
Proof.
  intros A m v1 v2 x1. unfold update. rewrite t_update_shadow.
  reflexivity.
Qed.

Theorem update_same : forall X v x (m : partial_map X),
  m x = Some v ->
  update m x v = m.
Proof.
  intros X v x m H. unfold update. rewrite <- H.
  apply t_update_same.
Qed.

Theorem update_permute : forall (X:Type) v1 v2 x1 x2
                                (m : partial_map X),
  x2 <> x1 ->
    (update (update m x2 v2) x1 v1)
  = (update (update m x1 v1) x2 v2).
Proof.
  intros X v1 v2 x1 x2 m. unfold update.
  apply t_update_permute.
Qed.
