Load LFindLoad.
From lfind Require Import LFind.
Unset Printing Notations.
Set Printing Implicit.

From QuickChick Require Import QuickChick.
Require Export Coq.Arith.Arith.
From Coq Require Import Bool.Bool.
From Coq Require Import Logic.FunctionalExtensionality.
From VFA Require Import Perm.

(* Definition total_map {A} : Type := nat -> A. *)

Definition total_map (A : Type) : Type := (list (nat * A)) * A.

Definition t_empty {A: Type} (v : A) : total_map A := ([], v).

Fixpoint find_helper {A} (n : nat) (v : A) (f : list (nat * A)) : A :=
  match f with
  | [] => v
  | (key,val)::tl => if key =? n then val else find_helper n v tl
  end.

Definition find {A} (m : total_map A) (n : nat) : A :=
  match m with | (f,v) => find_helper n v f end.

Fixpoint update_helper {A} (n : nat) (v : A) (f : list (nat * A)) : list (nat * A) :=
  match f with
  | [] => (n,v) :: []
  | (key,val) :: tl => if key =? n then (key,v) :: tl else (key,val) :: (update_helper n v tl)
end.

Definition t_update {A : Type} (m : total_map A) (x : nat) (val :A) : total_map A := 
  match m with | (f,v) => ((update_helper x val f),v) end.

Lemma t_apply_empty {T} (x : nat) (v : T) : (find (t_empty v) x) = v.
Proof. intros. unfold t_empty. reflexivity. Qed.

Lemma t_incr_update {T} (x n : nat) (v t : T) (l : list (nat * T)) : n <> x ->
    (n,t) :: (update_helper x v l) = (update_helper x v ((n, t) :: l)).
Proof.
 intros. unfold update_helper. destruct (eq_nat_dec n x).
  - replace (n =? x) with true. rewrite e in H. contradiction. rewrite e. apply beq_nat_refl.
  - replace (n =? x) with false. induction l. auto. auto. symmetry. rewrite Nat.eqb_neq. auto.
Qed.

(* Helper Lemma = t_incr_update : ∀ (T : Type) (x n : nat) (v t : T) (l : list (nat * T)), n ≠ x → (n, t) :: update_helper x v l = update_helper x v ((n, t) :: l) *)
Lemma t_update_eq {T} (m: total_map T) (x : nat) (v : T) : find (t_update m x v) x = v.
Proof. 
  intros. destruct m. induction l.
  - simpl. replace (x =? x) with true. auto. apply beq_nat_refl.
  - destruct a. destruct (eq_nat_dec n x).
  * rewrite e. simpl. replace (x =? x) with true. simpl. replace (x =? x) with true. auto. apply beq_nat_refl. apply beq_nat_refl.
  * unfold t_update. replace (update_helper x v ((n, t0) :: l)) with ((n,t0) :: (update_helper x v l)). simpl. replace (n =? x) with false.
    unfold t_update in IHl. unfold find in IHl. auto. symmetry. rewrite Nat.eqb_neq. auto. apply t_incr_update. auto.
Qed.

Theorem eqb_eq : forall n m, n =? m = true <-> n = m.
Proof.
  split. 
  - generalize dependent m. induction n. destruct m. reflexivity. discriminate. 
  destruct m. discriminate. simpl. intros. rewrite (IHn m H). reflexivity.
  - intros. rewrite H. symmetry. apply beq_nat_refl.
Qed.

(* Helper Lemma = t_incr_update : ∀ (T : Type) (x n : nat) (v t : T) (l : list (nat * T)), n ≠ x → (n, t) :: update_helper x v l = update_helper x v ((n, t) :: l) *)
Theorem t_update_neq {T} (x1 x2 : nat) (v : T) (m : total_map T) : x1 <> x2 -> find (t_update m x1 v) x2 = find m x2.
Proof.
  destruct m. intros. unfold t_update. 
  assert (G: x1 <> x2 -> x1 =? x2 = false). intros. unfold not in H0. rewrite <- eqb_eq in H0.
  destruct (x1 =? x2). contradiction. reflexivity. induction l. simpl. apply G in H. rewrite H. reflexivity. 
  destruct a. destruct (eq_nat_dec n x1).
  * rewrite e. unfold update_helper. replace (x1 =? x1) with true. simpl. replace (x1 =? x2) with false. reflexivity. 
    symmetry. rewrite Nat.eqb_neq. apply H. apply beq_nat_refl.
  * replace (update_helper x1 v ((n, t0) :: l)) with ((n,t0) :: (update_helper x1 v l)). simpl. destruct (n =? x2).
    reflexivity. unfold find in IHl. apply IHl. apply t_incr_update. auto.
Qed. 

Lemma t_update_shadow {A} (m: total_map A) (v1 v2 : A) (x : nat) : t_update (t_update m x v1) x v2 = t_update m x v2.
Proof.
  destruct m. unfold t_update. simpl. replace (update_helper x v2 (update_helper x v1 l)) with (update_helper x v2 l).
  reflexivity. induction l. simpl. replace (x =? x) with true. reflexivity. apply beq_nat_refl.
  destruct a0. destruct (eq_nat_dec n x).
  - rewrite e. simpl. replace (x =? x) with true. simpl. replace (x =? x) with true. reflexivity. apply beq_nat_refl. apply beq_nat_refl.
  - simpl. replace (n =? x) with false. simpl. replace (n =? x) with false. rewrite IHl. reflexivity. symmetry. apply Nat.eqb_neq. auto.
    symmetry. apply Nat.eqb_neq. auto.
Qed.

Lemma pull_first {T} (x : T) (m n : list T) : x :: m = x :: n -> m = n.
Proof. intros. inversion H. reflexivity. Qed.

Definition TotalMapEqualHelper {T} `{ _ : Dec_Eq T} (n : nat) (t t' : T)  (l l' : list (nat * T)) : Prop := find_helper n t l = find_helper n t' l'.
Definition TotalMapEqual {T} `{ _ : Dec_Eq T} (n : nat) (m m' : total_map T) : Prop := TotalMapEqualHelper n (snd m) (snd m') (fst m) (fst m').

Theorem t_update_same {T} `{ _ : Dec_Eq T} (n : nat) (x : nat) (v : T) (m : total_map T) : TotalMapEqual n (t_update m x (find m x)) m.
Proof.
  destruct m. simpl. unfold TotalMapEqual. unfold TotalMapEqualHelper. intros. simpl. induction l.
  - simpl. destruct (x =? n). reflexivity. reflexivity.
  - destruct a. simpl. destruct (eq_nat_dec n0 x).
    * rewrite e. replace (x =? x) with true. simpl. reflexivity. apply beq_nat_refl.
    * replace (n0 =? x) with false. simpl. destruct (eq_nat_dec n0 n). rewrite e; replace (n =? n) with true. reflexivity. apply beq_nat_refl.
      replace (n0 =? n) with false. apply IHl. symmetry; apply Nat.eqb_neq; auto. symmetry; apply Nat.eqb_neq; auto.
Qed.

(* Helper Lemma = iff_reflect : ∀ (P : Prop) (b : bool), P ↔ b = true → reflect P b *)
(* Helper Lemma = eqb_eq : ∀ n m : nat, (n =? m) = true ↔ n = m *)
Lemma beq_idP : forall x y, reflect (x = y) (Nat.eqb x y).
Proof. intros. 
  lfind_debug.
  Admitted.

(* apply iff_reflect. rewrite eqb_eq. split. auto. auto. Qed. *)
