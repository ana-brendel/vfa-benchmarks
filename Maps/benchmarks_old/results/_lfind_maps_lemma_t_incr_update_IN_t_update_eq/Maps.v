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

Definition TotalMapEqualHelper {T} `{ _ : Dec_Eq T} (n : nat) (t t' : T)  (l l' : list (nat * T)) : Prop := find_helper n t l = find_helper n t' l'.
Definition TotalMapEqual {T} `{ _ : Dec_Eq T} (n : nat) (m m' : total_map T) : Prop := TotalMapEqualHelper n (snd m) (snd m') (fst m) (fst m').  

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
    unfold t_update in IHl. unfold find in IHl. auto. symmetry. rewrite Nat.eqb_neq. auto. 
    lfind_debug.
    Admitted.
    
    (* apply t_incr_update. auto.
Qed. *)
