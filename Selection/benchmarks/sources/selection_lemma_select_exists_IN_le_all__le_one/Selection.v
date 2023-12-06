(** * Selection:  Selection Sort *)
(* Some proofs from: https://github.com/kolya-vasiliev/verified-functional-algorithms-2019/blob/master/Selection.v *)

Load LFindLoad.
From lfind Require Import LFind.
Unset Printing Notations.
Set Printing Implicit.

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From VFA Require Import Perm.
Hint Constructors Permutation : core.
From Coq Require Export Lists.List.  (* for exercises involving [List.length] *)

Definition list_length {T} (l : list T) := List.length l.

(* ################################################################# *)
(** * The Selection-Sort Program  *)
Fixpoint select (x: nat) (l: list nat) : nat * list nat :=
  match l with
  | [] => (x, [])
  | h :: t =>
    if x <=? h
    then let (j, l') := select x t
         in (j, h :: l')
    else let (j, l') := select h t
         in (j, x :: l')
  end.

Fixpoint selsort (l : list nat) (n : nat) : list nat :=
  match l, n with
  | _, O => []  (* ran out of fuel *)
  | [], _ => []
  | x :: r, S n' => let (y, r') := select x r
                  in y :: selsort r' n'
end.

Definition selection_sort (l : list nat) : list nat :=
  selsort l (length l).
  
(* ################################################################# *)
(** * Proof of Correctness *)

Inductive sorted: list nat -> Prop :=
 | sorted_nil: sorted []
 | sorted_1: forall i, sorted [i]
 | sorted_cons: forall i j l, i <= j -> sorted (j :: l) -> sorted (i :: j :: l).

Hint Constructors sorted : core.

Definition is_a_sorting_algorithm (f: list nat -> list nat) := forall al,
    Permutation al (f al) /\ sorted (f al).

Lemma select_perm: forall x l y r, select x l = (y, r) -> Permutation (x :: l) (y :: r).
Proof.
  intros x l; revert x.
  induction l; intros.
  - simpl in *. inversion H. apply Permutation_refl.
  - unfold select in H.  
    bdestruct (x <=? a); fold select in H.
    + specialize (IHl x).   
      destruct (select x l) eqn:Seq.
      apply perm_trans with (a :: n :: l0);
        try apply perm_swap.
      apply perm_trans with (a :: x :: l);
        try apply perm_swap.
      apply perm_skip.
      apply IHl. reflexivity. inversion H. rewrite <- H2.
      apply perm_swap.
    + specialize (IHl a).
      destruct (select a l) eqn:Seq.
      apply perm_trans with (x :: n :: l0);
        try apply perm_swap.
      apply perm_skip. apply IHl.
      reflexivity. inversion H. apply perm_swap.
Qed.

Lemma select_rest_length : forall x l y r, select x l = (y, r) -> list_length l = list_length r.
Proof.
  intros. apply select_perm in H.
  apply Permutation_length in H. auto.
Qed.

Lemma selsort_perm: forall n l, list_length l = n -> Permutation l (selsort l n).
Proof.
  induction n.
  - intros. rewrite length_zero_iff_nil in H.
    subst. apply Permutation_refl.
  - intros. destruct l. inversion H.
    simpl. 
    destruct (select n0 l) eqn:Seq.
    apply perm_trans with (n1 :: l0).
    apply select_perm. auto.
    apply perm_skip. apply IHn. inversion H.
    symmetry. eapply select_rest_length. eauto.
    (* apply select_rest_length in Seq. auto. *)
Qed.

Lemma selection_sort_perm: forall l, Permutation l (selection_sort l).
Proof. 
  unfold selection_sort. intros. 
  apply selsort_perm. reflexivity. 
Qed.

Lemma select_exists (l : list nat) (a : nat) : exists i j, select a l = (i ,j).
Proof.
  generalize dependent a. induction l.
  - intros. exists a. exists []. reflexivity.
  - intros. unfold select. destruct (a0 <=? a).
  + fold select. assert (P: exists i j, select a0 l = (i,j)). apply IHl.
  inversion P. inversion H. exists x. exists (a :: x0). rewrite H0. reflexivity.
  + fold select. assert (P: exists i j, select a l = (i,j)). apply IHl.
  inversion P. inversion H. exists x. exists (a0 :: x0). rewrite H0. reflexivity.
Qed.

Lemma select_fst_leq: forall al bl x y, select x al = (y, bl) -> y <= x.
Proof.
  intros. 
  unfold select in H.
  generalize dependent x; generalize dependent y; generalize dependent bl. induction al.
  - intros. inversion H. auto.
  - intros. fold select in IHal. fold select in H.  
  bdestruct (x <=? a).
  -- pose (select_exists al x).
  inversion e. inversion H1. rewrite H2 in H. apply IHal with (bl := x1). inversion H. 
  rewrite <- H4. auto.
  -- pose (select_exists al a).
  inversion e. inversion H1. rewrite H2 in H. inversion H. rewrite <- H4.
  apply IHal in H2. inversion H2. unfold gt in H0. apply lt_n_Sm_le. apply lt_S. auto. 
  unfold gt in H0. apply le_lt_n_Sm in H3. rewrite H6 in H3. assert (Q: x0 < x). 
  apply lt_trans with (m := a). auto. auto. apply lt_n_Sm_le. apply lt_S. auto.
Qed. 

Definition le_all x xs := Forall (fun y => x <= y) xs.
Hint Unfold le_all : core.
Infix "<=*" := le_all (at level 70, no associativity).

Lemma le_all__le_one : forall lst y n, y <=* lst -> In n lst -> y <= n.
Proof. 
  intros. unfold le_all in H. destruct H.
  - contradiction.
  - pose (select_perm n (x::l)). 
  lfind_debug.
  Admitted.

  (* pose (select_exists (x::l) n). inversion e. inversion H2.
  apply p in H3. apply in_inv in H0. destruct H0.
  -- rewrite <- H0. auto.
  -- rewrite Forall_forall in H1. apply H1. auto.
Qed. *)
