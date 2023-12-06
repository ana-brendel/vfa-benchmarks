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
  lfind_debug.
  Admitted.

  (* apply Permutation_length in H. auto.
Qed. *)
