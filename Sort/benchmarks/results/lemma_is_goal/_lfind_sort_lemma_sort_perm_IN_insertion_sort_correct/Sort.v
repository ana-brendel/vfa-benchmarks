(** * Sort: Insertion Sort *)
(* From Verified Functional Algorithms Textbook *)
Load LFindLoad.
From lfind Require Import LFind.
Unset Printing Notations.
Set Printing Implicit.
Require Export Coq.Arith.Arith.

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From VFA Require Import Perm.

(* ################################################################# *)
(** * The Insertion-Sort Program *)

Fixpoint insert (i : nat) (l : list nat) :=
  match l with
  | [] => [i]
  | h :: t => if i <=? h then i :: h :: t else h :: insert i t
  end.

Fixpoint sort (l : list nat) : list nat :=
  match l with
  | [] => []
  | h :: t => insert h (sort t)
  end.

Inductive sorted : list nat -> Prop :=
| sorted_nil :
    sorted []
| sorted_1 : forall x,
    sorted [x]
| sorted_cons : forall x y l,
    x <= y -> sorted (y :: l) -> sorted (x :: y :: l).

Definition sortedd (al : list nat) := forall i j iv jv,
    i < j ->
    nth_error al i = Some iv ->
    nth_error al j = Some jv ->
    iv <= jv.

Definition is_a_sorting_algorithm (f: list nat -> list nat) := forall al,
    Permutation al (f al) /\ sorted (f al).

(* ################################################################# *)
(** * Proof of Correctness *)

Lemma insert_sorted: forall a l, sorted l -> sorted (insert a l).
Proof. 
    intros. induction H.
    - constructor.
    - simpl. bdestruct (a <=? x).
    apply sorted_cons. auto. apply sorted_1. 
    apply sorted_cons. unfold gt in H. apply lt_S in H. unfold lt in H. apply le_S_n. auto. apply sorted_1.
    - bdestruct (a <=? x).
    * unfold insert. replace (a <=? x) with true. constructor. auto. apply sorted_cons. auto. auto.
    symmetry. apply leb_correct. auto.
    * unfold insert. replace (a <=? x) with false. unfold insert in IHsorted. bdestruct (a <=? y).
        + constructor. unfold gt in H1. apply lt_S in H1. unfold lt in H1. apply le_S_n. auto. auto.
        + fold insert. fold insert in IHsorted. apply sorted_cons. auto. auto.
        + symmetry. apply leb_correct_conv. auto.
Qed.

Theorem sort_sorted: forall l, sorted (sort l).
Proof.
  induction l.
  * simpl. apply sorted_nil.
  * unfold sort. fold sort. unfold sort in IHl. fold sort in IHl. apply insert_sorted. auto.
Qed.

Lemma insert_perm: forall x l,
    Permutation (x :: l) (insert x l).
Proof.
  intros. induction l.
  - simpl. auto.
  - simpl. destruct (x <=? a). auto.
    apply perm_trans with (l' := (a :: x :: l)). apply perm_swap. apply perm_skip. auto.
Qed.

Theorem sort_perm: forall l, Permutation l (sort l).
Proof.
    induction l.
    - auto.
    - unfold sort. fold sort. apply perm_trans with (l' := (a :: (sort l))).
    -- apply perm_skip. auto.
    -- apply insert_perm.
Qed. 

Theorem insertion_sort_correct: is_a_sorting_algorithm sort.
Proof. unfold is_a_sorting_algorithm. intros. split. 
    lfind_debug.
    Admitted.
    (* apply sort_perm. apply sort_sorted. Qed. *)
