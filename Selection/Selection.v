(** * Selection:  Selection Sort *)
(* Some proofs from: https://github.com/kolya-vasiliev/verified-functional-algorithms-2019/blob/master/Selection.v *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From VFA Require Import Perm.
Hint Constructors Permutation : core.
From Coq Require Export Lists.List.  (* for exercises involving [List.length] *)

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

Lemma select_rest_length : forall x l y r, select x l = (y, r) -> length l = length r.
Proof.
  intros. apply select_perm in H.
  apply Permutation_length in H. auto.
Qed.

Lemma selsort_perm: forall n l, length l = n -> Permutation l (selsort l n).
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
    apply select_rest_length in Seq. auto.
Qed.

Lemma selection_sort_perm: forall l, Permutation l (selection_sort l).
Proof. 
  unfold selection_sort. intros. 
  apply selsort_perm. reflexivity. 
Qed.

Lemma select_fst_leq: forall al bl x y, select x al = (y, bl) -> y <= x.
Proof.
  intros. 
  (* inversion H. unfold select in H. generalize dependent x; generalize dependent y. *)
  unfold select in H.
  induction al.
  intros. inversion H. auto.
  intros. fold select in IHal. apply IHal. fold select in H.  bdestruct (x <=? a).
  inversion H. unfold select.

(** [] *)

(** To represent the concept of comparing a number to a list, we
    introduce a new notation: *)

Definition le_all x xs := Forall (fun y => x <= y) xs.
Hint Unfold le_all : core.
Infix "<=*" := le_all (at level 70, no associativity).

(** **** Exercise: 1 star, standard (le_all__le_one) *)

(** Prove that if [y] is no more than any of the elements of [lst],
    and if [n] is in [lst], then [y] is no more than [n]. Hint: a
    library theorem about [Forall] and [In] will make this easy. *)

Lemma le_all__le_one : forall lst y n,
    y <=* lst -> In n lst -> y <= n.
Proof. (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 2 stars, standard (select_smallest) *)

(** Prove that the first component of [select _ _] is no bigger than
    any of the elements in the second component. Proceed by induction
    on [al]. *)

Lemma select_smallest: forall al bl x y,
    select x al = (y, bl) ->
    y <=* bl.
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 2 stars, standard (select_in) *)

(** Prove that the element returned by [select] must be one of the
    elements in its input. Proceed by induction on [al]. *)

Lemma select_in : forall al bl x y,
    select x al = (y, bl) ->
    In y (x :: al).
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 3 stars, standard (cons_of_small_maintains_sort) *)

(** Prove that adding an element to the beginning of a
    selection-sorted list maintains sortedness, as long as the element
    is small enough and enough fuel is provided. No induction is
    needed. *)

Lemma cons_of_small_maintains_sort: forall bl y n,
    n = length bl ->
    y <=* bl ->
    sorted (selsort bl n) ->
    sorted (y :: selsort bl n).
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 2 stars, standard (selsort_sorted) *)

(** Prove that [selsort] produces a sorted list when given
    sufficient fuel.  Proceed by induction on [n].  This proof
    will make use of a few previous lemmas. *)

Lemma selsort_sorted : forall n al,
    length al = n -> sorted (selsort al n).
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 1 star, standard (selection_sort_sorted) *)

(** Prove that [selection_sort] produces a sorted list. *)

Lemma selection_sort_sorted : forall al,
    sorted (selection_sort al).
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 1 star, standard (selection_sort_is_correct) *)

(** Finish the proof of correctness! *)

Theorem selection_sort_is_correct :
  is_a_sorting_algorithm selection_sort.
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(* ################################################################# *)
(** * Recursive Functions That are Not Structurally Recursive *)

(** We used fuel above to create a structurally recursive
    version of [selsort] that Coq would accept as terminating.  The
    amount of fuel decreased at each call, until it reached zero.
    Since the fuel argument was structurally decreasing, Coq accepted
    the definition.  But it complicated the implementation of
    [selsort] and the proofs about it.

    Coq provides a command [Function] that implements a similar idea
    as fuel, but without requiring the function definition to be
    structurally recursive.  Instead, the function is annotated with a
    _measure_ that is decreasing at each recursive call. To activate
    such annotations, we need to load a library. *)

Require Import Recdef.  (* needed for [measure] feature *)

(** Now we can add a [measure] annotation on the definition of
    [selsort] to tell Coq that each recursive call decreases the
    length of [l]: *)

Function selsort' l {measure length l} :=
  match l with
  | [] => []
  | x :: r => let (y, r') := select x r
            in y :: selsort' r'
end.

(** The [measure] annotation takes two parameters, a measure
    function and an argument name.  Above, the function is [length]
    and the argument is [l].  The function must return a [nat] when
    applied to the argument.  Coq then challenges us to prove that
    [length] applied to [l] is actually decreasing at every recursive
    call. *)

Proof.
  intros l x r HL y r' Hsel.
  apply select_rest_length in Hsel. inv Hsel. simpl. lia.
Defined.

(** The proof must end with [Defined] instead of [Qed].  That
    ensures the function's body can be used in computation.  For
    example, the following unit test succeeds, but try changing
    [Defined] to [Qed] and see how it gets stuck. *)

Example selsort'_example : selsort' [3;1;4;1;5;9;2;6;5] = [1;1;2;3;4;5;5;6;9].
Proof. reflexivity. Qed.

(** The definition of [selsort'] is completed by the [Function]
    command using a helper function that it generates,
    [selsort'_terminate].  Neither of them is going to be useful to
    unfold in proofs: *)

Print selsort'.
Print selsort'_terminate.

(** Instead, anywhere you want to unfold or simplify [selsort'], you
    should now rewrite with [selsort'_equation], which was
    automatically defined by the [Function] command: *)

Check selsort'_equation.

(** **** Exercise: 1 star, standard (selsort'_perm) *)

(** Hint: Follow the same strategy as [selsort_perm]. In our solution,
    there was only a one-line change. *)

Lemma selsort'_perm : forall n l,
    length l = n -> Permutation l (selsort' l).
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 1 star, standard (cons_of_small_maintains_sort') *)

(** Hint: Follow the same strategy as
    [cons_of_small_maintains_sort']. In our solution, there was only a
    one-line change. *)

Lemma cons_of_small_maintains_sort': forall bl y,
    y <=* bl ->
    sorted (selsort' bl) ->
    sorted (y :: selsort' bl).
Proof. (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 1 star, standard (selsort'_sorted) *)

(** Hint: Follow the same strategy as [selsort_sorted]. In our
    solution, there were only three small changes. *)

Lemma selsort'_sorted : forall n al,
    length al = n -> sorted (selsort' al).
Proof. (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 1 star, standard (selsort'_is_correct) *)

(** Finish the proof of correctness! *)

Theorem selsort'_is_correct :
  is_a_sorting_algorithm selsort'.
Proof. (* FILL IN HERE *) Admitted.

(** [] *)


(* ################################################################# *)
(** * Selection Sort with Multisets (Optional) *)

(** This section relies on [Multiset]. *)

From VFA Require Import Multiset.

(** Let's prove the correctness of [selection_sort] using multisets
    instead of permutations. These exercises and their proofs were
    contributed by William Ma. *)

(** **** Exercise: 3 stars, standard, optional (select_contents) *)

Lemma select_contents : forall al bl x y,
  select x al = (y, bl) ->
  union (singleton x) (contents al) = union (singleton y) (contents bl).
Proof. (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 3 stars, standard, optional (selection_sort_contents) *)

Lemma selection_sort_contents : forall n l,
  length l = n ->
  contents l = contents (selection_sort l).
Proof. (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 2 stars, standard, optional (sorted_iff_sorted) *)

Lemma sorted_iff_sorted : forall l, sorted l <-> Sort.sorted l.
Proof. (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 1 star, standard, optional (selection_sort_correct') *)

Theorem selection_sort_correct' :
  is_a_sorting_algorithm' selection_sort.
Proof. (* FILL IN HERE *) Admitted.

(** [] *)

(* 2023-08-23 11:34 *)
