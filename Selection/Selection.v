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
  - pose (select_perm n (x::l)). pose (select_exists (x::l) n). inversion e. inversion H2.
  apply p in H3. apply in_inv in H0. destruct H0.
  -- rewrite <- H0. auto.
  -- rewrite Forall_forall in H1. apply H1. auto.
Qed.

(* I think this is a good example of where forward reasoning makes targeting lemmas easier *)
Lemma select_smallest: forall al bl x y, select x al = (y, bl) -> y <=* bl.
Proof.
  intros. unfold le_all. 
  generalize dependent bl; generalize dependent x; generalize dependent y. induction al.
  - intros. inversion H. auto.
  - intros. unfold select in H. bdestruct (x <=? a).
  * fold select in H. pose (select_exists al x). inversion e. inversion H1.
  rewrite H2 in H. inversion H2. apply IHal in H2. inversion H. apply Forall_cons.
  ** apply le_trans with (m:=x). rewrite <- H5. eapply select_fst_leq. eauto. auto.
  ** rewrite <- H5. auto.
  * fold select in H. pose (select_exists al a). inversion e. inversion H1. rewrite H2 in H.
  inversion H2.  apply IHal in H2. inversion H. apply Forall_cons.
  ** rewrite <- H5. apply lt_n_Sm_le. apply lt_S. apply Nat.le_lt_trans with (m:=a). 
  eapply select_fst_leq. eauto. auto.
  ** rewrite <- H5. auto.
Qed. 
   
Lemma select_in : forall al bl x y, select x al = (y, bl) -> In y (x :: al).
Proof. intros.
  generalize dependent bl; generalize dependent x; generalize dependent y. induction al.
  - intros. inversion H. simpl. left. reflexivity.
  - intros. 
  * inversion H. bdestruct (x <=? a). 
  ** simpl. apply or_comm. apply or_assoc. 
  right. apply or_comm. replace (x = y \/ In y al) with (In y (x :: al)).
  pose (select_exists al x). inversion e. inversion H2. rewrite H3 in H1. 
  inversion H1. eapply IHal. rewrite <- H5. eauto. simpl. reflexivity.
  ** apply select_perm in H. eapply Permutation_in. apply Permutation_sym. eauto. 
  simpl. left. auto.
Qed.

Lemma cons_of_small_maintains_sort: forall bl y n,
  n = length bl -> y <=* bl -> sorted (selsort bl n) -> sorted (y :: selsort bl n).
Proof.
  intros. symmetry in H. apply selsort_perm in H. induction (selsort bl n).
  - apply sorted_1.
  - apply sorted_cons. eapply le_all__le_one. eauto. eapply Permutation_in. 
  apply Permutation_sym. eauto. simpl. auto. auto.
Qed.

Lemma selsort_sorted : forall n al, length al = n -> sorted (selsort al n).
Proof.
  intros. generalize dependent al. induction n.
  - intros. assert (P : al = []). destruct al. auto. simpl in H. inversion H. 
  rewrite P. simpl. apply sorted_nil.
  - intros. destruct al. simpl in H. inversion H.
  simpl in H. inversion H. simpl. pose (select_exists al n0).
  inversion e. inversion H0.
  rewrite H2. apply cons_of_small_maintains_sort.
  + eapply select_rest_length. eauto.
  + eapply select_smallest. eauto.
  + rewrite H1. apply IHn. rewrite <- H1. symmetry. eapply select_rest_length. eauto.
Qed. 

Lemma selection_sort_sorted : forall al, sorted (selection_sort al).
Proof.
  unfold selection_sort. intros. apply selsort_sorted. reflexivity.
Qed.

Theorem selection_sort_is_correct : is_a_sorting_algorithm selection_sort.
Proof.
  unfold is_a_sorting_algorithm. intros. split.
  apply selection_sort_perm. apply selection_sort_sorted.
Qed.

(* ################################################################# *)
(** * Recursive Functions That are Not Structurally Recursive *)

Require Import Recdef.  (* needed for [measure] feature *)

Function selsortt l {measure length l} :=
  match l with
  | [] => []
  | x :: r => let (y, r') := select x r
            in y :: selsortt r'
end.
Proof.
  intros l x r HL y r' Hsel.
  apply select_rest_length in Hsel. inv Hsel. simpl. lia.
Defined.

Lemma selsortt_perm : forall n l, length l = n -> Permutation l (selsortt l).
Proof.
  induction n.
  - intros. rewrite length_zero_iff_nil in H. subst. apply Permutation_refl.
  - intros. destruct l. inversion H. rewrite selsortt_equation. 
    destruct (select n0 l) eqn:Seq. apply perm_trans with (n1 :: l0).
    + pose (select_perm n0 l). rewrite Seq in p. apply p. auto.
    + apply perm_skip. apply IHn. simpl in H. inversion H. 
    symmetry. eapply select_rest_length. eauto.
    (* This is how dude from GitHub did it below *)
    (* + apply perm_skip. apply IHn. assert (length (n0::l) = (length (n1::l0))).
    { 
      apply Permutation_length.
      pose (select_perm n0 l).
      rewrite Seq in p.
      apply p. auto.
    } inversion H0. inversion H. reflexivity. *)
  Qed.

Lemma list_has_length {T} (l : list T): exists x, length l = x.
Proof. induction l. exists 0. reflexivity. inversion IHl. exists (S x). simpl. auto.
Qed.

Lemma cons_of_small_maintains_sortt: forall bl y,
    y <=* bl -> sorted (selsortt bl) -> sorted (y :: selsortt bl).
Proof. 
  intros. assert (L: exists x, length bl = x). apply list_has_length.
  inversion L. apply selsortt_perm in H1. induction (selsortt bl).
  - apply sorted_1.
  - apply sorted_cons. eapply le_all__le_one. eauto. eapply Permutation_in. 
  apply Permutation_sym. eauto. simpl. auto. auto.
Qed.

Lemma selsortt_sorted : forall n al, length al = n -> sorted (selsortt al).
Proof. 
  intros. generalize dependent al. induction n.
  - intros. assert (P : al = []). destruct al. auto. simpl in H. inversion H. 
  rewrite P. simpl. apply sorted_nil.
  - intros. destruct al. simpl in H. inversion H.
  simpl in H. inversion H. simpl. pose (select_exists al n0).
  inversion e. inversion H0. rewrite selsortt_equation. rewrite H2. apply cons_of_small_maintains_sortt.
  + eapply select_smallest. eauto.
  + apply IHn. rewrite <- H1. symmetry. eapply select_rest_length. eauto.
Qed. 

Theorem selsortt_is_correct :
  is_a_sorting_algorithm selsortt.
Proof. 
  unfold is_a_sorting_algorithm. intros. assert (E: exists x, length al = x). apply list_has_length.
  inversion E. split.
  eapply selsortt_perm. eauto.
  eapply selsortt_sorted. eauto.
Qed.

(* ################################################################# *)
(** * Selection Sort with Multisets (Optional) *)

(** This section relies on [Multiset] --> don't have decidability for *)

From VFA Require Import Multiset.

Lemma select_contents : forall al bl x y,
  select x al = (y, bl) ->
  union (singleton x) (contents al) = union (singleton y) (contents bl).
Proof. (* FILL IN HERE *) Admitted.

Lemma selection_sort_contents : forall n l,
  length l = n ->
  contents l = contents (selection_sort l).
Proof. (* FILL IN HERE *) Admitted.

Lemma sorted_iff_sorted : forall l, sorted l <-> Sort.sorted l.
Proof. (* FILL IN HERE *) Admitted.

Theorem selection_sort_correct' :
  is_a_sorting_algorithm' selection_sort.
Proof. (* FILL IN HERE *) Admitted.
