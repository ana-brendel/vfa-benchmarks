(** * Sort: Insertion Sort *)
(* Some proofs rom https://github.com/kolya-vasiliev/verified-functional-algorithms-2019/blob/master/Sort.v *)

From VFA Require Import Perm. 

Fixpoint insert (i:nat) (l: list nat) := 
    match l with
    | nil => i::nil
    | h::t => if i <=? h then i::h::t else h :: insert i t
end.

Fixpoint sort (l: list nat) : list nat :=
    match l with
    | nil => nil
    | h::t => insert h (sort t)
end.

Inductive sorted: list nat -> Prop := 
| sorted_nil:
    sorted nil
| sorted_1: forall x,
    sorted (x::nil)
| sorted_cons: forall x y l,
    x <= y -> sorted (y::l) -> sorted (x::y::l).

Definition sorted' (al: list nat) :=
forall i j, i < j < length al -> nth i al 0 <= nth j al 0.
    
Definition is_a_sorting_algorithm (f: list nat -> list nat) :=
    forall al, Permutation al (f al) /\ sorted (f al).

Lemma insert_perm: forall x l,  Permutation (x :: l) (insert x l).
Proof.
  intros. induction l.
  - simpl. auto.
  - simpl. destruct (x <=? a). auto.
    apply perm_trans with (l' := (a :: x :: l)). apply perm_swap. apply perm_skip. auto.
Qed.

Theorem sort_perm: forall l, Permutation l (sort l).
Proof. induction l. 
    + apply Permutation_refl.
    + apply perm_trans with (a::(sort l)).
    * apply perm_skip. assumption.
    * simpl. apply insert_perm.
Qed.

Lemma insert_sorted:
    forall a l, sorted l -> sorted (insert a l).
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
Proof. induction l. 
    * constructor.
    * apply insert_sorted. assumption. Qed.

Theorem insertion_sort_correct: is_a_sorting_algorithm sort.
Proof. split. apply sort_perm. apply sort_sorted. Qed.

(* ################################################################# *)
(** * Making Sure the Specification is Right *)

Lemma nth_error_nil : forall i, @nth_error nat [] i = None.
Proof. intros. destruct i. auto. auto. Qed.

Lemma sorted_sorted': forall al, sorted al -> sorted' al.
Proof.
    intros. induction H. 
    - unfold sorted'. intros. inversion H. simpl in H1. inversion H1.
    - unfold sorted'. intros. inversion H. simpl in H1. inversion H1. rewrite H3 in H0. contradiction.
        rewrite <- H2 in H1. simpl in H1. rewrite nth_error_nil in H1. discriminate H1.
        rewrite <- H3 in H1. simpl in H1. rewrite nth_error_nil in H1. discriminate H1.
    - unfold sorted'. unfold sorted' in IHsorted. intros. destruct i. 
        + destruct j. inversion H1. simpl in H2. inversion H2. simpl in H3.
            bdestruct (0 <=? j).
            * inversion H4. rewrite <- H6 in H3. simpl in H3. inversion H3. rewrite <- H8. rewrite <- H5. auto.
            assert (P: nth_error (y :: l) 0 = Some y). simpl. auto. assert (Q: 0 < S m). apply neq_O_lt. auto.
            assert (R: y <= jv). apply IHsorted with (i:= 0) (j:= S m). auto. auto. rewrite H7. auto.
            apply le_trans with (m:= y). rewrite <- H5. auto. auto.
            * unfold gt in H4. inversion H4.
        + assert (P: exists m, j = S m). inversion H1. exists (S i). reflexivity. exists m. reflexivity.
        inversion P. rewrite H4 in H3. simpl in H2; simpl in H3. rewrite H4 in H1. apply lt_S_n in H1.
        apply IHsorted with (iv:=iv) (jv:=jv) in H1. auto. auto. auto.
Qed. 

Lemma sorted'_sorted: forall al, sorted' al -> sorted al.
Proof. 
    induction al. 
    * constructor. 
    * unfold sorted' in *. intro H. 
    destruct al; constructor.
    + apply (H 0 1). simpl. omega.
    + apply IHal.  
        intros. apply (H (S i) (S j)).
        simpl in *. omega.
Qed.
(** [] *)

(* ################################################################# *)
(** * Proving Correctness from the Alternate Spec *)

(** Depending on how you write the specification of a program, it can
    be _much_ harder or easier to prove correctness.  We saw that the
    predicates [sorted] and [sorted'] are equivalent; but it is really
    difficult to prove correctness of insertion sort directly from
    [sorted'].

    Try it yourself, if you dare!  I managed it, but my proof is quite
    long and complicated.  I found that I needed all these facts:
    - [insert_perm], [sort_perm]
    - [Forall_perm], [Permutation_length]
    - [Permutation_sym], [Permutation_trans]
    - a new lemma [Forall_nth], stated below.

    Maybe you will find a better way that's not so complicated.

    DO NOT USE [sorted_sorted'], [sorted'_sorted], [insert_sorted], or
    [sort_sorted] in these proofs! *)

(** **** Exercise: 3 stars, optional (Forall_nth)  *)
Lemma Forall_nth:
    forall {A: Type} (P: A -> Prop) d (al: list A),
    Forall P al <-> (forall i,  i < length al -> P (nth i al d)).
Proof. intros. split; intro H. 
    - induction H.
    * intros. inversion H.
    * intros. destruct i.
        + assumption.
        + apply IHForall. simpl in H1. omega.
    - induction al; constructor.
    apply (H 0). simpl. omega.
    apply IHal.
    intros. apply (H (S i)). simpl. omega.
Qed.

(** [] *)


(** **** Exercise: 4 stars, optional (insert_sorted')  *)
Lemma insert_sorted':
    forall a l, sorted' l -> sorted' (insert a l).
Proof. unfold sorted'. 
    induction l; intros.
    - simpl in H0. assert (i=0 /\ j=0). omega.
    destruct H1. subst. constructor. 
    - destruct i, j.
    * omega.
    * simpl. 
        simpl in H0.
        bdestruct (a <=? a0).
        + apply le_trans with a0. assumption.
        destruct j. constructor.
        apply (H 0 (S j)). 
        simpl. simpl in H0. omega.
        + specialize (H 0).
        assert (Forall (fun n => a0 <= n) l).
        {
            rewrite (Forall_nth). intros. apply (H (S i)).
            simpl. omega.       
        }

        assert (Forall (fun n => a0 <= n) (a::l)).
        {
            constructor.
            omega. assumption.
        }
        
        assert (Forall (fun n : nat => a0 <= n) (insert a l)).
        {
            apply Forall_perm with (a :: l).
            apply insert_perm.
            assumption.
        }
        
        rewrite Forall_nth in H4.

        apply H4. simpl in H0. omega.

    * omega.
    * simpl. simpl in H0. 
    bdestruct (a <=? a0).
    + apply H. simpl. simpl in H0. omega.
    + apply IHl; try (simpl in H0; omega).
        intros. apply (H (S i0) (S j0)). simpl. omega.      
Qed.

(** [] *)

(** **** Exercise: 4 stars, optional (insert_sorted')  *)
Theorem sort_sorted': forall l, sorted' (sort l).
Proof. induction l. 
    - unfold sorted'. intros. simpl in H. assert (i=0 /\ j=0). omega.
    destruct H0. subst. constructor.
    - simpl. apply insert_sorted'. assumption.  
Qed.
