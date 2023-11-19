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

Theorem insertion_sort_correct:
    is_a_sorting_algorithm sort.
Proof. unfold is_a_sorting_algorithm. intros. split. apply sort_perm. apply sort_sorted. Qed.

(* ################################################################# *)
(** * Validating the Specification (Advanced) *)
Lemma nth_error_nil : forall i, @nth_error nat [] i = None.
Proof. intros. destruct i. auto. auto. Qed.

Lemma sorted_sortedd: forall al, sorted al -> sortedd al.
Proof.
    intros. induction H. 
    - unfold sortedd. intros. rewrite nth_error_nil in H0. discriminate H0.
    - unfold sortedd. intros. inversion H. 
        rewrite <- H2 in H1. simpl in H1. rewrite nth_error_nil in H1. discriminate H1.
        rewrite <- H3 in H1. simpl in H1. rewrite nth_error_nil in H1. discriminate H1.
    - unfold sortedd. unfold sortedd in IHsorted. intros. destruct i. 
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

Lemma sortedd_sorted : forall al, sortedd al -> sorted al.
Proof.
    intros. induction al.
    - apply sorted_nil.
    - destruct al. apply sorted_1.
    unfold sortedd in H. apply sorted_cons.
    * apply H with (i:=0) (j:=1). auto. simpl. auto. simpl. auto.
    * apply IHal. unfold sortedd. intros. assert (P: S i < S j). apply lt_n_S. auto.
    apply H with (iv:=iv) (jv:=jv) in P. auto. simpl. auto. simpl. auto.
Qed. 

(* ################################################################# *)
(** * Proving Correctness from the Alternative Spec (Optional) *)

Lemma nth_error_insert : forall l a i iv,
    nth_error (insert a l) i = Some iv -> a = iv \/ exists i', nth_error l i' = Some iv.
Proof.
    intros. generalize dependent i. induction l.
    - intros. simpl in H. destruct i. simpl in H. left. inversion H. auto. simpl in H. rewrite nth_error_nil in H.
    discriminate H.
    - intros. destruct i.
    -- unfold insert in H. destruct (a <=? a0). simpl in H. inversion H. left. auto. fold insert in H.
    simpl in H. inversion H. right. exists 0. simpl; reflexivity.
    -- unfold insert in H. destruct (a <=? a0). 
        * simpl in H. right. exists i. auto.
        * fold insert in H. simpl in H. apply IHl in H. destruct H. left. auto. right. inversion H.
        exists (S x). simpl. auto.
Qed.  

Lemma sortedd_single: forall a, sortedd([a]).
Proof.
    intros. unfold sortedd. intros. destruct i.
    intros. destruct j. inversion H. simpl in H1. rewrite nth_error_nil in H1. discriminate H1.
    intros. destruct j. inversion H. simpl in H1. rewrite nth_error_nil in H1. discriminate H1.
Qed.

Lemma sortedd_nil: sortedd([]).
Proof.
    intros. unfold sortedd. intros. destruct i.
    intros. destruct j. inversion H. simpl in H1. discriminate H1.
    intros. destruct j. inversion H. simpl in H1. discriminate H1.
Qed.

(* sortedd_nil (1) *)
Lemma sortedd_remove : forall a l, sortedd (a :: l) -> sortedd l.
Proof. 
    intros. generalize dependent a. induction l.
    - intros. apply sortedd_nil.
    - intros. unfold sortedd in H. unfold sortedd. intros. assert (P: S i < S j). apply lt_n_S. auto.
    apply H with (iv:=iv) (jv:=jv) in P. auto. simpl. auto. simpl. auto.
Qed.

Lemma sortedd_remove_cons : forall a b l, a <=? b = true /\ sortedd (b :: l) -> sortedd (a :: b :: l).
Proof. 
    intros. generalize dependent a. generalize dependent b. induction l.
    - intros. destruct H. unfold sortedd. intros. destruct i. destruct j. inversion H1. simpl in H2.
    destruct j. simpl in H3. inversion H2; inversion H3. rewrite <- H5; rewrite <- H6. 
    apply leb_complete.
    auto. simpl in H3. rewrite nth_error_nil in H3. discriminate H3. simpl in H2. 
    assert (Q: exists m, j = S m). inversion H1. exists (S i). reflexivity. exists m. reflexivity.
    inversion Q. rewrite H4 in H3. simpl in H3. destruct i. destruct x.
    rewrite H4 in H1. apply lt_S_n in H1. inversion H1. simpl in H3. rewrite nth_error_nil in H3. discriminate H3. 
    simpl in H2. rewrite nth_error_nil in H2. discriminate H2.
    - intros. destruct H. assert (B: sortedd (b :: a :: l)). auto. unfold sortedd in B. assert (B': 0 < 1). auto.
    apply B with (iv:=b) (jv:=a) in B'. unfold sortedd. intros. 
    destruct i.
    * destruct j. inversion H1.
    simpl in H3. simpl in H2. destruct j. 
    simpl in H3. inversion H3; inversion H2. rewrite <- H5; rewrite <- H6. apply leb_complete. auto.
    assert (Q: 0 < S j). apply neq_O_lt. auto.
    apply B with (iv:=b) (jv:=jv) in Q. inversion H2. rewrite <- H5. apply le_trans with (m:=b).
    apply leb_complete. auto. auto. simpl. auto. auto.
    * assert (Q: exists m, j = S m). inversion H1. exists (S i). reflexivity. exists m. reflexivity.
    inversion Q. rewrite H4 in H1. rewrite H4 in H3. apply lt_S_n in H1. 
    apply B with (iv:=iv) (jv:=jv) in H1. auto. simpl in H2; simpl in H3. auto. auto.
    * simpl; auto. 
    * simpl; auto.
Qed.   

Lemma remove_false: forall P, P <-> False \/ P.
Proof. split. intros. right. auto. intros. destruct H. destruct H. auto. Qed.

Lemma simple_insert: forall a n l, n < a -> insert a (n::l) = n :: insert a l.
Proof. intros. simpl. bdestruct (a <=? n). 
    - apply leb_correct_conv in H. apply leb_correct in H0. rewrite H0 in H. discriminate H.
    - auto.
Qed.

Lemma false_to_equality: False <-> (true = false).
Proof. split. intros. contradiction. intros. discriminate H. Qed.

(* sortedd_remove_cons (5) *)
(* sortedd_single (2) *)
(* sortedd_remove (1) *)
(* simple_insert (1) *)
Lemma insert_sortedd: forall a l, sortedd l -> sortedd (insert a l).
Proof.
    intros. generalize dependent a. induction l.
    * intros. simpl. apply sortedd_single.
    * intros. unfold insert. 
    assert (P: a <=? a0 = false \/ a0 =? a = true \/ a0 <=? a = false).
    + intros. bdestruct (a <=? a0). right. inversion H0. left. symmetry. apply beq_nat_refl. right.
    rewrite H2. apply le_lt_n_Sm in H1. rewrite H2 in H1. apply leb_correct_conv. auto. auto.
    + bdestruct (a <=? a0).
    ++ rewrite <- false_to_equality in P. rewrite <- remove_false in P. destruct P.
    - symmetry in H1. symmetry in H1. rewrite Nat.eqb_eq in H1.
     rewrite H1. replace (a <=? a) with true. unfold sortedd. intros.
     destruct i.
        -- destruct j. inversion H2. 
           assert (A: nth_error (a :: l) 0 = Some iv). simpl. simpl in H3. auto.
            simpl in H4. destruct j.
            --- rewrite A in H4. inversion H4. auto.
            --- unfold sortedd in H. apply H with (i:=0) (j:= S j). apply neq_O_lt. auto. auto. auto.
        --  assert (Q: exists m, j = S m). inversion H2. exists (S i). reflexivity. exists m. reflexivity.
            inversion Q. rewrite H5 in H4. simpl in H3; simpl in H4. unfold sortedd in H. 
            apply H with (i:=i) (j:=x). rewrite H5 in H2. apply lt_S_n in H2. auto. auto. auto.
        -- symmetry. apply leb_correct. auto.
    - rewrite H1. destruct l. 
    -- simpl. apply sortedd_remove_cons. split. apply leb_correct. auto. apply sortedd_single.
    -- assert (Q: sortedd (a :: n :: l)). auto. unfold sortedd in Q.
        assert (R: 0 < 1). auto. apply Q with (iv:=a) (jv:=n) in R.
        unfold insert. unfold insert in H. bdestruct (a0 <=? n). apply sortedd_remove_cons. 
        split. apply leb_correct. auto.
        auto. apply leb_correct in H0. apply leb_complete_conv in H1. unfold gt in H2. 
         apply sortedd_remove_cons. split. apply leb_correct. auto. 
         eapply sortedd_remove. eauto.
         fold insert. apply sortedd_remove_cons. split. apply leb_correct. auto.
         unfold gt in H2. replace (n :: insert a0 l) with (insert a0 (n::l)).
         apply IHl. eapply sortedd_remove. eauto. apply simple_insert. auto.
         auto. auto.
    ++ unfold gt in H0. apply leb_correct in H0. apply leb_complete in H0. apply le_S in H0. apply le_S_n in H0.
    apply leb_correct in H0. rewrite H0. 
    lfind_debug.
    Admitted.

    (* apply sortedd_remove_cons. split. auto. auto.
Qed. *)