(** * SearchTree: Binary Search Trees *)

Require Import Coq.Strings.String.
From VFA Require Import Perm.
Require Import FunctionalExtensionality.
Require Import Coq.Arith.Arith.

(* ################################################################# *)
(** * Total and Partial Maps *)
From vfa_benchmark Require Import LFindMaps.
(* ################################################################# *)
(** * Program for Binary Search Trees *)

Section TREES.
Variable V : Type.
Variable default: V.

Inductive tree : Type :=
| E : tree
| T: tree -> nat -> V -> tree -> tree.

Definition empty_tree : tree := E.

Fixpoint lookup (x: nat) (t : tree) : V :=
  match t with
  | E => default
  | T tl k v tr => if x <? k then lookup x tl
                        else if k <? x then lookup x tr
                        else v
  end.

Fixpoint insert (x: nat) (v: V) (s: tree) : tree :=
match s with
| E => T E x v E
| T a y v' b => if  x <? y then T (insert x v a) y v' b
                        else if y <? x then T a y v' (insert x v b)
                        else T a x v b
end.

Fixpoint elements' (s: tree) (base: list (nat*V)) : list (nat * V) :=
match s with
| E => base
| T a k v b => elements' a ((k,v) :: elements' b base)
end.

Definition elements (s: tree) : list (nat * V) := elements' s nil.

(* ################################################################# *)

(* ################################################################# *)
(** * Proof of Correctness *)

(** To build the [Abs] relation, we'll use these two auxiliary
    functions that construct maps: *)

(* In list, if above or equal to that nat, then use the other value in pair, else use the total map default 
      order of preference (most recent with higher priority) is preserved in list of pivots*)
Inductive total_map_pivot (A : Type): Type := 
  | TMP_nil : A -> (total_map_pivot A)
  | TMP_single : (total_map A) -> (total_map_pivot A)
  | TMP_cons : (total_map_pivot A)  -> nat -> (total_map_pivot A) -> (total_map_pivot A).

Fixpoint above_pivot {A} (pivot : nat) (l2 : list (nat * A)) : list (nat * A) :=
  match l2 with
  | [] => []
  | (key,val) :: tl => if key >=? pivot then (key,val) :: (above_pivot pivot tl) else (above_pivot pivot tl) 
  end.

Fixpoint below_pivot {A} (pivot : nat) (l1 : list (nat * A)) : list (nat * A) :=
  match l1 with
  | [] => []
  | (key,val) :: tl => if key <? pivot then (key,val) :: (above_pivot pivot tl) else (above_pivot pivot tl) 
  end.

Definition combine {A} (pivot: nat) (m1 m2: total_map A) : total_map_pivot A :=
  TMP_cons A (TMP_single A m1) pivot (TMP_single A m2). 

Definition combine_p {A} (pivot: nat) (m1 m2: total_map_pivot A) : total_map_pivot A := TMP_cons A m1 pivot m2. 

Definition t_empty_p {A: Type} (v : A) : total_map_pivot A := TMP_nil A v.

Fixpoint find {A} (m : total_map_pivot A) (n : nat) : A :=
  match m with 
  | TMP_nil _ v => v 
  | TMP_single _ m => LFindMaps.find m n
  | TMP_cons _ m1 p m2 => if n <? p then find m1 n else find m2 n
  end.

Fixpoint update {A : Type} (m : total_map_pivot A) (x : nat) (val :A) : total_map_pivot A := 
  match m with 
  | TMP_nil _ v => TMP_single A (LFindMaps.t_update (LFindMaps.t_empty v) x val)
  | TMP_single _ m => TMP_single A (LFindMaps.t_update m x val)
  | TMP_cons _ m1 p m2 => if x <? p then update m1 x val else update m2 x val
  end.
  
  (** [combine pivot a b] uses the map [a] on any input less than
    [pivot], and uses map [b] on any input [ >= pivot]. *)
  
  Inductive Abs:  tree -> total_map_pivot V -> Prop :=
  | Abs_E: Abs E (TMP_nil V default)
  | Abs_T: forall a b l k v r,
        Abs l a ->
        Abs r b ->
        Abs (T l k v r)  (update (combine_p k a b) k v).
  
  (** **** Exercise: 3 stars (check_example_map)  *)
  (** Prove that your [example_map] is the right one.
      If it isn't, go back and fix your definition of [example_map].
      You will probably need the [bdestruct] tactic, and [omega]. *)
  
  Theorem empty_tree_relate: Abs empty_tree (TMP_nil V default).
  Proof.
  constructor.
  Qed.

Lemma update_at_pivot {A} (k : nat) (v : A) (a b : total_map_pivot A): update (combine_p k a b) k v = TMP_cons A a k (update b k v).
Proof. Admitted.

Lemma ltb_false_lt : forall n, false = (n <? n).
Proof.
  intros. symmetry. apply not_true_is_false. unfold not. intros. apply Nat.ltb_lt in H. apply lt_irrefl in H. contradiction.
Qed.
  
  (** **** Exercise: 3 stars (lookup_relate)  *)
Theorem lookup_relate:
  forall k t cts ,
    Abs t cts -> lookup k t =  find cts k.
Proof. 
  intros. induction H.
  - reflexivity.
  - rewrite update_at_pivot. simpl. bdestruct (k <? k0).
    + auto.
    + generalize dependent r. intros. induction b.
      * simpl. intros. unfold ge in H1. destruct H1.
        ** replace (k0 <? k0) with false. replace (k0 =? k0) with true. reflexivity. apply beq_nat_refl. apply ltb_false_lt.
        ** bdestruct (k0 =? S m). rewrite H2. replace (S m <? S m) with false. reflexivity. 
          apply ltb_false_lt. bdestruct (k0 =? S m). 
          rewrite H3 in H2; contradiction. apply le_lt_n_Sm in H1. bdestruct (k0 <? S m). 
          auto. apply lt_not_le in H1. unfold ge in H4. contradiction.
      * simpl. intros. destruct H1.
        ** replace (k0 <? k0) with false. symmetry; apply t_update_eq. apply ltb_false_lt.
        ** apply le_lt_n_Sm in H1. bdestruct (k0 <? S m). replace (LFindMaps.find (t_update t k0 v) (S m))
          with (LFindMaps.find t (S m)). auto. symmetry; apply t_update_neq. unfold not. intros.
          rewrite H3 in H2. apply lt_irrefl in H2. contradiction. 
          apply lt_not_le in H1. unfold ge in H2. contradiction.
      * simpl. intros. destruct H1.
      ** replace (k0 <? k0) with false. destruct (k0 <? n). simpl. 

        




      + unfold ge in H1. destruct H1.
        ++ replace (k0 <? k0) with false. generalize dependent r. induction b.
         * simpl. replace (k0 =? k0) with true. reflexivity. apply beq_nat_refl.
         * simpl. symmetry. apply t_update_eq.
         * simpl. induction r.
         -- bdestruct (k0 <? n). 
         ** intros. apply IHb1 with (r := E). inversion H1. auto.
         ** intros. apply IHb2 with (r := E). inversion H1. auto.
         -- bdestruct (k0 <? n).
         ** intros. assert (G : Abs (T r1 n0 v0 r2) (TMP_cons V b1 n b2) -> lookup k0 (T r1 n0 v0 r2) = find b1 k0). intros. auto. apply IHb1 in G. auto.
  
  
    intros. induction H.
    - reflexivity.
    - simpl. unfold t_update. unfold combine.
      rewrite IHAbs1, IHAbs2.
      bdestruct (k <? k0).
        bdestruct (k0 =? k).    
          replace (k0 <? k0) with false. rewrite H2 in H1. apply lt_irrefl in H1. contradiction. simpl. destruct k0. simpl. rewrite H2 in H1; apply lt_irrefl in H1. contradiction. rewrite H2 in H1; apply lt_irrefl in H1. contradiction. 
          (* reflexivity. *)
        bdestruct (k0 =? k).    
          bdestruct (k0 <? k). 
            rewrite H3 in H4. apply lt_irrefl in H4. contradiction. 
            rewrite H3 in H2. contradiction. 
          bdestruct (k0 <? k).
            assert (G: k < k). apply Nat.lt_trans with (m := k0). auto. auto.
            apply lt_irrefl in G. contradiction. 
            replace (k0 <? k0) with false. unfold find.
            omega.
  Qed.      
        
  
  (** [] *)
  
  (** **** Exercise: 4 stars (insert_relate)  *)
  Theorem insert_relate:
  forall k v t cts,
      Abs t cts ->
      Abs (insert k v t) (t_update cts k v).
  Proof. intros.
    induction H.
    - simpl. 
      evar (m: total_map V).
      replace (t_update (t_empty default) k v) with m. subst m.
      constructor; constructor.
      subst m. extensionality x. 
  
      unfold t_update, t_empty, combine.
      bdestruct (k =? x).
      * reflexivity.
      * destruct (x <? k); reflexivity.
    - unfold insert. bdestruct (k <? k0).
      * fold insert.
        evar (m: total_map V).
        replace (t_update
          (t_update (combine k0 a b) k0 v0)
          k v) with m. subst m.
        constructor; eassumption.
        subst m.
        assert (combine k0 (t_update a k v) b =
          t_update (combine k0 a b) k v).
        {
          extensionality x. 
          unfold t_update, combine.
          bdestruct (x <? k0).
          reflexivity.
          bdestruct (k =? x).
          omega. reflexivity.        
        } 
        rewrite H2.
        apply t_update_permute; omega.
      * fold insert.     
        bdestruct (k0 <? k).
        + evar (m: total_map V).
          replace (t_update (t_update 
            (combine k0 a b) k0 v0) k v) with m. 
          subst m.
          constructor; eassumption.
          subst m.
          assert (combine k0 a (t_update b k v) =
            t_update (combine k0 a b) k v).
          {
            extensionality x. 
            unfold t_update, combine.
            bdestruct (x <? k0).
            bdestruct (k =? x).
            omega. reflexivity.
            reflexivity.        
          } 
          rewrite H3.
          apply t_update_permute; omega.
        + assert (k0 = k). omega.
          subst. rewrite t_update_shadow.
          constructor; assumption.
  Qed.         
  
  
  (** [] *)
  
  (* ################################################################# *)
  (** * Correctness Proof of the [elements] Function *)
  
  Fixpoint list2map (el: list (nat*V)) : total_map V :=
  match el with
  | nil => t_empty default
  | (i,v)::el' => t_update (list2map el') i v
  end.
  
  
  (** Instead of doing a _formal_ proof that [elements_relate] is true,
      prove that it's false!  That is, as long as type [V] contains at
      least two distinct values. *)
  
  (** **** Exercise: 4 stars (not_elements_relate)  *)
  Theorem not_elements_relate:
    forall v, v <> default ->
    ~ (forall t cts,  Abs t cts -> list2map (elements t) = cts).
  Proof.
  intros.
  intro.
  pose (bogus := T (T E 3 v E) 2 v E).
  pose (m := t_update (t_empty default) 2 v).
  pose (m' := t_update
          (combine 2
            (t_update (combine 3 (t_empty default) (t_empty default)) 3 v)
            (t_empty default)) 2 v).
  assert (Paradox: list2map (elements bogus) = m /\ list2map (elements bogus) <> m).
  split.
  
  assert (m=m').
  subst m m'. extensionality x.
  unfold t_update, t_empty, combine.
  bdestruct (2 =? x).
    reflexivity.
    bdestruct (x <? 2).
      bdestruct (3=?x).
        omega.
        bdestruct (x <? 3).
          reflexivity. 
          reflexivity.
      reflexivity.
  rewrite H1.
  subst m'.
  apply H0.
  repeat constructor.
  
  subst bogus. intro.
  assert (list2map (elements (T (T E 3 v E) 2 v E)) 3 =
      m 3).
  rewrite H1. reflexivity.
    
  subst m. simpl in H2. unfold t_update, t_empty in H2.
  simpl in H2. apply H. assumption.
  
  destruct Paradox. apply H2. apply H1.
  Qed.
  
  Fixpoint forall_nodes (t: tree) (P: tree->nat->V->tree->Prop) : Prop :=
  match t with
  | E => True
  | T l k v r => P l k v r /\ forall_nodes l P /\ forall_nodes r P
  end.
  
  Definition SearchTreeX (t: tree) :=
  forall_nodes t
    (fun l k v r =>
        forall_nodes l (fun _ j _ _ => j<k) /\
        forall_nodes r (fun _ j _ _ => j>k)).
  
  
  Inductive SearchTree' : nat -> tree -> nat -> Prop :=
  | ST_E : forall lo hi, lo <= hi -> SearchTree' lo E hi
  | ST_T: forall lo l k v r hi,
      SearchTree' lo l k ->
      SearchTree' (S k) r hi ->
      SearchTree' lo (T l k v r) hi.
  
  Inductive SearchTree: tree -> Prop :=
  | ST_intro: forall t hi, SearchTree' 0 t hi -> SearchTree t.
  
  Lemma SearchTree'_le:
    forall lo t hi, @SearchTree' lo t hi -> lo <= hi.
  Proof. 
  induction 1; omega.
  Qed.
  
  (** Before we prove that [elements] is correct, let's consider a simpler version. *)
  
  Fixpoint slow_elements (s: tree) : list (nat * V) :=
  match s with
  | E => nil
  | T a k v b => slow_elements a ++ [(k,v)] ++ slow_elements b
  end.
  
  (** **** Exercise: 3 stars, optional (elements_slow_elements)  *)
  Theorem elements_slow_elements: elements = slow_elements.
  Proof.
  extensionality s.
  unfold elements.
  assert (forall base, elements' s base = slow_elements s ++ base).
  { 
    induction s.
    reflexivity.
    simpl. intros. rewrite IHs1, IHs2.
    rewrite <- app_assoc. 
    reflexivity.
  }
  rewrite H. Search (_ ++ [] = _).
  apply app_nil_r.
  Qed.
  
  (** [] *)
  
  Ltac IHSearchTree H1 H2 := try eapply H1;
          try eapply H2;        
          simpl; apply in_or_app; right; left;
          reflexivity.
  
  (** **** Exercise: 3 stars, optional (slow_elements_range)  *)
  Lemma slow_elements_range:
  forall k v lo t hi,
    SearchTree' lo t hi ->
    In (k,v) (slow_elements t) ->
    lo <= k < hi.
  Proof. intros.       
    generalize dependent k.  
    generalize dependent v.
    
    induction H; intros. 
    - inversion H0.
    - intros. simpl in H1.
      Search (In _ (_ ++ _) -> In _ _ \/ In _ _).    
      apply in_app_or in H1.
      destruct H1 as [H1|H1].
      * apply IHSearchTree'1 in H1.
        destruct H1.
        split. assumption.
        destruct r. 
        inversion H0. omega.     
        assert (S k <= k1 < hi) by           
          IHSearchTree IHSearchTree'1 IHSearchTree'2.      
        omega.
      * destruct H1 as [H1|H1].
        + inversion H1. subst.
          destruct r, l.
          inversion H0. inversion H.
          omega.
          
          inversion H0.
          assert (lo <= k < k0) by           
            IHSearchTree IHSearchTree'1 IHSearchTree'2.
          omega.
          
          inversion H.
          assert (S k0 <= k < hi) by           
            IHSearchTree IHSearchTree'1 IHSearchTree'2.
          omega.
          
          assert (S k0 <= k < hi) by           
            IHSearchTree IHSearchTree'1 IHSearchTree'2.
          assert (lo <= k1 < k0) by           
            IHSearchTree IHSearchTree'1 IHSearchTree'2.
          omega.
      + apply IHSearchTree'2 in H1.
        destruct H1. split; try assumption.
        
        destruct l.
        inversion H. omega.
        assert (lo <= k1 < k) by           
            IHSearchTree IHSearchTree'1 IHSearchTree'2.
        omega.
  Qed.
    
  
  (** [] *)
  
  (* ================================================================= *)
  (** ** Auxiliary Lemmas About [In] and [list2map] *)
  
  
  Lemma In_decidable:
    forall (al: list (nat*V)) (i: nat),
    (exists v, In (i,v) al) \/ (~exists v, In (i,v) al).
  Proof.
  intros.
  induction al as [ | [k v]].
  right; intros [w H]; inv H.
  destruct IHal as [[w H] | H].
  left; exists w; right; auto.
  bdestruct (k =? i).
  subst k.
  left; eauto.
  exists v; left; auto.
  right. intros [w H1].
  destruct H1. inv H1. omega.
  apply H; eauto.
  Qed.
  
  Lemma list2map_app_left:
    forall (al bl: list (nat*V)) (i: nat) v,
      In (i,v) al -> list2map (al++bl) i = list2map al i.
  Proof.
  intros.
  revert H; induction al as [| [j w] al]; intro; simpl; auto.
  inv H.
  destruct H. inv H.
  unfold t_update.
  bdestruct (i=?i); [ | omega].
  auto.
  unfold t_update.
  bdestruct (j=?i); auto.
  Qed.
  
  Lemma list2map_app_right:
    forall (al bl: list (nat*V)) (i: nat),
      ~(exists v, In (i,v) al) -> list2map (al++bl) i = list2map bl i.
  Proof.
  intros.
  revert H; induction al as [| [j w] al]; intro; simpl; auto.
  unfold t_update.
  bdestruct (j=?i).
  subst j.
  contradiction H.
  exists w; left; auto.
  apply IHal.
  contradict H.
  destruct H as [u ?].
  exists u; right; auto.
  Qed.
  
  Lemma list2map_not_in_default:
  forall (al: list (nat*V)) (i: nat),
    ~(exists v, In (i,v) al) -> list2map al i = default.
  Proof.
  intros.
  induction al as [| [j w] al].
  reflexivity.
  simpl.
  unfold t_update.
  bdestruct (j=?i).
  subst.
  contradiction H.
  exists w; left; auto.
  apply IHal.
  intros [v ?].
  apply H. exists v; right; auto.
  Qed.
  
  (** **** Exercise: 3 stars, optional (elements_relate)  *)
  Theorem elements_relate:
    forall t cts,
    SearchTree t ->
    Abs t cts ->
    list2map (elements t) = cts.
  Proof.
  rewrite elements_slow_elements.
  intros until 1. inv H.
  revert cts; induction H0; intros.
  * (* ST_E case *)
  inv H0.
  reflexivity.
  * (* ST_T case *)
  inv H.
  specialize (IHSearchTree'1 _ H5). clear H5.
  specialize (IHSearchTree'2 _ H6). clear H6.
  unfold slow_elements; fold slow_elements.
  subst.
  extensionality i.
  destruct (In_decidable (slow_elements l) i)  as [[w H] | Hleft].
  rewrite list2map_app_left with (v:=w); auto.
  pose proof (slow_elements_range _ _ _ _ _ H0_ H).
  unfold combine, t_update.
  bdestruct (k=?i); [ omega | ].
  bdestruct (i<?k); [ | omega].
  auto.
  rewrite list2map_app_right; auto.
  
  simpl.
  unfold combine, t_update.
  bdestruct (k =? i). reflexivity.
  bdestruct (i <? k); auto. 
  destruct (In_decidable (slow_elements r) i)  as [[w H'] | HH].
  pose proof (slow_elements_range _ _ _ _ _ H0_0 H').
  omega.
  apply list2map_not_in_default in Hleft.
  apply list2map_not_in_default in HH. 
  subst. assumption.
  Qed.
  
  (** [] *)
  
  (* ################################################################# *)
  (** * Preservation of Representation Invariant *)
  
  (** How do we know that all the trees we will encounter (particularly,
    that the [elements] function will encounter), have the [SearchTree]
    property?  Well, the empty tree is a [SearchTree]; and if you insert
    into a tree that's a [SearchTree], then the result is a
    [SearchTree]; and these are the only ways that you're supposed to
    build trees.  So we need to prove those two theorems. *)
  
  (** **** Exercise: 1 star (empty_tree_SearchTree)  *)
  Theorem empty_tree_SearchTree:  SearchTree empty_tree.
  Proof.
  clear default.
  apply ST_intro with 0.
  constructor. constructor.
  Qed.
    (* This is here to avoid a nasty interaction between Admitted
    and Section/Variable.  It's also a hint that the [default] value
    is not needed in this theorem. *)
  
  (** [] *)
  
  (** **** Exercise: 3 stars (insert_SearchTree)  *)
  
  Lemma SearchTree'_upperbound: forall lo t hi hi2,
  SearchTree' lo t hi -> hi <= hi2 -> SearchTree' lo t hi2.
  Proof. intros. revert H0. revert hi2. 
    induction H.
    - constructor. omega.
    - intros. constructor; auto.
  Qed.
  
  Lemma SearchTree'_lowerbound: forall lo t hi lo2,
  SearchTree' lo t hi -> lo2 <= lo -> SearchTree' lo2 t hi.
  Proof. intros. revert H0. revert lo2. 
    induction H.
    - constructor. omega.
    - intros. constructor; auto.
  Qed.
  
  
  Theorem insert_SearchTree':
    forall t k v lo hi,
    SearchTree' lo t hi -> 
      exists lo' hi', (hi' = hi \/ hi' = (S k)) /\
        (lo = lo' \/ k = lo') /\
        SearchTree' lo' (insert k v t) hi'.
  Proof. induction t; intros.
      exists k, (S k).
      repeat (split; auto).
      repeat constructor.
      
      inv H. 
      unfold insert. fold insert.
      bdestruct (k0 <? k).
      * apply (IHt1 k0 v0) in H6.
        destruct H6 as [lo2 [hi2 H6]].
        exists lo2, hi.
        repeat (split; try omega).
        constructor; auto.
        destruct H6 as [[HX|HY] [H1 H2]]; subst.
        - assumption.
        - apply SearchTree'_upperbound with (S k0).
          assumption. omega.
      * bdestruct (k <? k0).
        + apply (IHt2 k0 v0) in H7.
          destruct H7 as [lo2 [hi2 H7]].
          exists lo, hi2.
          repeat (split; try omega).
          constructor; auto. 
          destruct H7 as [H1 [[HX|HY] H2]]; subst.
          - assumption.
          - apply SearchTree'_lowerbound with (lo2).
            assumption. omega.
        + assert (k = k0) by omega; subst.
          exists lo, hi. repeat (split; auto).
          constructor; auto. 
  Qed.
  
  Theorem insert_SearchTree:
    forall k v t,
    SearchTree t -> SearchTree (insert k v t).
  Proof. 
  (* This is here to avoid a nasty interaction between Admitted and Section/Variable *)
    intros. inv H.
    apply (insert_SearchTree' _ k v) in H0.
    destruct H0 as [lo' [hi' [H1 [H2 H3]]]].
    apply ST_intro with hi'. 
    apply SearchTree'_lowerbound with lo'; [auto|omega].
  Qed.
  
  (** [] *)
  
  (* ################################################################# *)
  (** * We Got Lucky *)
  
  (** Recall the statement of [lookup_relate]: *)
  
  Check lookup_relate.
  (*  forall (k : nat) (t : tree) (cts : total_map V),
        Abs t cts -> lookup k t = cts (Id k)  *)
  
  (** In general, to prove that a function satisfies the abstraction relation,
    one also needs to use the representation invariant.  That was certainly
    the case with [elements_relate]: *)
  
  Check elements_relate.
  (*  : forall (t : tree) (cts : total_map V),
        SearchTree t -> Abs t cts -> elements_property t cts   *)
  
  (** To put that another way, the general form of [lookup_relate] should be: *)
  
  Lemma lookup_relate':
    forall (k : nat) (t : tree) (cts : total_map V),
      SearchTree t -> Abs t cts -> lookup k t = cts k.
  
  (** That is certainly provable, since it's a weaker statement than what we proved: *)
  
  Proof.
  intros.
  apply lookup_relate.
  apply H0.
  Qed.
  
  Theorem insert_relate':
  forall k v t cts,
      SearchTree t ->
      Abs t cts ->
      Abs (insert k v t) (t_update cts k v).
  Proof. intros. apply insert_relate; auto.
  Qed.
  
  (** The question is, why did we not need the representation invariant in
    the proof of [lookup_relate]?  The answer is that our particular Abs
    relation is much more clever than necessary:  *)
  
  Print Abs.
  (* Inductive Abs : tree -> total_map V -> Prop :=
      Abs_E : Abs E (t_empty default)
    | Abs_T : forall (a b: total_map V) (l: tree) (k: nat) (v: V) (r: tree),
              Abs l a ->
              Abs r b ->
        Abs (T l k v r) (t_update (combine k a b) (Id k) v)
  *)
  (** Because the [combine] function is chosen very carefully, it turns out
    that this abstraction relation even works on bogus trees! *)
  
  Remark abstraction_of_bogus_tree:
  forall v2 v3,
    Abs (T (T E 3 v3 E) 2 v2 E) (t_update (t_empty default) 2 v2).
  Proof.
  intros.
  evar (m: total_map V).
  replace  (t_update (t_empty default) 2 v2) with m; subst m.
  repeat constructor.
  extensionality x.
  unfold t_update, combine, t_empty.
  bdestruct (2 =? x).
  auto.
  bdestruct (x <? 2).
  bdestruct (3 =? x).
  (* LOOK HERE! *)
  omega.
  bdestruct (x <? 3).
  auto.
  auto.
  auto.
  Qed.
  
  (** Step through the proof to [LOOK HERE], and notice what's going on.
    Just when it seems that [(T (T E 3 v3 E) 2 v2 E)] is about to produce [v3]
    while [(t_update (t_empty default) (Id 2) v2)] is about to produce [default],
    [omega] finds a contradiction.  What's happening is that [combine 2]
    is careful to ignore any nats >= 2 in the left-hand subtree.
  
    For that reason, [Abs] matches the _actual_ behavior of [lookup],
    even on bogus trees.  But that's a really strong condition!  We should
    not have to care about the behavior of [lookup] (and [insert]) on
    bogus trees.  We should not need to prove anything about it, either.
  
    Sure, it's convenient in this case that the abstraction relation is able to
    cope with ill-formed trees.  But in general, when proving correctness of
    abstract-data-type (ADT) implementations, it may be a lot of extra
    effort to make the abstraction relation as heavy-duty as that.
    It's often much easier for the abstraction relation to assume that the
    representation is well formed.  Thus, the general statement of our
    correctness theorems will be more like [lookup_relate'] than like
    [lookup_relate].  *)
  
  (* ################################################################# *)
  (** * Every Well-Formed Tree Does Actually Relate to an Abstraction *)
  
  (** We're not quite done yet.  We would like to know that
      _every tree that satisfies the representation invariant, means something_.
  
    So as a general sanity check, we need the following theorem: *)
  
  (** **** Exercise: 2 stars (can_relate)  *)
  Lemma can_relate:
  forall t,  SearchTree t -> exists cts, Abs t cts.
  Proof. induction t; intros.
    - exists (t_empty default). constructor.
    - intros. inv H. inv H0.
      apply (SearchTree'_lowerbound _ _ _ 0) in H7; try omega.
      apply ST_intro in H6.
      apply ST_intro in H7.
      destruct (IHt1 H6). destruct (IHt2 H7).
      evar (m: total_map V).
      exists m. subst m.
      constructor; eassumption.
  Qed.
  
    
  (** [] *)
  
  (** Now, because we happen to have a super-strong abstraction relation, that
    even works on bogus trees, we can prove a super-strong can_relate function: *)
  
  (** **** Exercise: 2 stars (unrealistically_strong_can_relate)  *)
  Lemma unrealistically_strong_can_relate:
  forall t,  exists cts, Abs t cts.
  Proof. induction t; intros.
    - exists (t_empty default). constructor.
    - destruct IHt1. destruct IHt2.
      evar (m: total_map V).
      exists m. subst m.
      constructor; eassumption.
  Qed.
  (** [] *)
  
  (* ################################################################# *)
  (** * It Wasn't Really Luck, Actually *)
  
  (** In the previous section, I said, "we got lucky that the abstraction
      relation that I happened to choose had this super-strong property."
  
      But actually, the first time I tried to prove correctness of search trees,
      I did _not_ get lucky.  I chose a different abstraction relation: *)
  
  Definition AbsX (t: tree) (m: total_map V) : Prop :=
      list2map (elements t) = m.
  
  (** It's easy to prove that [elements] respects this abstraction relation: *)
  
  Theorem elements_relateX:
    forall t cts,
    SearchTree t ->
    AbsX t cts ->
    list2map (elements t) = cts.
  Proof.
  intros.
  apply H0.
  Qed.
  
  (** But it's not so easy to prove that [lookup] and [insert] respect this
      relation.  For example, the following claim is not true. *)
  
  Theorem naive_lookup_relateX:
    forall k t cts ,
      AbsX t cts -> lookup k t =  cts k.
  Abort.  (* Not true *)
  
  (** In fact, [naive_lookup_relateX] is provably false,
      as long as the type [V] contains at least two different values. *)
  
  Theorem not_naive_lookup_relateX:
    forall v, default <> v ->
      ~ (forall k t cts , AbsX t cts -> lookup k t =  cts k).
  Proof.
  unfold AbsX.
  intros v H.
  intros H0.
  pose (bogus := T (T E 3 v E) 2 v E).
  pose (m := t_update (t_update (t_empty default) 2 v) 3 v).
  assert (list2map (elements bogus) = m).
    reflexivity.
  assert (~ lookup 3 bogus = m 3). {
    unfold bogus, m, t_update, t_empty.
    simpl.
    apply H.
  }
  (** Right here you see how it is proved.  [bogus] is our old friend,
      the bogus tree that does not satisfy the [SearchTree] property.
      [m] is the [total_map] that corresponds to the elements of [bogus].
      The [lookup] function returns [default] at nat [3],
      but the map [m] returns [v] at nat [3].  And yet, assumption [H0]
      claims that they should return the same thing. *)
  apply H2.
  apply H0.
  apply H1.
  Qed.
  
  (** **** Exercise: 4 stars, optional (lookup_relateX)  *)
  Theorem lookup_relateX:
    forall k t cts ,
      SearchTree t -> AbsX t cts -> lookup k t =  cts k.
  Proof.
  intros.
  unfold AbsX in H0. subst cts.
  (* this will work:
  destruct (unrealistically_strong_can_relate t).
  replace (list2map (elements t)) with x.
  apply lookup_relate; auto.
  symmetry. apply elements_relate; auto.
  *)
  inv H. remember 0 as lo in H0.
  clear - H0.
  rewrite elements_slow_elements.
  induction H0.
  reflexivity.
  simpl. bdestruct (k <? k0).
  - destruct (In_decidable (slow_elements l) k) as [[e E]| HH].
    + rewrite (list2map_app_left _ _ _ e); auto.
    + destruct (In_decidable (slow_elements r) k) as [[e E]| HH2].
      pose proof (slow_elements_range k e _ _ _ H0_0 E).
      omega. 
      rewrite (list2map_app_right); auto.
      apply list2map_not_in_default in HH.
      apply list2map_not_in_default in HH2.    
      simpl. unfold t_update. bdestruct (k0 =? k).
      omega. rewrite IHSearchTree'1, HH, HH2.
      reflexivity.
  - bdestruct (k0 <? k).
    + destruct (In_decidable (slow_elements l) k) as [[e E]| HH].
      * pose proof (slow_elements_range k e _ _ _ H0_ E).
        omega.
      * rewrite list2map_app_right; auto.
        simpl. unfold t_update. bdestruct (k0 =? k);
        [omega | auto].
    + assert (k = k0) by omega. subst.
      destruct (In_decidable (slow_elements l) k0) as [[e E]| HH].
      pose proof (slow_elements_range k0 e _ _ _ H0_ E).
      omega. rewrite (list2map_app_right); auto.
      simpl. unfold t_update. rewrite Nat.eqb_refl. reflexivity.  
  Qed.      
  
  (** To prove this, you'll need to use this collection of facts:
    [In_decidable], [list2map_app_left], [list2map_app_right],
    [list2map_not_in_default], [slow_elements_range].  The point is,
    it's not very pretty. *)
  
  (** [] *)
  
  (* ================================================================= *)
  (** ** Coherence With [elements] Instead of [lookup] *)
  (** The first definition of the abstraction relation, [Abs], is "coherent"
      with the [lookup] operation, but not very coherent with the [elements]
      operation.  That is, [Abs] treats all trees, including ill-formed ones,
      much the way [lookup] does, so it was easy to prove [lookup_relate].
      But it was harder to prove [elements_relate].
  
      The alternate abstraction relation, [AbsX], is coherent with [elements],
      but not very coherent with [lookup].  So proving [elements_relateX] is
      trivial, but proving [lookup_relate] is difficult.
  
      This kind of thing comes up frequently.  The important thing to remember
      is that you often have choices in formulating the abstraction relation,
      and the choice you make will affect the simplicity and elegance of your
      proofs.   If you find things getting too difficult, step back and reconsider
      your abstraction relation. *)
  
  End TREES.