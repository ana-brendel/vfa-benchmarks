Load LFindLoad.
Load LFindLoad.
(* From vfa_benchmark Require Import Perm. *)

From lfind Require Import LFind.
Require Import Coq.Strings.String.
Require Export Permutation.
From Coq Require Export Lists.List.
Export ListNotations.

Lemma lfind_state   (l : nat) (f : nat) (b : nat) (y : nat) (utter : list nat) : @Permutation nat
  (@app nat (@app nat (@cons nat b (@nil nat)) utter)
     (@cons nat f (@cons nat l (@cons nat y (@nil nat)))))
  (@app nat (@app nat (@cons nat f (@cons nat l (@nil nat))) utter)
     (@cons nat b (@cons nat y (@nil nat)))).
Admitted.

From QuickChick Require Import QuickChick.
QCInclude "/home/anabrendel/lfind/vfa-benchmarks/Perm/benchmarks/_lfind_perm_lemma_app_assoc_IN_butterfly-1/".
QCInclude ".".
Extract Constant defNumTests => "50".
Require Import String. Open Scope string.
Derive Show for nat.
Derive Arbitrary for nat.
Instance Dec_Eq_nat : Dec_Eq nat.
Proof. dec_eq. Qed.


Definition ElementList {A} `{_ : Dec_Eq A} := list (A * nat).

Fixpoint allElementsIn {A} `{_ : Dec_Eq A} (n m : ElementList) : Prop :=
   match n with
   | [] => True
   | hd :: tl => In hd m /\ allElementsIn tl m
   end.

Definition elementList_eq {A} `{_ : Dec_Eq A} (n m : ElementList) : Prop := (allElementsIn n m) /\ (allElementsIn m n).

Fixpoint addOccurance {A} `{_ : Dec_Eq A} (x : A) (n : ElementList) : ElementList :=
   match n with 
   | [] => [(x,1)]
   | (hd,c) :: tl => if (dec_eq hd x) then (hd,(c+1)) :: tl else (hd,c) :: (addOccurance x tl)
   end.

Fixpoint getElementList {A} `{_ : Dec_Eq A} (n : list A) : ElementList :=
   match n with 
   | [] => []
   | hd :: tl => addOccurance hd (getElementList tl)
   end.

Lemma removeFalse : forall P, P <-> (False \/ P).
Proof. split. intros. right. apply H. intros. destruct H. contradiction. apply H. Qed.


Lemma propDecHelper : forall P Q, {P} + {~P} -> {Q} + {~Q} -> {Q \/ P} + {~ (Q \/ P)}.
Proof.
   intros. inversion H.
   - left. right. auto.
   - inversion H0. left. left. auto. right. unfold not. intros. inversion H3. 
   contradiction. contradiction.
Qed.

Instance In_dec {A} `{_ : Dec_Eq A} (x : A) (n : list A)  : Dec (In x n).
Proof. 
   dec_eq. induction n.
   - right. auto.
   - destruct (dec_eq x a).
   -- rewrite e. left. simpl. left. auto.
   -- simpl. assert (G: {a = x} + {~(a = x)}). dec_eq. apply propDecHelper. auto. auto.
Qed.

Instance NoDup_dec {A} `{_ : Dec_Eq A} (n : list A)  : Dec (NoDup n).
Proof. 
   dec_eq. induction n.
   - left. apply NoDup_nil.
   - destruct (IHn).
   + destruct (In_dec a n). inversion dec. 
   ++ right. unfold not. intros. apply NoDup_remove_2 with (l := []) in H1. simpl in H1. contradiction.
   ++ left. apply NoDup_cons. auto. auto.
   + right. unfold not; intros. apply NoDup_remove_1 with (l := []) in H0. simpl in H0. contradiction.
Qed. 

Lemma dec_implies_dec (P Q : Prop): (P <-> Q) -> ({P} + {~P} -> {Q} + {~Q}).
Proof.
   intros. inversion H0. apply H in H1. left. auto. right. unfold not. intros. unfold not in H1.
   apply H1. apply H. auto.
Qed.

(* Instance Permutation_dec {A} `{_ : Dec_Eq A} (n m : list A)  : Dec (Permutation n m).
Proof. 
   dec_eq. generalize dependent m. induction n. 
   - intros. destruct m. left. auto. right. unfold not; intros. apply Permutation_nil_cons in H0. contradiction.
   - intros. destruct m.
   -- right. unfold not; intros. apply Permutation_sym in H0; apply Permutation_nil_cons in H0. contradiction.
   --    *)

Fixpoint checkTransitive {A} `{_ : Dec_Eq A} (m n : list A) : bool :=

Fixpoint isPerm {A} `{_ : Dec_Eq A} (m n : list A) : bool :=
   match m,n with
   | [],[] => true
   | x :: m', y :: n' =>
      if (dec_eq x y) then (isPerm m' n')
      else match m',n' with
      | [],[] => false
      | x' :: m'', y' :: n'' =>
         if (dec_eq x' y) then (if (dec_eq x y') then (isPerm m'' n'') else )

Lemma permNoDupHelper {A} `{_ : Dec_Eq A} (n m: list A) : Permutation n m -> ((NoDup n) /\ (NoDup m)).
Proof.
   intros. generalize dependent n. induction m.
   - intros. destruct n. auto. split. apply NoDup_nil. apply NoDup_nil. apply Permutation_sym in H0. apply Permutation_nil_cons in H0. contradiction.
   - intros. apply Permutation_NoDup in H0 as G. apply Permutation_NoDup' in H0 as K. split.
   apply K. auto. auto. 

Lemma tieTogether {A} `{_ : Dec_Eq A} (n m: list A) : ((NoDup n) /\ (NoDup m) /\ (forall a, In a n <-> In a m)) <-> Permutation n m.
Proof. 
   split. intros. destruct H0. destruct H1. apply NoDup_Permutation. auto. auto. auto.
   intros. split. 
   
Instance Permutation_dec {A} `{_ : Dec_Eq A} (n m : list A)  : Dec (Permutation n m).
Proof. 
   dec_eq.   


Lemma if__eq {A} `{_ : Dec_Eq A}  (m n : list A) : Permutation n m -> elementList_eq (getElementList n) (getElementList m).
Proof.
   generalize dependent m. induction n.
   - intros. destruct m. simpl. unfold elementList_eq. simpl. auto. apply Permutation_nil_cons in H0. contradiction.
   - intros. destruct m. 
      -- apply Permutation_sym in H0; apply Permutation_nil_cons in H0. contradiction.
      -- unfold elementList_eq. split.
      * simpl. apply NoDup_Permutation 


Lemma helper {A} (a : A) (m : list A) : ~Permutation m (a :: m).
Proof.
   unfold not. intros. induction m.
   - apply Permutation_nil_cons in H. auto.
   - assert (G: Permutation (a :: a0 :: m) (a0 :: a :: m)). apply perm_swap.
   assert (I: Permutation (a0 :: m) (a0 :: a :: m)). apply perm_trans with (l' := (a :: a0 :: m)).
   auto. auto. apply Permutation_cons_inv in I. apply IHm. auto.
Qed.

Fixpoint inb {A} `{_ : Dec_Eq A}  (x : A) (l : list A) : bool := 
   match l with
   | [] => false
   | y :: l' => if (dec_eq x y) then true else (inb x l')
   end..

Fixpoint removeOnce {A} `{_ : Dec_Eq A}  (x : A) (l : list A) : list A := 
   match l with
   | [] => []
   | y :: l' => if (dec_eq x y) then l' else (y :: (removeOnce x l'))
   end.

Fixpoint isPermutation {A} `{_ : Dec_Eq A}  (m n : list A) : bool :=
   match m,n with
   | [],[] => true
   | [], _ => false
   | _, [] => false
   | x :: m', y => if (inb x y) then (isPermutation m' (removeOnce x y)) else false
   end.


Lemma flip_ins {A} `{_ : Dec_Eq A}  (a a0 x : A) (l : list A) : inb x (a0 :: a :: l) = inb x (a :: a0 :: l).
Proof.
   simpl. destruct (dec_eq x a0). destruct (dec_eq x a). auto. auto. destruct (dec_eq x a). auto. reflexivity.
Qed.

Lemma in_cons {A} `{_ : Dec_Eq A}  (a x : A) (l : list A) : a <> x /\ inb x (a :: l) = true -> inb x l = true.
Proof. 
   intros. destruct H0. induction l.
   - simpl in H1. destruct (dec_eq x a). rewrite e in H0. contradiction. discriminate H1.
   - unfold inb. destruct (dec_eq x a0). simpl. reflexivity. rewrite flip_ins in H1. 
   fold inb.  destruct (dec_eq x a). 
   + apply IHl. rewrite e. auto.
   + apply IHl. inversion  H1. simpl. destruct (dec_eq x a).  destruct (dec_eq x a0). auto. auto.
   destruct (dec_eq x a0). rewrite e in n. contradiction. reflexivity.
Qed.
   
Lemma inConstruction {A} `{_ : Dec_Eq A}  (x : A) (l : list A) : inb x l = true -> exists n m, l = app n (x :: m) /\ inb x n = false.
Proof. 
   intros. induction l.
   - simpl in H0. discriminate H0.
   - destruct (dec_eq a x).
   + exists []. exists l. rewrite e. auto.
   + assert (inb x l = true).
   * apply in_cons with (a0 := a). auto.
   * apply IHl in H1. inversion H1. inversion H2. destruct H3. rewrite H3 in H0. exists (a :: x0). exists x1.
   simpl. rewrite H3. split. reflexivity. destruct (dec_eq x a). rewrite e in n. contradiction. apply H4.
Qed.

Lemma removeRemoveOnce {A} `{_ : Dec_Eq A}  (x : A) (l k : list A) : inb x l = false -> removeOnce x (app l (x :: k)) = app l k.
Proof.
   intros. simpl. induction l.
   - simpl. destruct (dec_eq x x). auto. contradiction.
   - simpl. destruct (dec_eq x a). 
   + rewrite e in H0. simpl in H0. destruct (dec_eq a a). discriminate H0. contradiction.
   + simpl. f_equal. apply IHl. inversion H0. destruct (dec_eq x a). discriminate H2. reflexivity.
Qed.

Lemma if_isPerm_eq {A} `{_ : Dec_Eq A}  (m n : list A) : Permutation n m -> (isPermutation n m) = true.
Proof.
   intros. generalize dependent m. induction n.
   - destruct m. auto. intros. apply Permutation_nil_cons in H0. contradiction.
   - destruct m. 
   -- intros. apply Permutation_sym in H0. apply Permutation_nil_cons in H0. contradiction.
   -- intros. destruct (dec_eq a a0).
   + rewrite e. rewrite e in H0. apply Permutation_cons_inv in H0. simpl. destruct (dec_eq a0 a0).
   apply IHn. apply H0. contradiction.
   + unfold isPermutation. simpl. destruct (dec_eq a a0). rewrite e in n0. contradiction. 
   (* assert (G: inb a m = true -> exists j k, (removeOnce a m) = app j k). apply remove_inConstruction. *)
   assert (I: inb a m = true -> exists p q, m = app p (a :: q) /\ inb a p = false). apply inConstruction.
   destruct (inb a m). 
   ++ assert (Z: exists p q : list A, m = app p (a :: q) /\ inb a p = false). apply I. reflexivity.  
   fold isPermutation. apply IHn. inversion Z. inversion H1. destruct H2. rewrite H2. 
   replace (removeOnce a (app x (a :: x0))) with (app x x0).
   * apply Permutation_sym. Admitted.

Lemma contra_if_isPerm_eq {A} `{_ : Dec_Eq A}  (m n : list A) : (isPermutation n m) = false -> ~Permutation n m.
Proof.
   intros. generalize dependent m. induction n. 
   - destruct m. unfold not; intros. simpl in H0. discriminate H0. intros. apply Permutation_nil_cons.
   - induction m. 
   + unfold not; intros. apply Permutation_sym in H1. apply Permutation_nil_cons in H1. contradiction.
   + destruct (dec_eq a a0). 
   * rewrite e. intros. simpl in H0. destruct (dec_eq a0 a0). assert (G: Permutation (a0 :: n) (a0 :: m) <-> Permutation n m). 
   split. intros. apply Permutation_cons_inv in H1. auto. intros. apply perm_skip. auto.
   rewrite G. apply IHn. apply H0. contradiction.
   * 
   


Lemma fi_isPerm_eq {A} `{_ : Dec_Eq A}  (m n : list A) : (isPermutation n m) = true -> Permutation n m.
Proof.
   intros. generalize dependent m. induction n.
   - intros. destruct m. auto. simpl in H0. discriminate H0.
   - destruct m. 
   -- intros. simpl in H0. discriminate H0.
   -- intros. apply IHn.


Instance show_list {T} `{_ : Show T} : Show (list T) := 
{| show := 
     let fix aux l :=
       match l with
       | nil => "nil"
       | cons x xs => "cons " ++ show x ++ " (" ++ aux xs ++ ")"
       end
      in aux
|}.
Derive Arbitrary for list
Instance Dec_Eq_list {T} `{_ : Dec_Eq T}  : Dec_Eq (list T).
Proof. dec_eq. Qed.




Open Scope string_scope.

Parameter print : list nat -> string -> list nat.
Extract Constant print => "Extract.print".
Definition collect_data (l : nat) (f : nat) (b : nat) (y : nat) (utter : list nat) :=
 let lfind_var := "l:" ++ "(" ++ show l ++ ")"++ "|" ++"f:" ++ "(" ++ show f ++ ")"++ "|" ++"b:" ++ "(" ++ show b ++ ")"++ "|" ++"y:" ++ "(" ++ show y ++ ")"++ "|" ++"utter:" ++ "(" ++ show utter ++ ")"
 in let lfind_v := print utter lfind_var
 in lfind_state l f b y lfind_v.
QuickChick collect_data.
Success.