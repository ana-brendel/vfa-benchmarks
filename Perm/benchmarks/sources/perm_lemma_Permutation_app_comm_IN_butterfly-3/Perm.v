(* Perm: Basic Techniques for Permutations and Ordering *)
(* From: https://github.com/kolya-vasiliev/verified-functional-algorithms-2019/blob/master/Perm.v *)

Load LFindLoad.
From lfind Require Import LFind.
Unset Printing Notations.
Set Printing Implicit.

Require Import Coq.Strings.String.
Require Export Coq.Bool.Bool.
Require Export Coq.Arith.Arith.
Require Export Coq.Arith.EqNat.
Require Export Coq.omega.Omega.
Require Export Coq.Lists.List.
Export ListNotations.
Require Export Permutation.

(* ################################################################# *)
(* The Less-Than Order on the Natural Numbers *)

(* For some reason, the Coq library has [ <? ] and [ <=? ] notations, but is missing these three: *)

Notation  "a >=? b" := (Nat.leb b a) (at level 70, only parsing) : nat_scope.
Notation  "a >? b"  := (Nat.ltb b a) (at level 70, only parsing) : nat_scope.
Notation " a =? b"  := (beq_nat a b) (at level 70) : nat_scope.

(* Inductive reflect (P : Prop) : bool -> Set :=
	  | ReflectT : P -> reflect P true 
    | ReflectF : ~ P -> reflect P false *)            

(* ================================================================= *)

(* Helper Lemma = iff_reflect : ∀ (P : Prop) (b : bool), P ↔ b = true → reflect P b *)
(* Helper Lemma = Nat.eqb_eq : ∀ n m : nat, (n =? m) = true ↔ n = m *)
Lemma beq_reflect : forall x y, reflect (x = y) (x =? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry.  apply Nat.eqb_eq.
Qed.

(* Helper Lemma = iff_reflect : ∀ (P : Prop) (b : bool), P ↔ b = true → reflect P b *)
(* Helper Lemma = Nat.ltb_lt : ∀ n m : nat, (n <? m) = true ↔ n < m *)
Lemma blt_reflect : forall x y, reflect (x < y) (x <? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry. apply Nat.ltb_lt.
Qed.

(* Helper Lemma = iff_reflect : ∀ (P : Prop) (b : bool), P ↔ b = true → reflect P b *)
(* Helper Lemma = Nat.leb_le : ∀ n m : nat, (n <=? m) = true ↔ n ≤ m *)
Lemma ble_reflect : forall x y, reflect (x <= y) (x <=? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry. apply Nat.leb_le.
Qed.

Definition maybe_swap (al: list nat) : list nat :=
  match al with
  | a :: b :: ar => if a >? b then b::a::ar else a::b::ar
  | _ => al
  end.

Hint Resolve blt_reflect ble_reflect beq_reflect : bdestruct.
Ltac bdestruct X :=
  let H := fresh in let e := fresh "e" in 
  evar (e: Prop);
  assert (H : reflect e X); subst e;
  [eauto with bdestruct
  | destruct H as [H|H];
    [| try first [apply not_lt in H | apply not_le in H]]].

Theorem maybe_swap_idempotent:
  forall al, maybe_swap (maybe_swap al) = maybe_swap al.
Proof.
  intros.
  destruct al as [ | a al].
  simpl.
  reflexivity.
  destruct al as [ | b al].
  simpl.
  reflexivity.
  simpl.
  destruct (blt_reflect b a).   
  simpl.
  bdestruct (a <? b).
  omega.
  reflexivity.
  simpl.
  bdestruct (b <? a).
  omega.
  reflexivity.
Qed.


(* ################################################################# *)
(** * Permutations *)

(* Do not modify the following line: *)
Definition manual_grade_for_Permutation_properties : option (prod nat string) := None.

(* Helper Lemma = Permutation_app_comm : ∀ (A : Type) (l l' : list A), Permutation (l ++ l') (l' ++ l) *)
(* Helper Lemma = app_assoc : ∀ (A : Type) (l m n : list A), l ++ m ++ n = (l ++ m) ++ n *)
(* Helper Lemma = Permutation_app_head : ∀ (A : Type) (l tl tl' : list A), Permutation tl tl' → Permutation (l ++ tl) (l ++ tl') *)
(* Inductive Constructors = perm_trans, perm_skip, perm_swap *)
Example butterfly: forall b u t e r f l y : nat,
  Permutation ([b;u;t;t;e;r]++[f;l;y]) ([f;l;u;t;t;e;r]++[b;y]).
Proof.
  intros.
  change [b;u;t;t;e;r] with ([b]++[u;t;t;e;r]).
  change [f;l;u;t;t;e;r] with ([f;l]++[u;t;t;e;r]).
  remember [u;t;t;e;r] as utter.
  clear Hequtter.
  rewrite <- app_assoc.
  rewrite <- app_assoc.
  apply perm_trans with (utter ++ [f;l;y] ++ [b]).
  rewrite (app_assoc utter [f;l;y]).
  apply Permutation_app_comm.
  eapply perm_trans.
  2: apply Permutation_app_comm.
    rewrite <- app_assoc.
  apply Permutation_app_head.
  eapply perm_trans.
  lfind_debug.
  Admitted.

  (* 2: apply Permutation_app_comm.
  simpl.
  apply perm_skip.
  apply perm_skip.
  apply perm_swap.
Qed. *)
