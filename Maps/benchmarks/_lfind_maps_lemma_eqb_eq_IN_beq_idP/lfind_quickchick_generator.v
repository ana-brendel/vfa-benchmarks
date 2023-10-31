Load LFindLoad.

From lfind Require Import LFind.
From Coq Require Import Bool.Bool.
From Coq Require Import Logic.FunctionalExtensionality.
From VFA Require Import Perm.
From QuickChick Require Import QuickChick.
Load LFindLoad.
From vfa_benchmark Require Import Maps.

Lemma lfind_state   (y : nat) (x : nat) : iff (@eq nat x y) (@eq bool (Nat.eqb x y) true).
Admitted.

From QuickChick Require Import QuickChick.
QCInclude "/home/anabrendel/lfind/vfa-benchmarks/Maps/benchmarks/_lfind_maps_lemma_eqb_eq_IN_beq_idP/".
QCInclude ".".
Extract Constant defNumTests => "50".

Derive Show for nat.

        Derive Arbitrary for nat.

        Instance Dec_Eq_nat : Dec_Eq nat.

        Proof. dec_eq. Qed.




Open Scope string_scope.

Parameter print : nat -> string -> nat.
Extract Constant print => "Extract.print".
Definition collect_data (y : nat) (x : nat) :=
 let lfind_var := "y:" ++ "(" ++ show y ++ ")"++ "|" ++"x:" ++ "(" ++ show x ++ ")"
 in let lfind_v := print x lfind_var
 in lfind_state y lfind_v.
QuickChick collect_data.
Success.