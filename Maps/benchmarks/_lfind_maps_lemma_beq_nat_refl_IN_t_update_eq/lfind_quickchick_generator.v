Load LFindLoad.
Load LFindLoad.
From vfa_benchmark Require Import Maps.

From lfind Require Import LFind.
From Coq Require Import Bool.Bool.
From Coq Require Import Logic.FunctionalExtensionality.
From VFA Require Import Perm.

Lemma lfind_state {A}  (x : nat) : @eq bool true (Nat.eqb x x).
Admitted.

From QuickChick Require Import QuickChick.
QCInclude "/home/anabrendel/lfind/vfa-benchmarks/Maps/benchmarks/_lfind_maps_lemma_beq_nat_refl_IN_t_update_eq/".
QCInclude ".".
Extract Constant defNumTests => "50".
Derive Show for nat.

        Derive Arbitrary for nat.

        Instance Dec_Eq_nat : Dec_Eq nat.

        Proof. dec_eq. Qed.


Derive Show for bool.

        Derive Arbitrary for bool.

        Instance Dec_Eq_bool : Dec_Eq bool.

        Proof. dec_eq. Qed.




Derive Show for total_map.

        Derive Arbitrary for total_map.

        Instance Dec_Eq_total_map : Dec_Eq total_map A.

        Proof. dec_eq. Qed.

Notation A := nat.


Open Scope string_scope.

Parameter print : nat -> string -> nat.
Extract Constant print => "Extract.print".
Definition collect_data (x : nat) :=
 let lfind_var := "x:" ++ "(" ++ show x ++ ")"
 in let lfind_v := print x lfind_var
 in lfind_state  lfind_v.
QuickChick collect_data.
Success.