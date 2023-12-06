Load LFindLoad.

From lfind Require Import LFind.
From VFA Require Import Perm.
From QuickChick Require Import QuickChick.
Load LFindLoad.
From vfa_benchmark Require Import Selection.

Lemma lfind_state   (y : nat) (bl : list nat) : @ex nat (fun x : nat => @eq nat (@list_length nat bl) x).
Admitted.

From QuickChick Require Import QuickChick.
QCInclude "/home/anabrendel/lfind/vfa-benchmarks/Selection/benchmarks/sources/_lfind_selection_lemma_list_has_length_IN_cons_of_small_maintains_sortt/".
QCInclude ".".
Extract Constant defNumTests => "50".

Require Import decide.

Open Scope string_scope.

Parameter print : list nat -> string -> list nat.
Extract Constant print => "Extract.print".
Definition collect_data (y : nat) (bl : list nat) :=
 let lfind_var := "y:" ++ "(" ++ show y ++ ")"++ "`" ++"bl:" ++ "(" ++ show bl ++ ")"
 in let lfind_v := print bl lfind_var
 in lfind_state y lfind_v.
QuickChick collect_data.
Success.