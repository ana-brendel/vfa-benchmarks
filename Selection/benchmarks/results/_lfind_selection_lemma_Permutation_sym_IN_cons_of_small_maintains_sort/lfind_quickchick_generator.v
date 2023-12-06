Load LFindLoad.

From lfind Require Import LFind.
From VFA Require Import Perm.
From QuickChick Require Import QuickChick.
Load LFindLoad.
From vfa_benchmark Require Import Selection.

Lemma lfind_state   (a : nat) (l : list nat) (y : nat) (bl : list nat) : @Permutation nat ?l bl.
Admitted.

From QuickChick Require Import QuickChick.
QCInclude "/home/anabrendel/lfind/vfa-benchmarks/Selection/benchmarks/sources/_lfind_selection_lemma_Permutation_sym_IN_cons_of_small_maintains_sort/".
QCInclude ".".
Extract Constant defNumTests => "50".

Require Import decide.

Open Scope string_scope.

Parameter print : list nat -> string -> list nat.
Extract Constant print => "Extract.print".
Definition collect_data (a : nat) (l : list nat) (y : nat) (bl : list nat) :=
 let lfind_var := "a:" ++ "(" ++ show a ++ ")"++ "`" ++"l:" ++ "(" ++ show l ++ ")"++ "`" ++"y:" ++ "(" ++ show y ++ ")"++ "`" ++"bl:" ++ "(" ++ show bl ++ ")"
 in let lfind_v := print bl lfind_var
 in lfind_state a l y lfind_v.
QuickChick collect_data.
Success.