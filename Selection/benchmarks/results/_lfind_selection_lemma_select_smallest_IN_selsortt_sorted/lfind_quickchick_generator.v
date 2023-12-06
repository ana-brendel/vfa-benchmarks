Load LFindLoad.

From lfind Require Import LFind.
From VFA Require Import Perm.
From QuickChick Require Import QuickChick.
Load LFindLoad.
From vfa_benchmark Require Import Selection.

Lemma lfind_state   (n0 : nat) (n : nat) (al : list nat) (x : nat) (x0 : list nat) : le_all x x0.
Admitted.

From QuickChick Require Import QuickChick.
QCInclude "/home/anabrendel/lfind/vfa-benchmarks/Selection/benchmarks/sources/_lfind_selection_lemma_select_smallest_IN_selsortt_sorted/".
QCInclude ".".
Extract Constant defNumTests => "50".

Require Import decide.

Open Scope string_scope.

Parameter print : list nat -> string -> list nat.
Extract Constant print => "Extract.print".
Definition collect_data (n0 : nat) (n : nat) (al : list nat) (x : nat) (x0 : list nat) :=
 let lfind_var := "n0:" ++ "(" ++ show n0 ++ ")"++ "`" ++"n:" ++ "(" ++ show n ++ ")"++ "`" ++"al:" ++ "(" ++ show al ++ ")"++ "`" ++"x:" ++ "(" ++ show x ++ ")"++ "`" ++"x0:" ++ "(" ++ show x0 ++ ")"
 in let lfind_v := print x0 lfind_var
 in lfind_state n0 n al x lfind_v.
QuickChick collect_data.
Success.