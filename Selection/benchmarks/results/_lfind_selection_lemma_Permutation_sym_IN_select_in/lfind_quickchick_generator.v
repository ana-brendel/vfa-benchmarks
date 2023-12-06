Load LFindLoad.

From lfind Require Import LFind.
From VFA Require Import Perm.
From QuickChick Require Import QuickChick.
Load LFindLoad.
From vfa_benchmark Require Import Selection.

Lemma lfind_state   (a : nat) (y : nat) (al : list nat) (bl : list nat) (x : nat) : @Permutation nat ?l (@cons nat x (@cons nat a al)).
Admitted.

From QuickChick Require Import QuickChick.
QCInclude "/home/anabrendel/lfind/vfa-benchmarks/Selection/benchmarks/sources/_lfind_selection_lemma_Permutation_sym_IN_select_in/".
QCInclude ".".
Extract Constant defNumTests => "50".

Require Import decide.

Open Scope string_scope.

Parameter print : nat -> string -> nat.
Extract Constant print => "Extract.print".
Definition collect_data (a : nat) (y : nat) (al : list nat) (bl : list nat) (x : nat) :=
 let lfind_var := "a:" ++ "(" ++ show a ++ ")"++ "`" ++"y:" ++ "(" ++ show y ++ ")"++ "`" ++"al:" ++ "(" ++ show al ++ ")"++ "`" ++"bl:" ++ "(" ++ show bl ++ ")"++ "`" ++"x:" ++ "(" ++ show x ++ ")"
 in let lfind_v := print x lfind_var
 in lfind_state a y al bl lfind_v.
QuickChick collect_data.
Success.