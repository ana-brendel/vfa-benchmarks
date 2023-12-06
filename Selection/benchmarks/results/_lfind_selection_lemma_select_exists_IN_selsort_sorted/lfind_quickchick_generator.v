Load LFindLoad.

From lfind Require Import LFind.
From VFA Require Import Perm.
From QuickChick Require Import QuickChick.
Load LFindLoad.
From vfa_benchmark Require Import Selection.

Lemma lfind_state   (n : nat) (al : list nat) : sorted
  (let (y, r') := select n0 al in
   @cons nat y (selsort r' (@list_length nat al))).
Admitted.

From QuickChick Require Import QuickChick.
QCInclude "/home/anabrendel/lfind/vfa-benchmarks/Selection/benchmarks/sources/_lfind_selection_lemma_select_exists_IN_selsort_sorted/".
QCInclude ".".
Extract Constant defNumTests => "50".

Require Import decide.

Open Scope string_scope.

Parameter print : list nat -> string -> list nat.
Extract Constant print => "Extract.print".
Definition collect_data (n : nat) (al : list nat) :=
 let lfind_var := "n:" ++ "(" ++ show n ++ ")"++ "`" ++"al:" ++ "(" ++ show al ++ ")"
 in let lfind_v := print al lfind_var
 in lfind_state n lfind_v.
QuickChick collect_data.
Success.