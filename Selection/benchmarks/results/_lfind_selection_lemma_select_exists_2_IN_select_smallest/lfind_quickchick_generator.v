Load LFindLoad.

From lfind Require Import LFind.
From VFA Require Import Perm.
From QuickChick Require Import QuickChick.
Load LFindLoad.
From vfa_benchmark Require Import Selection.

Lemma lfind_state   (a : nat) (y : nat) (al : list nat) (x : nat) (bl : list nat) : @Forall nat (fun y0 : nat => le y y0) bl.
Admitted.

From QuickChick Require Import QuickChick.
QCInclude "/home/anabrendel/lfind/vfa-benchmarks/Selection/benchmarks/sources/_lfind_selection_lemma_select_exists_2_IN_select_smallest/".
QCInclude ".".
Extract Constant defNumTests => "50".

Require Import decide.

Open Scope string_scope.

Parameter print : list nat -> string -> list nat.
Extract Constant print => "Extract.print".
Definition collect_data (a : nat) (y : nat) (al : list nat) (x : nat) (bl : list nat) :=
 let lfind_var := "a:" ++ "(" ++ show a ++ ")"++ "`" ++"y:" ++ "(" ++ show y ++ ")"++ "`" ++"al:" ++ "(" ++ show al ++ ")"++ "`" ++"x:" ++ "(" ++ show x ++ ")"++ "`" ++"bl:" ++ "(" ++ show bl ++ ")"
 in let lfind_v := print bl lfind_var
 in lfind_state a y al x lfind_v.
QuickChick collect_data.
Success.