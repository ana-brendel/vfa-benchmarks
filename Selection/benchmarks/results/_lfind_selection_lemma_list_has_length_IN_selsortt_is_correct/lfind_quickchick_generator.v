Load LFindLoad.

From lfind Require Import LFind.
From VFA Require Import Perm.
From QuickChick Require Import QuickChick.
Load LFindLoad.
From vfa_benchmark Require Import Selection.

Lemma lfind_state   (al : list nat) : @ex nat (fun x : nat => @eq nat (@list_length nat al) x).
Admitted.

From QuickChick Require Import QuickChick.
QCInclude "/home/anabrendel/lfind/vfa-benchmarks/Selection/benchmarks/sources/_lfind_selection_lemma_list_has_length_IN_selsortt_is_correct/".
QCInclude ".".
Extract Constant defNumTests => "50".

Require Import decide.

Open Scope string_scope.

Parameter print : list nat -> string -> list nat.
Extract Constant print => "Extract.print".
Definition collect_data (al : list nat) :=
 let lfind_var := "al:" ++ "(" ++ show al ++ ")"
 in let lfind_v := print al lfind_var
 in lfind_state  lfind_v.
QuickChick collect_data.
Success.