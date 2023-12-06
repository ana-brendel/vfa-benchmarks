Load LFindLoad.

From lfind Require Import LFind.
From VFA Require Import Perm.
From QuickChick Require Import QuickChick.
Load LFindLoad.
From vfa_benchmark Require Import Selection.

From QuickChick Require Import QuickChick.
QCInclude "/home/anabrendel/lfind/vfa-benchmarks/Selection/benchmarks/sources/_lfind_selection_lemma_selsort_perm_IN_selection_sort_perm/".
QCInclude ".".
Extract Constant defNumTests => "50".

Require Import decide.

Lemma conj4: forall (l : list nat), @Permutation nat l (selsort l (@length nat l)).
Admitted.
QuickChick conj4.