Load LFindLoad.

From lfind Require Import LFind.
From VFA Require Import Perm.
From QuickChick Require Import QuickChick.
Load LFindLoad.
From vfa_benchmark Require Import Selection.

From QuickChick Require Import QuickChick.
QCInclude "/home/anabrendel/lfind/vfa-benchmarks/Selection/benchmarks/sources/_lfind_selection_lemma_selsort_sorted_IN_selection_sort_sorted/".
QCInclude ".".
Extract Constant defNumTests => "50".

Require Import decide.

Lemma conj1: forall (lf1 : list nat), sorted lf1.
Admitted.
QuickChick conj1.