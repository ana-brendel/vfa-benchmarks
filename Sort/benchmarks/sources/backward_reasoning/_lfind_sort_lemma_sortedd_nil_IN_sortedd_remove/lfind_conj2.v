Load LFindLoad.

From lfind Require Import LFind.
From VFA Require Import Perm.
From QuickChick Require Import QuickChick.
Load LFindLoad.
From vfa_benchmark Require Import Sort.

From QuickChick Require Import QuickChick.
QCInclude "/home/anabrendel/lfind/vfa-benchmarks/Sort/benchmarks/sources/backward_reasoning/_lfind_sort_lemma_sortedd_nil_IN_sortedd_remove/".
QCInclude ".".
Extract Constant defNumTests => "50".

Require Import decide.

Lemma conj2: forall , sortedd (@nil nat).
Admitted.
QuickChick conj2.