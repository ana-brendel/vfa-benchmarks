Load LFindLoad.
From lfind Require Import LFind.
From VFA Require Import Perm.
From vfa_benchmark Require Import Selection.

Set Printing Depth 1000.
Unset Printing Notations.
Set Printing Implicit.

Definition lfind_eval (l : list nat) :=
@length nat l.

Compute lfind_eval ((nil)).
