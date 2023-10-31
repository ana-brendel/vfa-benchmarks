Load LFindLoad.

From lfind Require Import LFind.
Require Import Coq.Strings.String.
From QuickChick Require Import QuickChick.
Load LFindLoad.
From vfa_benchmark Require Import Perm.

Lemma lfind_state   (y : nat) (x : nat) : iff (@eq bool (Nat.eqb x y) true) (@eq nat x y).
Admitted.

From QuickChick Require Import QuickChick.
QCInclude "/home/anabrendel/lfind/vfa-benchmarks/Perm/benchmarks/_lfind_perm_lemma_eqb_eq_IN_beq_reflect/".
QCInclude ".".
Extract Constant defNumTests => "50".



Derive Show for bool.

        Derive Arbitrary for bool.

        Instance Dec_Eq_bool : Dec_Eq bool.

        Proof. dec_eq. Qed.


Open Scope string_scope.

Parameter print : nat -> string -> nat.
Extract Constant print => "Extract.print".
Definition collect_data (y : nat) (x : nat) :=
 let lfind_var := "y:" ++ "(" ++ show y ++ ")"++ "|" ++"x:" ++ "(" ++ show x ++ ")"
 in let lfind_v := print x lfind_var
 in lfind_state y lfind_v.
QuickChick collect_data.
Success.