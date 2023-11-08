Load LFindLoad.

From lfind Require Import LFind.
From Coq Require Import Bool.Bool.
From Coq Require Import Logic.FunctionalExtensionality.
From VFA Require Import Perm.
From QuickChick Require Import QuickChick.
Load LFindLoad.
From vfa_benchmark Require Import Maps.

Lemma lfind_state {X}  (n : nat) (v1 : X) (x2 : nat) (x1 : nat) (H : Dec_Eq X) (m : partial_map X) (v2 : X) : @TotalMapEqual (option X) (@Dec_eq_opt X H) n
  (@t_update (option X) (@t_update (option X) m x2 (@Some X v2)) x1
     (@Some X v1))
  (@t_update (option X) (@t_update (option X) m x1 (@Some X v1)) x2
     (@Some X v2)).
Admitted.

From QuickChick Require Import QuickChick.
QCInclude "/home/anabrendel/lfind/vfa-benchmarks/Maps/benchmarks/_lfind_maps_lemma_t_update_permute_IN_update_permute/".
QCInclude ".".
Extract Constant defNumTests => "50".
Notation X := nat.



From QuickChick Require Import QuickChick.
From QuickChick Require Import QuickChick Tactics.
Import QcNotation.
Require Export Coq.Arith.Arith.
Require Export Coq.Bool.Bool.
Require Export Coq.Logic.ClassicalFacts.

Require Import String. Open Scope string.

Derive Show for nat. 
Derive Arbitrary for nat.
Instance Dec_Eq_nat  : Dec_Eq (nat).
Proof. dec_eq. Qed.

Derive Show for bool. 
Derive Arbitrary for bool.
Instance Dec_Eq_bool : Dec_Eq (bool).
Proof. dec_eq. Qed.

Instance show_prod {A} `{_ : Show A} : Show (prod nat A) := 
{| show := 
    let fix aux l := 
        match l with
        | (n,t) => "(" ++ show n ++ ", " ++ show t ++ ")"
        end
    in aux 
|}.
Derive Arbitrary for prod.
Instance Dec_Eq_prod {A} `{_ : Dec_Eq A} : Dec_Eq (prod nat A).
Proof. dec_eq. Qed.

Instance show_option {A} `{_ : Show A} : Show (option A) :=
{| show := 
    let fix aux l := 
        match l with
        | None => "None"
        | Some x => "Some ("++ show x ++")"
        end
    in aux 
|}.
Derive Arbitrary for option.
Instance Dec_Eq_option {A} `{_ : Dec_Eq A} : Dec_Eq (option A).
Proof. dec_eq. Qed.

Instance Dec_Eq_total_map {A} `{_ : Dec_Eq A} : Dec_Eq (total_map A).
Proof. dec_eq. Qed.

Instance show_list {T} `{_ : Show T} : Show (list T) := 
{| show := 
     let fix aux l :=
       match l with
       | nil => "nil"
       | cons x xs => "cons " ++ show x ++ " (" ++ aux xs ++ ")"
       end
      in aux
|}.

Instance show_total_map {T} `{_ : Show T} : Show (total_map T) := 
{| show := 
     let fix aux l :=
       match l with
       | (l,t) => "(" ++ show l ++ ", " ++ show t ++ ")"
       end
      in aux
|}.

Definition genTotalMapSize {A} (g : G A) : nat -> G (total_map A) := 
    let fix aux sz := 
        match sz with
        | O => (liftM t_empty g)
        | S z => (liftM3 t_update (aux z) arbitrary g)
      end in aux.

Definition genTotalMapBounded {A} (g : G A) : G (total_map A) := sized (genTotalMapSize g).

Definition mapShrink {A} (x : A) := (@nil A).

Instance genMapInstanceGen {A} `{_ : Gen A} : Gen (total_map A) := {| arbitrary := genTotalMapBounded arbitrary |}.
Instance genMapInstanceShrink {A} : Shrink (total_map A) := {| shrink := mapShrink |}.

Instance Dec_TotalMapEqualHelper_total_map {A} `{_ : Dec_Eq A} (n : nat) (t t' : A) (l l' : list (nat * A)) : Dec (TotalMapEqualHelper n t t' l l').
Proof.
  dec_eq. unfold TotalMapEqualHelper. apply dec_eq.
Qed.

Instance Dec_TotalMapEqual_total_map {A} `{_ : Dec_Eq A} (n : nat) (m m' : total_map A) : Dec (TotalMapEqual n m m').
Proof.
  dec_eq. unfold TotalMapEqual. apply dec_eq.
Qed. 

Derive Show for partial_map.

        Derive Arbitrary for partial_map.

        Instance Dec_Eq_partial_map : Dec_Eq partial_map X.

        Proof. dec_eq. Qed.


Open Scope string_scope.

Parameter print : X -> string -> X.
Extract Constant print => "Extract.print".
Definition collect_data (n : nat) (v1 : X) (x2 : nat) (x1 : nat) (H : Dec_Eq X) (m : partial_map X) (v2 : X) :=
 let lfind_var := "n:" ++ "(" ++ show n ++ ")"++ "|" ++"v1:" ++ "(" ++ show v1 ++ ")"++ "|" ++"x2:" ++ "(" ++ show x2 ++ ")"++ "|" ++"x1:" ++ "(" ++ show x1 ++ ")"++ "|" ++"H:" ++ "(" ++ show H ++ ")"++ "|" ++"m:" ++ "(" ++ show m ++ ")"++ "|" ++"v2:" ++ "(" ++ show v2 ++ ")"
 in let lfind_v := print v2 lfind_var
 in lfind_state n v1 x2 x1 H m lfind_v.
QuickChick collect_data.
Success.