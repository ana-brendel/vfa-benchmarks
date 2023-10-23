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
