From QuickChick Require Import QuickChick.
From QuickChick Require Import QuickChick Tactics.
Import QcNotation.
Require Export Coq.Arith.Arith.
Require Export Coq.Bool.Bool.
Require Export Coq.Logic.ClassicalFacts.

Require Import String. Open Scope string.

Derive Show for bool. 
Derive Arbitrary for bool.
Instance Dec_Eq_bool : Dec_Eq (bool).
Proof. dec_eq. Qed.

Derive Show for nat. 
Derive Arbitrary for nat.
Instance Dec_Eq_nat  : Dec_Eq (nat).
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
Derive Arbitrary for list.
Instance Dec_Eq_list {T} `{_ : Dec_Eq T}  : Dec_Eq (list T).
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

Definition getMapFromList {A} (default : A) (l : list A) : (total_map A) :=
  let fix aux f n l :=
    match l with
    | [] => f
    | elem :: rest => aux (t_update f n elem) (S n) rest
  end in aux (t_empty default) 0 l.

Definition genListTen {A} (g : G A) : G (list A) := 
    liftM2 cons g (liftM2 cons g 
        (liftM2 cons g (liftM2 cons g 
            (liftM2 cons g (liftM2 cons g 
                (liftM2 cons g (liftM2 cons g 
                    (liftM2 cons g (liftM2 cons g (ret nil)))))))))).

Definition genTotalMapSize {A} (g : G A) : nat -> G (total_map A) := 
    let fix aux sz := 
        match sz with
        | O => (liftM t_empty g)
        | S z => (liftM2 getMapFromList g (genListTen g))
      end in aux.

Definition genTotalMapBounded {A} (g : G A) : G (total_map A) := sized (genTotalMapSize g).

Definition mapShrink {A} (x : A) := (@nil A).

Instance genMapInstanceGen {A} `{_ : Gen A} : Gen (total_map A) := {| arbitrary := genTotalMapBounded arbitrary |}.
Instance genMapInstanceShrink {A} : Shrink (total_map A) := {| shrink := mapShrink |}.

(* again, note that this only shows the first 10 distinct inputs for nats to the map *)
Instance show_total_map {A} `{_ : Show A} : Show (total_map A) :=
{| show := 
    fun f => "fun x => match x with | 0 => " ++ show (f 0) ++ 
      " | 1 => " ++ show (f 1) ++ " | 2 => " ++ show (f 2) ++
      " | 3 => " ++ show (f 3) ++ " | 4 => " ++ show (f 4) ++
      " | 5 => " ++ show (f 5) ++ " | 6 => " ++ show (f 6) ++
      " | 7 => " ++ show (f 7) ++ " | 8 => " ++ show (f 8) ++
      " | 9 => " ++ show (f 9) ++ " | _ => " ++ show (f 10) ++ " end"
|}.

Instance show_partial_map {A} `{_ : Show A} : Show (partial_map A) :=
{| show := 
    fun f => "fun x => match x with | 0 => " ++ show (f 0) ++ 
      " | 1 => " ++ show (f 1) ++ " | 2 => " ++ show (f 2) ++
      " | 3 => " ++ show (f 3) ++ " | 4 => " ++ show (f 4) ++
      " | 5 => " ++ show (f 5) ++ " | 6 => " ++ show (f 6) ++
      " | 7 => " ++ show (f 7) ++ " | 8 => " ++ show (f 8) ++
      " | 9 => " ++ show (f 9) ++ " | _ => " ++ show (f 10) ++ " end"
|}.