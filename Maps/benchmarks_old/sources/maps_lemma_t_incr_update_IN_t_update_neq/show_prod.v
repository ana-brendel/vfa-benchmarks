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