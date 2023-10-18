Require Import String. Open Scope string.
Derive Show for nat.
Derive Arbitrary for nat.
Instance Dec_Eq_nat : Dec_Eq nat.
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
