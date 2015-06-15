Require Export Assignment11_09.

(* problem #10: 30 points *)

(** Write a type checking function [tyeq: tm -> ty -> bool].
**)

Fixpoint tycheck (t: tm) (T: ty) : bool :=
  FILL_IN_HERE.

Example tycheck_ex1:
  tycheck
    (tif (tiszero (tpred (tsucc (tsucc tzero)))) ttrue (tiszero (tsucc tzero))) 
    TBool 
  = true.
Proof. exact FILL_IN_HERE. Qed.

Example tycheck_ex2:
  tycheck
    (tif (tiszero (tpred (tsucc (tsucc tzero)))) tzero (tiszero (tsucc tzero))) 
    TBool 
  = false.
Proof. exact FILL_IN_HERE. Qed.

(** Prove that the type checking function [tyeq: tm -> ty -> bool] is correct.

    Hint: use the lemma [andb_prop].
**)

Check andb_prop.

Theorem tycheck_correct1: forall t T
    (TYCHK: tycheck t T = true),
  |- t \in T.
Proof.
  exact FILL_IN_HERE.
Qed.

Theorem tycheck_correct2: forall t T
    (HASTY: |- t \in T),
  tycheck t T = true.
Proof.
  exact FILL_IN_HERE.
Qed.

(*-- Check --*)

Check (conj tycheck_ex1 tycheck_ex2 :
 (tycheck
    (tif (tiszero (tpred (tsucc (tsucc tzero)))) ttrue (tiszero (tsucc tzero))) 
    TBool 
  = true)
 /\
 (tycheck
    (tif (tiszero (tpred (tsucc (tsucc tzero)))) tzero (tiszero (tsucc tzero))) 
    TBool 
  = false)).

Check tycheck_correct1: forall t T
    (TYCHK: tycheck t T = true),
  |- t \in T.

Check tycheck_correct2: forall t T
    (HASTY: |- t \in T),
  tycheck t T = true.
