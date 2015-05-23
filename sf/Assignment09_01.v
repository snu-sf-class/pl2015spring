Require Export Assignment09_00.

(* problem #01: 10 points *)

(** **** Exercise: 2 stars (hoare_asgn_examples)  *)

Theorem assn_sub_ex1: 
  {{ (fun st => st X <= 5) [X |-> APlus (AId X) (ANum 1)] }}
      X ::= APlus (AId X) (ANum 1)
  {{ fun st => st X <= 5 }}.
Proof.
  exact FILL_IN_HERE.
Qed.

(*-- Check --*)
Check assn_sub_ex1: 
  {{ (fun st => st X <= 5) [X |-> APlus (AId X) (ANum 1)] }}
      X ::= APlus (AId X) (ANum 1)
  {{ fun st => st X <= 5 }}.

