Require Export Assignment10_00.

(* problem #01: 10 points *)

(** **** Exercise: 1 star (test_step_2)  *)
(** Right-hand sides of sums can take a step only when the
    left-hand side is finished: if [t2] can take a step to [t2'],
    then [P (C n) t2] steps to [P (C n)
    t2']: *)

Example test_step_2 : 
      P 
        (C 0)
        (P 
          (C 2) 
          (P (C 0) (C 3)))
      ==>
      P 
        (C 0)
        (P 
          (C 2) 
          (C (0 + 3))).
Proof. 
  exact FILL_IN_HERE.
Qed.

(*-- Check --*)
Check test_step_2 : 
      P 
        (C 0)
        (P 
          (C 2) 
          (P (C 0) (C 3)))
      ==>
      P 
        (C 0)
        (P 
          (C 2) 
          (C (0 + 3))).

