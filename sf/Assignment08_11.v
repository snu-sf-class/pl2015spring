Require Export Assignment08_10.

(* problem #11: 10 points *)

(** **** Exercise: 2 stars (assign_aequiv)  *)
Theorem assign_aequiv : forall X e,
  aequiv (AId X) e -> 
  cequiv SKIP (X ::= e).
Proof.
  exact FILL_IN_HERE.
Qed.

(*-- Check --*)
Check assign_aequiv : forall X e,
  aequiv (AId X) e -> 
  cequiv SKIP (X ::= e).

