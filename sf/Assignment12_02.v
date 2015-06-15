Require Export Assignment12_01.

(* problem #02: 10 points *)

(** **** Exercise: 2 stars, optional (typable_empty__closed)  *)
Corollary typable_empty__closed : forall t T, 
    empty |- t \in T  ->
    closed t.
Proof.
  exact FILL_IN_HERE.
Qed.

(*-- Check --*)
Check typable_empty__closed : forall t T, 
    empty |- t \in T  ->
    closed t.

