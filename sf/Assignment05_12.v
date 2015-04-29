Require Export Assignment05_11.

(* problem #12: 10 points *)




(** 2 stars (false_beq_nat)  *)
Theorem false_beq_nat : forall n m : nat,
     n <> m ->
     beq_nat n m = false.
Proof.
  (* FILL IN HERE *)
  intros.
  destruct (beq_nat n m) eqn:eqnm.
  - apply beq_nat_true in eqnm.
    apply H in eqnm.
    inversion eqnm.
  - reflexivity.
Qed.
(** [] *)




