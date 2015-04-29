Require Export Assignment05_38.

(* problem #39: 10 points *)

Theorem ble_nat_false : forall n m,
  ble_nat n m = false -> ~(n <= m).
Proof.
  (* FILL IN HERE *)
  intros.
  intros lenm.
  apply le_ble_nat in lenm.
  rewrite -> lenm in H.
  inversion H.
Qed.
(** [] *)

