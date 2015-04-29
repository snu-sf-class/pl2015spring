Require Export Assignment05_34.

(* problem #35: 10 points *)

Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
  (* FILL IN HERE *)
  unfold lt.
  intros.
  apply le_S.
  apply H.
Qed.

