Require Export Assignment05_36.

(* problem #37: 10 points *)

Theorem le_ble_nat : forall n m,
  n <= m ->
  ble_nat n m = true.
Proof.
  (* Hint: This may be easiest to prove by induction on [m]. *)
  (* FILL IN HERE *)
  intros n m.
  generalize dependent n.
  induction m as [| m' IH].
  - intros.
    inversion H.
    simpl.
    reflexivity.
  - intros.
    destruct n as [| n'].
    + simpl.
      reflexivity.
    + simpl.
      apply IH.
      apply Sn_le_Sm__n_le_m.
      apply H.
Qed.

