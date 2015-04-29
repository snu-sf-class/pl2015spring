Require Export Assignment05_35.

(* problem #36: 10 points *)

Theorem ble_nat_true : forall n m,
  ble_nat n m = true -> n <= m.
Proof. 
  (* FILL IN HERE *)
  intros n.
  induction n as [| n' IH].
  - intros.
    apply O_le_n.
  - intros.
    destruct m as [| m'].
    + simpl in H.
      inversion H.
    + apply n_le_m__Sn_le_Sm.
      apply IH.
      simpl in H.
      apply H.
Qed.

