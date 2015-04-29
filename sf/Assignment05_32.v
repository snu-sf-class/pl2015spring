Require Export Assignment05_31.

(* problem #32: 10 points *)

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof. 
  (* FILL IN HERE *)
  intros n m.
  generalize dependent n.
  induction m as [| m' IH].
  - intros.
    inversion H.
    + apply le_n.
    + inversion H2.
  - intros.
    inversion H.
    + apply le_n.
    + apply le_S.
      apply IH.
      apply H2.
Qed.

