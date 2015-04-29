Require Export Assignment05_29.

(* problem #30: 10 points *)

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  (* FILL IN HERE *)
  intros.
  induction n as [| n' IH].
  - apply le_n.
  - apply le_S.
    apply IH.
Qed.

