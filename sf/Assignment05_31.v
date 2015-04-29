Require Export Assignment05_30.

(* problem #31: 10 points *)

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof. 
  (* FILL IN HERE *)
  intros.
  induction H.
  - apply le_n.
  - apply le_S.
    apply IHle.
Qed.

