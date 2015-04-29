Require Export Assignment05_15.

(* problem #16: 10 points *)







(** 2 stars (b_times2)  *)
Theorem b_times2: forall n, beautiful n -> beautiful (2*n).
Proof.
    (* FILL IN HERE *)
  intros.
  induction H.
  - simpl. apply b_0.
  - simpl.
    apply b_sum with (n:=3).
    + apply b_3.
    + apply b_3.
  - apply b_sum with (n:=5).
    + apply b_5.
    + apply b_5.
  - rewrite -> mult_comm.
    rewrite -> mult_plus_distr_r.
    rewrite -> mult_comm in IHbeautiful1.
    rewrite -> mult_comm in IHbeautiful2.
    apply b_sum.
    + apply IHbeautiful1.
    + apply IHbeautiful2.
Qed.

(** [] *)



