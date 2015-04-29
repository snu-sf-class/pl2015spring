Require Export Assignment05_19.

(* problem #20: 10 points *)








(** 3 stars, advanced (beautiful__gorgeous)  *)
Theorem beautiful__gorgeous : forall n, beautiful n -> gorgeous n.
Proof.
 (* FILL IN HERE *)
  intros.
  induction H.
  - apply g_0.
  - apply g_plus3.
    apply g_0.
  - apply g_plus5.
    apply g_0.
  - apply gorgeous_sum.
    + apply IHbeautiful1.
    + apply IHbeautiful2.
Qed.
(** [] *)




