Require Export Assignment05_18.

(* problem #19: 10 points *)




(** 2 stars (gorgeous_sum)  *)
Theorem gorgeous_sum : forall n m,
  gorgeous n -> gorgeous m -> gorgeous (n + m).
Proof.
 (* FILL IN HERE *)
  intros.
  induction H.
  - simpl.
    apply H0.
  - rewrite <- plus_assoc.
    apply g_plus3.
    apply IHgorgeous.
  - rewrite <- plus_assoc.
    apply g_plus5.
    apply IHgorgeous.
Qed.
(** [] *)


