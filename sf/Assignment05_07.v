Require Export Assignment05_06.

(* problem #07: 10 points *)



(** 2 stars, optional (orb_false_elim)  *)
Theorem orb_false_elim : forall b c,
  orb b c = false -> b = false /\ c = false.
Proof. 
  (* FILL IN HERE *)
  intros.
  destruct b.
  - inversion H.
  - split.
    + reflexivity.
    + destruct c.
      * inversion H.
      * reflexivity.
Qed.
(** [] *)



