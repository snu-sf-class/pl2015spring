Require Export Assignment05_13.

(* problem #14: 10 points *)




(** 2 star (ev__even)  *)
Theorem ev__even: forall n : nat,
  ev n -> even n.
Proof.
  (* FILL IN HERE *)
  intros.
  induction H.
  - reflexivity.
  - unfold even.
    simpl.
    apply IHev.
Qed.

(** [] *)


