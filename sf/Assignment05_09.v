Require Export Assignment05_08.

(* problem #09: 10 points *)



(** 2 stars (contrapositive)  *)
Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).
Proof.
  (* FILL IN HERE *)
  intros.
  intros HP.
  apply H0.
  apply H.
  apply HP.
Qed.
(** [] *)



