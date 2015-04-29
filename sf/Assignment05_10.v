Require Export Assignment05_09.

(* problem #10: 10 points *)




(** 1 star (not_both_true_and_false)  *)
Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof. 
  (* FILL IN HERE *)
  intros.
  intros H.
  destruct H as [HP HNP].
  apply HNP.
  apply HP.
Qed.
(** [] *)



