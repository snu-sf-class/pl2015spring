Require Export Assignment05_01.

(* problem #02: 10 points *)



(** 2 stars (and_assoc)  *)
(** In the following proof, notice how the _nested pattern_ in the
    [destruct] breaks the hypothesis [H : P /\ (Q /\ R)] down into
    [HP: P], [HQ : Q], and [HR : R].  Finish the proof from there: *)

Theorem and_assoc : forall P Q R : Prop, 
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R H.
  destruct H as [HP [HQ HR]].
(* FILL IN HERE *) admit.
Qed.
(** [] *)



