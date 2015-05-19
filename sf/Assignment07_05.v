Require Export Assignment07_04.

(* problem #05: 10 points *)

(** **** Exercise: 1 star (update_eq)  *)
Theorem update_eq : forall n x st,
  (update st x n) x = n.
Proof.
  (* FILL IN HERE *)
  intros.
  unfold update.
  destruct (eq_id_dec x x).
  - reflexivity.
  - exfalso.
    apply n0.
    reflexivity.
Qed.
(** [] *)

