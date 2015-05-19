Require Export Assignment07_05.

(* problem #06: 10 points *)

(** **** Exercise: 1 star (update_neq)  *)
Theorem update_neq : forall x2 x1 n st,
  x2 <> x1 ->                        
  (update st x2 n) x1 = (st x1).
Proof.
  (* FILL IN HERE *)
  intros.
  unfold update.
  simpl.
  destruct (eq_id_dec x2 x1).
  - exfalso.
    apply H. apply e.
  - reflexivity.
Qed.

(** [] *)

