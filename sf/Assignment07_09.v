Require Export Assignment07_08.

(* problem #09: 10 points *)

(** **** Exercise: 2 stars (update_same)  *)
Theorem update_same : forall n1 x1 x2 (st : state),
  st x1 = n1 ->
  (update st x1 n1) x2 = st x2.
Proof.
  (* FILL IN HERE *) admit.
Qed.
(** [] *)

