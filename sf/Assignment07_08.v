Require Export Assignment07_07.

(* problem #08: 10 points *)

(** **** Exercise: 1 star (update_shadow)  *)
Theorem update_shadow : forall n1 n2 x1 x2 (st : state),
   (update  (update st x2 n1) x2 n2) x1 = (update st x2 n2) x1.
Proof.
  (* FILL IN HERE *) admit.
Qed.
(** [] *)

