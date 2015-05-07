Require Export Assignment06_02.

(* problem #03: 10 points *)

(** **** Exercise: 2 stars (dist_exists_or)  *)
(** Prove that existential quantification distributes over
    disjunction. *)

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
   (* FILL IN HERE *)
  intros.
  split.
  - intros expq.
    destruct expq as [x [px | qx]].
    + left. exists x. apply px.
    + right. exists x. apply qx.
  - intros expexq.
    destruct expexq as [[x px] | [x qx]].
    + exists x. left. apply px.
    + exists x. right. apply qx.
Qed.
(** [] *)


