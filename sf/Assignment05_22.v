Require Export Assignment05_21.

(* problem #22: 10 points *)



(** 1 star (inversion_practice)  *)
Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  (* FILL IN HERE *)
  intros.
  inversion H.
  inversion pf_evn.
  apply pf_evn0.
Qed.

(** The [inversion] tactic can also be used to derive goals by showing
    the absurdity of a hypothesis. *)


