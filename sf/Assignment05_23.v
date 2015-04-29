Require Export Assignment05_22.

(* problem #23: 10 points *)

(** 1 star (inversion_practice)  *)
Theorem even5_nonsense : 
  ev 5 -> 2 + 2 = 9.
Proof.
  (* FILL IN HERE *)
  intros.
  inversion H.
  inversion pf_evn.
  inversion pf_evn0.
Qed.
(** [] *)


