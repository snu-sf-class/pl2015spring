Require Export Assignment05_20.

(* problem #21: 10 points *)





(** 2 stars (ev_sum)  *)

Theorem ev_sum : forall n m,
   ev n -> ev m -> ev (n+m).
Proof. 
  (* FILL IN HERE *)
  intros n m Hn.
  generalize dependent m.
  induction Hn.
  - intros.
    simpl.
    apply H.
  - intros.
    simpl.
    apply ev_SS.
    apply IHHn.
    apply H.
Qed.
(** [] *)





