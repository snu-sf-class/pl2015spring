Require Export Assignment09_11.

(* problem #12: 10 points *)

(** **** Exercise: 2 stars, advanced (hoare_asgn_weakest)  *)
(** Show that the precondition in the rule [hoare_asgn] is in fact the
    weakest precondition. *)

Theorem hoare_asgn_weakest : forall Q X a,
  is_wp (Q [X |-> a]) (X ::= a) Q.
Proof.
  intros.
  unfold is_wp.
  split.
  - intros st1 st2 cev pre.
    unfold assn_sub in pre.
    inversion cev. subst.
    auto.
  - intros.
    intros st Hst.
    unfold assn_sub.
    eapply H.
    + constructor.
      reflexivity.
    + auto.
Qed.

(*-- Check --*)
Check hoare_asgn_weakest : forall Q X a,
  is_wp (Q [X |-> a]) (X ::= a) Q.
