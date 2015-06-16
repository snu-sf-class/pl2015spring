Require Export Assignment09_10.

(* problem #11: 10 points *)

(** **** Exercise: 3 stars, advanced, optional (is_wp_formal)  *)
(** Prove formally using the definition of [hoare_triple] that [Y <= 4]
   is indeed the weakest precondition of [X ::= Y + 1] with respect to
   postcondition [X <= 5]. *)

Theorem is_wp_example :
  is_wp (fun st => st Y <= 4)
    (X ::= APlus (AId Y) (ANum 1)) (fun st => st X <= 5).
Proof.
  unfold is_wp.
  split.
  - eapply hoare_consequence_pre.
    { apply hoare_asgn. }
    intros st HY.
    unfold assn_sub.
    rewrite update_eq.
    simpl.
    omega.
  - intros.
    intros st Hst.
    apply (H st (update st X (st Y + 1))) in Hst.
    + rewrite update_eq in Hst.
      omega.
    + constructor.
      simpl.
      reflexivity.
Qed.

(*-- Check --*)
Check is_wp_example :
  is_wp (fun st => st Y <= 4)
    (X ::= APlus (AId Y) (ANum 1)) (fun st => st X <= 5).

