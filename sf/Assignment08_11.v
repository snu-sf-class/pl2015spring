Require Export Assignment08_10.

(* problem #11: 10 points *)

(** **** Exercise: 2 stars (assign_aequiv)  *)
Theorem assign_aequiv : forall X e,
  aequiv (AId X) e -> 
  cequiv SKIP (X ::= e).
Proof.
  intros.
  split; intros Has.
  - replace st' with (update st X (aeval st e)).
    + constructor. reflexivity.
    + unfold aequiv in H.
      inversion Has. subst.
      apply functional_extensionality.
      intros Y. unfold update.
      destruct (eq_id_dec X Y).
      * rewrite <- H. subst. simpl. reflexivity.
      * reflexivity.
  - inversion Has. subst.
    assert (STEQ: st = update st X (aeval st e)).
    {
      apply functional_extensionality.
      intros Y.
      unfold update.
      destruct (eq_id_dec X Y).
      - rewrite <- H. subst. simpl. reflexivity.
      - reflexivity.
    }
    rewrite <- STEQ.
    constructor.
Qed.

(*-- Check --*)
Check assign_aequiv : forall X e,
  aequiv (AId X) e -> 
  cequiv SKIP (X ::= e).

