Require Export Assignment08_12.

(* problem #13: 10 points *)

(** **** Exercise: 3 stars (CIf_congruence)  *)
Theorem CIf_congruence : forall b b' c1 c1' c2 c2',
  bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (IFB b THEN c1 ELSE c2 FI) (IFB b' THEN c1' ELSE c2' FI).
Proof.
  intros.
  split.
  - intros HEVc.
    inversion HEVc; subst.
    + apply E_IfTrue.
      * rewrite <- H; auto.
      * apply H0; auto.
    + apply E_IfFalse.
      * rewrite <- H ; auto.
      * apply H1; auto.
  - intros HEVc.
    inversion HEVc; subst.
    + apply E_IfTrue.
      * rewrite -> H; auto.
      * apply H0; auto.
    + apply E_IfFalse.
      * rewrite -> H ; auto.
      * apply H1; auto.
Qed.

(*-- Check --*)
Check CIf_congruence : forall b b' c1 c1' c2 c2',
  bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (IFB b THEN c1 ELSE c2 FI) (IFB b' THEN c1' ELSE c2' FI).

