Require Export Assignment08_06.

(* problem #07: 10 points *)

(** **** Exercise: 2 stars (IFB_false)  *)
Theorem IFB_false: forall b c1 c2,
  bequiv b BFalse  ->
  cequiv 
    (IFB b THEN c1 ELSE c2 FI) 
    c2.
Proof.
  intros.
  split; intros Has.
  - inversion Has; subst.
    + unfold bequiv in H.
      simpl in H.
      rewrite -> H in H5.
      inversion H5.
    + auto.
  - apply E_IfFalse.
    + rewrite -> H. simpl. reflexivity.
    + auto.
Qed.

(*-- Check --*)
Check IFB_false: forall b c1 c2,
  bequiv b BFalse  ->
  cequiv 
    (IFB b THEN c1 ELSE c2 FI) 
    c2.

