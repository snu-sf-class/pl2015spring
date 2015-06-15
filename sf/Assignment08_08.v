Require Export Assignment08_07.

(* problem #08: 10 points *)

(** **** Exercise: 3 stars (swap_if_branches)  *)
(** Show that we can swap the branches of an IF by negating its
    condition *)

Theorem swap_if_branches: forall b e1 e2,
  cequiv
    (IFB b THEN e1 ELSE e2 FI)
    (IFB BNot b THEN e2 ELSE e1 FI).
Proof.
  intros.
  split; intros Has.
  - destruct (beval st b) eqn:HEVb; inversion Has; subst;
    try (rewrite -> HEVb in H4; inversion H4).
    + apply E_IfFalse; auto.
      simpl. rewrite -> HEVb. reflexivity.
    + apply E_IfTrue; auto.
      simpl. rewrite -> HEVb. reflexivity.
  - destruct (beval st b) eqn:HEVb; inversion Has; subst;
    try (simpl in H4; rewrite -> HEVb in H4; inversion H4).
    + apply E_IfTrue; auto.
    + apply E_IfFalse; auto.
Qed.

(*-- Check --*)
Check swap_if_branches: forall b e1 e2,
  cequiv
    (IFB b THEN e1 ELSE e2 FI)
    (IFB BNot b THEN e2 ELSE e1 FI).

