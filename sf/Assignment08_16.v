Require Export Assignment08_15.

(* problem #16: 10 points *)

Lemma optimize_0plus_aexp_sound:
  atrans_sound optimize_0plus_aexp.
Proof.
  unfold atrans_sound. intros. unfold aequiv. intros.
  induction a.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl.
    remember (optimize_0plus_aexp a1) as a1' eqn:Ha1'.
    remember (optimize_0plus_aexp a2) as a2' eqn:Ha2'.
    destruct a1; destruct a2; try (destruct n);
    try (rewrite -> IHa1; rewrite -> IHa2; simpl; reflexivity);
    try (rewrite -> IHa2; simpl; reflexivity);
    try (rewrite -> IHa1; simpl; rewrite plus_0_r; reflexivity).
    + destruct n0; simpl in *.
      * rewrite plus_0_r. auto.
      * rewrite <- IHa1. rewrite <- IHa2. simpl. reflexivity.
  - simpl.
    rewrite <- IHa1. rewrite <- IHa2. reflexivity.
  - simpl.
    rewrite <- IHa1. rewrite <- IHa2. reflexivity.
Qed.

(*-- Check --*)
Check optimize_0plus_aexp_sound:
  atrans_sound optimize_0plus_aexp.

