Require Export Assignment07_02.

(* problem #03: 20 points *)

(** **** Exercise: 3 stars  (bevalR)  *)
(** Write a relation [bevalR] in the same style as
    [aevalR], and prove that it is equivalent to [beval].*)


Inductive bevalR: bexp -> bool -> Prop :=
(* FILL IN HERE *)
| E_BTrue : bevalR BTrue true
| E_BFalse : bevalR BFalse false
| E_BEq : forall a1 a2 n1 n2,
            aevalR a1 n1 -> aevalR a2 n2 ->
            bevalR (BEq a1 a2) (beq_nat n1 n2)
| E_BLe : forall a1 a2 n1 n2,
            aevalR a1 n1 -> aevalR a2 n2 ->
            bevalR (BLe a1 a2) (ble_nat n1 n2)
| E_BNot : forall b bv, bevalR b bv ->
                        bevalR (BNot b) (negb bv)
| E_BAnd : forall b1 b2 bv1 bv2,
             bevalR b1 bv1 -> bevalR b2 bv2 ->
             bevalR (BAnd b1 b2) (andb bv1 bv2)
.

Theorem beval_iff_bevalR : forall b bv,
  bevalR b bv <-> beval b = bv.
Proof.
  intros b bv.
  split; generalize dependent bv.
  {
    induction b; intros bv evalb; simpl; inversion evalb; subst;
    try (reflexivity);
    try (apply aeval_iff_aevalR in H1;
         apply aeval_iff_aevalR in H3;
         rewrite -> H1; rewrite -> H3;
         reflexivity).
    - apply IHb in H0.
      rewrite -> H0.
      reflexivity.
    - apply IHb1 in H1.
      apply IHb2 in H3.
      simpl.
      rewrite -> H1.
      rewrite -> H3.
      reflexivity.
  }
  {
    induction b; intros bv; simpl; intros eval;
    rewrite <- eval; constructor;
    try (apply aeval_iff_aevalR;reflexivity).
    - apply IHb.
      reflexivity.
    - apply IHb1.
      reflexivity.
    - apply IHb2.
      reflexivity.
  }
Qed.

(** [] *)

