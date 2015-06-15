Require Export Assignment08_03.

(* problem #04: 10 points *)

(** **** Exercise: 4 stars (no_whiles_terminating)  *)
(** Imp programs that don't involve while loops always terminate.
    State and prove a theorem [no_whiles_terminating] that says this. *)

(* Hint *)
Check andb_true_iff.

Theorem no_whiles_terminate: forall c st
    (NOWHL: no_whiles c = true),
  exists st', c / st || st'.
Proof.
  intros c.
  induction c; intros.
  - exists st. constructor.
  - exists (update st i (aeval st a)).
    constructor. reflexivity.
  - simpl in NOWHL.
    symmetry in NOWHL.
    apply andb_true_eq in NOWHL.
    destruct NOWHL as [NW1 NW2].
    symmetry in NW1, NW2.
    apply (IHc1 st) in NW1.
    destruct NW1 as [st1 CEV1].
    apply (IHc2 st1) in NW2.
    destruct NW2 as [st2 CEV2].
    eexists. econstructor.
    apply CEV1.
    apply CEV2.
  - simpl in NOWHL.
    symmetry in NOWHL.
    apply andb_true_eq in NOWHL.
    destruct NOWHL as [NW1 NW2].
    symmetry in NW1, NW2.
    apply (IHc1 st) in NW1.
    destruct NW1 as [st1 CEV1].
    apply (IHc2 st) in NW2.
    destruct NW2 as [st2 CEV2].
    destruct (beval st b) eqn:EVb;
      eexists; [apply E_IfTrue | apply E_IfFalse]; eauto.
  - simpl in NOWHL.
    inversion NOWHL.
Qed.

(*-- Check --*)
Check no_whiles_terminate: forall c st
    (NOWHL: no_whiles c = true),
  exists st', c / st || st'.

