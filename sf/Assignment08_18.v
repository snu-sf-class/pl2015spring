Require Export Assignment08_17.

(* problem #18: 10 points *)

Lemma optimize_0plus_com_sound:
  ctrans_sound optimize_0plus_com.
Proof.
  unfold ctrans_sound. intros.
  induction c; simpl.
  - apply refl_cequiv.
  - apply CAss_congruence. apply optimize_0plus_aexp_sound.
  - apply CSeq_congruence; auto.
  - apply CIf_congruence; auto.
    apply optimize_0plus_bexp_sound.
  - apply CWhile_congruence; auto.
    apply optimize_0plus_bexp_sound.
Qed.

(*-- Check --*)
Check optimize_0plus_com_sound:
  ctrans_sound optimize_0plus_com.

