Require Export Assignment08_14.

(* problem #15: 10 points *)

(** **** Exercise: 3 stars (fold_constants_com_sound)  *)
(** Complete the [WHILE] case of the following proof. *)

Theorem fold_constants_com_sound : 
  ctrans_sound fold_constants_com.
Proof. 
  unfold ctrans_sound. intros c. 
  com_cases (induction c) Case; simpl.
  Case "SKIP". apply refl_cequiv.
  Case "::=". apply CAss_congruence. apply fold_constants_aexp_sound.
  Case ";;". 
    (***
     Note how we use the tactic [eauto].
     ***)
   destruct c1; destruct c2; try (apply CSeq_congruence; assumption)
   ; eauto using skip_left, skip_right.
  Case "IFB". 
    assert (bequiv b (fold_constants_bexp b)).
      SCase "Pf of assertion". apply fold_constants_bexp_sound.
    destruct (fold_constants_bexp b) eqn:Heqb;
      (* If the optimization doesn't eliminate the if, then the result
         is easy to prove from the IH and fold_constants_bexp_sound *)
      try (apply CIf_congruence; assumption).
    SCase "b always true".
      apply trans_cequiv with c1; try assumption.
      apply IFB_true; assumption.
    SCase "b always false".
      apply trans_cequiv with c2; try assumption.
      apply IFB_false; assumption.
  Case "WHILE".
    assert (bequiv b (fold_constants_bexp b)).
    { apply fold_constants_bexp_sound. }
    destruct (fold_constants_bexp b) eqn:Heqb.
    - apply WHILE_true. auto.
    - split; intros Has; inversion Has.
      + constructor.
      + rewrite -> H in H2. simpl in H2. inversion H2.
      + apply E_WhileEnd. apply H.
    - apply CWhile_congruence; auto.
    - apply CWhile_congruence; auto.
    - apply CWhile_congruence; auto.
    - apply CWhile_congruence; auto.
Qed.

(*-- Check --*)
Check fold_constants_com_sound : 
  ctrans_sound fold_constants_com.

