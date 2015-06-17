Require Export Assignment10_09.

(* problem #10: 10 points *)

(** The fact that small-step reduction implies big-step is now
    straightforward to prove, once it is stated correctly. 

    The proof proceeds by induction on the multi-step reduction
    sequence that is buried in the hypothesis [normal_form_of t t']. *)
(** Make sure you understand the statement before you start to
    work on the proof.  *)

Lemma my_p_exists_step: forall t t1 t2,
                          t = P t1 t2 ->
                          exists t', t ==> t'.
Proof.
  intros t.
  induction t.
  - intros. inversion H.
  - intros.
    inversion H; subst. clear H.
    destruct t0.
    + destruct t3.
      * eexists. constructor.
      * assert (Hex: exists t', P t3_1 t3_2 ==> t').
        { eapply IHt2. reflexivity. }
        inversion Hex.
        eexists. apply ST_Plus2.
        { constructor. }
        { apply H. }
    + assert (Hex: exists t', P t0_1 t0_2 ==> t').
      { eapply IHt1. reflexivity. }
      inversion Hex.
      eexists. constructor. eauto.
Qed.

(** **** Exercise: 3 stars (multistep__eval)  *)
Theorem multistep__eval : forall t t',
  normal_form_of t t' -> exists n, t' = C n /\ t || n.
Proof.
  intros.
  destruct H as [Hp Hn].
  induction Hp.
  - unfold step_normal_form in Hn.
    unfold normal_form in Hn.
    destruct x.
    + exists n. split; auto. constructor.
    + exfalso. apply Hn.
      eapply my_p_exists_step.
      reflexivity.
  - specialize (IHHp Hn).
    inversion IHHp.
    destruct H0 as [Hz HEVy].
    eexists.
    split; eauto.
    eapply step__eval; eauto.
Qed.

(*-- Check --*)
Check multistep__eval : forall t t',
  normal_form_of t t' -> exists n, t' = C n /\ t || n.

