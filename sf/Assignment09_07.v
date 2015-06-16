Require Export Assignment09_06.

(* problem #07: 10 points *)

(** **** Exercise: 3 stars, optional (add_slowly_decoration)  *)
(** The following program adds the variable X into the variable Z
    by repeatedly decrementing X and incrementing Z.
  WHILE X <> 0 DO
     Z ::= Z + 1;;
     X ::= X - 1
  END

    Following the pattern of the [subtract_slowly] example above, pick
    a precondition and postcondition that give an appropriate
    specification of [add_slowly]; then (informally) decorate the
    program accordingly. *)

Theorem slow_addition_dec_correct : forall n m,
  {{fun st => st X = n /\ st Y = m }}
  WHILE BNot (BEq (AId X) (ANum 0)) DO
     Y ::= APlus (AId Y) (ANum 1);;
     X ::= AMinus (AId X) (ANum 1)
  END
  {{fun st => st Y = n + m}}.
Proof.
  intros.
  eapply hoare_consequence_pre.
  {
    eapply hoare_consequence_post.
    {
      eapply hoare_while with (P:=(fun st => st X + st Y = n + m)).
      eapply hoare_seq.
      - apply hoare_asgn.
      - eapply hoare_consequence_pre.
        + apply hoare_asgn.
        + intros st [Hsum Hb].
          unfold assn_sub.
          simpl.
          rewrite update_eq.
          rewrite update_neq.
          rewrite update_neq.
          rewrite update_eq.
          rewrite plus_comm.
          rewrite <- plus_assoc.
          rewrite le_plus_minus_r.
          * rewrite plus_comm. auto.
          * simpl in Hb.
            destruct (st X).
            { inversion Hb. }
            { apply le_n_S. apply le_0_n. }
          * intros C; inversion C.
          * intros C; inversion C.
    }
    intros st [Hsum Hb].
    simpl in Hb.
    destruct (st X).
    - simpl in Hsum. auto.
    - simpl in Hb. inversion Hb.
  }
  intros st [HX HY].
  subst. auto.
Qed.

(*-- Check --*)
Check slow_addition_dec_correct : forall n m,
  {{fun st => st X = n /\ st Y = m }}
  WHILE BNot (BEq (AId X) (ANum 0)) DO
     Y ::= APlus (AId Y) (ANum 1);;
     X ::= AMinus (AId X) (ANum 1)
  END
  {{fun st => st Y = n + m}}.

