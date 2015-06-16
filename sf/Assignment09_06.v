Require Export Assignment09_05.

(* problem #06: 10 points *)

(** **** Exercise: 2 stars (slow_assignment)  *)
(** A roundabout way of assigning a number currently stored in [X] to
    the variable [Y] is to start [Y] at [0], then decrement [X] until
    it hits [0], incrementing [Y] at each step. Here is a program that
    implements this idea:
      {{ X = m }}
    Y ::= 0;;
    WHILE X <> 0 DO
      X ::= X - 1;;
      Y ::= Y + 1
    END
      {{ Y = m }} 
    Write an informal decorated program showing that this is correct. *)

Theorem slow_assignment : forall m,
    {{ fun st => st X = m }}
    Y ::= ANum 0;;
    WHILE BNot (BEq (AId X) (ANum 0)) DO
      X ::= AMinus (AId X) (ANum 1);;
      Y ::= APlus (AId Y) (ANum 1)
    END
    {{ fun st => st Y = m }}.
Proof.
  intros.
  apply hoare_seq with (fun st => st X + st Y = m).
  {
    eapply hoare_consequence_post.
    {
      eapply hoare_while.
      eapply hoare_consequence_pre.
      {
        eapply hoare_seq.
        - eapply hoare_asgn.
        - eapply hoare_asgn.
      }
      simpl.
      unfold assn_sub.
      intros st [Hp Hb].
      simpl.
      rewrite update_neq.
      rewrite update_eq.
      rewrite update_eq.
      rewrite update_neq.
      subst.
      rewrite plus_comm.
      rewrite <- plus_assoc.
      rewrite le_plus_minus_r.
      - apply plus_comm.
      - destruct (st X).
        + simpl in Hb. inversion Hb.
        + apply le_n_S. apply le_0_n.
      - intros C. inversion C.
      - intros C. inversion C.
    }
    intros st [Hsum Hb].
    simpl in Hb.
    destruct (st X).
    + simpl in Hsum. auto.
    + simpl in Hb. inversion Hb.
  }
  eapply hoare_consequence_pre.
  {
    eapply hoare_asgn.
  }
  intros st Hst.
  unfold assn_sub.
  simpl.
  rewrite update_neq.
  rewrite update_eq.
  - rewrite plus_0_r.
    auto.
  - intros C. inversion C.
Qed.

(*-- Check --*)
Check slow_assignment : forall m,
    {{ fun st => st X = m }}
    Y ::= ANum 0;;
    WHILE BNot (BEq (AId X) (ANum 0)) DO
      X ::= AMinus (AId X) (ANum 1);;
      Y ::= APlus (AId Y) (ANum 1)
    END
    {{ fun st => st Y = m }}.
  
