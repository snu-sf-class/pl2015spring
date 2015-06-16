Require Export Assignment09_08.

(* problem #09: 10 points *)

(** **** Exercise: 4 stars (factorial)  *)
(** Recall that [n!] denotes the factorial of [n] (i.e. [n! =
    1*2*...*n]).  Here is an Imp program that calculates the factorial
    of the number initially stored in the variable [X] and puts it in
    the variable [Y]:
    {{ X = m }} 
  Y ::= 1 ;;
  WHILE X <> 0
  DO
     Y ::= Y * X ;;
     X ::= X - 1
  END
    {{ Y = m! }}

    Fill in the blanks in following decorated program:
    {{ X = m }} ->>
    {{                                      }}
  Y ::= 1;;
    {{                                      }}
  WHILE X <> 0
  DO   {{                                      }} ->>
       {{                                      }}
     Y ::= Y * X;;
       {{                                      }}
     X ::= X - 1
       {{                                      }}
  END
    {{                                      }} ->>
    {{ Y = m! }}
*)

Print fact.

Theorem factorial_dec_correct: forall m,
  {{ fun st => st X = m }} 
  Y ::= ANum 1 ;;
  WHILE BNot (BEq (AId X) (ANum 0))
  DO
     Y ::= AMult (AId Y) (AId X) ;;
     X ::= AMinus (AId X) (ANum 1)
  END
  {{ fun st => st Y = fact m }}.
Proof.
  intros.
  eapply hoare_consequence_pre.
  {
    eapply hoare_consequence_post.
    {
      eapply hoare_seq.
      {
        apply hoare_while with (P:=fun st => st Y * fact (st X) = fact m).
        eapply hoare_seq.
        { apply hoare_asgn. }
        eapply hoare_consequence_pre.
        { apply hoare_asgn. }
        intros st [HY Hb].
        simpl in Hb.
        unfold assn_sub. simpl.
        rewrite update_neq.
        rewrite update_eq.
        rewrite update_eq.
        rewrite update_neq.
        destruct (st X).
        { inversion Hb. }
        simpl.
        rewrite <- minus_n_O.
        assert (Hf: forall n, fact (S n) = (S n) * fact n).
        { intros.
          induction n0.
          - simpl. reflexivity.
          - simpl. reflexivity.
        }
        rewrite <- mult_assoc.
        rewrite <- Hf.
        auto.
        intros C; inversion C.
        intros C; inversion C.
      }
      apply hoare_asgn.
    }
    intros st [Hf Hb].
    simpl in Hb.
    destruct (st X).
    simpl in Hf.
    rewrite <- Hf.
    omega.
    simpl in Hb. inversion Hb.
  }
  intros st HX.
  unfold assn_sub. simpl.
  rewrite update_neq.
  rewrite plus_0_r. subst. auto.
  intros C; inversion C.
Qed.

(*-- Check --*)
Check factorial_dec_correct: forall m,
  {{ fun st => st X = m }} 
  Y ::= ANum 1 ;;
  WHILE BNot (BEq (AId X) (ANum 0))
  DO
     Y ::= AMult (AId Y) (AId X) ;;
     X ::= AMinus (AId X) (ANum 1)
  END
  {{ fun st => st Y = fact m }}.

