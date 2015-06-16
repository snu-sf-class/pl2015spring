Require Export Assignment09_09.

(* problem #10: 10 points *)

(** **** Exercise: 3 stars (two_loops)  *)
(** Here is a very inefficient way of adding 3 numbers:
  X ::= 0;;
  Y ::= 0;;
  Z ::= c;;
  WHILE X <> a DO
    X ::= X + 1;;
    Z ::= Z + 1
  END;;
  WHILE Y <> b DO
    Y ::= Y + 1;;
    Z ::= Z + 1
  END

    Show that it does what it should by filling in the blanks in the
    following decorated program.

    {{ True }} ->>
    {{                                        }}
  X ::= 0;;
    {{                                        }}
  Y ::= 0;;
    {{                                        }}
  Z ::= c;;
    {{                                        }}
  WHILE X <> a DO
      {{                                        }} ->>
      {{                                        }}
    X ::= X + 1;;
      {{                                        }}
    Z ::= Z + 1
      {{                                        }}
  END;;
    {{                                        }} ->>
    {{                                        }}
  WHILE Y <> b DO
      {{                                        }} ->>
      {{                                        }}
    Y ::= Y + 1;;
      {{                                        }}
    Z ::= Z + 1
      {{                                        }}
  END
    {{                                        }} ->>
    {{ Z = a + b + c }}
*)

Theorem add_three_numbers_correct: forall a b c,
  {{ fun st => True }}                                   
  X ::= ANum 0;;
  Y ::= ANum 0;;
  Z ::= ANum c;;
  WHILE BNot (BEq (AId X) (ANum a)) DO
    X ::= APlus (AId X) (ANum 1);;
    Z ::= APlus (AId Z) (ANum 1)
  END;;
  WHILE BNot (BEq (AId Y) (ANum b)) DO
    Y ::= APlus (AId Y) (ANum 1);;
    Z ::= APlus (AId Z) (ANum 1)
  END
  {{ fun st => st Z = a + b + c }}.
Proof.
  intros.
  eapply hoare_consequence_pre.
  {
    eapply hoare_consequence_post.
    {
      eapply hoare_seq.
      {
        eapply hoare_seq.
        {
          eapply hoare_seq.
          {
            eapply hoare_seq.
            {
              apply hoare_while with (P:= (fun st => st Z = c + a + st Y)).
              eapply hoare_seq.
              { apply hoare_asgn. }
              eapply hoare_consequence_pre.
              { apply hoare_asgn. }
              intros st [Hs Hb].
              simpl in Hb.
              unfold assn_sub.
              simpl.
              rewrite update_eq.
              rewrite update_neq.
              rewrite update_neq.
              rewrite update_eq.
              rewrite -> Hs.
              omega.
              intros C; inversion C.
              intros C; inversion C.
            }
            eapply hoare_consequence_post.
            {
              apply hoare_while with (P:= (fun st => st Y = 0 /\st Z = c + st X)).
              eapply hoare_seq.
              { apply hoare_asgn. }
              eapply hoare_consequence_pre.
              { apply hoare_asgn. }
              intros st [[HY Hs] Hb].
              simpl in Hb.
              unfold assn_sub. simpl.
              rewrite update_neq.
              rewrite update_neq.
              rewrite update_eq.
              rewrite update_neq.
              rewrite update_neq.
              rewrite update_eq.
              split; auto.
              rewrite Hs. omega.
              intros C; inversion C.
              intros C; inversion C.
              intros C; inversion C.
              intros C; inversion C.
            }
            intros st [[HY Hs] Hb].
            simpl in Hb.
            destruct (eq_nat_dec (st X) a) as [Heq | Hneq].
            { subst. rewrite HY. rewrite <- Hs. omega. }
            apply beq_nat_false_iff in Hneq.
            rewrite -> Hneq in Hb.
            inversion Hb.
          }
          apply hoare_asgn.
        }
        apply hoare_asgn.
      }
      apply hoare_asgn.
    }
    intros st [Hs Hb].
    simpl in Hb.
    destruct (beq_nat (st Y) b) eqn:HY.
    - apply beq_nat_true in HY.
      omega.
    - inversion Hb.
  }
  intros st _.
  unfold assn_sub. simpl.
  rewrite update_neq.
  rewrite update_eq.
  rewrite update_eq.
  rewrite update_neq.
  rewrite update_neq.
  rewrite update_eq.
  omega.
  intros C; inversion C.
  intros C; inversion C.
  intros C; inversion C.
Qed.

(*-- Check --*)
Check add_three_numbers_correct: forall a b c,
  {{ fun st => True }}                                   
  X ::= ANum 0;;
  Y ::= ANum 0;;
  Z ::= ANum c;;
  WHILE BNot (BEq (AId X) (ANum a)) DO
    X ::= APlus (AId X) (ANum 1);;
    Z ::= APlus (AId Z) (ANum 1)
  END;;
  WHILE BNot (BEq (AId Y) (ANum b)) DO
    Y ::= APlus (AId Y) (ANum 1);;
    Z ::= APlus (AId Z) (ANum 1)
  END
  {{ fun st => st Z = a + b + c }}.

