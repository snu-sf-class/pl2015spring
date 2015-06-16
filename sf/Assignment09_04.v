Require Export Assignment09_03.

(* problem #04: 10 points *)

(** **** Exercise: 2 stars (hoare_asgn_example4)  *)
(** Translate this "decorated program" into a formal proof:
                   {{ True }} ->>
                   {{ 1 = 1 }}
    X ::= 1;;
                   {{ X = 1 }} ->>
                   {{ X = 1 /\ 2 = 2 }}
    Y ::= 2
                   {{ X = 1 /\ Y = 2 }}
*)

Example hoare_asgn_example4 :
  {{fun st => True}} (X ::= (ANum 1);; Y ::= (ANum 2)) 
  {{fun st => st X = 1 /\ st Y = 2}}.
Proof.
  apply hoare_consequence_pre with ((fun st => st X = 1) [ X |-> (ANum 1)]).
  {
    apply hoare_seq with (fun st => st X = 1).
    {
      apply hoare_consequence_pre with
      ((fun st => st X = 1 /\ st Y = 2) [Y |-> (ANum 2)]).
      - eapply hoare_asgn.
      - intros st Hst.
        unfold assn_sub.
        split.
        + rewrite update_neq; auto.
          intros EQ. inversion EQ.
        + rewrite update_eq. auto.
    }
    apply hoare_asgn.
  }
  intros st Hst.
  unfold assn_sub.
  rewrite update_eq.
  reflexivity.
Qed.

(*-- Check --*)
Check hoare_asgn_example4 :
  {{fun st => True}} (X ::= (ANum 1);; Y ::= (ANum 2)) 
  {{fun st => st X = 1 /\ st Y = 2}}.

