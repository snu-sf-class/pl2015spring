Require Export Assignment09_04.

(* problem #05: 10 points *)

(** **** Exercise: 2 stars (if_minus_plus)  *)
(** Prove the following hoare triple using [hoare_if]: *)

Theorem if_minus_plus :
  {{fun st => True}}
  IFB (BLe (AId X) (AId Y))
    THEN (Z ::= AMinus (AId Y) (AId X))
    ELSE (Y ::= APlus (AId X) (AId Z))
  FI
  {{fun st => st Y = st X + st Z}}. 
Proof.
  eapply hoare_consequence_pre.
  { eapply hoare_if; eapply hoare_asgn. }
  intros st Hst.
  destruct (beval st (BLe (AId X) (AId Y))) eqn:Hbev; split; intros.
  - unfold assn_sub.
    rewrite update_neq.
    rewrite update_neq.
    rewrite update_eq.
    simpl in Hbev. simpl.
    apply le_plus_minus.
    apply ble_nat_true. auto.
    intros C; inversion C.
    intros C; inversion C.
  - inversion H.
  - inversion H.
  - unfold assn_sub.
    rewrite update_eq.
    rewrite update_neq.
    rewrite update_neq.
    simpl. reflexivity.
    intros C. inversion C.
    intros C. inversion C.
Qed.

(*-- Check --*)
Check if_minus_plus :
  {{fun st => True}}
  IFB (BLe (AId X) (AId Y))
    THEN (Z ::= AMinus (AId Y) (AId X))
    ELSE (Y ::= APlus (AId X) (AId Z))
  FI
  {{fun st => st Y = st X + st Z}}. 

