Require Export Assignment08_11.

(* problem #12: 10 points *)

(** **** Exercise: 3 stars, optional (CSeq_congruence)  *)
Theorem CSeq_congruence : forall c1 c1' c2 c2',
  cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (c1;;c2) (c1';;c2').
Proof. 
  intros.
  split; intros Has.
  - inversion Has. subst.
    apply E_Seq with st'0; [apply H | apply H0]; auto.
  - inversion Has. subst.
    apply E_Seq with st'0; [apply H | apply H0]; auto.
Qed.

(*-- Check --*)
Check CSeq_congruence : forall c1 c1' c2 c2',
  cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (c1;;c2) (c1';;c2').

