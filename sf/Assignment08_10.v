Require Export Assignment08_09.

(* problem #10: 10 points *)

(** **** Exercise: 2 stars, optional (seq_assoc)  *)
Theorem seq_assoc : forall c1 c2 c3,
  cequiv ((c1;;c2);;c3) (c1;;(c2;;c3)).
Proof.
  intros.
  split; intros Has.
  - inversion Has; subst.
    inversion H1; subst.
    apply E_Seq with st'1.
    { auto. }
    apply E_Seq with st'0; auto.
  - inversion Has; subst.
    inversion H4; subst.
    apply E_Seq with st'1; auto.
    apply E_Seq with st'0; auto.
Qed.

(*-- Check --*)
Check seq_assoc : forall c1 c2 c3,
  cequiv ((c1;;c2);;c3) (c1;;(c2;;c3)).

