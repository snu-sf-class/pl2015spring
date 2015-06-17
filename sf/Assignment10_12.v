Require Export Assignment10_11.

(* problem #12: 10 points *)

(** **** Exercise: 3 stars, optional  *)
Lemma par_body_n__Sn : forall n st,
  st X = n /\ st Y = 0 ->
  par_loop / st ==>c* par_loop / (update st X (S n)).
Proof.
  intros.
  destruct H as [HX HY].
  unfold par_loop.
  eapply multi_step.
  { apply CS_Par2.  
    constructor. }
  eapply multi_step.
  { apply CS_Par2.
    constructor. constructor. constructor. }
  eapply multi_step.
  { apply CS_Par2.
    constructor. constructor. }
  eapply multi_step.
  { apply CS_Par2.
    rewrite -> HY. simpl.
    constructor. }
  eapply multi_step.
  { apply CS_Par2.
    constructor. constructor. constructor. constructor. }
  eapply multi_step.
  { apply CS_Par2.
    repeat constructor. }
  eapply multi_step.
  { apply CS_Par2.
    constructor. rewrite -> HX. apply CS_Ass. }
  eapply multi_step.
  { apply CS_Par2.
    apply CS_SeqFinish. }
  replace (n+1) with (S n).
  eapply multi_refl.
  rewrite plus_comm. simpl. reflexivity.
Qed.

(*-- Check --*)
Check par_body_n__Sn : forall n st,
  st X = n /\ st Y = 0 ->
  par_loop / st ==>c* par_loop / (update st X (S n)).

