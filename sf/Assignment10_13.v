Require Export Assignment10_12.

(* problem #13: 10 points *)

(** **** Exercise: 3 stars, optional  *)
Lemma par_body_n : forall n st,
  st X = 0 /\ st Y = 0 ->
  exists st',
    par_loop / st ==>c*  par_loop / st' /\ st' X = n /\ st' Y = 0.
Proof.
  intros.
  induction n; destruct H as [HX HY].
  - exists st.
    split.
    { apply multi_refl. }
    split; auto.
  - destruct IHn as [st' [Hst HXY']].
    assert (HY': st' Y = 0). inversion HXY'; auto.
    apply par_body_n__Sn in HXY'.
    exists (update st' X (S n)).
    split.
    { eapply multi_trans; eauto. }
    split.
    + rewrite update_eq. reflexivity.
    + rewrite update_neq; auto.
      intros C; inversion C.
Qed.

(*-- Check --*)
Check par_body_n : forall n st,
  st X = 0 /\ st Y = 0 ->
  exists st',
    par_loop / st ==>c*  par_loop / st' /\ st' X = n /\ st' Y = 0.

