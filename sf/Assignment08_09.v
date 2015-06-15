Require Export Assignment08_08.

(* problem #09: 10 points *)

(** **** Exercise: 2 stars (WHILE_true)  *)
(** Prove the following theorem. _Hint_: You'll want to use
    [WHILE_true_nonterm] here. *)

(* from Equiv.v *)
Lemma WHILE_true_nonterm : forall b c st st',
     bequiv b BTrue ->
     ~( (WHILE b DO c END) / st || st' ).
Proof. 
  (* WORKED IN CLASS *)
  intros b c st st' Hb.
  intros H.
  remember (WHILE b DO c END) as cw eqn:Heqcw.
  ceval_cases (induction H) Case;
    (* Most rules don't apply, and we can rule them out 
       by inversion *)
    inversion Heqcw; subst; clear Heqcw.
  (* The two interesting cases are the ones for WHILE loops: *)
  Case "E_WhileEnd". (* contradictory -- b is always true! *)
    unfold bequiv in Hb.
    (* [rewrite] is able to instantiate the quantifier in [st] *)
    rewrite Hb in H. inversion H.
  Case "E_WhileLoop". (* immediate from the IH *)
    apply IHceval2. reflexivity.  Qed.

Theorem WHILE_true: forall b c,
     bequiv b BTrue  ->
     cequiv 
       (WHILE b DO c END)
       (WHILE BTrue DO SKIP END).
Proof. 
  intros.
  split; intros Has.
  - exfalso. eapply WHILE_true_nonterm; eauto.
  - exfalso. eapply WHILE_true_nonterm.
    apply refl_bequiv.
    eauto.
Qed.

(*-- Check --*)
Check WHILE_true: forall b c,
     bequiv b BTrue  ->
     cequiv 
       (WHILE b DO c END)
       (WHILE BTrue DO SKIP END).

