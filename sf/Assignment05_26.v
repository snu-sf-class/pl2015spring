Require Export Assignment05_25.

(* problem #26: 10 points *)











(** 3 star (even__ev)  
    Note that proving [even__ev] directly is hard.
    You might find it easier to prove [even__ev_strong] first
    and then prove [even__ev] using it.
*)

Lemma even__ev_strong: forall n : nat, 
  (even (pred n) -> ev (pred n)) /\ (even n -> ev n).
Proof.
  (* FILL IN HERE *)
  intros.
  induction n as [|n' IH].
  - split.
    + intros.
      simpl.
      apply ev_0.
    + intros.
      apply ev_0.
  - split.
    + inversion IH.
      simpl.
      apply H0.
    + inversion IH.
      destruct n'.
      * intros.
        inversion H1.
      * intros.
        simpl in H.
        apply ev_SS.
        apply H.
        inversion H1.
        unfold even.
        apply H3.
Qed.
(** [] *)


