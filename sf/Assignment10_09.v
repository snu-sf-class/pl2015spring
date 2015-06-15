Require Export Assignment10_08.

(* problem #09: 10 points *)

(** **** Exercise: 3 stars (step__eval)  *)
Lemma step__eval : forall t t' n,
     t ==> t' ->
     t' || n ->
     t || n.
Proof.
  intros t t' n Hs. generalize dependent n.
  exact FILL_IN_HERE.
Qed.

(*-- Check --*)
Check step__eval : forall t t' n,
     t ==> t' ->
     t' || n ->
     t || n.

