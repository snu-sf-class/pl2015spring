Require Export Assignment10_10.

(* problem #11: 10 points *)

(** **** Exercise: 3 stars, optional (interp_tm)  *)
(** Remember that we also defined big-step evaluation of [tm]s as a
    function [evalF].  Prove that it is equivalent to the existing
    semantics.
 
    Hint: we just proved that [eval] and [multistep] are
    equivalent, so logically it doesn't matter which you choose.
    One will be easier than the other, though!  *)

Theorem evalF_eval : forall t n,
  evalF t = n <-> t || n.
Proof.
  intros t.
  induction t.
  - intros.
    split; intros.
    + simpl in H. subst. constructor.
    + inversion H. simpl. reflexivity.
  - intros.
    simpl.
    split; intros.
    + subst.
      constructor.
      * apply IHt1. reflexivity.
      * apply IHt2. reflexivity.
    + inversion H. subst.
      apply IHt1 in H2.
      apply IHt2 in H4.
      subst. reflexivity.
Qed.

(*-- Check --*)
Check evalF_eval : forall t n,
  evalF t = n <-> t || n.

