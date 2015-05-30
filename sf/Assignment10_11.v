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
  exact FILL_IN_HERE.
Qed.

(*-- Check --*)
Check evalF_eval : forall t n,
  evalF t = n <-> t || n.

