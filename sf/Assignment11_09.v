Require Export Assignment11_08.

(* problem #09: 10 points *)

(** **** Exercise: 2 stars (subject_expansion)  *)
(** Having seen the subject reduction property, it is reasonable to
    wonder whether the opposity property -- subject _expansion_ --
    also holds.  That is, is it always the case that, if [t ==> t']
    and [|- t' \in T], then [|- t \in T]?  If so, prove it.  If
    not, give a counter-example.  (You do not need to prove your
    counter-example in Coq, but feel free to do so if you like.)
*)

Theorem subject_expansion_false: 
  exists t t' T,
    t ==> t' /\
    |- t' \in T /\
    ~ |- t \in T.
Proof.
  exact FILL_IN_HERE.
Qed.

(*-- Check --*)
Check subject_expansion_false: 
  exists t t' T,
    t ==> t' /\
    |- t' \in T /\
    ~ |- t \in T.

