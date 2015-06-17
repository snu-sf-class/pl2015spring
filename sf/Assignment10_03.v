Require Export Assignment10_02.

(* problem #03: 10 points *)

(** **** Exercise: 1 star, optional (test_multistep_2)  *)
Lemma test_multistep_2:
  C 3 ==>* C 3.
Proof.
  apply multi_refl.
Qed.

(*-- Check --*)
Check test_multistep_2:
  C 3 ==>* C 3.

