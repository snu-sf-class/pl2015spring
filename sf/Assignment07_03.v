Require Export Assignment07_02.

(* problem #03: 20 points *)

(** **** Exercise: 3 stars  (bevalR)  *)
(** Write a relation [bevalR] in the same style as
    [aevalR], and prove that it is equivalent to [beval].*)


Inductive bevalR: bexp -> bool -> Prop :=
(* FILL IN HERE *)
.

Theorem beval_iff_bevalR : forall b bv,
  bevalR b bv <-> beval b = bv.
Proof.
  admit.
Qed.

(** [] *)

