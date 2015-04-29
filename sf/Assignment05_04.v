Require Export Assignment05_03.

(* problem #04: 10 points *)



Theorem iff_trans : forall P Q R : Prop, 
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  (* FILL IN HERE *)
  intros.
  split.
  - intros HP.
    apply H0.
    apply H.
    apply HP.
  - intros HR.
    apply H.
    apply H0.
    apply HR.
Qed.


