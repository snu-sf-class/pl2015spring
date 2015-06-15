Require Export Assignment08_05.

(* problem #06: 10 points *)

(** **** Exercise: 2 stars (skip_right)  *)
(** Prove that adding a SKIP after a command results in an equivalent
    program *)

Theorem skip_right: forall c,
  cequiv 
    (c;; SKIP) 
    c.
Proof. 
  intros. split.
  - intros Hseq.
    inversion Hseq.
    inversion H4. subst.
    apply H1.
  - intros Hc.
    apply E_Seq with st'; auto.
    constructor.
Qed.

(*-- Check --*)
Check skip_right: forall c,
  cequiv 
    (c;; SKIP) 
    c.

