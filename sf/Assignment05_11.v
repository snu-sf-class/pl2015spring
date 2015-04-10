Require Import Assignment05_00.
Require Import Assignment05_01.
Require Import Assignment05_02.
Require Import Assignment05_03.
Require Import Assignment05_04.
Require Import Assignment05_05.
Require Import Assignment05_06.
Require Import Assignment05_07.
Require Import Assignment05_08.
Require Import Assignment05_09.
Require Import Assignment05_10.

(* problem #11: 10 points *)


(** 3 stars (excluded_middle_irrefutable)  *)
(** This theorem implies that it is always safe to add a decidability
axiom (i.e. an instance of excluded middle) for any _particular_ Prop [P].
Why? Because we cannot prove the negation of such an axiom; if we could,
we would have both [~ (P \/ ~P)] and [~ ~ (P \/ ~P)], a contradiction. *)

Theorem excluded_middle_irrefutable:  forall (P:Prop), ~ ~ (P \/ ~ P).  
Proof.
  (* FILL IN HERE *) admit.
Qed.




