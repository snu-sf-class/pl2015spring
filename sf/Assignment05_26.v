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
Require Import Assignment05_11.
Require Import Assignment05_12.
Require Import Assignment05_13.
Require Import Assignment05_14.
Require Import Assignment05_15.
Require Import Assignment05_16.
Require Import Assignment05_17.
Require Import Assignment05_18.
Require Import Assignment05_19.
Require Import Assignment05_20.
Require Import Assignment05_21.
Require Import Assignment05_22.
Require Import Assignment05_23.
Require Import Assignment05_24.
Require Import Assignment05_25.

(* problem #26: 10 points *)











(** 3 star (even__ev)  
    Note that proving [even__ev] directly is hard.
    You might find it easier to prove [even__ev_strong] first
    and then prove [even__ev] using it.
*)

Lemma even__ev_strong: forall n : nat, 
  (even (pred n) -> ev (pred n)) /\ (even n -> ev n).
Proof.
  (* FILL IN HERE *) admit.
Qed.
(** [] *)


