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

(* problem #25: 10 points *)









(** 3 stars, optional (ev_plus_plus)  *)
(** Here's an exercise that just requires applying existing lemmas.  No
    induction or even case analysis is needed, but some of the rewriting
    may be tedious. 
    Hint: You can use [plus_comm], [plus_assoc], [double_plus], [double_even], [ev_sum], [ev_ev__ev].
*)
Check plus_comm.
Check plus_assoc.
Check double_plus.
Check double_even.
Check ev_sum.
Check ev_ev__ev.

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  (* FILL IN HERE *) admit.
Qed.
(** [] *)


