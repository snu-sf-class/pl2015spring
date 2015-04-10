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
Require Import Assignment05_26.
Require Import Assignment05_27.

(* problem #28: 30 points *)


(** 4 stars (palindromes)  *)
(** A palindrome is a sequence that reads the same backwards as
    forwards.

    - Define an inductive proposition [pal] on [list X] that
      captures what it means to be a palindrome. (Hint: You'll need
      three cases.  Your definition should be based on the structure
      of the list; just having a single constructor
        c : forall l, l = rev l -> pal l
      may seem obvious, but will not work very well.)
 
    - Prove [pal_app_rev] that 
       forall l, pal (l ++ rev l).
    - Prove [pal_rev] that 
       forall l, pal l -> l = rev l.
*)

Inductive pal {X: Type} : list X -> Prop :=
(* FILL IN HERE *)
.

Theorem pal_app_rev: forall (X: Type) (l: list X),
  pal (l ++ rev l).
Proof.
  (* FILL IN HERE *) admit.
Qed.

Theorem pal_rev: forall (X: Type) (l: list X),
  pal l -> l = rev l.
Proof.
  (* FILL IN HERE *) admit.
Qed.

(** [] *)




