Require Import Omega.

(*
Inductive nat : Type := 
| O : nat 
| S : nat -> nat
.
*)

(*
Definition plus := 
fix plus (n m : nat) {struct n} : nat :=
  match n with
  | 0 => m
  | S p => S (plus p m)
  end
.
     : nat -> nat -> nat
*)

Print plus.

Fixpoint sum (n: nat) : nat :=
  match n with
  | 0 => 0
  | S m => sum m + n
  end.

Eval compute in (sum 5).
Eval compute in (sum 6).

Lemma sum_eqn: 
  forall n, 2 * sum n = n * (n + 1).
Proof.
  induction n.
  - auto.
  - simpl.
    rewrite (mult_plus_distr_l n 1).
    rewrite <- IHn. 
    omega.
Qed.

Print sum_eqn.

