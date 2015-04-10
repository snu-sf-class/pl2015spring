
Require Export MoreCoq.

(* Important: 
   - You are NOT allowed to use the [admit] tactic
     because [admit] simply admits any goal 
     regardless of whether it is provable or not.

     But, you can leave [admit] for problems that you cannot prove.
     Then you will get zero points for those problems.

   - You are NOT allowed to use the following tactics.

     [tauto], [intuition], [firstorder], [omega].

   - Do NOT add any additional `Require Import/Export`.
*)

Inductive and (P Q : Prop) : Prop :=
  conj : P -> Q -> (and P Q). 

Notation "P /\ Q" := (and P Q) : type_scope.

Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q
  | or_intror : Q -> or P Q. 

Notation "P \/ Q" := (or P Q) : type_scope.

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q) 
                      (at level 95, no associativity) 
                      : type_scope.

Inductive False : Prop := . 

Definition not (P:Prop) := P -> False.

Notation "~ x" := (not x) : type_scope.

Notation "x <> y" := (~ (x = y)) : type_scope.

Inductive le : nat -> nat -> Prop :=
  | le_n : forall n, le n n
  | le_S : forall n m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

Definition even (n:nat) : Prop := 
  evenb n = true.

Inductive ev : forall (n: nat), Prop :=
  | ev_0 : ev O
  | ev_SS : forall (n:nat) (pf_evn :ev n), ev (S (S n))
.

Inductive beautiful : nat -> Prop :=
| b_0   : beautiful 0
| b_3   : beautiful 3
| b_5   : beautiful 5
| b_sum : forall n m (beuty_n:beautiful n) (beauty_m: beautiful m),
            beautiful (n+m)
.

Inductive gorgeous : nat -> Prop :=
  g_0 : gorgeous 0
| g_plus3 : forall n, gorgeous n -> gorgeous (3+n)
| g_plus5 : forall n, gorgeous n -> gorgeous (5+n)
.



