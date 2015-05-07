Require Export Assignment06_05.

(* problem #06: 20 points *)

(** **** Exercise: 4 stars, advanced (no_repeats)  *)
(** The following inductively defined proposition... *)

Inductive appears_in {X:Type} (a:X) : list X -> Prop :=
  | ai_here : forall l, appears_in a (a::l)
  | ai_later : forall b l, appears_in a l -> appears_in a (b::l).

(** ...gives us a precise way of saying that a value [a] appears at
    least once as a member of a list [l]. 

    Here's a pair of warm-ups about [appears_in].
*)

Lemma appears_in_app : forall (X:Type) (xs ys : list X) (x:X), 
     appears_in x (xs ++ ys) -> appears_in x xs \/ appears_in x ys.
Proof.
  (* FILL IN HERE *)
  intros X xs.
  induction xs as [| h t IH].
  - intros.
    simpl in H.
    right. apply H.
  - intros.
    simpl in H.
    inversion H.
    + left. apply ai_here.
    + apply IH in H1.
      destruct H1 as [appt | appys].
      * left. apply ai_later. apply appt.
      * right. apply appys.
Qed.

Lemma app_appears_in : forall (X:Type) (xs ys : list X) (x:X), 
     appears_in x xs \/ appears_in x ys -> appears_in x (xs ++ ys).
Proof.
  (* FILL IN HERE *)
  intros X xs.
  induction xs as [| h t IH].
  - intros.
    simpl.
    inversion H.
    + inversion H0.
    + apply H0.
  - intros.
    destruct H as [aiht | aiys].
    + inversion aiht.
      * simpl. apply ai_here.
      * simpl. apply ai_later.
        apply IH.
        left. apply H0.
    + simpl.
      apply ai_later.
      apply IH.
      right. apply aiys.
Qed.

