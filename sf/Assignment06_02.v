Require Export Assignment06_01.

(* problem #02: 10 points *)

(** **** Exercise: 3 stars, optional (not_exists_dist)  *)
(** (The other direction of this theorem requires the classical "law
    of the excluded middle".) *)

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  (* FILL IN HERE *)
  intros.
  assert (empx: P x \/ ~ P x).
  {
    apply H.
  }
  destruct empx as [px | npx].
  - apply px.
  - apply ex_falso_quodlibet.
    apply H0.
    exists x.
    apply npx.
Qed.
(** [] *)

