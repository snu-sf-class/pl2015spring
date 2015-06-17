Require Export Assignment10_14.

(* problem #15: 10 points *)

(* Hint: 

   First study the chapter "Auto.v".

   Using [;], [try] and [eauto], you can prove it in 7 lines thanks to:. 
     Hint Constructors bstep.

   You can use the following intro pattern:
     destruct ... as [[? | ?] | [? ?]].
*)

Theorem bexp_strong_progress: forall st b,
  (b = BTrue \/ b = BFalse) \/
  exists b', b / st ==>b b'.
Proof.
  intros. induction b; eauto; right;
  try (destruct (aexp_strong_progress st a) as [[n1 Hn1] | [a1' Ha1']];
      destruct (aexp_strong_progress st a0) as [[n2 Hn2] | [a2' Ha2']];
      subst; eexists; eauto).
  - destruct IHb as [[Hbt | Hbf] | [b' Hb']]; subst; eexists; eauto.
  - destruct IHb1 as [[Hbt1 | Hbf1] | [b1' Hb1']];
      destruct IHb2 as [[Hbt2 | Hbf2] | [b2' Hb2']]; subst; eexists; eauto.
Qed.

(*-- Check --*)
Check bexp_strong_progress: forall st b,
  (b = BTrue \/ b = BFalse) \/
  exists b', b / st ==>b b'.

