Require Export Assignment10_15.

(* problem #16: 10 points *)

(* Hint: 

   First study the chapter "Auto.v".

   Using [;], [try] and [eauto], you can prove it in 6 lines thanks to:
     Hint Constructors cstep.
 
   You can use the following intro pattern:
     destruct ... as [ | [? [? ?]]].
*)

Theorem cimp_strong_progress : forall c st,
  c = SKIP \/ 
  exists c' st', c / st ==>c c' / st'.
Proof.
  intros; induction c; eauto; right;
  try (destruct (aexp_strong_progress st a) as [[n Hn]|[a' Ha']];
       subst; eexists; eauto);
  try (destruct (bexp_strong_progress st b) as [[Hbt | Hbf]|[b' Hb']]);
  destruct IHc1 as [Hsk1 | [c1' [st1' Hc1']]];
  destruct IHc2 as [Hsk2 | [c2' [st2' Hc2']]]; subst; eexists; eauto.
Qed.

(*-- Check --*)
Check cimp_strong_progress : forall c st,
  c = SKIP \/ 
  exists c' st', c / st ==>c c' / st'.

