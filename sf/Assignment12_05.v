Require Export Assignment12_04.

(* problem #05: 20 points *)

(** Translate this informal recursive definition into one using [fix]:
<<
   halve = 
     \x:Nat. 
        if x=0 then 0 
        else if (pred x)=0 then 0
        else 1 + (halve (pred (pred x))))
>>
*)

Definition halve : tm :=
  FILL_IN_HERE.

Example halve_type: empty |- halve \in TArrow TNat TNat.
Proof.
  (* unfold halve; eauto 10. *)
  exact FILL_IN_HERE.
Qed.

Example halve_10: tapp halve (tnat 10) ==>* tnat 5.
Proof.
  (* unfold halve; normalize. *)
  exact FILL_IN_HERE.
Qed.

Example halve_11: tapp halve (tnat 11) ==>* tnat 5.
Proof.
  (* unfold halve; normalize. *)
  exact FILL_IN_HERE.
Qed.


Theorem halve_correct: forall n,
   tapp halve (tnat (n+n)) ==>* tnat n.
Proof.
  exact FILL_IN_HERE.
Qed.

(*-- Check --*)

Check conj halve_type (conj halve_10 halve_11) :
  empty |- halve \in TArrow TNat TNat /\
  tapp halve (tnat 10) ==>* tnat 5 /\ 
  tapp halve (tnat 11) ==>* tnat 5.

Check halve_correct: forall n,
   tapp halve (tnat (n + n)) ==>* tnat n.

