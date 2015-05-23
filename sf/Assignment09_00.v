
Require Export Imp.

(* Important: 
   - You are NOT allowed to use the [admit] tactic.

   - You are ALLOWED to use any tactics including:

     [tauto], [intuition], [firstorder], [omega].

   - Just leave [exact FILL_IN_HERE] for those problems that you fail to prove.
*)

(* Useful Lemmas *)

Lemma negb_true: 
  forall b, negb b = true -> b = false.
Proof. intros; apply negb_true_iff; eauto. Qed.

Lemma negb_false: 
  forall b, negb b = false -> b = true.
Proof. intros; apply negb_false_iff; eauto. Qed.

Check beq_nat_true.
Check beq_nat_false.
Check ble_nat_true.
Check ble_nat_false.



Definition FILL_IN_HERE {T: Type} : T.  Admitted.

Axiom functional_extensionality : forall {X Y: Type} {f g : X -> Y},
    (forall (x: X), f x = g x) ->  f = g.

Definition Assertion := state -> Prop.

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Notation "P ->> Q" :=
  (assert_implies P Q) (at level 80) : hoare_spec_scope.
Open Scope hoare_spec_scope.

Notation "P <<->> Q" :=
  (P ->> Q /\ Q ->> P) (at level 80) : hoare_spec_scope.

Definition hoare_triple
           (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st',
       c / st || st'  ->
       P st  ->
       Q st'.

Notation "{{ P }}  c  {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level)
  : hoare_spec_scope.

Definition assn_sub X a P : Assertion :=
  fun (st : state) =>
    P (update st X (aeval st a)).

Notation "P [ X |-> a ]" := (assn_sub X a P) (at level 10).

Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} (X ::= a) {{Q}}.
Proof.
  unfold hoare_triple.
  intros Q X a st st' HE HQ.
  inversion HE. subst.
  unfold assn_sub in HQ. assumption.  Qed.

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q c Hhoare Himp.
  intros st st' Hc HP. apply (Hhoare st st'). 
  assumption. apply Himp. assumption. Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P Q Q' c Hhoare Himp.
  intros st st' Hc HP. 
  apply Himp.
  apply (Hhoare st st'). 
  assumption. assumption. Qed.

Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
  {{P'}} c {{Q'}} ->
  P ->> P' ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q Q' c Hht HPP' HQ'Q.
  apply hoare_consequence_pre with (P' := P').
  apply hoare_consequence_post with (Q' := Q').
  assumption. assumption. assumption.  Qed.

Theorem hoare_skip : forall P,
     {{P}} SKIP {{P}}.
Proof.
  intros P st st' H HP. inversion H. subst.
  assumption.  Qed.

Theorem hoare_seq : forall P Q R c1 c2,
     {{Q}} c2 {{R}} ->
     {{P}} c1 {{Q}} ->
     {{P}} c1;;c2 {{R}}.
Proof.
  intros P Q R c1 c2 H1 H2 st st' H12 Pre.
  inversion H12; subst.
  apply (H1 st'0 st'); try assumption.
  apply (H2 st st'0); assumption. Qed.

Theorem hoare_if : forall Q1 Q2 Q b c1 c2,
  {{Q1}} c1 {{Q}} ->
  {{Q2}} c2 {{Q}} ->
  {{fun st => (beval st b = true -> Q1 st) /\ (beval st b = false -> Q2 st) }} 
    (IFB b THEN c1 ELSE c2 FI) 
  {{Q}}.
Proof.
  intros Q1 Q2 Q b c1 c2 HTrue HFalse st st' HE [HQ1 HQ2].
  inversion HE; subst; eauto. 
Qed.

Lemma hoare_while : forall P b c,
  {{fun st => P st /\ beval st b = true}} c {{P}} ->
  {{P}} WHILE b DO c END {{fun st => P st /\ beval st b = false}}.
Proof.
  intros P b c Hhoare st st' He HP.
  (* Like we've seen before, we need to reason by induction 
     on [He], because, in the "keep looping" case, its hypotheses 
     talk about the whole loop instead of just [c]. *)
  remember (WHILE b DO c END) as wcom eqn:Heqwcom.
  ceval_cases (induction He) Case;
    try (inversion Heqwcom); subst; clear Heqwcom.
  Case "E_WhileEnd".
    split. assumption. assumption.
  Case "E_WhileLoop".
    apply IHHe2. reflexivity.
    apply (Hhoare st st'). assumption.
      split. assumption. assumption.
Qed.

Definition is_wp P c Q :=
  {{P}} c {{Q}} /\
  forall P', {{P'}} c {{Q}} -> (P' ->> P).

(** Here is a cute little program for computing the parity of the
    value initially stored in [X] (due to Daniel Cristofani).
    {{ X = m }}
  WHILE 2 <= X DO
    X ::= X - 2
  END
    {{ X = parity m }}
    The mathematical [parity] function used in the specification is
    defined in Coq as follows: *)

Fixpoint parity x :=
  match x with
  | 0 => 0
  | 1 => 1
  | S (S x') => parity x'
  end.

