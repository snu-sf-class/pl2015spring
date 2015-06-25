Require Import SfLib.
Require Import Program.
Require Import NPeano.

(* Important: 
   - You are NOT allowed to use the [admit] tactic.

   - You are ALLOWED to use any tactics including:

     [tauto], [intuition], [firstorder], [omega].

   - Just leave [exact FILL_IN_HERE] for those problems that you fail to prove.

    - Here is a (incomplete) list of tactics and tacticals you have learned.

      [intros]
      [revert]
      [reflexivity]
      [simpl]
      [rewrite]
      [induction]
      [assert]
      [unfold]
      [eapply] ... [with] ... [in] ...
      [destruct] ... [as] ... [eqn:] ...
      [inversion]
      [replace ... with ...]
      [symmetry]
      [generalize dependent]
      [split]
      [exists]
      [clear]
      [subst]
      [rename] ... [into] ...
      [contradiction]
      [constructor]
      [eauto]
      [repeat]
      [try]
      [;]

*)

Definition FILL_IN_HERE {T: Type} : T.  Admitted.

Axiom functional_extensionality : forall {X Y: Type} {f g : X -> Y},
    (forall (x: X), f x = g x) ->  f = g.

(**************
  Imp Language
 ***************)

Definition state := id -> nat.

Definition empty_state : state :=
  fun _ => 0.

Definition update (st : state) (x : id) (n : nat) : state :=
  fun x' => if eq_id_dec x x' then n else st x'.

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | AId : id -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Tactic Notation "aexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ANum" | Case_aux c "AId" | Case_aux c "APlus"
  | Case_aux c "AMinus" | Case_aux c "AMult" ].

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

Tactic Notation "bexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "BTrue" | Case_aux c "BFalse" | Case_aux c "BEq"
  | Case_aux c "BLe" | Case_aux c "BNot" | Case_aux c "BAnd" ].

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2  => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => beq_nat (aeval st a1) (aeval st a2)
  | BLe a1 a2   => ble_nat (aeval st a1) (aeval st a2)
  | BNot b1     => negb (beval st b1)
  | BAnd b1 b2  => andb (beval st b1) (beval st b2)
  end.

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com.

Tactic Notation "com_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "SKIP" | Case_aux c "::=" | Case_aux c ";;"
  | Case_aux c "IFB" | Case_aux c "WHILE" ].

Notation "'SKIP'" :=
  CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).

Reserved Notation "c1 '/' st '||' st'" (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      SKIP / st || st
  | E_Ass  : forall st a1 n x,
      aeval st a1 = n ->
      (x ::= a1) / st || (update st x n)
  | E_Seq : forall c1 c2 st st' st'',
      c1 / st  || st' ->
      c2 / st' || st'' ->
      (c1 ;; c2) / st || st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      c1 / st || st' ->
      (IFB b THEN c1 ELSE c2 FI) / st || st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      c2 / st || st' ->
      (IFB b THEN c1 ELSE c2 FI) / st || st'
  | E_WhileEnd : forall b st c,
      beval st b = false ->
      (WHILE b DO c END) / st || st
  | E_WhileLoop : forall st st' st'' b c,
      beval st b = true ->
      c / st || st' ->
      (WHILE b DO c END) / st' || st'' ->
      (WHILE b DO c END) / st || st''

  where "c1 '/' st '||' st'" := (ceval c1 st st').

Hint Constructors ceval.

Tactic Notation "ceval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_Skip" | Case_aux c "E_Ass" | Case_aux c "E_Seq"
  | Case_aux c "E_IfTrue" | Case_aux c "E_IfFalse"
  | Case_aux c "E_WhileEnd" | Case_aux c "E_WhileLoop" ].

(**************
  Hoare Logic & Rules
 ***************)

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


(**************
  STLC Language
 ***************)

Inductive ty : Type :=
  | TArrow : ty -> ty -> ty
  | TNat   : ty
  | TUnit  : ty
  | TProd  : ty -> ty -> ty
  | TSum   : ty -> ty -> ty
  | TList  : ty -> ty.

Tactic Notation "T_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "TArrow" | Case_aux c "TNat"
  | Case_aux c "TProd" | Case_aux c "TUnit"
  | Case_aux c "TSum" | Case_aux c "TList"  ].

Inductive tm : Type :=
  (* pure STLC *)
  | tvar : id -> tm
  | tapp : tm -> tm -> tm
  | tabs : id -> ty -> tm -> tm
  (* numbers *)
  | tnat : nat -> tm
  | tsucc : tm -> tm
  | tpred : tm -> tm
  | tmult : tm -> tm -> tm
  | tif0  : tm -> tm -> tm -> tm
  (* units *)
  | tunit : tm
  (* pairs *)
  | tpair : tm -> tm -> tm
  | tfst : tm -> tm
  | tsnd : tm -> tm
  (* let *)
  | tlet : id -> tm -> tm -> tm 
          (* i.e., [let x = t1 in t2] *)
  (* sums *)
  | tinl : ty -> tm -> tm
  | tinr : ty -> tm -> tm
  | tcase : tm -> id -> tm -> id -> tm -> tm  
          (* i.e., [case t0 of inl x1 => t1 | inr x2 => t2] *)
  (* lists *)
  | tnil : ty -> tm
  | tcons : tm -> tm -> tm
  | tlcase : tm -> tm -> id -> id -> tm -> tm 
          (* i.e., [lcase t1 of | nil -> t2 | x::y -> t3] *)
  (* fix *)
  | tfix  : tm -> tm.

Tactic Notation "t_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "tvar" | Case_aux c "tapp" | Case_aux c "tabs"
  | Case_aux c "tnat" | Case_aux c "tsucc" | Case_aux c "tpred"
  | Case_aux c "tmult" | Case_aux c "tif0"
  | Case_aux c "tpair" | Case_aux c "tfst" | Case_aux c "tsnd"
  | Case_aux c "tunit" | Case_aux c "tlet" 
  | Case_aux c "tinl" | Case_aux c "tinr" | Case_aux c "tcase"
  | Case_aux c "tnil" | Case_aux c "tcons" | Case_aux c "tlcase"
  | Case_aux c "tfix" ].

Fixpoint subst (x:id) (s:tm) (t:tm) : tm :=
  match t with
  | tvar y => 
      if eq_id_dec x y then s else t
  | tabs y T t1 => 
      tabs y T (if eq_id_dec x y then t1 else (subst x s t1))
  | tapp t1 t2 => 
      tapp (subst x s t1) (subst x s t2)
  | tnat n => 
      tnat n
  | tsucc t1 => 
      tsucc (subst x s t1)
  | tpred t1 => 
      tpred (subst x s t1)
  | tmult t1 t2 => 
      tmult (subst x s t1) (subst x s t2)
  | tif0 t1 t2 t3 => 
      tif0 (subst x s t1) (subst x s t2) (subst x s t3)
  | tpair t1 t2 => 
      tpair (subst x s t1) (subst x s t2)
  | tfst t1 => 
      tfst (subst x s t1)
  | tsnd t1 => 
      tsnd (subst x s t1)
  | tunit => tunit
  | tlet y t1 t2 => 
      tlet y (subst x s t1) (if eq_id_dec x y then t2 else (subst x s t2))
  | tinl T t1 => 
      tinl T (subst x s t1)
  | tinr T t1 => 
      tinr T (subst x s t1)
  | tcase t0 y1 t1 y2 t2 => 
      tcase (subst x s t0) 
         y1 (if eq_id_dec x y1 then t1 else (subst x s t1))
         y2 (if eq_id_dec x y2 then t2 else (subst x s t2))
  | tnil T => 
      tnil T
  | tcons t1 t2 => 
      tcons (subst x s t1) (subst x s t2)
  | tlcase t1 t2 y1 y2 t3 => 
      tlcase (subst x s t1) (subst x s t2) y1 y2
        (if eq_id_dec x y1 then 
           t3 
         else if eq_id_dec x y2 then t3 
              else (subst x s t3))
  | tfix t1 => tfix (subst x s t1)
  end.

Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).

Inductive value : tm -> Prop :=
  | v_abs : forall x T11 t12,
      value (tabs x T11 t12)
  (* Numbers are values: *)
  | v_nat : forall n1,
      value (tnat n1)
  (* A pair is a value if both components are: *)
  | v_pair : forall v1 v2,
      value v1 ->
      value v2 ->
      value (tpair v1 v2)
  (* A unit is always a value *)
  | v_unit : value tunit
  (* A tagged value is a value:  *)
  | v_inl : forall v T,
      value v -> 
      value (tinl T v)
  | v_inr : forall v T,
      value v -> 
      value (tinr T v)
  (* A list is a value iff its head and tail are values: *)
  | v_lnil : forall T, value (tnil T)
  | v_lcons : forall v1 vl,
      value v1 ->
      value vl ->
      value (tcons v1 vl)
  (* A fix is a value *)
  | v_fix : forall v,
      value v -> 
      value (tfix v)
  .

Hint Constructors value.

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T11 t12 v2,
       value v2 ->
       (tapp (tabs x T11 t12) v2) ==> [x:=v2]t12
  | ST_App1 : forall t1 t1' t2,
       t1 ==> t1' ->
       (tapp t1 t2) ==> (tapp t1' t2)
  | ST_App2 : forall v1 t2 t2',
       value v1 ->
       t2 ==> t2' ->
       (tapp v1 t2) ==> (tapp v1 t2')
  (* nats *)
  | ST_Succ1 : forall t1 t1',
       t1 ==> t1' ->
       (tsucc t1) ==> (tsucc t1')
  | ST_SuccNat : forall n1,
       (tsucc (tnat n1)) ==> (tnat (S n1))
  | ST_Pred : forall t1 t1',
       t1 ==> t1' ->
       (tpred t1) ==> (tpred t1')
  | ST_PredNat : forall n1,
       (tpred (tnat n1)) ==> (tnat (pred n1))
  | ST_Mult1 : forall t1 t1' t2,
       t1 ==> t1' ->
       (tmult t1 t2) ==> (tmult t1' t2)
  | ST_Mult2 : forall v1 t2 t2',
       value v1 ->
       t2 ==> t2' ->
       (tmult v1 t2) ==> (tmult v1 t2')
  | ST_MultNats : forall n1 n2,
       (tmult (tnat n1) (tnat n2)) ==> (tnat (mult n1 n2))
  | ST_If01 : forall t1 t1' t2 t3,
       t1 ==> t1' ->
       (tif0 t1 t2 t3) ==> (tif0 t1' t2 t3)
  | ST_If0Zero : forall t2 t3,
       (tif0 (tnat 0) t2 t3) ==> t2
  | ST_If0Nonzero : forall n t2 t3,
       (tif0 (tnat (S n)) t2 t3) ==> t3
  (* pairs *)
  | ST_Pair1 : forall t1 t1' t2,
        t1 ==> t1' ->
        (tpair t1 t2) ==> (tpair t1' t2)
  | ST_Pair2 : forall v1 t2 t2',
        value v1 ->
        t2 ==> t2' ->
        (tpair v1 t2) ==> (tpair v1 t2')
  | ST_Fst1 : forall t1 t1',
        t1 ==> t1' ->
        (tfst t1) ==> (tfst t1')
  | ST_FstPair : forall v1 v2,
        value v1 ->
        value v2 ->
        (tfst (tpair v1 v2)) ==> v1
  | ST_Snd1 : forall t1 t1',
        t1 ==> t1' ->
        (tsnd t1) ==> (tsnd t1')
  | ST_SndPair : forall v1 v2,
        value v1 ->
        value v2 ->
        (tsnd (tpair v1 v2)) ==> v2
  (* let *)
  | ST_Let1 : forall x t1 t1' t2,
       t1 ==> t1' ->
       (tlet x t1 t2) ==> (tlet x t1' t2)
  | ST_LetValue : forall x v1 t2,
       value v1 ->
       (tlet x v1 t2) ==> [x:=v1]t2
  (* sums *)
  | ST_Inl : forall t1 t1' T,
        t1 ==> t1' ->
        (tinl T t1) ==> (tinl T t1')
  | ST_Inr : forall t1 t1' T,
        t1 ==> t1' ->
        (tinr T t1) ==> (tinr T t1')
  | ST_Case : forall t0 t0' x1 t1 x2 t2,
        t0 ==> t0' ->
        (tcase t0 x1 t1 x2 t2) ==> (tcase t0' x1 t1 x2 t2)
  | ST_CaseInl : forall v0 x1 t1 x2 t2 T,
        value v0 -> 
        (tcase (tinl T v0) x1 t1 x2 t2) ==> [x1:=v0]t1
  | ST_CaseInr : forall v0 x1 t1 x2 t2 T,
        value v0 -> 
        (tcase (tinr T v0) x1 t1 x2 t2) ==> [x2:=v0]t2
  (* lists *)
  | ST_Cons1 : forall t1 t1' t2,
       t1 ==> t1' ->
       (tcons t1 t2) ==> (tcons t1' t2)
  | ST_Cons2 : forall v1 t2 t2',
       value v1 ->
       t2 ==> t2' ->
       (tcons v1 t2) ==> (tcons v1 t2')
  | ST_Lcase1 : forall t1 t1' t2 x1 x2 t3,
       t1 ==> t1' ->
       (tlcase t1 t2 x1 x2 t3) ==> (tlcase t1' t2 x1 x2 t3)
  | ST_LcaseNil : forall T t2 x1 x2 t3,
       (tlcase (tnil T) t2 x1 x2 t3) ==> t2
  | ST_LcaseCons : forall v1 vl t2 x1 x2 t3,
       value v1  ->
       value vl  ->
       (tlcase (tcons v1 vl) t2 x1 x2 t3) ==> (subst x2 vl (subst x1 v1 t3))
  (* fix *)
  | ST_Fix1 : forall t1 t1',
       t1 ==> t1' ->
       (tfix t1) ==> (tfix t1')
  | ST_AppFix : forall F1 v2,
       value F1 ->
       value v2 ->
       (tapp (tfix F1) v2) ==> (tapp (tapp F1 (tfix F1)) v2)

where "t1 '==>' t2" := (step t1 t2).

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_AppAbs" | Case_aux c "ST_App1" | Case_aux c "ST_App2"
  | Case_aux c "ST_Succ1" | Case_aux c "ST_SuccNat"
  | Case_aux c "ST_Pred1" | Case_aux c "ST_PredNat"
  | Case_aux c "ST_Mult1" | Case_aux c "ST_Mult2"
  | Case_aux c "ST_MultNats" | Case_aux c "ST_If01"
  | Case_aux c "ST_If0Zero" | Case_aux c "ST_If0Nonzero"
  | Case_aux c "ST_Pair1" | Case_aux c "ST_Pair2"
  | Case_aux c "ST_Fst1" | Case_aux c "ST_FstPair"
  | Case_aux c "ST_Snd1" | Case_aux c "ST_SndPair"
  | Case_aux c "ST_Let1" | Case_aux c "ST_LetValue"
  | Case_aux c "ST_Inl" | Case_aux c "ST_Inr" | Case_aux c "ST_Case"
  | Case_aux c "ST_CaseInl" | Case_aux c "ST_CaseInr"
  | Case_aux c "ST_Cons1" | Case_aux c "ST_Cons2" | Case_aux c "ST_Lcase1"
  | Case_aux c "ST_LcaseNil" | Case_aux c "ST_LcaseCons"
  | Case_aux c "ST_Fix1" | Case_aux c "ST_AppFix"
  ].

Notation multistep := (multi step).
Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).

Hint Constructors step.
Hint Constructors multi.

Definition context := partial_map ty.

Reserved Notation "Gamma '|--' t '\in' T" (at level 40).

Inductive has_type : context -> tm -> ty -> Prop :=
  (* Typing rules for proper terms *)
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      Gamma |-- (tvar x) \in T
  | T_Abs : forall Gamma x T11 T12 t12,
      (extend Gamma x T11) |-- t12 \in T12 -> 
      Gamma |-- (tabs x T11 t12) \in (TArrow T11 T12)
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma |-- t1 \in (TArrow T1 T2) -> 
      Gamma |-- t2 \in T1 -> 
      Gamma |-- (tapp t1 t2) \in T2
  (* nats *)
  | T_Nat : forall Gamma n1,
      Gamma |-- (tnat n1) \in TNat
  | T_Succ : forall Gamma t1,
      Gamma |-- t1 \in TNat ->
      Gamma |-- (tsucc t1) \in TNat
  | T_Pred : forall Gamma t1,
      Gamma |-- t1 \in TNat ->
      Gamma |-- (tpred t1) \in TNat
  | T_Mult : forall Gamma t1 t2,
      Gamma |-- t1 \in TNat ->
      Gamma |-- t2 \in TNat ->
      Gamma |-- (tmult t1 t2) \in TNat
  | T_If0 : forall Gamma t1 t2 t3 T1,
      Gamma |-- t1 \in TNat ->
      Gamma |-- t2 \in T1 ->
      Gamma |-- t3 \in T1 ->
      Gamma |-- (tif0 t1 t2 t3) \in T1
  (* pairs *)
  | T_Pair : forall Gamma t1 t2 T1 T2,
      Gamma |-- t1 \in T1 ->
      Gamma |-- t2 \in T2 ->
      Gamma |-- (tpair t1 t2) \in (TProd T1 T2)
  | T_Fst : forall Gamma t T1 T2,
      Gamma |-- t \in (TProd T1 T2) ->
      Gamma |-- (tfst t) \in T1
  | T_Snd : forall Gamma t T1 T2,
      Gamma |-- t \in (TProd T1 T2) ->
      Gamma |-- (tsnd t) \in T2
  (* unit *)
  | T_Unit : forall Gamma,
      Gamma |-- tunit \in TUnit
  (* let *)
  | T_Let : forall Gamma x t1 t2 T1 T2,
      Gamma |-- t1 \in T1 ->
      (extend Gamma x T1) |-- t2 \in T2 ->
      Gamma |-- tlet x t1 t2 \in T2
  (* sums *)
  | T_Inl : forall Gamma t1 T1 T2,
      Gamma |-- t1 \in T1 ->
      Gamma |-- (tinl T2 t1) \in (TSum T1 T2)
  | T_Inr : forall Gamma t2 T1 T2,
      Gamma |-- t2 \in T2 ->
      Gamma |-- (tinr T1 t2) \in (TSum T1 T2)
  | T_Case : forall Gamma t0 x1 T1 t1 x2 T2 t2 T,
      Gamma |-- t0 \in (TSum T1 T2) -> 
      (extend Gamma x1 T1) |-- t1 \in T ->
      (extend Gamma x2 T2) |-- t2 \in T -> 
      Gamma |-- (tcase t0 x1 t1 x2 t2) \in T
  (* lists *)
  | T_Nil : forall Gamma T,
      Gamma |-- (tnil T) \in (TList T)
  | T_Cons : forall Gamma t1 t2 T1,
      Gamma |-- t1 \in T1 ->
      Gamma |-- t2 \in (TList T1) ->
      Gamma |-- (tcons t1 t2) \in (TList T1)
  | T_Lcase : forall Gamma t1 T1 t2 x1 x2 t3 T2,
      Gamma |-- t1 \in (TList T1) ->
      Gamma |-- t2 \in T2 ->
      (extend (extend Gamma x2 (TList T1)) x1 T1) |-- t3 \in T2 ->
      Gamma |-- (tlcase t1 t2 x1 x2 t3) \in T2
  (* fix *)
  | T_Fix : forall Gamma t1 T1 T2,
      Gamma |-- t1 \in TArrow (TArrow T1 T2) (TArrow T1 T2) ->
      Gamma |-- tfix t1 \in TArrow T1 T2

where "Gamma '|--' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type.

Tactic Notation "has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_Var" | Case_aux c "T_Abs" | Case_aux c "T_App" 
  | Case_aux c "T_Nat" | Case_aux c "T_Succ" | Case_aux c "T_Pred"
  | Case_aux c "T_Mult" | Case_aux c "T_If0"
  | Case_aux c "T_Pair" | Case_aux c "T_Fst" | Case_aux c "T_Snd"
  | Case_aux c "T_Unit" 
(* let *)
  | Case_aux c "T_Let" 
  | Case_aux c "T_Inl" | Case_aux c "T_Inr" | Case_aux c "T_Case"
  | Case_aux c "T_Nil" | Case_aux c "T_Cons" | Case_aux c "T_Lcase" 
(* fix *)
  | Case_aux c "T_Fix" 
].

Hint Extern 2 (has_type _ (tapp _ _) _) =>
  eapply T_App; auto.
Hint Extern 2 (has_type _ (tlcase _ _ _ _ _) _) =>
  eapply T_Lcase; auto.
Hint Extern 2 (_ = _) => compute; reflexivity.

(**************
  Tatic [normalize1] and [normalize]
 ***************)

Tactic Notation "print_goal" := match goal with |- ?x => idtac x end.

Tactic Notation "normalize1" :=
  print_goal; eapply multi_step ; [ (eauto 10; fail) | (instantiate; simpl)].

Tactic Notation "normalize" := 
   repeat normalize1;
   apply multi_refl.

Lemma tsucc_compat: forall t t',
  t ==>* t' ->
  tsucc t ==>* tsucc t'.
Proof.
  intros; induction H; eauto.
Qed.

(**************
  Example Code for Exam Problems
 ***************)

(* Variables *)

Notation A := (Id 0).
Notation B := (Id 1).
Notation I := (Id 2).
Notation J := (Id 3).
Notation K := (Id 4).
Notation M := (Id 6).
Notation N := (Id 5).
Notation X := (Id 7).
Notation Y := (Id 8).
Notation Z := (Id 9).
Notation Plus := (Id 10).
Notation SUM := (Id 11).

(* Dead Code Elimination *)

Fixpoint optimize_dce (c: com) : com :=
  match c with
  | SKIP     =>
      SKIP
  | i ::= a  =>
      match a with
      | AId j => if eq_id_dec i j then SKIP else i ::= a
      | _ => i ::= a
      end
  | c1 ;; c2  =>
      (optimize_dce c1) ;; (optimize_dce c2)
  | IFB b THEN c1 ELSE c2 FI =>
      IFB b
      THEN optimize_dce c1
      ELSE optimize_dce c2
      FI
  | WHILE b DO c END =>
      WHILE b DO
        optimize_dce c
      END
  end.

(* Summation function *)

Fixpoint sum n :=
  match n with 
  | 0 => 0 
  | S m => n + sum m 
  end.

(* Summation Program *)

Definition sum_com : com :=
  SUM ::= ANum 0 ;;
  WHILE BNot (BEq (AId N) (ANum 0)) DO
    SUM ::= APlus (AId N) (AId SUM);;
    N ::= AMinus (AId N) (ANum 1)
  END.

Definition sum2_com : com :=
  SUM ::= ANum 0 ;;
  I ::= ANum 0 ;;
  WHILE BNot (BEq (AId I) (AId N)) DO
    I ::= APlus (ANum 1) (AId I) ;;
    SUM ::= APlus (AId I) (AId SUM)
  END.

(* foo Program *)

Definition tmfoo: tm :=
  tabs X (TProd (TArrow TNat TNat) (TSum TUnit TNat)) (
    tlet Y (tfst (tvar X)) (tlet Z (tsnd (tvar X)) (
      tcase (tvar Z)
        A (tvar Y)
        B (tabs M TNat (tapp (tvar Y) (tmult (tvar M) (tvar B))))
    ))
  ).

(*=========== 3141592 ===========*)

(* Easy *)

(* Find the weakest precondition [WP] of [X := X+2] for postcondition [X < 8].

      {{ WP }} X := Y*2 + 2 {{ X < 8 }}

   Hint: use the lemma [eq_id].
*)

Definition WP : Assertion :=
  fun st => st Y < 3.

(*
Check eq_id.

Theorem is_wp_example :
  is_wp WP (X ::= APlus (AMult (AId Y) (ANum 2)) (ANum 2)) (fun st => st X < 8).
Proof.
  unfold WP; split; red; intros.
  - inversion H; subst.
    unfold update; rewrite eq_id; simpl; omega.
  - eapply H in H0; eauto.
    unfold update in H0; rewrite eq_id in H0; simpl in *; omega.
Qed.

(*-- Check --*)

Check is_wp_example :
  is_wp WP (X ::= APlus (AId X) (ANum 2)) (fun st => st X > 8).
*)

(*=========== 3141592 [20] ===========*)

(* Easy *)

(*
  Write an Imp program [sort_two] that sorts values in the variables 'X' and 'Y'.
  In other words, [sort_two] should satisfy 

  {{ X = n /\ Y = m }}
     sort_two 
  {{ X <= Y /\ ((X = n /\ Y = m) \/ (X = m /\ Y = n)) }}
*)

Definition sort_two : com :=
  IFB (BLe (AId X) (AId Y)) THEN SKIP ELSE (Z ::= AId X;; X ::= AId Y;; Y ::= AId Z) FI.

Example sort_two_ex1: forall st
    (RUN: sort_two / update (update empty_state X 5) Y 3 || st),
  st X = 3 /\ st Y = 5.
Proof.
  intros.
  repeat match goal with [ H: ceval _ _ _ |- _ ] => rename H into _X; dependent destruction _X end. 
  auto.
Qed.

Example sort_two_ex2: forall st
    (RUN: sort_two / update (update empty_state X 2) Y 7 || st),
  st X = 2 /\ st Y = 7.
Proof.
  intros.
  repeat match goal with [H: ceval _ _ _ |- _] => rename H into _X; dependent destruction _X end. 
  auto.
Qed.

(* Medium *)

(* Hint: use the following lemmas and the tactic [omega]. *)

Check ble_nat_true.
Check ble_nat_false.

Theorem sort_two_correct: forall n m,
  {{ fun st => st X = n /\ st Y = m }} 
    sort_two 
  {{ fun st => st X <= st Y /\ ((st X = n /\ st Y = m) \/ (st X = m /\ st Y = n)) }}.
Proof.
  unfold sort_two; intros.
  eapply hoare_consequence_pre.
  - eapply hoare_if.
    + eapply hoare_skip.
    + eapply hoare_seq.
      * eapply hoare_seq; apply hoare_asgn. 
      * apply hoare_asgn.
  - unfold assn_sub, update; simpl. 
    repeat intro; destruct H; rewrite H, H0.
    split; intros; [apply ble_nat_true in H1 | apply ble_nat_false in H1]; omega.
Qed.

(*-- Check --*)

Check conj sort_two_ex1 sort_two_ex2: 
  (forall st
    (RUN: sort_two / update (update empty_state X 5) Y 3 || st),
  st X = 3 /\ st Y = 5)
  /\
  (forall st
    (RUN: sort_two / update (update empty_state X 2) Y 7 || st),
  st X = 2 /\ st Y = 7).

Check sort_two_correct: forall n m,
  {{ fun st => st X = n /\ st Y = m }} 
    sort_two 
  {{ fun st => st X <= st Y /\ ((st X = n /\ st Y = m) \/ (st X = m /\ st Y = n)) }}.

(*=========== 3141592 ===========*)

(* Hard *)

(* Hint: use the lemma [Nat.sub_0_r] and the tactic [omega]. *)

Check Nat.sub_0_r.

Theorem sum_com_correct: forall n,
  {{ fun st => st N = n}} 
    sum_com
  {{ fun st => st SUM = sum n }}.
Proof.
  intros; unfold sum_com.
  eapply hoare_seq.
  - eapply hoare_consequence_post.
    + apply hoare_while with (P := fun st => st SUM + sum (st N) = sum n).
      eapply hoare_seq; [apply hoare_asgn|].
      eapply hoare_consequence_pre; [apply hoare_asgn|].
      unfold assn_sub, update; simpl.
      repeat intro; destruct H.
      destruct (st N); simpl in *; try discriminate. 
      rewrite Nat.sub_0_r; omega.
    + simpl; repeat intro; destruct H.
      destruct (st N); simpl in *; try discriminate.
      omega.
  - eapply hoare_consequence_pre; [apply hoare_asgn|].
    unfold assn_sub, update; simpl.
    repeat intro; rewrite H; auto.
Qed.

(*-- Check --*)

Check sum_com_correct: forall n,
  {{ fun st => st N = n}} 
    sum_com
  {{ fun st => st SUM = sum n }}.

(*=========== 3141592 ===========*)

(* Very Hard *)

(* Hint: use the tactic [omega]. *)
(* Hint: use the following lemmas *)

Check negb_true_iff.
Check negb_false_iff.
Check beq_nat_true.
Check beq_nat_false.

Theorem sum2_com_correct: forall n,
  {{ fun st => st N = n}} 
    sum2_com
  {{ fun st => st SUM = sum n }}.
Proof.
  intros; unfold sum2_com.
  eapply hoare_seq.
  { eapply hoare_seq.
    - eapply hoare_consequence_post.
      + apply hoare_while with 
        (P := fun st => st SUM = sum (st I) /\ st I <= n /\ st N = n).
        eapply hoare_seq; [apply hoare_asgn|].
        eapply hoare_consequence_pre; [apply hoare_asgn|].
        unfold assn_sub, update.
        simpl; repeat intro.
        destruct H as [[HA [HB HC]] HD]; subst. 
        rewrite negb_true_iff in HD. 
        apply beq_nat_false in HD.
        omega.
      + red; simpl; repeat intro.
        destruct H as [[HA [HB HC]] HD]; subst. 
        rewrite negb_false_iff in HD.
        apply beq_nat_true in HD. 
        rewrite HA; f_equal; omega.
    - eapply hoare_asgn.
  }
  repeat red; repeat intro.
  inversion H; subst.
  unfold update; simpl; omega.
Qed.

(*-- Check --*)

Check sum2_com_correct: forall n,
  {{ fun st => st N = n}} 
    sum2_com
  {{ fun st => st SUM = sum n }}.

(*=========== 3141592 ===========*)

(* Medium *)

(* Hint:
   Use [functional_extensionality].
*)

Theorem optimize_dce_correct: forall st st' c,
  (c / st || st') -> (optimize_dce c / st || st').
Proof.
  intros; induction H; simpl; intros; eauto.
  destruct a1; eauto.
  destruct (eq_id_dec x i) eqn: EQ; subst; eauto.
  replace (update st i (aeval st (AId i))) with st; eauto.
  apply functional_extensionality.
  unfold update; intros.
  destruct (eq_id_dec i x); subst; eauto.
Qed.

(*-- Check --*)
Check optimize_dce_correct: forall st st' c,
  (c / st || st') -> (optimize_dce c / st || st').

(*=========== 3141592 ===========*)

(* Easy *)

(* Write the type of the program [tmfoo] *)

Definition tmfooty : ty :=
  TArrow (TProd (TArrow TNat TNat) (TSum TUnit TNat)) (TArrow TNat TNat).

Lemma tmfoo_type: empty |-- tmfoo \in tmfooty.
Proof.
  unfold tmfoo, tmfooty; eauto 15.
Qed.

(*-- Check --*)

Check tmfoo_type: empty |-- tmfoo \in tmfooty.

(*=========== 3141592 ===========*)

(* Easy *)

(** Translate this informal recursive definition into one using [fix]:
<<
   tmmultpair = 
     \X:Nat*Nat. mult (fst X) (fst X)
>>
*)

Definition tmmultpair : tm :=
  tabs X (TProd TNat TNat) (
    tmult (tfst (tvar X)) (tsnd (tvar X))
  ).

Example tmmultpair_type: empty |-- tmmultpair \in TArrow (TProd TNat TNat) TNat.
Proof.
  unfold tmmultpair; eauto 10.
Qed.

Example tmmultpair_ex1: tapp tmmultpair (tpair (tnat 2) (tnat 3)) ==>* tnat 6.
Proof.
  unfold tmmultpair; normalize.
Qed.

Example tmmultpair_ex2: tapp tmmultpair (tpair (tnat 5) (tnat 8)) ==>* tnat 40.
Proof.
  unfold tmmultpair; normalize.
Qed.

(*-- Check --*)

Check conj tmmultpair_type (conj tmmultpair_ex1 tmmultpair_ex2) :
  empty |-- tmmultpair \in TArrow (TProd TNat TNat) TNat /\
  tapp tmmultpair (tpair (tnat 2) (tnat 3)) ==>* tnat 6 /\
  tapp tmmultpair (tpair (tnat 5) (tnat 8)) ==>* tnat 40.

(*=========== 3141592 [20] ===========*)

(* Medium *)

(** Translate this informal recursive definition into one using [fix]:
<<
   tmplus = 
     \x:Nat. \y:Nat.
        if x=0 then y 
        else succ (tmplus (pred x) y)
>>
*)

Definition tmplus : tm :=
  tfix (tabs Plus (TArrow TNat (TArrow TNat TNat)) (tabs X TNat (tabs Y TNat (
    tif0 (tvar X)
    (tvar Y)
    (tsucc (tapp (tapp (tvar Plus) (tpred (tvar X))) (tvar Y)))
  )))).

Example tmplus_type: empty |-- tmplus \in TArrow TNat (TArrow TNat TNat).
Proof.
  unfold tmplus; eauto 10.
Qed.

Example tmplus_ex1: tapp (tapp tmplus (tnat 2)) (tnat 3) ==>* tnat 5.
Proof.
  unfold tmplus; normalize.
Qed.

Example tmplus_ex2: tapp (tapp tmplus (tnat 1)) (tnat 8) ==>* tnat 9.
Proof.
  unfold tmplus; normalize.
Qed.

(* Medium *)

(* Hint: 
   Use the tactic [normalize1] and [normalize], which takes one-step of execution.
     (e.g.) [do 5 normalize1] takes 5 steps of execution.
   Note that you have to unfold the definition [tmplus] before using [normalize1] and [normalize].

   Use the lemma [tsucc_compat].
 *)

Check tsucc_compat.

Theorem tmplus_correct: forall n m,
   tapp (tapp tmplus (tnat n)) (tnat m) ==>* tnat (n+m).
Proof.
  induction n; unfold tmplus; intros.
  - normalize.
  - do 5 normalize1.
    eapply multi_trans.
    + normalize1.
      eapply tsucc_compat, IHn.
    + normalize.
Qed.

(*-- Check --*)

Check conj tmplus_type (conj tmplus_ex1 tmplus_ex2) :
  empty |-- tmplus \in TArrow TNat (TArrow TNat TNat) /\
  tapp (tapp tmplus (tnat 2)) (tnat 3) ==>* tnat 5 /\ 
  tapp (tapp tmplus (tnat 1)) (tnat 8) ==>* tnat 9.

Check tmplus_correct: forall n m,
   tapp (tapp tmplus (tnat n)) (tnat m) ==>* tnat (n+m).

