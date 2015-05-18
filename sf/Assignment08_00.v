
Require Export SfLib.

(* Important: 
   - You are NOT allowed to use the [admit] tactic.

   - You are ALLOWED to use any tactics including:

     [tauto], [intuition], [firstorder], [omega].

   - Just leave [exact FILL_IN_HERE] for those problems that you fail to prove.
*)


Definition FILL_IN_HERE {T: Type} : T.  Admitted.

Axiom functional_extensionality : forall {X Y: Type} {f g : X -> Y},
    (forall (x: X), f x = g x) ->  f = g.



Definition state := id -> nat.

Definition empty_state : state :=
  fun _ => 0.

Definition update (st : state) (x : id) (n : nat) : state :=
  fun x' => if eq_id_dec x x' then n else st x'.

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | AId : id -> aexp                (* <----- NEW *)
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Tactic Notation "aexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ANum" | Case_aux c "AId" | Case_aux c "APlus"
  | Case_aux c "AMinus" | Case_aux c "AMult" ].

(** Defining a few variable names as notational shorthands will make
    examples easier to read: *)

Definition X : id := Id 0.
Definition Y : id := Id 1.
Definition Z : id := Id 2.

Opaque X.
Opaque Y.
Opaque Z.

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

Tactic Notation "ceval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_Skip" | Case_aux c "E_Ass" | Case_aux c "E_Seq"
  | Case_aux c "E_IfTrue" | Case_aux c "E_IfFalse"
  | Case_aux c "E_WhileEnd" | Case_aux c "E_WhileLoop" ].

Definition aequiv (a1 a2 : aexp) : Prop :=
  forall (st:state), 
    aeval st a1 = aeval st a2.

Definition bequiv (b1 b2 : bexp) : Prop :=
  forall (st:state), 
    beval st b1 = beval st b2.

(** For commands, the situation is a little more subtle.  We can't
    simply say "two commands are behaviorally equivalent if they
    evaluate to the same ending state whenever they are started in the
    same initial state," because some commands (in some starting
    states) don't terminate in any final state at all!  What we need
    instead is this: two commands are behaviorally equivalent if, for
    any given starting state, they either both diverge or both
    terminate in the same final state.  A compact way to express this
    is "if the first one terminates in a particular state then so does
    the second, and vice versa." *)

Definition cequiv (c1 c2 : com) : Prop :=
  forall (st st' : state), 
    (c1 / st || st') <-> (c2 / st || st').

Definition atrans_sound (atrans : aexp -> aexp) : Prop :=
  forall (a : aexp),
    aequiv a (atrans a).

Definition btrans_sound (btrans : bexp -> bexp) : Prop :=
  forall (b : bexp),
    bequiv b (btrans b).

Definition ctrans_sound (ctrans : com -> com) : Prop :=
  forall (c : com),
    cequiv c (ctrans c).

(* ####################################################### *)
(** ** Behavioral Equivalence is an Equivalence *)

Lemma refl_aequiv : forall (a : aexp), aequiv a a.
Proof.
  intros a st. reflexivity.  Qed.

Lemma sym_aequiv : forall (a1 a2 : aexp), 
  aequiv a1 a2 -> aequiv a2 a1.
Proof.
  intros a1 a2 H. intros st. symmetry. apply H.  Qed.

Lemma trans_aequiv : forall (a1 a2 a3 : aexp), 
  aequiv a1 a2 -> aequiv a2 a3 -> aequiv a1 a3. 
Proof.
  unfold aequiv. intros a1 a2 a3 H12 H23 st.
  rewrite (H12 st). rewrite (H23 st). reflexivity.  Qed.

Lemma refl_bequiv : forall (b : bexp), bequiv b b.
Proof.
  unfold bequiv. intros b st. reflexivity.  Qed.

Lemma sym_bequiv : forall (b1 b2 : bexp), 
  bequiv b1 b2 -> bequiv b2 b1.
Proof.
  unfold bequiv. intros b1 b2 H. intros st. symmetry. apply H.  Qed.

Lemma trans_bequiv : forall (b1 b2 b3 : bexp), 
  bequiv b1 b2 -> bequiv b2 b3 -> bequiv b1 b3. 
Proof.
  unfold bequiv. intros b1 b2 b3 H12 H23 st.
  rewrite (H12 st). rewrite (H23 st). reflexivity.  Qed.

Lemma refl_cequiv : forall (c : com), cequiv c c.
Proof.
  unfold cequiv. intros c st st'. apply iff_refl.  Qed.

Lemma sym_cequiv : forall (c1 c2 : com), 
  cequiv c1 c2 -> cequiv c2 c1.
Proof.
  unfold cequiv. intros c1 c2 H st st'.
  assert (c1 / st || st' <-> c2 / st || st') as H'. 
    SCase "Proof of assertion". apply H.
  apply iff_sym. assumption.
Qed.

Lemma iff_trans : forall (P1 P2 P3 : Prop), 
  (P1 <-> P2) -> (P2 <-> P3) -> (P1 <-> P3).
Proof.
  intros P1 P2 P3 H12 H23.
  inversion H12. inversion H23.
  split; intros A. 
    apply H1. apply H. apply A.
    apply H0. apply H2. apply A.  Qed.

Lemma trans_cequiv : forall (c1 c2 c3 : com), 
  cequiv c1 c2 -> cequiv c2 c3 -> cequiv c1 c3. 
Proof.
  unfold cequiv. intros c1 c2 c3 H12 H23 st st'.
  apply iff_trans with (c2 / st || st'). apply H12. apply H23.  Qed.

(* ######################################################## *)
(** ** Behavioral Equivalence is a Congruence *)

Theorem CAss_congruence : forall i a1 a1',
  aequiv a1 a1' ->
  cequiv (CAss i a1) (CAss i a1').
Proof.
  intros i a1 a2 Heqv st st'.
  split; intros Hceval.
  Case "->".
    inversion Hceval. subst. apply E_Ass. 
    rewrite Heqv. reflexivity.
  Case "<-".
    inversion Hceval. subst. apply E_Ass.
    rewrite Heqv. reflexivity.  Qed.

(** The congruence property for loops is a little more interesting,
    since it requires induction.

    _Theorem_: Equivalence is a congruence for [WHILE] -- that is, if
    [b1] is equivalent to [b1'] and [c1] is equivalent to [c1'], then
    [WHILE b1 DO c1 END] is equivalent to [WHILE b1' DO c1' END].

    _Proof_: Suppose [b1] is equivalent to [b1'] and [c1] is
    equivalent to [c1'].  We must show, for every [st] and [st'], that
    [WHILE b1 DO c1 END / st || st'] iff [WHILE b1' DO c1' END / st
    || st'].  We consider the two directions separately.

      - ([->]) We show that [WHILE b1 DO c1 END / st || st'] implies
        [WHILE b1' DO c1' END / st || st'], by induction on a
        derivation of [WHILE b1 DO c1 END / st || st'].  The only
        nontrivial cases are when the final rule in the derivation is
        [E_WhileEnd] or [E_WhileLoop].

          - [E_WhileEnd]: In this case, the form of the rule gives us
            [beval st b1 = false] and [st = st'].  But then, since
            [b1] and [b1'] are equivalent, we have [beval st b1' =
            false], and [E-WhileEnd] applies, giving us [WHILE b1' DO
            c1' END / st || st'], as required.

          - [E_WhileLoop]: The form of the rule now gives us [beval st
            b1 = true], with [c1 / st || st'0] and [WHILE b1 DO c1
            END / st'0 || st'] for some state [st'0], with the
            induction hypothesis [WHILE b1' DO c1' END / st'0 ||
            st'].  

            Since [c1] and [c1'] are equivalent, we know that [c1' /
            st || st'0].  And since [b1] and [b1'] are equivalent, we
            have [beval st b1' = true].  Now [E-WhileLoop] applies,
            giving us [WHILE b1' DO c1' END / st || st'], as
            required.

      - ([<-]) Similar. [] *)

Theorem CWhile_congruence : forall b1 b1' c1 c1',
  bequiv b1 b1' -> cequiv c1 c1' ->
  cequiv (WHILE b1 DO c1 END) (WHILE b1' DO c1' END).
Proof.
  (* WORKED IN CLASS *)
  unfold bequiv,cequiv.
  intros b1 b1' c1 c1' Hb1e Hc1e st st'.
  split; intros Hce.
  Case "->".
    remember (WHILE b1 DO c1 END) as cwhile eqn:Heqcwhile.
    induction Hce; inversion Heqcwhile; subst.
    SCase "E_WhileEnd".
      apply E_WhileEnd. rewrite <- Hb1e. apply H.
    SCase "E_WhileLoop".
      apply E_WhileLoop with (st' := st').
      SSCase "show loop runs". rewrite <- Hb1e. apply H.
      SSCase "body execution". 
        apply (Hc1e st st').  apply Hce1. 
      SSCase "subsequent loop execution".
        apply IHHce2. reflexivity.
  Case "<-".
    remember (WHILE b1' DO c1' END) as c'while eqn:Heqc'while.
    induction Hce; inversion Heqc'while; subst.
    SCase "E_WhileEnd".
      apply E_WhileEnd. rewrite -> Hb1e. apply H.
    SCase "E_WhileLoop".
      apply E_WhileLoop with (st' := st').
      SSCase "show loop runs". rewrite -> Hb1e. apply H.
      SSCase "body execution". 
        apply (Hc1e st st').  apply Hce1. 
      SSCase "subsequent loop execution".
        apply IHHce2. reflexivity.  Qed.

(* ######################################################## *)
(** ** Definitions used in the exercises *)

Definition loop : com :=
  WHILE BTrue DO
    SKIP
  END.

Fixpoint no_whiles (c : com) : bool :=
  match c with
  | SKIP       => true
  | _ ::= _    => true
  | c1 ;; c2  => andb (no_whiles c1) (no_whiles c2)
  | IFB _ THEN ct ELSE cf FI => andb (no_whiles ct) (no_whiles cf)
  | WHILE _ DO _ END  => false
  end.

Fixpoint fold_constants_aexp (a : aexp) : aexp :=
  match a with
  | ANum n       => ANum n
  | AId i        => AId i
  | APlus a1 a2  => 
      match (fold_constants_aexp a1, fold_constants_aexp a2) with
      | (ANum n1, ANum n2) => ANum (n1 + n2)
      | (a1', a2') => APlus a1' a2'
      end
  | AMinus a1 a2 => 
      match (fold_constants_aexp a1, fold_constants_aexp a2) with
      | (ANum n1, ANum n2) => ANum (n1 - n2)
      | (a1', a2') => AMinus a1' a2'
      end
  | AMult a1 a2  => 
      match (fold_constants_aexp a1, fold_constants_aexp a2) with
      | (ANum n1, ANum n2) => ANum (n1 * n2)
      | (a1', a2') => AMult a1' a2'
      end
  end.

Fixpoint fold_constants_bexp (b : bexp) : bexp :=
  match b with
  | BTrue        => BTrue
  | BFalse       => BFalse
  | BEq a1 a2  => 
      match (fold_constants_aexp a1, fold_constants_aexp a2) with
      | (ANum n1, ANum n2) => if beq_nat n1 n2 then BTrue else BFalse
      | (a1', a2') => BEq a1' a2'
      end
  | BLe a1 a2  => 
      match (fold_constants_aexp a1, fold_constants_aexp a2) with
      | (ANum n1, ANum n2) => if ble_nat n1 n2 then BTrue else BFalse
      | (a1', a2') => BLe a1' a2'
      end
  | BNot b1  => 
      match (fold_constants_bexp b1) with
      | BTrue => BFalse
      | BFalse => BTrue
      | b1' => BNot b1'
      end
  | BAnd b1 b2  => 
      match (fold_constants_bexp b1, fold_constants_bexp b2) with
      | (_, BFalse) | (BFalse, _) => BFalse
      | (b1', BTrue) | (BTrue, b1') => b1'
      | (b1', b2') => BAnd b1' b2'
      end
  end.

Fixpoint fold_constants_com (c : com) : com :=
  match c with
  | SKIP      => 
      SKIP
  | i ::= a  => 
      CAss i (fold_constants_aexp a)
  | SKIP ;; c' | c' ;; SKIP => c'
  | c1 ;; c2  => 
      (fold_constants_com c1) ;; (fold_constants_com c2)
  | IFB b THEN c1 ELSE c2 FI => 
      match fold_constants_bexp b with
      | BTrue => fold_constants_com c1
      | BFalse => fold_constants_com c2
      | b' => IFB b' THEN fold_constants_com c1 
                     ELSE fold_constants_com c2 FI
      end
  | WHILE b DO c END => 
      match fold_constants_bexp b with
      | BTrue => WHILE BTrue DO SKIP END
      | BFalse => SKIP
      | b' => WHILE b' DO (fold_constants_com c) END
      end
  end.

Theorem fold_constants_aexp_sound : 
  atrans_sound fold_constants_aexp.
Proof.
  unfold atrans_sound. intros a. unfold aequiv. intros st.
  aexp_cases (induction a) Case; simpl;
    (* ANum and AId follow immediately *)
    try reflexivity;
    (* APlus, AMinus, and AMult follow from the IH
       and the observation that
              aeval st (APlus a1 a2) 
            = ANum ((aeval st a1) + (aeval st a2)) 
            = aeval st (ANum ((aeval st a1) + (aeval st a2)))
       (and similarly for AMinus/minus and AMult/mult) *)
    try (destruct (fold_constants_aexp a1);
         destruct (fold_constants_aexp a2);
         rewrite IHa1; rewrite IHa2; reflexivity). Qed.

Theorem skip_left: forall c,
  cequiv 
     (SKIP;; c) 
     c.
Proof. 
  (* WORKED IN CLASS *)
  intros c st st'.
  split; intros H.
  Case "->". 
    inversion H. subst. 
    inversion H2. subst. 
    assumption.
  Case "<-". 
    apply E_Seq with st.
    apply E_Skip. 
    assumption.  
Qed.

Theorem IFB_true: forall b c1 c2,
     bequiv b BTrue  ->
     cequiv 
       (IFB b THEN c1 ELSE c2 FI) 
       c1.
Proof.
  intros b c1 c2 Hb.
  split; intros H.
  Case "->".
    inversion H; subst.
    SCase "b evaluates to true".
      assumption.
    SCase "b evaluates to false (contradiction)".
      unfold bequiv in Hb. simpl in Hb.
      rewrite Hb in H5.
      inversion H5.
  Case "<-".
    apply E_IfTrue; try assumption.
    unfold bequiv in Hb. simpl in Hb.
    rewrite Hb. reflexivity.  Qed.

(* ######################################################## *)
(* optimize_0plus *)

Fixpoint optimize_0plus_aexp (e:aexp) : aexp := 
  match e with
  | ANum n => 
      ANum n
  | AId i => AId i
  | APlus (ANum 0) e' | APlus e' (ANum 0) =>
      optimize_0plus_aexp e'
  | APlus e1 e2 => 
      APlus (optimize_0plus_aexp e1) (optimize_0plus_aexp e2)
  | AMinus e1 e2 => 
      AMinus (optimize_0plus_aexp e1) (optimize_0plus_aexp e2)
  | AMult e1 e2 => 
      AMult (optimize_0plus_aexp e1) (optimize_0plus_aexp e2)
  end.

Fixpoint optimize_0plus_bexp (b : bexp) : bexp :=
  match b with
  | BTrue => BTrue
  | BFalse => BFalse
  | BEq a1 a2  => 
      BEq (optimize_0plus_aexp a1) (optimize_0plus_aexp a2)
  | BLe a1 a2  => 
      BLe (optimize_0plus_aexp a1) (optimize_0plus_aexp a2)
  | BNot b1  => 
      BNot (optimize_0plus_bexp b1)
  | BAnd b1 b2  => 
      BAnd (optimize_0plus_bexp b1) (optimize_0plus_bexp b2)
  end.

Fixpoint optimize_0plus_com (c : com) : com :=
  match c with
  | SKIP     => 
      SKIP
  | i ::= a  => 
      CAss i (optimize_0plus_aexp a)
  | c1 ;; c2  => 
      (optimize_0plus_com c1) ;; (optimize_0plus_com c2)
  | IFB b THEN c1 ELSE c2 FI => 
      IFB (optimize_0plus_bexp b) 
      THEN optimize_0plus_com c1 
      ELSE optimize_0plus_com c2 
      FI
  | WHILE b DO c END => 
      WHILE (optimize_0plus_bexp b) DO 
        (optimize_0plus_com c) 
      END
  end.

Definition constfold_0plus (c: com) : com :=
  optimize_0plus_com (fold_constants_com c).

Eval compute in 
  constfold_0plus
    (X ::= APlus (ANum 4) (ANum 5);;
     Y ::= AMinus (AId X) (ANum 3);;
     IFB BEq (AMinus (AId X) (AId Y)) (APlus (AId X) (AMinus (ANum 4) (ANum 4))) THEN
       SKIP 
     ELSE
       Y ::= ANum 0
     FI;;
     IFB BLe (ANum 0) (AMinus (ANum 4) (APlus (ANum 2) (ANum 1))) THEN
       Y ::= ANum 0
     ELSE
       SKIP 
     FI;;
     WHILE BEq (AId Y) (ANum 0) DO 
       X ::= APlus (AId X) (ANum 1) 
     END).
  

(* ######################################################## *)
(** HP Calculators, programming languages like Forth and Postscript,
    and abstract machines like the Java Virtual Machine all evaluate
    arithmetic expressions using a stack. For instance, the expression
<<
   (2*3)+(3*(4-2))
>>
   would be entered as
<<
   2 3 * 3 4 2 - * +
>>
   and evaluated like this:
<<
  []            |    2 3 * 3 4 2 - * +
  [2]           |    3 * 3 4 2 - * +
  [3, 2]        |    * 3 4 2 - * +
  [6]           |    3 4 2 - * +
  [3, 6]        |    4 2 - * +
  [4, 3, 6]     |    2 - * +
  [2, 4, 3, 6]  |    - * +
  [2, 3, 6]     |    * +
  [6, 6]        |    +
  [12]          |
>>

  The task of this exercise is to write a small compiler that
  translates [aexp]s into stack machine instructions.

  The instruction set for our stack language will consist of the
  following instructions:
     - [SPush n]: Push the number [n] on the stack.
     - [SLoad x]: Load the identifier [x] from the store and push it
                  on the stack
     - [SPlus]:   Pop the two top numbers from the stack, add them, and
                  push the result onto the stack.
     - [SMinus]:  Similar, but subtract.
     - [SMult]:   Similar, but multiply. *)

Inductive sinstr : Type :=
| SPush : nat -> sinstr
| SLoad : id -> sinstr
| SPlus : sinstr
| SMinus : sinstr
| SMult : sinstr.

(** Write a function to evaluate programs in the stack language. It
    takes as input a state, a stack represented as a list of
    numbers (top stack item is the head of the list), and a program
    represented as a list of instructions, and returns the stack after
    executing the program. Test your function on the examples below.

    Note that the specification leaves unspecified what to do when
    encountering an [SPlus], [SMinus], or [SMult] instruction if the
    stack contains less than two elements.  In a sense, it is
    immaterial what we do, since our compiler will never emit such a
    malformed program. *)

Fixpoint s_execute (st : state) (stack : list nat)
                   (prog : list sinstr)
                 : list nat :=
  match prog with
  | [] => stack
  | ins :: prog' => 
    match ins with
    | SPush n => s_execute st (n :: stack) prog'
    | SLoad x => s_execute st (st x :: stack) prog'
    | SPlus => 
      match stack with
      | na :: nb :: stack' => s_execute st (nb+na :: stack') prog'
      | _ => s_execute st stack prog'
      end
    | SMinus => 
      match stack with
      | na :: nb :: stack' => s_execute st (nb-na :: stack') prog'
      | _ => s_execute st stack prog'
      end
    | SMult =>
      match stack with
      | na :: nb :: stack' => s_execute st (nb*na :: stack') prog'
      | _ => s_execute st stack prog'
      end
    end
  end.

Eval compute in 
     s_execute empty_state []
       [SPush 5; SPush 3; SPush 1; SMinus].

Eval compute in
     s_execute (update empty_state X 3) [3;4]
       [SPush 4; SLoad X; SMult; SPlus].

