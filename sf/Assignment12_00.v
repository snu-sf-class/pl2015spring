
Require Export Types.

Definition FILL_IN_HERE {T: Type} : T.  Admitted.

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

Definition stuck (t:tm) : Prop :=
  normal_form step t /\ ~ value t.

Definition context := partial_map ty.

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).

Inductive has_type : context -> tm -> ty -> Prop :=
  (* Typing rules for proper terms *)
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      Gamma |- (tvar x) \in T
  | T_Abs : forall Gamma x T11 T12 t12,
      (extend Gamma x T11) |- t12 \in T12 -> 
      Gamma |- (tabs x T11 t12) \in (TArrow T11 T12)
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma |- t1 \in (TArrow T1 T2) -> 
      Gamma |- t2 \in T1 -> 
      Gamma |- (tapp t1 t2) \in T2
  (* nats *)
  | T_Nat : forall Gamma n1,
      Gamma |- (tnat n1) \in TNat
  | T_Succ : forall Gamma t1,
      Gamma |- t1 \in TNat ->
      Gamma |- (tsucc t1) \in TNat
  | T_Pred : forall Gamma t1,
      Gamma |- t1 \in TNat ->
      Gamma |- (tpred t1) \in TNat
  | T_Mult : forall Gamma t1 t2,
      Gamma |- t1 \in TNat ->
      Gamma |- t2 \in TNat ->
      Gamma |- (tmult t1 t2) \in TNat
  | T_If0 : forall Gamma t1 t2 t3 T1,
      Gamma |- t1 \in TNat ->
      Gamma |- t2 \in T1 ->
      Gamma |- t3 \in T1 ->
      Gamma |- (tif0 t1 t2 t3) \in T1
  (* pairs *)
  | T_Pair : forall Gamma t1 t2 T1 T2,
      Gamma |- t1 \in T1 ->
      Gamma |- t2 \in T2 ->
      Gamma |- (tpair t1 t2) \in (TProd T1 T2)
  | T_Fst : forall Gamma t T1 T2,
      Gamma |- t \in (TProd T1 T2) ->
      Gamma |- (tfst t) \in T1
  | T_Snd : forall Gamma t T1 T2,
      Gamma |- t \in (TProd T1 T2) ->
      Gamma |- (tsnd t) \in T2
  (* unit *)
  | T_Unit : forall Gamma,
      Gamma |- tunit \in TUnit
  (* let *)
  | T_Let : forall Gamma x t1 t2 T1 T2,
      Gamma |- t1 \in T1 ->
      (extend Gamma x T1) |- t2 \in T2 ->
      Gamma |- tlet x t1 t2 \in T2
  (* sums *)
  | T_Inl : forall Gamma t1 T1 T2,
      Gamma |- t1 \in T1 ->
      Gamma |- (tinl T2 t1) \in (TSum T1 T2)
  | T_Inr : forall Gamma t2 T1 T2,
      Gamma |- t2 \in T2 ->
      Gamma |- (tinr T1 t2) \in (TSum T1 T2)
  | T_Case : forall Gamma t0 x1 T1 t1 x2 T2 t2 T,
      Gamma |- t0 \in (TSum T1 T2) -> 
      (extend Gamma x1 T1) |- t1 \in T ->
      (extend Gamma x2 T2) |- t2 \in T -> 
      Gamma |- (tcase t0 x1 t1 x2 t2) \in T
  (* lists *)
  | T_Nil : forall Gamma T,
      Gamma |- (tnil T) \in (TList T)
  | T_Cons : forall Gamma t1 t2 T1,
      Gamma |- t1 \in T1 ->
      Gamma |- t2 \in (TList T1) ->
      Gamma |- (tcons t1 t2) \in (TList T1)
  | T_Lcase : forall Gamma t1 T1 t2 x1 x2 t3 T2,
      Gamma |- t1 \in (TList T1) ->
      Gamma |- t2 \in T2 ->
      (extend (extend Gamma x2 (TList T1)) x1 T1) |- t3 \in T2 ->
      Gamma |- (tlcase t1 t2 x1 x2 t3) \in T2
  (* fix *)
  | T_Fix : forall Gamma t1 T1 T2,
      Gamma |- t1 \in TArrow (TArrow T1 T2) (TArrow T1 T2) ->
      Gamma |- tfix t1 \in TArrow T1 T2

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

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

Theorem progress : forall t T, 
     empty |- t \in T ->
     value t \/ exists t', t ==> t'. 
Proof with eauto.
  (* Theorem: Suppose empty |- t : T.  Then either
       1. t is a value, or
       2. t ==> t' for some t'.
     Proof: By induction on the given typing derivation. *)
  intros t T Ht.
  remember (@empty ty) as Gamma.
  generalize dependent HeqGamma.
  has_type_cases (induction Ht) Case; intros HeqGamma; subst.
  Case "T_Var".
    (* The final rule in the given typing derivation cannot be [T_Var],
       since it can never be the case that [empty |- x : T] (since the
       context is empty). *)
    inversion H.
  Case "T_Abs".
    (* If the [T_Abs] rule was the last used, then [t = tabs x T11 t12],
       which is a value. *)
    left...
  Case "T_App".
    (* If the last rule applied was T_App, then [t = t1 t2], and we know 
       from the form of the rule that
         [empty |- t1 : T1 -> T2]
         [empty |- t2 : T1]
       By the induction hypothesis, each of t1 and t2 either is a value 
       or can take a step. *)
    right.
    destruct IHHt1; subst...
    SCase "t1 is a value".
      destruct IHHt2; subst...
      SSCase "t2 is a value".
      (* If both [t1] and [t2] are values, then we know that 
         [t1 = tabs x T11 t12], since abstractions are the only values
         that can have an arrow type.  But 
         [(tabs x T11 t12) t2 ==> [x:=t2]t12] by [ST_AppAbs]. *)
        inversion H; subst; try (solve by inversion)...
      SSCase "t2 steps".
        (* If [t1] is a value and [t2 ==> t2'], then [t1 t2 ==> t1 t2'] 
           by [ST_App2]. *)
        inversion H0 as [t2' Hstp]. exists (tapp t1 t2')...
    SCase "t1 steps".
      (* Finally, If [t1 ==> t1'], then [t1 t2 ==> t1' t2] by [ST_App1]. *)
      inversion H as [t1' Hstp]. exists (tapp t1' t2)...
  Case "T_Nat".
    left...
  Case "T_Succ".
    right.
    destruct IHHt...
    SCase "t1 is a value".
      inversion H; subst; try solve by inversion.
      exists (tnat (S n1))...
    SCase "t1 steps".
      inversion H as [t1' Hstp].
      exists (tsucc t1')...
  Case "T_Pred".
    right.
    destruct IHHt...
    SCase "t1 is a value".
      inversion H; subst; try solve by inversion.
      exists (tnat (pred n1))...
    SCase "t1 steps".
      inversion H as [t1' Hstp].
      exists (tpred t1')...
  Case "T_Mult".
    right.
    destruct IHHt1...
    SCase "t1 is a value".
      destruct IHHt2...
      SSCase "t2 is a value".
        inversion H; subst; try solve by inversion.
        inversion H0; subst; try solve by inversion.
        exists (tnat (mult n1 n0))...
      SSCase "t2 steps".
        inversion H0 as [t2' Hstp].
        exists (tmult t1 t2')...
    SCase "t1 steps".
      inversion H as [t1' Hstp].
      exists (tmult t1' t2)...
  Case "T_If0".
    right.
    destruct IHHt1...
    SCase "t1 is a value".
      inversion H; subst; try solve by inversion.
      destruct n1 as [|n1'].
      SSCase "n1=0".
        exists t2...
      SSCase "n1<>0".
        exists t3...
    SCase "t1 steps".
      inversion H as [t1' H0].
      exists (tif0 t1' t2 t3)...
  Case "T_Pair".
    destruct IHHt1...
    SCase "t1 is a value".
      destruct IHHt2...
      SSCase "t2 steps".
        right.  inversion H0 as [t2' Hstp].
        exists (tpair t1 t2')...
    SCase "t1 steps".
      right. inversion H as [t1' Hstp].
      exists (tpair t1' t2)...
  Case "T_Fst".
    right.
    destruct IHHt...
    SCase "t1 is a value".
      inversion H; subst; try solve by inversion.
      exists v1...
    SCase "t1 steps".
      inversion H as [t1' Hstp].
      exists (tfst t1')...
  Case "T_Snd".
    right.
    destruct IHHt...
    SCase "t1 is a value".
      inversion H; subst; try solve by inversion.
      exists v2...
    SCase "t1 steps".
      inversion H as [t1' Hstp].
      exists (tsnd t1')...
  Case "T_Unit".
    left...
  Case "T_Let".
    right.
    destruct IHHt1; subst...
    destruct H...
  Case "T_Inl".
    destruct IHHt... 
    SCase "t1 steps". 
      right. inversion H as [t1' Hstp]... 
      (* exists (tinl _ t1')... *)
  Case "T_Inr".
    destruct IHHt... 
    SCase "t1 steps". 
      right. inversion H as [t1' Hstp]... 
      (* exists (tinr _ t1')... *)
  Case "T_Case".
    right. 
    destruct IHHt1...
    SCase "t0 is a value".
      inversion H; subst; try solve by inversion.
      SSCase "t0 is inl".
        exists ([x1:=v]t1)...  
      SSCase "t0 is inr".        
        exists ([x2:=v]t2)...
    SCase "t0 steps".
      inversion H as [t0' Hstp]. 
      exists (tcase t0' x1 t1 x2 t2)...
  Case "T_Nil".
    left...
  Case "T_Cons".
    destruct IHHt1...
    SCase "head is a value".
      destruct IHHt2...
      SSCase "tail steps".
        right. inversion H0 as [t2' Hstp].
        exists (tcons t1 t2')...
    SCase "head steps".
      right. inversion H as [t1' Hstp].
      exists (tcons t1' t2)...
  Case "T_Lcase".
    right.
    destruct IHHt1... 
    SCase "t1 is a value".
      inversion H; subst; try solve by inversion.
      SSCase "t1=tnil".
        exists t2...
      SSCase "t1=tcons v1 vl".
        exists ([x2:=vl]([x1:=v1]t3))...
    SCase "t1 steps".
      inversion H as [t1' Hstp].
      exists (tlcase t1' t2 x1 x2 t3)...
  Case "T_Fix".
  destruct IHHt...
  destruct H...
Qed.

Inductive appears_free_in : id -> tm -> Prop :=
  | afi_var : forall x,
      appears_free_in x (tvar x)
  | afi_app1 : forall x t1 t2,
      appears_free_in x t1 -> appears_free_in x (tapp t1 t2)
  | afi_app2 : forall x t1 t2,
      appears_free_in x t2 -> appears_free_in x (tapp t1 t2)
  | afi_abs : forall x y T11 t12,
        y <> x  ->
        appears_free_in x t12 ->
        appears_free_in x (tabs y T11 t12)
  (* nats *)
  | afi_succ : forall x t,
     appears_free_in x t ->
     appears_free_in x (tsucc t)
  | afi_pred : forall x t,
     appears_free_in x t -> 
     appears_free_in x (tpred t)
  | afi_mult1 : forall x t1 t2,
     appears_free_in x t1 -> 
     appears_free_in x (tmult t1 t2)
  | afi_mult2 : forall x t1 t2,
     appears_free_in x t2 -> 
     appears_free_in x (tmult t1 t2)
  | afi_if01 : forall x t1 t2 t3,
     appears_free_in x t1 -> 
     appears_free_in x (tif0 t1 t2 t3)
  | afi_if02 : forall x t1 t2 t3,
     appears_free_in x t2 -> 
     appears_free_in x (tif0 t1 t2 t3)
  | afi_if03 : forall x t1 t2 t3,
     appears_free_in x t3 -> 
     appears_free_in x (tif0 t1 t2 t3)
  (* pairs *)
  | afi_pair1 : forall x t1 t2,
      appears_free_in x t1 ->
      appears_free_in x (tpair t1 t2)
  | afi_pair2 : forall x t1 t2,
      appears_free_in x t2 ->
      appears_free_in x (tpair t1 t2)
  | afi_fst : forall x t,
      appears_free_in x t ->
      appears_free_in x (tfst t)
  | afi_snd : forall x t,
      appears_free_in x t ->
      appears_free_in x (tsnd t)
  (* let *)
  | afi_let1 : forall x y t1 t2,
      appears_free_in x t1 ->
      appears_free_in x (tlet y t1 t2) 
  | afi_let2 : forall x y t1 t2,
      y <> x  ->
      appears_free_in x t2 ->
      appears_free_in x (tlet y t1 t2) 
  (* sums *)
  | afi_inl : forall x t T,
      appears_free_in x t ->
      appears_free_in x (tinl T t)
  | afi_inr : forall x t T,
      appears_free_in x t ->
      appears_free_in x (tinr T t)
  | afi_case0 : forall x t0 x1 t1 x2 t2,
      appears_free_in x t0 ->
      appears_free_in x (tcase t0 x1 t1 x2 t2)
  | afi_case1 : forall x t0 x1 t1 x2 t2,
      x1 <> x -> 
      appears_free_in x t1 ->
      appears_free_in x (tcase t0 x1 t1 x2 t2)
  | afi_case2 : forall x t0 x1 t1 x2 t2,
      x2 <> x -> 
      appears_free_in x t2 ->
      appears_free_in x (tcase t0 x1 t1 x2 t2)
  (* lists *)
  | afi_cons1 : forall x t1 t2,
     appears_free_in x t1 ->
     appears_free_in x (tcons t1 t2)
  | afi_cons2 : forall x t1 t2,
     appears_free_in x t2 ->
     appears_free_in x (tcons t1 t2)
  | afi_lcase1 : forall x t1 t2 y1 y2 t3,
     appears_free_in x t1 ->
     appears_free_in x (tlcase t1 t2 y1 y2 t3)
  | afi_lcase2 : forall x t1 t2 y1 y2 t3,
     appears_free_in x t2 ->
     appears_free_in x (tlcase t1 t2 y1 y2 t3)
  | afi_lcase3 : forall x t1 t2 y1 y2 t3,
     y1 <> x ->
     y2 <> x ->
     appears_free_in x t3 ->
     appears_free_in x (tlcase t1 t2 y1 y2 t3)
  (* fix *)
  | afi_fix : forall x t1,
     appears_free_in x t1 ->
     appears_free_in x (tfix t1)
  .

Hint Constructors appears_free_in.

Definition closed (t:tm) :=
  forall x, ~ appears_free_in x t.

Lemma context_invariance : forall Gamma Gamma' t S,
     Gamma |- t \in S  ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x)  ->
     Gamma' |- t \in S.
Proof with eauto 12.
  intros. generalize dependent Gamma'.
  has_type_cases (induction H) Case; 
    intros Gamma' Heqv...
  Case "T_Var".
    apply T_Var... rewrite <- Heqv...
  Case "T_Abs".
    apply T_Abs... apply IHhas_type. intros y Hafi.
    unfold extend. 
    destruct (eq_id_dec x y)...
  Case "T_Let".
    eapply T_Let... apply IHhas_type2. intros y Hafi.
    unfold extend.
    destruct (eq_id_dec x y)...
  Case "T_Case".
    eapply T_Case... 
     apply IHhas_type2. intros y Hafi.
       unfold extend.
       destruct (eq_id_dec x1 y)... 
     apply IHhas_type3. intros y Hafi.
       unfold extend.
       destruct (eq_id_dec x2 y)...
  Case "T_Lcase".
    eapply T_Lcase... apply IHhas_type3. intros y Hafi.
    unfold extend. 
    destruct (eq_id_dec x1 y)...
    destruct (eq_id_dec x2 y)...
Qed.

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   Gamma |- t \in T ->
   exists T', Gamma x = Some T'.
Proof with eauto.
  intros x t T Gamma Hafi Htyp.
  has_type_cases (induction Htyp) Case; inversion Hafi; subst...
  Case "T_Abs".
    destruct IHHtyp as [T' Hctx]... exists T'.
    unfold extend in Hctx. 
    rewrite neq_id in Hctx...
  Case "T_Let".
    destruct IHHtyp2 as [T' Hctx]... exists T'.
    unfold extend in Hctx. 
    rewrite neq_id in Hctx...
  Case "T_Case".
    SCase "left".
      destruct IHHtyp2 as [T' Hctx]... exists T'. 
      unfold extend in Hctx. 
      rewrite neq_id in Hctx...
    SCase "right".
      destruct IHHtyp3 as [T' Hctx]... exists T'. 
      unfold extend in Hctx. 
      rewrite neq_id in Hctx...
  Case "T_Lcase".
    clear Htyp1 IHHtyp1 Htyp2 IHHtyp2.
    destruct IHHtyp3 as [T' Hctx]... exists T'.
    unfold extend in Hctx.
    rewrite neq_id in Hctx... rewrite neq_id in Hctx... 
Qed.

(* ###################################################################### *)
(** *** Substitution *)

Lemma substitution_preserves_typing : forall Gamma x U v t S,
     (extend Gamma x U) |- t \in S  ->
     empty |- v \in U   ->
     Gamma |- ([x:=v]t) \in S.
Proof with eauto.
  (* Theorem: If Gamma,x:U |- t : S and empty |- v : U, then 
     Gamma |- [x:=v]t : S. *)
  intros Gamma x U v t S Htypt Htypv. 
  generalize dependent Gamma. generalize dependent S.
  (* Proof: By induction on the term t.  Most cases follow directly
     from the IH, with the exception of tvar and tabs.
     The former aren't automatic because we must reason about how the
     variables interact. *)
  t_cases (induction t) Case;
    intros S Gamma Htypt; simpl; inversion Htypt; subst...
  Case "tvar".
    simpl. rename i into y.
    (* If t = y, we know that
         [empty |- v : U] and
         [Gamma,x:U |- y : S]
       and, by inversion, [extend Gamma x U y = Some S].  We want to
       show that [Gamma |- [x:=v]y : S].

       There are two cases to consider: either [x=y] or [x<>y]. *)
    destruct (eq_id_dec x y).
    SCase "x=y".
    (* If [x = y], then we know that [U = S], and that [[x:=v]y = v].
       So what we really must show is that if [empty |- v : U] then
       [Gamma |- v : U].  We have already proven a more general version
       of this theorem, called context invariance. *)
      subst.
      unfold extend in H1. rewrite eq_id in H1. 
      inversion H1; subst. clear H1.
      eapply context_invariance...
      intros x Hcontra.
      destruct (free_in_context _ _ S empty Hcontra) as [T' HT']...
      inversion HT'.
    SCase "x<>y".
    (* If [x <> y], then [Gamma y = Some S] and the substitution has no
       effect.  We can show that [Gamma |- y : S] by [T_Var]. *)
      apply T_Var... unfold extend in H1. rewrite neq_id in H1...
  Case "tabs".
    rename i into y. rename t into T11.
    (* If [t = tabs y T11 t0], then we know that
         [Gamma,x:U |- tabs y T11 t0 : T11->T12]
         [Gamma,x:U,y:T11 |- t0 : T12]
         [empty |- v : U]
       As our IH, we know that forall S Gamma, 
         [Gamma,x:U |- t0 : S -> Gamma |- [x:=v]t0 : S].
    
       We can calculate that 
         [x:=v]t = tabs y T11 (if beq_id x y then t0 else [x:=v]t0)
       And we must show that [Gamma |- [x:=v]t : T11->T12].  We know
       we will do so using [T_Abs], so it remains to be shown that:
         [Gamma,y:T11 |- if beq_id x y then t0 else [x:=v]t0 : T12]
       We consider two cases: [x = y] and [x <> y].
    *)
    apply T_Abs...
    destruct (eq_id_dec x y).
    SCase "x=y".
    (* If [x = y], then the substitution has no effect.  Context
       invariance shows that [Gamma,y:U,y:T11] and [Gamma,y:T11] are
       equivalent.  Since the former context shows that [t0 : T12], so
       does the latter. *)
      eapply context_invariance...
      subst.
      intros x Hafi. unfold extend.
      destruct (eq_id_dec y x)...
    SCase "x<>y".
    (* If [x <> y], then the IH and context invariance allow us to show that
         [Gamma,x:U,y:T11 |- t0 : T12]       =>
         [Gamma,y:T11,x:U |- t0 : T12]       =>
         [Gamma,y:T11 |- [x:=v]t0 : T12] *)
      apply IHt. eapply context_invariance...
      intros z Hafi. unfold extend.
      destruct (eq_id_dec y z)...
      subst. rewrite neq_id...
  Case "tlet".
    rename i into y.
    eapply T_Let...
    destruct (eq_id_dec x y).
    SCase "x=y".
      eapply context_invariance...
      subst.
      intros x Hafi. unfold extend.
      destruct (eq_id_dec y x)...
    SCase "x<>y".
      apply IHt2. eapply context_invariance...
      intros z Hafi. unfold extend.
      destruct (eq_id_dec y z)...
      subst. rewrite neq_id...
  Case "tcase".
    rename i into x1. rename i0 into x2.
    eapply T_Case...
      SCase "left arm".
       destruct (eq_id_dec x x1).
       SSCase "x = x1".
        eapply context_invariance...
        subst.
        intros z Hafi. unfold extend.
        destruct (eq_id_dec x1 z)...
       SSCase "x <> x1". 
         apply IHt2. eapply context_invariance...
         intros z Hafi.  unfold extend.
         destruct (eq_id_dec x1 z)...
           subst. rewrite neq_id...
      SCase "right arm".
       destruct (eq_id_dec x x2).
       SSCase "x = x2".
        eapply context_invariance...
        subst.
        intros z Hafi. unfold extend.
        destruct (eq_id_dec x2 z)...
       SSCase "x <> x2". 
         apply IHt3. eapply context_invariance...
         intros z Hafi.  unfold extend.
         destruct (eq_id_dec x2 z)...
           subst. rewrite neq_id...
  Case "tlcase".
    rename i into y1. rename i0 into y2.
    eapply T_Lcase... 
    destruct (eq_id_dec x y1).
    SCase "x=y1".
      simpl.  
      eapply context_invariance...
      subst.
      intros z Hafi. unfold extend.
      destruct (eq_id_dec y1 z)... 
    SCase "x<>y1".
      destruct (eq_id_dec x y2).
      SSCase "x=y2".
        eapply context_invariance...
        subst. 
        intros z Hafi. unfold extend.
        destruct (eq_id_dec y2 z)...
      SSCase "x<>y2".
        apply IHt3. eapply context_invariance...
        intros z Hafi. unfold extend.
        destruct (eq_id_dec y1 z)...
        subst. rewrite neq_id... 
        destruct (eq_id_dec y2 z)...
        subst. rewrite neq_id... 
Qed.

(* ###################################################################### *)
(** *** Preservation *)

Theorem preservation : forall t t' T,
     empty |- t \in T  ->
     t ==> t'  ->
     empty |- t' \in T.
Proof with eauto.
  intros t t' T HT.
  (* Theorem: If [empty |- t : T] and [t ==> t'], then [empty |- t' : T]. *)
  remember (@empty ty) as Gamma. generalize dependent HeqGamma.
  generalize dependent t'.
  (* Proof: By induction on the given typing derivation.  Many cases are
     contradictory ([T_Var], [T_Abs]).  We show just the interesting ones. *)
  has_type_cases (induction HT) Case; 
    intros t' HeqGamma HE; subst; inversion HE; subst...
  Case "T_App".
    (* If the last rule used was [T_App], then [t = t1 t2], and three rules
       could have been used to show [t ==> t']: [ST_App1], [ST_App2], and 
       [ST_AppAbs]. In the first two cases, the result follows directly from 
       the IH. *)
    inversion HE; subst...
    SCase "ST_AppAbs".
      (* For the third case, suppose 
           [t1 = tabs x T11 t12]
         and
           [t2 = v2].  
         We must show that [empty |- [x:=v2]t12 : T2]. 
         We know by assumption that
             [empty |- tabs x T11 t12 : T1->T2]
         and by inversion
             [x:T1 |- t12 : T2]
         We have already proven that substitution_preserves_typing and 
             [empty |- v2 : T1]
         by assumption, so we are done. *)
      apply substitution_preserves_typing with T1...
      inversion HT1...
  Case "T_App".
    inversion HT1...
  Case "T_Fst".
    inversion HT...
  Case "T_Snd".
    inversion HT...
  Case "T_Let".
    apply substitution_preserves_typing with T1...
  Case "T_Case".
    SCase "ST_CaseInl".
      inversion HT1; subst. 
      eapply substitution_preserves_typing...
    SCase "ST_CaseInr".
      inversion HT1; subst. 
      eapply substitution_preserves_typing...
  Case "T_Lcase".
    SCase "ST_LcaseCons".
      inversion HT1; subst.
      apply substitution_preserves_typing with (TList T1)...
      apply substitution_preserves_typing with T1...
Qed.
(** [] *)

Hint Extern 2 (has_type _ (tapp _ _) _) =>
  eapply T_App; auto.
Hint Extern 2 (has_type _ (tlcase _ _ _ _ _) _) =>
  eapply T_Lcase; auto.
Hint Extern 2 (_ = _) => compute; reflexivity.


(** Variables *)

Notation A := (Id 0).
Notation B := (Id 1).
Notation I := (Id 2).
Notation J := (Id 3).
Notation K := (Id 4).
Notation N := (Id 5).
Notation M := (Id 6).
Notation X := (Id 7).
Notation Y := (Id 8).
Notation Z := (Id 9).
Notation Halve := (Id 10).
Notation Loop := (Id 11).

Definition tloop : tm :=
  tfix (tabs Loop (TArrow TNat TNat) (tabs X TNat (
    tapp (tvar Loop) (tvar X)
  ))).

Example tloop_type:
  empty |- tloop \in TArrow TNat TNat.
Proof.
  unfold tloop; eauto 10.
Qed.

