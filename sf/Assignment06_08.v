Require Export Assignment06_07.

(* problem #08: 40 points *)

(** **** Exercise: 4 stars, advanced (pigeonhole principle)  *)
(** The "pigeonhole principle" states a basic fact about counting:
   if you distribute more than [n] items into [n] pigeonholes, some 
   pigeonhole must contain at least two items.  As is often the case,
   this apparently trivial fact about numbers requires non-trivial
   machinery to prove, but we now have enough... *)

(** First a pair of useful lemmas (we already proved these for lists
    of naturals, but not for arbitrary lists). *)

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2. 
Proof. 
  (* FILL IN HERE *)
  intros.
  induction l1 as [| h t IH].
  - simpl.
    reflexivity.
  - simpl.
    rewrite -> IH.
    reflexivity.
Qed.

Lemma appears_in_app_split : forall (X:Type) (x:X) (l:list X),
  appears_in x l -> 
  exists l1, exists l2, l = l1 ++ (x::l2).
Proof.
  (* FILL IN HERE *)
  intros.
  induction H.
  - exists nil. exists l.
    simpl.
    reflexivity.
  - destruct IHappears_in as [l1 [l2 eql]].
    exists (b::l1). exists l2.
    simpl.
    rewrite <- eql.
    reflexivity.
Qed.

(** Now define a predicate [repeats] (analogous to [no_repeats] in the
   exercise above), such that [repeats X l] asserts that [l] contains
   at least one repeated element (of type [X]).  *)

Inductive repeats {X:Type} : list X -> Prop :=
  (* FILL IN HERE *)
| rep_here : forall x l, appears_in x l -> repeats (x::l)
| rep_later : forall x l, repeats l -> repeats (x::l)
.

(** Now here's a way to formalize the pigeonhole principle. List [l2]
    represents a list of pigeonhole labels, and list [l1] represents
    the labels assigned to a list of items: if there are more items
    than labels, at least two items must have the same label.  This
    proof is much easier if you use the [excluded_middle] hypothesis
    to show that [appears_in] is decidable, i.e. [forall x
    l, (appears_in x l) \/ ~ (appears_in x l)].  However, it is also
    possible to make the proof go through _without_ assuming that
    [appears_in] is decidable; if you can manage to do this, you will
    not need the [excluded_middle] hypothesis. *)

Theorem pigeonhole_principle: forall (X:Type) (l1  l2:list X), 
   excluded_middle -> 
   (forall x, appears_in x l1 -> appears_in x l2) -> 
   length l2 < length l1 -> 
   repeats l1.  
Proof.
   intros X l1. induction l1 as [|x l1'].
   (* FILL IN HERE *)
   - intros.
     inversion H1.
   - intros.
     assert (em_aix: appears_in x l1' \/ ~ appears_in x l1').
     {
       apply H.
     }
     inversion em_aix.
     + apply rep_here.
       apply H2.
     + assert (aixl2 : appears_in x l2).
       {
         apply H0.
         apply ai_here.
       }
       apply appears_in_app_split in aixl2.
       destruct aixl2 as [l21 [l22 eql2]].
       apply rep_later.
       apply IHl1' with (l21 ++ l22).
       * apply H.
       * intros.
         assert (aixl1: appears_in x0 (x::l1')).
         {
           apply ai_later.
           apply H3.
         }
         apply H0 in aixl1.
         rewrite -> eql2 in aixl1.
         apply appears_in_app in aixl1.
         destruct aixl1 as [ail21 | ail22].
         {
           apply app_appears_in.
           left. apply ail21.
         }
         {
           apply app_appears_in.
           right.
           inversion ail22.
           - apply ex_falso_quodlibet.
             apply H2.
             rewrite <- H5.
             apply H3.
           - apply H5.
         }
       * rewrite -> app_length.
         rewrite -> eql2 in H1.
         simpl in H1.
         rewrite -> app_length in H1.
         simpl in H1.
         rewrite <- plus_n_Sm in H1.
         apply Sn_le_Sm__n_le_m.
         apply H1.
Qed.

