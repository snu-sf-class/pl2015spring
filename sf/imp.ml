type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type unit0 =
| Tt

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Pair of 'a * 'b

(** val fst : ('a1, 'a2) prod -> 'a1 **)

let fst = function
| Pair (x, y) -> x

(** val snd : ('a1, 'a2) prod -> 'a2 **)

let snd = function
| Pair (x, y) -> y

type 'a list =
| Nil
| Cons of 'a * 'a list

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | Nil -> m
  | Cons (a, l1) -> Cons (a, (app l1 m))

type comparison =
| Eq
| Lt
| Gt

type compareSpecT =
| CompEqT
| CompLtT
| CompGtT

(** val compareSpec2Type : comparison -> compareSpecT **)

let compareSpec2Type = function
| Eq -> CompEqT
| Lt -> CompLtT
| Gt -> CompGtT

type 'a compSpecT = compareSpecT

(** val compSpec2Type : 'a1 -> 'a1 -> comparison -> 'a1 compSpecT **)

let compSpec2Type x y c =
  compareSpec2Type c

type 'a sig0 =
  'a
  (* singleton inductive, whose constructor was exist *)

type 'a sumor =
| Inleft of 'a
| Inright

(** val plus : int -> int -> int **)

let rec plus = ( + )

(** val mult : int -> int -> int **)

let rec mult = ( * )

(** val minus : int -> int -> int **)

let rec minus n0 m =
  (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
    (fun _ ->
    n0)
    (fun k ->
    (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
      (fun _ ->
      n0)
      (fun l ->
      minus k l)
      m)
    n0

(** val nat_iter : int -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

let rec nat_iter n0 f x =
  (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
    (fun _ ->
    x)
    (fun n' ->
    f (nat_iter n' f x))
    n0

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

type reflect =
| ReflectT
| ReflectF

(** val iff_reflect : bool -> reflect **)

let iff_reflect = function
| true -> ReflectT
| false -> ReflectF

module Pos = 
 struct 
  type t = positive
  
  (** val succ : positive -> positive **)
  
  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH
  
  (** val add : positive -> positive -> positive **)
  
  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q -> XI (add p q)
       | XO q -> XO (add p q)
       | XH -> XI p)
    | XH ->
      (match y with
       | XI q -> XO (succ q)
       | XO q -> XI q
       | XH -> XO XH)
  
  (** val add_carry : positive -> positive -> positive **)
  
  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XI (add_carry p q)
       | XO q -> XO (add_carry p q)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q -> XI (succ q)
       | XO q -> XO (succ q)
       | XH -> XI XH)
  
  (** val pred_double : positive -> positive **)
  
  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH
  
  (** val pred : positive -> positive **)
  
  let pred = function
  | XI p -> XO p
  | XO p -> pred_double p
  | XH -> XH
  
  (** val pred_N : positive -> n **)
  
  let pred_N = function
  | XI p -> Npos (XO p)
  | XO p -> Npos (pred_double p)
  | XH -> N0
  
  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
  
  (** val mask_rect : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1 **)
  
  let mask_rect f f0 f1 = function
  | IsNul -> f
  | IsPos x -> f0 x
  | IsNeg -> f1
  
  (** val mask_rec : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1 **)
  
  let mask_rec f f0 f1 = function
  | IsNul -> f
  | IsPos x -> f0 x
  | IsNeg -> f1
  
  (** val succ_double_mask : mask -> mask **)
  
  let succ_double_mask = function
  | IsNul -> IsPos XH
  | IsPos p -> IsPos (XI p)
  | IsNeg -> IsNeg
  
  (** val double_mask : mask -> mask **)
  
  let double_mask = function
  | IsPos p -> IsPos (XO p)
  | x0 -> x0
  
  (** val double_pred_mask : positive -> mask **)
  
  let double_pred_mask = function
  | XI p -> IsPos (XO (XO p))
  | XO p -> IsPos (XO (pred_double p))
  | XH -> IsNul
  
  (** val pred_mask : mask -> mask **)
  
  let pred_mask = function
  | IsPos q ->
    (match q with
     | XH -> IsNul
     | _ -> IsPos (pred q))
  | _ -> IsNeg
  
  (** val sub_mask : positive -> positive -> mask **)
  
  let rec sub_mask x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double_mask (sub_mask p q)
       | XO q -> succ_double_mask (sub_mask p q)
       | XH -> IsPos (XO p))
    | XO p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XH ->
      (match y with
       | XH -> IsNul
       | _ -> IsNeg)
  
  (** val sub_mask_carry : positive -> positive -> mask **)
  
  and sub_mask_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XO p ->
      (match y with
       | XI q -> double_mask (sub_mask_carry p q)
       | XO q -> succ_double_mask (sub_mask_carry p q)
       | XH -> double_pred_mask p)
    | XH -> IsNeg
  
  (** val sub : positive -> positive -> positive **)
  
  let sub x y =
    match sub_mask x y with
    | IsPos z -> z
    | _ -> XH
  
  (** val mul : positive -> positive -> positive **)
  
  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y
  
  (** val iter : positive -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)
  
  let rec iter n0 f x =
    match n0 with
    | XI n' -> f (iter n' f (iter n' f x))
    | XO n' -> iter n' f (iter n' f x)
    | XH -> f x
  
  (** val pow : positive -> positive -> positive **)
  
  let pow x y =
    iter y (mul x) XH
  
  (** val square : positive -> positive **)
  
  let rec square = function
  | XI p0 -> XI (XO (add (square p0) p0))
  | XO p0 -> XO (XO (square p0))
  | XH -> XH
  
  (** val div2 : positive -> positive **)
  
  let div2 = function
  | XI p0 -> p0
  | XO p0 -> p0
  | XH -> XH
  
  (** val div2_up : positive -> positive **)
  
  let div2_up = function
  | XI p0 -> succ p0
  | XO p0 -> p0
  | XH -> XH
  
  (** val size_nat : positive -> int **)
  
  let rec size_nat = function
  | XI p0 -> (fun x -> x + 1) (size_nat p0)
  | XO p0 -> (fun x -> x + 1) (size_nat p0)
  | XH -> (fun x -> x + 1) 0
  
  (** val size : positive -> positive **)
  
  let rec size = function
  | XI p0 -> succ (size p0)
  | XO p0 -> succ (size p0)
  | XH -> XH
  
  (** val compare_cont : positive -> positive -> comparison -> comparison **)
  
  let rec compare_cont x y r =
    match x with
    | XI p ->
      (match y with
       | XI q -> compare_cont p q r
       | XO q -> compare_cont p q Gt
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q -> compare_cont p q Lt
       | XO q -> compare_cont p q r
       | XH -> Gt)
    | XH ->
      (match y with
       | XH -> r
       | _ -> Lt)
  
  (** val compare : positive -> positive -> comparison **)
  
  let compare x y =
    compare_cont x y Eq
  
  (** val min : positive -> positive -> positive **)
  
  let min p p' =
    match compare p p' with
    | Gt -> p'
    | _ -> p
  
  (** val max : positive -> positive -> positive **)
  
  let max p p' =
    match compare p p' with
    | Gt -> p
    | _ -> p'
  
  (** val eqb : positive -> positive -> bool **)
  
  let rec eqb p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> eqb p0 q0
       | _ -> false)
    | XO p0 ->
      (match q with
       | XO q0 -> eqb p0 q0
       | _ -> false)
    | XH ->
      (match q with
       | XH -> true
       | _ -> false)
  
  (** val leb : positive -> positive -> bool **)
  
  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true
  
  (** val ltb : positive -> positive -> bool **)
  
  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false
  
  (** val sqrtrem_step :
      (positive -> positive) -> (positive -> positive) -> (positive, mask)
      prod -> (positive, mask) prod **)
  
  let sqrtrem_step f g = function
  | Pair (s, y) ->
    (match y with
     | IsPos r ->
       let s' = XI (XO s) in
       let r' = g (f r) in
       if leb s' r'
       then Pair ((XI s), (sub_mask r' s'))
       else Pair ((XO s), (IsPos r'))
     | _ -> Pair ((XO s), (sub_mask (g (f XH)) (XO (XO XH)))))
  
  (** val sqrtrem : positive -> (positive, mask) prod **)
  
  let rec sqrtrem = function
  | XI p0 ->
    (match p0 with
     | XI p1 -> sqrtrem_step (fun x -> XI x) (fun x -> XI x) (sqrtrem p1)
     | XO p1 -> sqrtrem_step (fun x -> XO x) (fun x -> XI x) (sqrtrem p1)
     | XH -> Pair (XH, (IsPos (XO XH))))
  | XO p0 ->
    (match p0 with
     | XI p1 -> sqrtrem_step (fun x -> XI x) (fun x -> XO x) (sqrtrem p1)
     | XO p1 -> sqrtrem_step (fun x -> XO x) (fun x -> XO x) (sqrtrem p1)
     | XH -> Pair (XH, (IsPos XH)))
  | XH -> Pair (XH, IsNul)
  
  (** val sqrt : positive -> positive **)
  
  let sqrt p =
    fst (sqrtrem p)
  
  (** val gcdn : int -> positive -> positive -> positive **)
  
  let rec gcdn n0 a b =
    (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
      (fun _ ->
      XH)
      (fun n1 ->
      match a with
      | XI a' ->
        (match b with
         | XI b' ->
           (match compare a' b' with
            | Eq -> a
            | Lt -> gcdn n1 (sub b' a') a
            | Gt -> gcdn n1 (sub a' b') b)
         | XO b0 -> gcdn n1 a b0
         | XH -> XH)
      | XO a0 ->
        (match b with
         | XI p -> gcdn n1 a0 b
         | XO b0 -> XO (gcdn n1 a0 b0)
         | XH -> XH)
      | XH -> XH)
      n0
  
  (** val gcd : positive -> positive -> positive **)
  
  let gcd a b =
    gcdn (plus (size_nat a) (size_nat b)) a b
  
  (** val ggcdn :
      int -> positive -> positive -> (positive, (positive, positive) prod)
      prod **)
  
  let rec ggcdn n0 a b =
    (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
      (fun _ -> Pair (XH, (Pair (a,
      b))))
      (fun n1 ->
      match a with
      | XI a' ->
        (match b with
         | XI b' ->
           (match compare a' b' with
            | Eq -> Pair (a, (Pair (XH, XH)))
            | Lt ->
              let Pair (g, p) = ggcdn n1 (sub b' a') a in
              let Pair (ba, aa) = p in
              Pair (g, (Pair (aa, (add aa (XO ba)))))
            | Gt ->
              let Pair (g, p) = ggcdn n1 (sub a' b') b in
              let Pair (ab, bb) = p in
              Pair (g, (Pair ((add bb (XO ab)), bb))))
         | XO b0 ->
           let Pair (g, p) = ggcdn n1 a b0 in
           let Pair (aa, bb) = p in Pair (g, (Pair (aa, (XO bb))))
         | XH -> Pair (XH, (Pair (a, XH))))
      | XO a0 ->
        (match b with
         | XI p ->
           let Pair (g, p0) = ggcdn n1 a0 b in
           let Pair (aa, bb) = p0 in Pair (g, (Pair ((XO aa), bb)))
         | XO b0 -> let Pair (g, p) = ggcdn n1 a0 b0 in Pair ((XO g), p)
         | XH -> Pair (XH, (Pair (a, XH))))
      | XH -> Pair (XH, (Pair (XH, b))))
      n0
  
  (** val ggcd :
      positive -> positive -> (positive, (positive, positive) prod) prod **)
  
  let ggcd a b =
    ggcdn (plus (size_nat a) (size_nat b)) a b
  
  (** val coq_Nsucc_double : n -> n **)
  
  let coq_Nsucc_double = function
  | N0 -> Npos XH
  | Npos p -> Npos (XI p)
  
  (** val coq_Ndouble : n -> n **)
  
  let coq_Ndouble = function
  | N0 -> N0
  | Npos p -> Npos (XO p)
  
  (** val coq_lor : positive -> positive -> positive **)
  
  let rec coq_lor p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> XI (coq_lor p0 q0)
       | XO q0 -> XI (coq_lor p0 q0)
       | XH -> p)
    | XO p0 ->
      (match q with
       | XI q0 -> XI (coq_lor p0 q0)
       | XO q0 -> XO (coq_lor p0 q0)
       | XH -> XI p0)
    | XH ->
      (match q with
       | XO q0 -> XI q0
       | _ -> q)
  
  (** val coq_land : positive -> positive -> n **)
  
  let rec coq_land p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Nsucc_double (coq_land p0 q0)
       | XO q0 -> coq_Ndouble (coq_land p0 q0)
       | XH -> Npos XH)
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (coq_land p0 q0)
       | XO q0 -> coq_Ndouble (coq_land p0 q0)
       | XH -> N0)
    | XH ->
      (match q with
       | XO q0 -> N0
       | _ -> Npos XH)
  
  (** val ldiff : positive -> positive -> n **)
  
  let rec ldiff p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (ldiff p0 q0)
       | XO q0 -> coq_Nsucc_double (ldiff p0 q0)
       | XH -> Npos (XO p0))
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (ldiff p0 q0)
       | XO q0 -> coq_Ndouble (ldiff p0 q0)
       | XH -> Npos p)
    | XH ->
      (match q with
       | XO q0 -> Npos XH
       | _ -> N0)
  
  (** val coq_lxor : positive -> positive -> n **)
  
  let rec coq_lxor p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (coq_lxor p0 q0)
       | XO q0 -> coq_Nsucc_double (coq_lxor p0 q0)
       | XH -> Npos (XO p0))
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Nsucc_double (coq_lxor p0 q0)
       | XO q0 -> coq_Ndouble (coq_lxor p0 q0)
       | XH -> Npos (XI p0))
    | XH ->
      (match q with
       | XI q0 -> Npos (XO q0)
       | XO q0 -> Npos (XI q0)
       | XH -> N0)
  
  (** val shiftl_nat : positive -> int -> positive **)
  
  let shiftl_nat p n0 =
    nat_iter n0 (fun x -> XO x) p
  
  (** val shiftr_nat : positive -> int -> positive **)
  
  let shiftr_nat p n0 =
    nat_iter n0 div2 p
  
  (** val shiftl : positive -> n -> positive **)
  
  let shiftl p = function
  | N0 -> p
  | Npos n1 -> iter n1 (fun x -> XO x) p
  
  (** val shiftr : positive -> n -> positive **)
  
  let shiftr p = function
  | N0 -> p
  | Npos n1 -> iter n1 div2 p
  
  (** val testbit_nat : positive -> int -> bool **)
  
  let rec testbit_nat p n0 =
    match p with
    | XI p0 ->
      ((fun zero succ n ->
      if n=0 then zero () else succ (n-1))
         (fun _ ->
         true)
         (fun n' ->
         testbit_nat p0 n')
         n0)
    | XO p0 ->
      ((fun zero succ n ->
      if n=0 then zero () else succ (n-1))
         (fun _ ->
         false)
         (fun n' ->
         testbit_nat p0 n')
         n0)
    | XH ->
      ((fun zero succ n ->
      if n=0 then zero () else succ (n-1))
         (fun _ ->
         true)
         (fun n1 ->
         false)
         n0)
  
  (** val testbit : positive -> n -> bool **)
  
  let rec testbit p n0 =
    match p with
    | XI p0 ->
      (match n0 with
       | N0 -> true
       | Npos n1 -> testbit p0 (pred_N n1))
    | XO p0 ->
      (match n0 with
       | N0 -> false
       | Npos n1 -> testbit p0 (pred_N n1))
    | XH ->
      (match n0 with
       | N0 -> true
       | Npos p0 -> false)
  
  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)
  
  let rec iter_op op p a =
    match p with
    | XI p0 -> op a (iter_op op p0 (op a a))
    | XO p0 -> iter_op op p0 (op a a)
    | XH -> a
  
  (** val to_nat : positive -> int **)
  
  let to_nat x =
    iter_op plus x ((fun x -> x + 1) 0)
  
  (** val of_nat : int -> positive **)
  
  let rec of_nat n0 =
    (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
      (fun _ ->
      XH)
      (fun x ->
      (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
        (fun _ ->
        XH)
        (fun n1 ->
        succ (of_nat x))
        x)
      n0
  
  (** val of_succ_nat : int -> positive **)
  
  let rec of_succ_nat n0 =
    (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
      (fun _ ->
      XH)
      (fun x ->
      succ (of_succ_nat x))
      n0
 end

module Coq_Pos = 
 struct 
  type t = positive
  
  (** val succ : positive -> positive **)
  
  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH
  
  (** val add : positive -> positive -> positive **)
  
  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q -> XI (add p q)
       | XO q -> XO (add p q)
       | XH -> XI p)
    | XH ->
      (match y with
       | XI q -> XO (succ q)
       | XO q -> XI q
       | XH -> XO XH)
  
  (** val add_carry : positive -> positive -> positive **)
  
  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XI (add_carry p q)
       | XO q -> XO (add_carry p q)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q -> XI (succ q)
       | XO q -> XO (succ q)
       | XH -> XI XH)
  
  (** val pred_double : positive -> positive **)
  
  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH
  
  (** val pred : positive -> positive **)
  
  let pred = function
  | XI p -> XO p
  | XO p -> pred_double p
  | XH -> XH
  
  (** val pred_N : positive -> n **)
  
  let pred_N = function
  | XI p -> Npos (XO p)
  | XO p -> Npos (pred_double p)
  | XH -> N0
  
  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg
  
  (** val mask_rect : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1 **)
  
  let mask_rect f f0 f1 = function
  | IsNul -> f
  | IsPos x -> f0 x
  | IsNeg -> f1
  
  (** val mask_rec : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1 **)
  
  let mask_rec f f0 f1 = function
  | IsNul -> f
  | IsPos x -> f0 x
  | IsNeg -> f1
  
  (** val succ_double_mask : mask -> mask **)
  
  let succ_double_mask = function
  | IsNul -> IsPos XH
  | IsPos p -> IsPos (XI p)
  | IsNeg -> IsNeg
  
  (** val double_mask : mask -> mask **)
  
  let double_mask = function
  | IsPos p -> IsPos (XO p)
  | x0 -> x0
  
  (** val double_pred_mask : positive -> mask **)
  
  let double_pred_mask = function
  | XI p -> IsPos (XO (XO p))
  | XO p -> IsPos (XO (pred_double p))
  | XH -> IsNul
  
  (** val pred_mask : mask -> mask **)
  
  let pred_mask = function
  | IsPos q ->
    (match q with
     | XH -> IsNul
     | _ -> IsPos (pred q))
  | _ -> IsNeg
  
  (** val sub_mask : positive -> positive -> mask **)
  
  let rec sub_mask x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double_mask (sub_mask p q)
       | XO q -> succ_double_mask (sub_mask p q)
       | XH -> IsPos (XO p))
    | XO p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XH ->
      (match y with
       | XH -> IsNul
       | _ -> IsNeg)
  
  (** val sub_mask_carry : positive -> positive -> mask **)
  
  and sub_mask_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XO p ->
      (match y with
       | XI q -> double_mask (sub_mask_carry p q)
       | XO q -> succ_double_mask (sub_mask_carry p q)
       | XH -> double_pred_mask p)
    | XH -> IsNeg
  
  (** val sub : positive -> positive -> positive **)
  
  let sub x y =
    match sub_mask x y with
    | IsPos z -> z
    | _ -> XH
  
  (** val mul : positive -> positive -> positive **)
  
  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y
  
  (** val iter : positive -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)
  
  let rec iter n0 f x =
    match n0 with
    | XI n' -> f (iter n' f (iter n' f x))
    | XO n' -> iter n' f (iter n' f x)
    | XH -> f x
  
  (** val pow : positive -> positive -> positive **)
  
  let pow x y =
    iter y (mul x) XH
  
  (** val square : positive -> positive **)
  
  let rec square = function
  | XI p0 -> XI (XO (add (square p0) p0))
  | XO p0 -> XO (XO (square p0))
  | XH -> XH
  
  (** val div2 : positive -> positive **)
  
  let div2 = function
  | XI p0 -> p0
  | XO p0 -> p0
  | XH -> XH
  
  (** val div2_up : positive -> positive **)
  
  let div2_up = function
  | XI p0 -> succ p0
  | XO p0 -> p0
  | XH -> XH
  
  (** val size_nat : positive -> int **)
  
  let rec size_nat = function
  | XI p0 -> (fun x -> x + 1) (size_nat p0)
  | XO p0 -> (fun x -> x + 1) (size_nat p0)
  | XH -> (fun x -> x + 1) 0
  
  (** val size : positive -> positive **)
  
  let rec size = function
  | XI p0 -> succ (size p0)
  | XO p0 -> succ (size p0)
  | XH -> XH
  
  (** val compare_cont : positive -> positive -> comparison -> comparison **)
  
  let rec compare_cont x y r =
    match x with
    | XI p ->
      (match y with
       | XI q -> compare_cont p q r
       | XO q -> compare_cont p q Gt
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q -> compare_cont p q Lt
       | XO q -> compare_cont p q r
       | XH -> Gt)
    | XH ->
      (match y with
       | XH -> r
       | _ -> Lt)
  
  (** val compare : positive -> positive -> comparison **)
  
  let compare x y =
    compare_cont x y Eq
  
  (** val min : positive -> positive -> positive **)
  
  let min p p' =
    match compare p p' with
    | Gt -> p'
    | _ -> p
  
  (** val max : positive -> positive -> positive **)
  
  let max p p' =
    match compare p p' with
    | Gt -> p
    | _ -> p'
  
  (** val eqb : positive -> positive -> bool **)
  
  let rec eqb p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> eqb p0 q0
       | _ -> false)
    | XO p0 ->
      (match q with
       | XO q0 -> eqb p0 q0
       | _ -> false)
    | XH ->
      (match q with
       | XH -> true
       | _ -> false)
  
  (** val leb : positive -> positive -> bool **)
  
  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true
  
  (** val ltb : positive -> positive -> bool **)
  
  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false
  
  (** val sqrtrem_step :
      (positive -> positive) -> (positive -> positive) -> (positive, mask)
      prod -> (positive, mask) prod **)
  
  let sqrtrem_step f g = function
  | Pair (s, y) ->
    (match y with
     | IsPos r ->
       let s' = XI (XO s) in
       let r' = g (f r) in
       if leb s' r'
       then Pair ((XI s), (sub_mask r' s'))
       else Pair ((XO s), (IsPos r'))
     | _ -> Pair ((XO s), (sub_mask (g (f XH)) (XO (XO XH)))))
  
  (** val sqrtrem : positive -> (positive, mask) prod **)
  
  let rec sqrtrem = function
  | XI p0 ->
    (match p0 with
     | XI p1 -> sqrtrem_step (fun x -> XI x) (fun x -> XI x) (sqrtrem p1)
     | XO p1 -> sqrtrem_step (fun x -> XO x) (fun x -> XI x) (sqrtrem p1)
     | XH -> Pair (XH, (IsPos (XO XH))))
  | XO p0 ->
    (match p0 with
     | XI p1 -> sqrtrem_step (fun x -> XI x) (fun x -> XO x) (sqrtrem p1)
     | XO p1 -> sqrtrem_step (fun x -> XO x) (fun x -> XO x) (sqrtrem p1)
     | XH -> Pair (XH, (IsPos XH)))
  | XH -> Pair (XH, IsNul)
  
  (** val sqrt : positive -> positive **)
  
  let sqrt p =
    fst (sqrtrem p)
  
  (** val gcdn : int -> positive -> positive -> positive **)
  
  let rec gcdn n0 a b =
    (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
      (fun _ ->
      XH)
      (fun n1 ->
      match a with
      | XI a' ->
        (match b with
         | XI b' ->
           (match compare a' b' with
            | Eq -> a
            | Lt -> gcdn n1 (sub b' a') a
            | Gt -> gcdn n1 (sub a' b') b)
         | XO b0 -> gcdn n1 a b0
         | XH -> XH)
      | XO a0 ->
        (match b with
         | XI p -> gcdn n1 a0 b
         | XO b0 -> XO (gcdn n1 a0 b0)
         | XH -> XH)
      | XH -> XH)
      n0
  
  (** val gcd : positive -> positive -> positive **)
  
  let gcd a b =
    gcdn (plus (size_nat a) (size_nat b)) a b
  
  (** val ggcdn :
      int -> positive -> positive -> (positive, (positive, positive) prod)
      prod **)
  
  let rec ggcdn n0 a b =
    (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
      (fun _ -> Pair (XH, (Pair (a,
      b))))
      (fun n1 ->
      match a with
      | XI a' ->
        (match b with
         | XI b' ->
           (match compare a' b' with
            | Eq -> Pair (a, (Pair (XH, XH)))
            | Lt ->
              let Pair (g, p) = ggcdn n1 (sub b' a') a in
              let Pair (ba, aa) = p in
              Pair (g, (Pair (aa, (add aa (XO ba)))))
            | Gt ->
              let Pair (g, p) = ggcdn n1 (sub a' b') b in
              let Pair (ab, bb) = p in
              Pair (g, (Pair ((add bb (XO ab)), bb))))
         | XO b0 ->
           let Pair (g, p) = ggcdn n1 a b0 in
           let Pair (aa, bb) = p in Pair (g, (Pair (aa, (XO bb))))
         | XH -> Pair (XH, (Pair (a, XH))))
      | XO a0 ->
        (match b with
         | XI p ->
           let Pair (g, p0) = ggcdn n1 a0 b in
           let Pair (aa, bb) = p0 in Pair (g, (Pair ((XO aa), bb)))
         | XO b0 -> let Pair (g, p) = ggcdn n1 a0 b0 in Pair ((XO g), p)
         | XH -> Pair (XH, (Pair (a, XH))))
      | XH -> Pair (XH, (Pair (XH, b))))
      n0
  
  (** val ggcd :
      positive -> positive -> (positive, (positive, positive) prod) prod **)
  
  let ggcd a b =
    ggcdn (plus (size_nat a) (size_nat b)) a b
  
  (** val coq_Nsucc_double : n -> n **)
  
  let coq_Nsucc_double = function
  | N0 -> Npos XH
  | Npos p -> Npos (XI p)
  
  (** val coq_Ndouble : n -> n **)
  
  let coq_Ndouble = function
  | N0 -> N0
  | Npos p -> Npos (XO p)
  
  (** val coq_lor : positive -> positive -> positive **)
  
  let rec coq_lor p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> XI (coq_lor p0 q0)
       | XO q0 -> XI (coq_lor p0 q0)
       | XH -> p)
    | XO p0 ->
      (match q with
       | XI q0 -> XI (coq_lor p0 q0)
       | XO q0 -> XO (coq_lor p0 q0)
       | XH -> XI p0)
    | XH ->
      (match q with
       | XO q0 -> XI q0
       | _ -> q)
  
  (** val coq_land : positive -> positive -> n **)
  
  let rec coq_land p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Nsucc_double (coq_land p0 q0)
       | XO q0 -> coq_Ndouble (coq_land p0 q0)
       | XH -> Npos XH)
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (coq_land p0 q0)
       | XO q0 -> coq_Ndouble (coq_land p0 q0)
       | XH -> N0)
    | XH ->
      (match q with
       | XO q0 -> N0
       | _ -> Npos XH)
  
  (** val ldiff : positive -> positive -> n **)
  
  let rec ldiff p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (ldiff p0 q0)
       | XO q0 -> coq_Nsucc_double (ldiff p0 q0)
       | XH -> Npos (XO p0))
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (ldiff p0 q0)
       | XO q0 -> coq_Ndouble (ldiff p0 q0)
       | XH -> Npos p)
    | XH ->
      (match q with
       | XO q0 -> Npos XH
       | _ -> N0)
  
  (** val coq_lxor : positive -> positive -> n **)
  
  let rec coq_lxor p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (coq_lxor p0 q0)
       | XO q0 -> coq_Nsucc_double (coq_lxor p0 q0)
       | XH -> Npos (XO p0))
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Nsucc_double (coq_lxor p0 q0)
       | XO q0 -> coq_Ndouble (coq_lxor p0 q0)
       | XH -> Npos (XI p0))
    | XH ->
      (match q with
       | XI q0 -> Npos (XO q0)
       | XO q0 -> Npos (XI q0)
       | XH -> N0)
  
  (** val shiftl_nat : positive -> int -> positive **)
  
  let shiftl_nat p n0 =
    nat_iter n0 (fun x -> XO x) p
  
  (** val shiftr_nat : positive -> int -> positive **)
  
  let shiftr_nat p n0 =
    nat_iter n0 div2 p
  
  (** val shiftl : positive -> n -> positive **)
  
  let shiftl p = function
  | N0 -> p
  | Npos n1 -> iter n1 (fun x -> XO x) p
  
  (** val shiftr : positive -> n -> positive **)
  
  let shiftr p = function
  | N0 -> p
  | Npos n1 -> iter n1 div2 p
  
  (** val testbit_nat : positive -> int -> bool **)
  
  let rec testbit_nat p n0 =
    match p with
    | XI p0 ->
      ((fun zero succ n ->
      if n=0 then zero () else succ (n-1))
         (fun _ ->
         true)
         (fun n' ->
         testbit_nat p0 n')
         n0)
    | XO p0 ->
      ((fun zero succ n ->
      if n=0 then zero () else succ (n-1))
         (fun _ ->
         false)
         (fun n' ->
         testbit_nat p0 n')
         n0)
    | XH ->
      ((fun zero succ n ->
      if n=0 then zero () else succ (n-1))
         (fun _ ->
         true)
         (fun n1 ->
         false)
         n0)
  
  (** val testbit : positive -> n -> bool **)
  
  let rec testbit p n0 =
    match p with
    | XI p0 ->
      (match n0 with
       | N0 -> true
       | Npos n1 -> testbit p0 (pred_N n1))
    | XO p0 ->
      (match n0 with
       | N0 -> false
       | Npos n1 -> testbit p0 (pred_N n1))
    | XH ->
      (match n0 with
       | N0 -> true
       | Npos p0 -> false)
  
  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)
  
  let rec iter_op op p a =
    match p with
    | XI p0 -> op a (iter_op op p0 (op a a))
    | XO p0 -> iter_op op p0 (op a a)
    | XH -> a
  
  (** val to_nat : positive -> int **)
  
  let to_nat x =
    iter_op plus x ((fun x -> x + 1) 0)
  
  (** val of_nat : int -> positive **)
  
  let rec of_nat n0 =
    (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
      (fun _ ->
      XH)
      (fun x ->
      (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
        (fun _ ->
        XH)
        (fun n1 ->
        succ (of_nat x))
        x)
      n0
  
  (** val of_succ_nat : int -> positive **)
  
  let rec of_succ_nat n0 =
    (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
      (fun _ ->
      XH)
      (fun x ->
      succ (of_succ_nat x))
      n0
  
  (** val eq_dec : positive -> positive -> bool **)
  
  let rec eq_dec p y0 =
    match p with
    | XI p0 ->
      (match y0 with
       | XI p1 -> eq_dec p0 p1
       | _ -> false)
    | XO p0 ->
      (match y0 with
       | XO p1 -> eq_dec p0 p1
       | _ -> false)
    | XH ->
      (match y0 with
       | XH -> true
       | _ -> false)
  
  (** val peano_rect : 'a1 -> (positive -> 'a1 -> 'a1) -> positive -> 'a1 **)
  
  let rec peano_rect a f p =
    let f2 = peano_rect (f XH a) (fun p0 x -> f (succ (XO p0)) (f (XO p0) x))
    in
    (match p with
     | XI q -> f (XO q) (f2 q)
     | XO q -> f2 q
     | XH -> a)
  
  (** val peano_rec : 'a1 -> (positive -> 'a1 -> 'a1) -> positive -> 'a1 **)
  
  let peano_rec =
    peano_rect
  
  type coq_PeanoView =
  | PeanoOne
  | PeanoSucc of positive * coq_PeanoView
  
  (** val coq_PeanoView_rect :
      'a1 -> (positive -> coq_PeanoView -> 'a1 -> 'a1) -> positive ->
      coq_PeanoView -> 'a1 **)
  
  let rec coq_PeanoView_rect f f0 p = function
  | PeanoOne -> f
  | PeanoSucc (p1, p2) -> f0 p1 p2 (coq_PeanoView_rect f f0 p1 p2)
  
  (** val coq_PeanoView_rec :
      'a1 -> (positive -> coq_PeanoView -> 'a1 -> 'a1) -> positive ->
      coq_PeanoView -> 'a1 **)
  
  let rec coq_PeanoView_rec f f0 p = function
  | PeanoOne -> f
  | PeanoSucc (p1, p2) -> f0 p1 p2 (coq_PeanoView_rec f f0 p1 p2)
  
  (** val peanoView_xO : positive -> coq_PeanoView -> coq_PeanoView **)
  
  let rec peanoView_xO p = function
  | PeanoOne -> PeanoSucc (XH, PeanoOne)
  | PeanoSucc (p0, q0) ->
    PeanoSucc ((succ (XO p0)), (PeanoSucc ((XO p0), (peanoView_xO p0 q0))))
  
  (** val peanoView_xI : positive -> coq_PeanoView -> coq_PeanoView **)
  
  let rec peanoView_xI p = function
  | PeanoOne -> PeanoSucc ((succ XH), (PeanoSucc (XH, PeanoOne)))
  | PeanoSucc (p0, q0) ->
    PeanoSucc ((succ (XI p0)), (PeanoSucc ((XI p0), (peanoView_xI p0 q0))))
  
  (** val peanoView : positive -> coq_PeanoView **)
  
  let rec peanoView = function
  | XI p0 -> peanoView_xI p0 (peanoView p0)
  | XO p0 -> peanoView_xO p0 (peanoView p0)
  | XH -> PeanoOne
  
  (** val coq_PeanoView_iter :
      'a1 -> (positive -> 'a1 -> 'a1) -> positive -> coq_PeanoView -> 'a1 **)
  
  let rec coq_PeanoView_iter a f p = function
  | PeanoOne -> a
  | PeanoSucc (p0, q0) -> f p0 (coq_PeanoView_iter a f p0 q0)
  
  (** val eqb_spec : positive -> positive -> reflect **)
  
  let eqb_spec x y =
    iff_reflect (eqb x y)
  
  (** val switch_Eq : comparison -> comparison -> comparison **)
  
  let switch_Eq c = function
  | Eq -> c
  | x -> x
  
  (** val mask2cmp : mask -> comparison **)
  
  let mask2cmp = function
  | IsNul -> Eq
  | IsPos p0 -> Gt
  | IsNeg -> Lt
  
  (** val leb_spec0 : positive -> positive -> reflect **)
  
  let leb_spec0 x y =
    iff_reflect (leb x y)
  
  (** val ltb_spec0 : positive -> positive -> reflect **)
  
  let ltb_spec0 x y =
    iff_reflect (ltb x y)
  
  module Private_Tac = 
   struct 
    
   end
  
  module Private_Dec = 
   struct 
    (** val max_case_strong :
        positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1) ->
        (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
    
    let max_case_strong n0 m compat hl hr =
      let c = compSpec2Type n0 m (compare n0 m) in
      (match c with
       | CompGtT -> compat n0 (max n0 m) __ (hl __)
       | _ -> compat m (max n0 m) __ (hr __))
    
    (** val max_case :
        positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1) ->
        'a1 -> 'a1 -> 'a1 **)
    
    let max_case n0 m x x0 x1 =
      max_case_strong n0 m x (fun _ -> x0) (fun _ -> x1)
    
    (** val max_dec : positive -> positive -> bool **)
    
    let max_dec n0 m =
      max_case n0 m (fun x y _ h0 -> h0) true false
    
    (** val min_case_strong :
        positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1) ->
        (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
    
    let min_case_strong n0 m compat hl hr =
      let c = compSpec2Type n0 m (compare n0 m) in
      (match c with
       | CompGtT -> compat m (min n0 m) __ (hr __)
       | _ -> compat n0 (min n0 m) __ (hl __))
    
    (** val min_case :
        positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1) ->
        'a1 -> 'a1 -> 'a1 **)
    
    let min_case n0 m x x0 x1 =
      min_case_strong n0 m x (fun _ -> x0) (fun _ -> x1)
    
    (** val min_dec : positive -> positive -> bool **)
    
    let min_dec n0 m =
      min_case n0 m (fun x y _ h0 -> h0) true false
   end
  
  (** val max_case_strong :
      positive -> positive -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
  
  let max_case_strong n0 m x x0 =
    Private_Dec.max_case_strong n0 m (fun x1 y _ x2 -> x2) x x0
  
  (** val max_case : positive -> positive -> 'a1 -> 'a1 -> 'a1 **)
  
  let max_case n0 m x x0 =
    max_case_strong n0 m (fun _ -> x) (fun _ -> x0)
  
  (** val max_dec : positive -> positive -> bool **)
  
  let max_dec =
    Private_Dec.max_dec
  
  (** val min_case_strong :
      positive -> positive -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
  
  let min_case_strong n0 m x x0 =
    Private_Dec.min_case_strong n0 m (fun x1 y _ x2 -> x2) x x0
  
  (** val min_case : positive -> positive -> 'a1 -> 'a1 -> 'a1 **)
  
  let min_case n0 m x x0 =
    min_case_strong n0 m (fun _ -> x) (fun _ -> x0)
  
  (** val min_dec : positive -> positive -> bool **)
  
  let min_dec =
    Private_Dec.min_dec
 end

module N = 
 struct 
  type t = n
  
  (** val zero : n **)
  
  let zero =
    N0
  
  (** val one : n **)
  
  let one =
    Npos XH
  
  (** val two : n **)
  
  let two =
    Npos (XO XH)
  
  (** val succ_double : n -> n **)
  
  let succ_double = function
  | N0 -> Npos XH
  | Npos p -> Npos (XI p)
  
  (** val double : n -> n **)
  
  let double = function
  | N0 -> N0
  | Npos p -> Npos (XO p)
  
  (** val succ : n -> n **)
  
  let succ = function
  | N0 -> Npos XH
  | Npos p -> Npos (Coq_Pos.succ p)
  
  (** val pred : n -> n **)
  
  let pred = function
  | N0 -> N0
  | Npos p -> Coq_Pos.pred_N p
  
  (** val succ_pos : n -> positive **)
  
  let succ_pos = function
  | N0 -> XH
  | Npos p -> Coq_Pos.succ p
  
  (** val add : n -> n -> n **)
  
  let add n0 m =
    match n0 with
    | N0 -> m
    | Npos p ->
      (match m with
       | N0 -> n0
       | Npos q -> Npos (Coq_Pos.add p q))
  
  (** val sub : n -> n -> n **)
  
  let sub n0 m =
    match n0 with
    | N0 -> N0
    | Npos n' ->
      (match m with
       | N0 -> n0
       | Npos m' ->
         (match Coq_Pos.sub_mask n' m' with
          | Coq_Pos.IsPos p -> Npos p
          | _ -> N0))
  
  (** val mul : n -> n -> n **)
  
  let mul n0 m =
    match n0 with
    | N0 -> N0
    | Npos p ->
      (match m with
       | N0 -> N0
       | Npos q -> Npos (Coq_Pos.mul p q))
  
  (** val compare : n -> n -> comparison **)
  
  let compare n0 m =
    match n0 with
    | N0 ->
      (match m with
       | N0 -> Eq
       | Npos m' -> Lt)
    | Npos n' ->
      (match m with
       | N0 -> Gt
       | Npos m' -> Coq_Pos.compare n' m')
  
  (** val eqb : n -> n -> bool **)
  
  let rec eqb n0 m =
    match n0 with
    | N0 ->
      (match m with
       | N0 -> true
       | Npos p -> false)
    | Npos p ->
      (match m with
       | N0 -> false
       | Npos q -> Coq_Pos.eqb p q)
  
  (** val leb : n -> n -> bool **)
  
  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true
  
  (** val ltb : n -> n -> bool **)
  
  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false
  
  (** val min : n -> n -> n **)
  
  let min n0 n' =
    match compare n0 n' with
    | Gt -> n'
    | _ -> n0
  
  (** val max : n -> n -> n **)
  
  let max n0 n' =
    match compare n0 n' with
    | Gt -> n0
    | _ -> n'
  
  (** val div2 : n -> n **)
  
  let div2 = function
  | N0 -> N0
  | Npos p0 ->
    (match p0 with
     | XI p -> Npos p
     | XO p -> Npos p
     | XH -> N0)
  
  (** val even : n -> bool **)
  
  let even = function
  | N0 -> true
  | Npos p ->
    (match p with
     | XO p0 -> true
     | _ -> false)
  
  (** val odd : n -> bool **)
  
  let odd n0 =
    negb (even n0)
  
  (** val pow : n -> n -> n **)
  
  let pow n0 = function
  | N0 -> Npos XH
  | Npos p0 ->
    (match n0 with
     | N0 -> N0
     | Npos q -> Npos (Coq_Pos.pow q p0))
  
  (** val square : n -> n **)
  
  let square = function
  | N0 -> N0
  | Npos p -> Npos (Coq_Pos.square p)
  
  (** val log2 : n -> n **)
  
  let log2 = function
  | N0 -> N0
  | Npos p0 ->
    (match p0 with
     | XI p -> Npos (Coq_Pos.size p)
     | XO p -> Npos (Coq_Pos.size p)
     | XH -> N0)
  
  (** val size : n -> n **)
  
  let size = function
  | N0 -> N0
  | Npos p -> Npos (Coq_Pos.size p)
  
  (** val size_nat : n -> int **)
  
  let size_nat = function
  | N0 -> 0
  | Npos p -> Coq_Pos.size_nat p
  
  (** val pos_div_eucl : positive -> n -> (n, n) prod **)
  
  let rec pos_div_eucl a b =
    match a with
    | XI a' ->
      let Pair (q, r) = pos_div_eucl a' b in
      let r' = succ_double r in
      if leb b r'
      then Pair ((succ_double q), (sub r' b))
      else Pair ((double q), r')
    | XO a' ->
      let Pair (q, r) = pos_div_eucl a' b in
      let r' = double r in
      if leb b r'
      then Pair ((succ_double q), (sub r' b))
      else Pair ((double q), r')
    | XH ->
      (match b with
       | N0 -> Pair (N0, (Npos XH))
       | Npos p ->
         (match p with
          | XH -> Pair ((Npos XH), N0)
          | _ -> Pair (N0, (Npos XH))))
  
  (** val div_eucl : n -> n -> (n, n) prod **)
  
  let div_eucl a b =
    match a with
    | N0 -> Pair (N0, N0)
    | Npos na ->
      (match b with
       | N0 -> Pair (N0, a)
       | Npos p -> pos_div_eucl na b)
  
  (** val div : n -> n -> n **)
  
  let div a b =
    fst (div_eucl a b)
  
  (** val modulo : n -> n -> n **)
  
  let modulo a b =
    snd (div_eucl a b)
  
  (** val gcd : n -> n -> n **)
  
  let gcd a b =
    match a with
    | N0 -> b
    | Npos p ->
      (match b with
       | N0 -> a
       | Npos q -> Npos (Coq_Pos.gcd p q))
  
  (** val ggcd : n -> n -> (n, (n, n) prod) prod **)
  
  let ggcd a b =
    match a with
    | N0 -> Pair (b, (Pair (N0, (Npos XH))))
    | Npos p ->
      (match b with
       | N0 -> Pair (a, (Pair ((Npos XH), N0)))
       | Npos q ->
         let Pair (g, p0) = Coq_Pos.ggcd p q in
         let Pair (aa, bb) = p0 in
         Pair ((Npos g), (Pair ((Npos aa), (Npos bb)))))
  
  (** val sqrtrem : n -> (n, n) prod **)
  
  let sqrtrem = function
  | N0 -> Pair (N0, N0)
  | Npos p ->
    let Pair (s, m) = Coq_Pos.sqrtrem p in
    (match m with
     | Coq_Pos.IsPos r -> Pair ((Npos s), (Npos r))
     | _ -> Pair ((Npos s), N0))
  
  (** val sqrt : n -> n **)
  
  let sqrt = function
  | N0 -> N0
  | Npos p -> Npos (Coq_Pos.sqrt p)
  
  (** val coq_lor : n -> n -> n **)
  
  let coq_lor n0 m =
    match n0 with
    | N0 -> m
    | Npos p ->
      (match m with
       | N0 -> n0
       | Npos q -> Npos (Coq_Pos.coq_lor p q))
  
  (** val coq_land : n -> n -> n **)
  
  let coq_land n0 m =
    match n0 with
    | N0 -> N0
    | Npos p ->
      (match m with
       | N0 -> N0
       | Npos q -> Coq_Pos.coq_land p q)
  
  (** val ldiff : n -> n -> n **)
  
  let rec ldiff n0 m =
    match n0 with
    | N0 -> N0
    | Npos p ->
      (match m with
       | N0 -> n0
       | Npos q -> Coq_Pos.ldiff p q)
  
  (** val coq_lxor : n -> n -> n **)
  
  let coq_lxor n0 m =
    match n0 with
    | N0 -> m
    | Npos p ->
      (match m with
       | N0 -> n0
       | Npos q -> Coq_Pos.coq_lxor p q)
  
  (** val shiftl_nat : n -> int -> n **)
  
  let shiftl_nat a n0 =
    nat_iter n0 double a
  
  (** val shiftr_nat : n -> int -> n **)
  
  let shiftr_nat a n0 =
    nat_iter n0 div2 a
  
  (** val shiftl : n -> n -> n **)
  
  let shiftl a n0 =
    match a with
    | N0 -> N0
    | Npos a0 -> Npos (Coq_Pos.shiftl a0 n0)
  
  (** val shiftr : n -> n -> n **)
  
  let shiftr a = function
  | N0 -> a
  | Npos p -> Coq_Pos.iter p div2 a
  
  (** val testbit_nat : n -> int -> bool **)
  
  let testbit_nat = function
  | N0 -> (fun x -> false)
  | Npos p -> Coq_Pos.testbit_nat p
  
  (** val testbit : n -> n -> bool **)
  
  let testbit a n0 =
    match a with
    | N0 -> false
    | Npos p -> Coq_Pos.testbit p n0
  
  (** val to_nat : n -> int **)
  
  let to_nat = function
  | N0 -> 0
  | Npos p -> Coq_Pos.to_nat p
  
  (** val of_nat : int -> n **)
  
  let of_nat n0 =
    (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
      (fun _ ->
      N0)
      (fun n' -> Npos
      (Coq_Pos.of_succ_nat n'))
      n0
  
  (** val iter : n -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)
  
  let iter n0 f x =
    match n0 with
    | N0 -> x
    | Npos p -> Coq_Pos.iter p f x
  
  (** val eq_dec : n -> n -> bool **)
  
  let eq_dec n0 m =
    match n0 with
    | N0 ->
      (match m with
       | N0 -> true
       | Npos p -> false)
    | Npos x ->
      (match m with
       | N0 -> false
       | Npos p0 -> Coq_Pos.eq_dec x p0)
  
  (** val discr : n -> positive sumor **)
  
  let discr = function
  | N0 -> Inright
  | Npos p -> Inleft p
  
  (** val binary_rect :
      'a1 -> (n -> 'a1 -> 'a1) -> (n -> 'a1 -> 'a1) -> n -> 'a1 **)
  
  let binary_rect f0 f2 fS2 n0 =
    let f2' = fun p -> f2 (Npos p) in
    let fS2' = fun p -> fS2 (Npos p) in
    (match n0 with
     | N0 -> f0
     | Npos p ->
       let rec f = function
       | XI p1 -> fS2' p1 (f p1)
       | XO p1 -> f2' p1 (f p1)
       | XH -> fS2 N0 f0
       in f p)
  
  (** val binary_rec :
      'a1 -> (n -> 'a1 -> 'a1) -> (n -> 'a1 -> 'a1) -> n -> 'a1 **)
  
  let binary_rec =
    binary_rect
  
  (** val peano_rect : 'a1 -> (n -> 'a1 -> 'a1) -> n -> 'a1 **)
  
  let peano_rect f0 f n0 =
    let f' = fun p -> f (Npos p) in
    (match n0 with
     | N0 -> f0
     | Npos p -> Coq_Pos.peano_rect (f N0 f0) f' p)
  
  (** val peano_rec : 'a1 -> (n -> 'a1 -> 'a1) -> n -> 'a1 **)
  
  let peano_rec =
    peano_rect
  
  (** val leb_spec0 : n -> n -> reflect **)
  
  let leb_spec0 x y =
    iff_reflect (leb x y)
  
  (** val ltb_spec0 : n -> n -> reflect **)
  
  let ltb_spec0 x y =
    iff_reflect (ltb x y)
  
  module Private_BootStrap = 
   struct 
    
   end
  
  (** val recursion : 'a1 -> (n -> 'a1 -> 'a1) -> n -> 'a1 **)
  
  let recursion x =
    peano_rect x
  
  module Private_OrderTac = 
   struct 
    module IsTotal = 
     struct 
      
     end
    
    module Tac = 
     struct 
      
     end
   end
  
  module Private_NZPow = 
   struct 
    
   end
  
  module Private_NZSqrt = 
   struct 
    
   end
  
  (** val sqrt_up : n -> n **)
  
  let sqrt_up a =
    match compare N0 a with
    | Lt -> succ (sqrt (pred a))
    | _ -> N0
  
  (** val log2_up : n -> n **)
  
  let log2_up a =
    match compare (Npos XH) a with
    | Lt -> succ (log2 (pred a))
    | _ -> N0
  
  module Private_NZDiv = 
   struct 
    
   end
  
  (** val lcm : n -> n -> n **)
  
  let lcm a b =
    mul a (div b (gcd a b))
  
  (** val eqb_spec : n -> n -> reflect **)
  
  let eqb_spec x y =
    iff_reflect (eqb x y)
  
  (** val b2n : bool -> n **)
  
  let b2n = function
  | true -> Npos XH
  | false -> N0
  
  (** val setbit : n -> n -> n **)
  
  let setbit a n0 =
    coq_lor a (shiftl (Npos XH) n0)
  
  (** val clearbit : n -> n -> n **)
  
  let clearbit a n0 =
    ldiff a (shiftl (Npos XH) n0)
  
  (** val ones : n -> n **)
  
  let ones n0 =
    pred (shiftl (Npos XH) n0)
  
  (** val lnot : n -> n -> n **)
  
  let lnot a n0 =
    coq_lxor a (ones n0)
  
  module Private_Tac = 
   struct 
    
   end
  
  module Private_Dec = 
   struct 
    (** val max_case_strong :
        n -> n -> (n -> n -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1)
        -> 'a1 **)
    
    let max_case_strong n0 m compat hl hr =
      let c = compSpec2Type n0 m (compare n0 m) in
      (match c with
       | CompGtT -> compat n0 (max n0 m) __ (hl __)
       | _ -> compat m (max n0 m) __ (hr __))
    
    (** val max_case :
        n -> n -> (n -> n -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)
    
    let max_case n0 m x x0 x1 =
      max_case_strong n0 m x (fun _ -> x0) (fun _ -> x1)
    
    (** val max_dec : n -> n -> bool **)
    
    let max_dec n0 m =
      max_case n0 m (fun x y _ h0 -> h0) true false
    
    (** val min_case_strong :
        n -> n -> (n -> n -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1)
        -> 'a1 **)
    
    let min_case_strong n0 m compat hl hr =
      let c = compSpec2Type n0 m (compare n0 m) in
      (match c with
       | CompGtT -> compat m (min n0 m) __ (hr __)
       | _ -> compat n0 (min n0 m) __ (hl __))
    
    (** val min_case :
        n -> n -> (n -> n -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)
    
    let min_case n0 m x x0 x1 =
      min_case_strong n0 m x (fun _ -> x0) (fun _ -> x1)
    
    (** val min_dec : n -> n -> bool **)
    
    let min_dec n0 m =
      min_case n0 m (fun x y _ h0 -> h0) true false
   end
  
  (** val max_case_strong : n -> n -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
  
  let max_case_strong n0 m x x0 =
    Private_Dec.max_case_strong n0 m (fun x1 y _ x2 -> x2) x x0
  
  (** val max_case : n -> n -> 'a1 -> 'a1 -> 'a1 **)
  
  let max_case n0 m x x0 =
    max_case_strong n0 m (fun _ -> x) (fun _ -> x0)
  
  (** val max_dec : n -> n -> bool **)
  
  let max_dec =
    Private_Dec.max_dec
  
  (** val min_case_strong : n -> n -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
  
  let min_case_strong n0 m x x0 =
    Private_Dec.min_case_strong n0 m (fun x1 y _ x2 -> x2) x x0
  
  (** val min_case : n -> n -> 'a1 -> 'a1 -> 'a1 **)
  
  let min_case n0 m x x0 =
    min_case_strong n0 m (fun _ -> x) (fun _ -> x0)
  
  (** val min_dec : n -> n -> bool **)
  
  let min_dec =
    Private_Dec.min_dec
 end

(** val eq_nat_dec : int -> int -> bool **)

let rec eq_nat_dec n0 m =
  (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
    (fun _ ->
    (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
      (fun _ ->
      true)
      (fun m0 ->
      false)
      m)
    (fun n1 ->
    (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
      (fun _ ->
      false)
      (fun m0 ->
      eq_nat_dec n1 m0)
      m)
    n0

(** val beq_nat : int -> int -> bool **)

let rec beq_nat = ( = )

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = function
| Nil -> Nil
| Cons (x, l') -> app (rev l') (Cons (x, Nil))

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| Nil -> Nil
| Cons (a, t0) -> Cons ((f a), (map f t0))

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l a0 =
  match l with
  | Nil -> a0
  | Cons (b, t0) -> fold_left f t0 (f a0 b)

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| Nil -> a0
| Cons (b, t0) -> f b (fold_right f a0 t0)

(** val forallb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec forallb f = function
| Nil -> true
| Cons (a, l0) -> if f a then forallb f l0 else false

(** val n_of_digits : bool list -> n **)

let rec n_of_digits = function
| Nil -> N0
| Cons (b, l') ->
  N.add (if b then Npos XH else N0) (N.mul (Npos (XO XH)) (n_of_digits l'))

(** val n_of_ascii : char -> n **)

let n_of_ascii a =
  (* If this appears, you're using Ascii internals. Please don't *) (fun f c -> let n = Char.code c in let h i = (n land (1 lsl i)) <> 0 in f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
    (fun a0 a1 a2 a3 a4 a5 a6 a7 ->
    n_of_digits (Cons (a0, (Cons (a1, (Cons (a2, (Cons (a3, (Cons (a4, (Cons
      (a5, (Cons (a6, (Cons (a7, Nil)))))))))))))))))
    a

(** val nat_of_ascii : char -> int **)

let nat_of_ascii a =
  N.to_nat (n_of_ascii a)

type string =
| EmptyString
| String of char * string

(** val string_dec : string -> string -> bool **)

let rec string_dec s s0 =
  match s with
  | EmptyString ->
    (match s0 with
     | EmptyString -> true
     | String (a, s1) -> false)
  | String (a, s1) ->
    (match s0 with
     | EmptyString -> false
     | String (a0, s2) -> if (=) a a0 then string_dec s1 s2 else false)

(** val append : string -> string -> string **)

let rec append s1 s2 =
  match s1 with
  | EmptyString -> s2
  | String (c, s1') -> String (c, (append s1' s2))

(** val ble_nat : int -> int -> bool **)

let rec ble_nat n0 m =
  (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
    (fun _ ->
    true)
    (fun n' ->
    (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
      (fun _ ->
      false)
      (fun m' ->
      ble_nat n' m')
      m)
    n0

type id =
  int
  (* singleton inductive, whose constructor was Id *)

(** val eq_id_dec : id -> id -> bool **)

let eq_id_dec id1 id2 =
  eq_nat_dec id1 id2

type state = id -> int

(** val empty_state : state **)

let empty_state x =
  0

(** val update : state -> id -> int -> state **)

let update st x n0 x' =
  if eq_id_dec x x' then n0 else st x'

type aexp =
| ANum of int
| AId of id
| APlus of aexp * aexp
| AMinus of aexp * aexp
| AMult of aexp * aexp

type bexp =
| BTrue
| BFalse
| BEq of aexp * aexp
| BLe of aexp * aexp
| BNot of bexp
| BAnd of bexp * bexp

(** val aeval : state -> aexp -> int **)

let rec aeval st = function
| ANum n0 -> n0
| AId x -> st x
| APlus (a1, a2) -> plus (aeval st a1) (aeval st a2)
| AMinus (a1, a2) -> minus (aeval st a1) (aeval st a2)
| AMult (a1, a2) -> mult (aeval st a1) (aeval st a2)

(** val beval : state -> bexp -> bool **)

let rec beval st = function
| BTrue -> true
| BFalse -> false
| BEq (a1, a2) -> beq_nat (aeval st a1) (aeval st a2)
| BLe (a1, a2) -> ble_nat (aeval st a1) (aeval st a2)
| BNot b1 -> negb (beval st b1)
| BAnd (b1, b2) -> if beval st b1 then beval st b2 else false

type com =
| CSkip
| CAss of id * aexp
| CSeq of com * com
| CIf of bexp * com * com
| CWhile of bexp * com

(** val ceval_step : state -> com -> int -> state option **)

let rec ceval_step st c i =
  (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
    (fun _ ->
    None)
    (fun i' ->
    match c with
    | CSkip -> Some st
    | CAss (l, a1) -> Some (update st l (aeval st a1))
    | CSeq (c1, c2) ->
      (match ceval_step st c1 i' with
       | Some st' -> ceval_step st' c2 i'
       | None -> None)
    | CIf (b, c1, c2) ->
      if beval st b then ceval_step st c1 i' else ceval_step st c2 i'
    | CWhile (b1, c1) ->
      if beval st b1
      then (match ceval_step st c1 i' with
            | Some st' -> ceval_step st' c i'
            | None -> None)
      else Some st)
    i

(** val isWhite : char -> bool **)

let isWhite c =
  let n0 = nat_of_ascii c in
  if if beq_nat n0 ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
          ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
          ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
          ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
          ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
          ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
          ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
          ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
          ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
          ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
          ((fun x -> x + 1) ((fun x -> x + 1)
          0))))))))))))))))))))))))))))))))
     then true
     else beq_nat n0 ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) 0)))))))))
  then true
  else if beq_nat n0 ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) 0))))))))))
       then true
       else beq_nat n0 ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
              ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
              ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
              ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
              ((fun x -> x + 1) 0)))))))))))))

(** val isLowerAlpha : char -> bool **)

let isLowerAlpha c =
  let n0 = nat_of_ascii c in
  if ble_nat ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
       ((fun x -> x + 1)
       0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
       n0
  then ble_nat n0 ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1)
         0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  else false

(** val isAlpha : char -> bool **)

let isAlpha c =
  let n0 = nat_of_ascii c in
  if if ble_nat ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
          ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
          ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
          ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
          ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
          ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
          ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
          ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
          ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
          ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
          ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
          ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
          ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
          ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
          ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
          ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
          ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
          ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
          ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
          ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
          ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
          ((fun x -> x + 1) ((fun x -> x + 1)
          0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
          n0
     then ble_nat n0 ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
     else false
  then true
  else if ble_nat ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
            ((fun x -> x + 1)
            0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
            n0
       then ble_nat n0 ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
              ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
              ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
              ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
              ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
              ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
              ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
              ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
              ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
              ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
              ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
              ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
              ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
              ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
              ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
              ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
              ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
              ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
              ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
              ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
              ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
              ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
              ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
              ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
              ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
              ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
              ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
              ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
              ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
              ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
              ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
              ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
              ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
              ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
              ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
              ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
              ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
              ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
              ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
              ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
              ((fun x -> x + 1) ((fun x -> x + 1)
              0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
       else false

(** val isDigit : char -> bool **)

let isDigit c =
  let n0 = nat_of_ascii c in
  if ble_nat ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
       0)))))))))))))))))))))))))))))))))))))))))))))))) n0
  then ble_nat n0 ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  else false

type chartype =
| White
| Alpha
| Digit
| Other

(** val classifyChar : char -> chartype **)

let classifyChar c =
  if isWhite c
  then White
  else if isAlpha c then Alpha else if isDigit c then Digit else Other

(** val list_of_string : string -> char list **)

let rec list_of_string = function
| EmptyString -> Nil
| String (c, s0) -> Cons (c, (list_of_string s0))

(** val string_of_list : char list -> string **)

let rec string_of_list xs =
  fold_right (fun x x0 -> String (x, x0)) EmptyString xs

type token = string

(** val tokenize_helper :
    chartype -> char list -> char list -> char list list **)

let rec tokenize_helper cls acc xs =
  let tk =
    match acc with
    | Nil -> Nil
    | Cons (a, l) -> Cons ((rev acc), Nil)
  in
  (match xs with
   | Nil -> tk
   | Cons (x, xs') ->
     (match cls with
      | White ->
        (match classifyChar x with
         | White ->
           (* If this appears, you're using Ascii internals. Please don't *) (fun f c -> let n = Char.code c in let h i = (n land (1 lsl i)) <> 0 in f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
             (fun b b0 b1 b2 b3 b4 b5 b6 ->
             if b
             then if b0
                  then app tk (tokenize_helper White Nil xs')
                  else if b1
                       then app tk (tokenize_helper White Nil xs')
                       else if b2
                            then if b3
                                 then app tk (tokenize_helper White Nil xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper White Nil
                                                    xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper White
                                                         Nil xs')
                                                else app tk (Cons ((Cons
                                                       (')', Nil)),
                                                       (tokenize_helper Other
                                                         Nil xs')))
                                      else app tk
                                             (tokenize_helper White Nil xs')
                            else app tk (tokenize_helper White Nil xs')
             else if b0
                  then app tk (tokenize_helper White Nil xs')
                  else if b1
                       then app tk (tokenize_helper White Nil xs')
                       else if b2
                            then if b3
                                 then app tk (tokenize_helper White Nil xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper White Nil
                                                    xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper White
                                                         Nil xs')
                                                else app tk (Cons ((Cons
                                                       ('(', Nil)),
                                                       (tokenize_helper Other
                                                         Nil xs')))
                                      else app tk
                                             (tokenize_helper White Nil xs')
                            else app tk (tokenize_helper White Nil xs'))
             x
         | Other ->
           let tp = Other in
           (* If this appears, you're using Ascii internals. Please don't *) (fun f c -> let n = Char.code c in let h i = (n land (1 lsl i)) <> 0 in f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
             (fun b b0 b1 b2 b3 b4 b5 b6 ->
             if b
             then if b0
                  then app tk (tokenize_helper tp (Cons (x, Nil)) xs')
                  else if b1
                       then app tk (tokenize_helper tp (Cons (x, Nil)) xs')
                       else if b2
                            then if b3
                                 then app tk
                                        (tokenize_helper tp (Cons (x, Nil))
                                          xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper tp (Cons
                                                    (x, Nil)) xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper tp
                                                         (Cons (x, Nil)) xs')
                                                else app tk (Cons ((Cons
                                                       (')', Nil)),
                                                       (tokenize_helper Other
                                                         Nil xs')))
                                      else app tk
                                             (tokenize_helper tp (Cons (x,
                                               Nil)) xs')
                            else app tk
                                   (tokenize_helper tp (Cons (x, Nil)) xs')
             else if b0
                  then app tk (tokenize_helper tp (Cons (x, Nil)) xs')
                  else if b1
                       then app tk (tokenize_helper tp (Cons (x, Nil)) xs')
                       else if b2
                            then if b3
                                 then app tk
                                        (tokenize_helper tp (Cons (x, Nil))
                                          xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper tp (Cons
                                                    (x, Nil)) xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper tp
                                                         (Cons (x, Nil)) xs')
                                                else app tk (Cons ((Cons
                                                       ('(', Nil)),
                                                       (tokenize_helper Other
                                                         Nil xs')))
                                      else app tk
                                             (tokenize_helper tp (Cons (x,
                                               Nil)) xs')
                            else app tk
                                   (tokenize_helper tp (Cons (x, Nil)) xs'))
             x
         | x0 ->
           (* If this appears, you're using Ascii internals. Please don't *) (fun f c -> let n = Char.code c in let h i = (n land (1 lsl i)) <> 0 in f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
             (fun b b0 b1 b2 b3 b4 b5 b6 ->
             if b
             then if b0
                  then app tk (tokenize_helper x0 (Cons (x, Nil)) xs')
                  else if b1
                       then app tk (tokenize_helper x0 (Cons (x, Nil)) xs')
                       else if b2
                            then if b3
                                 then app tk
                                        (tokenize_helper x0 (Cons (x, Nil))
                                          xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper x0 (Cons
                                                    (x, Nil)) xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper x0
                                                         (Cons (x, Nil)) xs')
                                                else app tk (Cons ((Cons
                                                       (')', Nil)),
                                                       (tokenize_helper Other
                                                         Nil xs')))
                                      else app tk
                                             (tokenize_helper x0 (Cons (x,
                                               Nil)) xs')
                            else app tk
                                   (tokenize_helper x0 (Cons (x, Nil)) xs')
             else if b0
                  then app tk (tokenize_helper x0 (Cons (x, Nil)) xs')
                  else if b1
                       then app tk (tokenize_helper x0 (Cons (x, Nil)) xs')
                       else if b2
                            then if b3
                                 then app tk
                                        (tokenize_helper x0 (Cons (x, Nil))
                                          xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper x0 (Cons
                                                    (x, Nil)) xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper x0
                                                         (Cons (x, Nil)) xs')
                                                else app tk (Cons ((Cons
                                                       ('(', Nil)),
                                                       (tokenize_helper Other
                                                         Nil xs')))
                                      else app tk
                                             (tokenize_helper x0 (Cons (x,
                                               Nil)) xs')
                            else app tk
                                   (tokenize_helper x0 (Cons (x, Nil)) xs'))
             x)
      | Alpha ->
        (match classifyChar x with
         | White ->
           (* If this appears, you're using Ascii internals. Please don't *) (fun f c -> let n = Char.code c in let h i = (n land (1 lsl i)) <> 0 in f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
             (fun b b0 b1 b2 b3 b4 b5 b6 ->
             if b
             then if b0
                  then app tk (tokenize_helper White Nil xs')
                  else if b1
                       then app tk (tokenize_helper White Nil xs')
                       else if b2
                            then if b3
                                 then app tk (tokenize_helper White Nil xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper White Nil
                                                    xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper White
                                                         Nil xs')
                                                else app tk (Cons ((Cons
                                                       (')', Nil)),
                                                       (tokenize_helper Other
                                                         Nil xs')))
                                      else app tk
                                             (tokenize_helper White Nil xs')
                            else app tk (tokenize_helper White Nil xs')
             else if b0
                  then app tk (tokenize_helper White Nil xs')
                  else if b1
                       then app tk (tokenize_helper White Nil xs')
                       else if b2
                            then if b3
                                 then app tk (tokenize_helper White Nil xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper White Nil
                                                    xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper White
                                                         Nil xs')
                                                else app tk (Cons ((Cons
                                                       ('(', Nil)),
                                                       (tokenize_helper Other
                                                         Nil xs')))
                                      else app tk
                                             (tokenize_helper White Nil xs')
                            else app tk (tokenize_helper White Nil xs'))
             x
         | Alpha ->
           (* If this appears, you're using Ascii internals. Please don't *) (fun f c -> let n = Char.code c in let h i = (n land (1 lsl i)) <> 0 in f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
             (fun b b0 b1 b2 b3 b4 b5 b6 ->
             if b
             then if b0
                  then tokenize_helper Alpha (Cons (x, acc)) xs'
                  else if b1
                       then tokenize_helper Alpha (Cons (x, acc)) xs'
                       else if b2
                            then if b3
                                 then tokenize_helper Alpha (Cons (x, acc))
                                        xs'
                                 else if b4
                                      then if b5
                                           then tokenize_helper Alpha (Cons
                                                  (x, acc)) xs'
                                           else if b6
                                                then tokenize_helper Alpha
                                                       (Cons (x, acc)) xs'
                                                else app tk (Cons ((Cons
                                                       (')', Nil)),
                                                       (tokenize_helper Other
                                                         Nil xs')))
                                      else tokenize_helper Alpha (Cons (x,
                                             acc)) xs'
                            else tokenize_helper Alpha (Cons (x, acc)) xs'
             else if b0
                  then tokenize_helper Alpha (Cons (x, acc)) xs'
                  else if b1
                       then tokenize_helper Alpha (Cons (x, acc)) xs'
                       else if b2
                            then if b3
                                 then tokenize_helper Alpha (Cons (x, acc))
                                        xs'
                                 else if b4
                                      then if b5
                                           then tokenize_helper Alpha (Cons
                                                  (x, acc)) xs'
                                           else if b6
                                                then tokenize_helper Alpha
                                                       (Cons (x, acc)) xs'
                                                else app tk (Cons ((Cons
                                                       ('(', Nil)),
                                                       (tokenize_helper Other
                                                         Nil xs')))
                                      else tokenize_helper Alpha (Cons (x,
                                             acc)) xs'
                            else tokenize_helper Alpha (Cons (x, acc)) xs')
             x
         | Digit ->
           let tp = Digit in
           (* If this appears, you're using Ascii internals. Please don't *) (fun f c -> let n = Char.code c in let h i = (n land (1 lsl i)) <> 0 in f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
             (fun b b0 b1 b2 b3 b4 b5 b6 ->
             if b
             then if b0
                  then app tk (tokenize_helper tp (Cons (x, Nil)) xs')
                  else if b1
                       then app tk (tokenize_helper tp (Cons (x, Nil)) xs')
                       else if b2
                            then if b3
                                 then app tk
                                        (tokenize_helper tp (Cons (x, Nil))
                                          xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper tp (Cons
                                                    (x, Nil)) xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper tp
                                                         (Cons (x, Nil)) xs')
                                                else app tk (Cons ((Cons
                                                       (')', Nil)),
                                                       (tokenize_helper Other
                                                         Nil xs')))
                                      else app tk
                                             (tokenize_helper tp (Cons (x,
                                               Nil)) xs')
                            else app tk
                                   (tokenize_helper tp (Cons (x, Nil)) xs')
             else if b0
                  then app tk (tokenize_helper tp (Cons (x, Nil)) xs')
                  else if b1
                       then app tk (tokenize_helper tp (Cons (x, Nil)) xs')
                       else if b2
                            then if b3
                                 then app tk
                                        (tokenize_helper tp (Cons (x, Nil))
                                          xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper tp (Cons
                                                    (x, Nil)) xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper tp
                                                         (Cons (x, Nil)) xs')
                                                else app tk (Cons ((Cons
                                                       ('(', Nil)),
                                                       (tokenize_helper Other
                                                         Nil xs')))
                                      else app tk
                                             (tokenize_helper tp (Cons (x,
                                               Nil)) xs')
                            else app tk
                                   (tokenize_helper tp (Cons (x, Nil)) xs'))
             x
         | Other ->
           let tp = Other in
           (* If this appears, you're using Ascii internals. Please don't *) (fun f c -> let n = Char.code c in let h i = (n land (1 lsl i)) <> 0 in f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
             (fun b b0 b1 b2 b3 b4 b5 b6 ->
             if b
             then if b0
                  then app tk (tokenize_helper tp (Cons (x, Nil)) xs')
                  else if b1
                       then app tk (tokenize_helper tp (Cons (x, Nil)) xs')
                       else if b2
                            then if b3
                                 then app tk
                                        (tokenize_helper tp (Cons (x, Nil))
                                          xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper tp (Cons
                                                    (x, Nil)) xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper tp
                                                         (Cons (x, Nil)) xs')
                                                else app tk (Cons ((Cons
                                                       (')', Nil)),
                                                       (tokenize_helper Other
                                                         Nil xs')))
                                      else app tk
                                             (tokenize_helper tp (Cons (x,
                                               Nil)) xs')
                            else app tk
                                   (tokenize_helper tp (Cons (x, Nil)) xs')
             else if b0
                  then app tk (tokenize_helper tp (Cons (x, Nil)) xs')
                  else if b1
                       then app tk (tokenize_helper tp (Cons (x, Nil)) xs')
                       else if b2
                            then if b3
                                 then app tk
                                        (tokenize_helper tp (Cons (x, Nil))
                                          xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper tp (Cons
                                                    (x, Nil)) xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper tp
                                                         (Cons (x, Nil)) xs')
                                                else app tk (Cons ((Cons
                                                       ('(', Nil)),
                                                       (tokenize_helper Other
                                                         Nil xs')))
                                      else app tk
                                             (tokenize_helper tp (Cons (x,
                                               Nil)) xs')
                            else app tk
                                   (tokenize_helper tp (Cons (x, Nil)) xs'))
             x)
      | Digit ->
        (match classifyChar x with
         | White ->
           (* If this appears, you're using Ascii internals. Please don't *) (fun f c -> let n = Char.code c in let h i = (n land (1 lsl i)) <> 0 in f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
             (fun b b0 b1 b2 b3 b4 b5 b6 ->
             if b
             then if b0
                  then app tk (tokenize_helper White Nil xs')
                  else if b1
                       then app tk (tokenize_helper White Nil xs')
                       else if b2
                            then if b3
                                 then app tk (tokenize_helper White Nil xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper White Nil
                                                    xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper White
                                                         Nil xs')
                                                else app tk (Cons ((Cons
                                                       (')', Nil)),
                                                       (tokenize_helper Other
                                                         Nil xs')))
                                      else app tk
                                             (tokenize_helper White Nil xs')
                            else app tk (tokenize_helper White Nil xs')
             else if b0
                  then app tk (tokenize_helper White Nil xs')
                  else if b1
                       then app tk (tokenize_helper White Nil xs')
                       else if b2
                            then if b3
                                 then app tk (tokenize_helper White Nil xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper White Nil
                                                    xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper White
                                                         Nil xs')
                                                else app tk (Cons ((Cons
                                                       ('(', Nil)),
                                                       (tokenize_helper Other
                                                         Nil xs')))
                                      else app tk
                                             (tokenize_helper White Nil xs')
                            else app tk (tokenize_helper White Nil xs'))
             x
         | Alpha ->
           let tp = Alpha in
           (* If this appears, you're using Ascii internals. Please don't *) (fun f c -> let n = Char.code c in let h i = (n land (1 lsl i)) <> 0 in f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
             (fun b b0 b1 b2 b3 b4 b5 b6 ->
             if b
             then if b0
                  then app tk (tokenize_helper tp (Cons (x, Nil)) xs')
                  else if b1
                       then app tk (tokenize_helper tp (Cons (x, Nil)) xs')
                       else if b2
                            then if b3
                                 then app tk
                                        (tokenize_helper tp (Cons (x, Nil))
                                          xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper tp (Cons
                                                    (x, Nil)) xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper tp
                                                         (Cons (x, Nil)) xs')
                                                else app tk (Cons ((Cons
                                                       (')', Nil)),
                                                       (tokenize_helper Other
                                                         Nil xs')))
                                      else app tk
                                             (tokenize_helper tp (Cons (x,
                                               Nil)) xs')
                            else app tk
                                   (tokenize_helper tp (Cons (x, Nil)) xs')
             else if b0
                  then app tk (tokenize_helper tp (Cons (x, Nil)) xs')
                  else if b1
                       then app tk (tokenize_helper tp (Cons (x, Nil)) xs')
                       else if b2
                            then if b3
                                 then app tk
                                        (tokenize_helper tp (Cons (x, Nil))
                                          xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper tp (Cons
                                                    (x, Nil)) xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper tp
                                                         (Cons (x, Nil)) xs')
                                                else app tk (Cons ((Cons
                                                       ('(', Nil)),
                                                       (tokenize_helper Other
                                                         Nil xs')))
                                      else app tk
                                             (tokenize_helper tp (Cons (x,
                                               Nil)) xs')
                            else app tk
                                   (tokenize_helper tp (Cons (x, Nil)) xs'))
             x
         | Digit ->
           (* If this appears, you're using Ascii internals. Please don't *) (fun f c -> let n = Char.code c in let h i = (n land (1 lsl i)) <> 0 in f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
             (fun b b0 b1 b2 b3 b4 b5 b6 ->
             if b
             then if b0
                  then tokenize_helper Digit (Cons (x, acc)) xs'
                  else if b1
                       then tokenize_helper Digit (Cons (x, acc)) xs'
                       else if b2
                            then if b3
                                 then tokenize_helper Digit (Cons (x, acc))
                                        xs'
                                 else if b4
                                      then if b5
                                           then tokenize_helper Digit (Cons
                                                  (x, acc)) xs'
                                           else if b6
                                                then tokenize_helper Digit
                                                       (Cons (x, acc)) xs'
                                                else app tk (Cons ((Cons
                                                       (')', Nil)),
                                                       (tokenize_helper Other
                                                         Nil xs')))
                                      else tokenize_helper Digit (Cons (x,
                                             acc)) xs'
                            else tokenize_helper Digit (Cons (x, acc)) xs'
             else if b0
                  then tokenize_helper Digit (Cons (x, acc)) xs'
                  else if b1
                       then tokenize_helper Digit (Cons (x, acc)) xs'
                       else if b2
                            then if b3
                                 then tokenize_helper Digit (Cons (x, acc))
                                        xs'
                                 else if b4
                                      then if b5
                                           then tokenize_helper Digit (Cons
                                                  (x, acc)) xs'
                                           else if b6
                                                then tokenize_helper Digit
                                                       (Cons (x, acc)) xs'
                                                else app tk (Cons ((Cons
                                                       ('(', Nil)),
                                                       (tokenize_helper Other
                                                         Nil xs')))
                                      else tokenize_helper Digit (Cons (x,
                                             acc)) xs'
                            else tokenize_helper Digit (Cons (x, acc)) xs')
             x
         | Other ->
           let tp = Other in
           (* If this appears, you're using Ascii internals. Please don't *) (fun f c -> let n = Char.code c in let h i = (n land (1 lsl i)) <> 0 in f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
             (fun b b0 b1 b2 b3 b4 b5 b6 ->
             if b
             then if b0
                  then app tk (tokenize_helper tp (Cons (x, Nil)) xs')
                  else if b1
                       then app tk (tokenize_helper tp (Cons (x, Nil)) xs')
                       else if b2
                            then if b3
                                 then app tk
                                        (tokenize_helper tp (Cons (x, Nil))
                                          xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper tp (Cons
                                                    (x, Nil)) xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper tp
                                                         (Cons (x, Nil)) xs')
                                                else app tk (Cons ((Cons
                                                       (')', Nil)),
                                                       (tokenize_helper Other
                                                         Nil xs')))
                                      else app tk
                                             (tokenize_helper tp (Cons (x,
                                               Nil)) xs')
                            else app tk
                                   (tokenize_helper tp (Cons (x, Nil)) xs')
             else if b0
                  then app tk (tokenize_helper tp (Cons (x, Nil)) xs')
                  else if b1
                       then app tk (tokenize_helper tp (Cons (x, Nil)) xs')
                       else if b2
                            then if b3
                                 then app tk
                                        (tokenize_helper tp (Cons (x, Nil))
                                          xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper tp (Cons
                                                    (x, Nil)) xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper tp
                                                         (Cons (x, Nil)) xs')
                                                else app tk (Cons ((Cons
                                                       ('(', Nil)),
                                                       (tokenize_helper Other
                                                         Nil xs')))
                                      else app tk
                                             (tokenize_helper tp (Cons (x,
                                               Nil)) xs')
                            else app tk
                                   (tokenize_helper tp (Cons (x, Nil)) xs'))
             x)
      | Other ->
        (match classifyChar x with
         | White ->
           (* If this appears, you're using Ascii internals. Please don't *) (fun f c -> let n = Char.code c in let h i = (n land (1 lsl i)) <> 0 in f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
             (fun b b0 b1 b2 b3 b4 b5 b6 ->
             if b
             then if b0
                  then app tk (tokenize_helper White Nil xs')
                  else if b1
                       then app tk (tokenize_helper White Nil xs')
                       else if b2
                            then if b3
                                 then app tk (tokenize_helper White Nil xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper White Nil
                                                    xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper White
                                                         Nil xs')
                                                else app tk (Cons ((Cons
                                                       (')', Nil)),
                                                       (tokenize_helper Other
                                                         Nil xs')))
                                      else app tk
                                             (tokenize_helper White Nil xs')
                            else app tk (tokenize_helper White Nil xs')
             else if b0
                  then app tk (tokenize_helper White Nil xs')
                  else if b1
                       then app tk (tokenize_helper White Nil xs')
                       else if b2
                            then if b3
                                 then app tk (tokenize_helper White Nil xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper White Nil
                                                    xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper White
                                                         Nil xs')
                                                else app tk (Cons ((Cons
                                                       ('(', Nil)),
                                                       (tokenize_helper Other
                                                         Nil xs')))
                                      else app tk
                                             (tokenize_helper White Nil xs')
                            else app tk (tokenize_helper White Nil xs'))
             x
         | Other ->
           (* If this appears, you're using Ascii internals. Please don't *) (fun f c -> let n = Char.code c in let h i = (n land (1 lsl i)) <> 0 in f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
             (fun b b0 b1 b2 b3 b4 b5 b6 ->
             if b
             then if b0
                  then tokenize_helper Other (Cons (x, acc)) xs'
                  else if b1
                       then tokenize_helper Other (Cons (x, acc)) xs'
                       else if b2
                            then if b3
                                 then tokenize_helper Other (Cons (x, acc))
                                        xs'
                                 else if b4
                                      then if b5
                                           then tokenize_helper Other (Cons
                                                  (x, acc)) xs'
                                           else if b6
                                                then tokenize_helper Other
                                                       (Cons (x, acc)) xs'
                                                else app tk (Cons ((Cons
                                                       (')', Nil)),
                                                       (tokenize_helper Other
                                                         Nil xs')))
                                      else tokenize_helper Other (Cons (x,
                                             acc)) xs'
                            else tokenize_helper Other (Cons (x, acc)) xs'
             else if b0
                  then tokenize_helper Other (Cons (x, acc)) xs'
                  else if b1
                       then tokenize_helper Other (Cons (x, acc)) xs'
                       else if b2
                            then if b3
                                 then tokenize_helper Other (Cons (x, acc))
                                        xs'
                                 else if b4
                                      then if b5
                                           then tokenize_helper Other (Cons
                                                  (x, acc)) xs'
                                           else if b6
                                                then tokenize_helper Other
                                                       (Cons (x, acc)) xs'
                                                else app tk (Cons ((Cons
                                                       ('(', Nil)),
                                                       (tokenize_helper Other
                                                         Nil xs')))
                                      else tokenize_helper Other (Cons (x,
                                             acc)) xs'
                            else tokenize_helper Other (Cons (x, acc)) xs')
             x
         | x0 ->
           (* If this appears, you're using Ascii internals. Please don't *) (fun f c -> let n = Char.code c in let h i = (n land (1 lsl i)) <> 0 in f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
             (fun b b0 b1 b2 b3 b4 b5 b6 ->
             if b
             then if b0
                  then app tk (tokenize_helper x0 (Cons (x, Nil)) xs')
                  else if b1
                       then app tk (tokenize_helper x0 (Cons (x, Nil)) xs')
                       else if b2
                            then if b3
                                 then app tk
                                        (tokenize_helper x0 (Cons (x, Nil))
                                          xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper x0 (Cons
                                                    (x, Nil)) xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper x0
                                                         (Cons (x, Nil)) xs')
                                                else app tk (Cons ((Cons
                                                       (')', Nil)),
                                                       (tokenize_helper Other
                                                         Nil xs')))
                                      else app tk
                                             (tokenize_helper x0 (Cons (x,
                                               Nil)) xs')
                            else app tk
                                   (tokenize_helper x0 (Cons (x, Nil)) xs')
             else if b0
                  then app tk (tokenize_helper x0 (Cons (x, Nil)) xs')
                  else if b1
                       then app tk (tokenize_helper x0 (Cons (x, Nil)) xs')
                       else if b2
                            then if b3
                                 then app tk
                                        (tokenize_helper x0 (Cons (x, Nil))
                                          xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper x0 (Cons
                                                    (x, Nil)) xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper x0
                                                         (Cons (x, Nil)) xs')
                                                else app tk (Cons ((Cons
                                                       ('(', Nil)),
                                                       (tokenize_helper Other
                                                         Nil xs')))
                                      else app tk
                                             (tokenize_helper x0 (Cons (x,
                                               Nil)) xs')
                            else app tk
                                   (tokenize_helper x0 (Cons (x, Nil)) xs'))
             x)))

(** val tokenize : string -> string list **)

let tokenize s =
  map string_of_list (tokenize_helper White Nil (list_of_string s))

type 'x optionE =
| SomeE of 'x
| NoneE of string

(** val build_symtable : token list -> int -> token -> int **)

let rec build_symtable xs n0 =
  match xs with
  | Nil -> (fun s -> n0)
  | Cons (x, xs0) ->
    if forallb isLowerAlpha (list_of_string x)
    then (fun s ->
           if string_dec s x
           then n0
           else build_symtable xs0 ((fun x -> x + 1) n0) s)
    else build_symtable xs0 n0

type 't parser0 = token list -> ('t, token list) prod optionE

(** val many_helper :
    'a1 parser0 -> 'a1 list -> int -> token list -> ('a1 list, token list)
    prod optionE **)

let rec many_helper p acc steps xs =
  (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
    (fun _ -> NoneE (String ('T', (String ('o', (String ('o', (String (' ',
    (String ('m', (String ('a', (String ('n', (String ('y', (String (' ',
    (String ('r', (String ('e', (String ('c', (String ('u', (String ('r',
    (String ('s', (String ('i', (String ('v', (String ('e', (String (' ',
    (String ('c', (String ('a', (String ('l', (String ('l', (String ('s',
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))
    (fun steps' ->
    match p xs with
    | SomeE p0 ->
      let Pair (t0, xs') = p0 in many_helper p (Cons (t0, acc)) steps' xs'
    | NoneE s -> SomeE (Pair ((rev acc), xs)))
    steps

(** val many : 'a1 parser0 -> int -> 'a1 list parser0 **)

let rec many p steps =
  many_helper p Nil steps

(** val firstExpect : token -> 'a1 parser0 -> 'a1 parser0 **)

let firstExpect t0 p = function
| Nil ->
  NoneE
    (append (String ('e', (String ('x', (String ('p', (String ('e', (String
      ('c', (String ('t', (String ('e', (String ('d', (String (' ', (String
      ('\'', EmptyString))))))))))))))))))))
      (append t0 (String ('\'', (String ('.', EmptyString))))))
| Cons (x, xs') ->
  if string_dec x t0
  then p xs'
  else NoneE
         (append (String ('e', (String ('x', (String ('p', (String ('e',
           (String ('c', (String ('t', (String ('e', (String ('d', (String
           (' ', (String ('\'', EmptyString))))))))))))))))))))
           (append t0 (String ('\'', (String ('.', EmptyString))))))

(** val expect : token -> unit0 parser0 **)

let expect t0 =
  firstExpect t0 (fun xs -> SomeE (Pair (Tt, xs)))

(** val parseIdentifier :
    (string -> int) -> token list -> (id, token list) prod optionE **)

let parseIdentifier symtable = function
| Nil ->
  NoneE (String ('E', (String ('x', (String ('p', (String ('e', (String ('c',
    (String ('t', (String ('e', (String ('d', (String (' ', (String ('i',
    (String ('d', (String ('e', (String ('n', (String ('t', (String ('i',
    (String ('f', (String ('i', (String ('e', (String ('r',
    EmptyString))))))))))))))))))))))))))))))))))))))
| Cons (x, xs') ->
  if forallb isLowerAlpha (list_of_string x)
  then SomeE (Pair ((symtable x), xs'))
  else NoneE
         (append (String ('I', (String ('l', (String ('l', (String ('e',
           (String ('g', (String ('a', (String ('l', (String (' ', (String
           ('i', (String ('d', (String ('e', (String ('n', (String ('t',
           (String ('i', (String ('f', (String ('i', (String ('e', (String
           ('r', (String (':', (String ('\'',
           EmptyString))))))))))))))))))))))))))))))))))))))))
           (append x (String ('\'', EmptyString))))

(** val parseNumber : token list -> (int, token list) prod optionE **)

let parseNumber = function
| Nil ->
  NoneE (String ('E', (String ('x', (String ('p', (String ('e', (String ('c',
    (String ('t', (String ('e', (String ('d', (String (' ', (String ('n',
    (String ('u', (String ('m', (String ('b', (String ('e', (String ('r',
    EmptyString))))))))))))))))))))))))))))))
| Cons (x, xs') ->
  if forallb isDigit (list_of_string x)
  then SomeE (Pair
         ((fold_left (fun n0 d ->
            plus
              (mult ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                ((fun x -> x + 1) 0)))))))))) n0)
              (minus (nat_of_ascii d) (nat_of_ascii '0'))) (list_of_string x)
            0), xs'))
  else NoneE (String ('E', (String ('x', (String ('p', (String ('e', (String
         ('c', (String ('t', (String ('e', (String ('d', (String (' ',
         (String ('n', (String ('u', (String ('m', (String ('b', (String
         ('e', (String ('r', EmptyString))))))))))))))))))))))))))))))

(** val parsePrimaryExp :
    int -> (string -> int) -> token list -> (aexp, token list) prod optionE **)

let rec parsePrimaryExp steps symtable xs =
  (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
    (fun _ -> NoneE (String ('T', (String ('o', (String ('o', (String (' ',
    (String ('m', (String ('a', (String ('n', (String ('y', (String (' ',
    (String ('r', (String ('e', (String ('c', (String ('u', (String ('r',
    (String ('s', (String ('i', (String ('v', (String ('e', (String (' ',
    (String ('c', (String ('a', (String ('l', (String ('l', (String ('s',
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))
    (fun steps' ->
    match parseIdentifier symtable xs with
    | SomeE p -> let Pair (i, rest) = p in SomeE (Pair ((AId i), rest))
    | NoneE err ->
      (match parseNumber xs with
       | SomeE p -> let Pair (n0, rest) = p in SomeE (Pair ((ANum n0), rest))
       | NoneE err0 ->
         (match firstExpect (String ('(', EmptyString))
                  (parseSumExp steps' symtable) xs with
          | SomeE p ->
            let Pair (e, rest) = p in
            (match expect (String (')', EmptyString)) rest with
             | SomeE p0 ->
               let Pair (u, rest') = p0 in SomeE (Pair (e, rest'))
             | NoneE err1 -> NoneE err1)
          | NoneE err1 -> NoneE err1)))
    steps

(** val parseProductExp :
    int -> (string -> int) -> token list -> (aexp, token list) prod optionE **)

and parseProductExp steps symtable xs =
  (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
    (fun _ -> NoneE (String ('T', (String ('o', (String ('o', (String (' ',
    (String ('m', (String ('a', (String ('n', (String ('y', (String (' ',
    (String ('r', (String ('e', (String ('c', (String ('u', (String ('r',
    (String ('s', (String ('i', (String ('v', (String ('e', (String (' ',
    (String ('c', (String ('a', (String ('l', (String ('l', (String ('s',
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))
    (fun steps' ->
    match parsePrimaryExp steps' symtable xs with
    | SomeE p ->
      let Pair (e, rest) = p in
      (match many
               (firstExpect (String ('*', EmptyString))
                 (parsePrimaryExp steps' symtable)) steps' rest with
       | SomeE p0 ->
         let Pair (es, rest') = p0 in
         SomeE (Pair ((fold_left (fun x x0 -> AMult (x, x0)) es e), rest'))
       | NoneE err -> NoneE err)
    | NoneE err -> NoneE err)
    steps

(** val parseSumExp :
    int -> (string -> int) -> token list -> (aexp, token list) prod optionE **)

and parseSumExp steps symtable xs =
  (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
    (fun _ -> NoneE (String ('T', (String ('o', (String ('o', (String (' ',
    (String ('m', (String ('a', (String ('n', (String ('y', (String (' ',
    (String ('r', (String ('e', (String ('c', (String ('u', (String ('r',
    (String ('s', (String ('i', (String ('v', (String ('e', (String (' ',
    (String ('c', (String ('a', (String ('l', (String ('l', (String ('s',
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))
    (fun steps' ->
    match parseProductExp steps' symtable xs with
    | SomeE p ->
      let Pair (e, rest) = p in
      (match many (fun xs0 ->
               match firstExpect (String ('+', EmptyString))
                       (parseProductExp steps' symtable) xs0 with
               | SomeE p0 ->
                 let Pair (e0, rest') = p0 in
                 SomeE (Pair ((Pair (true, e0)), rest'))
               | NoneE err ->
                 (match firstExpect (String ('-', EmptyString))
                          (parseProductExp steps' symtable) xs0 with
                  | SomeE p0 ->
                    let Pair (e0, rest') = p0 in
                    SomeE (Pair ((Pair (false, e0)), rest'))
                  | NoneE err0 -> NoneE err0)) steps' rest with
       | SomeE p0 ->
         let Pair (es, rest') = p0 in
         SomeE (Pair
         ((fold_left (fun e0 term ->
            let Pair (y, e1) = term in
            if y then APlus (e0, e1) else AMinus (e0, e1)) es e), rest'))
       | NoneE err -> NoneE err)
    | NoneE err -> NoneE err)
    steps

(** val parseAExp :
    int -> (string -> int) -> token list -> (aexp, token list) prod optionE **)

let parseAExp =
  parseSumExp

(** val parseAtomicExp :
    int -> (string -> int) -> token list -> (bexp, token list) prod optionE **)

let rec parseAtomicExp steps symtable xs =
  (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
    (fun _ -> NoneE (String ('T', (String ('o', (String ('o', (String (' ',
    (String ('m', (String ('a', (String ('n', (String ('y', (String (' ',
    (String ('r', (String ('e', (String ('c', (String ('u', (String ('r',
    (String ('s', (String ('i', (String ('v', (String ('e', (String (' ',
    (String ('c', (String ('a', (String ('l', (String ('l', (String ('s',
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))
    (fun steps' ->
    match expect (String ('t', (String ('r', (String ('u', (String ('e',
            EmptyString)))))))) xs with
    | SomeE p -> let Pair (u, rest) = p in SomeE (Pair (BTrue, rest))
    | NoneE err ->
      (match expect (String ('f', (String ('a', (String ('l', (String ('s',
               (String ('e', EmptyString)))))))))) xs with
       | SomeE p -> let Pair (u, rest) = p in SomeE (Pair (BFalse, rest))
       | NoneE err0 ->
         (match firstExpect (String ('n', (String ('o', (String ('t',
                  EmptyString)))))) (parseAtomicExp steps' symtable) xs with
          | SomeE p ->
            let Pair (e, rest) = p in SomeE (Pair ((BNot e), rest))
          | NoneE err1 ->
            (match firstExpect (String ('(', EmptyString))
                     (parseConjunctionExp steps' symtable) xs with
             | SomeE p ->
               let Pair (e, rest) = p in
               (match expect (String (')', EmptyString)) rest with
                | SomeE p0 ->
                  let Pair (u, rest') = p0 in SomeE (Pair (e, rest'))
                | NoneE err2 -> NoneE err2)
             | NoneE err2 ->
               (match parseProductExp steps' symtable xs with
                | SomeE p ->
                  let Pair (e, rest) = p in
                  (match firstExpect (String ('=', (String ('=',
                           EmptyString)))) (parseAExp steps' symtable) rest with
                   | SomeE p0 ->
                     let Pair (e', rest') = p0 in
                     SomeE (Pair ((BEq (e, e')), rest'))
                   | NoneE err3 ->
                     (match firstExpect (String ('<', (String ('=',
                              EmptyString)))) (parseAExp steps' symtable)
                              rest with
                      | SomeE p0 ->
                        let Pair (e', rest') = p0 in
                        SomeE (Pair ((BLe (e, e')), rest'))
                      | NoneE err4 ->
                        NoneE (String ('E', (String ('x', (String ('p',
                          (String ('e', (String ('c', (String ('t', (String
                          ('e', (String ('d', (String (' ', (String ('\'',
                          (String ('=', (String ('=', (String ('\'', (String
                          (' ', (String ('o', (String ('r', (String (' ',
                          (String ('\'', (String ('<', (String ('=', (String
                          ('\'', (String (' ', (String ('a', (String ('f',
                          (String ('t', (String ('e', (String ('r', (String
                          (' ', (String ('a', (String ('r', (String ('i',
                          (String ('t', (String ('h', (String ('m', (String
                          ('e', (String ('t', (String ('i', (String ('c',
                          (String (' ', (String ('e', (String ('x', (String
                          ('p', (String ('r', (String ('e', (String ('s',
                          (String ('s', (String ('i', (String ('o', (String
                          ('n',
                          EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                | NoneE err3 -> NoneE err3)))))
    steps

(** val parseConjunctionExp :
    int -> (string -> int) -> token list -> (bexp, token list) prod optionE **)

and parseConjunctionExp steps symtable xs =
  (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
    (fun _ -> NoneE (String ('T', (String ('o', (String ('o', (String (' ',
    (String ('m', (String ('a', (String ('n', (String ('y', (String (' ',
    (String ('r', (String ('e', (String ('c', (String ('u', (String ('r',
    (String ('s', (String ('i', (String ('v', (String ('e', (String (' ',
    (String ('c', (String ('a', (String ('l', (String ('l', (String ('s',
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))
    (fun steps' ->
    match parseAtomicExp steps' symtable xs with
    | SomeE p ->
      let Pair (e, rest) = p in
      (match many
               (firstExpect (String ('&', (String ('&', EmptyString))))
                 (parseAtomicExp steps' symtable)) steps' rest with
       | SomeE p0 ->
         let Pair (es, rest') = p0 in
         SomeE (Pair ((fold_left (fun x x0 -> BAnd (x, x0)) es e), rest'))
       | NoneE err -> NoneE err)
    | NoneE err -> NoneE err)
    steps

(** val parseBExp :
    int -> (string -> int) -> token list -> (bexp, token list) prod optionE **)

let parseBExp =
  parseConjunctionExp

(** val parseSimpleCommand :
    int -> (string -> int) -> token list -> (com, token list) prod optionE **)

let rec parseSimpleCommand steps symtable xs =
  (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
    (fun _ -> NoneE (String ('T', (String ('o', (String ('o', (String (' ',
    (String ('m', (String ('a', (String ('n', (String ('y', (String (' ',
    (String ('r', (String ('e', (String ('c', (String ('u', (String ('r',
    (String ('s', (String ('i', (String ('v', (String ('e', (String (' ',
    (String ('c', (String ('a', (String ('l', (String ('l', (String ('s',
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))
    (fun steps' ->
    match expect (String ('S', (String ('K', (String ('I', (String ('P',
            EmptyString)))))))) xs with
    | SomeE p -> let Pair (u, rest) = p in SomeE (Pair (CSkip, rest))
    | NoneE err ->
      (match firstExpect (String ('I', (String ('F', EmptyString))))
               (parseBExp steps' symtable) xs with
       | SomeE p ->
         let Pair (e, rest) = p in
         (match firstExpect (String ('T', (String ('H', (String ('E', (String
                  ('N', EmptyString))))))))
                  (parseSequencedCommand steps' symtable) rest with
          | SomeE p0 ->
            let Pair (c, rest') = p0 in
            (match firstExpect (String ('E', (String ('L', (String ('S',
                     (String ('E', EmptyString))))))))
                     (parseSequencedCommand steps' symtable) rest' with
             | SomeE p1 ->
               let Pair (c', rest'') = p1 in
               (match expect (String ('E', (String ('N', (String ('D',
                        EmptyString)))))) rest'' with
                | SomeE p2 ->
                  let Pair (u, rest''') = p2 in
                  SomeE (Pair ((CIf (e, c, c')), rest'''))
                | NoneE err0 -> NoneE err0)
             | NoneE err0 -> NoneE err0)
          | NoneE err0 -> NoneE err0)
       | NoneE err0 ->
         (match firstExpect (String ('W', (String ('H', (String ('I', (String
                  ('L', (String ('E', EmptyString))))))))))
                  (parseBExp steps' symtable) xs with
          | SomeE p ->
            let Pair (e, rest) = p in
            (match firstExpect (String ('D', (String ('O', EmptyString))))
                     (parseSequencedCommand steps' symtable) rest with
             | SomeE p0 ->
               let Pair (c, rest') = p0 in
               (match expect (String ('E', (String ('N', (String ('D',
                        EmptyString)))))) rest' with
                | SomeE p1 ->
                  let Pair (u, rest'') = p1 in
                  SomeE (Pair ((CWhile (e, c)), rest''))
                | NoneE err1 -> NoneE err1)
             | NoneE err1 -> NoneE err1)
          | NoneE err1 ->
            (match parseIdentifier symtable xs with
             | SomeE p ->
               let Pair (i, rest) = p in
               (match firstExpect (String (':', (String ('=', EmptyString))))
                        (parseAExp steps' symtable) rest with
                | SomeE p0 ->
                  let Pair (e, rest') = p0 in
                  SomeE (Pair ((CAss (i, e)), rest'))
                | NoneE err2 -> NoneE err2)
             | NoneE err2 -> NoneE err2))))
    steps

(** val parseSequencedCommand :
    int -> (string -> int) -> token list -> (com, token list) prod optionE **)

and parseSequencedCommand steps symtable xs =
  (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
    (fun _ -> NoneE (String ('T', (String ('o', (String ('o', (String (' ',
    (String ('m', (String ('a', (String ('n', (String ('y', (String (' ',
    (String ('r', (String ('e', (String ('c', (String ('u', (String ('r',
    (String ('s', (String ('i', (String ('v', (String ('e', (String (' ',
    (String ('c', (String ('a', (String ('l', (String ('l', (String ('s',
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))
    (fun steps' ->
    match parseSimpleCommand steps' symtable xs with
    | SomeE p ->
      let Pair (c, rest) = p in
      (match firstExpect (String (';', (String (';', EmptyString))))
               (parseSequencedCommand steps' symtable) rest with
       | SomeE p0 ->
         let Pair (c', rest') = p0 in SomeE (Pair ((CSeq (c, c')), rest'))
       | NoneE err -> SomeE (Pair (c, rest)))
    | NoneE err -> NoneE err)
    steps

(** val bignumber : int **)

let bignumber =
  (fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val parse : string -> (com, token list) prod optionE **)

let parse str =
  let tokens = tokenize str in
  parseSequencedCommand bignumber (build_symtable tokens 0) tokens

