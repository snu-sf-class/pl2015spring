(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

type 'a option =
| Some of 'a
| None

type sumbool =
| Left
| Right

(** val plus : int -> int -> int **)

let rec plus = ( + )

(** val mult : int -> int -> int **)

let rec mult = ( * )

(** val minus : int -> int -> int **)

let rec minus n m =
  (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
    (fun _ ->
    n)
    (fun k ->
    (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
      (fun _ ->
      n)
      (fun l ->
      minus k l)
      m)
    n

(** val eq_nat_dec : int -> int -> sumbool **)

let rec eq_nat_dec n m =
  (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
    (fun _ ->
    (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
      (fun _ ->
      Left)
      (fun m0 ->
      Right)
      m)
    (fun n0 ->
    (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
      (fun _ ->
      Right)
      (fun m0 ->
      eq_nat_dec n0 m0)
      m)
    n

(** val beq_nat : int -> int -> bool **)

let rec beq_nat = ( = )

(** val ble_nat : int -> int -> bool **)

let rec ble_nat n m =
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
    n

type id =
  int
  (* singleton inductive, whose constructor was Id *)

(** val eq_id_dec : id -> id -> sumbool **)

let eq_id_dec id1 id2 =
  eq_nat_dec id1 id2

type state = id -> int

(** val update : state -> id -> int -> state **)

let update st x n x' =
  match eq_id_dec x x' with
  | Left -> n
  | Right -> st x'

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
| ANum n -> n
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

