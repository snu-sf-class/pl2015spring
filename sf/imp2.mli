val negb : bool -> bool

type 'a option =
| Some of 'a
| None

type sumbool =
| Left
| Right

val plus : int -> int -> int

val mult : int -> int -> int

val minus : int -> int -> int

val eq_nat_dec : int -> int -> sumbool

val beq_nat : int -> int -> bool

val ble_nat : int -> int -> bool

type id =
  int
  (* singleton inductive, whose constructor was Id *)

val eq_id_dec : id -> id -> sumbool

type state = id -> int

val update : state -> id -> int -> state

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

val aeval : state -> aexp -> int

val beval : state -> bexp -> bool

type com =
| CSkip
| CAss of id * aexp
| CSeq of com * com
| CIf of bexp * com * com
| CWhile of bexp * com

val ceval_step : state -> com -> int -> state option

