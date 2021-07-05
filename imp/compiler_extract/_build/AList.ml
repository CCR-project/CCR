open BinNums
open Coqlib0
open RelDec
open String0

type 'a coq_Dec = 'a -> 'a -> bool

(** val dec : 'a1 coq_Dec -> 'a1 -> 'a1 -> bool **)

let dec dec0 =
  dec0

(** val positive_Dec_obligation_1 : positive -> positive -> bool **)

let rec positive_Dec_obligation_1 p x =
  match p with
  | Coq_xI p0 ->
    (match x with
     | Coq_xI p1 -> positive_Dec_obligation_1 p0 p1
     | _ -> false)
  | Coq_xO p0 ->
    (match x with
     | Coq_xO p1 -> positive_Dec_obligation_1 p0 p1
     | _ -> false)
  | Coq_xH -> (match x with
               | Coq_xH -> true
               | _ -> false)

(** val positive_Dec : positive coq_Dec **)

let positive_Dec =
  positive_Dec_obligation_1

(** val string_Dec_obligation_1 : char list -> char list -> bool **)

let string_Dec_obligation_1 =
  string_dec

(** val string_Dec : char list coq_Dec **)

let string_Dec =
  string_Dec_obligation_1

(** val coq_Dec_RelDec : 'a1 coq_Dec -> 'a1 coq_RelDec **)

let coq_Dec_RelDec h a0 a1 =
  sumbool_to_bool (dec h a0 a1)
