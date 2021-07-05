open BinNums
open Datatypes

(** val ptr64 : bool **)

let ptr64 =
  true

(** val big_endian : bool **)

let big_endian =
  false

(** val align_int64 : coq_Z **)

let align_int64 =
  Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH)))

(** val align_float64 : coq_Z **)

let align_float64 =
  Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH)))

(** val splitlong : bool **)

let splitlong =
  negb ptr64

(** val default_nan_64 : bool * positive **)

let default_nan_64 =
  (true,
    (let rec f = function
     | O -> Coq_xH
     | S n0 -> Coq_xO (f n0)
     in f (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S
          O)))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val default_nan_32 : bool * positive **)

let default_nan_32 =
  (true,
    (let rec f = function
     | O -> Coq_xH
     | S n0 -> Coq_xO (f n0)
     in f (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          O))))))))))))))))))))))))

(** val choose_nan_64 : (bool * positive) list -> bool * positive **)

let choose_nan_64 = function
| [] -> default_nan_64
| n :: _ -> n

(** val choose_nan_32 : (bool * positive) list -> bool * positive **)

let choose_nan_32 = function
| [] -> default_nan_32
| n :: _ -> n

(** val float_of_single_preserves_sNaN : bool **)

let float_of_single_preserves_sNaN =
  false

(** val win64 : bool **)

let win64 = match Configuration.system with
    | "cygwin" when ptr64 -> true
    | _ -> false
