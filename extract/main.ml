open Stdlib
open List
open String

open Datatypes
open BinNums
open BinInt

open ITreeDefinition
open Any
open Universe
open ModSem

open MutFG
open Example0
open EchoAll
open Imp

let cl2s = fun cl -> String.concat "" (List.map (String.make 1) cl)

module Nat = struct
  include Nat
  let rec to_int = function | O -> 0 | S n -> succ (to_int n)
  let rec of_int n = assert(n >= 0); if(n == 0) then O else S (of_int (pred n))
end

module Z = struct
  include Z
  let to_int = fun n ->
    match n with
    | Zneg _ -> - (Nat.to_int (Z.to_nat (Z.opp n)))
    | _ -> Nat.to_int (Z.to_nat n)
  let of_int = fun n ->
    if (n > 0)
    then (Z.of_nat (Nat.of_int n))
    else (Z.opp (Z.of_nat (Nat.of_int (- n))))
end

let string_of_nat n =
  string_of_int (Nat.to_int n)

let string_of_z n =
  string_of_int (Z.to_int n)

let string_of_val v =
  match v with
  | Vint n -> "Vint " ^ string_of_z n
  | Vptr (ptr, ofs) -> "Vptr (" ^ string_of_nat ptr ^ ", " ^ string_of_z ofs ^ ")"
  | Vundef -> "Vundef"

let string_of_vals vs = List.fold_left (fun s i -> s ^ " " ^ string_of_val i) "" vs

let string_of_any v =
  match (Any.downcast v) with
  | Some v' -> string_of_val v'
  | None -> "fail"

let handle_Event = fun e k ->
  match e with
  | Choose ->
     print_string "Choose: ";
     let n =
       (try int_of_string (read_line())
        with Failure _ -> 0) in
     k (Obj.repr (Nat.of_int n))
  | Take ->
     print_string "Take: ";
     let n =
       (try int_of_string (read_line())
        with Failure _ -> 0) in
     k (Obj.repr (Nat.of_int n))
  | Syscall (str, args) ->
     print_string (cl2s str ^ "(" ^ string_of_vals args ^ " ): ");
     let n =
       if (String.equal (cl2s str) ("printf"))
       then (print_endline ""; 0)
       else (try int_of_string (read_line())
             with Failure _ -> 0) in
     k (Obj.repr (Vint (Z.of_int n)))

let rec run t =
  match observe t with
  | RetF r ->
     print_endline ("Return: " ^ (string_of_any r))
  | TauF t -> run t
  | VisF (e, k) -> handle_Event e (fun x -> run (k x))

let main =
  print_endline "-----------------------------------";
  print_endline "- Mutual Sum"; run (mutsum);
  print_endline "-----------------------------------";
  print_endline "- Imp factorial"; run (imp_ex);
  print_endline "-----------------------------------";
  print_endline "- Imp Mutual Sum"; run (mutsum_imp);
  print_endline "-----------------------------------";
  print_endline "- Delayed Echo"; run (echo_prog);
