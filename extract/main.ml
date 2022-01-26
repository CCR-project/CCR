open Stdlib
open List
open String

open Datatypes
open BinNums
open BinInt

open ITreeDefinition
open Any
open ImpPrelude
open ModSem
open ModSemE

open MutFG
open Example0
open EchoAll
open MWAll
open Imp
open Heapsort1

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

let string_of_zs ns = List.fold_left (fun s i -> s ^ " " ^ string_of_z i) "" ns

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
     let argv =
       match (Any.downcast args) with
       | Some args' -> args'
       | None -> []
     in
     print_string (cl2s str ^ "(" ^ string_of_zs argv ^ " ): ");
     let n =
       if (String.equal (cl2s str) ("print"))
       then (print_endline ""; 0)
       else (try int_of_string (read_line())
             with Failure _ -> 0) in
     k (Obj.repr (Any.upcast (Z.of_int n)))

let rec run t =
  match observe t with
  | RetF r ->
     print_endline ("Return: " ^ (string_of_any r))
  | TauF t -> run t
  | VisF (e, k) -> handle_Event e (fun x -> run (k x))

let main =
  print_endline (if coq_EXTRACT_MW_IMPL_LINKING_CHECK then "MW Linking: OK" else "MW Linking: Fail");
  print_endline "Which program do you want to execute?";
  print_endline "1: MW example on Imp level (it prints 0/42 infinitely)";
  print_endline "2: MW example on Abstraction level (it prints 0/42 infinitely)";
  print_endline "3: Mutual Sum example (in the technical report) on Imp level";
  print_endline "4: Mutual Sum example (in the technical report) on Abstraction level";
  print_endline "5: Echo example (in the technical report) on Imp level";
  print_endline "6: Echo example (in the technical report) on Imp+ level (everything is the same but shallow embedded into Coq)";
  print_endline "7: Echo example (in the technical report) on Abstraction level";
  print_endline "8: Heapsort example on abstraction level";
  print_endline "<<NOTE: These programs are all deterministic, but you may see some \"choose\" which is from Mem.alloc. Put any natural number; it does not affect semantics>>";
  match int_of_string (read_line()) with
  | 1 -> run (mw_impl_itr)
  | 2 -> run (mw_abs_itr)
  | 3 -> run (mutsum_imp)
  | 4 -> run (mutsum)
  | 5 -> run (echo_imp_itr)
  | 6 -> run (echo_impl_itr)
  | 7 -> run (echo_spec_itr)
  | 8 -> run (heapsort_main)
  | _ -> print_endline "Invalid Number!"
