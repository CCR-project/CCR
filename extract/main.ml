open Stdlib
open List
open String

open ITreeDefinition
open Any
open Universe
open ModSem

open MutFG
open Example0

let cl2s = fun cl -> String.concat "" (List.map (String.make 1) cl)

let string_of_val v =
  match v with
  | Vint n -> "Vint " ^ string_of_int n
  | Vptr (ptr, ofs) -> "Vptr (" ^ string_of_int ptr ^ ", " ^ string_of_int ofs ^ ")"
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
     k (Obj.repr n)
  | Take ->
     print_string "Take: ";
     let n =
       (try int_of_string (read_line())
        with Failure _ -> 0) in
     k (Obj.repr n)
  | Syscall (str, args) ->
     print_string (cl2s str ^ "(" ^ string_of_vals args ^ " ): ");
     let n =
       (try int_of_string (read_line())
        with Failure _ -> 0) in
     k (Obj.repr (Vint n))

let rec run t =
  match observe t with
  | RetF r ->
     print_endline (string_of_any r)
  | TauF t -> run t
  | VisF (e, k) -> handle_Event e (fun x -> run (k x))

let main =
  print_endline "-----------------------------------";
  print_endline "- Mutual Sum"; run (mutsum);
  print_endline "-----------------------------------";
  print_endline "- Example0"; run (ex0);
