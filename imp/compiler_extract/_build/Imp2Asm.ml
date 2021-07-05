open Asm
open Csharpminor2Asm
open Ctypes
open Errors
open Imp
open Imp2Csharpminor

(** val list_type_to_typelist : coq_type list -> typelist **)

let rec list_type_to_typelist = function
| [] -> Tnil
| h :: t -> Tcons (h, (list_type_to_typelist t))

(** val compile : builtinsTy -> programL -> Asm.program res **)

let compile builtins src =
  match compile builtins src with
  | OK csm -> transf_csharpminor_program csm
  | Error msg -> Error msg

(** val compile_imp : builtinsTy -> program -> Asm.program res **)

let compile_imp builtins src =
  compile builtins (lift src)
