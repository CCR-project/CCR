open AST
open BinNums
open Cop
open Ctypes
open Floats
open Integers
open List0

type expr =
| Econst_int of Int.int * coq_type
| Econst_float of float * coq_type
| Econst_single of float32 * coq_type
| Econst_long of Int64.int * coq_type
| Evar of ident * coq_type
| Etempvar of ident * coq_type
| Ederef of expr * coq_type
| Eaddrof of expr * coq_type
| Eunop of unary_operation * expr * coq_type
| Ebinop of binary_operation * expr * expr * coq_type
| Ecast of expr * coq_type
| Efield of expr * ident * coq_type
| Esizeof of coq_type * coq_type
| Ealignof of coq_type * coq_type

(** val typeof : expr -> coq_type **)

let typeof = function
| Econst_int (_, ty) -> ty
| Econst_float (_, ty) -> ty
| Econst_single (_, ty) -> ty
| Econst_long (_, ty) -> ty
| Evar (_, ty) -> ty
| Etempvar (_, ty) -> ty
| Ederef (_, ty) -> ty
| Eaddrof (_, ty) -> ty
| Eunop (_, _, ty) -> ty
| Ebinop (_, _, _, ty) -> ty
| Ecast (_, ty) -> ty
| Efield (_, _, ty) -> ty
| Esizeof (_, ty) -> ty
| Ealignof (_, ty) -> ty

type label = ident

type statement =
| Sskip
| Sassign of expr * expr
| Sset of ident * expr
| Scall of ident option * expr * expr list
| Sbuiltin of ident option * external_function * typelist * expr list
| Ssequence of statement * statement
| Sifthenelse of expr * statement * statement
| Sloop of statement * statement
| Sbreak
| Scontinue
| Sreturn of expr option
| Sswitch of expr * labeled_statements
| Slabel of label * statement
| Sgoto of label
and labeled_statements =
| LSnil
| LScons of coq_Z option * statement * labeled_statements

type coq_function = { fn_return : coq_type; fn_callconv : calling_convention;
                      fn_params : (ident * coq_type) list;
                      fn_vars : (ident * coq_type) list;
                      fn_temps : (ident * coq_type) list; fn_body : statement }

(** val var_names : (ident * coq_type) list -> ident list **)

let var_names vars =
  map fst vars

type fundef = coq_function Ctypes.fundef

(** val type_of_function : coq_function -> coq_type **)

let type_of_function f =
  Tfunction ((type_of_params f.fn_params), f.fn_return, f.fn_callconv)

type program = coq_function Ctypes.program
