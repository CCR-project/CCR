open AList
open BinNums
open Datatypes
open List0
open RelDec
open Skeleton

type var = char list

type expr =
| Var of var
| Lit of coq_Z
| Eq of expr * expr
| Lt of expr * expr
| Plus of expr * expr
| Minus of expr * expr
| Mult of expr * expr

type stmt =
| Skip
| Assign of var * expr
| Seq of stmt * stmt
| If of expr * stmt * stmt
| CallFun of var * char list * expr list
| CallPtr of var * expr * expr list
| CallSys of var * char list * expr list
| AddrOf of var * char list
| Malloc of var * expr
| Free of expr
| Load of var * expr
| Store of expr * expr
| Cmp of var * expr * expr

type coq_function = { fn_params : var list; fn_vars : var list; fn_body : stmt }

val call_ban : char list -> bool

val syscalls : (char list * nat) list

type extVars = char list list

type extFuns = (char list * nat) list

type progVars = (char list * coq_Z) list

type progFuns = (char list * coq_function) list

type programL = { nameL : char list list; ext_varsL : extVars;
                  ext_funsL : extFuns; prog_varsL : progVars;
                  prog_funsL : (char list * (char list * coq_function)) list;
                  publicL : char list list; defsL : (char list * Sk.gdef) list }

type program = { name : char list; ext_vars : extVars; ext_funs : extFuns;
                 prog_vars : progVars; prog_funs : progFuns }

val public : program -> char list list

val defs : program -> (char list * Sk.gdef) list

val lift : program -> programL
