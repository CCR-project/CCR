open AST
open Archi
open BinInt
open BinNums
open Cop
open Coqlib
open Csyntax
open Ctypes
open Datatypes
open Errors
open Integers
open List0
open Maps
open Memory
open Values

val do_cast : coq_val -> coq_type -> coq_type -> coq_val res

val lookup_composite : composite_env -> ident -> composite res

val constval : composite_env -> expr -> coq_val res

val constval_cast : composite_env -> expr -> coq_type -> coq_val res

type coq_initializer =
| Init_single of expr
| Init_array of initializer_list
| Init_struct of initializer_list
| Init_union of ident * coq_initializer
and initializer_list =
| Init_nil
| Init_cons of coq_initializer * initializer_list

val transl_init_single : composite_env -> coq_type -> expr -> init_data res

val padding : coq_Z -> coq_Z -> init_data list -> init_data list

val transl_init_rec :
  composite_env -> coq_type -> coq_initializer -> init_data list -> init_data
  list res

val transl_init_array :
  composite_env -> coq_type -> initializer_list -> coq_Z -> init_data list ->
  init_data list res

val transl_init_struct :
  composite_env -> coq_type -> members -> initializer_list -> coq_Z ->
  init_data list -> init_data list res

val transl_init :
  composite_env -> coq_type -> coq_initializer -> init_data list res
