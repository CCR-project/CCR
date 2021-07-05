open AList
open AST
open BinNums
open Cminor
open Coqlib0
open Coqlib
open Csharpminor
open Datatypes
open Errors
open Imp
open Integers
open List0
open Maps
open PeanoNat
open RelDec
open Skeleton
open String0

val s2p : char list -> ident

type builtinsTy =
  (char list * external_function) list
  (* singleton inductive, whose constructor was mk *)

val bts0 : builtinsTy -> (char list * external_function) list

val compile_expr : expr -> Csharpminor.expr

val compile_exprs : expr list -> Csharpminor.expr list

val make_signature : nat -> signature

val compile_stmt : stmt -> Csharpminor.stmt

val compile_eVar : char list -> ident * (fundef, unit) globdef

val compile_eVars : extVars -> (ident * (fundef, unit) globdef) list

val compile_iVar : (char list * coq_Z) -> ident * (fundef, unit) globdef

val compile_iVars : progVars -> (ident * (fundef, unit) globdef) list

val compile_eFun : (char list * nat) -> ident * (fundef, unit) globdef

val compile_eFuns : extFuns -> (ident * (fundef, unit) globdef) list

val compile_iFun :
  (char list * (char list * coq_function)) -> ident * (fundef, unit) globdef

val compile_iFuns :
  (char list * (char list * coq_function)) list -> (ident * (fundef, unit)
  globdef) list

val bts : builtinsTy -> (char list * (fundef, unit) globdef) list

val init_g0 : builtinsTy -> (char list * (fundef, unit) globdef) list

val init_g : builtinsTy -> (ident * (fundef, unit) globdef) list

val c_sys : (ident * (fundef, unit) globdef) list

val compile_gdefs :
  builtinsTy -> programL -> (ident * (fundef, unit) globdef) list

val compile : builtinsTy -> programL -> Csharpminor.program res

val extFun_Dec : (char list * nat) -> (char list * nat) -> bool

val name1 : ('a1 * 'a2) list -> 'a1 list

val name2 : ('a1 * ('a2 * 'a3)) list -> 'a2 list

val l_nameL : programL -> programL -> char list list

val l_pvs : programL -> programL -> (char list * coq_Z) list

val l_pfs :
  programL -> programL -> (char list * (char list * coq_function)) list

val l_publicL : builtinsTy -> programL -> programL -> char list list

val l_defsL : programL -> programL -> (char list * Sk.gdef) list

val link_imp_cond1 : programL -> programL -> bool

val _link_imp_cond2' : (char list * nat) -> extFuns -> bool

val _link_imp_cond2 : (char list * nat) list -> bool

val link_imp_cond2 : programL -> programL -> bool

val l_evs : programL -> programL -> char list list

val l_efs : programL -> programL -> (char list * nat) list

val link_imp_cond3 : builtinsTy -> programL -> programL -> bool

val link_imp : builtinsTy -> programL -> programL -> programL option

val list2nlist : 'a1 -> 'a1 list -> 'a1 nlist

val link_imp_nlist : builtinsTy -> programL nlist -> programL option

val link_imp_list : builtinsTy -> programL list -> programL option

val link_imps : builtinsTy -> program list -> programL option
