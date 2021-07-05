open Asm
open Csharpminor2Asm
open Ctypes
open Errors
open Imp
open Imp2Csharpminor

val list_type_to_typelist : coq_type list -> typelist

val compile : builtinsTy -> programL -> Asm.program res

val compile_imp : builtinsTy -> program -> Asm.program res
