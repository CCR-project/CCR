open Asm
open Cminorgen
open Compiler
open Csharpminor
open Errors

val transf_csharpminor_program : program -> Asm.program res
