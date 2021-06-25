Require Import Coqlib.
Require Import Universe.
Require Import Skeleton.
Require Import STS Behavior.
Require Import ModSem.
Require Import Imp2Csharpminor.

From compcert Require Import
     Ctypes AST Integers Cminor Csharpminor Globalenvs Linking Errors Cminorgen Behaviors Events.

From compcert Require Compiler.

Set Implicit Arguments.

Module ASMGEN.

  Import Compiler.

  (* For builtins at compile time, ref: Velus, Generation.v *)
  Fixpoint list_type_to_typelist (types: list type): typelist :=
    match types with
    | [] => Tnil
    | h :: t => Tcons h (list_type_to_typelist t)
    end
  .

  Definition transf_csharpminor_program (p: Csharpminor.program) : res Asm.program :=
    OK p
       @@@ time "Cminor generation" Cminorgen.transl_program
       @@@ transf_cminor_program.

End ASMGEN.
