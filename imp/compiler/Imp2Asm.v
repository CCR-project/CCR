Require Import Coqlib.
Require Import ImpPrelude.
Require Import Imp.
Require Import Imp2Csharpminor.
Require Import Csharpminor2Asm.

From compcert Require Import Ctypes Errors Compiler.

Set Implicit Arguments.

Section ASMGEN.

  (* For builtins at compile time, ref: Velus, Generation.v *)
  Fixpoint list_type_to_typelist (types: list type): typelist :=
    match types with
    | [] => Tnil
    | h :: t => Tcons h (list_type_to_typelist t)
    end
  .

  Context `{builtins: builtinsTy}.

  Definition compile (src: Imp.programL) : res Asm.program :=
    match Imp2Csharpminor.compile src with
    | OK csm => transf_csharpminor_program csm
    | Error msg => Error msg
    end.

  Definition compile_imp (src: Imp.program) := compile (Imp.lift src).

End ASMGEN.
