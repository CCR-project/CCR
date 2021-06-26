Require Import Coqlib.
Require Import Universe.
Require Import Imp.
Require Import Imp2Csharpminor.

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

  Definition transf_csharpminor_program (p: Csharpminor.program) : res Asm.program :=
    OK p
       @@@ time "Cminor generation" Cminorgen.transl_program
       @@@ transf_cminor_program.

  Context `{builtins: builtinsTy}.

  Definition compile (src: Imp.programL) : res Asm.program :=
    match Imp2Csharpminor.compile src with
    | OK csm => transf_csharpminor_program csm
    | Error msg => Error msg
    end.

  Definition compile_imp (src: Imp.program) := compile (Imp.lift src).

End ASMGEN.
