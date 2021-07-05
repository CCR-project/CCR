From compcert Require Import Ctypes Errors Compiler.

Require Import String.

Set Implicit Arguments.

Section ASMGEN.

  Definition transf_csharpminor_program (p: Csharpminor.program) : res Asm.program :=
    OK p
       @@@ time "Cminor generation" Cminorgen.transl_program
       @@@ transf_cminor_program.

End ASMGEN.
