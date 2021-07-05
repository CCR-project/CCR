open Asm
open Cminorgen
open Compiler
open Csharpminor
open Errors

(** val transf_csharpminor_program : program -> Asm.program res **)

let transf_csharpminor_program p =
  apply_partial
    (apply_partial (OK p)
      (time
        ('C'::('m'::('i'::('n'::('o'::('r'::(' '::('g'::('e'::('n'::('e'::('r'::('a'::('t'::('i'::('o'::('n'::[])))))))))))))))))
        transl_program)) transf_cminor_program
