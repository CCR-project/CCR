open ClightToAsm
open Imp2Clight
open Imp_factorial

let compile_imp ofile =
  (* Convert Imp to Clight *)
  match Imp2Clight.compile (Imp_factorial.imp_factorial_mod) with
  | Errors.OK CL ->
     (* Convert to Asm *)
     (match Compiler.apply_partial
              (ClightToAsm.transf_clight2_program CL)
              Asmexpand.expand_program with
      | Errors.OK asm ->
         (* Print Asm in text form *)
         let oc = open_out ofile in
         PrintAsm.print_program oc asm;
         close_out oc
      | Errors.Error msg ->
         print_endline msg)
  | Errors.Error msg ->
     print_endline msg

let main =
  let tgt = read_line() in
  compile_imp tgt
