open Diagnostics
open Driveraux
(* open Driver *)
open Compiler
open Imp2Clight
open ImpSimple
open ImpFactorial

(* Preprocessing clight programs *)
(* ref: velus, veluslib.ml *)
let add_builtin p (name, (out, ins, b)) =
  let env = Env.empty in
  let id = Camlcoq.intern_string name in
  let id' = Camlcoq.coqstring_of_camlstring name in
  let targs = List.map (C2C.convertTyp env) ins
                |> Imp2Clight.list_type_to_typelist in
  let tres = C2C.convertTyp env out in
  let sg = Ctypes.signature_of_type targs tres AST.cc_default in
  let ef =
    if name = "malloc" then AST.EF_malloc else
    if name = "free" then AST.EF_free else
    if Str.string_match C2C.re_runtime name 0 then AST.EF_runtime(id', sg) else
    if Str.string_match C2C.re_builtin name 0
    && List.mem_assoc name C2C.builtins.builtin_functions
    then AST.EF_builtin(id', sg)
    else AST.EF_external(id', sg) in
  let decl = (id, AST.Gfun (Ctypes.External (ef, targs, tres, AST.cc_default))) in
  { p with Ctypes.prog_defs = decl :: p.Ctypes.prog_defs }

let add_builtins p =
  List.fold_left add_builtin p C2C.builtins_generic.builtin_functions


(* Imp program compilations *)
let compile_imp_simple =
  (* Convert Imp to Clight *)
  let i2c = Imp2Clight.compile (ImpSimple.imp_simple_prog) in
  match i2c with
  | Errors.OK clight_out ->
     let cl_built = add_builtins clight_out in
     (* Convert to Asm *)
     (match Compiler.apply_partial
              (Compiler.transf_clight_program cl_built)
              Asmexpand.expand_program with
      | Errors.OK asm ->
         (* Print Asm in text form *)
         let oc = open_out "simple.s" in
         PrintAsm.print_program oc asm;
         close_out oc
      | Errors.Error msg ->
         let loc = file_loc "test.c" in
         fatal_error loc "%a"  print_error msg)
  | Errors.Error msg ->
     print_endline "imp to clight failed"

let compile_imp_factorial =
  (* Convert Imp to Clight *)
  let i2c = Imp2Clight.compile (ImpFactorial.imp_factorial_prog) in
  match i2c with
  | Errors.OK clight_out ->
     let cl_built = add_builtins clight_out in
     (* Convert to Asm *)
     (match Compiler.apply_partial
              (Compiler.transf_clight_program cl_built)
              Asmexpand.expand_program with
      | Errors.OK asm ->
         (* Print Asm in text form *)
         let oc = open_out "factorial.s" in
         PrintAsm.print_program oc asm;
         close_out oc
      | Errors.Error msg ->
         let loc = file_loc "test.c" in
         fatal_error loc "%a"  print_error msg)
  | Errors.Error msg ->
     print_endline "imp to clight failed"

let main =
  print_endline "Start compilations...";
  compile_imp_simple;
  compile_imp_factorial;
  print_endline "Done."



(* let compile_i_file2 sourcename preproname =
 *   Driver.compile_c_file sourcename preproname
 *     (output_filename ~final:true sourcename ".c" ".s");
 *   ""
 * 
 * let process_c_file2 sourcename =
 *   ensure_inputfile_exists sourcename;
 *   let preproname = tmp_file ".i" in
 *     Frontend.preprocess sourcename preproname;
 *     compile_i_file2 sourcename preproname
 * 
 * (\* Processing of a .i / .p file (preprocessed C) *\)
 * let process_i_file2 sourcename =
 *   ensure_inputfile_exists sourcename;
 *   compile_i_file2 sourcename sourcename
 * 
 * let main =
 *     print_endline "start";
 *     process_i_file2 "test.c";
 *     print_endline "end" *)
