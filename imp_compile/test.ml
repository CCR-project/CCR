open Diagnostics
open Driveraux
open Compiler
open Imp
open Imp2Csharpminor
open Imp2CsharpminorLink
open Imp2Asm
open ImpSimple
open ImpFactorial
open ImpMutsum
open ImpKnot
open ImpMem1
open ImpMem2
open ImpLink

(* Preprocessing Csharpminor programs *)
(* ref: Velus, veluslib.ml *)
let add_builtin p (name, (out, ins, b)) =
  let env = Env.empty in
  let id = Camlcoq.intern_string name in
  let id' = Camlcoq.coqstring_of_camlstring name in
  let targs = List.map (C2C.convertTyp env) ins
                |> Imp2Asm.ASMGEN.list_type_to_typelist in
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
  let decl = (id, AST.Gfun (AST.External ef)) in
  { p with AST.prog_defs = decl :: p.AST.prog_defs }

let add_builtins p =
  List.fold_left add_builtin p C2C.builtins_generic.builtin_functions


(* Imp program compilations *)
let compile_imp p ofile =
  (* Convert Imp to Csharpminor *)
  let i2c = Imp2Csharpminor.compile p in
  match i2c with
  | Errors.OK csm_out ->
     let cl_built = add_builtins csm_out in
     (* Convert to Asm *)
     (match Compiler.apply_partial
              (Imp2Asm.ASMGEN.transf_csharpminor_program cl_built)
              Asmexpand.expand_program with
      | Errors.OK asm ->
         (* Print Asm in text form *)
         let oc = open_out ofile in
         PrintAsm.print_program oc asm;
         close_out oc
      | Errors.Error msg ->
         let loc = file_loc ofile in
         fatal_error loc "%a"  print_error msg)
  | Errors.Error msg ->
     print_endline "imp to clight failed"


let main =
  print_endline "Start Imp compilations...";
  compile_imp (Imp.lift ImpSimple.imp_simple_prog) "simple.s";
  compile_imp (Imp.lift ImpFactorial.imp_factorial_prog) "factorial.s";
  compile_imp (Imp.lift ImpMutsum.imp_mutsumF_prog) "mutsumF.s";
  compile_imp (Imp.lift ImpMutsum.imp_mutsumG_prog) "mutsumG.s";
  compile_imp (Imp.lift ImpMutsum.imp_mutsumMain_prog) "mutsumMain.s";
  compile_imp (Imp.lift ImpKnot.imp_knot_prog) "knot.s";
  compile_imp (Imp.lift ImpMem1.imp_mem1_f) "mem1F.s";
  compile_imp (Imp.lift ImpMem1.imp_mem1_main) "mem1Main.s";
  compile_imp (Imp.lift ImpMem2.imp_mem2_prog) "mem2.s";
  let _link1 = (Imp2CsharpminorLink.link_imps [ImpLink.imp_linkMain_prog; ImpLink.imp_linkF_prog; ImpLink.imp_linkG_prog]) in
  match _link1 with
  | Some link1 ->
     print_endline "link1 success";
     compile_imp (link1) "link.s";
     print_endline "Done."
  | None ->
     print_endline "link1 failed";
     print_endline "Done."
