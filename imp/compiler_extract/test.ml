open Diagnostics
open C
open Driveraux
open Compiler
open Imp
open Imp2Csharpminor
open Imp2Asm
(* open ImpSimple
 * open ImpFactorial
 * open ImpMutsum
 * open ImpKnot *)
(* open ImpMem1
 * open ImpMem2
 * open ImpLink *)

open StackImp
open EchoImp
open EchoMainImp
open ClientImp

(* open MWAppImp
 * open MWCImp
 * open MWMapImp *)

(** ****************************************************************** *)
(** CompCert.3.11 has major changes, and these codes are from CompCert.3.9. *)
(** ** The builtin environment *)

let re_runtime = Str.regexp "__compcert_i64_"

let ais_annot_functions =
  if Configuration.elf_target then
    [(* Ais Annotations, only available for ELF targets *)
       "__builtin_ais_annot",
     (TVoid [],
      [TPtr(TInt(IChar, [AConst]), [])],
      true);]
  else
    []


let builtins_generic_old = {
  builtin_typedefs = [];
  builtin_functions =
    ais_annot_functions
      @
    [
    (* Integer arithmetic *)
    "__builtin_bswap64",
    (TInt(IULongLong, []), [TInt(IULongLong, [])], false);
      "__builtin_bswap",
    (TInt(IUInt, []), [TInt(IUInt, [])], false);
    "__builtin_bswap32",
      (TInt(IUInt, []), [TInt(IUInt, [])], false);
    "__builtin_bswap16",
      (TInt(IUShort, []), [TInt(IUShort, [])], false);
    "__builtin_clz",
      (TInt(IInt, []), [TInt(IUInt, [])], false);
    "__builtin_clzl",
      (TInt(IInt, []), [TInt(IULong, [])], false);
    "__builtin_clzll",
      (TInt(IInt, []), [TInt(IULongLong, [])], false);
    "__builtin_ctz",
      (TInt(IInt, []), [TInt(IUInt, [])], false);
    "__builtin_ctzl",
      (TInt(IInt, []), [TInt(IULong, [])], false);
    "__builtin_ctzll",
      (TInt(IInt, []), [TInt(IULongLong, [])], false);
    (* Floating-point absolute value *)
    "__builtin_fabs",
    (TFloat(FDouble, []), [TFloat(FDouble, [])], false);
    "__builtin_fabsf",
    (TFloat(FFloat, []), [TFloat(FFloat, [])], false);
    (* Float arithmetic *)
    "__builtin_fsqrt",
    (TFloat(FDouble, []), [TFloat(FDouble, [])], false);
    "__builtin_sqrt",
    (TFloat(FDouble, []), [TFloat(FDouble, [])], false);
    (* Block copy *)
    "__builtin_memcpy_aligned",
         (TVoid [],
           [TPtr(TVoid [], []);
            TPtr(TVoid [AConst], []);
            TInt(IULong, []);
            TInt(IULong, [])],
          false);
    (* Selection *)
    "__builtin_sel",
        (TVoid [],
           [TInt(C.IBool, [])],
           true);
    (* Annotations *)
    "__builtin_annot",
        (TVoid [],
          [TPtr(TInt(IChar, [AConst]), [])],
          true);
    "__builtin_annot_intval",
        (TInt(IInt, []),
          [TPtr(TInt(IChar, [AConst]), []); TInt(IInt, [])],
          false);
    (* Software memory barrier *)
    "__builtin_membar",
        (TVoid [],
          [],
          false);
    (* Variable arguments *)
(* va_start(ap,n)
      (preprocessing) --> __builtin_va_start(ap, arg)
      (elaboration)   --> __builtin_va_start(ap) *)
    "__builtin_va_start",
        (TVoid [],
          [TPtr(TVoid [], [])],
          false);
(* va_arg(ap, ty)
      (preprocessing) --> __builtin_va_arg(ap, ty)
      (parsing)       --> __builtin_va_arg(ap, sizeof(ty)) *)
    "__builtin_va_arg",
        (TVoid [],
          [TPtr(TVoid [], []); TInt(IUInt, [])],
          false);
    "__builtin_va_copy",
        (TVoid [],
          [TPtr(TVoid [], []); TPtr(TVoid [], [])],
          false);
    "__builtin_va_end",
        (TVoid [],
          [TPtr(TVoid [], [])],
          false);
    "__compcert_va_int32",
        (TInt(IUInt, []),
          [TPtr(TVoid [], [])],
          false);
    "__compcert_va_int64",
        (TInt(IULongLong, []),
          [TPtr(TVoid [], [])],
          false);
    "__compcert_va_float64",
        (TFloat(FDouble, []),
          [TPtr(TVoid [], [])],
          false);
    "__compcert_va_composite",
        (TPtr(TVoid [], []),
          [TPtr(TVoid [], []); TInt(IULong, [])],
          false);
  (* Optimization hints *)
    "__builtin_unreachable",
        (TVoid [], [], false);
    "__builtin_expect",
        (TInt(ILong, []), [TInt(ILong, []); TInt(ILong, [])], false);
  (* Helper functions for int64 arithmetic *)
    "__compcert_i64_dtos",
        (TInt(ILongLong, []),
         [TFloat(FDouble, [])],
         false);
    "__compcert_i64_dtou",
        (TInt(IULongLong, []),
         [TFloat(FDouble, [])],
         false);
    "__compcert_i64_stod",
        (TFloat(FDouble, []),
         [TInt(ILongLong, [])],
         false);
    "__compcert_i64_utod",
        (TFloat(FDouble, []),
         [TInt(IULongLong, [])],
         false);
    "__compcert_i64_stof",
        (TFloat(FFloat, []),
         [TInt(ILongLong, [])],
         false);
    "__compcert_i64_utof",
        (TFloat(FFloat, []),
         [TInt(IULongLong, [])],
         false);
    "__compcert_i64_sdiv",
        (TInt(ILongLong, []),
         [TInt(ILongLong, []); TInt(ILongLong, [])],
         false);
    "__compcert_i64_udiv",
        (TInt(IULongLong, []),
         [TInt(IULongLong, []); TInt(IULongLong, [])],
         false);
    "__compcert_i64_smod",
        (TInt(ILongLong, []),
         [TInt(ILongLong, []); TInt(ILongLong, [])],
         false);
    "__compcert_i64_umod",
        (TInt(IULongLong, []),
         [TInt(IULongLong, []); TInt(IULongLong, [])],
         false);
    "__compcert_i64_shl",
        (TInt(ILongLong, []),
         [TInt(ILongLong, []); TInt(IInt, [])],
         false);
    "__compcert_i64_shr",
        (TInt(IULongLong, []),
         [TInt(IULongLong, []); TInt(IInt, [])],
         false);
    "__compcert_i64_sar",
        (TInt(ILongLong, []),
         [TInt(ILongLong, []); TInt(IInt, [])],
         false);
    "__compcert_i64_smulh",
        (TInt(ILongLong, []),
         [TInt(ILongLong, []); TInt(ILongLong, [])],
         false);
    "__compcert_i64_umulh",
        (TInt(IULongLong, []),
         [TInt(IULongLong, []); TInt(IULongLong, [])],
         false)
  ]
}

(** ****************************************************************** *)

(* builtin functions for CompCert compilation, ref: Velus project *)
let get_builtin (name, (out, ins, b)) =
  let env = Env.empty in
  let id' = Camlcoq.coqstring_of_camlstring name in
  let targs = List.map (C2C.convertTyp env) ins
                |> Imp2Asm.list_type_to_typelist in
  let tres = C2C.convertTyp env out in
  let sg = Ctypes.signature_of_type targs tres AST.cc_default in
  let ef =
    if name = "malloc" then AST.EF_malloc else
    if name = "free" then AST.EF_free else
    if Str.string_match re_runtime name 0 then AST.EF_runtime(id', sg) else
    if Str.string_match C2C.re_builtin name 0
    && List.mem_assoc name C2C.builtins.builtin_functions
    then AST.EF_builtin(id', sg)
    else AST.EF_external(id', sg) in
  let decl = (id', ef) in
  decl

let builtins =
  List.map get_builtin builtins_generic_old.builtin_functions


(* Imp program compilations *)
let compile_imp p ofile =
  (* Convert Imp to Asm *)
  let i2a =
    (Compiler.apply_partial
       (Imp2Asm.compile_imp builtins p)
       Asmexpand.expand_program) in
  match i2a with
  | Errors.OK asm ->
     (* Print Asm in text form *)
     let oc = open_out ofile in
     PrintAsm.print_program oc asm;
     close_out oc
  | Errors.Error msg ->
     let loc = file_loc ofile in
     fatal_error loc "%a"  print_error msg


(* Imp programL compilations for linked imps *)
let compile_impL p ofile =
  (* Convert Imp to Csharpminor *)
  let i2a =
    (Compiler.apply_partial
       (Imp2Asm.compile builtins p)
       Asmexpand.expand_program) in
  match i2a with
  | Errors.OK asm ->
     (* Print Asm in text form *)
     let oc = open_out ofile in
     PrintAsm.print_program oc asm;
     close_out oc
  | Errors.Error msg ->
     let loc = file_loc ofile in
     fatal_error loc "%a"  print_error msg



let main =
  print_endline "Start Imp compilations...";
  (* compile_imp (MWAppImp.coq_Appprog) "MWApp.s";
   * compile_imp (MWCImp.coq_MWprog) "MWC.s";
   * compile_imp (MWMapImp.coq_Map_prog) "MWMap.s";
   * print_endline "MW Done!"; *)
  compile_imp (StackImp.coq_Stack_prog) "stack.s";
  compile_imp (EchoImp.coq_Echo_prog) "echo.s";
  compile_imp (EchoMainImp.coq_EchoMain_prog) "echo_main.s";
  compile_imp (ClientImp.coq_Client_prog) "client.s";
  print_endline "Echo Done!";
  (* compile_imp (ImpSimple.imp_simple_prog) "simple.s";
   * compile_imp (ImpFactorial.imp_factorial_prog) "factorial.s";
   * compile_imp (ImpMutsum.imp_mutsumF_prog) "mutsumF.s";
   * compile_imp (ImpMutsum.imp_mutsumG_prog) "mutsumG.s";
   * compile_imp (ImpMutsum.imp_mutsumMain_prog) "mutsumMain.s";
   * compile_imp (ImpKnot.imp_knot_prog) "knot.s";
   * compile_imp (ImpMem1.imp_mem1_f) "mem1F.s";
   * compile_imp (ImpMem1.imp_mem1_main) "mem1Main.s";
   * compile_imp (ImpMem2.imp_mem2_prog) "mem2.s";  *)

  (* let _link1 =
   *   (Imp2Csharpminor.link_imps builtins
   *      [ImpLink.imp_linkMain_prog; ImpLink.imp_linkF_prog; ImpLink.imp_linkG_prog]) in
   * match _link1 with
   * | Some link1 ->
   *    print_endline "link1 succeed.";
   *    compile_impL (link1) "link.s";
   *    print_endline "Done!"
   * | None ->
   *    print_endline "link1 failed.";
   *    print_endline "Done!" *)
