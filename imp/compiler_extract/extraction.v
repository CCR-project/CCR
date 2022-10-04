From compcert Require
     Coqlib Wfsimpl AST Iteration Floats Compiler
     SelectLong Selection RTLgen Inlining ValueDomain Tailcall Allocation
     Bounds Ctypes Csyntax Ctyping Csharpminor Compiler Parser Initializers.

Require Import ClassicalDescription.
Require Coq.extraction.Extraction.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

Require Import Imp ImpNotations.
Require Import Imp2Csharpminor.
(* Require Import Csharpminor2Asm. *)
Require Import Imp2Asm.

(************************************)
(* example programs for compilation *)
(* Require Import ImpSimple. *)
(* Require Import ImpFactorial. *)
(* Require Import ImpMutsum. *)
(* Require Import ImpKnot. *)
(* Require Import ImpMem1. *)
(* Require Import ImpMem2. *)
(* Require Import ImpLink. *)
Require Import StackImp EchoImp EchoMainImp ClientImp.
(* Require Import MWAppImp MWCImp MWMapImp. *)
(************************************)

Extract Constant excluded_middle_informative => "true".

Extract Constant s2p => "(fun str -> Camlcoq.(str |> camlstring_of_coqstring |> intern_string))".

(* Coqlib *)
Extract Inlined Constant Coqlib.proj_sumbool => "(fun x -> x)".

(* Datatypes *)
Extract Inlined Constant Datatypes.fst => "fst".
Extract Inlined Constant Datatypes.snd => "snd".

(* Wfsimpl *)
Extraction Inline Wfsimpl.Fix Wfsimpl.Fixm.

(* Memory - work around an extraction bug. *)
Extraction NoInline Memory.Mem.valid_pointer.

(* Errors *)
Extraction Inline Errors.bind Errors.bind2.

(* Iteration *)

Extract Constant Iteration.GenIter.iterate =>
  "let rec iter f a =
     match f a with Coq_inl b -> Some b | Coq_inr a' -> iter f a'
   in iter".

(* Selection *)

Extract Constant Selection.compile_switch => "Switchaux.compile_switch".
Extract Constant Selection.if_conversion_heuristic => "Selectionaux.if_conversion_heuristic".

(* RTLgen *)
Extract Constant RTLgen.more_likely => "RTLgenaux.more_likely".
Extraction Inline RTLgen.ret RTLgen.error RTLgen.bind RTLgen.bind2.

(* Inlining *)
Extract Inlined Constant Inlining.should_inline => "Inliningaux.should_inline".
Extract Inlined Constant Inlining.inlining_info => "Inliningaux.inlining_info".
Extract Inlined Constant Inlining.inlining_analysis => "Inliningaux.inlining_analysis".
Extraction Inline Inlining.ret Inlining.bind.

(* Allocation *)
Extract Constant Allocation.regalloc => "Regalloc.regalloc".

(* Linearize *)
Extract Constant Linearize.enumerate_aux => "Linearizeaux.enumerate_aux".

(* SimplExpr *)
Extract Constant SimplExpr.first_unused_ident => "Camlcoq.first_unused_ident".
Extraction Inline SimplExpr.ret SimplExpr.error SimplExpr.bind SimplExpr.bind2.

(* Compopts *)
Extract Constant Compopts.optim_for_size =>
  "fun _ -> !Clflags.option_Osize".
Extract Constant Compopts.va_strict =>
  "fun _ -> false".
Extract Constant Compopts.propagate_float_constants =>
  "fun _ -> !Clflags.option_ffloatconstprop >= 1".
Extract Constant Compopts.generate_float_constants =>
  "fun _ -> !Clflags.option_ffloatconstprop >= 2".
Extract Constant Compopts.optim_tailcalls =>
  "fun _ -> !Clflags.option_ftailcalls".
Extract Constant Compopts.optim_constprop =>
  "fun _ -> !Clflags.option_fconstprop".
Extract Constant Compopts.optim_CSE =>
  "fun _ -> !Clflags.option_fcse".
Extract Constant Compopts.optim_redundancy =>
  "fun _ -> !Clflags.option_fredundancy".
Extract Constant Compopts.thumb =>
  "fun _ -> !Clflags.option_mthumb".
Extract Constant Compopts.debug =>
  "fun _ -> !Clflags.option_g".

(* Compiler *)
Extract Constant Compiler.print_Clight => "PrintClight.print_if".
Extract Constant Compiler.print_Cminor => "PrintCminor.print_if".
Extract Constant Compiler.print_RTL => "PrintRTL.print_if".
Extract Constant Compiler.print_LTL => "PrintLTL.print_if".
Extract Constant Compiler.print_Mach => "PrintMach.print_if".
Extract Constant Compiler.print => "fun (f: 'a -> unit) (x: 'a) -> f x; x".
Extract Constant Compiler.time  => "Timing.time_coq".

(*Extraction Inline Compiler.apply_total Compiler.apply_partial.*)

(* Cabs *)
Extract Constant Cabs.loc =>
"{ lineno : int;
   filename: string;
   byteno: int;
   ident : int;
 }".
Extract Inlined Constant Cabs.string => "String.t".
Extract Constant Cabs.char_code => "int64".

(* Processor-specific extraction directives *)

Load extractionMachdep.

(* Avoid name clashes *)
Extraction Blacklist List String Int.

(* Cutting the dependency to R. *)
Extract Inlined Constant Defs.F2R => "fun _ -> assert false".
Extract Inlined Constant Binary.FF2R => "fun _ -> assert false".
Extract Inlined Constant Binary.B2R => "fun _ -> assert false".
Extract Inlined Constant BinarySingleNaN.round_mode => "fun _ -> assert false".
Extract Inlined Constant Bracket.inbetween_loc => "fun _ -> assert false".

(* Needed in Coq 8.4 to avoid problems with Function definitions. *)
Set Extraction AccessOpaque.

(* Go! *)

Cd "imp/compiler_extract".

Separate Extraction
   (* Compiler.transf_c_program *)
   Compiler.transf_cminor_program
   Cexec.do_initial_state Cexec.do_step Cexec.at_final_state
   Ctypes.merge_attributes Ctypes.remove_attributes Ctypes.build_composite_env
   Initializers.transl_init Initializers.constval
   (* Csyntax.Eindex Csyntax.Epreincr Csyntax.Eselection *)
   Ctyping.typecheck_program
   Ctyping.epostincr Ctyping.epostdecr Ctyping.epreincr Ctyping.epredecr
   Ctyping.eselection
   Ctypes.make_program
   Clight.type_of_function
   Conventions1.callee_save_type Conventions1.is_float_reg
   Conventions1.int_caller_save_regs Conventions1.float_caller_save_regs
   Conventions1.int_callee_save_regs Conventions1.float_callee_save_regs
   Conventions1.dummy_int_reg Conventions1.dummy_float_reg
   RTL.instr_defs RTL.instr_uses
   Machregs.mregs_for_operation Machregs.mregs_for_builtin
   Machregs.two_address_op Machregs.is_stack_reg
   Machregs.destroyed_at_indirect_call
   AST.signature_main
   Floats.Float32.from_parsed Floats.Float.from_parsed
   Globalenvs.Senv.invert_symbol
   (* Parser.translation_unit_file *)
   (* For imp compilation *)
   Compiler.transf_clight_program
   Imp2Asm.list_type_to_typelist
   (* Csharpminor2Asm.transf_csharpminor_program *)
   Imp2Asm.compile
   Imp2Asm.compile_imp
   Imp2Csharpminor.link_imps
   (* test programs written in Imp *)
   (* imp_factorial_prog *)
   (* imp_simple_prog *)
   (* imp_mutsumF_prog imp_mutsumG_prog imp_mutsumMain_prog *)
   (* imp_knot_prog *)
   (* imp_mem1_f imp_mem1_main *)
   (* imp_mem2_prog *)
   (* imp_linkF_prog imp_linkG_prog imp_linkMain_prog *)
   Stack_prog Echo_prog EchoMain_prog Client_prog
   (* Appprog MWprog Map_prog *)
.

Cd "../..".
