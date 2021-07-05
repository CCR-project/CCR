open BinNums
open Datatypes
open Imp

(** val f : coq_function **)

let f =
  { fn_params = []; fn_vars =
    (('G'::('P'::[])) :: (('r'::('e'::('t'::[]))) :: [])); fn_body = (Seq
    ((AddrOf (('G'::('P'::[])), ('G'::[]))), (Seq ((Store
    ((ImpNotations.ImpNotations.coq_Var_coerce ('G'::('P'::[]))),
    (ImpNotations.ImpNotations.coq_Lit_coerce (Zpos (Coq_xI (Coq_xI (Coq_xI
      (Coq_xO (Coq_xI Coq_xH))))))))), (Seq ((Load (('r'::('e'::('t'::[]))),
    (ImpNotations.ImpNotations.coq_Var_coerce ('G'::('P'::[]))))), (Assign
    (('r'::('e'::('t'::('u'::('r'::('n'::[])))))),
    (ImpNotations.ImpNotations.coq_Var_coerce ('r'::('e'::('t'::[])))))))))))) }

(** val imp_mem1_f : program **)

let imp_mem1_f =
  { name = ('M'::('e'::('m'::('1'::('F'::[]))))); ext_vars =
    (('G'::[]) :: []); ext_funs = []; prog_vars = []; prog_funs =
    ((('f'::[]), f) :: []) }

(** val main : stmt **)

let main =
  Seq ((AddrOf (('G'::('P'::[])), ('G'::[]))), (Seq ((Store
    ((ImpNotations.ImpNotations.coq_Var_coerce ('G'::('P'::[]))),
    (ImpNotations.ImpNotations.coq_Lit_coerce (Zpos (Coq_xI (Coq_xO (Coq_xO
      (Coq_xO (Coq_xO Coq_xH))))))))), (Seq ((CallFun
    (('r'::('e'::('t'::[]))), ('f'::[]), [])), (Seq ((Load
    (('G'::('v'::('a'::('l'::[])))),
    (ImpNotations.ImpNotations.coq_Var_coerce ('G'::('P'::[]))))), (Assign
    (('r'::('e'::('t'::('u'::('r'::('n'::[])))))),
    (ImpNotations.ImpNotations.coq_Var_coerce ('G'::('v'::('a'::('l'::[]))))))))))))))

(** val main_def : coq_function **)

let main_def =
  { fn_params = []; fn_vars =
    (('G'::('P'::[])) :: (('r'::('e'::('t'::[]))) :: (('G'::('v'::('a'::('l'::[])))) :: [])));
    fn_body = main }

(** val imp_mem1_main : program **)

let imp_mem1_main =
  { name = ('M'::('e'::('m'::('1'::('M'::('a'::('i'::('n'::[]))))))));
    ext_vars = []; ext_funs = ((('f'::[]), O) :: []); prog_vars =
    ((('G'::[]), (Zpos (Coq_xI Coq_xH))) :: []); prog_funs =
    ((('m'::('a'::('i'::('n'::[])))), main_def) :: []) }
