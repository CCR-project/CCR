open BinNums
open Datatypes
open Imp

(** val fF : coq_function **)

let fF =
  { fn_params = (('n'::[]) :: []); fn_vars =
    (('g'::('_'::('r'::('e'::('t'::[]))))) :: []); fn_body = (If
    ((ImpNotations.ImpNotations.coq_Var_coerce ('n'::[])), (Seq ((CallFun
    (('g'::('_'::('r'::('e'::('t'::[]))))), ('g'::[]), ((Minus
    ((ImpNotations.ImpNotations.coq_Var_coerce ('n'::[])),
    (ImpNotations.ImpNotations.coq_Lit_coerce (Zpos Coq_xH)))) :: []))),
    (Assign (('r'::('e'::('t'::('u'::('r'::('n'::[])))))), (Plus
    ((ImpNotations.ImpNotations.coq_Var_coerce ('n'::[])),
    (ImpNotations.ImpNotations.coq_Var_coerce
      ('g'::('_'::('r'::('e'::('t'::[])))))))))))), (Assign
    (('r'::('e'::('t'::('u'::('r'::('n'::[])))))),
    (ImpNotations.ImpNotations.coq_Lit_coerce Z0))))) }

(** val imp_mutsumF_prog : program **)

let imp_mutsumF_prog =
  { name = ('M'::('u'::('t'::('S'::('u'::('m'::('F'::[]))))))); ext_vars =
    []; ext_funs = ((('g'::[]), (S O)) :: []); prog_vars = []; prog_funs =
    ((('f'::[]), fF) :: []) }

(** val gF : coq_function **)

let gF =
  { fn_params = (('n'::[]) :: []); fn_vars =
    (('f'::('_'::('r'::('e'::('t'::[]))))) :: []); fn_body = (If
    ((ImpNotations.ImpNotations.coq_Var_coerce ('n'::[])), (Seq ((CallFun
    (('f'::('_'::('r'::('e'::('t'::[]))))), ('f'::[]), ((Minus
    ((ImpNotations.ImpNotations.coq_Var_coerce ('n'::[])),
    (ImpNotations.ImpNotations.coq_Lit_coerce (Zpos Coq_xH)))) :: []))),
    (Assign (('r'::('e'::('t'::('u'::('r'::('n'::[])))))), (Plus
    ((ImpNotations.ImpNotations.coq_Var_coerce ('n'::[])),
    (ImpNotations.ImpNotations.coq_Var_coerce
      ('f'::('_'::('r'::('e'::('t'::[])))))))))))), (Assign
    (('r'::('e'::('t'::('u'::('r'::('n'::[])))))),
    (ImpNotations.ImpNotations.coq_Lit_coerce Z0))))) }

(** val imp_mutsumG_prog : program **)

let imp_mutsumG_prog =
  { name = ('M'::('u'::('t'::('S'::('u'::('m'::('G'::[]))))))); ext_vars =
    []; ext_funs = ((('f'::[]), (S O)) :: []); prog_vars = []; prog_funs =
    ((('g'::[]), gF) :: []) }

(** val mainF : coq_function **)

let mainF =
  { fn_params = []; fn_vars = (('r'::[]) :: []); fn_body = (Seq ((CallFun
    (('r'::[]), ('f'::[]),
    ((ImpNotations.ImpNotations.coq_Lit_coerce (Zpos (Coq_xO (Coq_xI (Coq_xO
       Coq_xH))))) :: []))), (Assign
    (('r'::('e'::('t'::('u'::('r'::('n'::[])))))),
    (ImpNotations.ImpNotations.coq_Var_coerce ('r'::[])))))) }

(** val imp_mutsumMain_prog : program **)

let imp_mutsumMain_prog =
  { name =
    ('M'::('u'::('t'::('S'::('u'::('m'::('M'::('a'::('i'::('n'::[]))))))))));
    ext_vars = []; ext_funs = ((('f'::[]), (S O)) :: []); prog_vars = [];
    prog_funs = ((('m'::('a'::('i'::('n'::[])))), mainF) :: []) }
