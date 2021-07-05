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

(** val imp_linkF_prog : program **)

let imp_linkF_prog =
  { name = ('L'::('i'::('n'::('k'::('F'::[]))))); ext_vars =
    (('t'::('e'::('s'::('t'::[])))) :: []); ext_funs = ((('g'::[]), (S
    O)) :: []); prog_vars = []; prog_funs = ((('f'::[]), fF) :: []) }

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

(** val imp_linkG_prog : program **)

let imp_linkG_prog =
  { name = ('L'::('i'::('n'::('k'::('G'::[]))))); ext_vars =
    (('t'::('e'::('s'::('t'::[])))) :: []); ext_funs = ((('f'::[]), (S
    O)) :: []); prog_vars = []; prog_funs = ((('g'::[]), gF) :: []) }

(** val mainF : coq_function **)

let mainF =
  { fn_params = []; fn_vars = (('r'::[]) :: (('s'::('c'::[])) :: []));
    fn_body = (Seq ((CallSys (('s'::('c'::[])),
    ('s'::('c'::('a'::('n'::[])))), [])), (Seq ((CallFun (('r'::[]),
    ('f'::[]),
    ((ImpNotations.ImpNotations.coq_Var_coerce ('s'::('c'::[]))) :: []))),
    (Seq ((CallSys (('_'::[]), ('p'::('r'::('i'::('n'::('t'::[]))))),
    ((ImpNotations.ImpNotations.coq_Var_coerce ('r'::[])) :: []))), (Assign
    (('r'::('e'::('t'::('u'::('r'::('n'::[])))))),
    (ImpNotations.ImpNotations.coq_Lit_coerce Z0))))))))) }

(** val imp_linkMain_prog : program **)

let imp_linkMain_prog =
  { name = ('L'::('i'::('n'::('k'::('M'::('a'::('i'::('n'::[]))))))));
    ext_vars = (('t'::('e'::('s'::('t'::[])))) :: []); ext_funs =
    ((('f'::[]), (S O)) :: []); prog_vars = []; prog_funs =
    ((('m'::('a'::('i'::('n'::[])))), mainF) :: []) }
