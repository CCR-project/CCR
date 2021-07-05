open BinNums
open Imp

(** val f : coq_function **)

let f =
  { fn_params = (('p'::('t'::('r'::[]))) :: []); fn_vars =
    (('p'::('t'::('r'::('V'::[])))) :: (('n'::('e'::('w'::('V'::[])))) :: []));
    fn_body = (Seq ((Load (('p'::('t'::('r'::('V'::[])))),
    (ImpNotations.ImpNotations.coq_Var_coerce ('p'::('t'::('r'::[])))))),
    (Seq ((Assign (('n'::('e'::('w'::('V'::[])))), (Mult
    ((ImpNotations.ImpNotations.coq_Lit_coerce (Zpos (Coq_xO Coq_xH))),
    (ImpNotations.ImpNotations.coq_Var_coerce ('p'::('t'::('r'::('V'::[]))))))))),
    (Store ((Plus
    ((ImpNotations.ImpNotations.coq_Var_coerce ('p'::('t'::('r'::[])))),
    (ImpNotations.ImpNotations.coq_Lit_coerce (Zpos (Coq_xO (Coq_xO (Coq_xO
      Coq_xH))))))),
    (ImpNotations.ImpNotations.coq_Var_coerce ('n'::('e'::('w'::('V'::[]))))))))))) }

(** val main : coq_function **)

let main =
  { fn_params = []; fn_vars =
    (('p'::('t'::('r'::[]))) :: (('a'::[]) :: (('b'::[]) :: []))); fn_body =
    (Seq ((Malloc (('p'::('t'::('r'::[]))),
    (ImpNotations.ImpNotations.coq_Lit_coerce (Zpos (Coq_xO (Coq_xO (Coq_xO
      (Coq_xO Coq_xH)))))))), (Seq ((Store
    ((ImpNotations.ImpNotations.coq_Var_coerce ('p'::('t'::('r'::[])))),
    (ImpNotations.ImpNotations.coq_Lit_coerce (Zpos (Coq_xO (Coq_xO (Coq_xI
      (Coq_xO Coq_xH)))))))), (Seq ((CallFun (('_'::[]), ('f'::[]),
    ((ImpNotations.ImpNotations.coq_Var_coerce ('p'::('t'::('r'::[])))) :: []))),
    (Seq ((Load (('a'::[]),
    (ImpNotations.ImpNotations.coq_Var_coerce ('p'::('t'::('r'::[])))))),
    (Seq ((Load (('b'::[]), (Plus
    ((ImpNotations.ImpNotations.coq_Var_coerce ('p'::('t'::('r'::[])))),
    (ImpNotations.ImpNotations.coq_Lit_coerce (Zpos (Coq_xO (Coq_xO (Coq_xO
      Coq_xH))))))))), (Seq ((Free
    (ImpNotations.ImpNotations.coq_Var_coerce ('p'::('t'::('r'::[]))))),
    (Assign (('r'::('e'::('t'::('u'::('r'::('n'::[])))))), (Plus
    ((ImpNotations.ImpNotations.coq_Var_coerce ('a'::[])),
    (ImpNotations.ImpNotations.coq_Var_coerce ('b'::[])))))))))))))))))) }

(** val imp_mem2_prog : program **)

let imp_mem2_prog =
  { name = ('M'::('e'::('m'::('2'::[])))); ext_vars = []; ext_funs = [];
    prog_vars = []; prog_funs = ((('m'::('a'::('i'::('n'::[])))),
    main) :: ((('f'::[]), f) :: [])) }
