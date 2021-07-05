open BinNums
open Imp

(** val coq_rec : coq_function **)

let coq_rec =
  { fn_params = (('n'::[]) :: []); fn_vars =
    (('_'::('f'::('A'::[]))) :: (('_'::('f'::('P'::[]))) :: (('r'::('e'::('c'::('P'::[])))) :: (('r'::('e'::('t'::[]))) :: []))));
    fn_body = (Seq ((AddrOf (('_'::('f'::('A'::[]))), ('_'::('f'::[])))),
    (Seq ((Load (('_'::('f'::('P'::[]))),
    (ImpNotations.ImpNotations.coq_Var_coerce ('_'::('f'::('A'::[])))))),
    (Seq ((AddrOf (('r'::('e'::('c'::('P'::[])))), ('r'::('e'::('c'::[]))))),
    (Seq ((CallPtr (('r'::('e'::('t'::[]))),
    (ImpNotations.ImpNotations.coq_Var_coerce ('_'::('f'::('P'::[])))),
    ((ImpNotations.ImpNotations.coq_Var_coerce ('r'::('e'::('c'::('P'::[]))))) :: (
    (ImpNotations.ImpNotations.coq_Var_coerce ('n'::[])) :: [])))), (Assign
    (('r'::('e'::('t'::('u'::('r'::('n'::[])))))),
    (ImpNotations.ImpNotations.coq_Var_coerce ('r'::('e'::('t'::[])))))))))))))) }

(** val knot : coq_function **)

let knot =
  { fn_params = (('f'::('P'::[])) :: []); fn_vars =
    (('_'::('f'::('A'::[]))) :: (('r'::('e'::('c'::('P'::[])))) :: []));
    fn_body = (Seq ((AddrOf (('_'::('f'::('A'::[]))), ('_'::('f'::[])))),
    (Seq ((Store
    ((ImpNotations.ImpNotations.coq_Var_coerce ('_'::('f'::('A'::[])))),
    (ImpNotations.ImpNotations.coq_Var_coerce ('f'::('P'::[]))))), (Seq
    ((AddrOf (('r'::('e'::('c'::('P'::[])))), ('r'::('e'::('c'::[]))))),
    (Assign (('r'::('e'::('t'::('u'::('r'::('n'::[])))))),
    (ImpNotations.ImpNotations.coq_Var_coerce ('r'::('e'::('c'::('P'::[]))))))))))))) }

(** val _fib : coq_function **)

let _fib =
  { fn_params = (('f'::('i'::('b'::('P'::[])))) :: (('n'::[]) :: []));
    fn_vars = (('a'::[]) :: (('b'::[]) :: [])); fn_body = (If
    ((ImpNotations.ImpNotations.coq_Var_coerce ('n'::[])), (If ((Minus
    ((ImpNotations.ImpNotations.coq_Var_coerce ('n'::[])),
    (ImpNotations.ImpNotations.coq_Lit_coerce (Zpos Coq_xH)))), (Seq
    ((CallPtr (('a'::[]),
    (ImpNotations.ImpNotations.coq_Var_coerce ('f'::('i'::('b'::('P'::[]))))),
    ((Minus ((ImpNotations.ImpNotations.coq_Var_coerce ('n'::[])),
    (ImpNotations.ImpNotations.coq_Lit_coerce (Zpos Coq_xH)))) :: []))), (Seq
    ((CallPtr (('b'::[]),
    (ImpNotations.ImpNotations.coq_Var_coerce ('f'::('i'::('b'::('P'::[]))))),
    ((Minus ((ImpNotations.ImpNotations.coq_Var_coerce ('n'::[])),
    (ImpNotations.ImpNotations.coq_Lit_coerce (Zpos (Coq_xO Coq_xH))))) :: []))),
    (Assign (('r'::('e'::('t'::('u'::('r'::('n'::[])))))), (Plus
    ((ImpNotations.ImpNotations.coq_Var_coerce ('a'::[])),
    (ImpNotations.ImpNotations.coq_Var_coerce ('b'::[])))))))))), (Assign
    (('r'::('e'::('t'::('u'::('r'::('n'::[])))))),
    (ImpNotations.ImpNotations.coq_Lit_coerce (Zpos Coq_xH)))))), (Assign
    (('r'::('e'::('t'::('u'::('r'::('n'::[])))))),
    (ImpNotations.ImpNotations.coq_Lit_coerce (Zpos Coq_xH)))))) }

(** val main : coq_function **)

let main =
  { fn_params = []; fn_vars =
    (('_'::('f'::('i'::('b'::('P'::[]))))) :: (('f'::('i'::('b'::('P'::[])))) :: (('r'::('e'::('t'::[]))) :: [])));
    fn_body = (Seq ((AddrOf (('_'::('f'::('i'::('b'::('P'::[]))))),
    ('_'::('f'::('i'::('b'::[])))))), (Seq ((CallFun
    (('f'::('i'::('b'::('P'::[])))), ('k'::('n'::('o'::('t'::[])))),
    ((ImpNotations.ImpNotations.coq_Var_coerce
       ('_'::('f'::('i'::('b'::('P'::[])))))) :: []))), (Seq ((CallPtr
    (('r'::('e'::('t'::[]))),
    (ImpNotations.ImpNotations.coq_Var_coerce ('f'::('i'::('b'::('P'::[]))))),
    ((ImpNotations.ImpNotations.coq_Lit_coerce (Zpos (Coq_xO (Coq_xI (Coq_xO
       Coq_xH))))) :: []))), (Assign
    (('r'::('e'::('t'::('u'::('r'::('n'::[])))))),
    (ImpNotations.ImpNotations.coq_Var_coerce ('r'::('e'::('t'::[])))))))))))) }

(** val imp_knot_prog : program **)

let imp_knot_prog =
  { name = ('K'::('n'::('o'::('t'::[])))); ext_vars = []; ext_funs = [];
    prog_vars = ((('_'::('f'::[])), Z0) :: []); prog_funs =
    ((('r'::('e'::('c'::[]))), coq_rec) :: ((('k'::('n'::('o'::('t'::[])))),
    knot) :: ((('_'::('f'::('i'::('b'::[])))),
    _fib) :: ((('m'::('a'::('i'::('n'::[])))), main) :: [])))) }
