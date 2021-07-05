open BinNums
open Imp

(** val factorial : stmt **)

let factorial =
  Seq ((AddrOf (('f'::('p'::('t'::('r'::[])))),
    ('f'::('a'::('c'::('t'::('o'::('r'::('i'::('a'::('l'::[]))))))))))), (Seq
    ((If ((ImpNotations.ImpNotations.coq_Var_coerce ('n'::[])), (Seq
    ((CallPtr (('o'::('u'::('t'::('p'::('u'::('t'::[])))))),
    (ImpNotations.ImpNotations.coq_Var_coerce ('f'::('p'::('t'::('r'::[]))))),
    ((Minus ((ImpNotations.ImpNotations.coq_Var_coerce ('n'::[])),
    (ImpNotations.ImpNotations.coq_Lit_coerce (Zpos Coq_xH)))) :: []))),
    (Assign (('o'::('u'::('t'::('p'::('u'::('t'::[])))))), (Mult
    ((ImpNotations.ImpNotations.coq_Var_coerce ('n'::[])),
    (ImpNotations.ImpNotations.coq_Var_coerce
      ('o'::('u'::('t'::('p'::('u'::('t'::[]))))))))))))), (Assign
    (('o'::('u'::('t'::('p'::('u'::('t'::[])))))),
    (ImpNotations.ImpNotations.coq_Lit_coerce (Zpos Coq_xH)))))), (Assign
    (('r'::('e'::('t'::('u'::('r'::('n'::[])))))),
    (ImpNotations.ImpNotations.coq_Var_coerce
      ('o'::('u'::('t'::('p'::('u'::('t'::[]))))))))))))

(** val factorial_fundef : coq_function **)

let factorial_fundef =
  { fn_params = (('n'::[]) :: []); fn_vars =
    (('o'::('u'::('t'::('p'::('u'::('t'::[])))))) :: (('f'::('p'::('t'::('r'::[])))) :: []));
    fn_body = factorial }

(** val main : stmt **)

let main =
  Seq ((Assign (('i'::('n'::[])),
    (ImpNotations.ImpNotations.coq_Lit_coerce (Zpos (Coq_xO (Coq_xO Coq_xH)))))),
    (Seq ((CallFun (('r'::('e'::('s'::('u'::('l'::('t'::[])))))),
    ('f'::('a'::('c'::('t'::('o'::('r'::('i'::('a'::('l'::[]))))))))),
    ((ImpNotations.ImpNotations.coq_Var_coerce ('i'::('n'::[]))) :: []))),
    (Assign (('r'::('e'::('t'::('u'::('r'::('n'::[])))))),
    (ImpNotations.ImpNotations.coq_Var_coerce
      ('r'::('e'::('s'::('u'::('l'::('t'::[]))))))))))))

(** val main_fundef : coq_function **)

let main_fundef =
  { fn_params = []; fn_vars =
    (('i'::('n'::[])) :: (('r'::('e'::('s'::('u'::('l'::('t'::[])))))) :: []));
    fn_body = main }

(** val imp_factorial_prog : program **)

let imp_factorial_prog =
  { name = ('F'::('a'::('c'::('t'::('o'::('r'::('i'::('a'::('l'::[])))))))));
    ext_vars = []; ext_funs = []; prog_vars = []; prog_funs =
    ((('f'::('a'::('c'::('t'::('o'::('r'::('i'::('a'::('l'::[]))))))))),
    factorial_fundef) :: ((('m'::('a'::('i'::('n'::[])))),
    main_fundef) :: [])) }
