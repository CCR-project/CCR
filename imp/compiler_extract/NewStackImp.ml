open BinNums
open Imp

(** val coq_new : coq_function **)

let coq_new =
  { fn_params = []; fn_vars =
    (('n'::('e'::('w'::('_'::('n'::('o'::('d'::('e'::[])))))))) :: []);
    fn_body = (Seq ((Malloc
    (('n'::('e'::('w'::('_'::('n'::('o'::('d'::('e'::[])))))))),
    (ImpNotations.ImpNotations.coq_Lit_coerce (Zpos Coq_xH)))), (Seq ((Store
    ((ImpNotations.ImpNotations.coq_Var_coerce
       ('n'::('e'::('w'::('_'::('n'::('o'::('d'::('e'::[]))))))))),
    (ImpNotations.ImpNotations.coq_Lit_coerce Z0))), (Assign
    (('r'::('e'::('t'::('u'::('r'::('n'::[])))))),
    (ImpNotations.ImpNotations.coq_Var_coerce
      ('n'::('e'::('w'::('_'::('n'::('o'::('d'::('e'::[]))))))))))))))) }

(** val pop : coq_function **)

let pop =
  { fn_params = (('s'::('t'::('k'::[]))) :: []); fn_vars =
    (('h'::('d'::[])) :: (('b'::[]) :: (('v'::[]) :: (('n'::('e'::('x'::('t'::[])))) :: []))));
    fn_body = (Seq ((Load (('h'::('d'::[])),
    (ImpNotations.ImpNotations.coq_Var_coerce ('s'::('t'::('k'::[])))))),
    (Seq ((Cmp (('b'::[]),
    (ImpNotations.ImpNotations.coq_Var_coerce ('h'::('d'::[]))),
    (ImpNotations.ImpNotations.coq_Lit_coerce Z0))), (If
    ((ImpNotations.ImpNotations.coq_Var_coerce ('b'::[])), (Assign
    (('r'::('e'::('t'::('u'::('r'::('n'::[])))))),
    (ImpNotations.ImpNotations.coq_Lit_coerce (Zneg Coq_xH)))), (Seq ((Load
    (('v'::[]),
    (ImpNotations.ImpNotations.coq_Var_coerce ('h'::('d'::[]))))), (Seq
    ((Load (('n'::('e'::('x'::('t'::[])))), (Plus
    ((ImpNotations.ImpNotations.coq_Var_coerce ('h'::('d'::[]))),
    (ImpNotations.ImpNotations.coq_Lit_coerce (Zpos (Coq_xO (Coq_xO (Coq_xO
      Coq_xH))))))))), (Seq ((Free
    (ImpNotations.ImpNotations.coq_Var_coerce ('h'::('d'::[])))), (Seq ((Free
    (Plus ((ImpNotations.ImpNotations.coq_Var_coerce ('h'::('d'::[]))),
    (ImpNotations.ImpNotations.coq_Lit_coerce (Zpos (Coq_xO (Coq_xO (Coq_xO
      Coq_xH)))))))), (Seq ((Store
    ((ImpNotations.ImpNotations.coq_Var_coerce ('s'::('t'::('k'::[])))),
    (ImpNotations.ImpNotations.coq_Var_coerce ('n'::('e'::('x'::('t'::[]))))))),
    (Assign (('r'::('e'::('t'::('u'::('r'::('n'::[])))))),
    (ImpNotations.ImpNotations.coq_Var_coerce ('v'::[])))))))))))))))))))) }

(** val push : coq_function **)

let push =
  { fn_params = (('s'::('t'::('k'::[]))) :: (('v'::[]) :: [])); fn_vars =
    (('n'::('e'::('w'::('_'::('n'::('o'::('d'::('e'::[])))))))) :: (('a'::('d'::('d'::('r'::('_'::('n'::('e'::('x'::('t'::[]))))))))) :: (('h'::('d'::[])) :: [])));
    fn_body = (Seq ((Malloc
    (('n'::('e'::('w'::('_'::('n'::('o'::('d'::('e'::[])))))))),
    (ImpNotations.ImpNotations.coq_Lit_coerce (Zpos (Coq_xO Coq_xH))))), (Seq
    ((Assign
    (('a'::('d'::('d'::('r'::('_'::('n'::('e'::('x'::('t'::[]))))))))), (Plus
    ((ImpNotations.ImpNotations.coq_Var_coerce
       ('n'::('e'::('w'::('_'::('n'::('o'::('d'::('e'::[]))))))))),
    (ImpNotations.ImpNotations.coq_Lit_coerce (Zpos (Coq_xO (Coq_xO (Coq_xO
      Coq_xH))))))))), (Seq ((Load (('h'::('d'::[])),
    (ImpNotations.ImpNotations.coq_Var_coerce ('s'::('t'::('k'::[])))))),
    (Seq ((Store
    ((ImpNotations.ImpNotations.coq_Var_coerce
       ('n'::('e'::('w'::('_'::('n'::('o'::('d'::('e'::[]))))))))),
    (ImpNotations.ImpNotations.coq_Var_coerce ('v'::[])))), (Seq ((Store
    ((ImpNotations.ImpNotations.coq_Var_coerce
       ('a'::('d'::('d'::('r'::('_'::('n'::('e'::('x'::('t'::[])))))))))),
    (ImpNotations.ImpNotations.coq_Var_coerce ('h'::('d'::[]))))), (Store
    ((ImpNotations.ImpNotations.coq_Var_coerce ('s'::('t'::('k'::[])))),
    (ImpNotations.ImpNotations.coq_Var_coerce
      ('n'::('e'::('w'::('_'::('n'::('o'::('d'::('e'::[]))))))))))))))))))))) }

(** val coq_Stack_prog : program **)

let coq_Stack_prog =
  { name = ('S'::('t'::('a'::('c'::('k'::[]))))); ext_vars = []; ext_funs =
    []; prog_vars = []; prog_funs = ((('n'::('e'::('w'::[]))),
    coq_new) :: ((('p'::('o'::('p'::[]))),
    pop) :: ((('p'::('u'::('s'::('h'::[])))), push) :: []))) }
