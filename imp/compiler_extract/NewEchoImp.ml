open BinNums
open Datatypes
open Imp

(** val echo : coq_function **)

let echo =
  { fn_params = []; fn_vars = (('h'::[]) :: []); fn_body = (Seq ((CallFun
    (('h'::[]), ('n'::('e'::('w'::[]))), [])), (Seq ((CallFun (('_'::[]),
    ('i'::('n'::('p'::('u'::('t'::[]))))),
    ((ImpNotations.ImpNotations.coq_Var_coerce ('h'::[])) :: []))), (CallFun
    (('_'::[]), ('o'::('u'::('t'::('p'::('u'::('t'::[])))))),
    ((ImpNotations.ImpNotations.coq_Var_coerce ('h'::[])) :: []))))))) }

(** val input : coq_function **)

let input =
  { fn_params = (('h'::[]) :: []); fn_vars = (('n'::[]) :: []); fn_body =
    (Seq ((CallFun (('n'::[]), ('g'::('e'::('t'::('i'::('n'::('t'::[])))))),
    [])), (If ((Eq ((ImpNotations.ImpNotations.coq_Var_coerce ('n'::[])),
    (ImpNotations.ImpNotations.coq_Lit_coerce (Zneg Coq_xH)))), Skip, (Seq
    ((CallFun (('_'::[]), ('p'::('u'::('s'::('h'::[])))), ((Var
    ('h'::[])) :: ((Var ('n'::[])) :: [])))), (CallFun (('_'::[]),
    ('i'::('n'::('p'::('u'::('t'::[]))))),
    ((ImpNotations.ImpNotations.coq_Var_coerce ('h'::[])) :: []))))))))) }

(** val output : coq_function **)

let output =
  { fn_params = (('h'::[]) :: []); fn_vars = (('n'::[]) :: []); fn_body =
    (Seq ((CallFun (('n'::[]), ('p'::('o'::('p'::[]))), ((Var
    ('h'::[])) :: []))), (If ((Eq
    ((ImpNotations.ImpNotations.coq_Var_coerce ('n'::[])),
    (ImpNotations.ImpNotations.coq_Lit_coerce (Zneg Coq_xH)))), Skip, (Seq
    ((CallFun (('_'::[]), ('p'::('u'::('t'::('i'::('n'::('t'::[])))))), ((Var
    ('n'::[])) :: []))), (CallFun (('_'::[]),
    ('o'::('u'::('t'::('p'::('u'::('t'::[])))))),
    ((ImpNotations.ImpNotations.coq_Var_coerce ('h'::[])) :: []))))))))) }

(** val coq_Echo_prog : program **)

let coq_Echo_prog =
  { name = ('E'::('c'::('h'::('o'::[])))); ext_vars = []; ext_funs =
    ((('n'::('e'::('w'::[]))),
    O) :: ((('g'::('e'::('t'::('i'::('n'::('t'::[])))))),
    O) :: ((('p'::('u'::('t'::('i'::('n'::('t'::[])))))), (S
    O)) :: ((('p'::('u'::('s'::('h'::[])))), (S (S
    O))) :: ((('p'::('o'::('p'::[]))), (S O)) :: []))))); prog_vars = [];
    prog_funs = ((('e'::('c'::('h'::('o'::[])))),
    echo) :: ((('i'::('n'::('p'::('u'::('t'::[]))))),
    input) :: ((('o'::('u'::('t'::('p'::('u'::('t'::[])))))),
    output) :: []))) }
