open BinNums
open Datatypes
open Imp

(** val main : coq_function **)

let main =
  { fn_params = []; fn_vars = []; fn_body = (Seq ((CallFun (('_'::[]),
    ('e'::('c'::('h'::('o'::[])))), [])), (Assign
    (('r'::('e'::('t'::('u'::('r'::('n'::[])))))),
    (ImpNotations.ImpNotations.coq_Lit_coerce Z0))))) }

(** val coq_EchoMain_prog : program **)

let coq_EchoMain_prog =
  { name = ('m'::('a'::('i'::('n'::[])))); ext_vars = []; ext_funs =
    ((('e'::('c'::('h'::('o'::[])))), O) :: []); prog_vars = []; prog_funs =
    ((('m'::('a'::('i'::('n'::[])))), main) :: []) }
