open Imp

(** val getint : coq_function **)

let getint =
  { fn_params = []; fn_vars = (('r'::('e'::('t'::[]))) :: []); fn_body = (Seq
    ((CallSys (('r'::('e'::('t'::[]))), ('s'::('c'::('a'::('n'::[])))), [])),
    (Assign (('r'::('e'::('t'::('u'::('r'::('n'::[])))))),
    (ImpNotations.ImpNotations.coq_Var_coerce ('r'::('e'::('t'::[])))))))) }

(** val putint : coq_function **)

let putint =
  { fn_params = (('v'::[]) :: []); fn_vars = []; fn_body = (CallSys
    (('_'::[]), ('p'::('r'::('i'::('n'::('t'::[]))))),
    ((ImpNotations.ImpNotations.coq_Var_coerce ('v'::[])) :: []))) }

(** val coq_Client_prog : program **)

let coq_Client_prog =
  { name = ('C'::('l'::('i'::('e'::('n'::('t'::[])))))); ext_vars = [];
    ext_funs = []; prog_vars = []; prog_funs =
    ((('g'::('e'::('t'::('i'::('n'::('t'::[])))))),
    getint) :: ((('p'::('u'::('t'::('i'::('n'::('t'::[])))))),
    putint) :: [])) }
