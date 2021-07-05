open BinNums
open Imp

(** val main : stmt **)

let main =
  Assign (('r'::('e'::('t'::('u'::('r'::('n'::[])))))),
    (ImpNotations.ImpNotations.coq_Lit_coerce (Zpos (Coq_xI (Coq_xI (Coq_xO
      (Coq_xO (Coq_xO (Coq_xI Coq_xH)))))))))

(** val main_fundef : coq_function **)

let main_fundef =
  { fn_params = []; fn_vars = []; fn_body = main }

(** val imp_simple_prog : program **)

let imp_simple_prog =
  { name = ('S'::('i'::('m'::('p'::('l'::('e'::[])))))); ext_vars = [];
    ext_funs = []; prog_vars = []; prog_funs =
    ((('m'::('a'::('i'::('n'::[])))), main_fundef) :: []) }
