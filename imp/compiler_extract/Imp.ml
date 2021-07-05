open AList
open BinNums
open Datatypes
open List0
open RelDec
open Skeleton

type var = char list

type expr =
| Var of var
| Lit of coq_Z
| Eq of expr * expr
| Lt of expr * expr
| Plus of expr * expr
| Minus of expr * expr
| Mult of expr * expr

type stmt =
| Skip
| Assign of var * expr
| Seq of stmt * stmt
| If of expr * stmt * stmt
| CallFun of var * char list * expr list
| CallPtr of var * expr * expr list
| CallSys of var * char list * expr list
| AddrOf of var * char list
| Malloc of var * expr
| Free of expr
| Load of var * expr
| Store of expr * expr
| Cmp of var * expr * expr

type coq_function = { fn_params : var list; fn_vars : var list; fn_body : stmt }

(** val call_ban : char list -> bool **)

let call_ban f =
  (||)
    ((||)
      ((||)
        ((||)
          ((||)
            (rel_dec (coq_Dec_RelDec string_Dec) f
              ('a'::('l'::('l'::('o'::('c'::[]))))))
            (rel_dec (coq_Dec_RelDec string_Dec) f
              ('f'::('r'::('e'::('e'::[]))))))
          (rel_dec (coq_Dec_RelDec string_Dec) f
            ('l'::('o'::('a'::('d'::[]))))))
        (rel_dec (coq_Dec_RelDec string_Dec) f
          ('s'::('t'::('o'::('r'::('e'::[])))))))
      (rel_dec (coq_Dec_RelDec string_Dec) f ('c'::('m'::('p'::[])))))
    (rel_dec (coq_Dec_RelDec string_Dec) f ('m'::('a'::('i'::('n'::[])))))

(** val syscalls : (char list * nat) list **)

let syscalls =
  (('p'::('r'::('i'::('n'::('t'::[]))))), (S
    O)) :: ((('s'::('c'::('a'::('n'::[])))), O) :: [])

type extVars = char list list

type extFuns = (char list * nat) list

type progVars = (char list * coq_Z) list

type progFuns = (char list * coq_function) list

type programL = { nameL : char list list; ext_varsL : extVars;
                  ext_funsL : extFuns; prog_varsL : progVars;
                  prog_funsL : (char list * (char list * coq_function)) list;
                  publicL : char list list; defsL : (char list * Sk.gdef) list }

type program = { name : char list; ext_vars : extVars; ext_funs : extFuns;
                 prog_vars : progVars; prog_funs : progFuns }

(** val public : program -> char list list **)

let public p =
  let sys = map fst syscalls in
  let evs = p.ext_vars in
  let efs = map fst p.ext_funs in
  let ivs = map fst p.prog_vars in
  let ifs = map fst p.prog_funs in app sys (app evs (app efs (app ivs ifs)))

(** val defs : program -> (char list * Sk.gdef) list **)

let defs p =
  let fs = map (fun pat -> let (fn, _) = pat in (fn, Sk.Gfun)) p.prog_funs in
  let vs =
    map (fun pat -> let (vn, vv) = pat in (vn, (Sk.Gvar vv))) p.prog_vars
  in
  filter (fun x -> let x0 = fst x in negb (call_ban x0)) (app fs vs)

(** val lift : program -> programL **)

let lift p =
  { nameL = (p.name :: []); ext_varsL = p.ext_vars; ext_funsL = p.ext_funs;
    prog_varsL = p.prog_vars; prog_funsL =
    (map (fun pf -> (p.name, pf)) p.prog_funs); publicL = (public p); defsL =
    (defs p) }
