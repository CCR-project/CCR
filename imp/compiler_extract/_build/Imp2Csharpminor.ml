open AList
open AST
open BinNums
open Cminor
open Coqlib0
open Coqlib
open Csharpminor
open Datatypes
open Errors
open Imp
open Integers
open List0
open Maps
open PeanoNat
open RelDec
open Skeleton
open String0

(** val s2p : char list -> ident **)

let s2p = (fun str -> Camlcoq.(str |> camlstring_of_coqstring |> intern_string))

type builtinsTy =
  (char list * external_function) list
  (* singleton inductive, whose constructor was mk *)

(** val bts0 : builtinsTy -> (char list * external_function) list **)

let bts0 builtinsTy0 =
  builtinsTy0

(** val compile_expr : expr -> Csharpminor.expr **)

let rec compile_expr = function
| Var x -> Evar (s2p x)
| Lit z -> Econst (Olongconst (Int64.repr z))
| Eq (a, b) ->
  let ca = compile_expr a in
  let cb = compile_expr b in
  Eunop (Olongofint, (Ebinop ((Ocmpl Ceq), ca, cb)))
| Lt (a, b) ->
  let ca = compile_expr a in
  let cb = compile_expr b in
  Eunop (Olongofint, (Ebinop ((Ocmpl Clt), ca, cb)))
| Plus (a, b) ->
  let ca = compile_expr a in let cb = compile_expr b in Ebinop (Oaddl, ca, cb)
| Minus (a, b) ->
  let ca = compile_expr a in let cb = compile_expr b in Ebinop (Osubl, ca, cb)
| Mult (a, b) ->
  let ca = compile_expr a in let cb = compile_expr b in Ebinop (Omull, ca, cb)

(** val compile_exprs : expr list -> Csharpminor.expr list **)

let compile_exprs exprs =
  map compile_expr exprs

(** val make_signature : nat -> signature **)

let make_signature n =
  { sig_args = (repeat Tlong n); sig_res = (Tret Tlong); sig_cc = cc_default }

(** val compile_stmt : stmt -> Csharpminor.stmt **)

let rec compile_stmt = function
| Skip -> Sskip
| Assign (x, e) -> let ex = compile_expr e in Sset ((s2p x), ex)
| Seq (s1, s2) ->
  let cs1 = compile_stmt s1 in let cs2 = compile_stmt s2 in Sseq (cs1, cs2)
| If (cond, sif, selse) ->
  let cc = compile_expr cond in
  let cif = compile_stmt sif in
  let celse = compile_stmt selse in
  let bexp = Ebinop ((Ocmpl Cne), cc, (Econst (Olongconst Int64.zero))) in
  Sifthenelse (bexp, cif, celse)
| CallFun (x, f, args) ->
  let id = s2p f in
  let sig0 = make_signature (length args) in
  let al = compile_exprs args in
  Scall ((Some (s2p x)), sig0, (Eaddrof id), al)
| CallPtr (x, pe, args) ->
  (match pe with
   | Var y ->
     let sig0 = make_signature (length args) in
     let al = compile_exprs args in
     Scall ((Some (s2p x)), sig0, (Evar (s2p y)), al)
   | _ -> Sskip)
| CallSys (x, f, args) ->
  let id = s2p f in
  let sig0 = make_signature (length args) in
  let al = compile_exprs args in
  Scall ((Some (s2p x)), sig0, (Eaddrof id), al)
| AddrOf (x, gn) -> let id = s2p gn in Sset ((s2p x), (Eaddrof id))
| Malloc (x, se) ->
  let a = compile_expr se in
  let adjofs = Ebinop (Omull, (Econst (Olongconst
    (Int64.repr (Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))), a)
  in
  Scall ((Some (s2p x)), (ef_sig EF_malloc), (Eaddrof
  (s2p ('m'::('a'::('l'::('l'::('o'::('c'::[])))))))), (adjofs :: []))
| Free _ -> Sseq (Sskip, Sskip)
| Load (x, pe) ->
  let cpe = compile_expr pe in Sset ((s2p x), (Eload (Mint64, cpe)))
| Store (pe, ve) ->
  let cpe = compile_expr pe in
  let cve = compile_expr ve in Sstore (Mint64, cpe, cve)
| Cmp (x, ae, be) ->
  let cae = compile_expr ae in
  let cbe = compile_expr be in
  let cmpexpr = Eunop (Olongofint, (Ebinop ((Ocmplu Ceq), cae, cbe))) in
  Sset ((s2p x), cmpexpr)

(** val compile_eVar : char list -> ident * (fundef, unit) globdef **)

let compile_eVar id =
  ((s2p id), (Gvar { gvar_info = (); gvar_init = []; gvar_readonly = false;
    gvar_volatile = false }))

(** val compile_eVars : extVars -> (ident * (fundef, unit) globdef) list **)

let compile_eVars src =
  map compile_eVar src

(** val compile_iVar :
    (char list * coq_Z) -> ident * (fundef, unit) globdef **)

let compile_iVar = function
| (id, z) ->
  ((s2p id), (Gvar { gvar_info = (); gvar_init = ((Init_int64
    (Int64.repr z)) :: []); gvar_readonly = false; gvar_volatile = false }))

(** val compile_iVars : progVars -> (ident * (fundef, unit) globdef) list **)

let compile_iVars src =
  map compile_iVar src

(** val compile_eFun : (char list * nat) -> ident * (fundef, unit) globdef **)

let compile_eFun = function
| (id, a) ->
  ((s2p id), (Gfun (External (EF_external (id, (make_signature a))))))

(** val compile_eFuns : extFuns -> (ident * (fundef, unit) globdef) list **)

let compile_eFuns src =
  map compile_eFun src

(** val compile_iFun :
    (char list * (char list * coq_function)) -> ident * (fundef, unit) globdef **)

let compile_iFun = function
| (_, p) ->
  let (fn, f) = p in
  let params = map s2p f.fn_params in
  let temps =
    app (map s2p f.fn_vars)
      ((s2p ('r'::('e'::('t'::('u'::('r'::('n'::[]))))))) :: ((s2p ('_'::[])) :: []))
  in
  let sig0 =
    if rel_dec (coq_Dec_RelDec string_Dec) fn ('m'::('a'::('i'::('n'::[]))))
    then signature_main
    else make_signature (length params)
  in
  let _body = compile_stmt f.fn_body in
  let body =
    if rel_dec (coq_Dec_RelDec string_Dec) fn ('m'::('a'::('i'::('n'::[]))))
    then Sseq (_body, (Sreturn (Some (Eunop (Ointoflong, (Evar
           (s2p ('r'::('e'::('t'::('u'::('r'::('n'::[])))))))))))))
    else Sseq (_body, (Sreturn (Some (Evar
           (s2p ('r'::('e'::('t'::('u'::('r'::('n'::[])))))))))))
  in
  let fdef = { fn_sig = sig0; Csharpminor.fn_params = params;
    Csharpminor.fn_vars = []; fn_temps = temps; Csharpminor.fn_body = body }
  in
  ((s2p fn), (Gfun (Internal fdef)))

(** val compile_iFuns :
    (char list * (char list * coq_function)) list -> (ident * (fundef, unit)
    globdef) list **)

let compile_iFuns src =
  map compile_iFun src

(** val bts : builtinsTy -> (char list * (fundef, unit) globdef) list **)

let bts builtins =
  map (fun pat -> let (name, ef) = pat in (name, (Gfun (External ef))))
    (bts0 builtins)

(** val init_g0 : builtinsTy -> (char list * (fundef, unit) globdef) list **)

let init_g0 =
  let malloc_def = External EF_malloc in
  let free_def = External EF_free in
  (fun builtins ->
  app (bts builtins) ((('m'::('a'::('l'::('l'::('o'::('c'::[])))))), (Gfun
    malloc_def)) :: ((('f'::('r'::('e'::('e'::[])))), (Gfun free_def)) :: [])))

(** val init_g : builtinsTy -> (ident * (fundef, unit) globdef) list **)

let init_g builtins =
  map (fun pat -> let (name, fd) = pat in ((s2p name), fd)) (init_g0 builtins)

(** val c_sys : (ident * (fundef, unit) globdef) list **)

let c_sys =
  map compile_eFun syscalls

(** val compile_gdefs :
    builtinsTy -> programL -> (ident * (fundef, unit) globdef) list **)

let compile_gdefs builtins src =
  let evars = compile_eVars src.ext_varsL in
  let ivars = compile_iVars src.prog_varsL in
  let efuns = compile_eFuns src.ext_funsL in
  let ifuns = compile_iFuns src.prog_funsL in
  app (init_g builtins) (app c_sys (app efuns (app evars (app ifuns ivars))))

(** val compile : builtinsTy -> programL -> Csharpminor.program res **)

let compile builtins src =
  let _defs = compile_gdefs builtins src in
  if list_norepet_dec (dec positive_Dec) (map fst _defs)
  then let pdefs = PTree_Properties.of_list _defs in
       let defs = PTree.elements pdefs in
       let pubs =
         app (map (fun x -> s2p (fst x)) (init_g0 builtins))
           (map s2p src.publicL)
       in
       OK { prog_defs = defs; prog_public = pubs; prog_main =
       (s2p ('m'::('a'::('i'::('n'::[]))))) }
  else Error ((MSG
         ('I'::('m'::('p'::('2'::('c'::('s'::('h'::('a'::('r'::('p'::('m'::('i'::('n'::('o'::('r'::(' '::('c'::('o'::('m'::('p'::('i'::('l'::('a'::('t'::('i'::('o'::('n'::(' '::('f'::('a'::('i'::('l'::('e'::('d'::(';'::(' '::('d'::('u'::('p'::('l'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('d'::('e'::('c'::('l'::('a'::('r'::('a'::('t'::('i'::('o'::('n'::('s'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: [])

(** val extFun_Dec : (char list * nat) -> (char list * nat) -> bool **)

let extFun_Dec x y =
  let (x0, x1) = x in
  let (s, n) = y in
  if let rec f s0 x2 =
       match s0 with
       | [] -> (match x2 with
                | [] -> true
                | _::_ -> false)
       | a::s1 ->
         (match x2 with
          | [] -> false
          | a1::s2 ->
            (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
              (fun x3 x4 x5 x6 x7 x8 x9 x10 ->
              (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                (fun b8 b9 b10 b11 b12 b13 b14 b15 ->
                if x3
                then if b8
                     then if x4
                          then if b9
                               then if x5
                                    then if b10
                                         then if x6
                                              then if b11
                                                   then if x7
                                                        then if b12
                                                             then if x8
                                                                  then 
                                                                    if b13
                                                                    then 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                  else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                             else false
                                                        else if b12
                                                             then false
                                                             else if x8
                                                                  then 
                                                                    if b13
                                                                    then 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                  else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                   else false
                                              else if b11
                                                   then false
                                                   else if x7
                                                        then if b12
                                                             then if x8
                                                                  then 
                                                                    if b13
                                                                    then 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                  else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                             else false
                                                        else if b12
                                                             then false
                                                             else if x8
                                                                  then 
                                                                    if b13
                                                                    then 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                  else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                         else false
                                    else if b10
                                         then false
                                         else if x6
                                              then if b11
                                                   then if x7
                                                        then if b12
                                                             then if x8
                                                                  then 
                                                                    if b13
                                                                    then 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                  else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                             else false
                                                        else if b12
                                                             then false
                                                             else if x8
                                                                  then 
                                                                    if b13
                                                                    then 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                  else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                   else false
                                              else if b11
                                                   then false
                                                   else if x7
                                                        then if b12
                                                             then if x8
                                                                  then 
                                                                    if b13
                                                                    then 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                  else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                             else false
                                                        else if b12
                                                             then false
                                                             else if x8
                                                                  then 
                                                                    if b13
                                                                    then 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                  else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                               else false
                          else if b9
                               then false
                               else if x5
                                    then if b10
                                         then if x6
                                              then if b11
                                                   then if x7
                                                        then if b12
                                                             then if x8
                                                                  then 
                                                                    if b13
                                                                    then 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                  else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                             else false
                                                        else if b12
                                                             then false
                                                             else if x8
                                                                  then 
                                                                    if b13
                                                                    then 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                  else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                   else false
                                              else if b11
                                                   then false
                                                   else if x7
                                                        then if b12
                                                             then if x8
                                                                  then 
                                                                    if b13
                                                                    then 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                  else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                             else false
                                                        else if b12
                                                             then false
                                                             else if x8
                                                                  then 
                                                                    if b13
                                                                    then 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                  else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                         else false
                                    else if b10
                                         then false
                                         else if x6
                                              then if b11
                                                   then if x7
                                                        then if b12
                                                             then if x8
                                                                  then 
                                                                    if b13
                                                                    then 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                  else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                             else false
                                                        else if b12
                                                             then false
                                                             else if x8
                                                                  then 
                                                                    if b13
                                                                    then 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                  else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                   else false
                                              else if b11
                                                   then false
                                                   else if x7
                                                        then if b12
                                                             then if x8
                                                                  then 
                                                                    if b13
                                                                    then 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                  else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                             else false
                                                        else if b12
                                                             then false
                                                             else if x8
                                                                  then 
                                                                    if b13
                                                                    then 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                  else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                     else false
                else if b8
                     then false
                     else if x4
                          then if b9
                               then if x5
                                    then if b10
                                         then if x6
                                              then if b11
                                                   then if x7
                                                        then if b12
                                                             then if x8
                                                                  then 
                                                                    if b13
                                                                    then 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                  else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                             else false
                                                        else if b12
                                                             then false
                                                             else if x8
                                                                  then 
                                                                    if b13
                                                                    then 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                  else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                   else false
                                              else if b11
                                                   then false
                                                   else if x7
                                                        then if b12
                                                             then if x8
                                                                  then 
                                                                    if b13
                                                                    then 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                  else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                             else false
                                                        else if b12
                                                             then false
                                                             else if x8
                                                                  then 
                                                                    if b13
                                                                    then 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                  else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                         else false
                                    else if b10
                                         then false
                                         else if x6
                                              then if b11
                                                   then if x7
                                                        then if b12
                                                             then if x8
                                                                  then 
                                                                    if b13
                                                                    then 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                  else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                             else false
                                                        else if b12
                                                             then false
                                                             else if x8
                                                                  then 
                                                                    if b13
                                                                    then 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                  else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                   else false
                                              else if b11
                                                   then false
                                                   else if x7
                                                        then if b12
                                                             then if x8
                                                                  then 
                                                                    if b13
                                                                    then 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                  else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                             else false
                                                        else if b12
                                                             then false
                                                             else if x8
                                                                  then 
                                                                    if b13
                                                                    then 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                  else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                               else false
                          else if b9
                               then false
                               else if x5
                                    then if b10
                                         then if x6
                                              then if b11
                                                   then if x7
                                                        then if b12
                                                             then if x8
                                                                  then 
                                                                    if b13
                                                                    then 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                  else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                             else false
                                                        else if b12
                                                             then false
                                                             else if x8
                                                                  then 
                                                                    if b13
                                                                    then 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                  else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                   else false
                                              else if b11
                                                   then false
                                                   else if x7
                                                        then if b12
                                                             then if x8
                                                                  then 
                                                                    if b13
                                                                    then 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                  else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                             else false
                                                        else if b12
                                                             then false
                                                             else if x8
                                                                  then 
                                                                    if b13
                                                                    then 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                  else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                         else false
                                    else if b10
                                         then false
                                         else if x6
                                              then if b11
                                                   then if x7
                                                        then if b12
                                                             then if x8
                                                                  then 
                                                                    if b13
                                                                    then 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                  else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                             else false
                                                        else if b12
                                                             then false
                                                             else if x8
                                                                  then 
                                                                    if b13
                                                                    then 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                  else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                   else false
                                              else if b11
                                                   then false
                                                   else if x7
                                                        then if b12
                                                             then if x8
                                                                  then 
                                                                    if b13
                                                                    then 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                  else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                             else false
                                                        else if b12
                                                             then false
                                                             else if x8
                                                                  then 
                                                                    if b13
                                                                    then 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                  else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2)
                a1)
              a)
     in f x0 s
  then let rec f n0 x2 =
         match n0 with
         | O -> (match x2 with
                 | O -> true
                 | S _ -> false)
         | S n1 -> (match x2 with
                    | O -> false
                    | S n2 -> f n1 n2)
       in f x1 n
  else false

(** val name1 : ('a1 * 'a2) list -> 'a1 list **)

let name1 l =
  map fst l

(** val name2 : ('a1 * ('a2 * 'a3)) list -> 'a2 list **)

let name2 l =
  map (fun x -> fst (snd x)) l

(** val l_nameL : programL -> programL -> char list list **)

let l_nameL src1 src2 =
  app src1.nameL src2.nameL

(** val l_pvs : programL -> programL -> (char list * coq_Z) list **)

let l_pvs src1 src2 =
  app src1.prog_varsL src2.prog_varsL

(** val l_pfs :
    programL -> programL -> (char list * (char list * coq_function)) list **)

let l_pfs src1 src2 =
  app src1.prog_funsL src2.prog_funsL

(** val l_publicL : builtinsTy -> programL -> programL -> char list list **)

let l_publicL builtins src1 src2 =
  app src1.publicL (app (map fst (init_g0 builtins)) src2.publicL)

(** val l_defsL : programL -> programL -> (char list * Sk.gdef) list **)

let l_defsL src1 src2 =
  app src1.defsL src2.defsL

(** val link_imp_cond1 : programL -> programL -> bool **)

let link_imp_cond1 src1 src2 =
  let c1 =
    list_norepet_dec (dec string_Dec)
      (app src1.ext_varsL (name2 (l_pfs src1 src2)))
  in
  let c2 =
    list_norepet_dec (dec string_Dec)
      (app src2.ext_varsL (name2 (l_pfs src1 src2)))
  in
  let c3 =
    list_norepet_dec (dec string_Dec)
      (app (name1 src1.ext_funsL) (name1 (l_pvs src1 src2)))
  in
  let c4 =
    list_norepet_dec (dec string_Dec)
      (app (name1 src2.ext_funsL) (name1 (l_pvs src1 src2)))
  in
  let c5 =
    list_norepet_dec (dec string_Dec)
      (app src1.ext_varsL (name1 src2.ext_funsL))
  in
  let c6 =
    list_norepet_dec (dec string_Dec)
      (app src2.ext_varsL (name1 src1.ext_funsL))
  in
  (&&)
    ((&&)
      ((&&)
        ((&&) ((&&) (sumbool_to_bool c1) (sumbool_to_bool c2))
          (sumbool_to_bool c3)) (sumbool_to_bool c4)) (sumbool_to_bool c5))
    (sumbool_to_bool c6)

(** val _link_imp_cond2' : (char list * nat) -> extFuns -> bool **)

let rec _link_imp_cond2' p l =
  let (id, n) = p in
  (match l with
   | [] -> true
   | p0 :: t ->
     let (id2, n2) = p0 in
     if (&&) (eqb id id2) (negb (Nat.eqb n n2))
     then false
     else _link_imp_cond2' p t)

(** val _link_imp_cond2 : (char list * nat) list -> bool **)

let rec _link_imp_cond2 = function
| [] -> true
| h :: t -> if _link_imp_cond2' h t then _link_imp_cond2 t else false

(** val link_imp_cond2 : programL -> programL -> bool **)

let link_imp_cond2 src1 src2 =
  _link_imp_cond2 (app src1.ext_funsL src2.ext_funsL)

(** val l_evs : programL -> programL -> char list list **)

let l_evs src1 src2 =
  let l_evs0 = nodup string_Dec (app src1.ext_varsL src2.ext_varsL) in
  let l_pvsn = name1 (l_pvs src1 src2) in
  filter (fun s -> negb (sumbool_to_bool (in_dec string_Dec s l_pvsn))) l_evs0

(** val l_efs : programL -> programL -> (char list * nat) list **)

let l_efs src1 src2 =
  let l_efs0 = nodup extFun_Dec (app src1.ext_funsL src2.ext_funsL) in
  let l_pfsn = name2 (l_pfs src1 src2) in
  filter (fun sn ->
    negb (sumbool_to_bool (in_dec string_Dec (fst sn) l_pfsn))) l_efs0

(** val link_imp_cond3 : builtinsTy -> programL -> programL -> bool **)

let link_imp_cond3 builtins src1 src2 =
  list_norepet_dec (dec string_Dec)
    (app (name1 (init_g0 builtins))
      (app (name1 syscalls)
        (app (name1 (l_efs src1 src2))
          (app (l_evs src1 src2)
            (app (name2 (l_pfs src1 src2)) (name1 (l_pvs src1 src2)))))))

(** val link_imp : builtinsTy -> programL -> programL -> programL option **)

let link_imp builtins src1 src2 =
  if (&&) ((&&) (link_imp_cond1 src1 src2) (link_imp_cond2 src1 src2))
       (sumbool_to_bool (link_imp_cond3 builtins src1 src2))
  then Some { nameL = (l_nameL src1 src2); ext_varsL = (l_evs src1 src2);
         ext_funsL = (l_efs src1 src2); prog_varsL = (l_pvs src1 src2);
         prog_funsL = (l_pfs src1 src2); publicL =
         (l_publicL builtins src1 src2); defsL = (l_defsL src1 src2) }
  else None

(** val list2nlist : 'a1 -> 'a1 list -> 'a1 nlist **)

let rec list2nlist a = function
| [] -> Coq_nbase a
| h :: t -> Coq_ncons (a, (list2nlist h t))

(** val link_imp_nlist : builtinsTy -> programL nlist -> programL option **)

let rec link_imp_nlist builtins = function
| Coq_nbase a -> Some a
| Coq_ncons (a, l) ->
  (match link_imp_nlist builtins l with
   | Some b -> link_imp builtins a b
   | None -> None)

(** val link_imp_list : builtinsTy -> programL list -> programL option **)

let link_imp_list builtins = function
| [] -> None
| h :: t -> link_imp_nlist builtins (list2nlist h t)

(** val link_imps : builtinsTy -> program list -> programL option **)

let link_imps builtins src_list =
  link_imp_list builtins (map lift src_list)
