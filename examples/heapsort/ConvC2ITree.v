(* Require Import ZArith String List Lia. *)

Require Import Coqlib.
Require Import ITreelib.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.
Require Import AList.

From compcert Require Import
     AST Maps Globalenvs Memory Values Linking Integers.
From compcert Require Import
     Ctypes Clight.
Section Clight.
Context {eff : Type -> Type}.
Context {HasCall : callE -< eff}.
Context {HasEvent : eventE -< eff}.

Section EVAL_EXPR_COMP.
  Definition divide_c (n m: Z): bool :=
    let x := Z.div m n in
    (x * n =? m)%Z.

  Definition assign_loc_c (ce: composite_env)
           (ty: type) (b: block) (ofs: ptrofs)
           (v: val): itree eff unit :=
  match access_mode ty with
  | By_value chunk =>
    ccallU "store" (chunk, b, ofs, v)
  | By_copy =>
    match v with
    | Vptr b' ofs' =>
      let chk1 :=
          if (0 <? sizeof ce ty) then
            andb (divide_c
                    (alignof_blockcopy ce ty)
                    (Ptrofs.unsigned ofs'))
                 (divide_c
                    (alignof_blockcopy ce ty)
                    (Ptrofs.unsigned ofs))
          else true in
      if negb chk1 then Ret tt else
        let chk2 :=
            (orb (negb (b' =? b))%positive
                 (orb (Ptrofs.unsigned ofs' =? Ptrofs.unsigned ofs)
                      (orb (Ptrofs.unsigned ofs' + sizeof ce ty <=? Ptrofs.unsigned ofs)
                           (Ptrofs.unsigned ofs + sizeof ce ty <=? Ptrofs.unsigned ofs'))))%Z
        in
        if negb chk2 then Ret tt else
          bytes <- @ccallU _ _ _ _ (option (list memval))
                           "loadbytes" (b', ofs', sizeof ce ty);;
          ccallU "storebytes" (b, ofs, bytes)
    | _ => Ret tt
    end
  | By_reference => Ret tt
  | By_nothing => Ret tt
  end%Z.

  Definition deref_loc_c (ty: type)
             (b:block) (ofs: ptrofs): itree eff (option val) :=
    match access_mode ty with
    | By_value chunk =>
      ccallU "load" (chunk, b, ofs)
    | By_reference => Ret (Some (Vptr b ofs))
    | By_copy => Ret (Some (Vptr b ofs))
    | By_nothing => Ret None
    end.
  
  Variable ge: Clight.genv.
  Variable e: Clight.env.
  Variable le: Clight.temp_env.

  Section EVAL_LVALUE.
    Variable _eval_expr_c: expr -> itree eff (option val).

    Definition _eval_lvalue_c (a: expr)
      : itree eff (option (block * ptrofs)) :=
      match a with
      | Evar id ty =>
        match e ! id with
        | Some (l, ty') =>
          if type_eq ty ty' then Ret (Some (l, Ptrofs.zero))
          else Ret None
        | None =>
          match Genv.find_symbol
                  (Clight.genv_genv ge) id with
          | Some l => Ret (Some (l, Ptrofs.zero))
          | None => Ret None
          end
        end
      | Ederef a ty =>
        v <- _eval_expr_c a;;
        match v with
        | Some (Vptr l ofs) => Ret (Some (l, ofs))
        | _ => Ret None
        end
      | Efield a i ty =>
        v <- _eval_expr_c a;;
        match v with
        | Some (Vptr l ofs) =>
          match Clight.typeof a with
          | Tstruct id att =>
            match (Clight.genv_cenv ge) ! id with
            | Some co =>
              match field_offset (Clight.genv_cenv ge)
                                 i (co_members co) with
              | Errors.OK delta =>
                Ret (Some (l, (Ptrofs.add ofs (Ptrofs.repr delta))))
              | _ => Ret None
              end
            | _ => Ret None
            end
          | Tunion id att =>
            match (Clight.genv_cenv ge) ! id with
            | Some _ => Ret (Some (l, ofs))
            | None => Ret None
            end
          | _ => Ret None
          end
        | _ => Ret None
        end
      | _ => Ret None
      end.

  End EVAL_LVALUE.

  Fixpoint eval_expr_c (expr: Clight.expr): itree eff (option val) :=
    match expr with
    | Econst_int i ty => Ret (Some (Vint i))
    | Econst_float f ty => Ret (Some (Vfloat f))
    | Econst_single f ty => Ret (Some (Vsingle f))
    | Econst_long i ty => Ret (Some (Vlong i))
    | Etempvar id ty => Ret ((le ! id))
    | Eaddrof a ty =>
      v <- _eval_lvalue_c eval_expr_c a;;
      match v with
      | None => Ret None (*??*)
      | Some (loc, ofs) => Ret (Some (Vptr loc ofs))
      end
    | Eunop op a ty =>
      v <- eval_expr_c a;;
      match v with
      | None => Ret None
      | Some v1 =>
        ccallU "unary_op" (op, v1, (Clight.typeof a))
      end
    | Ebinop op a1 a2 ty =>
      v1 <- eval_expr_c a1;;
      v2 <- eval_expr_c a2;;
      match v1, v2 with
      | Some v1, Some v2 =>
        ccallU "binary_op"
               ((Clight.genv_cenv ge), op,
                v1, (Clight.typeof a1),
                v2, (Clight.typeof a2))
      | _, _ => Ret None
      end
    | Ecast a ty =>
      v <- eval_expr_c a;;
      match v with
      | None => Ret None
      | Some v1 =>
        ccallU "sem_cast" (v1, (Clight.typeof a), ty)
      end
    | Esizeof ty1 ty =>
      Ret (Some (Vptrofs (Ptrofs.repr (sizeof (Clight.genv_cenv ge) ty1))))
    | Ealignof ty1 ty =>
      Ret (Some (Vptrofs (Ptrofs.repr (alignof (Clight.genv_cenv ge) ty1))))
    | a =>
      v <- _eval_lvalue_c eval_expr_c a;;
      match v with
      | None => Ret None
      | Some (loc, ofs) =>
        v <- deref_loc_c (Clight.typeof a) loc ofs;; Ret v
      end
    end.

  Definition eval_lvalue_c
    : expr -> itree eff (option (block * ptrofs)) :=
    _eval_lvalue_c eval_expr_c.

  Fixpoint eval_exprlist_c
           (es: list expr) (ts: typelist)
    : itree eff (option (list val)) :=
    match es, ts with
    | [], Tnil => Ret (Some [])
    | e::es', Tcons ty ts' =>
      v1 <- eval_expr_c e;;
      vs <- eval_exprlist_c es' ts';; 
      match v1, vs with
      | Some v1, Some vs =>
        v2 <- ccallU "sem_cast" (v1, typeof e, ty);;
        match v2 with
        | Some v2 => Ret (Some (v2::vs))
        | None => Ret None
        end
      | _, _ => Ret None
      end
    | _, _ => Ret None
    end.

End EVAL_EXPR_COMP.

Definition id_list_norepet_c: list ident -> bool :=
  fun ids => if Coqlib.list_norepet_dec (ident_eq) ids then true else false.

Definition id_list_disjoint_c: list ident -> list ident -> bool :=
  fun ids1 ids2 =>
    if (Coqlib.list_disjoint_dec ident_eq ids1 ids2)
    then true else false.

Fixpoint alloc_variables_c (ge: genv) (e: env)
         (vars: list (ident * type))
  : itree eff env := 
  match vars with
  | [] => Ret e
  | (id, ty) :: vars' =>
    v <- ccallU "alloc" (sizeof ge ty);;
    match v with
    | Vptr b ofs => alloc_variables_c ge (PTree.set id (b, ty) e) vars'
    | _ => triggerUB
    end
  end.

Definition function_entry_c
           (ge: genv) (f: function) (vargs: list val)
  : itree eff (option (env * temp_env)) :=
  if (id_list_norepet_c (var_names (fn_vars f)) &&
      id_list_norepet_c (var_names (fn_params f)) &&
      id_list_disjoint_c (var_names (fn_params f))
                         (var_names (fn_temps f)))%bool
  then
    e <- alloc_variables_c ge empty_env (fn_vars f);;
    match
      bind_parameter_temps (fn_params f) vargs
                            (create_undef_temps
                               (fn_temps f))
    with
    | None => Ret None
    | Some le => Ret (Some (e, le))
    end
  else Ret None.

Section DECOMP.

  Notation itr_t :=
    (itree eff (env * temp_env *
                option bool (*break/continue*) * option val)).

  Variable ge: genv.

  Definition _sassign_c e le a1 a2 :=
    v <- eval_lvalue_c ge e le a1;;
    match v with
    | Some (loc, ofs) =>
      v2 <- eval_expr_c ge e le a2;; 
      match v2 with
      | Some v2 =>
        v <- ccallU "sem_cast" (v2, typeof a2, typeof a1);;
        match v with
        | Some v =>
          assign_loc_c ge (typeof a1) loc ofs v
        | None => Ret tt
        end
      | None => Ret tt
      end
    | None => Ret tt
    end.

  Definition _scall_c e le a al
    : itree eff val :=
    match Cop.classify_fun (typeof a) with
    | Cop.fun_case_f tyargs tyres cconv =>
      vf <- (eval_expr_c ge e le a);;
      vf <- vf?;;
      vargs <- eval_exprlist_c ge e le al tyargs;;
      vargs <- vargs?;;
      fd <- (Globalenvs.Genv.find_funct ge vf)?;;
      if type_eq (type_of_fundef fd)
                 (Tfunction tyargs tyres cconv)
      then
        match vf with
        | Vptr b ofs =>
          match Genv.find_funct_ptr ge b with
          | Some (Internal f) =>
            (* v <- trigger (Call b vargs↑);; *)
            (* v <- v↓?;; *)
            (* Ret v *)
            triggerUB
          | Some (External ef _ retty _) =>
            match ef with
            | EF_external fn _ =>
              v <- trigger (Call fn vargs↑);;
              v <- v↓?;;
              Ret v
            | _ => triggerUB
            end
          | _ => triggerUB
          end
        | _ => triggerUB (* unreachable *)
        end
      else triggerUB
    | _ => triggerUB
    end.

  Definition _site_c
             (e: env) (le: temp_env) (a: expr)
    : itree eff (option bool) :=
    v1 <- eval_expr_c ge e le a;;
    match v1 with
    | Some v1 =>
      ccallU "bool_val" (v1, typeof a)
    | None => Ret None
    end.

  Definition sloop_iter_body_one
             (itr: itr_t)
    : itree eff (env * temp_env * (option (option val))) :=
    '(e', le', obc, v) <- itr;;
    match v with
    | Some retv =>
      (* return *)
      Ret (e', le', Some (Some retv))
    | None =>
      if (* is_break *)
        match obc with
        | None => false
        | Some bc => bc
        end
      then
        (* break, not return *)
        Ret (e', le', Some None)
      else
        (* continue *)
        Ret (e', le', None)
    end.

  Definition sloop_iter_body
             (itr1 itr2: env -> temp_env -> itr_t)
             (i: env * temp_env)
    : itree eff
            (env * temp_env +
             env * temp_env * option val) :=
    let '(e, le) := i in
    (* '(e1, le1, m1, obc1, v1) <- itr1 e le m ;; *)
    '(e1, le1, ov1) <- sloop_iter_body_one (itr1 e le) ;;
    match ov1 with
    | Some v1 =>
      (* break or return *)
      Ret (inr (e1, le1, v1))
    | None =>
      (* run loop2 *)
      '(e2, le2, ov2) <- sloop_iter_body_one (itr2 e1 le1);;
      match ov2 with
      | Some v2 =>
        Ret (inr (e2, le2, v2))
      | None =>
        Ret (inl (e2, le2))
      end
    end.

  Definition _sloop_itree
             (e: env) (le: temp_env)
             (itr1 itr2: env -> temp_env -> itr_t)
    : itr_t :=
    '(e', le', v) <-
    ITree.iter (sloop_iter_body itr1 itr2) (e, le) ;;
    Ret (e', le', None, v).

  Fixpoint free_list_aux (l: list (block * Z * Z)): itree eff unit :=
    match l with
    | nil => Ret tt
    | (b, lo, hi):: l' =>
      @ccallU _ _ _ _ unit "free" (b, lo, hi);;;
      free_list_aux l'
    end.
  
  Definition _sreturn_c
             (retty: type)
             (e: env) (le: temp_env)
             (oa: option expr)
    : itree eff (option val) :=
    free_list_aux (blocks_of_env ge e);;;
    match oa with
    | None => Ret (Some Vundef)
    | Some a =>
      v <- eval_expr_c ge e le a;;
      match v with
      | None => Ret None
      | Some v =>
        ccallU "sem_cast" (v, typeof a, retty)
      end
    end.

  Fixpoint decomp_stmt
           (retty: type)
           (stmt: statement) (* (k: cont) *)
           (e: env) (le: temp_env)
    : itr_t :=
    match stmt with
    | Sskip =>
      Ret ((* k, *) e, le, None, None)
    | Sassign a1 a2 =>
      _sassign_c e le a1 a2;;;
      Ret (e, le, None, None)
    | Sset id a =>
      v <- eval_expr_c ge e le a ;;
      match v with
      | Some v =>
        let le' := PTree.set id v le in
        Ret (e, le', None, None)
      | None =>
        triggerUB
      end
    | Scall optid a al =>
      v <- _scall_c e le a al;;
      Ret (e, (set_opttemp optid v le), None, None)
    | Sbuiltin _ _ _ _ =>
      triggerUB
    | Ssequence s1 s2 =>
      '(e', le', bc, v) <- decomp_stmt retty s1 e le;;
      match v with
      | Some retval =>
        Ret (e', le', None, v)
      | None =>
        match bc with
        | None =>
          decomp_stmt retty s2 e' le'
        | Some _ =>
          Ret (e', le', bc, None)
        end
      end
    | Sifthenelse a s1 s2 =>
      b <- _site_c e le a;;
      match b with
      | Some b =>
        if (b: bool) then (decomp_stmt retty s1 e le)
        else (decomp_stmt retty s2 e le)
      | None =>
        triggerUB
      end
    | Sloop s1 s2 =>
      let itr1 := decomp_stmt retty s1 in
      let itr2 := decomp_stmt retty s2 in
      _sloop_itree e le itr1 itr2
    (* '(e, le, m, bc, v) <- itr ;; *)

    | Sbreak =>
      Ret (e, le, Some true, None)
    | Scontinue =>
      Ret (e, le, Some false, None)
    | Sreturn oa =>
      v <- _sreturn_c retty e le oa;;
      match v with
      | Some v =>
        Ret (e, le, None, Some v)
      | None =>
        triggerUB
      end
    | _ =>
      (* not supported *)
      triggerUB
    end.

  Fixpoint decomp_func
           (f: Clight.function)
           (vargs: list val)
    : itree eff val :=
    t <- function_entry_c ge f vargs;;
    match t with
    | None =>
      triggerUB
    | Some (e, le) =>
      '(_, _, _, ov) <- decomp_stmt (fn_return f) (fn_body f) e le;;
      let v := match ov with
               | None => Vundef
               | Some v => v
               end
      in
      Ret v
    end.

End DECOMP.

Notation call_data := (block * (* fundef * *) list val * mem)%type.


Section DECOMP_PROG.

  Context `{SystemEnv}.

  Variable cprog_app: Clight.program.
  Let ge: genv := Clight.globalenv cprog_app.

  Fixpoint decomp_fundefs
           (defs: list (ident * globdef Clight.fundef type))
    : list (block * ident * (list val -> itree eff val)) :=
    match defs with
    | [] => []
    | (id, gdef) :: defs' =>
      match gdef with
      | Gvar _ => decomp_fundefs defs'
      | Gfun fd =>
        match fd with
        | Internal f =>
          match Genv.find_symbol ge id with
          | Some b =>
            (b, id, decomp_func ge f) :: decomp_fundefs defs'
          | None => decomp_fundefs defs'
          end
        | _ => decomp_fundefs defs'
        end
      end
    end.

  (* Definition modsem : ModSem.t := {| *)
  (*   ModSem.fnsems := List.map (fun '(fn, f) => (fn, cfunU (decomp_fundefs f))) cprog_app.(prog_defs); *)
  (*   ModSem.mn := "TT"; *)
  (*   ModSem.initial_st := tt↑; *)
  (* |}. *)

  (* Definition get_mod (m : program) : Mod.t := {| *)
  (*   Mod.get_modsem := fun ge => (modsem m (Sk.load_skenv ge)); *)
  (*   Mod.sk := m.(defs); *)
  (* |}. *)

End DECOMP_PROG.

(* Record program (F : Type) : Type := Build_program *)
(*   { prog_defs : list (ident * globdef (Ctypes.fundef F) type); *)
(*     prog_public : list ident; *)
(*     prog_main : ident; *)
(*     prog_types : list composite_definition; *)
(*     prog_comp_env : composite_env; *)
(*     prog_comp_env_eq : build_composite_env prog_types = *)
(*                        Errors.OK prog_comp_env } *)

End Clight.
