Require Import Coqlib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.
Require Import Imp.

Require Import Coq.Lists.SetoidList.

From compcert Require Import
     AST Integers Ctypes Clight Globalenvs Linking Errors Cshmgen.

Import Int.

Set Implicit Arguments.

Parameter s2p: string -> ident.

Section Compile.

  (* compile each program indiv, 
     prove behavior refinement for whole (closed) prog after linking *)

  Let to_long := Int64.repr.

  Let tgt_gdef := globdef (Ctypes.fundef function) type.
  Let tgt_gdefs := list (ident * tgt_gdef).

  Let Tlong0 :=
    (Tlong Signed noattr).

  Let Tptr0 tgt_ty :=
    (Tpointer tgt_ty noattr).

  Definition ident_key {T} id l : option T :=
    SetoidList.findA (Pos.eqb id) l.

  (* Definition string_key {T} l x : option T := *)
  (*   SetoidList.findA (String.string_dec x) l. *)

  (* ref: Velus, Generation.v *)
  Fixpoint list_type_to_typelist (types: list type): typelist :=
    match types with
    | [] => Tnil
    | h :: t => Tcons h (list_type_to_typelist t)
    end
  .

  Fixpoint args_to_typelist (args: list expr) : typelist :=
    match args with
    | [] => Tnil
    | h::t => Tcons Tlong0 (args_to_typelist t)
    end
  .

  Fixpoint compile_expr expr : option Clight.expr :=
    match expr with
    | Var x =>
      Some (Etempvar (s2p x) Tlong0)
    | Lit v =>
      match v with
      | Vint z => Some (Econst_long (to_long z) Tlong0)
      | _ => None
      end
    | Plus a b =>
      match (compile_expr a), (compile_expr b) with
      | Some ca, Some cb =>
        Some (Ebinop Cop.Oadd ca cb Tlong0)
      | _, _ => None
      end
    | Minus a b =>
      match (compile_expr a), (compile_expr b) with
      | Some ca, Some cb =>
        Some (Ebinop Cop.Osub ca cb Tlong0)
      | _, _ => None
      end
    | Mult a b =>
      match (compile_expr a), (compile_expr b) with
      | Some ca, Some cb =>
        Some (Ebinop Cop.Omul ca cb Tlong0)
      | _, _ => None
      end
    end
  .
  (** vsub, vmul may not agree with compcert's cop semantics *)

  (* (* for function pointer call *) *)
  (* Definition compile_expr_ptr tyargs expr : option Clight.expr := *)
  (*   match expr with *)
  (*   | Var x => *)
  (*     Some (Etempvar (s2p x) (Tptr0 (Tfunction tyargs Tlong0 cc_default))) *)
  (*   | _ => None *)
  (*   end *)
  (* . *)

  Fixpoint compile_exprs (exprs: list Imp.expr) acc : option (list Clight.expr) :=
    match exprs with
    | h :: t =>
      do hexp <- (compile_expr h); compile_exprs t (acc ++ [hexp])
    | [] => Some acc
    end
  .

  (* (* only check number of arguments, exploit Tlong <-> Tptr64 *) *)
  (* Fixpoint cnt_args (tyargs: typelist) (args: list expr) : bool := *)
  (*   match tyargs, args with *)
  (*   | Tnil, [] => true *)
  (*   | Tcons ty tys, e::es => cnt_args tys es *)
  (*   | _, _ => false *)
  (*   end *)
  (* . *)

  Fixpoint make_arg_types n :=
    match n with
    | O => Tnil
    | S n' => Tcons Tlong0 (make_arg_types n')
    end
  .

  Record pre_ge := mk_pre_ge {
    _ext_vars : list ident;
    _ext_funs : list (ident * type);
    _int_vars : list ident;
    _int_funs : list (ident * type);
  }.

  Fixpoint get_pre_ext_funs (src : extFuns) :=
    match src with
    | [] => []
    | (name, n) :: t =>
      (s2p name, Tfunction (make_arg_types n) Tlong0 cc_default)
        :: (get_pre_ext_funs t)
    end
  .

  Fixpoint get_pre_int_funs (src : progFuns) :=
    match src with
    | [] => []
    | (name, f) :: t =>
      (s2p name, Tfunction (make_arg_types (length f.(Imp.fn_params))) Tlong0 cc_default)
        :: (get_pre_int_funs t)
    end
  .

  Definition get_pre_ge (src : Imp.program) :=
    mk_pre_ge
      (List.map s2p src.(ext_vars))
      (get_pre_ext_funs src.(ext_funs))
      (List.map (fun '(s, z) => s2p s) src.(prog_vars))
      (get_pre_int_funs src.(prog_funs))
  .

  (** memory accessing calls *)
  (** load, store, cmp are translated to non-function calls. *)
  (** register alloc and free in advance so can be properly called *)
  Let malloc_args := (Tcons (Tptr0 Tlong0) Tnil).
  Let malloc_ret := (Tptr0 Tlong0).
  Let malloc_def : Ctypes.fundef function :=
    External EF_malloc malloc_args malloc_ret cc_default.

  Let free_args := (Tcons (Tptr0 Tlong0) Tnil).
  Let free_ret := Tvoid.
  Let free_def : Ctypes.fundef function :=
    External EF_free free_args free_ret cc_default.

  Variable pg : pre_ge.

  (* Imp has no type, value is either int64/ptr64 -> sem_cast can convert *)
  Fixpoint compile_stmt stmt : option statement :=
    match stmt with
    | Assign x e =>
      do ex <- (compile_expr e); Some (Sset (s2p x) ex)
    | Seq s1 s2 =>
      do cs1 <- (compile_stmt s1);
      do cs2 <- (compile_stmt s2);
      Some (Ssequence cs1 cs2)
    | If cond sif selse =>
      do cc <- (compile_expr cond);
      do cif <- (compile_stmt sif);
      do celse <- (compile_stmt selse);
      Some (Sifthenelse cc cif celse)
    | Skip =>
      Some (Sskip)

    | CallFun1 x f args =>
      let fdecls := pg.(_ext_funs) ++ pg.(_int_funs) in
      let id := s2p f in
      do fty <- (ident_key id fdecls);
      do al <- (compile_exprs args []);
      Some (Scall (Some (s2p x)) (Evar id fty) al)
    | CallFun2 f args =>
      let fdecls := pg.(_ext_funs) ++ pg.(_int_funs) in
      let id := s2p f in
      do fty <- (ident_key id fdecls);
      do al <- (compile_exprs args []);
      Some (Scall None (Evar id fty) al)

    (* only supports call by ptr with a variable (no other expr) *)
    | CallPtr1 x pe args =>
      match pe with
      | Var y =>
        do al <- (compile_exprs args []);
        let atys := make_arg_types (length args) in
        let fty := Tfunction atys Tlong0 cc_default in
        let a := Etempvar (s2p y) (Tptr0 fty) in
        Some (Scall (Some (s2p x)) a al)
      | _ => None
      end

    | CallPtr2 pe args =>
      match pe with
      | Var y =>
        do al <- (compile_exprs args []);
        let atys := make_arg_types (length args) in
        let fty := Tfunction atys Tlong0 cc_default in
        let a := Etempvar (s2p y) (Tptr0 fty) in
        Some (Scall None a al)
      | _ => None
      end

    | CallSys1 x f args =>
      let fdecls := pg.(_ext_funs) in
      let id := s2p f in
      do fty <- (ident_key id fdecls);
      do al <- (compile_exprs args []);
      Some (Scall (Some (s2p x)) (Evar id fty) al)
    | CallSys2 f args =>
      let fdecls := pg.(_ext_funs) in
      let id := s2p f in
      do fty <- (ident_key id fdecls);
      do al <- (compile_exprs args []);
      Some (Scall None (Evar id fty) al)

    | Expr r =>
      do cr <- (compile_expr r); Some (Sreturn (Some cr))

    | AddrOf x GN =>
      let id := s2p GN in
      let vdecls := pg.(_ext_vars) ++ pg.(_int_vars) in
      let fdecls := pg.(_ext_funs) ++ pg.(_int_funs) in
      if (existsb (fun p => Pos.eqb id p) vdecls)
      then Some (Sset (s2p x) (Eaddrof (Evar id Tlong0) Tlong0))
      else
        do fty <- (ident_key id fdecls);
        Some (Sset (s2p x) (Eaddrof (Evar id fty) fty))

    | Malloc x se =>
      do a <- (compile_expr se);
      let fty := (Tfunction malloc_args malloc_ret cc_default) in
      Some (Scall (Some (s2p x)) (Evar (s2p "malloc") fty) [a])
    | Free pe =>
      do a <- (compile_expr pe);
      let fty := (Tfunction free_args free_ret cc_default) in
      Some (Scall None (Evar (s2p "free") fty) [a])
    | Load x pe =>
      do cpe <- (compile_expr pe); Some (Sset (s2p x) (Ederef cpe Tlong0))
    | Store pe ve =>
      do cpe <- (compile_expr pe);
      do cve <- (compile_expr ve);
      Some (Sassign (Ederef cpe Tlong0) cve)
    | Cmp x ae be =>
      do cae <- (compile_expr ae);
      do cbe <- (compile_expr be);
      let cmpexpr := (Ebinop Cop.Oeq cae cbe Tlong0) in
      Some (Sset (s2p x) cmpexpr)
    end
  .

  Fixpoint compile_eVars (src : extVars) : tgt_gdefs :=
    match src with
    | [] => []
    | name :: t =>
      let init_value := [] in
      let gv := (mkglobvar Tlong0 init_value false false) in
      (s2p name, Gvar gv)::(compile_eVars t)
    end
  .

  Fixpoint compile_iVars (src : progVars) : tgt_gdefs :=
    match src with
    | [] => []
    | (name, z) :: t =>
      let init_value := [Init_int64 (to_long z)] in
      let gv := (mkglobvar Tlong0 init_value false false) in
      (s2p name, Gvar gv)::(compile_iVars t)
    end
  .

  Fixpoint compile_eFuns (src : extFuns) : option tgt_gdefs :=
    match src with
    | [] => Some []
    | (name, a) :: t =>
      do tail <- (compile_eFuns t);
      let tyargs := make_arg_types a in
      let sg := mksignature (typlist_of_typelist tyargs) (Tret AST.Tlong) cc_default in
      let fd := Gfun (External (EF_external name sg) tyargs Tlong0 cc_default) in 
      Some ((s2p name, fd) :: tail)
    end
  .

  Fixpoint compile_iFuns (src : progFuns) : option tgt_gdefs :=
    match src with
    | [] => Some []
    | (name, f) :: t =>
      do tail <- (compile_iFuns t);
      do fbody <- (compile_stmt f.(Imp.fn_body));
      let fdef := {|
            fn_return := Tlong0;
            fn_callconv := cc_default;
            fn_params := (List.map (fun vn => (s2p vn, Tlong0)) f.(Imp.fn_params));
            fn_vars := [];
            fn_temps := (List.map (fun vn => (s2p vn, Tlong0)) f.(Imp.fn_vars));
            fn_body := fbody;
          |} in
      let gf := Internal fdef in
      Some ((s2p name, Gfun gf) :: tail)
    end
  .

  Let init_g : tgt_gdefs :=
    [(s2p "malloc", Gfun malloc_def); (s2p "free", Gfun free_def)].

  Definition compile_gdefs (src : Imp.program) : option tgt_gdefs :=
    let evars := compile_eVars src.(ext_vars) in
    let ivars := compile_iVars src.(prog_vars) in
    do efuns <- compile_eFuns src.(ext_funs);
    do ifuns <- compile_iFuns src.(prog_funs);
    Some (evars ++ init_g ++ efuns ++ ivars ++ ifuns)
  .

  Definition _compile (src_defs : Imp.program) :=
    let optdefs := (compile_gdefs src_defs) in
    match optdefs with
    | None => Error [MSG "Imp2clight compilation failed"]
    | Some defs =>
      make_program [] defs (List.map (fun '(i, g) => i) defs) (s2p "main")
    end
  .

End Compile.

Definition compile (src : Imp.program) :=
  _compile (get_pre_ge src) src
.
