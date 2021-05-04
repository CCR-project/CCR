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

  Fixpoint compile_exprs (exprs: list Imp.expr) acc : option (list Clight.expr) :=
    match exprs with
    | h :: t =>
      do hexp <- (compile_expr h); compile_exprs t (acc ++ [hexp])
    | [] => Some acc
    end
  .

  Fixpoint make_arg_types n :=
    match n with
    | O => Tnil
    | S n' => Tcons Tlong0 (make_arg_types n')
    end
  .

  Record gmap := mk_gmap {
    _ext_vars : list ident;
    _ext_funs : list (ident * type);
    _int_vars : list ident;
    _int_funs : list (ident * type);
  }.

  Let get_gmap_efuns :=
    fun src =>
      List.map (fun '(name, n) => (s2p name, Tfunction (make_arg_types n) Tlong0 cc_default)) src.

  Let get_gmap_ifuns :=
    fun src =>
      List.map (fun '(name, f) => (s2p name, Tfunction (make_arg_types (length f.(Imp.fn_params))) Tlong0 cc_default)) src.

  Definition get_gmap (src : Imp.program) :=
    mk_gmap
      (List.map s2p src.(ext_vars))
      (get_gmap_efuns src.(ext_funs))
      (List.map (fun '(s, z) => s2p s) src.(prog_vars))
      (get_gmap_ifuns src.(prog_funs))
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

  Variable gm : gmap.

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
      let fdecls := gm.(_ext_funs) ++ gm.(_int_funs) in
      let id := s2p f in
      do fty <- (ident_key id fdecls);
      do al <- (compile_exprs args []);
      Some (Scall (Some (s2p x)) (Evar id fty) al)
    | CallFun2 f args =>
      let fdecls := gm.(_ext_funs) ++ gm.(_int_funs) in
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
      let fdecls := gm.(_ext_funs) in
      let id := s2p f in
      do fty <- (ident_key id fdecls);
      do al <- (compile_exprs args []);
      Some (Scall (Some (s2p x)) (Evar id fty) al)
    | CallSys2 f args =>
      let fdecls := gm.(_ext_funs) in
      let id := s2p f in
      do fty <- (ident_key id fdecls);
      do al <- (compile_exprs args []);
      Some (Scall None (Evar id fty) al)

    | Expr r =>
      do cr <- (compile_expr r); Some (Sreturn (Some cr))

    | AddrOf x GN =>
      let id := s2p GN in
      let vdecls := gm.(_ext_vars) ++ gm.(_int_vars) in
      let fdecls := gm.(_ext_funs) ++ gm.(_int_funs) in
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

  Let compile_eVars : extVars -> tgt_gdefs :=
    let init_value := [] in
    let gv := (mkglobvar Tlong0 init_value false false) in
    fun src => List.map (fun name => (s2p name, Gvar gv)) src.

  Let compile_iVars : progVars -> tgt_gdefs :=
    let mapf :=
        fun '(name, z) =>
          let init_value := [Init_int64 (to_long z)] in
          let gv := (mkglobvar Tlong0 init_value false false) in
          (s2p name, Gvar gv) in
    fun src => List.map mapf src.

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

  Fixpoint NoDupB (l : list ident) : bool :=
    match l with
    | [] => true
    | h :: t =>
      if (existsb (fun n => Pos.eqb h n) t)
      then false
      else NoDupB t
    end
  .

  Definition compile_gdefs (src : Imp.program) : option tgt_gdefs :=
    let evars := compile_eVars src.(ext_vars) in
    let ivars := compile_iVars src.(prog_vars) in
    do efuns <- compile_eFuns src.(ext_funs);
    do ifuns <- compile_iFuns src.(prog_funs);
    let defs := init_g ++ evars ++ efuns ++ ivars ++ ifuns in
    let ids := List.map (fun p => fst p) defs in
    if (NoDupB ids) then Some defs else None
  .

  Definition _compile (src : Imp.program) :=
    let optdefs := (compile_gdefs src) in
    match optdefs with
    | None => Error [MSG "Imp2clight compilation failed"]
    | Some _defs =>
      let pdefs := Maps.PTree_Properties.of_list _defs in
      let defs := Maps.PTree.elements pdefs in
      make_program [] defs (List.map s2p (src.(public) [])) (s2p "main")
    end
  .

End Compile.

Definition compile (src : Imp.program) :=
  _compile (get_gmap src) src
.

Section Link.

  (* Linker for Imp programs *)
  



  (* Imp's linker is Mod.add_list (and Sk.add for ge), 
     but resulting globval env is different from link_prog of Clight's linker,
     so we will define new linker which follows link_prog. *)

  (* Context `{Σ: GRA.t}. *)

  (* Definition link_Sk_merge (o1 o2 : option Sk.gdef) := *)
  (*   match o1 with *)
  (*   | Some gd1 => *)
  (*     match o2 with *)
  (*     | Some gd2 => *)
  (*     | None => o1 *)
  (*     end *)
  (*   | None => o2 *)
  (*   end *)
  (* . *)

  (* Definition clink_Sk (s1 s2 : Sk.t) : Sk.t := *)
  (*   let s2p_l := fun '(name, gd) => (s2p name, gd) in *)
  (*   let dm1 := Maps.PTree_Properties.of_list (List.map s2p_l s1) in *)
  (*   let dm2 := Maps.PTree_Properties.of_list (List.map s2p_l s2) in *)
    
    
  (*      Maps.PTree.elements (Maps.PTree.combine link_prog_merge dm1 dm2); *)
  (* Definition _add (md0 md1 : ModL.t) : ModL.t := {| *)
  (*   get_modsem := fun sk => *)
  (*                   ModSemL.add (md0.(get_modsem) sk) (md1.(get_modsem) sk); *)
  (*   sk := Sk.add md0.(sk) md1.(sk); *)
  (* |} *)
  (* . *)

End Link.
