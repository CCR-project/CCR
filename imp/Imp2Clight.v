Require Import Coqlib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.
Require Import Imp.
Require Import IMem0.

Require Import Coq.Lists.SetoidList.

From compcert Require Import
     AST Integers Ctypes Clight Globalenvs
     Linking Errors Cshmgen Behaviors Events.

Import Int.

Set Implicit Arguments.

Parameter s2p: string -> ident.

Definition to_long := Int64.repr.

Section Compile.

  (* compile each program indiv, 
     prove behavior refinement for whole (closed) prog after linking *)
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

  Definition get_gmap (src : Imp.programL) :=
    mk_gmap
      (List.map s2p src.(ext_varsL))
      (get_gmap_efuns src.(ext_funsL))
      (List.map (fun '(s, z) => s2p s) src.(prog_varsL))
      (get_gmap_ifuns src.(prog_funsL))
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

  Let id_init := List.map fst init_g.

  Fixpoint NoDupB {A} decA (l : list A) : bool :=
    match l with
    | [] => true
    | h :: t =>
      if in_dec decA h t then false else NoDupB decA t
    end
  .

  (* (* maybe cleanup using Dec... *) *)
  (* Fixpoint NoDupB {K} {R : K -> K -> Prop} {RD_K : RelDec R} (l : list K) : bool := *)
  (*   match l with *)
  (*   | [] => true *)
  (*   | h :: t => *)
  (*     if (existsb (fun n => h ?[ R ] n) t) *)
  (*     then false *)
  (*     else NoDupB t *)
  (*   end *)
  (* . *)

  Definition imp_prog_ids (src : Imp.programL) :=
    let id_ev := List.map s2p src.(ext_varsL) in
    let id_ef := List.map (fun p => s2p (fst p)) src.(ext_funsL) in
    let id_iv := List.map (fun p => s2p (fst p)) src.(prog_varsL) in
    let id_if := List.map (fun p => s2p (fst p)) src.(prog_funsL) in
    id_init ++ id_ev ++ id_ef ++ id_iv ++ id_if
  .

  Definition compile_gdefs (src : Imp.programL) : option tgt_gdefs :=
    let ids := imp_prog_ids src in
    if (@NoDupB _ positive_Dec ids) then
      let evars := compile_eVars src.(ext_varsL) in
      let ivars := compile_iVars src.(prog_varsL) in
      do efuns <- compile_eFuns src.(ext_funsL);
      do ifuns <- compile_iFuns src.(prog_funsL);
      let defs := init_g ++ evars ++ efuns ++ ivars ++ ifuns in
      Some defs
    else None
  .

  Definition _compile (src : Imp.programL) :=
    let optdefs := (compile_gdefs src) in
    match optdefs with
    | None => Error [MSG "Imp2clight compilation failed"]
    | Some _defs =>
      let pdefs := Maps.PTree_Properties.of_list _defs in
      let defs := Maps.PTree.elements pdefs in
      make_program [] defs (List.map s2p src.(publicL)) (s2p "main")
    end
  .

End Compile.

Definition compile (src : Imp.programL) :=
  _compile (get_gmap src) src
.

Definition extFun_Dec : forall x y : (string * nat), {x = y} + {x <> y}.
Proof.
  i. destruct x, y.
  assert (NC: {n = n0} + {n <> n0}); auto using nat_Dec.
  assert (SC: {s = s0} + {s <> s0}); auto using string_Dec.
  destruct NC; destruct SC; clarify; auto.
  all: right; intros p; apply pair_equal_spec in p; destruct p; clarify.
Qed.

Section Link.

  Variable src1 : Imp.programL.
  Variable src2 : Imp.programL.

  Let l_prog_varsL := src1.(prog_varsL) ++ src2.(prog_varsL).
  Let l_prog_funsL := src1.(prog_funsL) ++ src2.(prog_funsL).
  Let l_publicL := src1.(publicL) ++ src2.(publicL).
  Let l_defsL := src1.(defsL) ++ src2.(defsL).

  Let check_name_unique1 {K} {A} {B} decK
      (l1 : list (K * A)) (l2 : list (K * B)) :=
    let l1_k := List.map fst l1 in
    let l2_k := List.map fst l2 in
    @NoDupB _ decK (l1_k ++ l2_k).
  (* Let check_name_unique1 {K} {A} {B} {R : K -> K -> Prop} {RD_K : RelDec R} *)
  (*     (l1 : list (K * A)) (l2 : list (K * B)) := *)
  (*   let l1_k := List.map fst l1 in *)
  (*   let l2_k := List.map fst l2 in *)
  (*   NoDupB (l1_k ++ l2_k). *)
    
  (* check defined names are unique *)
  Definition link_imp_cond1 :=
    check_name_unique1 string_Dec l_prog_varsL l_prog_funsL.

  Let check_name_unique2 {K} {B} decK
      (l1 : list K) (l2 : list (K * B)) :=
    let l2_k := List.map fst l2 in
    @NoDupB _ decK (l1 ++ l2_k).
  (* Let check_name_unique2 {K} {B} {R : K -> K -> Prop} {RD_K : RelDec R} *)
  (*     (l1 : list K) (l2 : list (K * B)) := *)
  (*   let l2_k := List.map fst l2 in *)
  (*   NoDupB (l1 ++ l2_k). *)

  (* check external decls are consistent *)
  Definition link_imp_cond2 :=
    let sd := string_Dec in
    let c1 := check_name_unique2 sd src1.(ext_varsL) l_prog_funsL in
    let c2 := check_name_unique2 sd src2.(ext_varsL) l_prog_funsL in
    let c3 := check_name_unique1 sd src1.(ext_funsL) l_prog_varsL in
    let c4 := check_name_unique1 sd src2.(ext_funsL) l_prog_varsL in
    c1 && c2 && c3 && c4.

  (* check external fun decls' sig *)
  Fixpoint _link_imp_cond3' (p : string * nat) (l : extFuns) :=
    let '(name, n) := p in
    match l with
    | [] => true
    | (name2, n2) :: t =>
      if (eqb name name2 && negb (n =? n2)) then false
      else _link_imp_cond3' p t
    end
  .

  Fixpoint _link_imp_cond3 l :=
    match l with
    | [] => true
    | h :: t =>
      if (_link_imp_cond3' h t) then _link_imp_cond3 t
      else false
    end
  .

  Definition link_imp_cond3 :=
    _link_imp_cond3 (src1.(ext_funsL) ++ src2.(ext_funsL)).

  (* merge external decls; vars is simple, funs assumes cond3 is passed *)
  Let l_ext_vars0 := nodup string_Dec (src1.(ext_varsL) ++ src2.(ext_varsL)).

  Let l_ext_funs0 := nodup extFun_Dec (src1.(ext_funsL) ++ src2.(ext_funsL)).

  (* link external decls; need to remove defined names *)
  Let l_ext_vars :=
    let l_prog_varsL' := List.map fst l_prog_varsL in
    filter (fun s => negb (in_dec string_Dec s l_prog_varsL')) l_ext_vars0.

  Let l_ext_funs :=
    let l_prog_funsL' := List.map fst l_prog_funsL in
    filter (fun sn => negb (in_dec string_Dec (fst sn) l_prog_funsL')) l_ext_funs0.

  (* Linker for Imp programs, follows Clight's link_prog as possible *)
  Definition link_imp : option Imp.programL :=
    if (link_imp_cond1 && link_imp_cond2 && link_imp_cond3)
    then Some (mk_programL l_ext_vars l_ext_funs l_prog_varsL l_prog_funsL l_publicL l_defsL)
    else None
  .

  (* Parameter link_imp : Imp.programL -> Imp.programL -> option Imp.programL. *)

  (* Imp's linker is Mod.add_list (and Sk.add for ge), 
     but resulting globval env is different from link_prog of Clight's linker,
     so we will define new linker which follows link_prog. *)


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

Section Beh.

  Definition map_val (v : eventval) : option val :=
    match v with
    | EVlong vl => Some (Vint vl.(Int64.intval))
    | _ => None
    end.

  Inductive match_val : eventval -> val -> Prop :=
  | match_val_intro :
      forall v, match_val (EVlong v) (Vint v.(Int64.intval)).

  Fixpoint map_vals (vlist : list eventval) acc : option (list val) :=
    match vlist with
    | [] => Some acc
    | v :: t => do mv <- map_val v; map_vals t (acc ++ [mv])
    end.

  Inductive match_vals : list eventval -> list val -> Prop :=
  | match_vals_intro :
      forall v1 v2 l1 l2,
        match_val v1 v2 -> match_vals l1 l2 -> match_vals (v1 :: l1) (v2 :: l2).

  Definition map_event (ev : Events.event) : option Universe.event :=
    match ev with
    | Event_syscall name args r =>
      do margs <- map_vals args [];
      do mr <- map_val r;
      Some (event_sys name margs mr)
    | _ => None
    end.

  Inductive match_event : Events.event -> Universe.event -> Prop :=
  | match_event_intro :
      forall name eargs uargs er ur,
        match_vals eargs uargs -> match_val er ur ->
        match_event (Event_syscall name eargs er) (event_sys name uargs ur).

  Fixpoint map_trace (tr : trace) acc : option (list Universe.event) :=
    match tr with
    | [] => Some acc
    | ev :: t =>
      do mev <- map_event ev; map_trace t (acc ++ [mev])
    end.

  Inductive match_trace : trace -> list Universe.event -> Prop :=
  | match_trace_intro :
      forall ee et ue ut,
        match_event ee ue -> match_trace et ut ->
        match_trace (ee :: et) (ue :: ut).

  (* Inductive match_beh : program_behavior -> Tr.t -> Prop := *)
  (* | match_beh_Terminates : *)
  (*     forall tr mtr r, *)
  (*       map_trace tr [] = Some mtr -> *)
  (*       match_beh (Terminates tr r) (Tr.app mtr (Tr.done r.(intval))) *)
  (* | match_beh_Diverges : *)
  (*     forall tr mtr, *)
  (*       map_trace tr [] = Some mtr -> *)
  (*       match_beh (Diverges tr) (Tr.app mtr (Tr.spin)) *)
  (* | match_beh_Reacts : *)
  (*     forall ev mev trinf mt, *)
  (*       map_event ev = Some mev -> *)
  (*       match_beh (Reacts trinf) mt -> *)
  (*       match_beh (Reacts (Econsinf ev trinf)) (Tr.cons mev mt) *)
  (* | match_beh_Goes_wrong : *)
  (*     forall tr mtr, *)
  (*       map_trace tr [] = Some mtr -> *)
  (*       match_beh (Goes_wrong tr) (Tr.app mtr (Tr.ub)). *)

  Variant _match_beh match_beh (tgtb : program_behavior) (srcb : Tr.t) : Prop :=
  | match_beh_Terminates
      tr mtr r
      (MT : match_trace tr mtr)
      (TB : tgtb = Terminates tr r)
      (SB : srcb = Tr.done r.(intval))
    :
      _match_beh match_beh tgtb srcb
  | match_beh_Diverges
      tr mtr
      (MT : match_trace tr mtr)
      (TB : tgtb = Diverges tr)
      (SB : srcb = Tr.app mtr (Tr.spin))
    :
      _match_beh match_beh tgtb srcb
  | match_beh_Reacts
      ev mev trinf mtrinf
      (ME : match_event ev mev)
      (MB : match_beh (Reacts trinf) mtrinf)
      (TB : tgtb = Reacts (Econsinf ev trinf))
      (SB : srcb = Tr.cons mev mtrinf)
    :
      _match_beh match_beh tgtb srcb
  | match_beh_Goes_wrong
      tr mtr
      (MT : match_trace tr mtr)
      (TB : tgtb = Goes_wrong tr)
      (SB : srcb = Tr.app mtr (Tr.ub))
    :
      _match_beh match_beh tgtb srcb.

  Definition match_beh : _ -> _ -> Prop := paco2 _match_beh bot2.

  Lemma match_beh_mon : monotone2 _match_beh.
  Proof.
    ii. inv IN.
    - econs 1; eauto.
    - econs 2; eauto.
    - econs 3; eauto.
    - econs 4; eauto.
  Qed.

  Hint Constructors _match_beh.
  Hint Unfold match_beh.
  Hint Resolve match_beh_mon: paco.

End Beh.

Section Sim.

  Context `{Σ: GRA.t}.
  Variable src : Mod.t.
  Variable tgt : program.

  Let src_sem := ModL.compile (Mod.add_list ([src] ++ [IMem])).
  Let tgt_sem := semantics2 tgt.

  (* Variable idx: Type. *)
  (* Variable ord: idx -> idx -> Prop. *)

  Inductive match_states
            (src_st : src_sem.(STS.state))
            (tgt_st : tgt_sem.(Smallstep.state)) : Prop :=
  .

  (* From compcert Require Import SimplExprproof. *)

  (* Let state: Type := itree eventE Any.t. *)
  (* Definition state_sort (st0: state): sort := *)
  (*   match (observe st0) with *)
  (*   | TauF _ => demonic *)
  (*   | RetF rv => *)
  (*     match rv↓ with *)
  (*     | Some (Vint rv) => final rv *)
  (*     | _ => angelic *)
  (*     end *)
  (*   | VisF (Choose X) k => demonic *)
  (*   | VisF (Take X) k => angelic *)
  (*   | VisF (Syscall fn args rvs) k => vis *)
  (*   end *)
  (* . *)
End Sim.

Section Proof.

  Import Maps.PTree.

  Lemma list_norepet_NoDupB {K} {decK} :
    forall l, Coqlib.list_norepet l <-> @NoDupB K decK l = true.
  Proof.
    split; i.
    - induction H; ss.
      clarify.
      destruct (in_dec decK hd tl); clarify.
    - induction l; ss; clarify. constructor.
      des_ifs. econs 2; auto.
  Qed.
  (*   split; i. *)
  (*   - induction H; ss. *)
  (*     clarify. *)
  (*     assert (A: existsb (fun n : K => hd ?[ Logic.eq ] n) tl = false). *)
  (*     { clear H0 IHlist_norepet. induction tl; ss. *)
  (*       apply not_or_and in H. destruct H. *)
  (*       apply IHtl in H0. apply orb_false_intro; ss. *)
  (*       apply rel_dec_neq_false; auto. *)
  (*       apply Dec_RelDec_Correct. } *)
  (*     rewrite A; ss. *)
  (*   - induction l; ss; clarify. constructor. *)
  (*     destruct (existsb (fun n : K => a ?[ Logic.eq ] n) l) eqn:EQ; clarify. *)
  (*     econs 2; auto. clear H IHl. *)
  (*     induction l; ss; clarify. *)
  (*     apply orb_false_elim in EQ. destruct EQ. clarify. *)
  (*     apply and_not_or. split; auto. *)
  (*     unfold Logic.not. i. symmetry in H1. *)
  (*     eapply rel_dec_eq_true in H1; clarify. *)
  (*     apply Dec_RelDec_Correct. *)
  (* Qed. *)

  Definition wf_imp_prog (src : Imp.programL) :=
    Coqlib.list_norepet (imp_prog_ids src).

  Lemma compile_gdefs_then_wf : forall gm src l,
      compile_gdefs gm src = Some l
      ->
      wf_imp_prog src.
  Proof.
    unfold compile_gdefs. i.
    des_ifs. clear H.
    unfold wf_imp_prog. eapply list_norepet_NoDupB; eauto.
  Qed.

  Lemma compile_then_wf : forall src tgt,
      compile src = OK tgt
      ->
      wf_imp_prog src.
  Proof.
    unfold compile, _compile. i.
    destruct (compile_gdefs (get_gmap src) src) eqn:EQ; clarify.
    eauto using compile_gdefs_then_wf.
  Qed.

  (* Maps.PTree.elements_extensional 
     we will rely on above theorem for commutation lemmas *)
  Lemma _comm_link_imp_compile :
    forall src1 src2 srcl tgt1 tgt2 tgtl,
      compile src1 = OK tgt1 -> compile src2 = OK tgt2 ->
      link_imp src1 src2 = Some srcl ->
      link_program tgt1 tgt2 = Some tgtl ->
      compile srcl = OK tgtl.
  Proof.
  Admitted.

  Definition wf_link {T} (program_list : list T) :=
    exists h t, program_list = h :: t.

  Inductive compile_list :
    list programL -> list (Ctypes.program function) -> Prop :=
  | compile_nil :
      compile_list [] []
  | compile_head :
      forall src_h src_t tgt_h tgt_t,
        compile src_h = OK tgt_h ->
        compile_list src_t tgt_t ->
        compile_list (src_h :: src_t) (tgt_h :: tgt_t).

  Definition fold_right_option {T} f (opth : option T) (t : list T) :=
    fold_right
      (fun s2 opt => match opt with | Some s1 => f s1 s2 | None => None end)
      opth t.

  Lemma fold_right_option_None {T} :
    forall f (l : list T), fold_right_option f None l = None.
  Proof.
    intros f. induction l; ss; clarify.
    rewrite IHl. ss.
  Qed.

  Definition link_imp_list src_list :=
    match src_list with
    | [] => None
    | src_h :: src_t =>
      fold_right_option link_imp (Some src_h) src_t
    end.

  Definition link_clight_list (tgt_list : list (Ctypes.program function)) :=
    match tgt_list with
    | [] => None
    | tgt_h :: tgt_t =>
      fold_right_option link_program (Some tgt_h) tgt_t
    end.

  Lemma comm_link_imp_compile :
    forall src_list srcl tgt_list tgtl,
      compile_list src_list tgt_list ->
      link_imp_list src_list = Some srcl ->
      link_clight_list tgt_list = Some tgtl
      ->
      compile srcl = OK tgtl.
  Proof.
    i. destruct src_list; destruct tgt_list; ss; clarify.
    inv H; clarify.
    generalize dependent srcl. generalize dependent tgtl.
    generalize dependent p. generalize dependent p0.
    induction H7; i; ss; clarify.
    destruct (fold_right_option link_program (Some p0) tgt_t) eqn:FC;
      destruct (fold_right_option link_imp (Some p) src_t) eqn:FI;
      ss; clarify.
    eapply _comm_link_imp_compile.
    3: apply H0.
    3: apply H1.
    eapply IHcompile_list; eauto.
    auto.
  Qed.

  Context `{Σ: GRA.t}.

  Lemma _comm_link_imp_link_mod :
    forall sn1 src1 sn2 src2 snl srcl tgt1 tgt2 tgtl (ctx : Mod.t),
      ImpMod.get_mod sn1 src1 = tgt1 ->
      ImpMod.get_mod sn2 src2 = tgt2 ->
      link_imp src1 src2 = Some srcl ->
      ImpMod.get_mod snl srcl = tgtl ->
      Mod.add_list ([tgt1; tgt2] ++ [ctx])
      =
      Mod.add_list ([tgtl] ++ [ctx]).
  Proof.
  Admitted.

  Definition get_mod_list ns_list :=
    List.map (fun '(name, src) => ImpMod.get_mod name src) ns_list.

  Lemma comm_link_imp_link_mod :
    forall name_src_list namel srcl tgt_list tgtl ctx,
      get_mod_list name_src_list = tgt_list ->
      let src_list := List.map snd name_src_list in
      link_imp_list src_list = Some srcl ->
      ImpMod.get_mod namel srcl = tgtl ->
      Mod.add_list (tgt_list ++ [ctx])
      =
      Mod.add_list ([tgtl] ++ [ctx]).
  Proof.
    induction name_src_list; i; ss; clarify.
    destruct a as [name src]. ss.
    destruct name_src_list eqn:NSL; ss; clarify.
    (* Need to redefine ImpMod's ModSem's name *)
  Admitted.

  Lemma exists_mapped_beh :
    forall (src: Imp.program) tgt (beh: program_behavior),
      compile src = OK tgt ->
      program_behaves (semantics2 tgt) beh
      ->
      exists mbeh, match_beh beh mbeh.
  Proof.
  Admitted.

  Lemma single_compile_behavior_improves :
    forall name (src: Imp.program) srcM tgt (beh: program_behavior),
      compile src = OK tgt ->
      program_behaves (semantics2 tgt) beh ->
      Mod.add_list ([ImpMod.get_mod name src] ++ [IMem]) = srcM
      ->
      exists mbeh,
        match_beh beh mbeh /\
        Beh.of_program (ModL.compile srcM) mbeh.
  Proof.
  Admitted.

End Proof.
