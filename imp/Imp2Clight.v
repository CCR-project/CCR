Require Import Coqlib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.
Require Import Imp.
Require Import ImpProofs.
Require Import IMem0.

Require Import Coq.Lists.SetoidList.

From compcert Require Import
     AST Integers Ctypes Clight Globalenvs Linking Errors Cshmgen Behaviors Events.

Import Int.

Set Implicit Arguments.

Parameter s2p: string -> ident.

Definition to_long := Int64.repr.

Section Compile.

  (* compile each program indiv, 
     prove behavior refinement for whole (closed) prog after linking *)
  Let tgt_gdef := globdef (Ctypes.fundef function) type.
  Let tgt_gdefs := list (ident * tgt_gdef).

  Definition Tlong0 := (Tlong Signed noattr).

  Definition Tptr0 tgt_ty := (Tpointer tgt_ty noattr).

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
      (get_gmap_ifuns (List.map snd src.(prog_funsL)))
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
      match s1 with
      | Expr _ => None
      | _ =>
        do cs1 <- (compile_stmt s1);
        do cs2 <- (compile_stmt s2);
        Some (Ssequence cs1 cs2)
      end
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

  Definition compile_function (f : Imp.function) : option function :=
    do fbody <- (compile_stmt f.(Imp.fn_body));
    let fdef := {|
          fn_return := Tlong0;
          fn_callconv := cc_default;
          fn_params := (List.map (fun vn => (s2p vn, Tlong0)) f.(Imp.fn_params));
          fn_vars := [];
          fn_temps := (List.map (fun vn => (s2p vn, Tlong0)) f.(Imp.fn_vars));
          fn_body := fbody;
        |} in
    Some fdef.

  Fixpoint compile_iFuns (src : progFuns) : option tgt_gdefs :=
    match src with
    | [] => Some []
    | (name, f) :: t =>
      do tail <- (compile_iFuns t);
      do cf <- (compile_function f);
      let gf := Internal cf in
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

  Definition imp_prog_ids (src : Imp.programL) :=
    let id_ev := List.map s2p src.(ext_varsL) in
    let id_ef := List.map (fun p => s2p (fst p)) src.(ext_funsL) in
    let id_iv := List.map (fun p => s2p (fst p)) src.(prog_varsL) in
    let id_if := List.map (fun p => s2p (fst (snd p))) src.(prog_funsL) in
    id_init ++ id_ev ++ id_ef ++ id_iv ++ id_if
  .

  Definition compile_gdefs (src : Imp.programL) : option tgt_gdefs :=
    let ids := imp_prog_ids src in
    if (@NoDupB _ positive_Dec ids) then
      let evars := compile_eVars src.(ext_varsL) in
      let ivars := compile_iVars src.(prog_varsL) in
      do efuns <- compile_eFuns src.(ext_funsL);
      do ifuns <- compile_iFuns (List.map snd src.(prog_funsL));
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

  Let l_nameL := src1.(nameL) ++ src2.(nameL).
  Let l_prog_varsL := src1.(prog_varsL) ++ src2.(prog_varsL).
  Let l_prog_funsLM := src1.(prog_funsL) ++ src2.(prog_funsL).
  Let l_prog_funsL := List.map snd l_prog_funsLM.
  Let l_publicL := src1.(publicL) ++ src2.(publicL).
  Let l_defsL := src1.(defsL) ++ src2.(defsL).

  Let check_name_unique1 {K} {A} {B} decK
      (l1 : list (K * A)) (l2 : list (K * B)) :=
    let l1_k := List.map fst l1 in
    let l2_k := List.map fst l2 in
    @NoDupB _ decK (l1_k ++ l2_k).

  (* check defined names are unique *)
  Definition link_imp_cond1 :=
    check_name_unique1 string_Dec l_prog_varsL l_prog_funsL.

  Let check_name_unique2 {K} {B} decK
      (l1 : list K) (l2 : list (K * B)) :=
    let l2_k := List.map fst l2 in
    @NoDupB _ decK (l1 ++ l2_k).

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
    then Some (mk_programL l_nameL l_ext_vars l_ext_funs l_prog_varsL l_prog_funsLM l_publicL l_defsL)
    else None
  .

End Link.

Section Beh.

  (* Definition map_val (v : eventval) : option val := *)
  (*   match v with *)
  (*   | EVlong vl => Some (Vint vl.(Int64.intval)) *)
  (*   | _ => None *)
  (*   end. *)

  Inductive match_val : eventval -> val -> Prop :=
  | match_val_intro :
      forall v, match_val (EVlong v) (Vint v.(Int64.intval)).

  (* Fixpoint map_vals (vlist : list eventval) acc : option (list val) := *)
  (*   match vlist with *)
  (*   | [] => Some acc *)
  (*   | v :: t => do mv <- map_val v; map_vals t (acc ++ [mv]) *)
  (*   end. *)

  (* Definition match_vals : list eventval -> list val -> Prop := List.Forall2 match_val. *)

  (* Definition map_event (ev : Events.event) : option Universe.event := *)
  (*   match ev with *)
  (*   | Event_syscall name args r => *)
  (*     do margs <- map_vals args []; *)
  (*     do mr <- map_val r; *)
  (*     Some (event_sys name margs mr) *)
  (*   | _ => None *)
  (*   end. *)

  Inductive match_event : Events.event -> Universe.event -> Prop :=
  | match_event_intro
      name eargs uargs er ur
      (MV: Forall2 match_val eargs uargs)
      (MV: match_val er ur)
    :
      match_event (Event_syscall name eargs er) (event_sys name uargs ur)
  .

  (* Fixpoint map_trace (tr : trace) acc : option (list Universe.event) := *)
  (*   match tr with *)
  (*   | [] => Some acc *)
  (*   | ev :: t => *)
  (*     do mev <- map_event ev; map_trace t (acc ++ [mev]) *)
  (*   end. *)

  (* Definition match_trace : trace -> list Universe.event -> Prop := List.Forall2 match_event. *)

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

  Variant _match_beh (match_beh: _ -> _ -> Prop) (tgtb : program_behavior) (srcb : Tr.t) : Prop :=
  | match_beh_Terminates
      tr mtr r
      (MT : Forall2 match_event tr mtr)
      (TB : tgtb = Terminates tr r)
      (SB : srcb = Tr.app mtr (Tr.done r.(intval)))
    :
      _match_beh match_beh tgtb srcb
  | match_beh_Diverges
      tr mtr
      (MT : Forall2 match_event tr mtr)
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
  | match_beh_ub_trace
      mtr tr
      (SB : srcb = Tr.app mtr (Tr.ub))
      (MT : Forall2 match_event tr mtr)
      (TB : behavior_prefix tr tgtb)
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

End Beh.
Hint Constructors _match_beh.
Hint Unfold match_beh.
Hint Resolve match_beh_mon: paco.

Section Sim.

  Context `{Σ: GRA.t}.

  (* Variable src : Imp.program. *)
  (* Let src_mod := ImpMod.get_mod src. *)
  (* Variable tgt : Ctypes.program function. *)

  (* Let src_sem := ModL.compile (Mod.add_list ([src_mod] ++ [IMem])). *)
  (* Let tgt_sem := semantics2 tgt. *)

  (* CC 'final_state' = the return state of "main", should return int32. *)

  Definition _itree_of_imp itr :=
    fun ge le ms mn rp =>
      snd <$> EventsL.interp_Es (ModSemL.prog ms) (transl_all mn (vret <- ('(_, retv) <- (interp_imp ge le itr);; Ret retv);; Ret (vret↑))) rp.

  Definition itree_of_imp_cont itr :=
    fun ge le ms mn rp =>
      EventsL.interp_Es (ModSemL.prog ms) (transl_all mn (lv <- (interp_imp ge le itr);; Ret (lv))) rp.

  Definition itree_of_imp_ret :=
    fun ms mn rp =>
      fun (v : val) => EventsL.interp_Es (ModSemL.prog ms) (transl_all mn (Ret (v↑))) rp.

  Definition itree_of_imp_stop itr :=
    fun ge le ms mn rp =>
      snd <$> EventsL.interp_Es (ModSemL.prog ms) (transl_all mn ('(_, vret) <- (interp_imp ge le itr);; Ret (vret↑))) rp.

  Lemma itree_of_imp_split
        ge le ms mn rp itr
    :
      itree_of_imp_stop itr ge le ms mn rp
      =
      snd <$> ('(r, p, (_, v)) <- (itree_of_imp_cont itr ge le ms mn rp);; (itree_of_imp_ret ms mn (r, p)) v).
  Proof.
    unfold itree_of_imp_stop, itree_of_imp_cont, itree_of_imp_ret. grind.
    rewrite! transl_all_bind; rewrite! EventsL.interp_Es_bind.
    unfold ITree.map. grind. destruct p0. grind.
  Qed.

  Lemma itree_of_imp_stop_same
        ge le ms mn rp itr
    :
      _itree_of_imp itr ge le ms mn rp = itree_of_imp_stop itr ge le ms mn rp.
  Proof.
    unfold itree_of_imp_stop, _itree_of_imp. grind.
    rewrite! transl_all_bind; rewrite! EventsL.interp_Es_bind.
    unfold ITree.map. grind.
  Qed.

  Lemma itree_of_imp_cont_bind
        ge le ms mn rp itr ktr
    :
      itree_of_imp_cont (x <- itr;; ktr x) ge le ms mn rp
      =
      '(r, p, (le2, v)) <- (itree_of_imp_cont itr ge le ms mn rp);; (itree_of_imp_cont (ktr v) ge le2 ms mn (r, p)).
  Proof.
    unfold itree_of_imp_cont. rewrite interp_imp_bind. grind.    
    rewrite! transl_all_bind; rewrite! EventsL.interp_Es_bind.
    grind.
  Qed.

  Definition itree_of_stmt (s : stmt) :=
    fun ge le ms mn rp => itree_of_imp_cont (denote_stmt s) ge le ms mn rp.

  Definition imp_state := itree eventE Any.t.
  Definition imp_cont := (r_state * p_state * (lenv * val)) -> itree eventE (r_state * p_state * (lenv * val)).
  Definition imp_stack := Any.t -> imp_state.

  Variable match_le : lenv -> temp_env -> Prop.
  Variable match_mem : Mem.t -> Memory.Mem.mem -> Prop.
  (* match_genv: ge = Sk.load_skenv imp.(defs), tgtge = globalenv (compile imp),
                 need to show they match only at beginning *)
  Variable match_ge : SkEnv.t -> genv -> Prop.
  Variable ge : SkEnv.t.
  Variable tgtge : genv.
  Hypothesis MGENV : match_ge ge tgtge.

  Fixpoint get_cont_stmts (cc: cont) : list Clight.statement :=
    match cc with
    | Kseq s k => s :: (get_cont_stmts k)
    | _ => []
    end
  .

  Inductive match_cont : imp_cont -> (list Clight.statement) -> Prop :=
  | match_nil
    :
      match_cont idK []
  | match_stmt
      st itr ktr chead ctail gm ge ms mn
      (CST: compile_stmt gm st = Some chead)
      (ITR: itr = fun '(r, p, (le, _)) => itree_of_stmt st ge le ms mn (r, p))
      (MC: match_cont ktr ctail)
    :
      match_cont (fun x => (itr x >>= ktr)) (chead :: ctail)
  .

  Inductive match_stack : imp_stack -> Clight.cont -> Prop :=
  | match_stack_bottom
    :
      match_stack idK Kstop

  | match_stack_cret_some
      tf rp ms mn le tle next stack tcont id tid glue tglue
      (WF_RETF: tf.(fn_return) = Tlong0)
      (MLE: match_le le tle)
      (MID: s2p id = tid)

      (GLUE: glue = fun v: Any.t => itree_of_imp_cont (` v0 : val <- (v↓)?;; trigger (SetVar id v0);; Ret Vundef) ge le ms mn rp)

      (MCONT: match_cont next (get_cont_stmts tcont))
      (MSTACK: match_stack stack (call_cont tcont))

      (TGLUE: tglue = Kcall (Some tid) tf empty_env tle tcont)
    :
      match_stack (fun v: Any.t => (x <- (glue v);; '(_, _, (_, rv)) <- next x;; Ret (rv↑) >>= stack)) (tglue)

  | match_stack_cret_none
      tf rp ms mn le tle next stack tcont glue tglue
      (WF_RETF: tf.(fn_return) = Tlong0)
      (MLE: match_le le tle)

      (GLUE: glue = fun _ => itree_of_imp_cont (Ret Vundef) ge le ms mn rp)

      (MCONT: match_cont next (get_cont_stmts tcont))
      (MSTACK: match_stack stack (call_cont tcont))

      (TGLUE: tglue = Kcall None tf empty_env tle tcont)
    :
      match_stack (fun v: Any.t => (x <- (glue v);; '(_, _, (_, rv)) <- next x;; Ret (rv↑) >>= stack)) (tglue)
  .

  Variant match_states : imp_state -> Clight.state -> Prop :=
  | match_states_intro
      gm tf rp ms mn le tle st itr tst m tm next stack tcont
      (* function is only used to check return type, which compiled one always passes, except "main" *)
      (* (CF: compile_function gm f = Some tgtf) *)
      (WF_RETF: tf.(fn_return) = Tlong0)
      (CST: compile_stmt gm st = Some tst)
      (ML: match_le le tle)
      (MM: match_mem m tm)
      (MCS: match_cont next (get_cont_stmts tcont))
      (MCN: match_stack stack (call_cont tcont))
      (ITR: itr = itree_of_stmt st ge le ms mn rp)
    :
      match_states (x <- itr;; '(_, _, (_, rv)) <- next x;; Ret (rv↑) >>= stack) (State tf tst tcont empty_env tle tm)
  .

  (* Definition alist_add_option optid v (le : lenv) := *)
  (*   match optid with *)
  (*   | None => le *)
  (*   | Some id => alist_add id v le *)
  (*   end. *)

  (* Variant match_id : option var -> option ident -> Prop := *)
  (* | match_id_None *)
  (*   : *)
  (*     match_id None None *)
  (* | match_id_Some *)
  (*     v *)
  (*   : *)
  (*     match_id (Some v) (Some (s2p v)). *)

  (* Hypothesis archi_ptr64 : Archi.ptr64 = true. *)
  (* Definition map_val (v : Universe.val) : Values.val := *)
  (*   match v with *)
  (*   | Vint z => Values.Vlong (to_long z) *)
  (*   | Vptr blk ofs => *)
  (*     let ofsv := to_long ofs in *)
  (*     Values.Vptr (Pos.of_nat blk) (Ptrofs.mkint ofsv.(Int64.intval) ofsv.(Int64.intrange)) *)
  (*   | Vundef => Values.Vundef *)
  (*   end. *)

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

  Definition fold_left_option {T} f (t : list T) (opth : option T) :=
    fold_left
      (fun opt s2 => match opt with | Some s1 => f s1 s2 | None => None end)
      t opth.

  Lemma fold_left_option_None {T} :
    forall f (l : list T), fold_left_option f l None = None.
  Proof.
    intros f. induction l; ss; clarify.
  Qed.

  Definition link_imp_list src_list :=
    match src_list with
    | [] => None
    | src_h :: src_t =>
      fold_left_option link_imp src_t (Some src_h)
    end.

  Definition link_clight_list (tgt_list : list (Ctypes.program function)) :=
    match tgt_list with
    | [] => None
    | tgt_h :: tgt_t =>
      fold_left_option link_program tgt_t (Some tgt_h)
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
    destruct (link_program p0 tgt_h) eqn:LPt; ss; clarify.
    2:{ rewrite fold_left_option_None in H1; clarify. }
    destruct (link_imp p src_h) eqn:LPs; ss; clarify.
    2:{ rewrite fold_left_option_None in H0; clarify. }
    eapply IHcompile_list.
    2: apply H1.
    2: apply H0.
    eapply _comm_link_imp_compile.
    3: apply LPs.
    3: apply LPt.
    auto. auto.
  Qed.

  Context `{Σ: GRA.t}.

  Lemma _comm_link_imp_link_mod :
    forall src1 src2 srcl tgt1 tgt2 tgtl (ctx : ModL.t),
      ImpMod.get_modL src1 = tgt1 ->
      ImpMod.get_modL src2 = tgt2 ->
      link_imp src1 src2 = Some srcl ->
      ImpMod.get_modL srcl = tgtl ->
      ModL.add (ModL.add ctx tgt1) tgt2
      =
      ModL.add ctx tgtl.
  Proof.
  Admitted.

  Lemma comm_link_imp_link_mod :
    forall src_list srcl tgt_list tgtl ctx,
      List.map (fun src => ImpMod.get_modL src) src_list = tgt_list ->
      link_imp_list src_list = Some srcl ->
      ImpMod.get_modL srcl = tgtl ->
      fold_left ModL.add tgt_list ctx
      =
      ModL.add ctx tgtl.
  Proof.
    destruct src_list eqn:SL; i; ss; clarify.
    move p after l.
    revert_until Σ.
    induction l; i; ss; clarify.
    destruct (link_imp p a) eqn:LI; ss; clarify.
    2:{ rewrite fold_left_option_None in H0; clarify. }
    erewrite _comm_link_imp_link_mod; eauto.
  Qed.

  Lemma single_compile_behavior_improves :
    forall (src: Imp.program) tgt (beh: program_behavior),
      compile src = OK tgt ->
      program_behaves (semantics2 tgt) beh ->
      let srcM := ModL.add IMem (ImpMod.get_mod src) in
      exists mbeh,
        match_beh beh mbeh /\ Beh.of_program (ModL.compile srcM) mbeh.
  Proof.
  Admitted.

  Theorem compile_behavior_improves :
    forall (src_list : list Imp.program) srclM tgt_list tgtl (beh : program_behavior),
      let src_list_lift := List.map Imp.lift src_list in
      compile_list src_list_lift tgt_list ->
      let src_list_mod := List.map (fun src => ImpMod.get_mod src) src_list in
      Mod.add_list (IMem :: src_list_mod) = srclM ->
      link_clight_list tgt_list = Some tgtl ->
      program_behaves (semantics2 tgtl) beh ->
      exists mbeh,
        match_beh beh mbeh /\ Beh.of_program (ModL.compile srclM) mbeh.
  Proof.
  Admitted.

End Proof.
