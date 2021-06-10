Require Import Coqlib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.
Require Import Imp.
Require Import ImpProofs.

Require Import Coq.Lists.SetoidList.

From compcert Require Import
     Ctypes AST Integers Cminor Csharpminor Globalenvs Linking Errors Cminorgen Behaviors Events.

From compcert Require Compiler.

(* From compcert Require Import Cminor Cminortyping. *)
(* Import RTLtypes. *)

Import Int.

Set Implicit Arguments.

Parameter s2p: string -> ident.

Lemma option_dec {T} :
  forall x : option T,
    {match x with | Some _ => True | None => False end} +
    {~ match x with | Some _ => True | None => False end}.
Proof.
  i. destruct x.
  - left. auto.
  - right. auto.
Qed.

Section Compile.

  (* compile each program indiv,
     prove behavior refinement for whole (closed) prog after linking *)
  Let tgt_gdef := globdef fundef ().
  Let tgt_gdefs := list (ident * tgt_gdef).

  (* Definition Tlong0 := (Tlong Signed noattr). *)
  (* Definition Tptr0 tgt_ty := (Tpointer tgt_ty noattr). *)

  Definition ident_key {T} (id: ident) l : option T := alist_find id l.

  (* Fixpoint args_to_typelist (args: list expr) : typelist := *)
  (*   match args with *)
  (*   | [] => Tnil *)
  (*   | h::t => Tcons Tlong0 (args_to_typelist t) *)
  (*   end *)
  (* . *)

  Fixpoint compile_expr (expr: Imp.expr) : option Csharpminor.expr :=
    match expr with
    | Var x =>
      Some (Evar (s2p x))
    | Lit v =>
      match v with
      | Vint z => Some (Econst (Olongconst (Int64.repr z)))
      | _ => None
      end
    | Plus a b =>
      match (compile_expr a), (compile_expr b) with
      | Some ca, Some cb => Some (Ebinop Oaddl ca cb)
      | _, _ => None
      end
    | Minus a b =>
      match (compile_expr a), (compile_expr b) with
      | Some ca, Some cb => Some (Ebinop Osubl ca cb)
      | _, _ => None
      end
    | Mult a b =>
      match (compile_expr a), (compile_expr b) with
      | Some ca, Some cb => Some (Ebinop Omull ca cb)
      | _, _ => None
      end
    end
  .
  (** vsub, vmul may not agree with compcert's cop semantics *)

  Fixpoint compile_exprs_acc (exprs: list Imp.expr) acc : option (list Csharpminor.expr) :=
    match exprs with
    | h :: t => do hexp <- (compile_expr h); compile_exprs_acc t (acc ++ [hexp])
    | [] => Some acc
    end
  .

  Fixpoint compile_exprs (exprs: list Imp.expr) : option (list Csharpminor.expr) :=
    match exprs with
    | h :: t =>
      do hexp <- (compile_expr h);
      do texps <- (compile_exprs t);
      Some (hexp :: texps)
    | [] => Some []
    end
  .

  (* Fixpoint make_arg_types n := *)
  (*   match n with *)
  (*   | O => Tnil *)
  (*   | S n' => Tcons Tlong0 (make_arg_types n') *)
  (*   end *)
  (* . *)

  (** memory accessing calls *)
  (** load, store, cmp are translated to non-function calls. *)
  (** register alloc and free in advance so can be properly called *)
  Let malloc_def : fundef := External EF_malloc.
  Let free_def : fundef := External EF_free.

  Record function2 := mk_function2 {
    fn_sig2 : signature;
    fn_params2 : list ident;
    fn_vars2 : list (ident * Z);
    fn_temps2 : list ident;
    fn_body2 : Imp.stmt;
  }.
  Definition fundef2 := AST.fundef function2.

  Let tgt_gdef2 := globdef fundef2 ().
  Let tgt_gdefs2 := list (ident * tgt_gdef2).

  Definition make_signature n :=
    mksignature (repeat Tlong n) (Tlong) (cc_default).

  Definition compile_eVars src : tgt_gdefs2 :=
    let gv := (mkglobvar () [] false false) in List.map (fun id => (s2p id, Gvar gv)) src.

  Definition compile_iVars src : tgt_gdefs2 :=
    List.map (fun '(id, z) => (s2p id, Gvar (mkglobvar () [Init_int64 (Int64.repr z)] false false))) src.

  Definition compile_eFuns (src : extFuns) : tgt_gdefs2 :=
    List.map (fun '(id, a) => (s2p id, Gfun (External (EF_external id (make_signature a))))) src.

  Definition pre_compile_function (f : Imp.function) : option function2 :=
    let params := (List.map (fun vn => s2p vn) f.(Imp.fn_params)) in
    let temps := (List.map (fun vn => s2p vn) f.(Imp.fn_vars)) ++ [(s2p "return"); (s2p "_")] in
    if (Coqlib.list_norepet_dec dec (params ++ temps)) then
      let fdef := {|
            fn_sig2 := make_signature (List.length params);
            fn_params2 := params;
            fn_vars2 := [];
            fn_temps2 := temps;
            fn_body2 := f.(Imp.fn_body);
          |} in
      Some fdef
    else None.

  (* Fixpoint pre_compile_iFuns (src : progFuns) : option tgt_gdefs2 := *)
  (*   match src with *)
  (*   | [] => Some [] *)
  (*   | (name, f) :: t => *)
  (*     do tail <- (pre_compile_iFuns t); *)
  (*     do cf <- (pre_compile_function f); *)
  (*     let gf := Internal cf in *)
  (*     Some ((s2p name, Gfun gf) :: tail) *)
  (*   end *)
  (* . *)

  Definition dummy_def : (ident * tgt_gdef) :=
    (s2p ".neverused", Gfun (External (EF_debug 1%positive 1%positive []))).

  Definition dummy_def2 : (ident * tgt_gdef2) :=
    (s2p ".neverused", Gfun (External (EF_debug 1%positive 1%positive []))).

  Definition pre_compile_iFuns (src : progFuns) : option tgt_gdefs2 :=
    let pcfs :=
        List.map
          (fun '(fn, f) => match (pre_compile_function f) with
                        | Some cf => Some (s2p fn, Gfun (Internal cf))
                        | None => None
                        end)
          src in
    if (Forall_dec (fun optf => match optf with | Some _ => True | None => False end) option_dec pcfs)
    then Some (List.map (fun optf => match optf with | Some tf => tf | None => dummy_def2 end) pcfs)
    else None.

  Record gmap := mk_gmap {
    _ext_vars : tgt_gdefs2;
    _ext_funs : tgt_gdefs2;
    _int_vars : tgt_gdefs2;
    _int_funs : tgt_gdefs2;
  }.

  Definition get_gmap (src : Imp.programL) :=
    let cev := (compile_eVars src.(ext_varsL)) in
    let cef := (compile_eFuns src.(ext_funsL)) in
    let civ := (compile_iVars src.(prog_varsL)) in
    do pre_ifuns <- (pre_compile_iFuns (List.map snd src.(prog_funsL)));
    if (Coqlib.list_norepet_dec dec (List.map fst (pre_ifuns ++ cef ++ civ ++ cev)))
    then Some (mk_gmap cev cef civ pre_ifuns)
    else None
  .

  Variable gm : gmap.

  Definition get_funsig (tf: tgt_gdef2) :=
    match tf with
    | Gfun fd2 =>
      match fd2 with
      | Internal f2 => Some (fn_sig2 f2)
      | External ef => Some (ef_sig ef)
      end
    | _ => None
    end.

  (* Imp has no type, value is either int64/ptr64 -> sem_cast can convert *)
  Fixpoint compile_stmt (stmt: Imp.stmt) : option Csharpminor.stmt :=
    match stmt with
    | Skip => Some (Sskip)
    | Assign x e =>
      do ex <- (compile_expr e); Some (Sset (s2p x) ex)
    | Seq s1 s2 =>
      do cs1 <- (compile_stmt s1);
      do cs2 <- (compile_stmt s2);
      Some (Sseq cs1 cs2)
    | If cond sif selse =>
      do cc <- (compile_expr cond);
      do cif <- (compile_stmt sif);
      do celse <- (compile_stmt selse);
      let bexp := Ebinop (Ocmplu Cne) cc (Econst (Olongconst Int64.zero)) in
      Some (Sifthenelse bexp cif celse)

    | CallFun x f args =>
      let fdecls := gm.(_ext_funs) ++ gm.(_int_funs) in
      let id := s2p f in
      do tf <- (ident_key id fdecls);
      do fsig <- (get_funsig tf);
      do al <- (compile_exprs args);
      Some (Scall (Some (s2p x)) fsig (Eaddrof id) al)

    (* only supports call by ptr with a variable (no other expr) *)
    | CallPtr x pe args =>
      match pe with
      | Var y =>
        do al <- (compile_exprs args);
        let fsig := make_signature (length al) in
        Some (Scall (Some (s2p x)) fsig (Evar (s2p y)) al)
      | _ => None
      end

    | CallSys x f args =>
      let fdecls := gm.(_ext_funs) in
      let id := s2p f in
      do tf <- (ident_key id fdecls);
      do fsig <- (get_funsig tf);
      do al <- (compile_exprs args);
      Some (Scall (Some (s2p x)) fsig (Eaddrof id) al)

    | AddrOf x GN =>
      let id := s2p GN in
      let decls := gm.(_ext_vars) ++ gm.(_int_vars) ++ gm.(_ext_funs) ++ gm.(_int_funs) in
      do found <- (ident_key id decls);
      Some (Sset (s2p x) (Eaddrof id))

    | Malloc x se =>
      do a <- (compile_expr se);
      let adjofs := Ebinop Omull (Econst (Olongconst (Int64.repr 8))) a in
      Some (Scall (Some (s2p x)) (ef_sig EF_malloc) (Eaddrof (s2p "malloc")) [adjofs])
    | Free pe =>
      do p <- (compile_expr pe);
      Some (Sseq Sskip Sskip)
    | Load x pe =>
      do cpe <- (compile_expr pe);
      Some (Sset (s2p x) (Eload Mint64 cpe))
    | Store pe ve =>
      do cpe <- (compile_expr pe);
      do cve <- (compile_expr ve);
      Some (Sstore Mint64 cpe cve)
    | Cmp x ae be =>
      do cae <- (compile_expr ae);
      do cbe <- (compile_expr be);
      let cmpexpr := (Ebinop (Ocmplu Ceq) cae cbe) in
      Some (Sset (s2p x) cmpexpr)
    end
  .

  (* Fixpoint NoDupB {A} decA (l : list A) : bool := *)
  (*   match l with *)
  (*   | [] => true *)
  (*   | h :: t => *)
  (*     if in_dec decA h t then false else NoDupB decA t *)
  (*   end *)
  (* . *)
  (* Coqlib.list_norepet_dec *)

  (* Definition compile_function (f : Imp.function) : option function := *)
  (*   do prefun <- (pre_compile_function f); *)
  (*   do fbody <- (compile_stmt f.(Imp.fn_body)); *)
  (*   let fdef := {| *)
  (*         fn_sig := prefun.(fn_sig); *)
  (*         fn_params := prefun.(fn_params); *)
  (*         fn_vars := prefun.(fn_vars); *)
  (*         fn_temps := prefun.(fn_temps); *)
  (*         fn_body := Sseq fbody (Sreturn (Some (Evar (s2p "return")))); *)
  (*       |} in *)
  (*   Some fdef. *)

  (* Fixpoint compile_iFuns (src : progFuns) : option tgt_gdefs := *)
  (*   match src with *)
  (*   | [] => Some [] *)
  (*   | (name, f) :: t => *)
  (*     do tail <- (compile_iFuns t); *)
  (*     do cf <- (compile_function f); *)
  (*     let gf := Internal cf in *)
  (*     Some ((s2p name, Gfun gf) :: tail) *)
  (*   end *)
  (* . *)

  Definition get_function (df2 : tgt_gdef2) : option tgt_gdef :=
    match df2 with
    | Gfun (Internal f2) =>
      do _fbody <- (compile_stmt f2.(fn_body2));
      let fbody := Sseq _fbody (Sreturn (Some (Evar (s2p "return")))) in
      let f := mkfunction (fn_sig2 f2) (fn_params2 f2) (fn_vars2 f2) (fn_temps2 f2) (fbody) in
      Some (Gfun (Internal f))
    | _ => None
    end
  .

  Definition lift_def (df2 : tgt_gdef2) : tgt_gdef :=
    match df2 with
    | Gfun (Internal _) =>
      match (get_function df2) with
      | Some df => df
      | None => snd dummy_def
      end
    | Gfun (External ef) => Gfun (External ef)
    | Gvar gv => Gvar gv
    end.

  Definition get_iFuns (pre : tgt_gdefs2) : option tgt_gdefs :=
    let tfs :=
        List.map
          (fun '(fn, df2) => match (get_function df2) with
                        | Some df => Some (fn, df)
                        | None => None
                          end)
          pre in
    if (Forall_dec (fun optf => match optf with | Some _ => True | None => False end) option_dec tfs)
    then Some (List.map (fun optf => match optf with | Some tf => tf | None => dummy_def end) tfs)
    else None.

  Let init_g : tgt_gdefs :=
    [(s2p "malloc", Gfun malloc_def); (s2p "free", Gfun free_def)].

  Definition compile_gdefs (src : Imp.programL) : option tgt_gdefs :=
    let lift_all := fun '(n, d) => (n, lift_def d) in
    let evars := List.map lift_all gm.(_ext_vars) in
    let ivars := List.map lift_all gm.(_int_vars) in
    let efuns := List.map lift_all gm.(_ext_funs) in
    do ifuns <- get_iFuns gm.(_int_funs);
    let defs := efuns ++ evars ++ init_g ++ ifuns ++ ivars in
    Some defs
  .

  Definition _compile (src : Imp.programL) : res program :=
    let optdefs := (compile_gdefs src) in
    match optdefs with
    | None => Error [MSG "Imp2csharpminor compilation failed"]
    | Some _defs =>
      if (Coqlib.list_norepet_dec dec (List.map fst _defs)) then
        let pdefs := Maps.PTree_Properties.of_list _defs in
        let defs := Maps.PTree.elements pdefs in
        OK (mkprogram defs (List.map s2p src.(publicL)) (s2p "main"))
      else Error [MSG "Imp2csharpminor compilation failed; duplicated declarations"]
    end
  .

  Definition _compile2 (src : Imp.programL) : res program :=
    let optdefs := (compile_gdefs src) in
    match optdefs with
    | None => Error [MSG "Imp2csharpminor compilation failed"]
    | Some _defs =>
      if (Coqlib.list_norepet_dec dec (List.map fst _defs)) then
        OK (mkprogram _defs (List.map s2p src.(publicL)) (s2p "main"))
      else Error [MSG "Imp2csharpminor compilation failed; duplicated declarations"]
    end
  .

End Compile.

Definition compile (src : Imp.programL) :=
  match (get_gmap src) with
  | Some gm => _compile gm src
  | _ => Error [MSG "Imp2csharpminor compilation failed"]
  end.

Definition compile2 (src : Imp.programL) :=
  match (get_gmap src) with
  | Some gm => _compile2 gm src
  | _ => Error [MSG "Imp2csharpminor compilation failed"]
  end.

Module ASMGEN.

  Import Compiler.

  (* For builtins at compile time, ref: Velus, Generation.v *)
  Fixpoint list_type_to_typelist (types: list type): typelist :=
    match types with
    | [] => Tnil
    | h :: t => Tcons h (list_type_to_typelist t)
    end
  .

  Definition transf_csharpminor_program (p: Csharpminor.program) : res Asm.program :=
    OK p
       @@@ time "Cminor generation" Cminorgen.transl_program
       @@@ transf_cminor_program.

End ASMGEN.

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
    Coqlib.list_norepet_dec decK (l1_k ++ l2_k).

  (* check defined names are unique *)
  Definition link_imp_cond1 :=
    check_name_unique1 string_Dec l_prog_varsL l_prog_funsL.

  Let check_name_unique2 {K} {B} decK
      (l1 : list K) (l2 : list (K * B)) :=
    let l2_k := List.map fst l2 in
    Coqlib.list_norepet_dec decK (l1 ++ l2_k).

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
      forall v, match_val (EVlong v) (Vint (Int64.signed v)).

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
