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

Import Int.

Set Implicit Arguments.

Parameter s2p: string -> ident.
Parameter s2p_inj: forall x y, (s2p x) = (s2p y) -> x = y.

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

  Definition make_signature n := mksignature (repeat Tlong n) (Tlong) (cc_default).

  Definition compile_eVars src : tgt_gdefs2 :=
    let gv := (mkglobvar () [] false false) in List.map (fun id => (s2p id, Gvar gv)) src.

  Definition compile_iVars src : tgt_gdefs2 :=
    List.map (fun '(id, z) => (s2p id, Gvar (mkglobvar () [Init_int64 (Int64.repr z)] false false))) src.

  Definition compile_eFuns (src : extFuns) : tgt_gdefs2 :=
    List.map (fun '(id, a) => (s2p id, Gfun (External (EF_external id (make_signature a))))) src.

  Definition pre_compile_function (fn : string) (f : Imp.function) : option function2 :=
    let params := (List.map (fun vn => s2p vn) f.(Imp.fn_params)) in
    let temps := (List.map (fun vn => s2p vn) f.(Imp.fn_vars)) ++ [(s2p "return"); (s2p "_")] in
    let sig := if (rel_dec fn "main"%string) then signature_main else (make_signature (List.length params)) in
    if (Coqlib.list_norepet_dec dec (params ++ temps)) then
      let fdef := {|
            fn_sig2 := sig;
            fn_params2 := params;
            fn_vars2 := [];
            fn_temps2 := temps;
            fn_body2 := f.(Imp.fn_body);
          |} in
      Some fdef
    else None.

  Definition dummy_def : (ident * tgt_gdef) :=
    (s2p ".neverused", Gfun (External (EF_debug 1%positive 1%positive []))).

  Definition dummy_def2 : (ident * tgt_gdef2) :=
    (s2p ".neverused", Gfun (External (EF_debug 1%positive 1%positive []))).

  Definition pre_compile_iFuns (src : progFuns) : option tgt_gdefs2 :=
    let pcfs :=
        List.map
          (fun '(fn, f) => match (pre_compile_function fn f) with
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
      let cmpexpr := Eunop Olongofint (Ebinop (Ocmplu Ceq) cae cbe) in
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

  Definition get_function (id : ident) (df2 : tgt_gdef2) : option tgt_gdef :=
    match df2 with
    | Gfun (Internal f2) =>
      do _fbody <- (compile_stmt f2.(fn_body2));
      let fbody :=
          if (rel_dec id (s2p "main"))
          then Sseq _fbody (Sreturn (Some (Eunop Ointoflong (Evar (s2p "return")))))
          else Sseq _fbody (Sreturn (Some (Evar (s2p "return")))) in
      let f := mkfunction (fn_sig2 f2) (fn_params2 f2) (fn_vars2 f2) (fn_temps2 f2) (fbody) in
      Some (Gfun (Internal f))
    | _ => None
    end
  .

  Definition lift_def (id : ident) (df2 : tgt_gdef2) : tgt_gdef :=
    match df2 with
    | Gfun (Internal _) =>
      match (get_function id df2) with
      | Some df => df
      | None => snd dummy_def
      end
    | Gfun (External ef) => Gfun (External ef)
    | Gvar gv => Gvar gv
    end.

  Definition get_iFuns (pre : tgt_gdefs2) : option tgt_gdefs :=
    let tfs :=
        List.map
          (fun '(fn, df2) => match (get_function fn df2) with
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
    let lift_all := fun '(n, d) => (n, lift_def n d) in
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

End Compile.

Definition compile (src : Imp.programL) :=
  match (get_gmap src) with
  | Some gm => _compile gm src
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

Section Beh.

  Inductive match_val : eventval -> val -> Prop :=
  | match_val_intro :
      forall v, match_val (EVlong v) (Vint (Int64.signed v)).

  Inductive match_event : Events.event -> Universe.event -> Prop :=
  | match_event_intro
      name eargs uargs er ur
      (MV: Forall2 match_val eargs uargs)
      (MV: match_val er ur)
    :
      match_event (Event_syscall name eargs er) (event_sys name uargs ur)
  .

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
