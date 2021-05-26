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
     Ctypes AST Integers Cminor Csharpminor Globalenvs Linking Errors Cminorgen Behaviors Events.

From compcert Require Compiler.

(* From compcert Require Import Cminor Cminortyping. *)
(* Import RTLtypes. *)

Import Int.

Set Implicit Arguments.

Parameter s2p: string -> ident.

Definition to_long := Int64.repr.

Section Compile.

  (* compile each program indiv,
     prove behavior refinement for whole (closed) prog after linking *)
  Let tgt_gdef := globdef fundef ().
  Let tgt_gdefs := list (ident * tgt_gdef).

  (* Definition Tlong0 := (Tlong Signed noattr). *)
  (* Definition Tptr0 tgt_ty := (Tpointer tgt_ty noattr). *)

  Definition ident_key {T} id l : option T :=
    SetoidList.findA (Pos.eqb id) l.

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
      | Vint z => Some (Econst (Olongconst (to_long z)))
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

  Fixpoint compile_exprs (exprs: list Imp.expr) acc : option (list Csharpminor.expr) :=
    match exprs with
    | h :: t => do hexp <- (compile_expr h); compile_exprs t (acc ++ [hexp])
    | [] => Some acc
    end
  .

  (* Fixpoint make_arg_types n := *)
  (*   match n with *)
  (*   | O => Tnil *)
  (*   | S n' => Tcons Tlong0 (make_arg_types n') *)
  (*   end *)
  (* . *)

  Definition make_signature n :=
    mksignature (repeat Tlong n) (Tlong) (cc_default).

  Record gmap := mk_gmap {
    _ext_vars : list ident;
    _ext_funs : list (ident * signature);
    _int_vars : list ident;
    _int_funs : list (ident * signature);
  }.

  Let get_gmap_efuns : extFuns -> list (ident * signature) :=
    fun src => List.map (fun '(name, n) => (s2p name, make_signature n)) src.

  Let get_gmap_ifuns : progFuns -> list (ident * signature) :=
    fun src =>
      List.map (fun '(name, f) => (s2p name, make_signature (length f.(Imp.fn_params)))) src.

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
  Let malloc_def : fundef := External EF_malloc.

  Let free_def : fundef := External EF_free.

  Variable gm : gmap.

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
      do fsig <- (ident_key id fdecls);
      do al <- (compile_exprs args []);
      Some (Scall (Some (s2p x)) fsig (Eaddrof id) al)

    (* only supports call by ptr with a variable (no other expr) *)
    | CallPtr x pe args =>
      match pe with
      | Var y =>
        do al <- (compile_exprs args []);
        let fsig := make_signature (length al) in
        Some (Scall (Some (s2p x)) fsig (Evar (s2p y)) al)
      | _ => None
      end

    | CallSys x f args =>
      let fdecls := gm.(_ext_funs) in
      let id := s2p f in
      do fsig <- (ident_key id fdecls);
      do al <- (compile_exprs args []);
      Some (Scall (Some (s2p x)) fsig (Eaddrof id) al)

    | AddrOf x GN =>
      let id := s2p GN in
      let vdecls := gm.(_ext_vars) ++ gm.(_int_vars) in
      let fdecls := gm.(_ext_funs) ++ gm.(_int_funs) in
      if (existsb (fun p => Pos.eqb id p) vdecls)
      then Some (Sset (s2p x) (Eaddrof id))
      else
        do fty <- (ident_key id fdecls);
        Some (Sset (s2p x) (Eaddrof id))

    | Malloc x se =>
      do a <- (compile_expr se);
      Some (Scall (Some (s2p x)) (ef_sig EF_malloc) (Eaddrof (s2p "malloc")) [a])
    | Free pe =>
      do a <- (compile_expr pe);
      Some (Scall None (ef_sig EF_free) (Eaddrof (s2p "free")) [a])
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

  Definition compile_eVars src : tgt_gdefs :=
    let gv := (mkglobvar () [] false false) in
    List.map (fun id => (s2p id, Gvar gv)) src.

  Definition compile_iVars src : tgt_gdefs :=
    List.map (fun '(id, z) => (s2p id, Gvar (mkglobvar () [Init_int64 (to_long z)] false false))) src.

  Definition compile_eFuns (src : extFuns) : tgt_gdefs :=
    List.map (fun '(id, a) => (s2p id, Gfun (External (EF_external id (make_signature a))))) src.

  Definition compile_function (f : Imp.function) : option function :=
    do fbody <- (compile_stmt f.(Imp.fn_body));
    let fdef := {|
          fn_sig := make_signature (List.length f.(Imp.fn_params));
          fn_params := (List.map (fun vn => s2p vn) f.(Imp.fn_params));
          fn_vars := [];
          fn_temps := (List.map (fun vn => s2p vn) f.(Imp.fn_vars)) ++ [(s2p "return"); (s2p "_")];
          fn_body := Sseq fbody (Sreturn (Some (Evar (s2p "return"))));
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

  (* Let id_init := List.map fst init_g. *)

  Fixpoint NoDupB {A} decA (l : list A) : bool :=
    match l with
    | [] => true
    | h :: t =>
      if in_dec decA h t then false else NoDupB decA t
    end
  .

  (* Definition imp_prog_ids (src : Imp.programL) := *)
  (*   let id_ev := List.map s2p src.(ext_varsL) in *)
  (*   let id_ef := List.map (fun p => s2p (fst p)) src.(ext_funsL) in *)
  (*   let id_iv := List.map (fun p => s2p (fst p)) src.(prog_varsL) in *)
  (*   let id_if := List.map (fun p => s2p (fst (snd p))) src.(prog_funsL) in *)
  (*   id_init ++ id_ev ++ id_ef ++ id_iv ++ id_if *)
  (* . *)

  Definition compile_gdefs (src : Imp.programL) : option tgt_gdefs :=
    let evars := compile_eVars src.(ext_varsL) in
    let ivars := compile_iVars src.(prog_varsL) in
    let efuns := compile_eFuns src.(ext_funsL) in
    do ifuns <- compile_iFuns (List.map snd src.(prog_funsL));
    let defs := init_g ++ evars ++ efuns ++ ivars ++ ifuns in
    Some defs
  .

  Definition _compile (src : Imp.programL) : res program :=
    let optdefs := (compile_gdefs src) in
    match optdefs with
    | None => Error [MSG "Imp2clight compilation failed"]
    | Some _defs =>
      if (@NoDupB _ positive_Dec (List.map fst _defs)) then
        let pdefs := Maps.PTree_Properties.of_list _defs in
        let defs := Maps.PTree.elements pdefs in
        OK (mkprogram defs (List.map s2p src.(publicL)) (s2p "main"))
      else Error [MSG "Imp2clight compilation failed; duplicated declarations"]
    end
  .

End Compile.

Definition compile (src : Imp.programL) :=
  _compile (get_gmap src) src.

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

  Definition itree_of_imp (itr: itree _ val) :=
    fun ge le ms mn rp =>
      EventsL.interp_Es (ModSemL.prog ms) (transl_all mn (vret <- ('(_, retv) <- (interp_imp ge le (itr;; retv <- denote_expr (Var "return"%string);; Ret retv));; Ret retv);; Ret (vret↑))) rp.

  Definition itree_of_imp_cont itr :=
    fun ge le ms mn rp =>
      EventsL.interp_Es (ModSemL.prog ms) (transl_all mn (lv <- (interp_imp ge le itr);; Ret (lv))) rp.

  Definition itree_of_imp_ret :=
    fun ge le ms mn rp =>
      itree_of_imp_cont (retv <- denote_expr (Var "return"%string);; Ret retv) ge le ms mn rp.

  Definition itree_of_imp_fun (itr: itree _ val) :=
    fun ge le ms mn rp =>
      itree_of_imp_cont (itr;; retv <- denote_expr (Var "return"%string);; Ret retv) ge le ms mn rp.

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

  Lemma itree_of_imp_fun_splits
        itr ge le ms mn rp
    :
      itree_of_imp_fun itr ge le ms mn rp
      =
      '(r, p, (le2, v)) <- (itree_of_imp_cont itr ge le ms mn rp);; (itree_of_imp_ret ge le2 ms mn (r, p)).
  Proof.
    unfold itree_of_imp_fun, itree_of_imp_ret. rewrite itree_of_imp_cont_bind. reflexivity.
  Qed.

  Definition itree_of_imp_pop :=
    fun ms mn (x: _ * _ * (lenv * val)) =>
      let '(r, p, (_, v)) := x in
      EventsL.interp_Es (ModSemL.prog ms) (transl_all mn (Ret (v↑))) (r, p).

  Lemma itree_of_imp_split_cont_pop
        ge le ms mn rp itr
    :
      itree_of_imp itr ge le ms mn rp
      =
      (x <- (itree_of_imp_fun itr ge le ms mn rp);; (itree_of_imp_pop ms mn x)).
  Proof.
    unfold itree_of_imp, itree_of_imp_fun, itree_of_imp_ret, itree_of_imp_cont, itree_of_imp_pop. grind.
    rewrite! transl_all_bind; rewrite! EventsL.interp_Es_bind. grind.
  Qed.

  Definition itree_of_cont_stmt (s : Imp.stmt) :=
    fun ge le ms mn rp => itree_of_imp_cont (denote_stmt s) ge le ms mn rp.

  Definition itree_of_fun_body (fb : Imp.stmt) :=
    fun ge le ms mn rp => itree_of_imp_fun (denote_stmt fb) ge le ms mn rp.

  Definition imp_state := itree eventE Any.t.
  Definition imp_cont := (r_state * p_state * (lenv * val)) -> itree eventE (r_state * p_state * (lenv * val)).
  Definition imp_stack := (r_state * p_state * Any.t) -> imp_state.

  (* Hypothesis archi_ptr64 : Archi.ptr64 = true. *)
  Definition map_val (v : Universe.val) : Values.val :=
    match v with
    | Vint z => Values.Vlong (to_long z)
    | Vptr blk ofs =>
      Values.Vptr (Pos.of_nat (blk+1)) (Ptrofs.repr ofs)
    | Vundef => Values.Vundef
    end.

  Definition map_val_opt (optv : option Universe.val) : option Values.val :=
    match optv with
    | Some v => Some (map_val v)
    | None => None
    end.

  Variant match_le : lenv -> temp_env -> Prop :=
  | match_le_intro
      sle tle
      (ML: forall x sv,
          (alist_find x sle = sv) ->
          (exists tv, (Maps.PTree.get (s2p x) tle = tv) /\
                 (tv = map_val_opt sv)))
    :
      match_le sle tle.

  (* match_genv: ge = Sk.load_skenv imp.(defs), tgtge = globalenv (compile imp),
                 need to show they match only at beginning *)

  Definition id2blk_cgenv (src: Imp.program) (id: string) : option positive :=
    match compile src with
    | Error _ => None
    | OK tgt =>
      let tgenv := Genv.globalenv tgt in
      Genv.find_symbol tgenv (s2p id)
    end.

  Lemma id2blk_cgenv_correct
        (src: Imp.program) tgt tgenv id
        (COMP: compile src = OK tgt)
        (TGE: tgenv = Genv.globalenv tgt)
    :
      Genv.find_symbol tgenv (s2p id) = id2blk_cgenv src id.
  Proof.
    unfold id2blk_cgenv. clarify. rewrite COMP. auto.
  Qed.

  (* Variable match_ge : SkEnv.t -> genv -> Prop. *)

  Variable match_mem : Mem.t -> Memory.Mem.mem -> Prop.

  (* Definition wf_ccont (cc: cont) : Prop := *)
  (*   match cc with *)
  (*   | Kstop | Kseq _ _ | Kcall _ _ _ _ _ => True *)
  (*   | _ => False *)
  (*   end. *)

  Fixpoint get_cont_stmts (cc: cont) : list Csharpminor.stmt :=
    match cc with
    | Kseq s k => s :: (get_cont_stmts k)
    | Kblock k => get_cont_stmts k
    | _ => []
    end
  .

  (* global env is fixed when src program is fixed *)
  Variable gm : gmap.
  Variable ge : SkEnv.t.
  (* ModSem should be fixed with src too *)
  Variable ms : ModSemL.t.

  Inductive match_code (mn: string) : imp_cont -> (list Csharpminor.stmt) -> Prop :=
  | match_code_nil
    :
      match_code mn idK []
  | match_code_cons
      code itr ktr chead ctail
      (CST: compile_stmt gm code = Some chead)
      (ITR: itr = fun '(r, p, (le, _)) => itree_of_cont_stmt code ge le ms mn (r, p))
      (MC: match_code mn ktr ctail)
    :
      match_code mn (fun x => (itr x >>= ktr)) (chead :: ctail)
  .

  Inductive match_stack : imp_stack -> Csharpminor.cont -> Prop :=
  | match_stack_bottom
    :
      match_stack (fun '(r, p, x) => Ret x) Kstop

  | match_stack_cret
      tf mn le tle next stack tcont id tid glue tglue
      (MLE: match_le le tle)
      (MID: s2p id = tid)

      (GLUE: glue = fun '(r, p, v) =>
                      itree_of_imp_cont (` v0 : val <- (v↓)?;; trigger (SetVar id v0);; Ret Vundef) ge le ms mn (r, p))

      (MCONT: match_code mn next (get_cont_stmts tcont))
      (MSTACK: match_stack stack (call_cont tcont))

      (TGLUE: tglue = Kcall (Some tid) tf empty_env tle tcont)
    :
      match_stack (fun x => (y <- (glue x);; z <- next y;; (itree_of_imp_pop ms mn z) >>= stack)) (tglue)
  .

  Variant match_states : imp_state -> Csharpminor.state -> Prop :=
  | match_states_intro
      tf rp mn le tle code itr tcode m tm next stack tcont
      (* function is only used to check return type, which compiled one always has Tlong0, except "main" which has *)
      (* (CF: compile_function gm f = Some tgtf) *)
      (CST: compile_stmt gm code = Some tcode)
      (ML: match_le le tle)
      (MM: match_mem m tm)
      (* (MG: match_ge ge tge) *)
      (* (WFCONT: wf_ccont tcont) *)
      (MCS: match_code mn next (get_cont_stmts tcont))
      (MCN: match_stack stack (call_cont tcont))
      (ITR: itr = itree_of_cont_stmt code ge le ms mn rp)
    :
      match_states (x <- itr;; y <- next x;; (itree_of_imp_pop ms mn y) >>= stack) (State tf tcode tcont empty_env tle tm)
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

  (* Definition wf_imp_prog (src : Imp.programL) := *)
  (*   Coqlib.list_norepet (compile_gdefs (get_gmap src) src). *)

  (* Lemma compile_then_wf : forall src tgt, *)
  (*     compile src = OK tgt *)
  (*     -> *)
  (*     wf_imp_prog src. *)
  (* Proof. *)
  (*   unfold compile, _compile. i. *)
  (*   destruct (compile_gdefs (get_gmap src) src) eqn:EQ; clarify. *)
  (*   eauto using compile_gdefs_then_wf. *)
  (* Qed. *)

  (* Maps.PTree.elements_extensional
     we will rely on above theorem for commutation lemmas *)
  Lemma _comm_link_imp_compile :
    forall src1 src2 srcl tgt1 tgt2 tgtl,
      compile src1 = OK tgt1 -> compile src2 = OK tgt2 ->
      link_imp src1 src2 = Some srcl ->
      link_prog tgt1 tgt2 = Some tgtl ->
      compile srcl = OK tgtl.
  Proof.
  Admitted.

  Definition wf_link {T} (program_list : list T) :=
    exists h t, program_list = h :: t.

  Inductive compile_list :
    list programL -> list (Csharpminor.program) -> Prop :=
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

  Definition link_clight_list (tgt_list : list (Csharpminor.program)) :=
    match tgt_list with
    | [] => None
    | tgt_h :: tgt_t =>
      fold_left_option link_prog tgt_t (Some tgt_h)
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
    destruct (link_prog p0 tgt_h) eqn:LPt; ss; clarify.
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
      program_behaves (Csharpminor.semantics tgt) beh ->
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
      program_behaves (Csharpminor.semantics tgtl) beh ->
      exists mbeh,
        match_beh beh mbeh /\ Beh.of_program (ModL.compile srclM) mbeh.
  Proof.
  Admitted.

End Proof.
