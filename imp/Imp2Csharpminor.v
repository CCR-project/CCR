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

Lemma option2bool {T} :
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

  (* Definition ident_key {T} (id: ident) l : option T := alist_find id l. *)

  Fixpoint compile_expr (expr: Imp.expr) : Csharpminor.expr :=
    match expr with
    | Var x => Evar (s2p x)
    | Lit z => Econst (Olongconst (Int64.repr z))
    | Plus a b =>
      let ca := compile_expr a in let cb := compile_expr b in (Ebinop Oaddl ca cb)
    | Minus a b =>
      let ca := compile_expr a in let cb := compile_expr b in (Ebinop Osubl ca cb)
    | Mult a b =>
      let ca := compile_expr a in let cb := compile_expr b in (Ebinop Omull ca cb)
    end
  .

  Definition compile_exprs (exprs: list Imp.expr) : list Csharpminor.expr := List.map (compile_expr) exprs.

  Definition make_signature n := mksignature (repeat Tlong n) (Tlong) (cc_default).

  (* Imp has no type, value is either int64/ptr64 -> sem_cast can convert *)
  Fixpoint compile_stmt (stmt: Imp.stmt) : Csharpminor.stmt :=
    match stmt with
    | Skip =>
      Sskip
    | Assign x e =>
      let ex := compile_expr e in (Sset (s2p x) ex)
    | Seq s1 s2 =>
      let cs1 := (compile_stmt s1) in
      let cs2 := (compile_stmt s2) in
      (Sseq cs1 cs2)
    | If cond sif selse =>
      let cc := (compile_expr cond) in
      let cif := (compile_stmt sif) in
      let celse := (compile_stmt selse) in
      let bexp := Ebinop (Ocmplu Cne) cc (Econst (Olongconst Int64.zero)) in
      (Sifthenelse bexp cif celse)

    | CallFun x f args =>
      let id := s2p f in
      let sig := (make_signature (List.length args)) in
      let al := (compile_exprs args) in
      (Scall (Some (s2p x)) sig (Eaddrof id) al)

    (* only supports call by ptr with a variable (no other expr) (syntatic check would be nice here...) *)
    | CallPtr x pe args =>
      match pe with
      | Var y =>
        let sig := make_signature (length args) in
        let al := (compile_exprs args) in
        (Scall (Some (s2p x)) sig (Evar (s2p y)) al)
      | _ => Sskip
      end

    | CallSys x f args =>
      let id := s2p f in
      let sig := (make_signature (List.length args)) in
      let al := (compile_exprs args) in
      (Scall (Some (s2p x)) sig (Eaddrof id) al)

    | AddrOf x gn =>
      let id := s2p gn in
      (Sset (s2p x) (Eaddrof id))

    | Malloc x se =>
      let a := (compile_expr se) in
      let adjofs := Ebinop Omull (Econst (Olongconst (Int64.repr 8))) a in
      (Scall (Some (s2p x)) (ef_sig EF_malloc) (Eaddrof (s2p "malloc")) [adjofs])
    | Free pe =>
      let p := (compile_expr pe) in
      (Sseq Sskip Sskip)
    | Load x pe =>
      let cpe := (compile_expr pe) in
      (Sset (s2p x) (Eload Mint64 cpe))
    | Store pe ve =>
      let cpe := (compile_expr pe) in
      let cve := (compile_expr ve) in
      (Sstore Mint64 cpe cve)
    | Cmp x ae be =>
      let cae := (compile_expr ae) in
      let cbe := (compile_expr be) in
      let cmpexpr := Eunop Olongofint (Ebinop (Ocmplu Ceq) cae cbe) in
      (Sset (s2p x) cmpexpr)
    end
  .

  (** memory accessing calls *)
  (** load, store, cmp are translated to non-function calls. *)
  (** register alloc and free in advance so can be properly called *)
  Let malloc_def : fundef := External EF_malloc.
  Let free_def : fundef := External EF_free.

  Definition compile_eVar : string -> (ident * tgt_gdef) :=
    fun id => (s2p id, Gvar (mkglobvar () [] false false)).

  Definition compile_eVars (src : extVars) : tgt_gdefs := List.map compile_eVar src.


  Definition compile_iVar : (string * Z) -> (ident * tgt_gdef) :=
    fun '(id, z) => (s2p id, Gvar (mkglobvar () [Init_int64 (Int64.repr z)] false false)).

  Definition compile_iVars (src : progVars) : tgt_gdefs := List.map compile_iVar src.


  Definition compile_eFun : (string * nat) -> (ident * tgt_gdef) :=
    fun '(id, a) => (s2p id, Gfun (External (EF_external id (make_signature a)))).

  Definition compile_eFuns (src : extFuns) : tgt_gdefs := List.map compile_eFun src.


  Definition compile_iFun : (string * (string * Imp.function)) -> (ident * tgt_gdef) :=
    fun '(_, (fn, f)) =>
      let params := (List.map (fun vn => s2p vn) f.(Imp.fn_params)) in
      let temps := (List.map (fun vn => s2p vn) f.(Imp.fn_vars)) ++ [(s2p "return"); (s2p "_")] in
      let sig := if (rel_dec fn "main"%string) then signature_main else (make_signature (List.length params)) in
      let _body := compile_stmt f.(Imp.fn_body) in
      let body :=
          if (rel_dec fn "main"%string)
          then (Sseq _body (Sreturn (Some (Eunop Ointoflong (Evar (s2p "return"))))))
          else (Sseq _body (Sreturn (Some (Evar (s2p "return"))))) in
      let fdef := {|
            fn_sig := sig;
            fn_params := params;
            fn_vars := [];
            fn_temps := temps;
            fn_body := body;
          |} in
      (s2p fn, Gfun (Internal fdef)).

  Definition compile_iFuns (src : list (string * (string * Imp.function))) : tgt_gdefs := List.map compile_iFun src.


  Definition init_g0 : list (string * tgt_gdef) :=
    [("malloc"%string, Gfun malloc_def); ("free"%string, Gfun free_def)].

  Definition init_g : tgt_gdefs := List.map (fun '(name, fd) => (s2p name, fd)) init_g0.

  Definition c_sys := List.map compile_eFun syscalls.

  Definition compile_gdefs (src : Imp.programL) : tgt_gdefs :=
    let evars := compile_eVars src.(ext_varsL) in
    let ivars := compile_iVars src.(prog_varsL) in
    let efuns := compile_eFuns src.(ext_funsL) in
    let ifuns := compile_iFuns src.(prog_funsL) in
    let defs := init_g ++ c_sys ++ efuns ++ evars ++ ifuns ++ ivars in
    defs.

End Compile.

Definition compile (src : Imp.programL) : res program :=
  let _defs := (compile_gdefs src) in
  if (Coqlib.list_norepet_dec dec (List.map fst _defs)) then
    let pdefs := Maps.PTree_Properties.of_list _defs in
    let defs := Maps.PTree.elements pdefs in
    OK (mkprogram defs (List.map s2p src.(publicL)) (s2p "main"))
  else Error [MSG "Imp2csharpminor compilation failed; duplicated declarations"]
.

Definition compile_imp p := compile (lift p).

Global Opaque init_g0.
Global Opaque init_g.


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
