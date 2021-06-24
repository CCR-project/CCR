(** * The Imp language  *)

Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.
Require Import AList.

Set Implicit Arguments.

(* ========================================================================== *)
(** ** Syntax *)

(** Imp manipulates a countable set of variables represented as [string]s: *)
Definition var : Set := string.

(** Expressions are made of variables, constant literals, and arithmetic operations. *)
Inductive expr : Type :=
| Var (_ : var)
| Lit (_ : Z)
| Plus  (_ _ : expr)
| Minus (_ _ : expr)
| Mult  (_ _ : expr)
.

(** function call exists only as a statement *)
Inductive stmt : Type :=
| Skip                           (* ; *)
| Assign (x : var) (e : expr)    (* x = e *)
| Seq    (a b : stmt)            (* a ; b *)
| If     (i : expr) (t e : stmt) (* if (i) then { t } else { e } *)
| CallFun (x : var) (f : gname) (args : list expr) (* x = f(args), call by name *)
| CallPtr (x : var) (p : expr) (args : list expr)  (* x = f(args), by pointer*)
| CallSys (x : var) (f : gname) (args : list expr) (* x = f(args), system call *)
| AddrOf (x : var) (X : gname)         (* x = &X *)
| Malloc (x : var) (s : expr)          (* x = malloc(s) *)
| Free (p : expr)                      (* free(p) *)
| Load (x : var) (p : expr)            (* x = *p *)
| Store (p : expr) (v : expr)          (* *p = v *)
| Cmp (x : var) (a : expr) (b : expr)  (* memory accessing equality comparison *)
.

(** information of a function *)
Record function : Type := mk_function {
  fn_params : list var;
  fn_vars : list var;     (* disjoint with fn_params *)
  fn_body : stmt
}.



(** ** Supported System Calls by Imp *)
Definition syscalls : list (string * nat) :=
  [("print", 1); ("scan", 1)].

Global Opaque syscalls.


(** ** Program *)

(** program components *)
(* declared external global variables *)
Definition extVars := list gname.
(* declared external functions with arg nums*)
Definition extFuns := list (gname * nat).
(* defined global variables *)
Definition progVars := list (gname * Z).
(* defined internal functions *)
Definition progFuns := list (gname * function).

(** Imp program *)
Record programL : Type := mk_programL {
  nameL : list mname;
  ext_varsL : extVars;
  ext_funsL : extFuns;
  prog_varsL : progVars;
  prog_funsL : list (mname * (gname * function));
  publicL : list gname;
  defsL : list (gname * Sk.gdef);
}.

Record program : Type := mk_program {
  name : mname;
  ext_vars : extVars;
  ext_funs : extFuns;
  prog_vars : progVars;
  prog_funs : progFuns;
  public : list gname :=
    let sys := List.map fst syscalls in
    let evs := ext_vars in
    let efs := List.map fst ext_funs in
    let ivs := List.map fst prog_vars in
    let ifs := List.map fst prog_funs in
    ["malloc"; "free"] ++ sys ++ evs ++ efs ++ ivs ++ ifs;
  defs : list (gname * Sk.gdef) :=
    let fs := (List.map (fun '(fn, _) => (fn, Sk.Gfun)) prog_funs) in
    let vs := (List.map (fun '(vn, vv) => (vn, Sk.Gvar vv)) prog_vars) in
    fs ++ vs;
}.

Definition lift (p : program) : programL :=
  mk_programL
    [p.(name)]
    p.(ext_vars) p.(ext_funs)
    p.(prog_vars) (List.map (fun pf => (p.(name), pf)) p.(prog_funs))
    p.(public) p.(defs).

Coercion lift : program >-> programL.





(* ========================================================================== *)
(** ** Semantics *)

(** Get/Set function local variables *)
Variant ImpState : Type -> Type :=
| GetVar (x : var) : ImpState val
| SetVar (x : var) (v : val) : ImpState unit.

(** Get pointer to a global variable/function *)
Variant GlobEnv : Type -> Type :=
| GetPtr (x: gname) : GlobEnv val
| GetName (p: val) : GlobEnv gname.

Section Denote.

  Context `{Σ: GRA.t}.
  Context {eff : Type -> Type}.
  Context {HasGlobVar: GlobEnv -< eff}.
  Context {HasImpState : ImpState -< eff}.
  Context {HasCall : callE -< eff}.
  Context {HasEvent : eventE -< eff}.

  (** Denotation of expressions *)
  Fixpoint denote_expr (e : expr) : itree eff val :=
    match e with
    | Var v     => u <- trigger (GetVar v) ;; assume (wf_val u) ;;; Ret u
    | Lit n     => assume (wf_val (Vint n)) ;;; Ret (Vint n)
    | Plus a b  => l <- denote_expr a ;; r <- denote_expr b ;; u <- (vadd l r)? ;; assume (wf_val u) ;;; Ret u
    | Minus a b => l <- denote_expr a ;; r <- denote_expr b ;; u <- (vsub l r)? ;; assume (wf_val u) ;;; Ret u
    | Mult a b  => l <- denote_expr a ;; r <- denote_expr b ;; u <- (vmul l r)? ;; assume (wf_val u) ;;; Ret u
    end.

  (** Denotation of statements *)
  Definition is_true (v : val) : option bool :=
    match v with
    | Vint n => if (n =? 0)%Z then Some false else Some true
    | _ => None
    end.

  Fixpoint denote_exprs_acc (es : list expr) (acc : list val) : itree eff (list val) :=
    match es with
    | [] => Ret acc
    | e :: s =>
      v <- denote_expr e;; denote_exprs_acc s (acc ++ [v])
    end.

  Fixpoint denote_exprs (es : list expr) : itree eff (list val) :=
    match es with
    | [] => Ret []
    | e :: s =>
      v <- denote_expr e;;
      vs <- denote_exprs s;;
      Ret (v :: vs)
    end.

  Definition call_ban f :=
    rel_dec f "alloc" || rel_dec f "free" || rel_dec f "load" || rel_dec f "store" || rel_dec f "cmp" || rel_dec f "main".

  Fixpoint denote_stmt (s : stmt) : itree eff val :=
    match s with
    | Skip => tau;; Ret Vundef
    | Assign x e =>
      v <- denote_expr e;; trigger (SetVar x v);;; tau;; Ret Vundef
    | Seq a b =>
      tau;; denote_stmt a;;; denote_stmt b
    | If i t e =>
      v <- denote_expr i;; `b: bool <- (is_true v)?;; tau;;
      if b then (denote_stmt t) else (denote_stmt e)

    | CallFun x f args =>
      if (call_ban f)
      then triggerUB
      else
        eval_args <- denote_exprs args;;
        v <- trigger (Call f (eval_args↑));; v <- unwrapN (v↓);;
        trigger (SetVar x v);;; tau;; Ret Vundef

    | CallPtr x e args =>
      assume (match e with | Var _ => True | _ => False end);;;
      p <- denote_expr e;; f <- trigger (GetName p);;
      if (call_ban f)
      then triggerUB
      else
        eval_args <- denote_exprs args;;
        v <- trigger (Call f (eval_args↑));; v <- unwrapN (v↓);;
        trigger (SetVar x v);;; tau;; Ret Vundef

    | CallSys x f args =>
      sig <- (alist_find f syscalls)? ;; assume (sig = List.length args);;;
      eval_args <- denote_exprs args;;
      v <- trigger (Syscall f eval_args top1);;
      trigger (SetVar x v);;; tau;; Ret Vundef

    | AddrOf x X =>
      v <- trigger (GetPtr X);; trigger (SetVar x v);;; tau;; Ret Vundef
    | Malloc x se =>
      s <- denote_expr se;;
      v <- trigger (Call "alloc" ([s]↑));; v <- unwrapN(v↓);;
      trigger (SetVar x v);;; tau;; Ret Vundef
    | Free pe =>
      p <- denote_expr pe;;
      trigger (Call "free" ([p]↑));;; tau;; Ret Vundef
    | Load x pe =>
      p <- denote_expr pe;;
      v <- trigger (Call "load" ([p]↑));; v <- unwrapN(v↓);;
      trigger (SetVar x v);;; tau;; Ret Vundef
    | Store pe ve =>
      p <- denote_expr pe;; v <- denote_expr ve;;
      trigger (Call "store" ([p ; v]↑));;; tau;; Ret Vundef
    | Cmp x ae be =>
      a <- denote_expr ae;; b <- denote_expr be;;
      v <- trigger (Call "cmp" ([a ; b]↑));; v <- unwrapN (v↓);;
      trigger (SetVar x v);;; tau;; Ret Vundef

    end.

End Denote.





(* ========================================================================== *)
(** ** Interpretation *)

Section Interp.

  Context `{Σ: GRA.t}.
  Definition effs := GlobEnv +' ImpState +' Es.

  Definition handle_GlobEnv {eff} `{eventE -< eff} (ge: SkEnv.t) : GlobEnv ~> (itree eff) :=
    fun _ e =>
      match e with
      | GetPtr X =>
        r <- (ge.(SkEnv.id2blk) X)?;; Ret (Vptr r 0)
      | GetName p =>
        match p with
        | Vptr n 0 => x <- (ge.(SkEnv.blk2id) n)?;; Ret (x)
        | _ => triggerUB
        end
      end.

  Definition interp_GlobEnv {eff} `{eventE -< eff} (ge: SkEnv.t) : itree (GlobEnv +' eff) ~> (itree eff) :=
    interp (case_ (handle_GlobEnv ge) ((fun T e => trigger e) : eff ~> itree eff)).

  (** function local environment *)
  Definition lenv := alist var val.
  Definition handle_ImpState {eff} `{eventE -< eff} : ImpState ~> stateT lenv (itree eff) :=
    fun _ e le =>
      match e with
      | GetVar x => r <- unwrapU (alist_find x le);; Ret (le, r)
      | SetVar x v => Ret (alist_add x v le, tt)
      end.

  Definition interp_ImpState {eff} `{eventE -< eff}: itree (ImpState +' eff) ~> stateT lenv (itree eff) :=
    State.interp_state (case_ handle_ImpState ModSem.pure_state).

  (* Definition interp_imp ge le (itr : itree effs val) := *)
  (*   interp_ImpState (interp_GlobEnv ge itr) le. *)

  Definition interp_imp ge : itree effs ~> stateT lenv (itree Es) :=
    fun _ itr le => interp_ImpState (interp_GlobEnv ge itr) le.

  Fixpoint init_lenv xs : lenv :=
    match xs with
    | [] => []
    | x :: t => (x, Vundef) :: (init_lenv t)
    end
  .

  Fixpoint init_args params args (acc: lenv) : option lenv :=
    match params, args with
    | [], [] => Some acc
    | x :: part, v :: argt =>
      init_args part argt (alist_add x v acc)
    | _, _ => None
    end
  .

  Lemma init_args_prop :
    forall params args acc le
      (INITSOME: init_args params args acc = Some le),
      <<INITLEN: List.length params = List.length args>>.
  Proof.
    induction params; i; ss; clarify.
    { destruct args; ss; clarify. }
    destruct args; ss; clarify. apply IHparams in INITSOME. red. rewrite INITSOME. ss.
  Qed.

  (* 'return' is a fixed register, holding the return value of this function. *)
  (* '_' is a black hole register, holding garbage *)
  Definition eval_imp (ge: SkEnv.t) (f: function) (args: list val) : itree Es val :=
    let vars := f.(fn_vars) ++ ["return"; "_"] in
    let params := f.(fn_params) in
    assume (NoDup (params ++ vars));;;
    match (init_args params args []) with
    | Some iargs =>
      '(_, retv) <- (interp_imp ge (tau;; (denote_stmt f.(fn_body));;; retv <- (denote_expr (Var "return")) ;; Ret retv)
                                    ((init_lenv vars) ++ iargs));; Ret retv
    | None => triggerUB
    end.

End Interp.





(* ========================================================================== *)
(**** ModSem ****)
Module ImpMod.
Section MODSEM.

  Context `{GRA: GRA.t}.

  Set Typeclasses Depth 5.
  (* Instance Initial_void1 : @Initial (Type -> Type) IFun void1 := @elim_void1. (*** TODO: move to ITreelib ***) *)

  Definition modsem (m : program) (ge: SkEnv.t) : ModSem.t := {|
    ModSem.fnsems := List.map (fun '(fn, f) => (fn, cfun (eval_imp ge f))) m.(prog_funs);
    ModSem.mn := m.(name);
    ModSem.initial_mr := ε;
    ModSem.initial_st := tt↑;
  |}.

  Definition get_mod (m : program) : Mod.t := {|
    Mod.get_modsem := fun ge => (modsem m ge);
    Mod.sk := m.(defs);
  |}.

  Definition modsemL (mL : programL) (ge: SkEnv.t) : ModSemL.t := {|
    ModSemL.fnsems :=
      List.map (fun '(mn, (fn, f)) => (fn, fun a => transl_all mn (cfun (eval_imp ge f) a))) mL.(prog_funsL);
    ModSemL.initial_mrs :=
      List.map (fun name => (name, (ε, tt↑))) mL.(nameL);
  |}.

  Definition get_modL (mL : programL) : ModL.t := {|
    ModL.get_modsem := fun ge => (modsemL mL ge);
    ModL.sk := mL.(defsL);
  |}.

  Lemma comm_imp_mod_lift :
      (compose get_modL lift) = (compose Mod.lift get_mod).
  Proof.
    unfold compose. extensionality p. unfold lift. unfold Mod.lift. unfold get_modL, get_mod.
    f_equal. unfold modsemL, modsem. ss. unfold ModSem.lift.
    ss. extensionality sk. f_equal.
    revert sk. induction (prog_funs p); i; ss; clarify.
    destruct a. unfold ModSem.map_snd. f_equal.
    apply IHp0.
  Qed.

End MODSEM.
End ImpMod.
