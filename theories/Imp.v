(** * The Imp language  *)

(* begin hide *)
From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses.

From ExtLib Require Import
     Data.String
     Structures.Monad
     Structures.Traversable
     Data.List
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

From ITree Require Import
     ITree
     ITreeFacts
     Events.MapDefault
     Events.StateFacts.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.

Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.

Set Implicit Arguments.
(* end hide *)

(* ========================================================================== *)
(** ** Syntax *)

(** Imp manipulates a countable set of variables represented as [string]s: *)
Definition var : Set := string.

(** Expressions are made of variables, constant literals, and arithmetic operations. *)
Inductive expr : Type :=
| Var (_ : var)
| Lit (_ : val)
| Plus  (_ _ : expr)
| Minus (_ _ : expr)
| Mult  (_ _ : expr)
.

(** function call exists only as a statement *)
Inductive stmt : Type :=
| Assign (x : var) (e : expr)    (* x = e *)
| Seq    (a b : stmt)            (* a ; b *)
| If     (i : expr) (t e : stmt) (* if (i) then { t } else { e } *)
| While  (t : expr) (b : stmt)   (* while (t) { b } *)
| Skip                           (* ; *)
| CallFun1 (x : var) (f : gname) (args : list expr) (* x = f(args), call by name *)
| CallFun2 (f : gname) (args : list expr) (* f(args) *)
| CallPtr1 (x : var) (p : expr) (args : list expr)  (* x = f(args), call by pointer *)
| CallPtr2 (p : expr) (args : list expr) (* f(args) *)
| CallSys1 (x : var) (f : gname) (args : list expr) (* x = f(args), system call *)
| CallSys2 (f : gname) (args : list expr) (* f(args) *)
| Return1 (e : expr)              (* return e *)
| Return2                         (* return *)
| AddrOf (x : var) (X : gname)   (* x = &X *)
| Load (x : var) (p : expr)      (* x = *p *)
| Store (p : expr) (v : expr)    (* *p = v *)
.

(** information of a function *)
Record function : Type := mk_function {
  fn_params : list var;
  fn_vars : list var; (* disjoint with fn_params *)
  fn_body : stmt
}.

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
    | Var v     => trigger (GetVar v)
    | Lit n     => Ret n
    | Plus a b  => l <- denote_expr a ;; r <- denote_expr b ;; (vadd l r)?
    | Minus a b => l <- denote_expr a ;; r <- denote_expr b ;; (vsub l r)?
    | Mult a b  => l <- denote_expr a ;; r <- denote_expr b ;; (vmul l r)?
    end.

  (** Denotation of statements *)
  Definition while (step : itree eff (unit + val)) : itree eff val :=
    ITree.iter (fun _ => step) tt.

  Definition is_true (v : val) : option bool :=
    match v with
    | Vint n => if (n =? 0)%Z then Some false else Some true
    | _ => None
    end.

  Fixpoint denote_stmt (s : stmt) : itree eff val :=
    match s with
    | Assign x e =>
      v <- denote_expr e;; trigger (SetVar x v);; Ret Vundef
    | Seq a b =>
      denote_stmt a;; denote_stmt b

    | If i t e =>
      v <- denote_expr i;; `b: bool <- (is_true v)?;;
      if b then (denote_stmt t) else (denote_stmt e)

    | While t b =>
      while (v <- denote_expr t;; `c: bool <- (is_true v)?;;
      if c then (denote_stmt b;; Ret (inl tt)) else (Ret (inr Vundef)))

    | Skip => Ret Vundef

    | CallFun1 x f args =>
      if (String.string_dec f "load" || String.string_dec f "store")
      then triggerUB
      else
        eval_args <- (mapT denote_expr args);;
        v <- trigger (Call f (eval_args↑));; v <- unwrapN (v↓);;
        trigger (SetVar x v);; Ret Vundef

    | CallFun2 f args =>
      if (String.string_dec f "load" || String.string_dec f "store")
      then triggerUB
      else
        eval_args <- (mapT denote_expr args);;
        trigger (Call f (eval_args↑));; Ret Vundef

    | CallPtr1 x e args =>
      p <- denote_expr e;; f <- trigger (GetName p);;
      if (String.string_dec f "load" || String.string_dec f "store")
      then triggerUB
      else
        eval_args <- (mapT denote_expr args);;
        v <- trigger (Call f (eval_args↑));; v <- unwrapN (v↓);;
        trigger (SetVar x v);; Ret Vundef

    | CallPtr2 e args =>
      p <- denote_expr e;; f <- trigger (GetName p);;
      if (String.string_dec f "load" || String.string_dec f "store")
      then triggerUB
      else
        eval_args <- (mapT denote_expr args);;
        trigger (Call f (eval_args↑));; Ret Vundef

    | CallSys1 x f args =>
      eval_args <- (mapT denote_expr args);;
      v <- trigger (Syscall f eval_args top1);;
      trigger (SetVar x v);; Ret Vundef

    | CallSys2 f args =>
      eval_args <- (mapT denote_expr args);;
      trigger (Syscall f eval_args top1);; Ret Vundef

    | Return1 e => v <- denote_expr e;; Ret v
    | Return2 => Ret Vundef

    | AddrOf x X =>
      v <- trigger (GetPtr X);; trigger (SetVar x v);; Ret Vundef
    | Load x pe =>
      p <- denote_expr pe;;
      v <- trigger (Call "load" (p↑));; v <- unwrapN(v↓);;
      trigger (SetVar x v);; Ret Vundef
    | Store pe ve =>
      p <- denote_expr pe;; v <- denote_expr ve;;
      trigger (Call "store" ([p ; v]↑));; Ret Vundef

    end.

End Denote.

(* ========================================================================== *)
(** ** Interpretation *)

Section Interp.

  Context `{Σ: GRA.t}.
  Definition effs := GlobEnv +' ImpState +' Es.

  Definition handle_GlobEnv {eff} `{eventE -< eff} : GlobEnv ~> stateT SkEnv.t (itree eff) :=
    fun _ e ge =>
      match e with
      | GetPtr X =>
        r <- (ge.(SkEnv.id2blk) X)?;; Ret (ge, Vptr r 0)
      | GetName p =>
        match p with
        | Vptr n z => x <- (ge.(SkEnv.blk2id) n)?;; Ret (ge, x)
        | _ => triggerUB
        end
      end.

  Definition interp_GlobEnv {eff} `{eventE -< eff}: itree (GlobEnv +' eff) ~> stateT SkEnv.t (itree eff) :=
    State.interp_state (case_ handle_GlobEnv ModSem.pure_state).

  (** function local environment *)
  Definition lenv := alist var val.
  Definition handle_ImpState {eff} `{eventE -< eff} : ImpState ~> stateT lenv (itree eff) :=
    fun _ e le =>
      match e with
      | GetVar x => r <- unwrapU (alist_find _ x le);; Ret (le, r)
      | SetVar x v => Ret (alist_add _ x v le, tt)
      end.

  Definition interp_ImpState {eff} `{eventE -< eff}: itree (ImpState +' eff) ~> stateT lenv (itree eff) :=
    State.interp_state (case_ handle_ImpState ModSem.pure_state).

  Definition interp_imp ge le (itr: itree effs val) :=
    interp_ImpState (interp_GlobEnv itr ge) le.
  
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
      init_args part argt (alist_add _ x v acc)
    | _, _ => None
    end
  .

  Definition eval_imp (ge: SkEnv.t) (f: function) (args: list val) : itree Es val :=
    match (init_args f.(fn_params) args []) with
    | Some iargs =>
      '(_, (_, retv)) <- (interp_imp ge (iargs++(init_lenv f.(fn_vars))) (denote_stmt f.(fn_body)));; Ret retv
    | None => triggerUB
    end
  .

End Interp.

(* ========================================================================== *)
(** ** Module *)

(** module components *)
Definition modVars := list (gname * val).
Definition modFuns := list (gname * function).

(** Imp module *)
Record module : Type := mk_module {
  mod_vars : modVars;
  mod_funs : modFuns;
}.

(**** ModSem ****)
Module ImpMod.
Section MODSEM.

  Context `{GRA: GRA.t}.
  Variable mn: mname.
  Variable m: module.

  Set Typeclasses Depth 5.
  (* Instance Initial_void1 : @Initial (Type -> Type) IFun void1 := @elim_void1. (*** TODO: move to ITreelib ***) *)

  Definition modsem (ge: SkEnv.t) : ModSem.t := {|
    ModSem.fnsems :=
      List.map (fun '(fn, f) => (fn, cfun (eval_imp ge f))) m.(mod_funs);
    ModSem.initial_mrs := [(mn, (URA.unit, tt↑))];
  |}.

  Definition get_mod: Mod.t := {|
    Mod.get_modsem := fun ge => (modsem ge);
    Mod.sk :=
      (List.map (fun '(vn, vv) => (vn, Sk.Gvar vv)) m.(mod_vars)) ++
      (List.map (fun '(fn, _) => (fn, Sk.Gfun)) m.(mod_funs));
  |}.

End MODSEM.
End ImpMod.

(* ========================================================================== *)
(** ** Notations *)

Module ImpNotations.

  (** A few notations for convenience.  *)
  Definition Var_coerce: string -> expr := Var.
  Definition Lit_coerce: val -> expr := Lit.
  Definition Vint_coerce: Z -> val := Vint.
  Coercion Var_coerce: string >-> expr.
  Coercion Lit_coerce: val >-> expr.
  Coercion Vint_coerce: Z >-> val.

  (* Definition opExpr := option expr. *)
  (* Definition opStr := option string. *)
  (* Definition opStr_coerce: opStr -> opExpr := *)
  (*   (fun os => do s <- os; Some (Var s)). *)
  (* Coercion opStr_coerce: opStr >-> opExpr. *)

  Declare Scope expr_scope.
  Bind Scope expr_scope with expr.

  Infix "+" := Plus : expr_scope.
  Infix "-" := Minus : expr_scope.
  Infix "*" := Mult : expr_scope.

  Declare Scope stmt_scope.
  Bind Scope stmt_scope with stmt.

  Notation "x '=#' e" :=
    (Assign x e) (at level 60, e at level 50): stmt_scope.

  Notation "a ';#' b" :=
    (Seq a b)
      (at level 100, right associativity,
       format
         "'[v' a  ';#' '/' '[' b ']' ']'"
      ): stmt_scope.

  Notation "'if#' i 'then#' t 'else#' e 'fi#'" :=
    (If i t e)
      (at level 100,
       right associativity,
       format
         "'[v ' 'if#'  i '/' '[' 'then#'  t  ']' '/' '[' 'else#'  e ']' '/' 'fi#' ']'").

  Notation "'while#' t 'do#' b 'end#'" :=
    (While t b)
      (at level 100,
       right associativity,
       format
         "'[v  ' 'while#'  t  'do#' '/' '[v' b  ']' ']' '/' 'end#'").

  Notation "'skip#'" :=
    (Skip) (at level 100): stmt_scope.

  Notation "'ret#'" :=
    (Return2) (at level 60): stmt_scope.

  Notation "'ret#' e" :=
    (Return1 e) (at level 60): stmt_scope.
  
  (* Different methods for function calls *)
  Notation "x '=@' f args" :=
    (CallFun1 x f args)
      (at level 60, f at level 9): stmt_scope.

  Notation "'@' f args" :=
    (CallFun2 f args)
      (at level 60, f at level 9): stmt_scope.

  Notation "x '=@*' fp args" :=
    (CallPtr1 x fp args)
      (at level 60, fp at level 9): stmt_scope.

  Notation "'@*' fp args" :=
    (CallPtr2 fp args)
      (at level 60, fp at level 9): stmt_scope.

  Notation "x '=@!' f args" :=
    (CallSys1 x f args)
      (at level 60, f at level 9): stmt_scope.

  Notation "'@!' f args" :=
    (CallSys2 f args)
      (at level 60, f at level 9): stmt_scope.

  (* interaction with the memory module *)
  Notation "x '=#&' X" :=
    (AddrOf x X) (at level 60): stmt_scope.

  Notation "x '=#' '*' p" :=
    (Load x p) (at level 60): stmt_scope.

  Notation "'*' p '=#' v" :=
    (Store p v) (at level 60): stmt_scope.

  Notation "x '=#' 'alloc#' s" :=
    (CallFun1 x "alloc" [s])
      (at level 60): stmt_scope.

  Notation "'free#' p" :=
    (CallFun2 "free" [p])
      (at level 60): stmt_scope.

  Notation "x '=#' '(' a '==' b ')'" :=
    (CallFun1 x "cmp" [a ; b])
      (at level 60): stmt_scope.

End ImpNotations.

(* ========================================================================== *)
(** ** Example *)
Section Example_Extract.

  Import ImpNotations.
  Let Σ: GRA.t := fun _ => of_RA.t RA.empty.
  Local Existing Instance Σ.

  Local Open Scope expr_scope.
  Local Open Scope stmt_scope.

  Definition factorial : stmt :=
    "output" =# 1%Z ;#
    while# "input"
    do# "output" =# "output" * "input";#
       "input"  =# "input" - 1%Z end#;#
    ret# "output".

  Definition factorial_fundef : function := {|
    fn_params := ["input"];
    fn_vars := ["output"];
    fn_body := factorial
  |}.

  Definition main : stmt :=
    "result" =@ "factorial" [4%Z : expr] ;#
    ret# "result".

  Definition main_fundef : function := {|
    fn_params := [];
    fn_vars := ["result"];
    fn_body := main
  |}.

  Definition ex_extract : module := {|
    mod_vars := [];
    mod_funs := [("factorial", factorial_fundef); ("main", main_fundef)];
  |}.
  
  Definition ex_prog: Mod.t := ImpMod.get_mod "Main" ex_extract.

  Definition imp_ex := ModSem.initial_itr_no_check (Mod.enclose ex_prog).

End Example_Extract.

(* ========================================================================== *)
(** ** Rewriting Leamms *)
Section PROOFS.

  (* expr *)
  Lemma denote_expr_Var
        v
    :
      denote_expr (Var v) = trigger (GetVar v).
  Proof. reflexivity. Qed.

  Lemma denote_expr_Lit
        n
    :
      denote_expr (Lit n) = Ret n.
  Proof. reflexivity. Qed.

  Lemma denote_expr_Plus
        a b
    :
      denote_expr (Plus a b) =
      l <- denote_expr a ;; r <- denote_expr b ;; (vadd l r)?.
  Proof. reflexivity. Qed.

  Lemma denote_expr_Minus
        a b
    :
      denote_expr (Minus a b) =
      l <- denote_expr a ;; r <- denote_expr b ;; (vsub l r)?.
  Proof. reflexivity. Qed.

  Lemma denote_expr_Mult
        a b
    :
      denote_expr (Mult a b) =
      l <- denote_expr a ;; r <- denote_expr b ;; (vmul l r)?.
  Proof. reflexivity. Qed.

  (* stmt *)
  Lemma denote_stmt_Assign
        x e
    :
      denote_stmt (Assign x e) =
      v <- denote_expr e ;; trigger (SetVar x v) ;; Ret Vundef.
  Proof. reflexivity. Qed.
  
  Lemma denote_stmt_Seq
        a b
    :
      denote_stmt (Seq a b) =
      denote_stmt a ;; denote_stmt b.
  Proof. reflexivity. Qed.

  Lemma denote_stmt_If
        i t e
    :
      denote_stmt (If i t e) =
      v <- denote_expr i ;; `b: bool <- (is_true v)? ;;
      if b then (denote_stmt t) else (denote_stmt e).
  Proof. reflexivity. Qed.

  Lemma denote_stmt_While
        t b
    :
      denote_stmt (While t b) =
      while (v <- denote_expr t ;; `c: bool <- (is_true v)? ;;
      if c then (denote_stmt b ;; Ret (inl tt)) else (Ret (inr Vundef))).
  Proof. reflexivity. Qed.

  Lemma denote_stmt_Skip
    :
      denote_stmt (Skip) = Ret Vundef.
  Proof. reflexivity. Qed.

  Lemma denote_stmt_Return1
        e
    :
      denote_stmt (Return1 e) =
      v <- denote_expr e;; Ret v.
  Proof. reflexivity. Qed.

  Lemma denote_stmt_Return2
    :
      denote_stmt (Return2) =
      Ret Vundef.
  Proof. reflexivity. Qed.

  Lemma denote_stmt_AddrOf
        x X
    :
      denote_stmt (AddrOf x X) =
      v <- trigger (GetPtr X);; trigger (SetVar x v);; Ret Vundef.
  Proof. reflexivity. Qed.

  Lemma denote_stmt_Load
        x pe
    :
      denote_stmt (Load x pe) =
      p <- denote_expr pe;;
      v <- trigger (Call "load" (p↑));; v <- unwrapN(v↓);;
      trigger (SetVar x v);; Ret Vundef.
  Proof. reflexivity. Qed.

  Lemma denote_stmt_Store
        pe ve
    :
      denote_stmt (Store pe ve) =
      p <- denote_expr pe;; v <- denote_expr ve;;
      trigger (Call "store" ([p ; v]↑));; Ret Vundef.
  Proof. reflexivity. Qed.

  Lemma denote_stmt_CallFun1
        x f args
    :
      denote_stmt (CallFun1 x f args) =
      if (String.string_dec f "load" || String.string_dec f "store")
      then triggerUB
      else
        eval_args <- (mapT denote_expr args);;
        v <- trigger (Call f (eval_args↑));; v <- unwrapN (v↓);;
        trigger (SetVar x v);; Ret Vundef.
  Proof. reflexivity. Qed.

  Lemma denote_stmt_CallFun2
        f args
    :
      denote_stmt (CallFun2 f args) =
      if (String.string_dec f "load" || String.string_dec f "store")
      then triggerUB
      else
        eval_args <- (@mapT list _ (itree _) _ expr val denote_expr args);;
        trigger (Call f (eval_args↑));; Ret Vundef.
  Proof. reflexivity. Qed.

  Lemma denote_stmt_CallPtr1
        x e args
    :
      denote_stmt (CallPtr1 x e args) =
      p <- denote_expr e;; f <- trigger (GetName p);;
      if (String.string_dec f "load" || String.string_dec f "store")
      then triggerUB
      else
        eval_args <- (@mapT list _ (itree _) _ expr val denote_expr args);;
        v <- trigger (Call f (eval_args↑));; v <- unwrapN (v↓);;
        trigger (SetVar x v);; Ret Vundef.
  Proof. reflexivity. Qed.
  
  Lemma denote_stmt_CallPtr2
        e args
    :
      denote_stmt (CallPtr2 e args) =
      p <- denote_expr e;; f <- trigger (GetName p);;
      if (String.string_dec f "load" || String.string_dec f "store")
      then triggerUB
      else
        eval_args <- (mapT denote_expr args);;
        trigger (Call f (eval_args↑));; Ret Vundef.
  Proof. reflexivity. Qed.

  Lemma denote_stmt_CallSys1
        x f args
    :
      denote_stmt (CallSys1 x f args) =
      eval_args <- (mapT denote_expr args);;
      v <- trigger (Syscall f eval_args top1);;
      trigger (SetVar x v);; Ret Vundef.
  Proof. reflexivity. Qed.

  Lemma denote_stmt_CallSys2
        f args
    :
      denote_stmt (CallSys2 f args) =
      eval_args <- (mapT denote_expr args);;
      trigger (Syscall f eval_args top1);; Ret Vundef.
  Proof. reflexivity. Qed.

  (* Lemma denote_stmt_CallFun2_bug *)
  (*       f *)
  (*   : *)
  (*     denote_stmt (CallFun2 f [Lit Vundef]) = *)
  (*     if (true) *)
  (*     then Ret Vundef *)
  (*     else *)
  (*       eval <- (@mapT (list) _ (itree _) _ (expr) (val) denote_expr [Lit Vundef]);; *)
  (*       trigger (Call f (eval)↑);; Ret Vundef. *)
  (* Proof. Abort. *)

  (* (* mapT cannot resolve types I guess... *) *)
  (* Lemma denote_stmt_CallFun2_bug *)
  (*       f *)
  (*   : *)
  (*     denote_stmt (CallFun2 f [Lit Vundef]) = *)
  (*     if (true) *)
  (*     then Ret Vundef *)
  (*     else *)
  (*       eval <- (mapT denote_expr [Lit Vundef]);; *)
  (*       trigger (Call f (eval)↑);; Ret Vundef. *)

  (* interp_imp *)
  Context `{Σ: GRA.t}.

  Lemma interp_imp_bind
        itr ktr ge0 le0
    :
      interp_imp ge0 le0 (v <- itr ;; ktr v)  =
      '(le1, (ge1, v)) <- interp_imp ge0 le0 itr ;;
      interp_imp ge1 le1 (ktr v).
  Proof.
    unfold interp_imp. unfold interp_GlobEnv.
    unfold interp_ImpState. grind. des_ifs.
  Qed.

  Lemma interp_imp_tau
        itr ge0 le0
    :
      interp_imp ge0 le0 (tau;; itr) =
      tau;; interp_imp ge0 le0 itr.
  Proof.
    unfold interp_imp, interp_ImpState, interp_GlobEnv.
    grind.
  Qed.

  Lemma interp_imp_Ret
        ge0 le0 v
    :
      interp_imp ge0 le0 (Ret v) = Ret (le0, (ge0, v)).
  Proof.
    unfold interp_imp, interp_ImpState, interp_GlobEnv.
    grind.
  Qed.

  Lemma interp_imp_triggerUB
        ge0 le0
    :
      (interp_imp ge0 le0 (triggerUB) : itree Es _) = triggerUB.
  Proof.
    unfold interp_imp, interp_ImpState, interp_GlobEnv, pure_state, triggerUB.
    grind.
  Qed.

  Lemma interp_imp_triggerNB
        ge0 le0
    :
      (interp_imp ge0 le0 (triggerNB) : itree Es _) = triggerNB.
  Proof.
    unfold interp_imp, interp_ImpState, interp_GlobEnv, pure_state, triggerNB.
    grind.
  Qed.

  Lemma interp_imp_unwrapU
        x ge0 le0
    :
      interp_imp ge0 le0 (unwrapU x) =
      x <- unwrapU x;; Ret (le0, (ge0, x)).
  Proof.
    unfold unwrapU. des_ifs.
    - rewrite interp_imp_Ret. ired. ss.
    - rewrite interp_imp_triggerUB.
      unfold triggerUB. grind.
  Qed.

  Lemma interp_imp_unwrapN
        x ge0 le0
    :
      interp_imp ge0 le0 (unwrapN x) =
      x <- unwrapN x;; Ret (le0, (ge0, x)).
  Proof.
    unfold unwrapN. des_ifs.
    - rewrite interp_imp_Ret. ired. ss.
    - rewrite interp_imp_triggerNB.
      unfold triggerNB. grind.
  Qed.

  Lemma interp_imp_GetPtr
        ge0 le0 X
    :
      (interp_imp ge0 le0 (trigger (GetPtr X))) =
      r <- (ge0.(SkEnv.id2blk) X)? ;; tau;; Ret (le0, (ge0, Vptr r 0)).
  Proof.
    unfold interp_imp, interp_GlobEnv, interp_ImpState, unwrapU.
    des_ifs; grind.
    - unfold unwrapU. des_ifs. grind.
    - unfold unwrapU. des_ifs. unfold triggerUB, pure_state. grind.
  Qed.

  Lemma interp_imp_GetVar
        ge0 le0 x
    :
      (interp_imp ge0 le0 (trigger (GetVar x)) : itree Es _) =
      r <- unwrapU (alist_find _ x le0);; tau;; tau;; Ret (le0, (ge0, r)).
  Proof.
    unfold interp_imp, interp_ImpState, interp_GlobEnv.
    grind. unfold unwrapU, pure_state, triggerUB. des_ifs; grind.
    - unfold unwrapU; grind.
    - unfold unwrapU, triggerUB. grind.
  Qed.

  Lemma interp_imp_Call
        ge0 le0 f args
    :
      (interp_imp ge0 le0 (trigger (Call f args)) : itree Es _) =
      r <- trigger (Call f args);; tau;; Ret (le0, (ge0, r)).
  Proof.
    unfold interp_imp, pure_state. grind.
  Qed.

  Lemma interp_imp_Syscall
        st0 f args
    :
      interp_imp (trigger (Syscall f args top1)) st0 =
      r <- trigger (Syscall f args top1);; tau;; Ret (st0, r).
  Proof.
    unfold interp_imp, pure_state. grind.
  Qed.

  Lemma interp_imp_SetVar
        ge0 le0 x v
    :
      interp_imp ge0 le0 (trigger (SetVar x v)) =
      Ret (alist_add _ x v le0, tt).
  Proof.
    unfold interp_imp, interp_ImpState, interp_GlobEnv.
    unfold unwrapU, pure_state, triggerUB. grind.
    des_ifs; grind.
    unfold triggerUB; grind.
  Qed.

  (* eval_imp  *)
  Lemma eval_imp_unfold
        fret fparams fvars fbody args
    :
      ` vret : val <- eval_imp (mk_function fret fparams fvars fbody) args ;; Ret (vret↑)
               =
               ` vret : val <-
                        (match init_args fparams args [] with
                         | Some iargs =>
                           ITree.bind (interp_imp (denote_stmt fbody) (iargs++(init_lenv (fvars))))
                                      (fun x_ : lenv * val => let (_, retv) := x_ in Ret retv)
                         | None => triggerUB
                         end) ;; Ret (vret↑).
  Proof. reflexivity. Qed.

End PROOFS.

(** tactics **)
Global Opaque denote_expr.
Global Opaque denote_stmt.
Global Opaque interp_imp.
Global Opaque eval_imp.

Require Import SimModSem.
Require Import HTactics.

(** tactic for imp-program reduction *)
Ltac imp_red :=
  cbn;
  match goal with
      (** denote_stmt *)
  | [ |- (gpaco6 (_sim_itree _) _ _ _ _ _ _ _ _ (_, ITree.bind' _ (interp_imp (denote_stmt (?stmt)) _))) ] =>
    match stmt with
    | Assign _ _ => rewrite denote_stmt_Assign
    | AddrOf _ _ => rewrite denote_stmt_AddrOf
    | Seq _ _ => rewrite denote_stmt_Seq
    | If _ _ _ => rewrite denote_stmt_If
    | While _ _ => rewrite denote_stmt_While
    | Skip => rewrite denote_stmt_Skip
    | CallFun _ _ _ => rewrite denote_stmt_CallFun
    | Return _ => rewrite denote_stmt_Return
    | Return_coerce _ => rewrite denote_stmt_Return
    | _ => fail
    end

      (** denote_expr *)
  | [ |- (gpaco6 (_sim_itree _) _ _ _ _ _ _ _ _ (_, ITree.bind' _ (interp_imp (denote_expr (?expr)) _))) ] =>
    match expr with
    | Var _ => rewrite denote_expr_Var
    | Lit _ => rewrite denote_expr_Lit
    | Plus _ _ => rewrite denote_expr_Plus
    | Minus _ _ => rewrite denote_expr_Minus
    | Mult _ _ => rewrite denote_expr_Mult
    | Var_coerce _ => rewrite denote_expr_Var
    | Lit_coerce _ => rewrite denote_expr_Lit
    | _ => fail
    end

       (** interp_imp *)
  | [ |- (gpaco6 (_sim_itree _) _ _ _ _ _ _ _ _ (_, ITree.bind' _ (interp_imp (?itr) _))) ] =>
    match itr with
    | ITree.bind' _ _ => rewrite interp_imp_bind
    | Ret _ => rewrite interp_imp_Ret
    | triggerUB => rewrite interp_imp_triggerUB
    | triggerNB => rewrite interp_imp_triggerNB
    | trigger (GetVar _) => rewrite interp_imp_GetVar
    | trigger (SetVar _ _) => rewrite interp_imp_SetVar
    | trigger (Call _ _) => rewrite interp_imp_Call
    | trigger (Syscall _ _ _) => rewrite interp_imp_Syscall
    | unwrapU _ => rewrite interp_imp_unwrapU
    | unwrapN _ => rewrite interp_imp_unwrapN
    | _ => fail
    end

  (* | [ |- (gpaco3 (_sim_itree _) _ _ _ _ _ (_, ITree.bind' _ (interp_imp (Tau _) _))) ] => *)
  (*   rewrite interp_imp_tau *)
       (** default *)
  | _ => idtac
  end.

Ltac imp_steps := repeat (repeat imp_red; steps).
