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

(** Imp types *)
Inductive type : Type :=
| Tint : type
| Tptr : type -> type
| Tvoid : type
.

Definition has_type (v: val) (t: type) : bool :=
  match v, t with
  | Vint _, Tint => true
  | Vptr _ _, Tptr _ => true
  | Vundef, _ => true
  | _, Tvoid => true
  | _, _ => false
  end
.

(* function name, return type, arguments types *)
Inductive fun_type : Type :=
| Fun (_ : gname) (_ : type) (_: list type)
| Sys (_ : gname) (_ : type) (_: list type)
.

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
| CallFun (x : option var) (f : fun_type) (args : list expr)  (* x = f(args) *)
| AddrOf (x : var) (X : gname)   (* x = &X *)
| Return (e : expr)    (* return e *)
.

Definition names (l : list (var * type)) := List.map (fun '(n, _) => n) l.

(** information of a function *)
Record function : Type := mk_function {
  fn_return : type;
  fn_params : list (var * type);
  fn_vars : list (var * type); (* disjoint with fn_params *)
  fn_body : stmt
}.

(* ========================================================================== *)
(** ** Notations *)

Module ImpNotations.

  (** A few notations for convenience.  *)
  Definition Return_coerce: expr -> stmt := Return.
  Definition Var_coerce: string -> expr := Var.
  Definition Lit_coerce: val -> expr := Lit.
  Definition Vint_coerce: Z -> val := Vint.
  Coercion Return_coerce: expr >-> stmt.
  Coercion Var_coerce: string >-> expr.
  Coercion Lit_coerce: val >-> expr.
  Coercion Vint_coerce: Z >-> val.

  Declare Scope expr_scope.
  Bind Scope expr_scope with expr.

  Infix "+" := Plus : expr_scope.
  Infix "-" := Minus : expr_scope.
  Infix "*" := Mult : expr_scope.

  Declare Scope stmt_scope.
  Bind Scope stmt_scope with stmt.

  Notation "x '=#' e" :=
    (Assign x e) (at level 60, e at level 50): stmt_scope.

  Notation "x '=#' '&' X" :=
    (AddrOf x X) (at level 60): stmt_scope.

  Notation "a ';;#' b" :=
    (Seq a b)
      (at level 100, right associativity,
       format
         "'[v' a  ';;#' '/' '[' b ']' ']'"
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

  Notation "x ':=#' '(' f ')' args" :=
    (CallFun (Some x) f args) (at level 60): stmt_scope.

  Notation "'#' '(' f ')' args" :=
    (CallFun None f args) (at level 60): stmt_scope.

  Notation "x ':=#' 'alloc' t s" :=
    (CallFun (Some x) (Fun "alloc" t [Tint]) [s]) (at level 60): stmt_scope.

  Notation "'#free' p" :=
    (CallFun None (Fun "free" Tvoid [Tptr Tvoid]) [p]) (at level 60): stmt_scope.

  Notation "x ':=#' 'load' p t" :=
    (CallFun (Some x) (Fun "load" t [Tptr t]) [p]) (at level 60): stmt_scope.

  Notation "'#store' p v" :=
    (CallFun None (Fun "store" Tvoid [Tptr Tvoid; Tvoid]) [p; v]) (at level 60): stmt_scope.

  Notation "x ':=#' '(' a ',#' t1 ')' == '(' b ',#' t2 ')'" :=
    (CallFun (Some x) (Fun "cmp" Tint [t1; t2]) [a; b]) (at level 60): stmt_scope.

End ImpNotations.

(* ========================================================================== *)
(** ** Semantics *)

(** Get/Set function local variables *)
Variant ImpState : Type -> Type :=
| GetVar (x : var) : ImpState val
| SetVar (x : var) (v : val) : ImpState unit.

(** Get pointer to a global variable *)
Variant GlobVar : Type -> Type :=
| GetPtr (x: var) : GlobVar val.

Section Denote.
 
  Context `{Σ: GRA.t}.
  Context {eff : Type -> Type}.
  Context {HasImpState : ImpState -< eff}.
  Context {HasCall : callE -< eff}.
  Context {HasEvent : eventE -< eff}.
  Context {HasGlobVar: GlobVar -< eff}.

  (** Denotation of expressions *)
  Fixpoint denote_expr (e : expr) : itree eff val :=
    match e with
    | Var v     => trigger (GetVar v)
    | Lit n     => Ret n
    | Plus a b  => l <- denote_expr a ;; r <- denote_expr b ;; (vadd l r)?
    | Minus a b => l <- denote_expr a ;; r <- denote_expr b ;; (vsub l r)?
    | Mult a b  => l <- denote_expr a ;; r <- denote_expr b ;; (vmul l r)?
    end.

  (** Rewriting lemmas *)
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

  (** Denotation of statements *)
  Definition while (step : itree eff (unit + val)) : itree eff val :=
    ITree.iter (fun _ => step) tt.

  (** Casting values into [bool]: [Vint 0] corresponds to [false] and any other
      value corresponds to [true].  *)
  Definition is_true (v : val) : option bool :=
    match v with
    | Vint n => if (n =? 0)%Z then Some false else Some true
    | _ => None
    end.

  Fixpoint check_args args types : bool :=
    match args, types with
    | [], [] => true
    | a::t1, t::t2 => (has_type a t) && (check_args t1 t2)
    | _, _ => false    
    end
  .

  Fixpoint denote_stmt (s : stmt) : itree eff val :=
    match s with
    | Assign x e =>  v <- denote_expr e ;; trigger (SetVar x v) ;; Ret Vundef
    | Seq a b    =>
      denote_stmt a ;; denote_stmt b
    | If i t e   =>
      v <- denote_expr i ;; `b: bool <- (is_true v)? ;;
      if b then (denote_stmt t) else (denote_stmt e)

    | While t b =>
      while (v <- denote_expr t ;; `c: bool <- (is_true v)? ;;
             if c then (denote_stmt b ;; Ret (inl tt)) else (Ret (inr Vundef)))

    | Skip => Ret Vundef
    | CallFun opt ft args =>
      match opt with
      | Some x =>        
        match ft with
        | Fun f ty atys =>
          eval_args <- (mapT denote_expr args) ;;
          if (check_args eval_args atys)
          then v <- trigger (Call f (eval_args↑)) ;; v <- unwrapN (v↓);;
               trigger (SetVar x v) ;; Ret Vundef
          else triggerUB
        | Sys f ty atys =>
          eval_args <- (mapT denote_expr args) ;;
          if (check_args eval_args atys)
          then v <- trigger (Syscall f eval_args top1) ;;
               trigger (SetVar x v) ;; Ret Vundef
          else triggerUB
        end

      | None =>
        match ft with
        | Fun f ty atys =>
          eval_args <- (mapT denote_expr args) ;;
          if (check_args eval_args atys)
          then trigger (Call f (eval_args↑)) ;; Ret Vundef
          else triggerUB
        | Sys f ty atys =>
          eval_args <- (mapT denote_expr args) ;;
          if (check_args eval_args atys)
          then trigger (Syscall f eval_args top1) ;; Ret Vundef
          else triggerUB
        end
      end

    | AddrOf x X =>
      v <- trigger (GetPtr X) ;; trigger (SetVar x v) ;; Ret Vundef

    | Return e => v <- denote_expr e ;; Ret v
    end.

  (** Rewriting lemmas *)
  Lemma denote_stmt_Assign
        x e
    :
      denote_stmt (Assign x e) =
      v <- denote_expr e ;; trigger (SetVar x v) ;; Ret Vundef.
  Proof. reflexivity. Qed.

  Lemma denote_stmt_AddrOf
        x X
    :
      denote_stmt (AddrOf x X) =
      v <- trigger (GetPtr X) ;; trigger (SetVar x v) ;; Ret Vundef.
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

  Lemma denote_stmt_CallFun
        opt ft args
    :
      denote_stmt (CallFun opt ft args) =
      match opt with
      | Some x =>        
        match ft with
        | Fun f ty atys =>
          eval_args <- (mapT denote_expr args) ;;
          if (check_args eval_args atys)
          then v <- trigger (Call f (eval_args↑)) ;; v <- unwrapN (v↓);;
               trigger (SetVar x v) ;; Ret Vundef
          else triggerUB
        | Sys f ty atys =>
          eval_args <- (mapT denote_expr args) ;;
          if (check_args eval_args atys)
          then v <- trigger (Syscall f eval_args top1) ;;
               trigger (SetVar x v) ;; Ret Vundef
          else triggerUB
        end

      | None =>
        match ft with
        | Fun f ty atys =>
          eval_args <- (mapT denote_expr args) ;;
          if (check_args eval_args atys)
          then trigger (Call f (eval_args↑)) ;; Ret Vundef
          else triggerUB
        | Sys f ty atys =>
          eval_args <- (mapT denote_expr args) ;;
          if (check_args eval_args atys)
          then trigger (Syscall f eval_args top1) ;; Ret Vundef
          else triggerUB
        end
      end.
  Proof. reflexivity. Qed.

  Lemma denote_stmt_Return
        e
    :
      denote_stmt (Return e) = v <- denote_expr e ;; Ret v.
  Proof. reflexivity. Qed.

End Denote.

(* ========================================================================== *)
(** ** Interpretation *)

Section Interp.

  Context `{Σ: GRA.t}.
  Definition effs := GlobVar +' ImpState +' Es.

  Definition handle_GlobVar {eff} `{eventE -< eff} : GlobVar ~> stateT SkEnv.t (itree eff) :=
    fun _ e ge =>
      match e with
      | GetPtr X => r <- (ge.(SkEnv.id2blk) X)? ;; Ret (ge, Vptr r 0)
      end.

  Definition interp_GlobVar {eff} `{eventE -< eff}: itree (GlobVar +' eff) ~> stateT SkEnv.t (itree eff) :=
    State.interp_state (case_ handle_GlobVar ModSem.pure_state).

  (** function local environment *)
  Definition lenv := alist var (type * val).
  Definition handle_ImpState {eff} `{eventE -< eff} : ImpState ~> stateT lenv (itree eff) :=
    fun _ e le =>
      match e with
      | GetVar x => '(_, r) <- unwrapU (alist_find _ x le) ;; Ret (le, r)
      | SetVar x v =>
        '(t, _) <- unwrapU (alist_find _ x le) ;;
        if (has_type v t)
        then Ret (alist_add _ x (t, v) le, tt)
        else triggerUB
      end.

  Definition interp_ImpState {eff} `{eventE -< eff}: itree (ImpState +' eff) ~> stateT lenv (itree eff) :=
    State.interp_state (case_ handle_ImpState ModSem.pure_state).

  Definition interp_imp ge le (itr: itree effs val) :=
    interp_ImpState (interp_GlobVar itr ge) le.

  Print Coercions.
  
  Fixpoint init_lenv vts : lenv :=
    match vts with
    | [] => []
    | (x, ty) :: t => (x, (ty, Vundef)) :: (init_lenv t)
    end
  .

  Fixpoint init_args params args (acc: lenv) : option lenv :=
    match params, args with
    | [], [] => Some acc
    | (x, ty) :: pt, argv :: argt =>
      if (has_type argv ty)
      then (init_args pt argt (alist_add _ x (ty, argv) acc))
      else None
    | _, _ => None
    end
  .

  Definition eval_imp (ge: SkEnv.t) (f: function) (args: list val) : itree Es val :=
    match (init_args f.(fn_params) args []) with
    | Some iargs =>
      '(_, (_, retv)) <- (interp_imp ge (iargs++(init_lenv f.(fn_vars))) (denote_stmt f.(fn_body))) ;; Ret retv
    | None => triggerUB
    end
  .

End Interp.

(** module components *)
Definition modVars := list (gname * val).
Definition modFuns := list (gname * function).

(** Imp module *)
Record module : Type := mk_module {
  mod_vars : modVars;
  mod_funs : modFuns;
}.

(**** ModSemL ****)
Module ImpMod.
Section MODSEML.
  Context `{GRA: GRA.t}.
  Variable mn: mname.
  Variable m: module.

  Set Typeclasses Depth 5.
  (* Instance Initial_void1 : @Initial (Type -> Type) IFun void1 := @elim_void1. (*** TODO: move to ITreelib ***) *)

  Definition modsem: ModSem.t := {|
    ModSem.fnsems :=
      List.map (fun '(fn, f) => (fn, cfun (eval_imp f))) m.(mod_funs);
    ModSem.mn := mn;
    ModSem.initial_mr := ε;
    ModSem.initial_st := tt↑;
  |}.

  Definition get_mod: Mod.t := {|
    Mod.get_modsem := fun ge => (modsem ge);
    Mod.sk :=
      (List.map (fun '(vn, vv) => (vn, Sk.Gvar vv)) m.(mod_vars)) ++
      (List.map (fun '(fn, _) => (fn, Sk.Gfun)) m.(mod_funs));
  |}.

End MODSEML.
End ImpMod.

Import ImpNotations.
Section Example_Extract.

  Let Σ: GRA.t := fun _ => of_RA.t RA.empty.
  Local Existing Instance Σ.

  Open Scope expr_scope.
  Open Scope stmt_scope.

  Definition factorial : stmt :=
    "output" =# 1%Z ;;#
    while# "input"
    do# "output" =# "output" * "input";;#
       "input"  =# "input" - 1%Z end#;;#
    "output".

  Definition factorial_fundef : function := {|
    fn_return := Tint;
    fn_params := [("input", Tint)];
    fn_vars := [("output", Tint)];
    fn_body := factorial
  |}.

  Let f_factorial := Fun "factorial" Tint [Tint].
  Definition main : stmt :=
    "result" :=# (f_factorial) [4%Z : expr] ;;#
    "result".

  Definition main_fundef : function := {|
    fn_return := Tint;
    fn_params := [];
    fn_vars := [("result", Tint)];
    fn_body := main
  |}.

  Definition ex_extract : module := {|
    mod_vars := [];
    mod_funs := [("factorial", factorial_fundef); ("main", main_fundef)];
  |}.
  
  Definition ex_prog: Mod.t := ImpMod.get_mod "Main" ex_extract.

  Definition imp_ex := ModSemL.initial_itr_no_check (ModL.enclose ex_prog).

End Example_Extract.


Section PROOFS.

  Context `{Σ: GRA.t}.

  Lemma interp_imp_bind
        itr ktr ge0 le0
    :
      interp_imp ge0 le0 (v <- itr ;; ktr v)  =
      '(le1, (ge1, v)) <- interp_imp ge0 le0 itr ;;
      interp_imp ge1 le1 (ktr v).
  Proof.
    unfold interp_imp. unfold interp_GlobVar.
    unfold interp_ImpState. grind. des_ifs.
  Qed.

  Lemma interp_imp_tau
        itr ge0 le0
    :
      interp_imp ge0 le0 (tau;; itr) =
      tau;; interp_imp ge0 le0 itr.
  Proof.
    unfold interp_imp, interp_ImpState, interp_GlobVar.
    grind.
  Qed.

  Lemma interp_imp_Ret
        ge0 le0 v
    :
      interp_imp ge0 le0 (Ret v) = Ret (le0, (ge0, v)).
  Proof.
    unfold interp_imp, interp_ImpState, interp_GlobVar.
    grind.
  Qed.

  Lemma interp_imp_triggerUB
        ge0 le0
    :
      (interp_imp ge0 le0 (triggerUB) : itree Es _) = triggerUB.
  Proof.
    unfold interp_imp, interp_ImpState, interp_GlobVar, pure_state, triggerUB.
    grind.
  Qed.

  Lemma interp_imp_triggerNB
        ge0 le0
    :
      (interp_imp ge0 le0 (triggerNB) : itree Es _) = triggerNB.
  Proof.
    unfold interp_imp, interp_ImpState, interp_GlobVar, pure_state, triggerNB.
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
    unfold interp_imp, interp_GlobVar, interp_ImpState, unwrapU.
    des_ifs; grind.
    - unfold unwrapU. des_ifs. grind.
    - unfold unwrapU. des_ifs. unfold triggerUB, pure_state. grind.
  Qed.

  Lemma interp_imp_GetVar
        ge0 le0 x
    :
      (interp_imp ge0 le0 (trigger (GetVar x)) : itree Es _) =
      '(_, r) <- unwrapU (alist_find _ x le0);; tau;; tau;; Ret (le0, (ge0, r)).
  Proof.
    unfold interp_imp, interp_ImpState, interp_GlobVar.
    grind. unfold unwrapU, pure_state, triggerUB. des_ifs; grind.
    - unfold unwrapU; grind.
    - unfold unwrapU, triggerUB. grind.
  Qed.

  Lemma interp_imp_SetVar
        ge0 le0 x v
    :
      (interp_imp ge0 le0 (trigger (SetVar x v)) : itree Es (_ * (_ * val))) =
      '(t, _) <- unwrapU (alist_find _ x le0) ;;
      if (has_type v t)
           then tau;; tau;; Ret ((alist_add _ x (t, v) le0, (ge0, tt)))
      else triggerUB.
  Proof.
    unfold interp_imp, interp_ImpState, interp_GlobVar.
    unfold unwrapU, pure_state, triggerUB. grind.
    des_ifs; grind.
    unfold triggerUB; grind.
  Qed.

  Lemma interp_imp_Call
        st0 f args
    :
      interp_imp (trigger (Call f args)) st0 =
      r <- trigger (Call f args);; tau;; Ret (st0, r).
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
