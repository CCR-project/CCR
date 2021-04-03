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
     Data.List.

From ITree Require Import
     ITree
     ITreeFacts
     Events.MapDefault
     Events.StateFacts.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.

Require Import Any.
Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
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
.

Definition has_type (v: val) (t: type) : bool :=
  match v, t with
  | Vint _, Tint => true
  | Vptr _ _, Tptr _ => true
  | Vundef, _ => true
  | _, _ => false
  end
.

Inductive fun_type : Type :=
| Fun (_ : gname) (_ : type)
| Sys (_ : gname) (_ : type)
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
| CallFun (x : var) (f : fun_type) (args : list expr)  (* x = f(args) *)
| Return (e : expr)    (* return e *)
.

(** information of a function *)
Record function : Type := mk_function {
  fn_return : type;
  fn_params : list (var * type);
  fn_vars : list (var * type); (* includes fn_params *)
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

  Bind Scope expr_scope with expr.

  Infix "+" := Plus : expr_scope.
  Infix "-" := Minus : expr_scope.
  Infix "*" := Mult : expr_scope.

  Bind Scope stmt_scope with stmt.

  Notation "x '=#' e" :=
    (Assign x e) (at level 60, e at level 50): stmt_scope.

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
    (CallFun x f args) (at level 60): stmt_scope.

End ImpNotations.

Import ImpNotations.

(* ========================================================================== *)
(** ** Semantics *)

(** Get/Set function local variables *)
Variant ImpState : Type -> Type :=
| GetVar (x : var) : ImpState val
| SetVar (x : var) (v : val) : ImpState unit.

Section Denote.
 
  Context `{Σ: GRA.t}.
  Context {eff : Type -> Type}.
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
    | CallFun x ft args =>
      match ft with
      | Fun f ty =>
        eval_args <- (mapT denote_expr args) ;;
        v <- trigger (Call f (eval_args↑)) ;; v <- unwrapN (v↓);;
        if (has_type v ty)
        then trigger (SetVar x v) ;; Ret Vundef
        else triggerNB
      | Sys f ty =>
        eval_args <- (mapT denote_expr args) ;;
        v <- trigger (Syscall f eval_args top1) ;;
        if (has_type v ty)
        then trigger (SetVar x v) ;; Ret Vundef
        else triggerNB
      end

    | Return e => v <- denote_expr e ;; Ret v
    end.

  (** Rewriting lemmas *)
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

  Lemma denote_stmt_CallFun
        x ft args
    :
      denote_stmt (CallFun x ft args) =
      match ft with
      | Fun f ty =>
        eval_args <- (mapT denote_expr args) ;;
        v <- trigger (Call f (eval_args↑)) ;; v <- unwrapN (v↓);;
        if (has_type v ty)
        then trigger (SetVar x v) ;; Ret Vundef
        else triggerNB
      | Sys f ty =>
        eval_args <- (mapT denote_expr args) ;;
        v <- trigger (Syscall f eval_args top1) ;;
        if (has_type v ty)
        then trigger (SetVar x v) ;; Ret Vundef
        else triggerNB
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

(* begin hide *)
From ITree Require Import
     Events.MapDefault.

From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

(** These enable typeclass instances for Maps keyed by strings and values *)
Instance RelDec_string : RelDec (@eq string) :=
  { rel_dec := fun s1 s2 => if string_dec s1 s2 then true else false}.

Instance RelDec_string_Correct: RelDec_Correct RelDec_string.
Proof.
  constructor; intros x y.
  split.
  - unfold rel_dec; simpl.
    destruct (string_dec x y) eqn:EQ; intros; eauto.
    inversion H.
  - unfold rel_dec; simpl.
    destruct (string_dec x y) eqn:EQ; intros; eauto.
Qed.
(* end hide *)

(** function local environment, local variables included when called *)
Definition lenv := alist var (type * val).
Definition handle_ImpState {E: Type -> Type} `{Σ: GRA.t} `{eventE -< E}: ImpState ~> stateT lenv (itree E) :=
  fun _ e le =>
    match e with
    | GetVar x => '(_, r) <- unwrapU (alist_find _ x le) ;; Ret (le, r)
    | SetVar x v =>
      '(t, _) <- unwrapU (alist_find _ x le) ;;
      if (has_type v t)
      then Ret (alist_add _ x (t, v) le, tt)
      else triggerUB
    end.

Definition interp_imp `{Σ: GRA.t} : itree (ImpState +' Es) ~> stateT lenv (itree Es) :=
  State.interp_state (case_ handle_ImpState ModSem.pure_state).

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

Definition eval_imp `{Σ: GRA.t} (f: function) (args: list val) : itree Es val :=
  match (init_args f.(fn_params) args (init_lenv f.(fn_vars))) with
  | Some le =>
    '(_, retv) <- (interp_imp (denote_stmt f.(fn_body)) le) ;; Ret retv
  | None => triggerUB
  end
.

(** module components *)
Definition modFuns := list (gname * function).
Definition modVars := list (gname * val).

(** Imp module *)
Record module : Type := mk_module {
  mod_vars : modVars;
  mod_funs : modFuns;
  mod_main : gname
}.

(**** ModSemL ****)
Module ImpMod.
<<<<<<< HEAD
Section MODSEML.
=======
Section MODSEML.

>>>>>>> 3b74b52 (upgraded imp)
  Context `{GRA: GRA.t}.
  Variable mn: mname.
  Variable m: module.

  Set Typeclasses Depth 5.
  (* Instance Initial_void1 : @Initial (Type -> Type) IFun void1 := @elim_void1. (*** TODO: move to ITreelib ***) *)

  Definition modsem: ModSem.t := {|
<<<<<<< HEAD
    ModSem.fnsems :=
      List.map (fun '(fn, f) => (fn, cfun (eval_imp f))) m.(mod_funs);
    ModSem.mn := mn;
    ModSem.initial_mr := ε;
    ModSem.initial_st := tt↑;
=======
    ModSem.fnsems :=
      List.map (fun '(fn, f) => (fn, cfun (eval_imp f))) m.(mod_funs);
    ModSem.mn := mn;
    ModSem.initial_mr := ε;
    ModSem.initial_st := tt↑;
>>>>>>> 3b74b52 (upgraded imp)
  |}.

  Definition get_mod: Mod.t := {|
    Mod.get_modsem := fun _ => modsem;
    Mod.sk :=
      (List.map (fun '(vn, vv) => (vn, Sk.Gvar vv)) m.(mod_vars)) ++
      (List.map (fun '(fn, _) => (fn, Sk.Gfun)) m.(mod_funs));
  |}.

End MODSEML.
End ImpMod.


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
    fn_vars := [("output", Tint); ("input", Tint)];
    fn_body := factorial
  |}.

  Definition main : stmt :=
    "result" :=# (Fun "factorial" Tint) [4%Z : expr] ;;#
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
    mod_main := "main"
  |}.
  
  Definition ex_prog: Mod.t := ImpMod.get_mod "Main" ex_extract.

  Definition imp_ex := ModSemL.initial_itr_no_check (ModL.enclose ex_prog).

End Example_Extract.


Section PROOFS.

  Context `{Σ: GRA.t}.

  Lemma interp_imp_bind
        A B
        (itr: itree (ImpState +' Es) A) (ktr: A -> itree (ImpState +' Es) B)
        st0
    :
      interp_imp (v <- itr ;; ktr v) st0 =
      '(st1, v) <- interp_imp (itr) st0 ;;
      interp_imp (ktr v) st1.
  Proof. unfold interp_imp. grind. des_ifs. Qed.

  Lemma interp_imp_tau
        A
        (itr: itree (ImpState +' Es) A)
        st0
    :
      interp_imp (tau;; itr) st0 =
      tau;; interp_imp itr st0.
  Proof. unfold interp_imp. grind. Qed.

  Lemma interp_imp_Ret
        T
        st0 (v: T)
    :
      interp_imp (Ret v) st0 = Ret (st0, v).
  Proof. unfold interp_imp. grind. Qed.

  Lemma interp_imp_triggerUB
        st0 A
    :
      (interp_imp (triggerUB) st0 : itree Es (_ * A)) = triggerUB.
  Proof.
    unfold interp_imp, pure_state, triggerUB. grind.
  Qed.

  Lemma interp_imp_triggerNB
        st0 A
    :
      (interp_imp (triggerNB) st0 : itree Es (_ * A)) = triggerNB.
  Proof.
    unfold interp_imp, pure_state, triggerNB. grind.
  Qed.

  Lemma interp_imp_GetVar
        st0 x
    :
      (interp_imp (trigger (GetVar x)) st0 : itree Es (_ * val)) =
      '(_, r) <- unwrapU (alist_find _ x st0);; tau;; Ret (st0, r).
  Proof.
    unfold interp_imp. grind.
  Qed.

  Lemma interp_imp_SetVar
        st0 x v
    :
      interp_imp (trigger (SetVar x v)) st0 =
      '(t, _) <- unwrapU (alist_find _ x st0) ;;
      if (has_type v t)
      then tau;; Ret (alist_add _ x (t, v) st0, tt)
      else triggerUB.
  Proof.
    unfold interp_imp. grind. unfold triggerUB.
    destruct (has_type v t); grind.    
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

  Lemma interp_imp_unwrapU
        X (x: option X) st0
    :
      interp_imp (unwrapU x) st0 =
      x <- unwrapU x;; Ret (st0, x).
  Proof.
    unfold unwrapU. des_ifs.
    - rewrite interp_imp_Ret. ired. ss.
    - rewrite interp_imp_triggerUB.
      unfold triggerUB. grind.
  Qed.

  Lemma interp_imp_unwrapN
        X (x: option X) st0
    :
      interp_imp (unwrapN x) st0 =
      x <- unwrapN x;; Ret (st0, x).
  Proof.
    unfold unwrapN. des_ifs.
    - rewrite interp_imp_Ret. ired. ss.
    - rewrite interp_imp_triggerNB.
      unfold triggerNB. grind.
  Qed.

  Lemma eval_imp_unfold
        fret fparams fvars fbody args
    :
      ` vret : val <- eval_imp (mk_function fret fparams fvars fbody) args ;; Ret (vret↑)
               =
               ` vret : val <-
                        (match init_args fparams args (init_lenv fvars) with
                         | Some le =>
                           ITree.bind (interp_imp (denote_stmt fbody) le)
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
