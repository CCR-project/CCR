From ExtLib Require Import
     Data.String
     Structures.Monad
     Structures.Traversable
     Data.List
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.
Require Import Imp.

Set Implicit Arguments.

(* ========================================================================== *)
(** ** Rewriting Leamms *)
Section PROOFS.

  Context `{Σ: GRA.t}.

  (* expr *)
  Lemma denote_expr_Var
        ge le0 v
    :
      interp_imp ge le0 (denote_expr (Var v)) =
      interp_imp ge le0 (u <- trigger (GetVar v);; assume (wf_val u);; Ret u).
  Proof. reflexivity. Qed.

  Lemma denote_expr_Lit
        ge le0 n
    :
      interp_imp ge le0 (denote_expr (Lit n)) =
      interp_imp ge le0 (assume (wf_val n);; Ret n).
  Proof. reflexivity. Qed.

  Lemma denote_expr_Plus
        ge le0 a b
    :
      interp_imp ge le0 (denote_expr (Plus a b)) =
      interp_imp ge le0 (l <- denote_expr a;; r <- denote_expr b;; u <- unwrapU (vadd l r);; assume (wf_val u);; Ret u).
  Proof. reflexivity. Qed.

  Lemma denote_expr_Minus
        ge le0 a b
    :
      interp_imp ge le0 (denote_expr (Minus a b)) =
      interp_imp ge le0 (l <- denote_expr a;; r <- denote_expr b;; u <- unwrapU (vsub l r);; assume (wf_val u);; Ret u).
  Proof. reflexivity. Qed.

  Lemma denote_expr_Mult
        ge le0 a b
    :
      interp_imp ge le0 (denote_expr (Mult a b)) =
      interp_imp ge le0 (l <- denote_expr a;; r <- denote_expr b;; u <- unwrapU (vmul l r);; assume (wf_val u);; Ret u).
  Proof. reflexivity. Qed.

  (* stmt *)
  Lemma denote_stmt_Assign
        ge le0 x e
    :
      interp_imp ge le0 (denote_stmt (Assign x e)) =
      interp_imp ge le0 (v <- denote_expr e ;; trigger (SetVar x v) ;; Ret Vundef).
  Proof. reflexivity. Qed.

  Lemma denote_stmt_Seq
        ge le0 a b
    :
      interp_imp ge le0 (denote_stmt (Seq a b)) =
      interp_imp ge le0 (denote_stmt a ;; denote_stmt b).
  Proof. reflexivity. Qed.

  Lemma denote_stmt_If
        ge le0 i t e
    :
      interp_imp ge le0 (denote_stmt (If i t e)) =
      interp_imp ge le0 (v <- denote_expr i ;; `b: bool <- (is_true v)? ;;
      if b then (denote_stmt t) else (denote_stmt e)).
  Proof. reflexivity. Qed.

  Lemma denote_stmt_Skip
        ge le0
    :
      interp_imp ge le0 (denote_stmt (Skip)) =
      interp_imp ge le0 (Ret Vundef).
  Proof. reflexivity. Qed.

  Lemma denote_stmt_Expr
        ge le0 e
    :
      interp_imp ge le0 (denote_stmt (Expr e)) =
      interp_imp ge le0 (v <- denote_expr e;; Ret v).
  Proof. reflexivity. Qed.

  Lemma denote_stmt_AddrOf
        ge le0 x X
    :
      interp_imp ge le0 (denote_stmt (AddrOf x X)) =
      interp_imp ge le0 (v <- trigger (GetPtr X);; trigger (SetVar x v);; Ret Vundef).
  Proof. reflexivity. Qed.

  Lemma denote_stmt_Malloc
        ge le0 x se
    :
      interp_imp ge le0 (denote_stmt (Malloc x se)) =
      interp_imp ge le0 (s <- denote_expr se;;
      v <- trigger (Call "alloc" ([s]↑));; v <- unwrapN(v↓);;
      trigger (SetVar x v);; Ret Vundef).
  Proof. reflexivity. Qed.

  Lemma denote_stmt_Free
        ge le0 pe
    :
      interp_imp ge le0 (denote_stmt (Free pe)) =
      interp_imp ge le0 (p <- denote_expr pe;;
      trigger (Call "free" ([p]↑));; Ret Vundef).
  Proof. reflexivity. Qed.

  Lemma denote_stmt_Load
        ge le0 x pe
    :
      interp_imp ge le0 (denote_stmt (Load x pe)) =
      interp_imp ge le0 (p <- denote_expr pe;;
      v <- trigger (Call "load" ([p]↑));; v <- unwrapN(v↓);;
      trigger (SetVar x v);; Ret Vundef).
  Proof. reflexivity. Qed.

  Lemma denote_stmt_Store
        ge le0 pe ve
    :
      interp_imp ge le0 (denote_stmt (Store pe ve)) =
      interp_imp ge le0 (p <- denote_expr pe;; v <- denote_expr ve;;
      trigger (Call "store" ([p ; v]↑));; Ret Vundef).
  Proof. reflexivity. Qed.

  Lemma denote_stmt_Cmp
        ge le0 x ae be
    :
      interp_imp ge le0 (denote_stmt (Cmp x ae be)) =
      interp_imp ge le0 ( a <- denote_expr ae;; b <- denote_expr be;;
      v <- trigger (Call "cmp" ([a ; b]↑));; v <- unwrapN (v↓);;
      trigger (SetVar x v);; Ret Vundef).
  Proof. reflexivity. Qed.

  Lemma denote_stmt_CallFun1
        ge le0 x f args
    :
      interp_imp ge le0 (denote_stmt (CallFun1 x f args)) =
      interp_imp ge le0 (
      if (call_mem f)
      then triggerUB
      else
        eval_args <- (denote_exprs args []);;
        v <- trigger (Call f (eval_args↑));; v <- unwrapN (v↓);;
        trigger (SetVar x v);; Ret Vundef).
  Proof. reflexivity. Qed.

  Lemma denote_stmt_CallFun2
        ge le0 f args
    :
      interp_imp ge le0 (denote_stmt (CallFun2 f args)) =
      interp_imp ge le0 (
      if (call_mem f)
      then triggerUB
      else
        eval_args <- (denote_exprs args []);;
        trigger (Call f (eval_args↑));; Ret Vundef).
  Proof. reflexivity. Qed.

  Lemma denote_stmt_CallPtr1
        ge le0 x e args
    :
      interp_imp ge le0 (denote_stmt (CallPtr1 x e args)) =
      interp_imp ge le0 (
      p <- denote_expr e;; f <- trigger (GetName p);;
      if (call_mem f)
      then triggerUB
      else
        eval_args <- (denote_exprs args []);;
        v <- trigger (Call f (eval_args↑));; v <- unwrapN (v↓);;
        trigger (SetVar x v);; Ret Vundef).
  Proof. reflexivity. Qed.

  Lemma denote_stmt_CallPtr2
        ge le0 e args
    :
      interp_imp ge le0 (denote_stmt (CallPtr2 e args)) =
      interp_imp ge le0 (
      p <- denote_expr e;; f <- trigger (GetName p);;
      if (call_mem f)
      then triggerUB
      else
        eval_args <- (denote_exprs args []);;
        trigger (Call f (eval_args↑));; Ret Vundef).
  Proof. reflexivity. Qed.

  Lemma denote_stmt_CallSys1
        ge le0 x f args
    :
      interp_imp ge le0 (denote_stmt (CallSys1 x f args)) =
      interp_imp ge le0 (
      eval_args <- (denote_exprs args []);;
      v <- trigger (Syscall f eval_args top1);;
      trigger (SetVar x v);; Ret Vundef).
  Proof. reflexivity. Qed.

  Lemma denote_stmt_CallSys2
        ge le0 f args
    :
      interp_imp ge le0 (denote_stmt (CallSys2 f args)) =
      interp_imp ge le0 (
      eval_args <- (denote_exprs args []);;
      trigger (Syscall f eval_args top1);; Ret Vundef).
  Proof. reflexivity. Qed.

  (* interp_imp *)

  Lemma interp_imp_bind
        itr ktr ge le0
    :
      interp_imp ge le0 (v <- itr ;; ktr v) =
      '(le1, v) <- interp_imp ge le0 itr ;;
      interp_imp ge le1 (ktr v).
  Proof.
    unfold interp_imp. unfold interp_GlobEnv.
    unfold interp_ImpState. grind. des_ifs.
  Qed.

  Lemma interp_imp_tau
        itr ge le0
    :
      interp_imp ge le0 (tau;; itr) =
      tau;; interp_imp ge le0 itr.
  Proof.
    unfold interp_imp, interp_ImpState, interp_GlobEnv.
    grind.
  Qed.

  Lemma interp_imp_Ret
        ge le0 v
    :
      interp_imp ge le0 (Ret v) = Ret (le0, v).
  Proof.
    unfold interp_imp, interp_ImpState, interp_GlobEnv.
    grind.
  Qed.

  Lemma interp_imp_triggerUB
        ge le0
    :
      (interp_imp ge le0 (triggerUB) : itree Es _) = triggerUB.
  Proof.
    unfold interp_imp, interp_ImpState, interp_GlobEnv, pure_state, triggerUB.
    grind. rewrite interp_trigger. grind.
  Qed.

  Lemma interp_imp_triggerNB
        ge le0
    :
      (interp_imp ge le0 (triggerNB) : itree Es _) = triggerNB.
  Proof.
    unfold interp_imp, interp_ImpState, interp_GlobEnv, pure_state, triggerNB.
    grind. rewrite interp_trigger. grind.
  Qed.

  Lemma interp_imp_unwrapU
        x ge le0
    :
      interp_imp ge le0 (unwrapU x) =
      x <- unwrapU x;; Ret (le0, x).
  Proof.
    unfold unwrapU. des_ifs.
    - rewrite interp_imp_Ret. ired. ss.
    - rewrite interp_imp_triggerUB.
      unfold triggerUB. grind.
  Qed.

  Lemma interp_imp_unwrapN
        x ge le0
    :
      interp_imp ge le0 (unwrapN x) =
      x <- unwrapN x;; Ret (le0, x).
  Proof.
    unfold unwrapN. des_ifs.
    - rewrite interp_imp_Ret. ired. ss.
    - rewrite interp_imp_triggerNB.
      unfold triggerNB. grind.
  Qed.

  Lemma interp_imp_GetPtr
        ge le0 X
    :
      interp_imp ge le0 (trigger (GetPtr X)) =
      r <- (ge.(SkEnv.id2blk) X)? ;; tau;; Ret (le0, Vptr r 0).
  Proof.
    unfold interp_imp, interp_GlobEnv, interp_ImpState, unwrapU.
    des_ifs; grind.
    - rewrite interp_trigger. grind.
      unfold unwrapU. des_ifs. grind.
    - rewrite interp_trigger. grind.
      unfold unwrapU. des_ifs. unfold triggerUB, pure_state. grind.
  Qed.

  Lemma interp_imp_GetVar
        ge le0 x
    :
      (interp_imp ge le0 (trigger (GetVar x)) : itree Es _) =
      r <- unwrapU (alist_find x le0);; tau;; tau;; Ret (le0, r).
  Proof.
    unfold interp_imp, interp_ImpState, interp_GlobEnv.
    rewrite interp_trigger. grind.
  Qed.

  Lemma interp_imp_SetVar_Vundef
        ge le0 x v
    :
      interp_imp ge le0 (trigger (SetVar x v) ;; Ret Vundef) =
      tau;; tau;; Ret (alist_add x v le0, Vundef).
  Proof.
    unfold interp_imp, interp_GlobEnv, interp_ImpState. grind.
    rewrite interp_trigger. grind.
  Qed.

  Lemma interp_imp_Call_only
        ge le0 f args
    :
      interp_imp ge le0 (trigger (Call f args);; Ret Vundef) =
      trigger (Call f args);; tau;; tau;; Ret (le0, Vundef).
  Proof.
    unfold interp_imp, interp_GlobEnv, interp_ImpState. grind.
    unfold pure_state. rewrite interp_trigger. grind.
  Qed.

  Lemma interp_imp_Call_ret
        ge le0 f args x
    :
      interp_imp ge le0
                 (v <- trigger (Call f args);; v <- unwrapN (v↓);;
                  trigger (SetVar x v);; Ret Vundef) =
      v <- trigger (Call f args);;
      tau;; tau;; v <- unwrapN (v↓);;
      tau;; tau;; Ret (alist_add x v le0, Vundef).
  Proof.
    unfold interp_imp, interp_GlobEnv, interp_ImpState. grind.
    unfold pure_state. rewrite interp_trigger. grind.
    unfold unwrapN. des_ifs; grind.
    - rewrite interp_trigger. grind.
    - unfold triggerNB. grind. rewrite interp_trigger. grind.
  Qed.

  Lemma interp_imp_Syscall_only
        ge le0 f args
    :
      interp_imp ge le0 (trigger (Syscall f args top1);; Ret Vundef) =
      trigger (Syscall f args top1);; tau;; tau;; Ret (le0, Vundef).
  Proof.
    unfold interp_imp, interp_GlobEnv, interp_ImpState. grind.
    unfold pure_state. rewrite interp_trigger. grind.
  Qed.

  Lemma interp_imp_Syscall_ret
        ge le0 f args x
    :
      interp_imp ge le0
                 (v <- trigger (Syscall f args top1);;
                  trigger (SetVar x v);; Ret Vundef) =
      v <- trigger (Syscall f args top1);;
      tau;; tau;; tau;; tau;;
      Ret (alist_add x v le0, Vundef).
  Proof.
    unfold interp_imp, interp_GlobEnv, interp_ImpState. grind.
    unfold pure_state. rewrite interp_trigger. grind.
    rewrite interp_trigger. grind.
  Qed.

  Lemma interp_imp_assume_wf_val
        ge le0 x
    :
      interp_imp ge le0 (assume (wf_val x);; Ret x) = assume (wf_val x);; tau;; tau;; Ret (le0, x).
  Proof.
    unfold interp_imp, interp_GlobEnv, interp_ImpState. grind.
    unfold assume. grind. rewrite interp_trigger. grind.
    unfold pure_state. grind.
  Qed.

  Lemma interp_imp_expr_Var
        ge le0 v
    :
      interp_imp ge le0 (denote_expr (Var v)) =
      r <- unwrapU (alist_find v le0);; tau;; tau;; assume (wf_val r);; tau;; tau;; Ret (le0, r).
  Proof.
    rewrite denote_expr_Var. rewrite interp_imp_bind. rewrite interp_imp_GetVar.
    grind. apply interp_imp_assume_wf_val.
  Qed.

  Lemma interp_imp_expr_Lit
        ge le0 n
    :
      interp_imp ge le0 (denote_expr (Lit n)) =
      assume (wf_val n);; tau;; tau;; Ret (le0, n).
  Proof.
    rewrite denote_expr_Lit. apply interp_imp_assume_wf_val.
  Qed.

  Lemma interp_imp_expr_Plus
        ge le0 a b
    :
      interp_imp ge le0 (denote_expr (Plus a b)) =
      '(le1, l) <- interp_imp ge le0 (denote_expr a) ;;
      '(le2, r) <- interp_imp ge le1 (denote_expr b) ;;
      v <- (vadd l r)? ;;
      assume (wf_val v);; tau;; tau;;
      Ret (le2, v)
  .
  Proof.
    rewrite denote_expr_Plus. rewrite interp_imp_bind.
    grind. rewrite interp_imp_bind. grind.
    rewrite interp_imp_bind. rewrite interp_imp_unwrapU. grind.
    apply interp_imp_assume_wf_val.
  Qed.

  Lemma interp_imp_expr_Minus
        ge le0 a b
    :
      interp_imp ge le0 (denote_expr (Minus a b)) =
      '(le1, l) <- interp_imp ge le0 (denote_expr a) ;;
      '(le2, r) <- interp_imp ge le1 (denote_expr b) ;;
      v <- (vsub l r)? ;;
      assume (wf_val v);; tau;; tau;;
      Ret (le2, v)
  .
  Proof.
    rewrite denote_expr_Minus. rewrite interp_imp_bind.
    grind. rewrite interp_imp_bind. grind.
    rewrite interp_imp_bind. rewrite interp_imp_unwrapU. grind.
    apply interp_imp_assume_wf_val.
  Qed.

  Lemma interp_imp_expr_Mult
        ge le0 a b
    :
      interp_imp ge le0 (denote_expr (Mult a b)) =
      '(le1, l) <- interp_imp ge le0 (denote_expr a) ;;
      '(le2, r) <- interp_imp ge le1 (denote_expr b) ;;
      v <- (vmul l r)? ;;
      assume (wf_val v);; tau;; tau;;
      Ret (le2, v)
  .
  Proof.
    rewrite denote_expr_Mult. rewrite interp_imp_bind.
    grind. rewrite interp_imp_bind. grind.
    rewrite interp_imp_bind. rewrite interp_imp_unwrapU. grind.
    apply interp_imp_assume_wf_val.
  Qed.

  Lemma interp_imp_Assign
        ge le0 x e
    :
      interp_imp ge le0 (denote_stmt (Assign x e)) =
      '(le1, v) <- interp_imp ge le0 (denote_expr e) ;;
      tau;; tau;; Ret (alist_add x v le1, Vundef).
  Proof.
    rewrite denote_stmt_Assign.
    rewrite interp_imp_bind. grind.
    apply interp_imp_SetVar_Vundef.
  Qed.

  Lemma interp_imp_Seq
        ge le0 a b
    :
      interp_imp ge le0 (denote_stmt (Seq a b)) =
      '(le1, _) <- interp_imp ge le0 (denote_stmt a) ;;
      interp_imp ge le1 (denote_stmt b).
  Proof.
    rewrite denote_stmt_Seq.
    apply interp_imp_bind.
  Qed.

  Lemma interp_imp_If
        ge le0 i t e
    :
      interp_imp ge le0 (denote_stmt (If i t e)) =
      '(le1, v) <- interp_imp ge le0 (denote_expr i) ;;
      `b: bool <- (is_true v)? ;;
       if b
       then interp_imp ge le1 (denote_stmt t)
       else interp_imp ge le1 (denote_stmt e).
  Proof.
    rewrite denote_stmt_If. rewrite interp_imp_bind.
    grind. destruct (is_true v); grind; des_ifs.
    unfold interp_imp, interp_GlobEnv, interp_ImpState.
    unfold triggerUB, pure_state. grind.
    rewrite interp_trigger. grind.
  Qed.

  Lemma interp_imp_Skip
        ge le0
    :
      interp_imp ge le0 (denote_stmt (Skip)) =
      Ret (le0, Vundef).
  Proof.
    rewrite denote_stmt_Skip. apply interp_imp_Ret.
  Qed.

  Lemma interp_imp_Expr
        ge le0 e
    :
      interp_imp ge le0 (denote_stmt (Expr e)) =
      '(le1, v) <- interp_imp ge le0 (denote_expr e) ;;
      Ret (le1, v).
  Proof.
    rewrite denote_stmt_Expr. rewrite interp_imp_bind.
    grind. apply interp_imp_Ret.
  Qed.

  Lemma interp_imp_AddrOf
        ge le0 x X
    :
      interp_imp ge le0 (denote_stmt (AddrOf x X)) =
      r <- (ge.(SkEnv.id2blk) X)? ;; tau;;
      tau;; tau;; Ret (alist_add x (Vptr r 0) le0, Vundef).
  Proof.
    rewrite denote_stmt_AddrOf. rewrite interp_imp_bind.
    rewrite interp_imp_GetPtr. grind.
    apply interp_imp_SetVar_Vundef.
  Qed.

  Lemma interp_imp_Malloc
        ge le0 x se
    :
      interp_imp ge le0 (denote_stmt (Malloc x se)) =
      '(le1, s) <- interp_imp ge le0 (denote_expr se);;
      v <- trigger (Call "alloc" ([s]↑));;
      tau;; tau;; v <- unwrapN (v↓);;
      tau;; tau;; Ret (alist_add x v le1, Vundef).
  Proof.
    rewrite denote_stmt_Malloc. rewrite interp_imp_bind.
    grind. apply interp_imp_Call_ret.
  Qed.

  Lemma interp_imp_Free
        ge le0 pe
    :
      interp_imp ge le0 (denote_stmt (Free pe)) =
      '(le1, p) <- interp_imp ge le0 (denote_expr pe);;
      trigger (Call "free" ([p]↑));; tau;; tau;; Ret (le1, Vundef).
  Proof.
    rewrite denote_stmt_Free. rewrite interp_imp_bind.
    grind. apply interp_imp_Call_only.
  Qed.

  Lemma interp_imp_Load
        ge le0 x pe
    :
      interp_imp ge le0 (denote_stmt (Load x pe)) =
      '(le1, p) <- interp_imp ge le0 (denote_expr pe);;
      v <- trigger (Call "load" ([p]↑));;
      tau;; tau;; v <- unwrapN (v↓);;
      tau;; tau;; Ret (alist_add x v le1, Vundef).
  Proof.
    rewrite denote_stmt_Load. rewrite interp_imp_bind.
    grind. apply interp_imp_Call_ret.
  Qed.

  Lemma interp_imp_Store
        ge le0 pe ve
    :
      interp_imp ge le0 (denote_stmt (Store pe ve)) =
      '(le1, p) <- interp_imp ge le0 (denote_expr pe);;
      '(le2, v) <- interp_imp ge le1 (denote_expr ve);;
      trigger (Call "store" ([p ; v]↑));; tau;; tau;; Ret (le2, Vundef).
  Proof.
    rewrite denote_stmt_Store. rewrite interp_imp_bind.
    grind. rewrite interp_imp_bind. grind.
    apply interp_imp_Call_only.
  Qed.

  Lemma interp_imp_Cmp
        ge le0 x ae be
    :
      interp_imp ge le0 (denote_stmt (Cmp x ae be)) =
      '(le1, a) <- interp_imp ge le0 (denote_expr ae);;
      '(le2, b) <- interp_imp ge le1 (denote_expr be);;
      v <- trigger (Call "cmp" ([a ; b]↑));;
      tau;; tau;; v <- unwrapN (v↓);;
      tau;; tau;; Ret (alist_add x v le2, Vundef).
  Proof.
    rewrite denote_stmt_Cmp. rewrite interp_imp_bind.
    grind. rewrite interp_imp_bind. grind.
    apply interp_imp_Call_ret.
  Qed.

  Fixpoint interp_imp_denote_exprs ge le es acc :=
    match es with
    | [] => Ret (le, acc)
    | e :: s =>
      '(le1, v) <- interp_imp ge le (denote_expr e);;
      interp_imp_denote_exprs ge le1 s (acc ++ [v])
    end.

  Lemma interp_imp_exprs
        ge le0 x f args acc
    :
      interp_imp ge le0 (
                   eval_args <- (denote_exprs args acc);;
                   v <- trigger (Call f (eval_args↑));; v <- unwrapN (v↓);;
                   trigger (SetVar x v);; Ret Vundef)
      =
      '(le1, vs) <- interp_imp_denote_exprs ge le0 args acc;;
      v <- trigger (Call f (vs↑));;
      tau;; tau;; v <- unwrapN (v↓);;
      tau;; tau;; Ret (alist_add x v le1, Vundef).
  Proof.
    move args before Σ. revert_until args. induction args; i.
    - grind. apply interp_imp_Call_ret.
    - grind. rewrite interp_imp_bind. grind.
      destruct x0. auto.
  Qed.

  Lemma interp_imp_exprs_only
        ge le0 f args acc
    :
      interp_imp ge le0 (
                   eval_args <- (denote_exprs args acc);;
                   trigger (Call f (eval_args↑));; Ret Vundef)
      =
      '(le1, vs) <- interp_imp_denote_exprs ge le0 args acc;;
      trigger (Call f (vs↑));;
      tau;; tau;; Ret (le1, Vundef).
  Proof.
    move args before Σ. revert_until args. induction args; i.
    - grind. apply interp_imp_Call_only.
    - grind. rewrite interp_imp_bind. grind.
      destruct x. auto.
  Qed.

  Lemma interp_imp_CallFun1
        ge le0 x f args
    :
      interp_imp ge le0 (denote_stmt (CallFun1 x f args)) =
      if (call_mem f)
      then triggerUB
      else
        '(le1, vs) <- interp_imp_denote_exprs ge le0 args [];;
        v <- trigger (Call f (vs↑));;
        tau;; tau;; v <- unwrapN (v↓);;
        tau;; tau;; Ret (alist_add x v le1, Vundef).
  Proof.
    rewrite denote_stmt_CallFun1. des_ifs; try (apply interp_imp_exprs).
    apply interp_imp_triggerUB.
  Qed.

  Lemma interp_imp_CallFun2
        ge le0 f args
    :
      interp_imp ge le0 (denote_stmt (CallFun2 f args)) =
      if (call_mem f)
      then triggerUB
      else
        '(le1, vs) <- interp_imp_denote_exprs ge le0 args [];;
        trigger (Call f (vs↑));;
        tau;; tau;; Ret (le1, Vundef).
  Proof.
    rewrite denote_stmt_CallFun2. des_ifs; try (apply interp_imp_exprs_only).
    apply interp_imp_triggerUB.
  Qed.

  Lemma interp_imp_CallPtr1
        ge le0 x e args
    :
      interp_imp ge le0 (denote_stmt (CallPtr1 x e args)) =
      '(le1, p) <- interp_imp ge le0 (denote_expr e);;
      match p with
      | Vptr n 0 =>
        match (SkEnv.blk2id ge n) with
        | Some f =>
          if (call_mem f)
          then tau;; triggerUB
          else
            tau;;
            '(le2, vs) <- interp_imp_denote_exprs ge le1 args [];;
            v <- trigger (Call f (vs↑));;
            tau;; tau;; v <- unwrapN (v↓);;
            tau;; tau;; Ret (alist_add x v le2, Vundef)
        | None => triggerUB
        end
      | _ => triggerUB
      end.
  Proof.
    rewrite denote_stmt_CallPtr1. rewrite interp_imp_bind. grind.
    unfold interp_imp, interp_GlobEnv, interp_ImpState. grind.
    des_ifs; rewrite interp_trigger; grind.
    all:( unfold triggerUB, unwrapU, pure_state; grind).
    - rewrite interp_trigger; grind.
    - rewrite <- (interp_imp_exprs ge) with (acc := []).
      unfold interp_imp, interp_GlobEnv, interp_ImpState. grind.
    - unfold triggerUB. grind.
  Qed.

  Lemma interp_imp_CallPtr2
        ge le0 e args
    :
      interp_imp ge le0 (denote_stmt (CallPtr2 e args)) =
      '(le1, p) <- interp_imp ge le0 (denote_expr e);;
      match p with
      | Vptr n 0 =>
        match (SkEnv.blk2id ge n) with
        | Some f =>
          if (call_mem f)
          then tau;; triggerUB
          else
            tau;;
            '(le2, vs) <- interp_imp_denote_exprs ge le1 args [];;
            trigger (Call f (vs↑));;
            tau;; tau;; Ret (le2, Vundef)
        | None => triggerUB
        end
      | _ => triggerUB
      end.
  Proof.
    rewrite denote_stmt_CallPtr2. rewrite interp_imp_bind. grind.
    unfold interp_imp, interp_GlobEnv, interp_ImpState. grind.
    des_ifs; rewrite interp_trigger; grind.
    all:( unfold triggerUB, unwrapU, pure_state; grind).
    - rewrite interp_trigger; grind.
    - rewrite <- (interp_imp_exprs_only ge) with (acc := []).
      unfold interp_imp, interp_GlobEnv, interp_ImpState. grind.
    - unfold triggerUB. grind.
  Qed.

  Lemma interp_imp_exprs_sys
        ge le0 x f args acc
    :
      interp_imp ge le0 (
                   eval_args <- (denote_exprs args acc);;
                   v <- trigger (Syscall f eval_args top1);;
                   trigger (SetVar x v);; Ret Vundef)
      =
      '(le1, vs) <- interp_imp_denote_exprs ge le0 args acc;;
      v <- trigger (Syscall f vs top1);;
      tau;; tau;; tau;; tau;;
      Ret (alist_add x v le1, Vundef).
  Proof.
    move args before Σ. revert_until args. induction args; i.
    - grind. apply interp_imp_Syscall_ret.
    - grind. rewrite interp_imp_bind. grind. destruct x0. auto.
  Qed.

  Lemma interp_imp_exprs_sys_only
        ge le0 f args acc
    :
      interp_imp ge le0 (
                   eval_args <- (denote_exprs args acc);;
                   trigger (Syscall f eval_args top1);; Ret Vundef)
      =
      '(le1, vs) <- interp_imp_denote_exprs ge le0 args acc;;
      trigger (Syscall f vs top1);;
      tau;; tau;; Ret (le1, Vundef).
  Proof.
    move args before Σ. revert_until args. induction args; i.
    - grind. apply interp_imp_Syscall_only.
    - grind. rewrite interp_imp_bind. grind. destruct x. auto.
  Qed.

  Lemma interp_imp_CallSys1
        ge le0 x f args
    :
      interp_imp ge le0 (denote_stmt (CallSys1 x f args)) =
      '(le1, vs) <- interp_imp_denote_exprs ge le0 args [];;
      v <- trigger (Syscall f vs top1);;
      tau;; tau;; tau;; tau;;
      Ret (alist_add x v le1, Vundef).
  Proof.
    rewrite denote_stmt_CallSys1. apply interp_imp_exprs_sys.
  Qed.

  Lemma interp_imp_CallSys2
        ge le0 f args
    :
      interp_imp ge le0 (denote_stmt (CallSys2 f args)) =
      '(le1, vs) <- interp_imp_denote_exprs ge le0 args [];;
      trigger (Syscall f vs top1);;
      tau;; tau;;
      Ret (le1, Vundef).
  Proof.
    rewrite denote_stmt_CallSys2. apply interp_imp_exprs_sys_only.
  Qed.

  (* eval_imp  *)
  Lemma unfold_eval_imp
        ge fparams fvars fbody args
    :
      ` vret : val <- eval_imp ge (mk_function fparams fvars fbody) args ;; Ret (vret↑)
               =
               ` vret : val <-
                        (match init_args fparams args [] with
                         | Some iargs =>
                           ITree.bind (interp_imp ge (iargs++(init_lenv (fvars))) (denote_stmt fbody))
                                      (fun x_ : lenv * val => let '(_, retv) := x_ in Ret retv)
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
Require Import ImpNotations.

Import ImpNotations.
(** tactic for imp-program reduction *)
Ltac imp_red :=
  cbn;
  match goal with
  (** denote_stmt *)
  | [ |- (gpaco6 (_sim_itree _) _ _ _ _ _ _ _ _ (_, ITree.bind' _ (interp_imp _ _ (denote_stmt (?stmt))))) ] =>
    match stmt with
    | Assign _ _ => rewrite interp_imp_Assign
    | Seq _ _ => rewrite interp_imp_Seq; imp_red
    | If _ _ _ => rewrite interp_imp_If
    | Skip => rewrite interp_imp_Skip
    | CallFun1 _ _ _ => rewrite interp_imp_CallFun1
    | CallFun2 _ _ => rewrite interp_imp_CallFun2
    | CallPtr1 _ _ _ => rewrite interp_imp_CallPtr1
    | CallPtr2 _ _ => rewrite interp_imp_CallPtr2
    | CallSys1 _ _ _ => rewrite interp_imp_CallSys1
    | CallSys2 _ _ => rewrite interp_imp_CallSys2
    | Expr _ => rewrite interp_imp_Expr
    | Expr_coerce _ => rewrite interp_imp_Expr
    | AddrOf _ _ => rewrite interp_imp_AddrOf
    | Malloc _ _ => rewrite interp_imp_Malloc
    | Free _ => rewrite interp_imp_Free
    | Load _ _ => rewrite interp_imp_Load
    | Store _ _ => rewrite interp_imp_Store
    | Cmp _ _ _ => rewrite interp_imp_Cmp
    | _ => fail
    end

      (** denote_expr *)
  | [ |- (gpaco6 (_sim_itree _) _ _ _ _ _ _ _ _ (_, ITree.bind' _ (interp_imp _ _ (denote_expr (?expr))))) ] =>
    match expr with
    | Var _ => rewrite interp_imp_expr_Var
    | Lit _ => rewrite interp_imp_expr_Lit
    | Plus _ _ => rewrite interp_imp_expr_Plus
    | Minus _ _ => rewrite interp_imp_expr_Minus
    | Mult _ _ => rewrite interp_imp_expr_Mult
    | Var_coerce _ => rewrite interp_imp_expr_Var
    | Lit_coerce _ => rewrite interp_imp_expr_Lit
    | _ => fail
    end

  | _ => idtac
  end.

Ltac imp_steps := repeat (repeat imp_red; steps).
