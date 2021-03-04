Require Import Any.
Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem.
Require Import Imp.

Set Implicit Arguments.

Section IMP.
  Import ImpNotations.
  Local Open Scope expr_scope.
  Local Open Scope stmt_scope.

  Let Σ: GRA.t := fun _ => URA.of_RA RA.empty.
  Local Existing Instance Σ.

  Definition g_stmt : stmt :=
    If (Var "n")
       ((CallFun "f_ret" "f" [(Var "n") - (Vint 1)]);;;(Expr ((Var "n") + "f_ret")))
       (Expr (Lit (Vint 0))).
    (* IF (Var "n") *)
    (* THEN (CallFun "g_ret" "g" [(Var "n") - (Vint 1)]);;; ((Var "n") + "g_ret") *)
    (* ELSE (Lit (Vint 0)) FI. *)
  
  Definition g_fun : function :=
    {| params := ["n"] ; body := g_stmt |}.

  Definition g_prog : program :=
    [("g", g_fun)].

  Definition g : Mod.t := ImpMod.get_mod "g" g_prog.
  (* Definition ex_extract : program := *)
  (*   [("factorial", factorial_fundef); ("main", main_fundef)]. *)

  (* Definition ex_prog: Mod.t := ImpMod.get_mod "Main" ex_extract. *)

  (* Definition imp_ex := ModSem.initial_itr_no_check (Mod.enclose ex_prog). *)
  
End IMP.
