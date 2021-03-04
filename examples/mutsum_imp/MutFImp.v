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

Definition foo := IF True then True else False.
  Definition f_stmt : stmt :=
    If (Var "n")
       ((CallFun "g_ret" "g" [(Var "n") - (Vint 1)]);;;(Expr ((Var "n") + "g_ret")))
       (Expr (Lit (Vint 0))).
    (* IF (Var "n") *)
    (* THEN (CallFun "g_ret" "g" [(Var "n") - (Vint 1)]);;; ((Var "n") + "g_ret") *)
    (* ELSE (Lit (Vint 0)) FI. *)
  
  Definition f_fun : function :=
    {| params := ["n"] ; body := f_stmt |}.

  Definition f_prog : program :=
    [("f", f_fun)].

  Definition f : Mod.t := ImpMod.get_mod "f" f_prog.
  (* Definition ex_extract : program := *)
  (*   [("factorial", factorial_fundef); ("main", main_fundef)]. *)

  (* Definition ex_prog: Mod.t := ImpMod.get_mod "Main" ex_extract. *)

  (* Definition imp_ex := ModSem.initial_itr_no_check (Mod.enclose ex_prog). *)
  
End IMP.
