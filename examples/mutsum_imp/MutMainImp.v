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

  Definition main_stmt : stmt :=
    CallFun "result" "f" [Lit (Vint 10)];;;
    Expr "result".
  
  Definition main_fun : function :=
    {| params := [] ; body := main_stmt |}.

  Definition main_prog : program :=
    [("main", main_fun)].

  Definition main : Mod.t := ImpMod.get_mod "Main" main_prog.

  (* Definition ex_extract : program := *)
  (*   [("factorial", factorial_fundef); ("main", main_fundef)]. *)

  (* Definition ex_prog: Mod.t := ImpMod.get_mod "Main" ex_extract. *)

  (* Definition imp_ex := ModSem.initial_itr_no_check (Mod.enclose ex_prog). *)
  
End IMP.
