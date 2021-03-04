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

  Definition f_stmt : stmt :=
    if# (Var "n")
    then# ("g_ret" :=# (Fun "g") [(Var "n") - (Vint 1)] ;;;
           Expr ((Var "n") + "g_ret"))
    else# (Expr (Vint 0)) fi#.
  
  Definition f_fun : function :=
    {| params := ["n"] ; body := f_stmt |}.

  Definition f_prog : program :=
    [("f", f_fun)].

  Definition f : Mod.t := ImpMod.get_mod "f" f_prog.
  
End IMP.
