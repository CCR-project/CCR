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
    if# (Var "n")
    then# ("f_ret" <<- (Fun "f") [(Var "n") - (Vint 1)] ;;;
           Expr ((Var "n") + "f_ret"))
    else# (Expr (Vint 0)) fi#.
  
  Definition g_fun : function :=
    {| params := ["n"] ; body := g_stmt |}.

  Definition g_prog : program :=
    [("g", g_fun)].

  Definition g : Mod.t := ImpMod.get_mod "g" g_prog.
  
End IMP.
