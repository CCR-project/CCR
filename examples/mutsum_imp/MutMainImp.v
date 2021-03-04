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
  Open Scope expr_scope.
  Open Scope stmt_scope.

  Let Σ: GRA.t := fun _ => URA.of_RA RA.empty.
  Local Existing Instance Σ.

  Definition main_stmt : stmt :=
    "input" <<- (Sys "scanf") [] ;;;
    "result" <<- (Fun "f") [Var "input"] ;;;
    Expr "result".
  
  Definition main_fun : function :=
    {| params := [] ; body := main_stmt |}.

  Definition main_prog : program :=
    [("main", main_fun)].

  Definition main : Mod.t := ImpMod.get_mod "Main" main_prog.

End IMP.
