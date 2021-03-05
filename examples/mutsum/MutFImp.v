Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Imp.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.



Section F.
  Context `{Σ: GRA.t}.

  Import ImpNotations.
  Local Open Scope expr_scope.
  Local Open Scope stmt_scope.

  Definition fF :=
    mk_function
      ["n"]
      (if# (Var "n")
       then# ("g_ret" :=# (Fun "g") [(Var "n") - (Vint 1)] ;;;
                      Expr ((Var "n") + "g_ret"))
       else# (Expr (Vint 0)) fi#).

  Definition f_prog : program :=
    [("f", fF)].

  Definition FSem: ModSem.t := ImpMod.modsem "F" f_prog.

  Definition F : Mod.t := ImpMod.get_mod "F" f_prog.

End F.
