Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Imp.
Require Import ImpNotations.

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
      ["g_ret"]
      (if# "n"
       then# "g_ret" =@ "g" ["n" - 1%Z : expr] ;#
             "n" + "g_ret"
       else# 0%Z
       fi#).

  Definition f_prog : program :=
    mk_program
      []
      [("f", fF)]
  .

  Definition FSem ge: ModSem.t := ImpMod.modsem "F" f_prog ge.
  Definition F : Mod.t := ImpMod.get_mod "F" f_prog.

End F.
