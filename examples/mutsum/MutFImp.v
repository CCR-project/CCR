Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Imp.
Require Import ImpNotations.

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
             return# ("n" + "g_ret")
       else# return# 0%Z
       fi#).

  Definition f_prog : program :=
    mk_program
      "F"
      []
      [("g", 1)]
      []
      [("f", fF)]
  .

  Definition FSem ge: ModSem.t := ImpMod.modsem f_prog ge.
  Definition F : Mod.t := ImpMod.get_mod f_prog.

End F.
