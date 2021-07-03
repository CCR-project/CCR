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



Section G.
  Context `{Σ: GRA.t}.

  Import ImpNotations.
  Local Open Scope expr_scope.
  Local Open Scope stmt_scope.

  Definition gF :=
    mk_function
      ["n"]
      ["f_ret"]
      (if# "n"
       then# "f_ret" =@ "f" ["n" - 1%Z : expr] ;#
             return# "n" + "f_ret"
       else# return# 0%Z
       fi#).

  Definition g_prog : program :=
    mk_program
      "G"
      []
      [("f", 1)]
      []
      [("g", gF)]
  .
  
  Definition GSem ge: ModSem.t := ImpMod.modsem g_prog ge.
  Definition G : Mod.t := ImpMod.get_mod g_prog.

End G.
