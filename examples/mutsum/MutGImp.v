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



Section G.
  Context `{Σ: GRA.t}.

  Import ImpNotations.
  Local Open Scope expr_scope.
  Local Open Scope stmt_scope.

  Definition gF :=
    mk_function
      ["n"]
      (if# "n"
       then# "f_ret" :=# (Fun "f") ["n" - 1%Z : expr] ;;#
             "n" + "f_ret"
       else# 0%Z fi#).

  Definition g_prog : program :=
    [("g", gF)].

  Definition GSem: ModSemL.t := ImpMod.modsem "G" g_prog.

  Definition G : Mod.t := ImpMod.get_mod "G" g_prog.

End G.
