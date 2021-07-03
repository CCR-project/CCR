Require Import ImpPrelude.
Require Import PCM.
Require Import ModSem.
Require Import Imp.
Require Import ImpNotations.

Set Implicit Arguments.



Section ECHO.

  Context `{Σ: GRA.t}.

  Import ImpNotations.
  Local Open Scope expr_scope.
  Local Open Scope stmt_scope.

  Definition main :=
    mk_function
      []
      []
      (
        @ "echo" [] ;#
        return# 0%Z
      ).

  Definition EchoMain_prog : program :=
    mk_program
      "main"
      []
      [("echo", 0)]
      []
      [("main", main)]
  .

  Definition EchoMainSem ge : ModSem.t := ImpMod.modsem EchoMain_prog ge.
  Definition EchoMain : Mod.t := ImpMod.get_mod EchoMain_prog.

End ECHO.
