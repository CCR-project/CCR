Require Import ImpPrelude.
Require Import PCM.
Require Import ModSem.
Require Import Imp.
Require Import ImpNotations.

Set Implicit Arguments.

Section CLIENT.

  Context `{Σ: GRA.t}.

  Import ImpNotations.
  Local Open Scope expr_scope.
  Local Open Scope stmt_scope.

  Definition getint :=
    mk_function
      []
      ["ret"]
      (
        "ret" =@! "scan" [] ;#
        return# "ret"
      ).

  Definition putint :=
    mk_function
      ["v"]
      []
      (
        @! "print" ["v" : expr]
      ).

  Definition Client_prog : program :=
    mk_program
      "Client"
      []
      []
      []
      [("getint", getint); ("putint", putint)]
  .

  Definition ClientSem ge : ModSem.t := ImpMod.modsem Client_prog ge.
  Definition Client : Mod.t := ImpMod.get_mod Client_prog.

End CLIENT.
