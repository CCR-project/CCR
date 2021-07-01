Require Import Universe.
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

  Definition echo :=
    mk_function
      []
      ["h"]
      (
        "h" =@ "new" [] ;#
        @ "input" ["h" : expr] ;#
        @ "output" ["h" : expr]
      ).

  Definition input :=
    mk_function
      ["h"]
      ["n"]
      (
        "n" =@ "getint" [] ;#
        if# ("n" + 1%Z)
        then# (
               @ "push" [Var "h"; Var "n"] ;#
               @ "input" ["h" : expr]
              )
        else# skip#
        fi#
      ).

  Definition output :=
    mk_function
      ["h"]
      ["n"]
      (
        "n" =@ "pop" [Var "h"] ;#
        if# ("n" + 1%Z)
        then# (
               @ "putint" [Var "n"] ;#
               @ "output" ["h" : expr]
              )
        else# skip#
        fi#
      ).

  Definition Echo_prog : program :=
    mk_program
      "EchoImp"
      []
      [("new", 0); ("getint", 0); ("putint", 1); ("push", 2); ("pop", 1)]
      []
      [("echo", echo); ("input", input); ("output", output)]
  .

  Definition EchoSem ge : ModSem.t := ImpMod.modsem Echo_prog ge.
  Definition Echo : Mod.t := ImpMod.get_mod Echo_prog.

End ECHO.
