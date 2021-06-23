Require Import Coqlib.
Require Import Universe.
Require Import Imp.
Require Import ImpNotations.

Set Implicit Arguments.

Import ImpNotations.
Local Open Scope expr_scope.
Local Open Scope stmt_scope.

Section F.

  Definition fF :=
    mk_function
      ["n"]
      ["g_ret"]
      (if# "n"
       then# "g_ret" =@ "g" ["n" - 1%Z : expr] ;#
             return# ("n" + "g_ret")
       else# return# (0%Z)
       fi#).

  Definition imp_linkF_prog : program :=
    mk_program
      "LinkF"
      []
      [("g", 1)]
      []
      [("f", fF)]
  .

End F.

Section G.

  Definition gF :=
    mk_function
      ["n"]
      ["f_ret"]
      (if# "n"
       then# "f_ret" =@ "f" ["n" - 1%Z : expr] ;#
             return# ("n" + "f_ret")
       else# return# (0%Z)
       fi#).

  Definition imp_linkG_prog : program :=
    mk_program
      "LinkG"
      []
      [("f", 1)]
      []
      [("g", gF)]
  .

End G.

Section Main.

  Definition mainF :=
    mk_function
      []
      ["r"]
      ("r" =@ "f" [11%Z : expr] ;#
       return# "r").

  Definition imp_linkMain_prog : program :=
    mk_program
      "LinkMain"
      []
      [("f", 1)]
      []
      [("main", mainF)]
  .

End Main.
